use std::cell::Ref;
use std::cell::RefCell;
use std::cell::RefMut;
use std::cell::UnsafeCell;
use std::collections::HashMap;
use std::fmt::{Display, Formatter};
use std::mem::MaybeUninit;
use std::rc::Rc;

use slice_dst::SliceWithHeader;

use crate::CodeAddress;

mod stack;
mod vm;

pub use stack::ExecutionContext;

// TODO: Put this in common for use by the compiler
#[repr(usize)]
enum GlobalClassSlots {
    /* The cyclical powerhouse */
    Object = 0,
    Class,

    /* Primitive classes */
    Bool,
    Num,
    String,
    Range,
    Null,

    /* Built-in classes */
    Sequence,
    List,
    Map,
    Fn,
    Fiber,
    System,

    End,
}

/// Create a properly initialized Class, Object, and Object metaclass
fn bootstrap_class() -> (ObjectRef, ObjectRef, ObjectRef) {
    const CLASS_NUM_FIELDS: usize = /*
            num_fields,
            supertype,
            name,
            methods,
        */
        4;

    let maybe: Rc<_> = SliceWithHeader::new::<Rc<DSTRefCellInner<MaybeUninit<ObjectRef>, Value>>, _>(
        AdjacentRefCell {
            value: MaybeUninit::uninit().into(),
            refcell: RefCell::new(()),
        },
        exact_repeat::exact_repeat(CLASS_NUM_FIELDS, Value::null()).map(UnsafeCell::new),
    );

    {
        // Trickery to increase refcount in preparation for materializing the ObjectRef inside class
        let maybe2 = Rc::clone(&maybe);
        std::mem::forget(maybe2);
    }

    let class = ObjectRef({
        let ptr = Rc::into_raw(maybe) as *mut DSTRefCellInner<MaybeUninit<ObjectRef>, Value>;
        unsafe {
            // SAFETY: `maybe` is initialized so we can dereference its parts, just not the
            // MaybeUninit<ObjectRef> yet
            let ptr_to_uninit: *mut ObjectRef = {
                let uninit: *mut MaybeUninit<ObjectRef> = UnsafeCell::raw_get(&(*ptr).header.value);
                (*uninit).as_mut_ptr()
            };

            // SAFETY: RcBox and SliceWithHeader are both repr(C) so this cast should be fine
            // type-wise as
            // long as maybe2 isn't used to access the inner allocation before it gets initialized
            // on the next line
            // Re-summon maybe2 from the abyss
            let maybe2: Rc<DSTRefCellInner<ObjectRef, Value>> = Rc::from_raw(ptr as *const _);
            ptr_to_uninit.write(ObjectRef(maybe2));

            // SAFETY: Since we used mem::forget earlier, the refcount says 2 Rc's exist right now, so
            // it should be fine to call from_raw again.
            Rc::from_raw(ptr as *const _)
        }
    });

    debug_assert_eq!(Rc::strong_count(&class.0), 2);

    let object_meta = ObjectRef::new(
        class.clone(),
        exact_repeat::exact_repeat(CLASS_NUM_FIELDS, Value::null()),
    );

    // Object metaclass.supertype = Class
    object_meta.borrow_fields_mut()[1] = class.clone().into();

    let object = ObjectRef::new(
        object_meta.clone(),
        exact_repeat::exact_repeat(CLASS_NUM_FIELDS, Value::null()),
    );

    // Class.num_fields = 4
    class.borrow_fields_mut()[0] = (CLASS_NUM_FIELDS as f64).into();
    // Class.supertype = Object
    class.borrow_fields_mut()[1] = object.clone().into();

    (class, object, object_meta)
}

static mut GLOBAL_STATE: Vec<Value> = vec![];

#[derive(Debug, Clone, Copy, PartialEq)]
pub enum PrimitiveValue {
    Boolean(bool),
    Number(f64),
    String(*const [u8]),
    Range(f64, f64, bool),
    Null,
}

impl PrimitiveValue {
    const fn get_primitive_class(&self) -> usize {
        use PrimitiveValue::*;
        (match self {
            Boolean(_) => GlobalClassSlots::Bool,
            Number(_) => GlobalClassSlots::Num,
            String(_) => GlobalClassSlots::String,
            Range(_, _, _) => GlobalClassSlots::Range,
            Null => GlobalClassSlots::Null,
        }) as usize
    }
}

impl From<f64> for PrimitiveValue {
    fn from(f: f64) -> PrimitiveValue {
        PrimitiveValue::Number(f)
    }
}

impl TryFrom<PrimitiveValue> for f64 {
    type Error = ConversionError;
    fn try_from(p: PrimitiveValue) -> Result<f64, Self::Error> {
        match p {
            PrimitiveValue::Number(f) => Ok(f),
            _ => Err(ConversionError::NotNumber),
        }
    }
}

impl From<bool> for PrimitiveValue {
    fn from(b: bool) -> PrimitiveValue {
        PrimitiveValue::Boolean(b)
    }
}

pub union NativeValue {
    ptr: *mut u8,
    int: u64,
}

#[derive(Debug, Clone)]
pub enum Value {
    Primitive(PrimitiveValue),
    List(Rc<RefCell<Vec<Value>>>),
    Map(Rc<RefCell<HashMap<PrimitiveValue, Value>>>),
    Object(ObjectRef),
    Native(*mut u8),
}

impl<T> From<T> for Value
where
    T: Into<PrimitiveValue>,
{
    fn from(p: T) -> Value {
        Value::Primitive(p.into())
    }
}

impl From<ObjectRef> for Value {
    fn from(o: ObjectRef) -> Value {
        Value::Object(o)
    }
}

impl PartialEq for Value {
    fn eq(&self, other: &Value) -> bool {
        match (self, other) {
            (Value::Primitive(a), Value::Primitive(b)) => a == b,
            (Value::Object(a), Value::Object(b)) => Rc::ptr_eq(&a.0, &b.0),
            _ => false,
        }
    }
}

impl Value {
    fn null() -> Self {
        Value::Primitive(PrimitiveValue::Null)
    }

    fn is_null(&self) -> bool {
        matches!(self, Value::Primitive(PrimitiveValue::Null))
    }

    pub fn truthy(&self) -> bool {
        !matches!(
            self,
            Value::Primitive(PrimitiveValue::Null)
                | Value::Primitive(PrimitiveValue::Boolean(false))
        )
    }

    pub fn get_class(&self) -> ObjectRef {
        match self {
            Value::Object(obj) => obj.borrow_class().clone(),
            Value::Primitive(p) => {
                let index = p.get_primitive_class();
                // SAFETY: Since this clones, it shouldn't matter if it gets overwritten later
                unsafe {
                    GLOBAL_STATE[index]
                        .clone()
                        .try_into()
                        .expect("Global class has been overwritten with a non-class object")
                }
            }
            Value::List(_) => unsafe {
                GLOBAL_STATE[GlobalClassSlots::List as usize]
                    .clone()
                    .try_into()
                    .expect("Global class has been overwritten with a non-class object")
            },
            Value::Map(_) => unsafe {
                GLOBAL_STATE[GlobalClassSlots::Map as usize]
                    .clone()
                    .try_into()
                    .expect("Global class has been overwritten with a non-class object")
            },
            Value::Native(_) => panic!("Tried to get the class of a Native object"),
        }
    }
}

#[derive(Debug, Clone)]
#[repr(transparent)]
pub struct ObjectRef(Rc<DSTRefCellInner<ObjectRef, Value>>);

#[derive(Debug)]
pub enum ConversionError {
    NotObject,
    NotPrimitive,
    NotNumber,
    OutOfBounds,
}

trait SafeFloatToInt<I> {
    fn to_int(self) -> Result<I, ConversionError>;
}

impl SafeFloatToInt<usize> for f64 {
    fn to_int(self) -> Result<usize, ConversionError> {
        if self.is_finite() && self <= usize::MAX as Self && self >= usize::MIN as Self {
            Ok(unsafe { self.to_int_unchecked() })
        } else {
            Err(ConversionError::OutOfBounds)
        }
    }
}

impl Display for ConversionError {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), std::fmt::Error> {
        write!(f, "{self:?}")
    }
}

impl std::error::Error for ConversionError {}

impl TryFrom<Value> for f64 {
    type Error = ConversionError;

    fn try_from(v: Value) -> Result<f64, Self::Error> {
        match v {
            Value::Primitive(p) => p.try_into(),
            _ => Err(ConversionError::NotPrimitive),
        }
    }
}

/*
impl<T> TryFrom<Value> for T
where T: TryFrom<PrimitiveValue>
{
    type Error = ConversionError;

    fn try_from(v: Value) -> T {
        match v {
            Value::Primitive(p) => p.try_into(),
            _ => Err(ConversionError::NotPrimitive)
        }
    }
}
*/

impl TryFrom<Value> for ObjectRef {
    type Error = ConversionError;
    fn try_from(v: Value) -> Result<ObjectRef, ConversionError> {
        match v {
            Value::Object(o) => Ok(o),
            _ => Err(ConversionError::NotObject),
        }
    }
}

#[repr(C)]
#[derive(Debug)]
struct AdjacentRefCell<T> {
    value: T,
    refcell: RefCell<()>,
}

impl<T> AdjacentRefCell<T> {
    fn new(t: T) -> Self {
        AdjacentRefCell {
            value: t,
            refcell: RefCell::new(()),
        }
    }
}

type DSTRefCellInner<Header, SliceType> =
    SliceWithHeader<AdjacentRefCell<UnsafeCell<Header>>, UnsafeCell<SliceType>>;

type Object = DSTRefCellInner<ObjectRef, Value>;

impl ObjectRef {
    fn new<I>(class: ObjectRef, slice: I) -> ObjectRef
    where
        I: IntoIterator<Item = Value>,
        I::IntoIter: ExactSizeIterator,
    {
        ObjectRef(SliceWithHeader::new::<
            Rc<DSTRefCellInner<ObjectRef, Value>>,
            _,
        >(
            AdjacentRefCell {
                value: class.into(),
                refcell: RefCell::new(()),
            },
            slice.into_iter().map(UnsafeCell::new),
        ))
    }

    // TODO: Return Ref<(ObjectRef, [Value])> instead
    fn borrow_class(&self) -> std::cell::Ref<ObjectRef> {
        Ref::map(self.0.header.refcell.borrow(), |_| {
            // Safety: Can coerce this lifetime since `header.0` will never be accessed unless the
            // original RefCell is succesfully borrowed first
            unsafe { &*(self.0.header.value.get()) }
        })
    }

    fn borrow_fields(&self) -> std::cell::Ref<[Value]> {
        Ref::map(self.0.header.refcell.borrow(), |_| {
            // SAFETY: self.slice will not be accessed unless by one of these methods that borrows
            // the refcell first
            // SAFETY: Idk if *[UnsafeCell<T>] -> *[T] is allowed or not
            unsafe { &*(&self.0.slice as *const [UnsafeCell<Value>] as *const [Value]) }
        })
    }

    fn borrow_class_mut(&self) -> std::cell::RefMut<ObjectRef> {
        RefMut::map(self.0.header.refcell.borrow_mut(), |_| unsafe {
            &mut *(self.0.header.value.get())
        })
    }

    fn borrow_fields_mut(&self) -> std::cell::RefMut<[Value]> {
        RefMut::map(self.0.header.refcell.borrow_mut(), |_| {
            // SAFETY: self.slice will not be accessed unless by one of these methods that borrows
            // the refcell first
            // SAFETY: Idk if *[UnsafeCell<T>] -> *[T] is allowed or not
            unsafe {
                &mut *(UnsafeCell::raw_get(
                    &self.0.slice as *const [UnsafeCell<Value>] as *const UnsafeCell<[Value]>,
                ))
            }
        })
    }
}

/*
let Class = ClassObject

type MetaClassObject = Object {
    class = Class,
    values = [
        num_fields: Number,
        supertype: *ClassObject,
        name: String,
        methods: List<List<String, CodeAddress>>,
    ]
}

type ClassObject = Object {
    class = metaclass of this class,
    values = [
        num_fields: Number,
        supertype: *ClassObject,
        name: String,
        methods: List<List<String, CodeAddress>>,
    ]
}
*/
struct ClassObject {
    supertype: Option<&'static ClassObject>,
    num_fields: usize,
    name: String,
    methods: Vec<(String, CodeAddress)>,
}

impl ClassObject {
    unsafe fn cast_from_object(_obj: &ObjectRef) -> Self {
        todo!()
    }
}

impl ObjectRef {
    /// #Safety
    ///
    /// Class must be an instance of a class constructed
    /// This method should only be called by constructor code which is auto-generated by our
    /// compiler
    unsafe fn from_class(class: &ObjectRef) -> ObjectRef {
        let num_fields = unsafe { ClassObject::cast_from_object(class).num_fields };
        ObjectRef::new(
            class.clone(),
            exact_repeat::exact_repeat(num_fields, Value::Primitive(PrimitiveValue::Null)),
        )
    }

    fn find_method(&self, _name: &str) -> Option<CodeAddress> {
        todo!()
    }
}

struct FunctionObject {
    arity: usize,
    code: CodeAddress,
    closure: ObjectRef,
}

#[cfg(test)]
mod test {
    use super::*;
    #[test]
    fn bootstrap() {
        let (class, object, object_meta) = bootstrap_class();

        // Clear all fields (supertype etc.) so that there are no cycles other than Class -> Class
        for field in object.borrow_fields_mut().iter_mut() {
            *field = Value::null();
        }
        for field in object_meta.borrow_fields_mut().iter_mut() {
            *field = Value::null();
        }
        for field in class.borrow_fields_mut().iter_mut() {
            *field = Value::null();
        }

        // Should deallocate object and object_meta since they are not referenced by class
        drop(object);
        drop(object_meta);
        drop_self_class(class);
    }
}

/// Safely drop an object which is its own class
fn drop_self_class(class: ObjectRef) /* -> Result<(), > */
{
    // If we hold the only non-cyclical reference to class, and class's class is still itself
    if Rc::strong_count(&class.0) == 2 && Rc::ptr_eq(&class.0, &class.borrow_class().0) {
        let obj = Rc::into_raw(class.0) as *const std::mem::ManuallyDrop<Object>;
        unsafe {
            // Decrement the count to account for the ref inside of class that is no longer
            // going to run its drop code
            Rc::decrement_strong_count(obj);

            // Drop the final reference and deallocate the ManuallyDrop<Object>
            let manual = Rc::<std::mem::ManuallyDrop<Object>>::from_raw(obj);
        }
    }
}
