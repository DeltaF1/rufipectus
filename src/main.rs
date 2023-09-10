#![deny(unsafe_op_in_unsafe_fn)]
use std::borrow::Cow;
use std::cell::Cell;
use std::collections::{HashMap, HashSet};

mod bytecode;
use bytecode::Assembler;
use bytecode::Lookup;

mod runtime;

type CodeAddress = u32;

#[derive(Debug, Default)]
struct InitializedOrderedSet<T> {
    items: Vec<T>,
    written_items: HashSet<T>,
}

impl<T: Default> InitializedOrderedSet<T> {
    fn new() -> Self {
        Default::default()
    }
}

impl<T> InitializedOrderedSet<T>
where
    T: std::cmp::Eq + std::hash::Hash,
{
    fn get_or_insert(&mut self, item: T) -> usize {
        self.get_index(&item).unwrap_or_else(|| {
            self.items.push(item);
            self.items.len() - 1
        })
    }

    pub fn get_index(&self, item: &T) -> Option<usize> {
        self.items.iter().position(|o| o == item)
    }

    pub fn read_use(&mut self, item: T) -> usize {
        self.get_or_insert(item)
    }

    pub fn validate(self) -> Option<Vec<T>> {
        for item in &self.items {
            if !self.written_items.contains(item) {
                return None;
            }
        }
        Some(self.items)
    }
}

impl<T> InitializedOrderedSet<T>
where
    T: std::cmp::Eq + std::hash::Hash + Copy,
{
    pub fn write_use(&mut self, item: T) -> usize {
        self.written_items.insert(item);
        self.get_or_insert(item)
    }
}

#[derive(PartialEq, Debug, Clone)]
enum Primitive {
    Bool(bool),
    Number(f64),
    String(*const [u8]),
    Range(isize, isize, bool),
    Null,
}

#[derive(Default, Debug, Clone)]
enum Type<'a> {
    #[default]
    Unknown,
    KnownType(BroadType),
    KnownPrimitive(Primitive),
    KnownClassOrSubtype(&'a ClassDef<'a>),
    KnownClass(&'a ClassDef<'a>), // Only possible to glean from constructors
}

impl<'a> PartialEq for Type<'a> {
    fn eq(&self, other: &Type<'a>) -> bool {
        match (self, other) {
            (Type::Unknown, Type::Unknown) => true,
            (Type::KnownType(b1), Type::KnownType(b2)) => b1 == b2,
            (Type::KnownPrimitive(p1), Type::KnownPrimitive(p2)) => p1 == p2,
            (Type::KnownClassOrSubtype(c1), Type::KnownClassOrSubtype(c2)) => {
                std::ptr::eq(c1 as *const _, c2 as *const _)
            }
            (Type::KnownClass(c1), Type::KnownClass(c2)) => {
                std::ptr::eq(c1 as *const _, c2 as *const _)
            }
            _ => false,
        }
    }
}

impl Type<'_> {
    fn discrim(&self) -> u8 {
        match self {
            Type::Unknown => 0,
            Type::KnownType(_) => 1,
            Type::KnownPrimitive(_) => 2,
            Type::KnownClassOrSubtype(_) => 3,
            Type::KnownClass(_) => 4,
        }
    }

    fn truthiness(&self) -> Option<bool> {
        match self {
            Type::Unknown => None,
            Type::KnownType(_) => Some(true),
            Type::KnownPrimitive(p) => match p {
                Primitive::Null => Some(false),
                Primitive::Bool(b) => Some(*b),
                _ => Some(true),
            },
            // TODO: Can classes override truthiness?
            Type::KnownClassOrSubtype(_) => Some(true),
            Type::KnownClass(_) => Some(true),
        }
    }
}

use std::ops::BitOr;
impl<'text> BitOr<Type<'text>> for Type<'text> {
    type Output = Type<'text>;

    fn bitor(self, other: Type<'text>) -> <Self as BitOr<Type<'text>>>::Output {
        if self == other {
            return self;
        }

        let (a, b);
        if self.discrim() < other.discrim() {
            (a, b) = (self, other);
        } else {
            (a, b) = (other, self)
        }

        match (a, b) {
            (Type::Unknown, _) => Type::Unknown,
            (Type::KnownType(b1), Type::KnownType(b2)) => {
                if b1 == b2 {
                    Type::KnownType(b1)
                } else {
                    Type::Unknown
                }
            }
            (Type::KnownType(BroadType::Object), Type::KnownClass(_)) => {
                Type::KnownType(BroadType::Object)
            }
            (Type::KnownType(BroadType::Object), Type::KnownClassOrSubtype(_)) => {
                Type::KnownType(BroadType::Object)
            }
            (Type::KnownType(BroadType::Object), Type::KnownPrimitive(_)) => Type::Unknown,
            (Type::KnownType(_), Type::KnownPrimitive(Primitive::Null)) => Type::Unknown,
            (Type::KnownType(b), Type::KnownPrimitive(p)) => {
                if b == (&p).into() {
                    Type::KnownType(b)
                } else {
                    Type::Unknown
                }
            }
            (Type::KnownPrimitive(p1), Type::KnownPrimitive(p2)) => {
                if p1 == p2 {
                    Type::KnownPrimitive(p1)
                } else if Into::<BroadType>::into(&p1) == (&p2).into() {
                    Type::KnownType((&p1).into())
                } else {
                    Type::Unknown
                }
            }
            (Type::KnownClassOrSubtype(c1), Type::KnownClass(c2))
            | (Type::KnownClassOrSubtype(c1), Type::KnownClassOrSubtype(c2)) => {
                if std::ptr::eq(c1, c2) {
                    Type::KnownClassOrSubtype(c1)
                } else if c2.is_subclass_of(c1) {
                    Type::KnownClassOrSubtype(c1)
                } else if c1.is_subclass_of(c2) {
                    Type::KnownClassOrSubtype(c2)
                } else {
                    Type::Unknown
                }
            }
            (Type::KnownClass(c1), Type::KnownClass(c2)) => {
                if std::ptr::eq(c1, c2) {
                    Type::KnownClass(c1)
                } else if c2.is_subclass_of(c1) {
                    Type::KnownClassOrSubtype(c1)
                } else if c1.is_subclass_of(c2) {
                    Type::KnownClassOrSubtype(c2)
                } else {
                    Type::Unknown
                }
            }
            (Type::KnownType(_), _) => Type::Unknown,
            (x, y) => panic!("Unforseen type combination ({x:?}, {y:?})"),
        }
    }
}

#[derive(PartialEq, Debug, Clone, Copy)]
// TODO: Replace with runtime::GlobalClassSlots
enum BroadType {
    Object,
    Bool,
    Number,
    String,
    Range,
}

impl From<&Primitive> for BroadType {
    fn from(p: &Primitive) -> BroadType {
        match p {
            Primitive::Bool(_) => BroadType::Bool,
            Primitive::String(_) => BroadType::String,
            Primitive::Number(_) => BroadType::Number,
            Primitive::Range(..) => BroadType::Range,
            Primitive::Null => panic!(),
        }
    }
}

#[derive(PartialEq, Eq, Hash, Debug, Clone, Copy)]
pub enum Arity {
    Getter,
    Setter,
    SubscriptGetter(usize),
    SubscriptSetter(usize),
    Func(usize),
}

impl Arity {
    pub fn arity(&self) -> usize {
        use Arity::*;
        match self {
            Getter => 0,
            Setter => 1,
            SubscriptGetter(n) => *n,
            SubscriptSetter(n) => *n + 1,
            Func(n) => *n,
        }
    }
}

#[derive(PartialEq, Eq, Hash, Debug, Clone)]
struct Signature<'a> {
    name: Cow<'a, str>,
    arity: Arity,
}

impl std::fmt::Display for Arity {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> Result<(), std::fmt::Error> {
        match *self {
            Arity::Getter => write!(f, ""),
            Arity::Setter => write!(f, "(_)"),
            Arity::Func(n) => {
                write!(f, "(")?;
                for _ in 1..n {
                    write!(f, "_,")?;
                }
                if n > 0 {
                    write!(f, "_")?;
                }
                write!(f, ")")
            }
            Arity::SubscriptGetter(n) => {
                write!(f, "[")?;
                for _ in 1..n {
                    write!(f, "_,")?;
                }

                if n > 0 {
                    write!(f, "_")?;
                }
                write!(f, "]")
            }
            Arity::SubscriptSetter(n) => {
                write!(f, "[")?;
                for _ in 1..n {
                    write!(f, "_,")?;
                }

                if n > 0 {
                    write!(f, "_")?;
                }
                write!(f, "]=(_)")
            }
        }
    }
}

impl std::fmt::Display for Signature<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> Result<(), std::fmt::Error> {
        write!(f, "{}{}", self.name, self.arity)
    }
}

impl<'a> From<&'a str> for Signature<'a> {
    fn from(name: &'a str) -> Signature {
        Signature {
            name: name.into(),
            arity: Arity::Func(0),
        }
    }
}

impl<'a> Signature<'a> {
    pub fn getter(name: &'a str) -> Self {
        Signature {
            name: name.into(),
            arity: Arity::Getter,
        }
    }

    pub fn setter(name: &'a str) -> Self {
        Signature {
            name: name.into(),
            arity: Arity::Setter,
        }
    }

    pub fn func(name: &'a str, n: usize) -> Self {
        Signature {
            name: name.into(),
            arity: Arity::Func(n),
        }
    }
}

impl Signature<'_> {
    /*
    pub fn parse(name: &'static str) -> Self {
        if name.contains("=") {
            Signature::setter(name)
        } else if !name.contains("(") {
            Signature::getter(name)
        } else {
            Signature::func(name, name.count(",") + !name.contains("()"))
        }
    }
    */
}
#[derive(Default, Debug)]
struct ClassBuilder<'a> {
    class: ClassDef<'a>,
    fields: InitializedOrderedSet<&'a str>,
    static_fields: InitializedOrderedSet<&'a str>,
}

struct MethodAst<'a> {
    ast: Statement<'a>,
}

#[derive(Default)]
struct ClassDef<'text> {
    name: Cow<'text, str>,
    // TODO: Rc<ClassDef<'text>>
    parent: Option<&'text ClassDef<'text>>,
    static_fields: Vec<&'text str>,
    fields: Vec<&'text str>,
    methods: HashMap<Signature<'text>, Cell<MethodAst<'text>>>,
}

impl std::fmt::Debug for ClassDef<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> Result<(), std::fmt::Error> {
        let un_celled = self
            .methods
            .iter()
            .map(|(k, v)| -> (&Signature, *const MethodAst) { (k, v.as_ptr()) });
        f.debug_struct("ClassDef")
            .field("name", &self.name)
            .field("parent", &self.parent.map(|p| p.name))
            .field("fields", &self.fields)
            .field("static_fields", &self.static_fields)
            .field(
                "methods",
                &un_celled
                    .map(|(k, v)| -> (&Signature, &MethodAst) {
                        // SAFETY: No &mut references will be made to this data before this function
                        // returns. In fact no &mut references *can* be made because we only have an
                        // immutable borrow for self/the Cell.
                        unsafe { (k, &*v) }
                    })
                    .collect::<HashMap<_, _>>(),
            )
            .finish()
    }
}

impl std::fmt::Debug for &MethodAst<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> Result<(), std::fmt::Error> {
        write!(f, "Method: {:?}", self.ast)
    }
}

impl<'a> ClassDef<'a> {
    fn new(name: Cow<'a, str>) -> Self {
        ClassDef {
            name,
            ..Default::default()
        }
    }

    pub fn is_subclass_of(&self, other: &ClassDef<'a>) -> bool {
        let mut current = self;

        while let Some(ancestor) = current.parent {
            if std::ptr::eq(ancestor, other) {
                return true;
            }

            current = ancestor;
        }

        false
    }

    pub fn child_of(&'a self, name: &'a str) -> ClassBuilder<'a> {
        ClassBuilder {
            class: ClassDef {
                name,
                parent: Some(self),
                ..Default::default()
            },
            ..Default::default()
        }
    }

    fn num_parent_fields(&self) -> usize {
        self.parent.map_or(0, ClassDef::num_fields)
    }

    fn num_fields(&self) -> usize {
        self.fields.len() + self.num_parent_fields()
    }

    pub fn get_field_index(&self, name: &str) -> Option<usize> {
        self.fields
            .iter()
            .position(|f| f == &name)
            .map(|existing| existing + self.num_parent_fields())
    }

    pub fn get_static_field_index(&self, name: &str) -> Option<usize> {
        self.static_fields.iter().position(|sf| sf == &name)
    }

    pub fn find_method(&self, sig: &Signature<'a>) -> Option<&'a Cell<MethodAst>> {
        let mut next = Some(self);
        while let Some(cls) = next {
            if let Some(cell) = cls.methods.get(sig) {
                return Some(cell);
            }
            next = cls.parent;
        }
        None
    }

    fn find_class_with_method(&self, sig: &Signature<'a>) -> Option<&ClassDef<'a>> {
        if self.methods.contains_key(sig) {
            Some(self)
        } else {
            self.parent
                .and_then(|parent| parent.find_class_with_method(sig))
        }
    }

    /// Only used for debugging
    fn find_field_in_parents(&self, name: &str) -> Option<(&ClassDef<'a>, usize)> {
        let mut to_search = self.parent;

        while let Some(class) = to_search {
            to_search = class.parent;
            if let Some(i) = class.get_field_index(name) {
                return Some((class, i));
            }
        }

        None
    }
}

impl<'a> ClassBuilder<'a> {
    pub fn new(name: &'a str) -> Self {
        ClassBuilder {
            class: ClassDef::new(name.into()),
            ..Default::default()
        }
    }

    pub fn write_field(&mut self, name: &'a str) -> usize {
        self.check_shadowed_field(name);
        self.fields.write_use(name) + self.class.num_parent_fields()
    }

    pub fn read_field(&mut self, name: &'a str) -> usize {
        self.check_shadowed_field(name);
        self.fields.read_use(name) + self.class.num_parent_fields()
    }

    fn check_shadowed_field(&self, name: &str) {
        if true
        /* config.WARNINGS */
        {
            if let Some((parent, _)) = self.class.find_field_in_parents(name) {
                println!("WARNING: field {} has same name as superclass {}. Remember that subclasses cannot access superclass fields", name, parent.name)
            }
        }
    }

    // TODO: Static fields can just be globals
    pub fn write_static_field(&mut self, name: &'a str) -> usize {
        self.static_fields.write_use(name) // + globals.len()
    }

    pub fn read_static_field(&mut self, name: &'a str) -> usize {
        self.static_fields.read_use(name) // + globals.len()
    }

    /*
    pub fn static_field(&mut self, name: &'a str) -> StaticVariable {
       if let Some(index) = self.class.static_fields.get(name) {
           StaticVariable::Exists(*index)
       } else {
           self.class.static_fields.insert(name, current);
           StaticVariable::New(current)
       }
    }
    */

    pub fn add_method<F>(&mut self, name: Signature<'a>, f: F) -> &Cell<MethodAst<'a>>
    where
        F: Fn(&mut Self) -> MethodAst<'a>,
    {
        // This is necessary because the .get gets confused about the borrow otherwise
        #[allow(clippy::map_entry)]
        if !self.class.methods.contains_key(&name) {
            let cell = f(self).into();
            self.class.methods.insert(name.clone(), cell);
        }
        self.class.methods.get(&name).unwrap()
    }

    pub fn finish(self) -> ClassDef<'a> {
        let mut class = self.class;
        class.fields = self.fields.validate().unwrap();
        // TODO: Result type
        // panic!("Field {field} in class {} is never written to!", self.class.name)

        class.static_fields = self.static_fields.validate().unwrap();

        class
    }
}

/*
 class Rectangle {
   width { _width }
   height { _height }
   construct new (width, height) {
       _width = width
       _height = height
   }
   area() {
       return _width * _height
   }
 }

 class Square is Rectangle {
   construct new (width) {
        __classname = "Square"
        super(width, width)
   }

   hello {
        print("hello from%(__classname)")
   }

   foo { height }
 }

 var s = Square.new(10)
 s.hello
*/

#[deprecated]
#[derive(Debug)]
enum Ast<'a> {
    Statement(Statement<'a>),
    Expression(Expression<'a>),
}

// TODO: Expression statement
#[derive(Debug)]
enum Statement<'a> {
    WriteField(usize, Box<Expression<'a>>),
    AssignLocal(usize, Box<Expression<'a>>),
    AssignGlobal(usize, Box<Expression<'a>>),
    If(Box<Expression<'a>>, IfBody<'a>),
    Block(Vec<Statement<'a>>),
    Return(Expression<'a>),
    ExprStatement(Expression<'a>),
}

#[derive(Debug)]
enum Expression<'a> {
    Call(Box<Expression<'a>>, AstSig<'a>),
    ThisCall(AstSig<'a>),
    SuperCall(AstSig<'a>),
    ReadField(usize),
    ReadStatic(usize),
    GlobalLookup(usize),
    ArgLookup(usize),
    LocalLookup(usize),
    Ternary(
        Box<Expression<'a>>,
        Box<Expression<'a>>,
        Box<Expression<'a>>,
    ),
    Primitive(Primitive),
}

#[derive(Debug)]
enum IfBody<'a> {
    ThenElse {
        then: Box<Statement<'a>>,
        r#else: Box<Statement<'a>>,
    },
    Then {
        then: Box<Statement<'a>>,
    },
    ThenElseIf {
        then: Box<Statement<'a>>,
        elseif: (Box<Expression<'a>>, Box<IfBody<'a>>),
    },
}

#[derive(Debug)]
enum AstSig<'a> {
    Getter(Cow<'a, str>),
    Setter(Cow<'a, str>, Box<Expression<'a>>),
    Func(Cow<'a, str>, Vec<Expression<'a>>),
}

impl<'a> From<&'a AstSig<'_>> for Signature<'a> {
    fn from(other: &'a AstSig) -> Self {
        match other {
            AstSig::Getter(s) => Signature::getter(s),
            AstSig::Setter(s, _) => Signature::setter(s),
            AstSig::Func(s, v) => Signature::func(s, v.len()),
        }
    }
}

#[derive(Default)]
struct Scope<'text> {
    names: Vec<&'text str>,
}

impl<'text> Scope<'text> {
    fn new() -> Self {
        Default::default()
    }

    fn declare(&mut self, name: &'text str) -> usize {
        if self.names.contains(&name) {
            panic!("Name {name} already exists in scope")
        }
        self.names.push(name);
        self.names.len() - 1
    }

    fn get_index(&self, name: &'text str) -> Option<usize> {
        self.names.iter().position(|n| n == &name)
    }
}

fn main() {
    let mut globals = Scope::new();
    let mut classes: Vec<&ClassDef> = vec![];
    let mut Rectangle = ClassBuilder::new("Rectangle");

    Rectangle.add_method(Signature::getter("width"), |class| {
        dbg!(class.read_field("_width"));
        MethodAst {
            ast: Statement::Return(Expression::ReadField(
                class.read_field("_width"),
            )),
        }
    });
    /*
    // if existing, error with "duplicate method"
    bytecode.emit(
        ByteCode::LoadThis(Rectangle.field("_width"))
    );
    bytecode.finish_function();
    */

    Rectangle.add_method(Signature::getter("height"), |class| {
        dbg!(class.read_field("_height"));
        MethodAst {
            ast: Statement::Return(Expression::ReadField(
                class.read_field("_height"),
            )),
        }
        /*
        // if existing, error with "duplicate method"
        bytecode.emit(
            ByteCode::LoadThis(Rectangle.field("_height"))
        );
        bytecode.finish_function();
        */
    });

    // TODO: add_constructor
    Rectangle.add_method(Signature::func("new init", 2), |class| {
        dbg!(class.write_field("_width"));
        dbg!(class.write_field("_height"));
        MethodAst {
            ast: Statement::Block(vec![
                Statement::WriteField(
                    class.write_field("_width"),
                    Box::new(Expression::ArgLookup(0)),
                ),
                Statement::WriteField(
                    class.write_field("_height"),
                    Box::new(Expression::ArgLookup(1)),
                ),
            ]),
        }
    });
    /*
    // wrapper for
    // bytecode.emit(
    //  ByteCode::New(Rectangle.new_fixup(Fixup::ClassNumFields))
    // )
    bytecode.emit(ByteCode::LoadArg(0));
    bytecode.emit(ByteCode::StoreThis(Rectangle.field("_width")));
    bytecode.emit(ByteCode::LoadArg(1));
    bytecode.emit(ByteCode::StoreThis(Rectangle.field("_height")));
    bytecode.finish_function();

    */
    Rectangle.add_method(Signature::func("area", 0), |class| {
        dbg!(class.read_field("_width"));
        dbg!(class.read_field("_height"));

        MethodAst {
            ast: Statement::Return(Expression::Call(
                Box::new(Expression::ReadField(class.read_field("_width"))),
                AstSig::Func(
                    "*".into(),
                    vec![Expression::ReadField(class.read_field("_height"))],
                ),
            )),
        }

        /*
        bytecode.emit(ByteCode::LoadThis(Rectangle.field("_width")));
        bytecode.emit(ByteCode::LoadThis(Rectangle.field("_height")));
        bytecode.emit(ByteCode::CallDynamic("*"));
            // Should the string go inline or in a bundle at the end of the function?
            // if it's a hotpath then could be better for caching
            // if it's a coldpath it could cause the hotpath to be farther away
        bytecode.finish_function();
        */
    });
    /*
    // Embed strings as a jump op followed by the string. if the string needs to be longer than 127
    // bytes, another jump op is emitted

    // End of rectangle class declaration
    Rectangle.fixup(Fixup::ClassNumFields, Rectangle.num_fields());
    // TODO: Generate runtime code to create the class object
    // PushPrimitive("Rectangle")
    // PushPrimitive(Rectangle.num_fields())
    // Push ??? (Rectangle's methods)
    // PushGlobal(xxx) // Class
    //

    */
    let Rectangle = Rectangle.finish();
    classes.push(&Rectangle);
    globals.declare("Rectangle");
    let mut Square = Rectangle.child_of("Square");
    // TODO: Creates a static method called "new" with auto-generated constructor code,
    // and an instance method called "new init". The
    // space makes it uncallable by normal code
    Square.add_method(Signature::func("new init", 0), |class| {
        /*
        bytecode.emit(ByteCode::PushConst("Square"));
        bytecode.emit(ByteCode::StoreStatic(Square.static_field("__classname")));
        bytecode.emit(ByteCode::LoadArg(0));
        bytecode.emit(ByteCode::LoadArg(0));
        */
        dbg!(class.write_static_field("__classname"));
        let sig = Signature::func("new init", 2);
        if let Some(index) = class
            .class
            .parent
            .and_then(|parent| parent.find_method(&sig))
        {
            /*
            bytecode.emit(ByteCode::CallAddress(index));
            */
        } else {
            panic!("Can't call super here: no such method {sig} in parent");
        }
        MethodAst {
            ast: Statement::Return(Expression::SuperCall(AstSig::Func(
                "new".into(),
                vec![Expression::ArgLookup(0), Expression::ArgLookup(0)],
            ))),
        }
    });
    /*
    bytecode.finish_function();
    */
    Square.add_method(Signature::getter("hello"), |class| {
        dbg!(class.read_static_field("__classname"));
        MethodAst {
            ast: Statement::Return(Expression::Call(
                Box::new(Expression::GlobalLookup(0 /* globals.read("System")*/)),
                AstSig::Func(
                    "print".into(),
                    vec![Expression::ReadStatic(
                        class.read_static_field("__classname"),
                    )],
                ),
            )),
        }
        /*
            bytecode.emit(ByteCode::LoadStatic(Square.static_field("__classname")));
            bytecode.emit(ByteCode::PushConst("hello from%()"));
            bytecode.emit(ByteCode::CallAddress(todo!("stdlib addresses should be known at compile time")));
            bytecode.finish_function();
        */
    });
    Square.add_method(Signature::getter("foo"), |class| {
        MethodAst {
            ast: Statement::Return(Expression::ThisCall(AstSig::Getter("height".into()))),
        }
        /*
            let word = "height";
            if let Some(index) = bytecode.function.get_local(word) {
                bytecode.emit(ByteCode::PushLocal(index));
            } else if word[0].is_lowercase() {
                // Can't CallAddress here because the method might be re-defined by a subclass
                // We can actually determine that statically but it requires a second-pass or some really
                // messy fixups
                // TODO: Keep track of whether a super-classes method was redefined by some further
                // subclass. If a method M for class A is the last version of M (i.e. there are no
                // subclasses of A that define M) then any call to M for an object that is known
                // at compile-time to be of type A can have the method's location compiled in.
                bytecode.emit(ByteCode::CallDynamic(word));
            } else {
                todo!("Recurse the lexical stack looking for locals")
            }
            bytecode.finish_function();
        */
    });
    /*
    bytecode.add_local("s");
    bytecode.emit(ByteCode::PushLocal(bytecode.function.get_local("Square")));
    bytecode.emit(ByteCode::CallDynamic("new"));
    bytecode.emit(ByteCode::StoreLocal(bytecode.function.get_local("s")));

    bytecode.emit(ByteCode::LoadLocal(bytecode.function.get_local("s")));
    bytecode.emit(ByteCode::CallDynamic("hello"));

    */
    let Square = Square.finish();
    classes.push(&Square);
    globals.declare("Square");
    dbg!(&Square);
    dbg!(&Rectangle);

    // TODO: Generate ast for _start to init classes as classdefs are created

    let top_level_ast = Statement::Block(vec![
        Statement::AssignGlobal(
            globals.declare("s"),
            Box::new(Expression::Call(
                Box::new(Expression::GlobalLookup(
                    globals.get_index("Square").unwrap(),
                )),
                AstSig::Func("new".into(), vec![]),
            )),
        ),
        Statement::ExprStatement(Expression::Call(
            Box::new(Expression::GlobalLookup(globals.get_index("s").unwrap())),
            AstSig::Getter("hello".into()),
        )),
    ]);

    dbg!(&top_level_ast);

    #[derive(Debug)]
    struct ClassMethodPair<'a, 'text>(&'a ClassDef<'text>, Signature<'text>);

    impl Eq for ClassMethodPair<'_, '_> {}
    impl<'a, 'text> PartialEq for ClassMethodPair<'a, 'text> {
        fn eq(&self, other: &ClassMethodPair<'a, 'text>) -> bool {
            std::ptr::eq(self.0 as *const _, other.0 as *const _) && self.1 == other.1
        }
    }

    use std::hash::Hash;
    impl Hash for ClassMethodPair<'_, '_> {
        fn hash<H>(&self, h: &mut H)
        where
            H: std::hash::Hasher,
        {
            std::ptr::hash(self.0, h);
            self.1.hash(h);
        }
    }

    let mut latest_implementation: HashMap<ClassMethodPair, &ClassDef> = HashMap::new();

    // Prepare class information to lookup methods more efficiently

    fn ancestors<'a, 'text>(class: &'a ClassDef<'text>) -> Vec<&'a ClassDef<'text>> {
        let mut vec = vec![];
        let mut current = class;
        while let Some(parent) = current.parent {
            vec.push(parent);
            current = parent;
        }
        vec
    }

    // Because classes is in creation-order, this will overwrite properly
    for class in classes {
        for ancestor in ancestors(class) {
            for method in ancestor.methods.keys() {
                latest_implementation.insert(ClassMethodPair(class, method.clone()), ancestor);
            }

            for method in class.methods.keys() {
                latest_implementation.remove(&ClassMethodPair(ancestor, method.clone()));
            }
        }
        for method in class.methods.keys() {
            latest_implementation.insert(ClassMethodPair(class, method.clone()), class);
        }
    }

    dbg!(latest_implementation
        .iter()
        .map(|(k, v)| {
            let ClassMethodPair(c1, m) = k;
            let c2 = v;

            ((c1.name, m.to_string()), c2.name)
        })
        .collect::<Vec<_>>());

    enum CallTarget<'a, 'text> {
        Dynamic(Signature<'text>),
        Static(&'a ClassDef<'text>, Signature<'text>),
    }

    fn resolve_call_target<'a, 'text>(
        x: &'a (),
        typ: Type<'text>,
        sig: Signature<'text>,
    ) -> CallTarget<'a, 'text> {
        let classes: HashMap<&'static str, ClassDef> = HashMap::new();
        let latest_implementation: HashMap<ClassMethodPair, &ClassDef> = HashMap::new();
        let call = match typ {
            Type::Unknown | Type::KnownType(BroadType::Object) => CallTarget::Dynamic(sig),
            Type::KnownType(BroadType::Bool) => CallTarget::Static(&classes["Bool"], sig),
            Type::KnownType(BroadType::Number) => CallTarget::Static(&classes["Num"], sig),
            Type::KnownType(BroadType::String) => CallTarget::Static(&classes["String"], sig),
            Type::KnownType(BroadType::Range) => CallTarget::Static(&classes["Range"], sig),
            Type::KnownPrimitive(p) => {
                todo!("Match p and recurse with appropriate BroadType")
            }
            Type::KnownClassOrSubtype(class) => {
                let latest = latest_implementation.get(&ClassMethodPair(class, sig.clone()));
                if let Some(latest) = latest {
                    CallTarget::Static(latest, sig)
                } else {
                    CallTarget::Dynamic(sig)
                }
            }
            Type::KnownClass(class) => {
                if let Some(target) = class.find_class_with_method(&sig) {
                    CallTarget::Static(target, sig)
                } else {
                    panic!(
                        "Statically determined it's impossible to call {sig} for class {0}",
                        class.name
                    )
                }
            }
        };
        todo!("Lifetimes")
    }

    fn type_of_expr<'a, 'text>(
        ast: &'a Expression<'text>,
        this_type: Option<&'a ClassDef<'text>>,
    ) -> Type<'text>
    where
        'a: 'text,
    {
        match ast {
            Expression::Call(receiver, ast_sig) => {
                let receiver_type = type_of_expr(receiver, this_type);
                let target = resolve_call_target(&(), receiver_type, ast_sig.into());
                match target {
                    CallTarget::Dynamic(_) => Type::Unknown,
                    CallTarget::Static(cls, sig) => {
                        todo!("Magic to determine if this method is a constructor")
                        // if cls.is_constructor(sig) {
                        //      Type::KnownClass(cls)
                        // } else {
                        //      Type::Unknown
                        // }
                    }
                }
            }
            Expression::SuperCall(ast_sig) => {
                todo!()
            }
            Expression::ThisCall(ast_sig) => {
                let receiver_type = Type::KnownClassOrSubtype(this_type.unwrap());
                let target = resolve_call_target(&(), receiver_type, ast_sig.into());
                match target {
                    CallTarget::Dynamic(_) => Type::Unknown,
                    CallTarget::Static(cls, sig) => {
                        todo!("Magic to determine if this method is a constructor")
                        // if cls.is_constructor(sig) {
                        //      Type::KnownClass(cls)
                        // } else {
                        //      Type::Unknown
                        // }
                    }
                }
            }
            Expression::ArgLookup(_) => {
                // TODO: Are there any arg types that are statically known?
                Type::Unknown
            }
            Expression::Ternary(_condition, then, r#else) => {
                match type_of_expr(_condition, this_type).truthiness() {
                    Some(true) => type_of_expr(then, this_type),
                    Some(false) => type_of_expr(r#else, this_type),
                    None => type_of_expr(then, this_type) | type_of_expr(r#else, this_type),
                }
            },
            Expression::Primitive(p) => {
                Type::KnownPrimitive(p.clone())
            },
            Expression::ReadField(_)
            | Expression::ReadStatic(_)
            | Expression::GlobalLookup(_)
            | Expression::LocalLookup(_) => Type::Unknown,
        }
    }

    let mut asm = Assembler::new();
    // -> next stages
    // return (vec![Rectangle, Square], top_level_ast)
}

// TODO:
//
// Store all methods in inheritance tree as a list, then can search backwards to find the most
// recent implementation of a method. each class object points into its location in this list
//
// class A {
//  foo
// }
//
// class B is A {
//  bar
// }
//
// class C is B {
//  foo
//  baz
// }
//
// class D is B {
//  bang
// }
//
// class E is D {
//  baz
//  foo
//  bar
// }
//
// A -> B -> C
//       \-> D -> E
//
//         END
//      +-------+
//      |  foo  |
// A -->+-------+
//      |  bar  |
// B -->+-------+<--
//      |  foo  |  |
//      +-------+  |
//      |  baz  |  |  D doesn't inherit from C, so skip over
// C -->+-------+  |  it to get to D's superclass
//      +-------+--+
//      | bang  |
// D -->+-------+
//      |  baz  |
//      +-------+
//      |  foo  |
//      +-------+
//      |  bar  |
// E -->+-------+
//
// To search, start at the pointer for the class then scan upwards for the matching signature

#[cfg(test)]
mod type_tests {
    use super::*;

    fn test_type_commutative<'a>(a: Type<'a>, b: Type<'a>, expected: Type<'a>) {
        assert_eq!(a.clone() | b.clone(), expected.clone());
        assert_eq!(b | a, expected);
    }

    #[test]
    fn same_types() {
        test_type_commutative(Type::Unknown, Type::Unknown, Type::Unknown);
    }
}
