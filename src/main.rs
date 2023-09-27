#![deny(unsafe_op_in_unsafe_fn)]
use std::borrow::Cow;
use std::cell::{Cell, UnsafeCell};
use std::collections::{HashMap, HashSet};

use std::fs::File;
use std::io::Read;
use std::rc::{Rc, Weak};

mod ast;
mod common;
mod parser;

mod bytecode;
use ast::{Expression, Signature, Statement};
use bytecode::{Assembler, Lookup};

mod runtime;

#[derive(Debug, Default)]
struct InitializedOrderedSet<T> {
    items: Vec<T>,
    written_items: HashSet<T>,
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

    pub fn contains(&self, item: &T) -> bool {
        self.items.contains(item)
    }

    pub fn read_use(&mut self, item: T) -> usize {
        self.get_or_insert(item)
    }

    pub fn validate(mut self) -> Result<Vec<T>, T> {
        for (i, item) in self.items.iter().enumerate() {
            if !self.written_items.contains(item) {
                return Err(self.items.remove(i));
            }
        }
        Ok(self.items)
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

#[derive(Default, Clone)]
enum Type<'a> {
    Unknown,
    KnownType(BroadType),
    KnownPrimitive(ast::Primitive),
    KnownClassOrSubtype(Rc<ClassDef<'a>>),
    KnownClass(Rc<ClassDef<'a>>), // Only possible to glean from constructors
    #[default]
    Bottom,
}

impl std::fmt::Debug for Type<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Unknown => write!(f, "Unknown"),
            Self::KnownType(arg0) => f.debug_tuple("KnownType").field(arg0).finish(),
            Self::KnownPrimitive(arg0) => f.debug_tuple("KnownPrimitive").field(arg0).finish(),
            Self::KnownClassOrSubtype(arg0) => f
                .debug_tuple("KnownClassOrSubtype")
                .field(&arg0.name)
                .finish(),
            Self::KnownClass(arg0) => f.debug_tuple("KnownClass").field(&arg0.name).finish(),
            Self::Bottom => write!(f, "Bottom"),
        }
    }
}

impl<'a> BitOrAssign for Type<'a> {
    fn bitor_assign(&mut self, rhs: Self) {
        *self = self.clone() | rhs
    }
}

impl<'a> PartialEq for Type<'a> {
    fn eq(&self, other: &Type<'a>) -> bool {
        match (self, other) {
            (Type::Unknown, Type::Unknown) => true,
            (Type::KnownType(b1), Type::KnownType(b2)) => b1 == b2,
            (Type::KnownPrimitive(p1), Type::KnownPrimitive(p2)) => p1 == p2,
            (Type::KnownClassOrSubtype(c1), Type::KnownClassOrSubtype(c2)) => Rc::ptr_eq(c1, c2),
            (Type::KnownClass(c1), Type::KnownClass(c2)) => Rc::ptr_eq(c1, c2),
            (Type::Bottom, Type::Bottom) => true,
            _ => false,
        }
    }
}

impl Type<'_> {
    fn discrim(&self) -> u8 {
        match self {
            Type::Unknown => 0,
            // TODO: need a partialordering over knowntype and knownprimitive
            Type::KnownType(_) => 1,
            Type::KnownPrimitive(_) => 2,
            Type::KnownClassOrSubtype(_) => 3,
            Type::KnownClass(_) => 4,
            Type::Bottom => 5,
        }
    }

    fn truthiness(&self) -> Option<bool> {
        use ast::Primitive;
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
            Type::Bottom => panic!(),
        }
    }
}

use std::ops::{BitOr, BitOrAssign};
impl<'text> BitOr<Type<'text>> for Type<'text> {
    type Output = Type<'text>;

    fn bitor(self, other: Type<'text>) -> <Self as BitOr<Type<'text>>>::Output {
        use ast::Primitive;
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
                } else if p1 == Primitive::Null || p2 == Primitive::Null {
                    Type::Unknown
                } else if Into::<BroadType>::into(&p1) == (&p2).into() {
                    Type::KnownType((&p1).into())
                } else {
                    Type::Unknown
                }
            }
            (Type::KnownClassOrSubtype(c1), Type::KnownClass(c2))
            | (Type::KnownClassOrSubtype(c1), Type::KnownClassOrSubtype(c2)) => {
                if Rc::ptr_eq(&c1, &c2) {
                    Type::KnownClassOrSubtype(c1)
                } else if c2.is_subclass_of(&c1) {
                    Type::KnownClassOrSubtype(c1)
                } else if c1.is_subclass_of(&c2) {
                    Type::KnownClassOrSubtype(c2)
                } else {
                    Type::Unknown
                }
            }
            (Type::KnownClass(c1), Type::KnownClass(c2)) => {
                if Rc::ptr_eq(&c1, &c2) {
                    Type::KnownClass(c1)
                } else if c2.is_subclass_of(&c1) {
                    Type::KnownClassOrSubtype(c1)
                } else if c1.is_subclass_of(&c2) {
                    Type::KnownClassOrSubtype(c2)
                } else {
                    Type::Unknown
                }
            }
            (Type::KnownType(_), _) => Type::Unknown,
            (x, Type::Bottom) => x,
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

impl From<&ast::Primitive> for BroadType {
    fn from(value: &ast::Primitive) -> Self {
        value.clone().into()
    }
}

impl From<ast::Primitive> for BroadType {
    fn from(p: ast::Primitive) -> BroadType {
        match p {
            ast::Primitive::Bool(_) => BroadType::Bool,
            ast::Primitive::String(_) => BroadType::String,
            ast::Primitive::Number(_) => BroadType::Number,
            ast::Primitive::Range(..) => BroadType::Range,
            ast::Primitive::Null => panic!(),
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

#[derive(Default, Debug)]
struct ClassBuilder<'a> {
    class: ClassDef<'a>,
    meta_class: ClassDef<'a>,
    fields: InitializedOrderedSet<&'a str>,
    static_fields: InitializedOrderedSet<&'a str>,
}

#[derive(Debug)]
struct MethodAst<'a> {
    ast: Statement<'a>,
}

#[derive(Default)]
struct ClassDef<'text> {
    name: Cow<'text, str>,
    parent: UnsafeCell<Option<Rc<ClassDef<'text>>>>,
    metaclass: UnsafeCell<Option<Rc<ClassDef<'text>>>>,
    fields: Vec<&'text str>,
    methods: HashMap<Signature<'text>, MethodAst<'text>>,

    // Metaclass only fields
    constructors: HashSet<Signature<'text>>,
    constructor_type: Cell<Option<Weak<ClassDef<'text>>>>,
}

impl std::fmt::Debug for ClassDef<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> Result<(), std::fmt::Error> {
        f.debug_struct("ClassDef")
            .field("name", &self.name)
            // SAFETY: parents are never modified
            // Furthermore no references escape this method
            .field("parent", &unsafe { self.get_parent() }.map(|p| &p.name))
            .field("fields", &self.fields)
            .field("metaclass", &self.metaclass)
            .field("methods", &self.methods)
            .field("constructors", &self.constructors)
            .field("constructor type", {
                let steal = self.constructor_type.take();
                let name = steal
                    .as_ref()
                    .and_then(|weak| weak.upgrade())
                    .map(|class| class.name.clone().into_owned());
                self.constructor_type.set(steal);
                &format!("{:?}", name)
            })
            .finish()
    }
}

/*
impl std::fmt::Debug for &MethodAst<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> Result<(), std::fmt::Error> {
        write!(f, "Method: {:?}", self.ast)
    }
}
*/

impl<'a> ClassDef<'a> {
    fn new(name: Cow<'a, str>) -> Self {
        ClassDef {
            name,
            ..Default::default()
        }
    }

    pub fn is_subclass_of(&self, other: &ClassDef<'a>) -> bool {
        let mut current = self;

        // SAFETY: parents are never modified
        // Furthermore no references escape this method
        while let Some(ancestor) = unsafe { current.get_parent() } {
            if std::ptr::eq(&**ancestor, other) {
                return true;
            }

            current = &ancestor;
        }

        false
    }

    pub fn child_of(parent: &Rc<ClassDef<'a>>, name: &'a str) -> ClassBuilder<'a> {
        let mut builder = ClassBuilder {
            class: ClassDef {
                name: name.into(),
                parent: Some(parent.clone()).into(),
                ..Default::default()
            },
            meta_class: ClassDef::new((name.to_owned() + " metaclass").into()),
            ..Default::default()
        };

        if name == "Class" {
            builder.write_field(";numFields");
            builder.write_field(";supertype");
            builder.write_field(";name");
            builder.write_field(";methods");
        }
        builder
    }

    unsafe fn get_parent(&self) -> Option<&Rc<ClassDef<'a>>> {
        unsafe { &*self.parent.get() }.into()
    }

    unsafe fn get_meta_class(&self) -> Option<&Rc<ClassDef<'a>>> {
        // SAFETY: Caller must provide reference mutability guarantees
        unsafe { &*self.metaclass.get() }.into()
    }

    fn num_parent_fields(&self) -> usize {
        // SAFETY: parents are never modified
        // Furthermore no references escape this method
        unsafe { self.get_parent() }.map_or(0, |r| ClassDef::num_fields(&**r))
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

    pub fn find_method<'b>(&'b self, sig: &Signature<'a>) -> Option<&'b MethodAst<'a>> {
        let mut next = Some(self);
        while let Some(cls) = next {
            if let Some(method) = cls.methods.get(sig) {
                return Some(method);
            }
            // SAFETY: parents are never modified
            // Furthermore no references escape this method
            next = unsafe { cls.get_parent() }.map(|r| &**r);
        }
        None
    }

    pub fn find_super_method(&self, sig: &Signature<'a>) -> Option<&MethodAst<'a>> {
        // SAFETY: parents are never modified
        // Furthermore no references escape this method
        unsafe { self.get_parent() }?.find_method(sig)
    }

    fn find_class_with_method(self: &Rc<Self>, sig: &Signature<'a>) -> Option<Rc<ClassDef<'a>>> {
        if self.methods.contains_key(sig) {
            Some(self.clone())
        } else {
            // SAFETY: parents are never modified
            // Furthermore no references escape this method
            unsafe { self.get_parent() }
                .and_then(|parent| ClassDef::find_class_with_method(parent, sig))
        }
    }

    fn find_super_class_with_method(
        self: &Rc<Self>,
        sig: &Signature<'a>,
    ) -> Option<Rc<ClassDef<'a>>> {
        // SAFETY: parents are never modified
        // Furthermore no references escape this method
        unsafe { self.get_parent() }?.find_class_with_method(sig)
    }

    /// Only used for debugging
    fn find_field_in_parents(&self, name: &str) -> Option<(Rc<ClassDef<'a>>, usize)> {
        // SAFETY: parents are never modified
        // Furthermore no references escape this method
        let mut to_search = unsafe { self.get_parent() };

        while let Some(class) = to_search {
            // SAFETY: parents are never modified
            // Furthermore no references escape this method
            to_search = unsafe { class.get_parent() };
            if let Some(i) = class.get_field_index(name) {
                return Some((Rc::clone(&class), i));
            }
        }

        None
    }

    fn get_constructor_type(&self) -> Option<Rc<ClassDef<'a>>> {
        let steal = self.constructor_type.take();
        let clone = steal.clone();
        self.constructor_type.set(steal);

        clone.as_ref().and_then(Weak::upgrade)
    }
}

impl<'a> ClassBuilder<'a> {
    pub fn new(name: &'a str) -> Self {
        let mut builder = ClassBuilder {
            class: ClassDef::new(name.into()),
            meta_class: ClassDef::new((name.to_owned() + " metaclass").into()),
            ..Default::default()
        };

        // Every class has these 4 unaccessable fields. The ; ensures they won't be looked up by the parser
        if name == "Class" {
            builder.write_field(";numFields");
            builder.write_field(";supertype");
            builder.write_field(";name");
            builder.write_field(";methods");
        }
        builder
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

    pub fn write_static_field(&mut self, name: &'a str) -> usize {
        self.static_fields.write_use(name)
    }

    pub fn read_static_field(&mut self, name: &'a str) -> usize {
        self.static_fields.read_use(name)
    }

    pub fn add_constructor(
        &mut self,
        sig: Signature<'a>,
        mut body: MethodAst<'a>,
    ) -> &MethodAst<'a> {
        let init_sig = Signature {
            name: sig.name.to_owned() + " init",
            arity: sig.arity,
        };

        assert!(sig.arity.arity() <= 2);
        let mut args = vec![];
        for n in 0..sig.arity.arity() {
            args.push(Expression::ArgLookup(n));
        }

        self.meta_class.methods.insert(
            sig.clone(),
            MethodAst {
                ast: Statement::Return(Expression::Call(
                    Box::new(Expression::Construct),
                    AstSig::from_sig(init_sig.clone(), args),
                )),
            }
            .into(),
        );

        self.meta_class.constructors.insert(sig);

        if ast::missing_return(&body.ast) {
            match &mut body.ast {
                Statement::Block(v) => v.push(Statement::Return(Expression::This)),
                _ => {
                    body.ast = Statement::Block(vec![body.ast, Statement::Return(Expression::This)])
                }
            }
        }

        // TODO: Error if any returns inside body return anything other than `this`

        self.add_method(init_sig, body)
    }

    pub fn add_constructor_with<F>(&mut self, sig: Signature<'a>, mut f: F) -> &MethodAst<'a>
    where
        F: FnMut(&mut Self) -> MethodAst<'a>,
    {
        let body = f(self).into();
        self.add_constructor(sig, body)
    }

    pub fn add_static_method(&mut self, sig: Signature<'a>, body: MethodAst<'a>) -> &MethodAst<'a> {
        self.meta_class.methods.insert(sig.clone(), body);
        self.meta_class.methods.get(&sig).unwrap()
    }

    pub fn add_static_method_with<F>(&mut self, sig: Signature<'a>, mut f: F) -> &MethodAst<'a>
    where
        F: FnMut(&mut Self) -> MethodAst<'a>,
    {
        // This is necessary because the .get gets confused about the borrow otherwise
        #[allow(clippy::map_entry)]
        if !self.meta_class.methods.contains_key(&sig) {
            let cell = f(self).into();
            self.meta_class.methods.insert(sig.clone(), cell);
        }
        self.meta_class.methods.get(&sig).unwrap()
    }

    pub fn add_method(&mut self, sig: Signature<'a>, body: MethodAst<'a>) -> &MethodAst<'a> {
        self.class.methods.insert(sig.clone(), body.into());
        self.class.methods.get(&sig).unwrap()
    }

    pub fn add_method_with<F>(&mut self, sig: Signature<'a>, mut f: F) -> &MethodAst<'a>
    where
        F: FnMut(&mut Self) -> MethodAst<'a>,
    {
        let body = f(self).into();
        self.add_method(sig, body)
    }

    pub fn finish(self, class_class: Option<Rc<ClassDef<'a>>>) -> Rc<ClassDef<'a>> {
        let mut class = self.class;
        let mut meta_class = self.meta_class;
        class.fields = self
            .fields
            .validate()
            .expect("A field was never written to!");
        // TODO: Result type
        // panic!("Field {field} in class {} is never written to!", self.class.name)

        meta_class.fields = self.static_fields.validate().unwrap();
        meta_class.parent = class_class.into();
        class.metaclass = Some(Rc::new(meta_class)).into();
        let class = Rc::new(class);
        let weak = Rc::downgrade(&class);

        // SAFETY: This is an owning reference to class so nothing else will be modifying it
        // Furthermore no references escape this method
        unsafe { class.get_meta_class() }
            .unwrap()
            .constructor_type
            .set(Some(weak));

        class
    }
}

#[derive(Default, Clone, Debug)]
struct Scope<'text> {
    shadowed: Option<Vec<&'text str>>,
    names: Vec<&'text str>,
}

impl<'text> Scope<'text> {
    fn new() -> Self {
        Default::default()
    }

    fn shadow(&self) -> Self {
        let mut shadowed = self.shadowed.clone().unwrap_or(vec![]);
        shadowed.extend_from_slice(&self.names);
        Scope {
            shadowed: Some(shadowed),
            ..Default::default()
        }
    }

    fn declare(&mut self, name: &'text str) -> usize {
        if self.names.contains(&name) {
            panic!("Name {name} already exists in scope")
        }
        self.names.push(name);
        self.names.len() - 1
    }

    fn get_index(&self, name: &'text str) -> Option<usize> {
        self.names
            .iter()
            .position(|n| n == &name)
            .map(|n| n + self.shadowed.as_ref().map(|v| v.len()).unwrap_or(0))
            .or_else(|| {
                self.shadowed
                    .as_ref()
                    .and_then(|v| v.iter().rev().position(|n| n == &name).map(|n| v.len() - n))
            })
    }

    fn contains(&self, name: &'text str) -> bool {
        self.names.contains(&name)
    }

    fn len(&self) -> usize {
        self.names.len() + self.shadowed.as_ref().map(Vec::len).unwrap_or(0)
    }
}

#[derive(Clone)]
struct ClassMethodPair<'text>(Rc<ClassDef<'text>>, Signature<'text>);

impl std::fmt::Debug for ClassMethodPair<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_tuple("ClassMethodPair")
            .field(&self.0.name)
            .field(&self.1)
            .finish()
    }
}

impl Eq for ClassMethodPair<'_> {}
impl<'text> PartialEq for ClassMethodPair<'text> {
    fn eq(&self, other: &ClassMethodPair<'text>) -> bool {
        Rc::ptr_eq(&self.0, &other.0) && (self.1 == other.1)
    }
}

use std::hash::Hash;

use crate::ast::{AstSig, IfBody};
use crate::common::GlobalClassSlots;
use crate::parser::Module;
impl Hash for ClassMethodPair<'_> {
    fn hash<H>(&self, h: &mut H)
    where
        H: std::hash::Hasher,
    {
        std::ptr::hash(Rc::as_ptr(&self.0), h);
        self.1.hash(h);
    }
}

/// classes must be in creation order!
fn generate_latest_implementations<'text>(
    classes: &[&Rc<ClassDef<'text>>],
) -> HashMap<ClassMethodPair<'text>, Rc<ClassDef<'text>>> {
    let mut latest_implementation: HashMap<ClassMethodPair, Rc<ClassDef>> = HashMap::new();
    // Prepare class information to lookup methods more efficiently

    fn ancestors<'c, 'text>(class: &'c ClassDef<'text>) -> Vec<&'c Rc<ClassDef<'text>>> {
        let mut vec = vec![];
        let mut current = class;
        // SAFETY: parents are never modified
        // Furthermore these references never escape generate_latest_implementations
        while let Some(parent) = unsafe { current.get_parent() } {
            vec.push(parent);
            current = &parent;
        }
        vec
    }

    // Because classes is in creation-order, this will overwrite properly
    for class in classes {
        for ancestor in ancestors(&class) {
            for method in ancestor.methods.keys() {
                latest_implementation.insert(
                    ClassMethodPair(Rc::clone(&class), method.clone()),
                    Rc::clone(ancestor),
                );
            }

            for method in class.methods.keys() {
                latest_implementation.remove(&ClassMethodPair(Rc::clone(ancestor), method.clone()));
            }
        }
        for method in class.methods.keys() {
            latest_implementation.insert(
                ClassMethodPair(Rc::clone(&class), method.clone()),
                Rc::clone(&class),
            );
        }
    }
    latest_implementation
}

#[derive(Debug)]
enum CallTarget<'text> {
    Dynamic(Signature<'text>),
    Static(Rc<ClassDef<'text>>, Signature<'text>),
}

impl<'text> std::cmp::PartialEq for CallTarget<'text> {
    fn eq(&self, other: &CallTarget<'text>) -> bool {
        match (self, other) {
            (CallTarget::Dynamic(sig1), CallTarget::Dynamic(sig2)) => sig1 == sig2,
            (CallTarget::Static(class1, sig1), CallTarget::Static(class2, sig2)) => {
                (sig1 == sig2) && Rc::ptr_eq(class1, class2)
            }
            _ => false,
        }
    }
}

#[derive(Clone)]
enum Query<'text> {
    MethodReturn(ClassMethodPair<'text>),
    MethodThis(ClassMethodPair<'text>),
    MethodArg(ClassMethodPair<'text>, usize),
    ClassField(Rc<ClassDef<'text>>, usize),
    Global(usize),
}

impl std::fmt::Debug for Query<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::MethodReturn(arg0) => f.debug_tuple("MethodReturn").field(arg0).finish(),
            Self::MethodThis(arg0) => f.debug_tuple("MethodThis").field(arg0).finish(),
            Self::MethodArg(arg0, arg1) => {
                f.debug_tuple("MethodArg").field(arg0).field(arg1).finish()
            }
            Self::ClassField(arg0, arg1) => f
                .debug_tuple("ClassField")
                .field(&arg0.name)
                .field(arg1)
                .finish(),
            Self::Global(arg0) => f.debug_tuple("Global").field(arg0).finish(),
        }
    }
}

impl Eq for Query<'_> {}

impl Hash for Query<'_> {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        core::mem::discriminant(self).hash(state);
        match self {
            Query::MethodReturn(p) => p.hash(state),
            Query::MethodThis(p) => p.hash(state),
            Query::MethodArg(p, n) => {
                p.hash(state);
                n.hash(state);
            }
            Query::ClassField(c, n) => {
                std::ptr::hash(Rc::as_ptr(c), state);
                n.hash(state);
            }
            Query::Global(n) => n.hash(state),
        }
    }
}

impl PartialEq for Query<'_> {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Self::MethodReturn(l0), Self::MethodReturn(r0)) => l0 == r0,
            (Self::MethodThis(l0), Self::MethodThis(r0)) => l0 == r0,
            (Self::MethodArg(l0, l1), Self::MethodArg(r0, r1)) => l0 == r0 && l1 == r1,
            (Self::ClassField(l0, l1), Self::ClassField(r0, r1)) => Rc::ptr_eq(l0, r0) && l1 == r1,
            (Self::Global(l0), Self::Global(r0)) => l0 == r0,
            _ => false,
        }
    }
}

// Create a "world of types" where every value's possible types are recorded. e.g.
// WriteField(n, expr) -> Class.FieldTypes[n] |= expr
// How to deal with complex dependencies?
// Reset all types that work out to "Unknown" and run a second time to see if anything further
// can be gleaned now that some types of fields etc are known

#[derive(Debug, Default, PartialEq, Clone)]
struct TypeDatabase<'text> {
    unresolved_queries: HashSet<Query<'text>>,
    facts: HashMap<Query<'text>, Type<'text>>,
}

impl<'text> TypeDatabase<'text> {
    fn new() -> Self {
        Default::default()
    }

    fn query_class_field(&mut self, class: &Rc<ClassDef<'text>>, field: usize) -> Type<'text> {
        self.query(Query::ClassField(Rc::clone(class), field))
    }

    fn query_global(&mut self, global: usize) -> Type<'text> {
        self.query(Query::Global(global))
    }

    fn query_method_return_type(
        &mut self,
        class: &Rc<ClassDef<'text>>,
        method: Signature<'text>,
    ) -> Option<Type<'text>> {
        let q = Query::MethodReturn(ClassMethodPair(Rc::clone(class), method));

        let ret = self.facts.get(&q).cloned();
        if ret == None {
            self.facts.insert(q, Type::Bottom);
            None
        } else {
            Some(self.query(q))
        }
    }

    fn add_fact(&mut self, query: Query<'text>, fact: Type<'text>) {
        if self.facts.contains_key(&query) {
            *self.facts.get_mut(&query).unwrap() |= fact;
        } else {
            self.facts.insert(query, fact);
        }
    }

    fn query(&mut self, query: Query<'text>) -> Type<'text> {
        match self.facts.get(&query) {
            Some(typ) => {
                if typ == &Type::Bottom {
                    self.unresolved_queries.insert(query);
                    // TODO: Return Type::Unknown instead? Exposing Bottom type to analyis will make things harder
                    // but also could enable optimizations
                } else {
                    self.unresolved_queries.remove(&query);
                }

                typ.clone()
            }
            None => {
                self.facts.insert(query.clone(), Type::Bottom);
                self.unresolved_queries.insert(query);
                Type::Bottom
            }
        }
    }
}

#[derive(Debug)]
/// Opaque ClassDef wrapper for AST
pub struct ClassRef<'a>(Rc<ClassDef<'a>>);

impl PartialEq for ClassRef<'_> {
    fn eq(&self, other: &Self) -> bool {
        Rc::ptr_eq(&self.0, &other.0)
    }
}

impl<'a> ClassRef<'a> {
    fn new(rc: Rc<ClassDef<'a>>) -> ClassRef<'a> {
        ClassRef(rc)
    }

    fn into_inner(self) -> Rc<ClassDef<'a>> {
        self.0
    }
}

struct Augur<'a, 'text> {
    classes: Vec<&'a Rc<ClassDef<'text>>>,

    current_method: Option<ClassMethodPair<'text>>,

    types: TypeDatabase<'text>,
    previous_types: Option<TypeDatabase<'text>>,
    method_lookups: HashMap<ClassMethodPair<'text>, Rc<ClassDef<'text>>>,
}

impl<'a, 'text> Augur<'a, 'text> {
    fn from_module(module: &'a parser::Module<'text>) -> Self {
        Augur::new(module.classes.iter().collect::<Vec<_>>())
    }

    fn new<T: Into<Vec<&'a Rc<ClassDef<'text>>>>>(classes: T) -> Self {
        let classes = classes.into();
        Augur {
            // FIXME: Should classes + method_lookups be their own thing? its only ever used in
            // resolve_call_target which could be a standalone function since it never touches any
            // part of augur other than these 2 fields
            method_lookups: generate_latest_implementations(&classes),
            classes: classes,
            types: TypeDatabase::new(),
            previous_types: None,
            current_method: None,
        }
    }

    // FIXME: Should this be its own thing that takes a Module or something?
    fn type_to_class(&mut self, typ: &Type<'text>) -> Option<Rc<ClassDef<'text>>> {
        match typ {
            Type::Unknown | Type::Bottom => None,
            _ => todo!(),
        }
    }

    /// Transform general types like KnownClass("Num") into more useful specialized types like
    /// KnownType(BroadType::Number)
    fn specialize_type(&mut self, typ: Type<'text>) -> Type<'text> {
        match typ {
            x @ (Type::Unknown | Type::Bottom) => x,
            Type::KnownClass(ref cls) => {
                let index = self
                    .classes
                    .iter()
                    .position(|c| Rc::ptr_eq(c, &cls))
                    .unwrap()
                    / 2;
                let slot = index.try_into();
                match slot {
                    Ok(GlobalClassSlots::Num) => Type::KnownType(BroadType::Number),
                    Err(_) => typ,
                    _ => todo!(),
                }
            }
            x => x,
        }
    }

    fn resolve_call_target(
        &mut self,
        typ: &Type<'text>,
        sig: Signature<'text>,
    ) -> CallTarget<'text> {
        match typ {
            Type::Unknown | Type::KnownType(BroadType::Object) => CallTarget::Dynamic(sig),
            // FIXME: This is jank esp. with the * 2
            Type::KnownType(BroadType::Bool) => self.resolve_call_target(
                &Type::KnownClass(Rc::clone(&self.classes[GlobalClassSlots::Bool as usize * 2])),
                sig,
            ),
            Type::KnownType(BroadType::Number) => self.resolve_call_target(
                &Type::KnownClass(Rc::clone(&self.classes[GlobalClassSlots::Num as usize * 2])),
                sig,
            ),
            Type::KnownType(BroadType::String) => self.resolve_call_target(
                &Type::KnownClass(Rc::clone(&self.classes[GlobalClassSlots::String as usize * 2])),
                sig,
            ),
            Type::KnownType(BroadType::Range) => self.resolve_call_target(
                &Type::KnownClass(Rc::clone(&self.classes[GlobalClassSlots::Range as usize * 2])),
                sig,
            ),
            Type::KnownPrimitive(p) => match p {
                ast::Primitive::Null => self.resolve_call_target(
                    &Type::KnownClass(Rc::clone(&self.classes[GlobalClassSlots::Null as usize * 2])),
                    sig,
                ),
                _ => {
                    let broad = p.into();
                    self.resolve_call_target(&Type::KnownType(broad), sig)
                }
            },
            Type::KnownClassOrSubtype(class) => {
                let latest = self
                    .method_lookups
                    .get(&ClassMethodPair(Rc::clone(class), sig.clone()));
                if let Some(latest) = latest {
                    CallTarget::Static(Rc::clone(latest), sig)
                } else {
                    CallTarget::Dynamic(sig)
                }
            }
            Type::KnownClass(class) => {
                if let Some(target) = ClassDef::find_class_with_method(&class, &sig) {
                    CallTarget::Static(target, sig)
                } else {
                    panic!("{0} does not implement '{sig}'", class.name)
                }
            }
            Type::Bottom => {
                //println!("Bottom type was receiver! sig being examined: {sig:?} augur.current_method: {:?}", &self.current_method);
                CallTarget::Dynamic(sig)
            }
        }
    }

    fn typecheck_method(
        &mut self,
        class: &Rc<ClassDef<'text>>,
        sig: Signature<'text>,
    ) -> Type<'text> {
        let inferred = match self.types.query_method_return_type(&class, sig.clone()) {
            Some(t) => t,
            None => {
                /*let specialized_this =
                    self.specialize_type(Type::KnownClassOrSubtype(Rc::clone(class)));
                self.types.add_fact(
                    Query::MethodThis(ClassMethodPair(Rc::clone(class), sig.clone())),
                    specialized_this,
                );*/
                let old_method = self
                    .current_method
                    .replace(ClassMethodPair(Rc::clone(&class), sig.clone()));
                let ast = class.find_method(&sig);
                if ast.is_none() {
                    panic!(
                        "Class {0:?} does not have expected method {sig}. Typedb is: {1:?}",
                        class.name, self.types
                    );
                }
                self.typecheck_statement(&ast.unwrap().ast);
                self.current_method = old_method;
                self.types.query_method_return_type(&class, sig).unwrap()
            }
        };

        if inferred == Type::Bottom {
            // Methods return Null by default
            Type::KnownPrimitive(ast::Primitive::Null)
        } else {
            inferred
        }
    }

    fn typecheck_expr(&mut self, ast: &Expression<'text>) -> Type<'text> {
        match ast {
            Expression::Call(receiver, ast_sig) => {
                let receiver: &Expression<'text> = receiver;
                let receiver_type: Type<'text> = self.typecheck_expr(receiver);

                let arg_types: Vec<Type> = match ast_sig {
                    AstSig::Getter(_) => vec![],
                    AstSig::Setter(_, e) => vec![self.typecheck_expr(e)],
                    AstSig::Func(_, v) => v.iter().map(|e| self.typecheck_expr(e)).collect(),
                };

                let target: CallTarget<'text> =
                    self.resolve_call_target(&receiver_type, ast_sig.into());
                match target {
                    CallTarget::Dynamic(_) => {
                        //todo!("If dynamic, then ANY method with that sig could be passed these types. We need to account for this, however that will mess up the analysis for future iterations. Need some way to mark this case as 'only apply these facts after the final aug is finished'");
                        Type::Unknown
                    }
                    CallTarget::Static(cls, sig) => {
                        for (i, arg) in arg_types.into_iter().enumerate() {
                            self.types.add_fact(
                                Query::MethodArg(ClassMethodPair(Rc::clone(&cls), sig.clone()), i),
                                arg,
                            );
                        }

                        self.types.add_fact(
                            Query::MethodThis(ClassMethodPair(Rc::clone(&cls), sig.clone())),
                            receiver_type,
                        );
                        //if cls.constructors.contains(&sig) {
                        //    Type::KnownClass(cls.get_constructor_type().unwrap())
                        //} else {
                        self.typecheck_method(&cls, sig)
                        //}
                    }
                }
            }
            Expression::SuperCall(ast_sig) => {
                let receiver_type = self.types.query(Query::MethodThis(
                    self.current_method
                        .clone()
                        .expect("Tried to typecheck SuperCall outside of a method!"),
                ));

                let arg_types: Vec<Type> = match ast_sig {
                    AstSig::Getter(_) => vec![],
                    AstSig::Setter(_, e) => vec![self.typecheck_expr(e)],
                    AstSig::Func(_, v) => v.iter().map(|e| self.typecheck_expr(e)).collect(),
                };

                let sig = ast_sig.into();
                let cls = self
                    .current_class()
                    .find_super_class_with_method(&sig)
                    .expect("Couldn't find super method");

                for (i, arg) in arg_types.into_iter().enumerate() {
                    self.types.add_fact(
                        Query::MethodArg(ClassMethodPair(Rc::clone(&cls), sig.clone()), i),
                        arg,
                    );
                }

                self.types.add_fact(
                    Query::MethodThis(ClassMethodPair(Rc::clone(&cls), sig.clone())),
                    receiver_type,
                );

                self.typecheck_method(&cls, sig.clone())
            }
            Expression::ArgLookup(n) => self
                .types
                .query(Query::MethodArg(self.current_method.clone().unwrap(), *n)),
            Expression::Or(left, right) => {
                let left = self.typecheck_expr(left);
                match left.truthiness() {
                    Some(true) => left,
                    Some(false) => self.typecheck_expr(right),
                    None => left | self.typecheck_expr(right),
                }
            }
            Expression::And(left, right) => {
                let left = self.typecheck_expr(left);
                match left.truthiness() {
                    Some(false) => left,
                    Some(true) => self.typecheck_expr(right),
                    None => left | self.typecheck_expr(right),
                }
            }
            Expression::Ternary(condition, then, r#else) => {
                match self.typecheck_expr(condition).truthiness() {
                    Some(true) => self.typecheck_expr(then),
                    Some(false) => self.typecheck_expr(r#else),
                    None => self.typecheck_expr(then) | self.typecheck_expr(r#else),
                }
            }
            Expression::Primitive(p) => Type::KnownPrimitive(p.clone()),
            Expression::ReadStatic(_) | Expression::LocalLookup(_) => {
                todo!()
            }
            Expression::ReadField(n) => {
                let current_class = &self.current_method.as_ref().unwrap().0;
                let field_type = self.types.query_class_field(current_class, *n);
                /*println!(
                    "Field {n} for class {current_class:?} is of type {:?}",
                    &field_type
                );*/
                field_type
            }
            Expression::GlobalLookup(n) => self.types.query_global(*n),
            Expression::InlineAsm(inputs, _asm) => {
                for e in inputs {
                    self.typecheck_expr(e);
                }
                Type::Unknown
            }
            Expression::This => self.types.query(Query::MethodThis(
                self.current_method
                    .clone()
                    .expect("Tried to typecheck 'this' outside of method"),
            )),
            Expression::ClassBody(class, _) => {
                // SAFETY: This reference is immediately cloned
                Type::KnownClass(Rc::clone(unsafe { class.0.get_meta_class() }.unwrap()))
            }
            Expression::Construct => {
                Type::KnownClass(self.current_class().get_constructor_type().unwrap())
            }
        }
    }

    fn current_class(&self) -> Rc<ClassDef<'text>> {
        Rc::clone(&self.current_method.as_ref().unwrap().0)
    }

    fn typecheck_statement(&mut self, statement: &Statement<'text>) {
        match statement {
            Statement::WriteField(n, e) => {
                let fact = self.typecheck_expr(e);
                self.types
                    .add_fact(Query::ClassField(self.current_class(), *n), fact);
            }
            Statement::WriteStaticField(_, _) => todo!(),
            Statement::AssignLocal(_, _) => todo!(),
            Statement::AssignGlobal(n, e) => {
                let fact = self.typecheck_expr(e);
                self.types.add_fact(Query::Global(*n), fact);
            }
            Statement::If(cond, if_body) => {
                // TODO: evaluate truthiness
                self.typecheck_expr(cond);
                let _t = None;
                self.typecheck_if(_t, if_body);
            }
            Statement::Block(v) => {
                for s in v {
                    self.typecheck_statement(s);
                }
            }
            Statement::Return(e) => {
                let fact = self.typecheck_expr(e);
                self.types.add_fact(
                    Query::MethodReturn(self.current_method.clone().unwrap()),
                    fact,
                )
            }
            Statement::Yield(e) => {
                self.typecheck_expr(e);
            }
            Statement::Break | Statement::Continue => {
                //todo!("Bottom type stuff?");
            }
            Statement::While(cond, body) => {
                self.typecheck_expr(cond);
                self.typecheck_statement(body);
            }
            Statement::For(name, seq, body) => {
                todo!();
                self.typecheck_statement(body);
            }
            Statement::ExprStatement(e) => {
                self.typecheck_expr(e);
            }
        }
    }

    fn typecheck_if(&mut self, _truthiness: Option<bool>, if_body: &IfBody<'text>) {
        match if_body {
            IfBody::Then { then } => {
                self.typecheck_statement(then);
            }
            IfBody::ThenElse { then, r#else } => {
                self.typecheck_statement(then);
                self.typecheck_statement(r#else);
            }
            IfBody::ThenElseIf { then, elseif } => {
                self.typecheck_statement(then);
                self.typecheck_expr(&elseif.0);
                let _t = None;
                self.typecheck_if(_t, &elseif.1);
            }
        }
    }

    fn aug(&mut self, top_level_ast: &'text Statement<'text>) {
        loop {
            if self
                .previous_types
                .as_ref()
                .is_some_and(|t| t == &self.types)
            {
                if self.types.unresolved_queries.len() > 0 {
                    //panic!("{:?}", self.types.unresolved_queries)
                }
                break;
            }

            self.previous_types = Some(self.types.clone());

            // TODO: Delete all Bottom from db before re-running
            self.typecheck_statement(top_level_ast);
        }
    }
}

#[derive(Default)]
struct PallBearer {
    strings: Vec<String>,
    current_loop_break: Option<Vec<String>>,
    current_loop_continue: Option<Vec<String>>,
}

impl<'a, 'text> PallBearer {
    fn new() -> Self {
        Default::default()
    }

    fn intern_string<S: Into<Cow<'text, str>>>(&mut self, string: S) -> common::StringAddress {
        let string = string.into();
        self.strings
            .iter()
            .position(|s| s == &string)
            .unwrap_or_else(|| {
                self.strings.push(string.to_string());
                self.strings.len() - 1
            })
            .try_into()
            .unwrap()
    }

    fn lower(
        &mut self,
        module: &'a parser::Module<'text>,
        augur: &mut Augur<'a, 'text>,
    ) -> (bytecode::Binary, bytecode::DebugSymbols<'text>) {
        for string in &module.strings {
            self.strings.push(string.to_string());
        }
        let mut asm = Assembler::new();

        asm.with_section("method dicts", |asm| {
            for class in &module.classes {
                asm.label(class.name.clone());
                let mut next: Option<&Rc<ClassDef>> = Some(class);
                while let Some(current) = next {
                    for (sig, _) in &current.methods {
                        let sig = format!("{}", sig);
                        let addr = Lookup::Absolute(vec![
                            "classes".into(),
                            current.name.clone(),
                            sig.clone().into(),
                        ]);
                        asm.emit_method_dict_entry(self.intern_string(&sig), addr.into());
                    }
                    // SAFETY: parents are never modified
                    next = unsafe { current.get_parent() };
                }
                asm.emit_method_dict_entry(u32::MAX, 0u32.into());
            }
        });

        asm.with_section("classes", |asm| {
            for class in &module.classes {
                self.lower_class(class, augur, asm)
            }
        });

        asm.with_section("_start", |asm| {
            self.lower_statement(augur, asm, &module.top_level_ast)
        });

        // TODO: emit a "Fault" opcode here to prevent falling off the end of the top level code
        // TODO: If any Dynamic calls were emitted, write down any matching sigs
        asm.emit_op(bytecode::Op::Exit);
        let (mut binary, debug) = asm.assemble().unwrap();
        binary.strings = self
            .strings
            .iter()
            .map(|s| s.clone().into_bytes().into_boxed_slice())
            .collect();

        (binary, debug)
    }

    fn lower_class(
        &mut self,
        class: &Rc<ClassDef<'text>>,
        augur: &mut Augur<'a, 'text>,
        asm: &mut Assembler<'text>,
    ) {
        asm.with_section(class.name.clone(), |asm| {
            for (sig, method) in &class.methods {
                self.lower_method(class, augur, asm, sig, method)
            }
        })
    }

    fn lower_method(
        &mut self,
        class: &Rc<ClassDef<'text>>,
        augur: &mut Augur<'a, 'text>,
        asm: &mut Assembler<'text>,
        sig: &Signature<'text>,
        ast: &MethodAst<'text>,
    ) {
        let old_method = augur
            .current_method
            .replace(ClassMethodPair(Rc::clone(class), sig.clone()));

        // TODO: If the method doesn't have an explicit return as the last statement, insert a
        // return null
        self.intern_string(sig.to_string());
        // TODO: self.methods.insert(intern(sig), (sig.arity, asm.current_position())))
        asm.with_section(sig.to_string(), |asm| {
            // TODO: Check with augur to determine the ABI of this method
            asm.emit_op(bytecode::Op::PopThis);
            self.lower_statement(augur, asm, &ast.ast);
            if ast::missing_return(&ast.ast) {
                asm.emit_op(bytecode::Op::PushPrimitive(bytecode::Primitive::Null));
                asm.emit_op(bytecode::Op::Ret);
            }
        });

        augur.current_method = old_method;
    }

    fn lower_statement(
        &mut self,
        augur: &mut Augur<'a, 'text>,
        asm: &mut Assembler<'text>,
        ast: &Statement<'text>,
    ) {
        match ast {
            Statement::WriteField(n, e) => {
                self.lower_expression(augur, asm, e);
                asm.emit_op(bytecode::Op::WriteField(*n));
            }
            Statement::WriteStaticField(n, e) => {
                // Push our own object so we don't lose it
                asm.emit_op(bytecode::Op::PushThis);
                {
                    self.lower_expression(augur, asm, e);
                    self.lower_expression(
                        augur,
                        asm,
                        &Expression::Call(
                            // Can't do Expression::This or else the augur will be confused about types
                            Box::new(Expression::InlineAsm(
                                vec![],
                                Assembler::from_ops(&[bytecode::Op::PushThis]).into_tree(),
                            )),
                            AstSig::Getter("class".into()),
                        ),
                    );
                    asm.emit_op(bytecode::Op::PopThis);
                    asm.emit_op(bytecode::Op::WriteField(*n));
                }
                asm.emit_op(bytecode::Op::PopThis);
            }
            Statement::AssignLocal(_, _) => todo!(),
            Statement::AssignGlobal(n, e) => {
                self.lower_expression(augur, asm, e);
                asm.emit_op(bytecode::Op::PopIntoGlobal(*n));
            }
            Statement::If(cond, body) => {
                asm.with_section("if", |asm| {
                    self.lower_expression(augur, asm, cond);
                    asm.emit_jump_if("then0".into());

                    fn lower_if_body<'a, 'text>(
                        pall: &mut PallBearer,
                        augur: &mut Augur<'a, 'text>,
                        asm: &mut Assembler<'text>,
                        body: &IfBody<'text>,
                        n: usize,
                    ) {
                        match body {
                            IfBody::Then { then } => {
                                asm.emit_jump(Into::<Lookup>::into("end").into());
                                asm.label(format!("then{n}").into());
                                pall.lower_statement(augur, asm, then);
                                asm.label("end".into());
                            }
                            IfBody::ThenElse { then, r#else } => {
                                asm.emit_jump("else".into());
                                asm.label(format!("then{n}").into());
                                pall.lower_statement(augur, asm, then);
                                asm.label("else".into());
                                pall.lower_statement(augur, asm, r#else);
                            }
                            IfBody::ThenElseIf { then, elseif } => {
                                asm.emit_jump(
                                    Lookup::Relative(vec![format!("elseif{n}").into()]).into(),
                                );
                                asm.label(format!("then{n}").into());
                                pall.lower_statement(augur, asm, then);
                                asm.label(format!("elseif{n}").into());
                                let (cond, body) = elseif;
                                pall.lower_expression(augur, asm, cond);
                                asm.emit_jump_if(
                                    Lookup::Relative(vec![format!("then{}", n + 1).into()]).into(),
                                );
                                lower_if_body(pall, augur, asm, body, n + 1);
                            }
                        }
                    }

                    lower_if_body(self, augur, asm, body, 0);
                });
            }
            Statement::Block(v) => {
                for statement in v {
                    self.lower_statement(augur, asm, statement);
                }
            }
            Statement::Return(e) => {
                self.lower_expression(augur, asm, e);
                asm.emit_op(bytecode::Op::Ret);
            }
            Statement::Yield(e) => {
                self.lower_expression(augur, asm, e);
                asm.emit_op(bytecode::Op::Yield);
            }
            Statement::Break => {
                let path = self
                    .current_loop_break
                    .as_ref()
                    .expect("Break outside of loop!");
                let cow_path = path.iter().map(|s| Cow::Owned(s.clone())).collect();
                asm.emit_jump(Lookup::Absolute(cow_path).into());
            }
            Statement::Continue => {
                let path = self
                    .current_loop_continue
                    .as_ref()
                    .expect("Break outside of loop!");
                let cow_path = path.iter().map(|s| Cow::Owned(s.clone())).collect();
                asm.emit_jump(Lookup::Absolute(cow_path).into());
            }
            Statement::While(cond, body) => {
                let rand: u32 = rand::random();
                asm.with_section(format!("while{}", rand), |asm| {
                    let cond_path = asm
                        .resolve("cond".into())
                        .into_iter()
                        .map(Cow::into_owned)
                        .collect();
                    let break_path = asm
                        .resolve("break".into())
                        .into_iter()
                        .map(Cow::into_owned)
                        .collect();

                    let old_continue = self.current_loop_continue.replace(cond_path);
                    let old_break = self.current_loop_break.replace(break_path);
                    asm.label("cond".into());
                    self.lower_expression(augur, asm, cond);
                    asm.emit_jump_if("then".into());
                    asm.emit_jump("break".into());

                    asm.label("then".into());
                    self.lower_statement(augur, asm, body);
                    asm.emit_jump("cond".into());

                    asm.label("break".into());
                    self.current_loop_continue = old_continue;
                    self.current_loop_break = old_break;
                });
            }
            Statement::For(var_name, sequence, body) => todo!("lower for loops"),
            Statement::ExprStatement(e) => {
                // TODO: Certain expression types are no-ops in ExprStatement
                // This can be picked up by peephole optimization but maybe easier to nip in the bud here
                self.lower_expression(augur, asm, e);
                asm.emit_op(bytecode::Op::Pop);
            }
        }
    }

    fn lower_expression(
        &mut self,
        augur: &mut Augur<'a, 'text>,
        asm: &mut Assembler<'text>,
        ast: &Expression<'text>,
    ) {
        let _typ = augur.typecheck_expr(ast);
        /*
        if let Type::KnownPrimitive(prim) = typ {
            ast = &Expression::Primitive(prim);
        }
        */
        match ast {
            Expression::This => asm.emit_op(bytecode::Op::PushThis),
            Expression::Call(receiver, ast_sig) => {
                // TODO: Figure out ABI from augur
                match ast_sig {
                    AstSig::Getter(_) => {}
                    AstSig::Setter(_, e) => self.lower_expression(augur, asm, e),
                    AstSig::Func(_, v) => {
                        for e in v {
                            self.lower_expression(augur, asm, e)
                        }
                    }
                }
                self.lower_expression(augur, asm, receiver);
                let receiver_type = augur.typecheck_expr(receiver);

                match augur.resolve_call_target(&receiver_type, ast_sig.into()) {
                    CallTarget::Dynamic(sig) => asm.emit_op(bytecode::Op::CallNamed(
                        sig.arity.arity() + 1,
                        self.intern_string(sig.to_string()).into(),
                    )),
                    CallTarget::Static(class, sig) => asm.emit_call(
                        sig.arity.arity() + 1, // ABI is args + 'this'
                        Lookup::Absolute(vec![
                            "classes".into(),
                            class.name.clone(),
                            sig.to_string().into(),
                        ])
                        .into(),
                    ),
                }
            }
            Expression::SuperCall(ast_sig) => {
                // TODO: Figure out ABI from augur
                match ast_sig {
                    AstSig::Getter(_) => {}
                    AstSig::Setter(_, e) => self.lower_expression(augur, asm, e),
                    AstSig::Func(_, v) => {
                        for e in v {
                            self.lower_expression(augur, asm, e)
                        }
                    }
                }
                self.lower_expression(augur, asm, &Expression::This);

                let sig = ast_sig.into();
                let current_class = &augur.current_method.as_ref().unwrap().0;
                //dbg!(&sig, &ast_sig, &current_class);
                let class_with_method = current_class
                    .find_super_class_with_method(&sig)
                    .expect("No super-impl found");
                //dbg!(&class_with_method);
                asm.emit_call(
                    sig.arity.arity() + 1,
                    Lookup::Absolute(vec![
                        "classes".into(),
                        class_with_method.name.clone(),
                        sig.to_string().into(),
                    ])
                    .into(),
                );
            }
            Expression::ReadField(n) => asm.emit_op(bytecode::Op::ReadField(*n)),
            Expression::ReadStatic(_) => todo!(),
            Expression::GlobalLookup(n) => asm.emit_op(bytecode::Op::PushGlobal(*n)),
            Expression::ArgLookup(n) => asm.emit_op(bytecode::Op::PushArg(*n)),
            Expression::LocalLookup(_) => todo!(),
            Expression::Or(left, right) => {
                let rand: u32 = rand::random();
                asm.with_section(format!("or{}", rand), |asm| {
                    self.lower_expression(augur, asm, left);
                    asm.emit_op(bytecode::Op::Dup);
                    asm.emit_jump_if("done".into());
                    self.lower_expression(augur, asm, right);
                    asm.label("done".into());
                });
            }
            Expression::And(left, right) => {
                let rand: u32 = rand::random();
                asm.with_section(format!("and{}", rand), |asm| {
                    self.lower_expression(augur, asm, left);
                    asm.emit_op(bytecode::Op::Dup);
                    asm.emit_jump_if("right".into());

                    asm.emit_jump("done".into());

                    asm.label("right".into());
                    self.lower_expression(augur, asm, right);
                    asm.label("done".into());
                });
            }
            Expression::Ternary(cond, left, right) => {
                let rand: u32 = rand::random();
                asm.with_section(format!("conditional{}", rand), |asm| {
                    self.lower_expression(augur, asm, cond);
                    asm.emit_jump_if("left".into());

                    asm.with_section("right", |asm| {
                        self.lower_expression(augur, asm, right);
                    });

                    asm.emit_jump("done".into());

                    asm.with_section("left", |asm| {
                        self.lower_expression(augur, asm, left);
                    });

                    asm.label("done".into());
                });
            }
            Expression::Primitive(p) => {
                let p = match p {
                    ast::Primitive::Bool(b) => bytecode::Primitive::Boolean(*b),
                    ast::Primitive::Number(f) => bytecode::Primitive::Number(*f),
                    ast::Primitive::String(addr) => bytecode::Primitive::String(*addr),
                    ast::Primitive::Range(_, _, _) => todo!(),
                    ast::Primitive::Null => bytecode::Primitive::Null,
                };
                asm.emit_op(bytecode::Op::PushPrimitive(p))
            }
            Expression::InlineAsm(args, section) => {
                for e in args {
                    self.lower_expression(augur, asm, e);
                }
                let rand: u32 = rand::random();
                asm.with_section(format!("inline{}", rand), |asm| {
                    asm.insert_tree(Lookup::Relative(vec![]), section.clone());
                });
            }
            Expression::ClassBody(class, super_class_slot) => {
                use bytecode::Op;
                use runtime::ClassStructure;

                let object_fields: i32 = class.0.num_fields().try_into().unwrap();
                // SAFETY: metaclass is never written to
                let metaclass = unsafe { class.0.get_meta_class() }.unwrap();
                let static_fields: i32 = metaclass.num_fields().try_into().unwrap();
                let class_name = &class.0.name;
                let meta_name = &metaclass.name;

                assert!(static_fields >= 4);
                asm.with_section(format!("class object creation {}", class_name), |asm| {
                    // No-op call just to restore `this`
                    asm.emit_call(0, "body".into());

                    asm.emit_jump("end".into());
                    asm.label("body".into());
                    // num_fields
                    asm.emit_literal(object_fields);
                    // superclass
                    asm.emit_op(Op::PushGlobal(*super_class_slot));
                    // methods
                    asm.emit_deferred_address(
                        Lookup::Absolute(vec!["method dicts".into(), class_name.clone()]).into(),
                    );
                    asm.emit_op(Op::PushPrimitive(bytecode::Primitive::String(
                        self.intern_string(class_name.clone()),
                    )));
                    // static num_fields
                    asm.emit_literal(static_fields);
                    // Class (metaclass's superclass)
                    asm.emit_op(Op::PushGlobal(GlobalClassSlots::Class as usize));
                    // metaclass's methods
                    asm.emit_deferred_address(
                        Lookup::Absolute(vec!["method dicts".into(), meta_name.clone()]).into(),
                    );
                    // metaclass's name
                    asm.emit_op(Op::PushPrimitive(bytecode::Primitive::String(
                        self.intern_string(meta_name.clone()),
                    )));
                    // 4
                    asm.emit_literal(4i32);
                    // Class (metaclass's class)
                    asm.emit_op(Op::PushGlobal(GlobalClassSlots::Class as usize));
                    // native NewObject ( #fields, superclass, #static_fields, Class, 4, Class -- #fields superclass #static_fields Class NewMetaclass)
                    asm.emit_op(Op::NativeCall(bytecode::NativeCall::NewObject));
                    // pop into this
                    asm.emit_op(Op::PopThis);
                    // write_field ClassStructure::Supertype
                    asm.emit_op(Op::WriteField(ClassStructure::Name as usize));
                    asm.emit_op(Op::WriteField(ClassStructure::Methods as usize));
                    asm.emit_op(Op::WriteField(ClassStructure::Supertype as usize));
                    // DUP
                    asm.emit_op(Op::Dup);
                    // - write_field ClassStructure::num_fields
                    asm.emit_op(Op::WriteField(ClassStructure::NumFields as usize));
                    // - Push this
                    asm.emit_op(Op::PushThis);
                    // ( #fields, superclass, #static_fields, NewMetaclass )
                    // - native NewObject
                    asm.emit_op(Op::NativeCall(bytecode::NativeCall::NewObject));
                    // ( #fields, superclass, NewClass )
                    // - pop into this
                    asm.emit_op(Op::PopThis);
                    // - write_field ClassStructure::Supertype
                    asm.emit_op(Op::WriteField(ClassStructure::Name as usize));
                    asm.emit_op(Op::WriteField(ClassStructure::Methods as usize));
                    asm.emit_op(Op::WriteField(ClassStructure::Supertype as usize));
                    // - write_field ClassStructure::num_fields
                    asm.emit_op(Op::WriteField(ClassStructure::NumFields as usize));
                    // - push this
                    asm.emit_op(Op::PushThis);
                    // - ret
                    asm.emit_op(Op::Ret);
                    asm.label("end".into());
                });
            }
            Expression::Construct => {
                asm.emit_op(bytecode::Op::ReadField(
                    runtime::ClassStructure::NumFields as usize,
                ));
                asm.emit_op(bytecode::Op::PushThis);
                asm.emit_op(bytecode::Op::NativeCall(bytecode::NativeCall::NewObject));
            }
        }
    }
}

fn main() {
    let file_name = std::env::args()
        .nth(1)
        .expect("Please provide the name of a wren file to run");
    // TODO: Yoke?
    let s = {
        let mut f = File::open(file_name).unwrap();
        let mut s = String::new();
        f.read_to_string(&mut s).unwrap();
        s
    };
    let prelude = include_str!("prelude.wren");

    let mut parser = parser::Parser::new();
    let mut prelude_ast = parser.feed_text(&prelude);

    // Perform surgery on this AST to remove the initialization code for Object and Class.
    // These will be sitting in their slots at the start of runtime already thanks to
    // runtime::warmup()
    //prelude_ast.remove(0);
    //prelude_ast.remove(0);
    let mut main_ast = parser.feed_text(&s);
    let mut top_level_ast = prelude_ast;
    top_level_ast.append(&mut main_ast);

    let mut parsed = Module::from_parser(parser, Statement::Block(top_level_ast));

    if let Statement::Block(ref mut v) = &mut parsed.top_level_ast {
        use bytecode::{Op, Primitive};
        use runtime::ClassStructure;
        v[0] = {
            let mut asm = Assembler::new();
            asm.with_section("class object creation Object", |asm| {
                let object = &parsed.classes[0];
                let object_fields: i32 = object.num_fields().try_into().unwrap();
                let object_meta = unsafe { object.get_meta_class() }.unwrap();
                let static_fields: i32 = object_meta.num_fields().try_into().unwrap();
                let meta_name = "Object metaclass";
                asm.emit_call(0, "body".into());

                asm.emit_jump("end".into());
                asm.label("body".into());
                // num_fields
                asm.emit_literal(object_fields);
                // Object has no superclass
                asm.emit_op(Op::PushPrimitive(Primitive::Null));
                // methods
                asm.emit_deferred_address(
                    Lookup::Absolute(vec!["method dicts".into(), "Object".into()]).into(),
                );
                // static num_fields
                asm.emit_literal(static_fields);
                // Class (metaclass's superclass)
                asm.emit_op(Op::PushGlobal(GlobalClassSlots::Class as usize));
                // metaclass's methods
                asm.emit_deferred_address(
                    Lookup::Absolute(vec!["method dicts".into(), meta_name.into()]).into(),
                );
                // Get Object metaclass
                asm.emit_op(Op::PushGlobal(GlobalClassSlots::Object as usize));
                asm.emit_op(Op::ClassOf);
                // pop into this
                asm.emit_op(Op::PopThis);
                // write_field ClassStructure::Supertype
                asm.emit_op(Op::WriteField(ClassStructure::Methods as usize));
                asm.emit_op(Op::WriteField(ClassStructure::Supertype as usize));
                // - write_field ClassStructure::num_fields
                asm.emit_op(Op::WriteField(ClassStructure::NumFields as usize));

                asm.emit_op(Op::PushGlobal(GlobalClassSlots::Object as usize));
                // - pop into this
                asm.emit_op(Op::PopThis);
                // - write_field ClassStructure::Supertype
                asm.emit_op(Op::WriteField(ClassStructure::Methods as usize));
                asm.emit_op(Op::WriteField(ClassStructure::Supertype as usize));
                // - write_field ClassStructure::num_fields
                asm.emit_op(Op::WriteField(ClassStructure::NumFields as usize));
                // - push this
                asm.emit_op(Op::PushThis);
                // - ret
                asm.emit_op(Op::Ret);
                asm.label("end".into());
            });
            Statement::ExprStatement(Expression::InlineAsm(vec![], asm.into_tree()))
        };

        v[1] = {
            let mut asm = Assembler::new();
            asm.with_section("class object creation Class", |asm| {
                let class = &parsed.classes[2];
                let object_fields: i32 = class.num_fields().try_into().unwrap();
                asm.emit_call(0, "body".into());

                asm.emit_jump("end".into());
                asm.label("body".into());
                // num_fields
                asm.emit_literal(object_fields);
                // Class's superclass is Object
                asm.emit_op(Op::PushGlobal(GlobalClassSlots::Object as usize));
                // methods
                asm.emit_deferred_address(
                    Lookup::Absolute(vec!["method dicts".into(), "Class".into()]).into(),
                );

                asm.emit_op(Op::PushGlobal(GlobalClassSlots::Class as usize));
                // - pop into this
                asm.emit_op(Op::PopThis);
                // - write_field ClassStructure::Supertype
                asm.emit_op(Op::WriteField(ClassStructure::Methods as usize));
                asm.emit_op(Op::WriteField(ClassStructure::Supertype as usize));
                // - write_field ClassStructure::num_fields
                asm.emit_op(Op::WriteField(ClassStructure::NumFields as usize));
                // - push this
                asm.emit_op(Op::PushThis);
                // - ret
                asm.emit_op(Op::Ret);
                asm.label("end".into());
            });
            Statement::ExprStatement(Expression::InlineAsm(vec![], asm.into_tree()))
        };
    }

    {
        let object_meta = unsafe { parsed.classes[0].get_meta_class() }.unwrap();
        let class = &parsed.classes[2];
        let class_meta = unsafe { class.get_meta_class() }.unwrap();
        assert_eq!(Rc::strong_count(&object_meta), 2);
        assert!(unsafe { object_meta.get_parent() }.is_none());
        assert_eq!(Rc::strong_count(&class_meta), 2);
    }

    {
        // SAFETY: Not going to modify object_meta (other than its parent field which is behind
        // another UnsafeCell)
        let object_meta: &Rc<ClassDef> = unsafe { parsed.classes[0].get_meta_class() }.unwrap();
        let class: &Rc<ClassDef> = &parsed.classes[2];

        // SAFETY: No other references to class_meta exist at the moment
        let class_meta: &mut Option<Rc<ClassDef>> = unsafe { &mut *class.metaclass.get() };
        *class_meta = Some(Rc::clone(&class));

        // SAFETY: No other references to object metaclass's parent exist at the moment, and in
        // fact none should ever exist at this point because we've asserted that it's None
        let object_meta_parent: &mut Option<Rc<ClassDef>> =
            unsafe { &mut *object_meta.parent.get() };
        *object_meta_parent = Some(Rc::clone(&class));
    }
    let mut augur = Augur::from_module(&parsed);
    augur.aug(&parsed.top_level_ast);

    let mut pall = PallBearer::new();
    let (assembled, debug) = pall.lower(&parsed, &mut augur);

    runtime::warmup();
    let ret = runtime::run(&assembled, Some(&debug), assembled.start).unwrap();
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
        let first = a.clone() | b.clone();
        let second = b | a;
        assert_eq!(first, second, "Type was not commutatively or'd");
        assert_eq!(first, expected);
    }

    macro_rules! identity {
        ($type:expr) => {
            test_type_commutative($type, $type, $type);
        };
    }

    #[test]
    fn same_types() {
        use ast::Primitive;
        identity!(Type::Unknown);
        identity!(Type::KnownType(BroadType::Bool));
        identity!(Type::KnownType(BroadType::Number));
        identity!(Type::KnownType(BroadType::Object));
        identity!(Type::KnownType(BroadType::Range));
        identity!(Type::KnownType(BroadType::String));

        identity!(Type::KnownPrimitive(Primitive::Bool(true)));
        identity!(Type::KnownPrimitive(Primitive::Bool(false)));
        identity!(Type::KnownPrimitive(Primitive::Number(1.0)));
        identity!(Type::KnownPrimitive(Primitive::Number(0.0)));
        identity!(Type::KnownPrimitive(Primitive::Number(-1.0)));
        //identity!(Type::KnownPrimitive(Primitive::Number(f64::NAN)));
        identity!(Type::KnownPrimitive(Primitive::Null));

        let class1 = Rc::new(ClassDef::new("A".into()));
        let class2 = Rc::new(ClassDef::child_of(&class1, "B").finish());

        identity!(Type::KnownClass(Rc::clone(&class1)));
        identity!(Type::KnownClass(Rc::clone(&class2)));
        identity!(Type::KnownClassOrSubtype(Rc::clone(&class1)));
        identity!(Type::KnownClassOrSubtype(Rc::clone(&class2)));
    }
}

#[cfg(test)]
mod method_lookup_tests {
    use super::*;
    // A <- B <- C
    // A
    //  - foo(_,_,_)
    //  - foo(_,_)
    // B
    //  - foo(_,_,_)
    // C
    //  - foo(_,_,_)
    //  - baz(_,_,_)
    fn class_hierarchy() -> (
        Rc<ClassDef<'static>>,
        Rc<ClassDef<'static>>,
        Rc<ClassDef<'static>>,
        Signature<'static>,
        Signature<'static>,
        Signature<'static>,
    ) {
        let foo = Signature::func("foo", 3);
        let foo2 = Signature::func("foo", 2);
        let baz = Signature::func("baz", 3);
        fn dummy_func<'text>(_: &mut ClassBuilder<'text>) -> MethodAst<'static> {
            MethodAst {
                ast: Statement::Return(Expression::Primitive(ast::Primitive::Null)),
            }
        }
        let mut classes = HashMap::new();

        let mut a = ClassBuilder::new("A");
        a.add_method_with(foo.clone(), dummy_func);
        a.add_method_with(foo2.clone(), dummy_func);
        let a = Rc::new(a.finish());
        classes.insert("A", Rc::clone(&a));

        let mut b = ClassDef::child_of(&a, "B");
        b.add_method_with(foo.clone(), dummy_func);
        let b = Rc::new(b.finish());
        classes.insert("B", Rc::clone(&b));

        let mut c = ClassDef::child_of(&b, "C");
        c.add_method_with(foo.clone(), dummy_func);
        c.add_method_with(baz.clone(), dummy_func);

        let c = Rc::new(c.finish());
        classes.insert("C", Rc::clone(&c));

        (Rc::clone(&a), Rc::clone(&b), Rc::clone(&c), foo, foo2, baz)
    }

    macro_rules! call_target {
        (static $class:ident [ $sig:ident ]) => {{
            CallTarget::Static(Rc::clone(&$class), ($sig).clone())
        }};

        (dyn $sig:ident) => {{
            CallTarget::Dynamic($sig.clone())
        }};
    }

    macro_rules! expect_call_target {
        ($aug:ident , $class:ident [ $sig:ident ] , $expected:expr ) => {
            assert_eq!(
                $aug.resolve_call_target(&Type::KnownClass(Rc::clone(&$class)), $sig.clone()),
                $expected
            )
        };

        ($aug:ident , ? $class:ident [ $sig:ident ] , $expected:expr ) => {
            assert_eq!(
                $aug.resolve_call_target(
                    &Type::KnownClassOrSubtype(Rc::clone(&$class)),
                    $sig.clone()
                ),
                $expected
            )
        };
    }

    #[test]
    fn known_class() {
        let (a, b, c, foo, foo2, baz) = class_hierarchy();
        let mut aug = Augur::new(vec![&a, &b, &c]);
        expect_call_target!(aug, c[foo], call_target!(static c[foo]));
        expect_call_target!(aug, b[foo], call_target!(static b[foo]));
        expect_call_target!(aug, a[foo], call_target!(static a[foo]));
        expect_call_target!(aug, a[foo2], call_target!(static a[foo2]));
        expect_call_target!(aug, c[baz], call_target!(static c[baz]));
    }

    #[test]
    fn shadowed_by_subtype() {
        let (a, b, c, foo, foo2, baz) = class_hierarchy();
        let mut aug = Augur::new(vec![&a, &b, &c]);
        expect_call_target!(aug, ?c[foo], call_target!(static c[foo]));
        expect_call_target!(aug, ?b[foo], call_target!(dyn foo));
        expect_call_target!(aug, ?a[foo], call_target!(dyn foo));
    }

    #[test]
    fn method_in_parent_unknown_subtype() {
        let (a, b, c, foo, foo2, baz) = class_hierarchy();
        let mut aug = Augur::new(vec![&a, &b, &c]);
        expect_call_target!(aug, ?c[foo2], call_target!(static a[foo2]));
        expect_call_target!(aug, ?b[foo2], call_target!(static a[foo2]));
        expect_call_target!(aug, ?a[foo2], call_target!(static a[foo2]));
    }

    #[test]
    fn method_in_parent() {
        let (a, b, c, foo, foo2, baz) = class_hierarchy();
        let mut aug = Augur::new(vec![&a, &b, &c]);
        expect_call_target!(aug, c[foo2], call_target!(static a[foo2]));
        expect_call_target!(aug, b[foo2], call_target!(static a[foo2]));
        expect_call_target!(aug, a[foo2], call_target!(static a[foo2]));
    }

    #[test]
    fn method_in_descendant() {
        let (a, b, c, foo, foo2, baz) = class_hierarchy();
        let mut aug = Augur::new(vec![&a, &b, &c]);
        expect_call_target!(aug, ?c[baz], call_target!(static c[baz]));
        expect_call_target!(aug, ?b[baz], call_target!(dyn baz));
        expect_call_target!(aug, ?a[baz], call_target!(dyn baz));
    }

    #[test]
    #[should_panic(
        expected = "Statically determined it's impossible to call baz(_,_,_) for class B"
    )]
    fn unreachable_method() {
        let (a, b, c, foo, foo2, baz) = class_hierarchy();
        let mut aug = Augur::new(vec![&a, &b, &c]);
        aug.resolve_call_target(&Type::KnownClass(Rc::clone(&b)), baz.clone());
    }
}

#[cfg(test)]
mod scope_tests {
    use super::Scope;
    #[test]
    fn scope_shadowing() {
        let mut s1 = Scope::new();

        s1.declare("var1");
        s1.declare("var2");
        s1.declare("var3");

        assert_eq!(s1.get_index("var0"), None);
        assert_eq!(s1.get_index("var1"), Some(0));
        assert_eq!(s1.get_index("var2"), Some(1));
        assert_eq!(s1.get_index("var3"), Some(2));

        let mut s2 = s1.shadow();

        s2.declare("var1");
        s2.declare("var4");

        assert_eq!(s1.get_index("var1"), Some(0));
        assert_eq!(s1.get_index("var4"), None);
        assert_eq!(s2.get_index("var1"), Some(3));
        assert_eq!(s2.get_index("var4"), Some(4));

        drop(s1);

        assert_eq!(s2.get_index("var1"), Some(3));
        assert_eq!(s2.get_index("var4"), Some(4));
    }

    #[test]
    #[should_panic]
    fn double_declare() {
        let mut s1 = Scope::new();

        s1.declare("var0");
        s1.declare("var0");
    }
}
