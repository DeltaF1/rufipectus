#![deny(unsafe_op_in_unsafe_fn)]
use std::borrow::Cow;
use std::cell::Cell;
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

    pub fn contains(&self, item: &T) -> bool {
        self.items.contains(item)
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
            (Type::Bottom, x) => x,
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
    parent: Option<Rc<ClassDef<'text>>>,
    metaclass: Option<Rc<ClassDef<'text>>>,
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
            .field("parent", &self.parent.as_ref().map(|p| &p.name))
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

        while let Some(ancestor) = &current.parent {
            if std::ptr::eq(&**ancestor, other) {
                return true;
            }

            current = &ancestor;
        }

        false
    }

    pub fn child_of(parent: &Rc<ClassDef<'a>>, name: &'a str) -> ClassBuilder<'a> {
        ClassBuilder {
            class: ClassDef {
                name: name.into(),
                parent: Some(parent.clone()),
                ..Default::default()
            },
            meta_class: ClassDef::new((name.to_owned() + " metaclass").into()),
            ..Default::default()
        }
    }

    fn num_parent_fields(&self) -> usize {
        self.parent.as_deref().map_or(0, ClassDef::num_fields)
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
            next = cls.parent.as_deref();
        }
        None
    }

    fn find_class_with_method(self: &Rc<Self>, sig: &Signature<'a>) -> Option<Rc<ClassDef<'a>>> {
        if self.methods.contains_key(sig) {
            Some(self.clone())
        } else {
            self.parent
                .as_ref()
                .and_then(|parent| ClassDef::find_class_with_method(parent, sig))
        }
    }

    /// Only used for debugging
    fn find_field_in_parents(&self, name: &str) -> Option<(Rc<ClassDef<'a>>, usize)> {
        let mut to_search = &self.parent;

        while let Some(class) = to_search {
            to_search = &class.parent;
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
        ClassBuilder {
            class: ClassDef::new(name.into()),
            meta_class: ClassDef::new((name.to_owned() + " metaclass").into()),
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

    pub fn write_static_field(&mut self, name: &'a str) -> usize {
        self.static_fields.write_use(name)
    }

    pub fn read_static_field(&mut self, name: &'a str) -> usize {
        self.static_fields.read_use(name)
    }

    pub fn add_constructor(&mut self, sig: Signature<'a>, body: MethodAst<'a>) -> &MethodAst<'a> {
        let asm = {
            let mut assembler = Assembler::new();
            assembler.emit_op(bytecode::Op::ReadField(
                runtime::ClassStructure::NumFields as usize,
            ));
            assembler.emit_op(bytecode::Op::PushThis);
            assembler.emit_op(bytecode::Op::NativeCall(bytecode::NativeCall::NewObject));
            assembler.into_tree()
        };

        self.meta_class.methods.insert(
            sig.clone(),
            MethodAst {
                ast: Statement::Return(Expression::InlineAsm(vec![], asm)),
            }
            .into(),
        );

        let init_sig = Signature {
            name: sig.name.to_owned() + " init",
            arity: sig.arity,
        };

        self.meta_class.constructors.insert(sig);

        self.add_method(init_sig, body)
    }

    pub fn add_constructor_with<F>(&mut self, sig: Signature<'a>, mut f: F) -> &MethodAst<'a>
    where
        F: FnMut(&mut Self) -> MethodAst<'a>,
    {
        let body = f(self).into();
        self.add_constructor(sig, body)
    }

    pub fn add_static_method<F>(&mut self, sig: Signature<'a>, mut f: F) -> &MethodAst<'a>
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

    pub fn finish(self) -> Rc<ClassDef<'a>> {
        let mut class = self.class;
        let mut meta_class = self.meta_class;
        class.fields = self
            .fields
            .validate()
            .expect("A field was never written to!");
        // TODO: Result type
        // panic!("Field {field} in class {} is never written to!", self.class.name)

        meta_class.fields = self.static_fields.validate().unwrap();

        class.metaclass = Some(Rc::new(meta_class));
        let class = Rc::new(class);
        let weak = Rc::downgrade(&class);

        class
            .metaclass
            .as_ref()
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

use crate::ast::AstSig;
use crate::common::GlobalClassSlots;
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
        while let Some(parent) = &current.parent {
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

    dbg!(latest_implementation
        .iter()
        .map(|(k, v)| {
            let ClassMethodPair(c1, m) = k;
            let c2 = v;

            ((&c1.name, m.to_string()), &c2.name)
        })
        .collect::<Vec<_>>());

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
        dbg!(&query);
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
                Type::Bottom
            }
        }
    }

    fn type_check_method(world: &mut TypeDatabase, class: &Rc<ClassDef>, method_ast: MethodAst) {}
}

struct MethodTypes<'text> {
    args: Vec<Type<'text>>,
    this: Type<'text>,
    ret: Type<'text>,
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
            method_lookups: generate_latest_implementations(&classes),
            classes: classes,
            types: TypeDatabase::new(),
            previous_types: None,
            current_method: None,
        }
    }

    fn resolve_call_target(
        &mut self,
        typ: Type<'text>,
        sig: Signature<'text>,
    ) -> CallTarget<'text> {
        dbg!(&typ, &sig);
        match typ {
            Type::Unknown | Type::KnownType(BroadType::Object) => CallTarget::Dynamic(sig),
            Type::KnownType(BroadType::Bool) => CallTarget::Static(
                Rc::clone(&self.classes[GlobalClassSlots::Bool as usize]),
                sig,
            ),
            Type::KnownType(BroadType::Number) => CallTarget::Static(
                Rc::clone(&self.classes[GlobalClassSlots::Num as usize]),
                sig,
            ),
            Type::KnownType(BroadType::String) => CallTarget::Static(
                Rc::clone(&self.classes[GlobalClassSlots::String as usize]),
                sig,
            ),
            Type::KnownType(BroadType::Range) => CallTarget::Static(
                Rc::clone(&self.classes[GlobalClassSlots::Range as usize]),
                sig,
            ),
            Type::KnownPrimitive(p) => match p {
                ast::Primitive::Null => CallTarget::Static(
                    Rc::clone(&self.classes[GlobalClassSlots::Null as usize]),
                    sig,
                ),
                _ => {
                    let broad = p.into();
                    self.resolve_call_target(Type::KnownType(broad), sig)
                }
            },
            Type::KnownClassOrSubtype(class) => {
                let latest = self
                    .method_lookups
                    .get(&ClassMethodPair(class, sig.clone()));
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
                    panic!(
                        "Statically determined it's impossible to call {sig} for class {0}",
                        class.name
                    )
                }
            }
            Type::Bottom => {
                dbg!("Bottom type was receiver");
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
                self.types.add_fact(
                    Query::MethodThis(ClassMethodPair(Rc::clone(class), sig.clone())),
                    Type::KnownClassOrSubtype(Rc::clone(class)),
                );
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
                self.typecheck_statement(&class.find_method(&sig).expect("Couldn't").ast);
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
                dbg!(&receiver_type);
                let target: CallTarget<'text> =
                    self.resolve_call_target(receiver_type, ast_sig.into());
                match target {
                    CallTarget::Dynamic(_) => Type::Unknown,
                    CallTarget::Static(cls, sig) => {
                        if cls.constructors.contains(&sig) {
                            Type::KnownClass(cls.get_constructor_type().unwrap())
                        } else {
                            self.typecheck_method(&cls, sig)
                        }
                    }
                }
            }
            Expression::SuperCall(ast_sig) => {
                todo!()
            }
            Expression::ThisCall(ast_sig) => {
                let receiver_type = self.types.query(Query::MethodThis(
                    self.current_method
                        .clone()
                        .expect("Tried to typecheck ThisCall outside of a method!"),
                ));
                let target = self.resolve_call_target(receiver_type, ast_sig.into());
                match target {
                    CallTarget::Dynamic(_) => Type::Unknown,
                    CallTarget::Static(_cls, _sig) => {
                        todo!("Magic to determine if this method is a constructor")
                        // if cls.is_constructor(sig) {
                        //      Type::KnownClass(cls)
                        // } else {
                        //      Type::Unknown
                        // }
                    }
                }
            }
            Expression::ArgLookup(n) => self
                .types
                .query(Query::MethodArg(self.current_method.clone().unwrap(), *n)),
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
                self.types.query_class_field(current_class, *n)
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
                Type::KnownClass(Rc::clone(class.0.metaclass.as_ref().unwrap()))
            }
        }
    }

    fn typecheck_statement(&mut self, statement: &Statement<'text>) {
        match statement {
            Statement::WriteField(_, _) => todo!(),
            Statement::WriteStaticField(_, _) => todo!(),
            Statement::AssignLocal(_, _) => todo!(),
            Statement::AssignGlobal(n, e) => {
                let fact = self.typecheck_expr(e);
                self.types.add_fact(Query::Global(*n), fact);
            }
            Statement::If(_, _) => todo!(),
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
            Statement::ExprStatement(e) => {
                self.typecheck_expr(e);
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
                break;
            }

            self.previous_types = Some(self.types.clone());

            self.typecheck_statement(top_level_ast);
        }
    }
}

#[derive(Default)]
struct PallBearer {
    strings: Vec<String>,
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
        asm.with_section("classes", |asm| {
            for class in &module.classes {
                self.lower_class(class, augur, asm)
            }
        });
        asm.with_section("_start", |asm| {
            self.lower_statement(augur, asm, &module.top_level_ast)
        });
        dbg!(&asm);

        // TODO: emit a "Fault" opcode here to prevent falling off the end of the top level code

        // TODO: If any Dynamic calls were emitted, write down any matching sigs
        // TODO: Fixup class objects to point to their method lists

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

        self.intern_string(sig.to_string());
        // TODO: self.methods.insert(intern(sig), (sig.arity, asm.current_position())))
        asm.with_section(sig.to_string(), |asm| {
            // TODO: Check with augur to determine the ABI of this method
            asm.emit_op(bytecode::Op::PopThis);
            self.lower_statement(augur, asm, &ast.ast);
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
                self.lower_expression(augur, asm, e);
                // FIXME: Generate code to get this' class object
                asm.emit_op(bytecode::Op::WriteField(*n));
            }
            Statement::AssignLocal(_, _) => todo!(),
            Statement::AssignGlobal(n, e) => {
                self.lower_expression(augur, asm, e);
                asm.emit_op(bytecode::Op::PopIntoGlobal(*n));
            }
            Statement::If(_, _) => todo!(),
            Statement::Block(v) => {
                for statement in v {
                    self.lower_statement(augur, asm, statement);
                }
            }
            Statement::Return(e) => {
                self.lower_expression(augur, asm, e);
                asm.emit_op(bytecode::Op::Ret);
            }
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
        mut ast: &Expression<'text>,
    ) {
        let typ = augur.typecheck_expr(ast);
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

                match augur.resolve_call_target(receiver_type, ast_sig.into()) {
                    CallTarget::Dynamic(sig) => asm.emit_op(bytecode::Op::CallNamed(
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
            Expression::SuperCall(_) => todo!(),
            Expression::ReadField(n) => asm.emit_op(bytecode::Op::ReadField(*n)),
            Expression::ReadStatic(_) => todo!(),
            Expression::GlobalLookup(n) => asm.emit_op(bytecode::Op::PushGlobal(*n)),
            Expression::ArgLookup(n) => asm.emit_op(bytecode::Op::PushArg(*n)),
            Expression::LocalLookup(_) => todo!(),
            Expression::Ternary(_, _, _) => todo!(),
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
                asm.insert_tree(Lookup::Relative(vec![]), section.clone())
            }
            Expression::ClassBody(class, super_class_slot) => {
                /*
                   This is a tricky operation. We need to create the metaclass object, then call Class.new() on it to create the class object.

                   Since calling convention puts `this` at the top of the stack, we need to push in this order

                   - num_fields
                   - superclass
                        - static num_fields
                        - Class (metaclass's superclass)
                        - Class (metaclass's class)
                        - call Class.new(_,_)
                          |
                     v-----
                    - metaclass
                    - call Class.new(_,_)
                */
                let object_fields: u32 = class.0.fields.len().try_into().unwrap();
                asm.emit_op(bytecode::Op::PushPrimitive(bytecode::Primitive::Number(
                    object_fields.into(),
                )));
                // FIXME: Allow for local class slots
                asm.emit_op(bytecode::Op::PushGlobal(*super_class_slot));
                {
                    let metaclass = class.0.metaclass.as_ref().unwrap();
                    let static_fields: u32 = metaclass.fields.len().try_into().unwrap();
                    asm.emit_op(bytecode::Op::PushPrimitive(bytecode::Primitive::Number(
                        static_fields.into(),
                    )));
                    asm.emit_op(bytecode::Op::PushGlobal(
                        common::GlobalClassSlots::Class as usize,
                    ));
                    asm.emit_op(bytecode::Op::Dup);
                    asm.emit_call(
                        3,
                        Lookup::Absolute(vec![
                            "classes".into(),
                            "Class metaclass".into(),
                            "new(_,_)".into(),
                        ])
                        .into(),
                    );
                }
                // Our metaclass is now on the stack
                asm.emit_call(
                    3,
                    Lookup::Absolute(vec![
                        "classes".into(),
                        "Class metaclass".into(),
                        "new(_,_)".into(),
                    ])
                    .into(),
                );

                // metaclass.new(class.num_fields, superclass)
                // TODO: Pointer to method lookup
            }
            Expression::ThisCall(_) => todo!(),
        }
    }
}

fn main() {
    // TODO: Yoke?
    let s = {
        let mut f = File::open("test.wren").unwrap();
        let mut s = String::new();
        f.read_to_string(&mut s);
        s
    };

    // FIXME: This will be generated by a prelude source file with actual content at some point
    let mut prelude = vec![];
    let mut meta_classes = vec![];
    for i in 0..common::GlobalClassSlots::End as usize {
        let builder = ClassBuilder::new(common::GlobalClassNames[i]);
        let class = builder.finish();
        if let Some(ref meta_class) = class.metaclass {
            meta_classes.push(Rc::clone(meta_class));
        }
        prelude.push(class);
    }
    prelude.append(&mut meta_classes);

    let parsed = {
        let mut parsed = parser::parse_file(&s);
        prelude.append(&mut parsed.classes);
        parsed.classes = prelude;
        parsed
    };

    dbg!(&parsed);
    let mut augur = Augur::from_module(&parsed);

    augur.aug(&parsed.top_level_ast);
    dbg!(&parsed.top_level_ast);
    dbg!(&augur.types);

    let mut pall = PallBearer::new();
    let (assembled, debug) = pall.lower(&parsed, &mut augur);
    //dbg!(&assembled);

    runtime::warmup();
    dbg!(runtime::run(&assembled, &debug, assembled.start));
    panic!();
    let mut globals = Scope::new();
    let mut classes: Vec<Rc<ClassDef>> = vec![];
    let mut Rectangle = ClassBuilder::new("Rectangle");

    Rectangle.add_method_with(Signature::getter("width"), |class| {
        dbg!(class.read_field("_width"));
        MethodAst {
            ast: Statement::Return(Expression::ReadField(class.read_field("_width"))),
        }
    });
    /*
    // if existing, error with "duplicate method"
    bytecode.emit(
        ByteCode::LoadThis(Rectangle.field("_width"))
    );
    bytecode.finish_function();
    */

    Rectangle.add_method_with(Signature::getter("height"), |class| {
        dbg!(class.read_field("_height"));
        MethodAst {
            ast: Statement::Return(Expression::ReadField(class.read_field("_height"))),
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
    Rectangle.add_constructor_with(
        Signature::func("new", 2 /*vec!["width", "height"]*/),
        |class /*method*/| {
            dbg!(class.write_field("_width"));
            dbg!(class.write_field("_height"));
            MethodAst {
                ast: Statement::Block(vec![
                    Statement::WriteField(
                        class.write_field("_width"),
                        Box::new(
                            /*method.lookup_name("width")*/ Expression::ArgLookup(0),
                        ),
                    ),
                    Statement::WriteField(
                        class.write_field("_height"),
                        Box::new(
                            /*method.lookup_name("height")*/ Expression::ArgLookup(1),
                        ),
                    ),
                ]),
            }
        },
    );
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
    Rectangle.add_method_with(Signature::func("area", 0), |class| {
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
    classes.push(Rectangle.clone());
    globals.declare("Rectangle");
    let mut Square = ClassDef::child_of(&Rectangle, "Square");
    // TODO: Creates a static method called "new" with auto-generated constructor code,
    // and an instance method called "new init". The
    // space makes it uncallable by normal code
    Square.add_constructor_with(Signature::func("new", 1), |class| {
        /*
        bytecode.emit(ByteCode::PushConst("Square"));
        bytecode.emit(ByteCode::StoreStatic(Square.static_field("__classname")));
        bytecode.emit(ByteCode::LoadArg(0));
        bytecode.emit(ByteCode::LoadArg(0));
        */
        let sig = Signature::func("new init", 2);
        let parent = &class.class.parent;
        if let Some(index) = &parent.as_ref().and_then(|p| p.find_method(&sig)) {
            /*
            bytecode.emit(ByteCode::CallAddress(index));
            */
        } else {
            panic!("Can't call super here: no such method {sig} in parent");
        }
        MethodAst {
            ast: Statement::Block(vec![
                Statement::WriteStaticField(
                    class.write_static_field("__classname"),
                    Box::new(Expression::Primitive(ast::Primitive::String(0))),
                ),
                Statement::ExprStatement(Expression::SuperCall(AstSig::Func(
                    "new".into(),
                    vec![Expression::ArgLookup(0), Expression::ArgLookup(0)],
                ))),
            ]),
        }
    });
    /*
    bytecode.finish_function();
    */
    Square.add_method_with(Signature::getter("hello"), |class| {
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
    Square.add_method_with(Signature::getter("foo"), |class| {
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
    let Square = Rc::new(Square.finish());
    classes.push(Rc::clone(&Square));
    globals.declare("Square");
    dbg!(&Square);
    dbg!(&Rectangle);

    assert_eq!(&Square.fields, &parsed.global_classes["Square"].fields);
    assert_eq!(
        &Rectangle.fields,
        &parsed.global_classes["Rectangle"].fields
    );

    //assert_eq!(&Rectangle.methods, &parsed.classes["Rectangle"].methods);
    //assert_eq!(&Square.methods, &parsed.classes["Square"].methods);

    let top_level_ast = Statement::Block(vec![
        Statement::AssignGlobal(
            globals.declare("s"),
            Box::new(Expression::Call(
                Box::new(Expression::GlobalLookup(
                    globals.get_index("Square").unwrap(),
                )),
                AstSig::Func(
                    "new".into(),
                    vec![Expression::Primitive(ast::Primitive::Number(10.0))],
                ),
            )),
        ),
        Statement::ExprStatement(Expression::Call(
            Box::new(Expression::GlobalLookup(globals.get_index("s").unwrap())),
            AstSig::Getter("hello".into()),
        )),
    ]);

    dbg!(&top_level_ast);
    assert_eq!(&top_level_ast, &parsed.top_level_ast);

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
        let first = (a.clone() | b.clone());
        let second = (b | a);
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
                $aug.resolve_call_target(Type::KnownClass(Rc::clone(&$class)), $sig.clone()),
                $expected
            )
        };

        ($aug:ident , ? $class:ident [ $sig:ident ] , $expected:expr ) => {
            assert_eq!(
                $aug.resolve_call_target(
                    Type::KnownClassOrSubtype(Rc::clone(&$class)),
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
        aug.resolve_call_target(Type::KnownClass(Rc::clone(&b)), baz.clone());
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
