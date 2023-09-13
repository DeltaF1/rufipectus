#![deny(unsafe_op_in_unsafe_fn)]
use std::borrow::Cow;
use std::collections::{HashMap, HashSet};

use std::fs::File;
use std::io::Read;
use std::rc::Rc;

mod ast;
mod common;

mod bytecode;
use ast::{Expression, Signature, Statement};
use bytecode::Assembler;

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

#[derive(Default, Debug, Clone)]
enum Type<'a> {
    #[default]
    Unknown,
    KnownType(BroadType),
    KnownPrimitive(ast::Primitive),
    KnownClassOrSubtype(Rc<ClassDef<'a>>),
    KnownClass(Rc<ClassDef<'a>>), // Only possible to glean from constructors
}

impl<'a> PartialEq for Type<'a> {
    fn eq(&self, other: &Type<'a>) -> bool {
        match (self, other) {
            (Type::Unknown, Type::Unknown) => true,
            (Type::KnownType(b1), Type::KnownType(b2)) => b1 == b2,
            (Type::KnownPrimitive(p1), Type::KnownPrimitive(p2)) => p1 == p2,
            (Type::KnownClassOrSubtype(c1), Type::KnownClassOrSubtype(c2)) => Rc::ptr_eq(c1, c2),
            (Type::KnownClass(c1), Type::KnownClass(c2)) => Rc::ptr_eq(c1, c2),
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
        }
    }
}

use std::ops::BitOr;
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
    fn from(p: &ast::Primitive) -> BroadType {
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

#[derive(PartialEq, Debug)]
struct MethodAst<'a> {
    ast: Statement<'a>,
}

#[derive(Default, Debug)]
struct ClassDef<'text> {
    name: Cow<'text, str>,
    // TODO: Rc<ClassDef<'text>>
    parent: Option<Rc<ClassDef<'text>>>,
    fields: Vec<&'text str>,
    methods: HashMap<Signature<'text>, MethodAst<'text>>,
}

/*
impl std::fmt::Debug for ClassDef<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> Result<(), std::fmt::Error> {
        let un_celled = self
            .methods
            .iter()
            .map(|(k, v)| -> (&Signature, *const MethodAst) { (k, v.as_ptr()) });
        f.debug_struct("ClassDef")
            .field("name", &self.name)
            .field("parent", &self.parent.as_ref().map(|p| &p.name))
            .field("fields", &self.fields)
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

    pub fn finish(self) -> ClassDef<'a> {
        let mut class = self.class;
        let mut meta_class = self.meta_class;
        class.fields = self
            .fields
            .validate()
            .expect("A field was never written to!");
        // TODO: Result type
        // panic!("Field {field} in class {} is never written to!", self.class.name)

        meta_class.fields = self.static_fields.validate().unwrap();

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

#[derive(Debug)]
struct ClassMethodPair<'text>(Rc<ClassDef<'text>>, Signature<'text>);

impl Eq for ClassMethodPair<'_> {}
impl<'text> PartialEq for ClassMethodPair<'text> {
    fn eq(&self, other: &ClassMethodPair<'text>) -> bool {
        Rc::ptr_eq(&self.0, &other.0) && (self.1 == other.1)
    }
}

use std::hash::Hash;

use crate::ast::AstSig;
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
    // TODO: &[&Rc..]
    classes: &[Rc<ClassDef<'text>>],
) -> HashMap<ClassMethodPair<'text>, Rc<ClassDef<'text>>> {
    let mut latest_implementation: HashMap<ClassMethodPair, Rc<ClassDef>> = HashMap::new();

    // Prepare class information to lookup methods more efficiently

    fn ancestors<'a, 'text>(class: &'a ClassDef<'text>) -> Vec<&'a Rc<ClassDef<'text>>> {
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

fn resolve_call_target<'a, 'text>(
    classes: &'a HashMap<&'text str, Rc<ClassDef<'text>>>,
    latest_implementation: &HashMap<ClassMethodPair<'text>, Rc<ClassDef<'text>>>,
    typ: Type<'text>,
    sig: Signature<'text>,
) -> CallTarget<'text> {
    match typ {
        Type::Unknown | Type::KnownType(BroadType::Object) => CallTarget::Dynamic(sig),
        Type::KnownType(BroadType::Bool) => CallTarget::Static(Rc::clone(&classes["Bool"]), sig),
        Type::KnownType(BroadType::Number) => CallTarget::Static(Rc::clone(&classes["Num"]), sig),
        Type::KnownType(BroadType::String) => {
            CallTarget::Static(Rc::clone(&classes["String"]), sig)
        }
        Type::KnownType(BroadType::Range) => CallTarget::Static(Rc::clone(&classes["Range"]), sig),
        Type::KnownPrimitive(p) => {
            todo!("Match p and recurse with appropriate BroadType")
        }
        Type::KnownClassOrSubtype(class) => {
            let latest = latest_implementation.get(&ClassMethodPair(class, sig.clone()));
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
    }
}

fn type_of_expr<'a, 'text>(
    ast: &'a Expression<'text>,
    this_type: Option<&Rc<ClassDef<'text>>>,
) -> Type<'text>
where
    'a: 'text,
{
    match ast {
        Expression::Call(receiver, ast_sig) => {
            let receiver_type = type_of_expr(receiver, this_type);
            let target = resolve_call_target(todo!(), todo!(), receiver_type, ast_sig.into());
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
            let receiver_type = Type::KnownClassOrSubtype(Rc::clone(this_type.unwrap()));
            let target = resolve_call_target(todo!(), todo!(), receiver_type, ast_sig.into());
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
            match type_of_expr(_condition, this_type.clone()).truthiness() {
                Some(true) => type_of_expr(then, this_type),
                Some(false) => type_of_expr(r#else, this_type),
                None => type_of_expr(then, this_type.clone()) | type_of_expr(r#else, this_type),
            }
        }
        Expression::Primitive(p) => Type::KnownPrimitive(p.clone()),
        Expression::ReadField(_)
        | Expression::ReadStatic(_)
        | Expression::GlobalLookup(_)
        | Expression::LocalLookup(_) => Type::Unknown,
        Expression::InlineAsm(_, _) => Type::Unknown,
        Expression::This => Type::KnownClassOrSubtype(Rc::clone(this_type.unwrap())),
    }
}

fn main() {
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
    let Rectangle = Rc::new(Rectangle.finish());
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

    // TODO: Generate ast for _start to init classes as classdefs are created

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
        }

        }

        }

        fn walk_tree<'a>(tree: mut Ast<'a>) -> Ast<'a> {
            match tree {
               Ast::Expression(e) => {
                    if type_of_expr(e, None) == KnownPrimitive(p) {
                       replace e with Expression::Primitive(p)
                    }

                    match e {
                        Expression::Ternary(cond, then, r#else) => {
                            if type_of_expr(cond, None).truthiness {
                                replce with then or else
                            }
                        }
                    }                     }
               }
            }
            tree
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
        HashMap<&'static str, Rc<ClassDef<'static>>>,
        HashMap<ClassMethodPair<'static>, Rc<ClassDef<'static>>>,
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
        (
            Rc::clone(&a),
            Rc::clone(&b),
            Rc::clone(&c),
            foo,
            foo2,
            baz,
            classes,
            generate_latest_implementations(&[a, b, c]),
        )
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
        ($classes:ident , $latest_implementation:ident , $class:ident [ $sig:ident ] , $expected:expr ) => {
            assert_eq!(
                resolve_call_target(
                    &$classes,
                    &$latest_implementation,
                    Type::KnownClass(Rc::clone(&$class)),
                    $sig.clone()
                ),
                $expected
            )
        };

        ($classes:ident , $latest_implementation:ident , ? $class:ident [ $sig:ident ] , $expected:expr ) => {
            assert_eq!(
                resolve_call_target(
                    &$classes,
                    &$latest_implementation,
                    Type::KnownClassOrSubtype(Rc::clone(&$class)),
                    $sig.clone()
                ),
                $expected
            )
        };
    }

    #[test]
    fn known_class() {
        let (a, b, c, foo, foo2, baz, classes, li) = class_hierarchy();
        expect_call_target!(classes, li, c[foo], call_target!(static c[foo]));
        expect_call_target!(classes, li, b[foo], call_target!(static b[foo]));
        expect_call_target!(classes, li, a[foo], call_target!(static a[foo]));
        expect_call_target!(classes, li, a[foo2], call_target!(static a[foo2]));
        expect_call_target!(classes, li, c[baz], call_target!(static c[baz]));
    }

    #[test]
    fn shadowed_by_subtype() {
        let (a, b, c, foo, foo2, baz, classes, li) = class_hierarchy();
        expect_call_target!(classes, li, ?c[foo], call_target!(static c[foo]));
        expect_call_target!(classes, li, ?b[foo], call_target!(dyn foo));
        expect_call_target!(classes, li, ?a[foo], call_target!(dyn foo));
    }

    #[test]
    fn method_in_parent_unknown_subtype() {
        let (a, b, c, foo, foo2, baz, classes, li) = class_hierarchy();
        expect_call_target!(classes, li, ?c[foo2], call_target!(static a[foo2]));
        expect_call_target!(classes, li, ?b[foo2], call_target!(static a[foo2]));
        expect_call_target!(classes, li, ?a[foo2], call_target!(static a[foo2]));
    }

    #[test]
    fn method_in_parent() {
        let (a, b, c, foo, foo2, baz, classes, li) = class_hierarchy();
        expect_call_target!(classes, li, c[foo2], call_target!(static a[foo2]));
        expect_call_target!(classes, li, b[foo2], call_target!(static a[foo2]));
        expect_call_target!(classes, li, a[foo2], call_target!(static a[foo2]));
    }

    #[test]
    fn method_in_descendant() {
        let (a, b, c, foo, foo2, baz, classes, li) = class_hierarchy();
        expect_call_target!(classes, li, ?c[baz], call_target!(static c[baz]));
        expect_call_target!(classes, li, ?b[baz], call_target!(dyn baz));
        expect_call_target!(classes, li, ?a[baz], call_target!(dyn baz));
    }

    #[test]
    #[should_panic(
        expected = "Statically determined it's impossible to call baz(_,_,_) for class B"
    )]
    fn unreachable_method() {
        let (a, b, c, foo, foo2, baz, classes, li) = class_hierarchy();
        resolve_call_target(&classes, &li, Type::KnownClass(Rc::clone(&b)), baz.clone());
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
