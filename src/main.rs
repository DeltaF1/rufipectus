use std::borrow::Cow;
use std::cell::Cell;
use std::collections::{HashMap, HashSet};

mod bytecode;
mod runtime;

type CodeAddress = u32;

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

enum Primitive {
    Bool(bool),
    Number(f64),
    String(*const [u8]),
    Range(isize, isize, bool),
    Null,
}

enum Value<'a> {
    Unknown,
    KnownType(Type),
    KnownPrimitive(Primitive),
    KnownObject(&'a ClassBuilder<'a>),
}

enum Type {
    Object,
    Bool,
    Number,
    String,
    Range,
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

#[derive(PartialEq, Eq, Hash, Debug, Clone, Copy)]
struct Signature<'a> {
    name: &'a str,
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
            name,
            arity: Arity::Func(0),
        }
    }
}

impl<'a> Signature<'a> {
    pub fn getter(name: &'a str) -> Self {
        Signature {
            name,
            arity: Arity::Getter,
        }
    }

    pub fn setter(name: &'a str) -> Self {
        Signature {
            name,
            arity: Arity::Setter,
        }
    }

    pub fn func(name: &'a str, n: usize) -> Self {
        Signature {
            name,
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
    ast: Ast<'a>,
}

#[derive(Default)]
struct ClassDef<'a> {
    name: &'a str,
    parent: Option<&'a ClassDef<'a>>,
    fields: Vec<&'a str>,
    static_fields: Vec<&'a str>,
    methods: HashMap<Signature<'a>, Cell<MethodAst<'a>>>,
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
    fn new(name: &'a str) -> Self {
        ClassDef {
            name,
            ..Default::default()
        }
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
            class: ClassDef::new(name),
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

    pub fn add_method<'c, 'b, F>(&mut self, name: Signature<'a>, f: F) -> &Cell<MethodAst<'a>>
    where
        F: Fn(&mut Self) -> MethodAst<'a>,
    {
        // This is necessary because the .get gets confused about the borrow otherwise
        #[allow(clippy::map_entry)]
        if !self.class.methods.contains_key(&name) {
            let cell = f(self).into();
            self.class.methods.insert(name, cell);
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

#[derive(Debug)]
enum Ast<'a> {
    Call(Box<Ast<'a>>, AstSig<'a>),
    ThisCall(AstSig<'a>),
    SuperCall(AstSig<'a>),
    ReadField(usize),
    WriteField(usize),
    LoadStatic(usize),
    GlobalLookup(usize),
    ArgLookup(usize),
    LocalLookup(usize),
    Sequence(Vec<Ast<'a>>),
}

#[derive(Debug)]
enum AstSig<'a> {
    Getter(Cow<'a, str>),
    Setter(Cow<'a, str>, Box<Ast<'a>>),
    Func(Cow<'a, str>, Vec<Ast<'a>>),
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

fn main() {
    let mut Rectangle = ClassBuilder::new("Rectangle");

    Rectangle.add_method(Signature::getter("width"), |class| {
        dbg!(class.read_field("_width"));
        MethodAst {
            ast: Ast::ReadField(class.read_field("_width")),
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
            ast: Ast::ReadField(class.read_field("_height")),
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
    Rectangle.add_method(Signature::func("new", 2), |class| {
        dbg!(class.write_field("_width"));
        dbg!(class.write_field("_height"));
        MethodAst {
            ast: Ast::Sequence(vec![
                Ast::WriteField(class.write_field("_width")),
                Ast::WriteField(class.write_field("_height")),
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
            ast: Ast::Call(
                Box::new(Ast::ReadField(class.read_field("_width"))),
                AstSig::Func(
                    "*".into(),
                    vec![Ast::ReadField(class.read_field("_height"))],
                ),
            ),
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
    let mut Square = Rectangle.child_of("Square");
    // TODO: Creates a static method called "new" with auto-generated constructor code,
    // and an instance method called "init new". The
    // space makes it uncallable by normal code
    Square.add_method(Signature::func("new", 0), |class| {
        /*
        bytecode.emit(ByteCode::PushConst("Square"));
        bytecode.emit(ByteCode::StoreStatic(Square.static_field("__classname")));
        bytecode.emit(ByteCode::LoadArg(0));
        bytecode.emit(ByteCode::LoadArg(0));
        */
        dbg!(class.write_static_field("__classname"));
        let sig = Signature::func("new", 2);
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
            ast: Ast::SuperCall(AstSig::Func(
                "new".into(),
                vec![Ast::ArgLookup(0), Ast::ArgLookup(0)],
            )),
        }
    });
    /*
    bytecode.finish_function();
    */
    Square.add_method(Signature::getter("hello"), |class| {
        dbg!(class.read_static_field("__classname"));
        MethodAst {
            ast: Ast::Call(
                Box::new(Ast::GlobalLookup(0 /* globals.read("System")*/)),
                AstSig::Func(
                    "print".into(),
                    vec![Ast::LoadStatic(class.read_static_field("__classname"))],
                ),
            ),
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
            ast: Ast::ThisCall(AstSig::Getter("height".into())),
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
    dbg!(&Square);
    dbg!(&Rectangle);

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
