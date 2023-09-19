use std::{borrow::Cow, rc::Rc};

use crate::{common::StringAddress, Arity, ClassRef};

#[derive(PartialEq, Debug, Clone)]
pub enum Primitive {
    Bool(bool),
    Number(f64),
    String(StringAddress),
    Range(isize, isize, bool),
    Null,
}

#[derive(PartialEq, Eq, Hash, Debug, Clone)]
pub struct Signature<'a> {
    pub name: Cow<'a, str>,
    pub arity: Arity,
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
    pub fn getter<T: Into<Cow<'a, str>>>(name: T) -> Self {
        Signature {
            name: name.into(),
            arity: Arity::Getter,
        }
    }

    pub fn setter<T: Into<Cow<'a, str>>>(name: T) -> Self {
        Signature {
            name: name.into(),
            arity: Arity::Setter,
        }
    }

    pub fn func<T: Into<Cow<'a, str>>>(name: T, n: usize) -> Self {
        Signature {
            name: name.into(),
            arity: Arity::Func(n),
        }
    }
}

impl<'text> Signature<'text> {
    pub fn new(name: Cow<'text, str>, arity: Arity) -> Self {
        Signature { name, arity }
    }
}

#[deprecated]
#[derive(Debug)]
enum Ast<'a> {
    Statement(Statement<'a>),
    Expression(Expression<'a>),
}

// TODO: Expression statement
#[derive(Debug, PartialEq)]
pub enum Statement<'a> {
    WriteField(usize, Box<Expression<'a>>),
    WriteStaticField(usize, Box<Expression<'a>>),
    AssignLocal(usize, Box<Expression<'a>>),
    AssignGlobal(usize, Box<Expression<'a>>),
    If(Box<Expression<'a>>, IfBody<'a>),
    Block(Vec<Statement<'a>>),
    Return(Expression<'a>),
    Yield(Expression<'a>),
    ExprStatement(Expression<'a>),
}

#[derive(Debug, PartialEq)]
pub enum Expression<'a> {
    This,
    Call(Box<Expression<'a>>, AstSig<'a>),
    #[deprecated]
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
    InlineAsm(Vec<Expression<'a>>, crate::bytecode::Section<'a>),
    ClassBody(ClassRef<'a>, usize),
    Construct,
}

#[derive(Debug, PartialEq)]
pub enum IfBody<'a> {
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

#[derive(Debug, PartialEq)]
pub enum AstSig<'a> {
    Getter(Cow<'a, str>),
    Setter(Cow<'a, str>, Box<Expression<'a>>),
    Func(Cow<'a, str>, Vec<Expression<'a>>),
}

impl<'a> From<&AstSig<'a>> for Signature<'a> {
    fn from(other: &AstSig<'a>) -> Self {
        match other {
            AstSig::Getter(s) => Signature::getter(s.clone()),
            AstSig::Setter(s, _) => Signature::setter(s.clone()),
            AstSig::Func(s, v) => Signature::func(s.clone(), v.len()),
        }
    }
}

impl<'a> AstSig<'a> {
    pub fn from_sig(sig: Signature<'a>, mut args: Vec<Expression<'a>>) -> Self {
        assert_eq!(sig.arity.arity(), args.len());
        match sig.arity {
            Arity::Getter => AstSig::Getter(sig.name),
            Arity::Setter => AstSig::Setter(sig.name, Box::new(args.pop().unwrap())),
            Arity::Func(_) => AstSig::Func(sig.name, args),
            _ => todo!("subscripts"),
        }
    }
}
