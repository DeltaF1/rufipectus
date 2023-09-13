use std::borrow::Cow;

use crate::{common::StringAddress, Arity};

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
    ExprStatement(Expression<'a>),
}

#[derive(Debug, PartialEq)]
pub enum Expression<'a> {
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
    InlineAsm(Vec<Expression<'a>>, crate::bytecode::Section<'a>),
    This,
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

impl<'a> From<&'a AstSig<'_>> for Signature<'a> {
    fn from(other: &'a AstSig) -> Self {
        match other {
            AstSig::Getter(s) => Signature::getter(s),
            AstSig::Setter(s, _) => Signature::setter(s),
            AstSig::Func(s, v) => Signature::func(s, v.len()),
        }
    }
}