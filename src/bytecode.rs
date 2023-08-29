use crate::Arity;
use crate::CodeAddress;

#[derive(Debug)]
struct StringAddress {}

#[derive(Debug)]
pub struct Signature {
    name: StringAddress,
    arity: Arity,
}

#[derive(Debug)]
#[non_exhaustive]
pub enum Primitive {
    Number(f64),
    Boolean(bool),
    Null,
}

impl From<i32> for Primitive {
    fn from(i: i32) -> Self {
        Primitive::Number(i.into())
    }
}

#[derive(Debug)]
#[repr(u32)]
pub enum NativeCall {
    NewObject = 0,
    Multiply,

    /* ... */
    Unimplemented,

    UserDefined(u32) = u32::MAX,
}

impl NativeCall {
    fn is_built_in(&self) -> bool {
        !matches!(self, NativeCall::UserDefined(_))
    }
}

#[derive(Debug)]
pub enum Op {
    Dup,
    Pop,
    Peek(usize),
    ReadField(usize),
    WriteField(usize),
    PushArg(usize),
    PushLocal(usize),
    PopIntoLocal(usize),
    PushGlobal(usize),
    PopIntoGlobal(usize),
    PushPrimitive(Primitive),
    PushThis,
    PopThis,
    Jump(i32),
    JumpIf(i32),
    CallDirect(usize, CodeAddress),
    CallNamed(Signature),
    Ret,
    RetNull,
    Yield,
    YieldNull,
    NativeCall(NativeCall),
}
