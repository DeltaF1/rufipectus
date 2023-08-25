use crate::Arity;
struct StringAddress {}
struct CodeAddress {}
struct Signature {
    name: StringAddress,
    arity: Arity,
}

enum Op {
    ReadField(usize),
    WriteField(usize),
    PushArg(usize),
    PushLocal(usize),
    PopIntoLocal(usize),
    PushGlobal(usize),
    PopIntoGlobal(usize),
    PushThis,
    CallDirect { arity: usize, address: CodeAddress },
    CallNamed { arity: usize, signature: Signature },
    Ret,
    RetNull,
    Yield,
    YieldNull,
    NativeCall(u64),
}
