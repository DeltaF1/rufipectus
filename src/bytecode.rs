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

/*
enum NativeCall {
    BuiltIn(u32),
    UserDefined(u32),
}

impl From<NativeCallNumber> for NativeCall {
    fn from(n: NativeCallNumber) -> NativeCall {
        match n {
            NativeCallNumber::Unimplemented => panic!("Tried to serialize Unimplemented native call"),
            NativeCallNumber::UserDefined(code) => NativeCall::UserDefined(code),
            x => {
                // SAFETY: NativeCallNumber is repr(u32)
                let discriminant = unsafe {
                    (&x as *const _ as *const u32).read()
                };
                NativeCall::BuiltIn(discriminant)
            },
        }
    }
}
*/

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

/*
pub struct Binary {
    instructions: [u8],
    strings: Vec<[u8]>,
    methods: Map<Signature, CodeAddress>
}
*/

fn test_assembler() {
    enum IntermediateState {
        Dirty,
        Complete(Vec<u8>),
        Sized(Vec<u8>),
    }

    enum Promise<'key, T> {
        Pending(&'key ()),
        Resolved(T),
    }

    /*
    fn address_with_name(name: &'static str) -> Promise<CodeAddress>
    {
        todo!()
    }

    fn generate_call_opcode(op: Op, out: &mut[u8]) {
        // write whatever byte represents a direct-call
        out[0] = 0xff;

        let target = asm.refresh_promise(op.target);

        if let Promise::Resolved(addr) = target {
            out[1..2] = addr.into_le_bytes();
        } else if let Promise::Pending(key) = target {
            out[1..2] = 0x0000;
            asm.add_fixup(/* start + offset of */ 1, key)
        }
    }

    fn fixups() {
    }
    let asm = Assembler::new();

    asm.global_label("start");
    asm.prim(69.0);
    asm.prim(420.0);
    asm.call(2, asm.address_with_name("first"));
    asm.r#yield();

    asm.global_label("first");
    asm.pop();
    asm.ret();

    let addr_of_first = asm.addr_of_label("first");
    let len_of_first = asm.length_of_label("first");
    */
}
