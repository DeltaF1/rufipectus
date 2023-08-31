use crate::Arity;
use crate::CodeAddress;
use std::collections::HashMap;

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

struct Binary {}
/*
pub struct Binary {
    instructions: [u8],
    strings: Vec<[u8]>,
    methods: Map<Signature, CodeAddress>,

    // Keep track of how many global objects there are
    variables: usize
}
*/

// TODO: Allow opcodes to be the result of a compile-time calculation? Probably overkill
#[non_exhaustive]
#[derive(Debug)]
enum VariableOp<'a> {
    Jump(Lookup<'a>),
    JumpIf(Lookup<'a>),
    CallDirect(usize, Lookup<'a>),
    // TODO: Any more opcodes that we want to be able to reference variables
}

impl<'a> From<VariableOp<'a>> for AssemblerOp<'a> {
    fn from(v: VariableOp<'a>) -> AssemblerOp<'a> {
        AssemblerOp::Variable(v)
    }
}

impl<'a> From<AssemblerOp<'a>> for AssemblerNode<'a> {
    fn from(o: AssemblerOp<'a>) -> AssemblerNode<'a> {
        AssemblerNode::Op(o)
    }
}

impl<'a> From<VariableOp<'a>> for AssemblerNode<'a> {
    fn from(v: VariableOp<'a>) -> AssemblerNode<'a> {
        AssemblerNode::Op(v.into())
    }
}

#[derive(Debug)]
enum AssemblerOp<'a> {
    StaticallyKnown(Op),
    Variable(VariableOp<'a>),
}

impl From<Op> for AssemblerOp<'_> {
    fn from(o: Op) -> AssemblerOp<'static> {
        AssemblerOp::StaticallyKnown(o)
    }
}

#[derive(Debug)]
enum AssemblerAddress<'a> {
    Known(CodeAddress),
    Lookup(Lookup<'a>),
}

impl From<CodeAddress> for AssemblerAddress<'_> {
    fn from(c: CodeAddress) -> AssemblerAddress<'static> {
        AssemblerAddress::Known(c)
    }
}

impl<'a> From<Lookup<'a>> for AssemblerAddress<'a> {
    fn from(l: Lookup<'a>) -> AssemblerAddress<'a> {
        AssemblerAddress::Lookup(l)
    }
}

#[derive(Debug)]
enum AssemblerOffset<'a> {
    Known(i32),
    Lookup(Lookup<'a>),
}

#[derive(Debug)]
enum AssemblerNode<'a> {
    Section(&'a str, Vec<AssemblerNode<'a>>),
    Label(&'a str),
    Op(AssemblerOp<'a>),
}

impl<'text> AssemblerNode<'text> {
    fn get_vec_mut(&mut self) -> &mut Vec<AssemblerNode<'text>> {
        match self {
            AssemblerNode::Section(_, v) => v,
            _ => panic!(),
        }
    }
}

#[derive(Debug)]
enum Lookup<'a> {
    Absolute(Vec<&'a str>),
    Relative(Vec<&'a str>),
}

impl<'a> From<&'a str> for Lookup<'a> {
    fn from(s: &'a str) -> Lookup<'a> {
        Lookup::Absolute(vec![s])
    }
}

impl<'a> From<&'a str> for AssemblerAddress<'a> {
    fn from(s: &'a str) -> AssemblerAddress<'a> {
        AssemblerAddress::Lookup(s.into())
    }
}

#[derive(Debug)]
struct MissingLabels<'text> {
    labels: Vec<&'text str>,
}

impl std::fmt::Display for MissingLabels<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> Result<(), std::fmt::Error> {
        todo!()
    }
}

impl std::error::Error for MissingLabels<'_> {}

#[derive(Debug)]
enum FixupType {
    CodeAddress,
    CodeOffset,
    DataAddress,
}

#[derive(Debug)]
struct Fixup<'a> {
    location: usize,
    typ: FixupType,
    key: Lookup<'a>,
}

#[derive(Debug)]
struct Assembler<'text> {
    root: AssemblerNode<'text>,
    current_path: Vec<&'text str>,
    state: IntermediateState<'text>,
}

impl<'text> Assembler<'text> {
    fn new() -> Self {
        Assembler {
            root: AssemblerNode::Section("", vec![]),
            current_path: vec![],
            state: Default::default(),
        }
    }

    fn find_section<'a, 'b>(&mut self, name: &'b [&'text str]) -> &'a mut AssemblerNode
    where
        'a: 'b,
    {
        todo!()
    }

    fn current_section<'a>(&'a mut self) -> &'a mut AssemblerNode<'text> {
        let mut current = &mut self.root;

        for name in &self.current_path {
            let vec = current.get_vec_mut();
            match vec.iter_mut().find(|node| {
                if let AssemblerNode::Section(sec_name, _) = node {
                    sec_name == name
                } else {
                    false
                }
            }) {
                Some(node) => current = node,
                none => panic!("Can't find the current section"),
            }
        }

        current
    }

    fn with_section<F>(&mut self, name: &'text str, mut f: F)
    where
        F: FnMut(&mut Self),
    {
        let cur = self.current_section();

        let new_section = AssemblerNode::Section(name, vec![]);

        if let AssemblerNode::Section(_, v) = cur {
            v.push(new_section)
        } else {
            panic!()
        }

        self.current_path.push(name);

        f(self);

        self.current_path.pop();
    }

    fn emit_op(&mut self, op: Op) {
        let section = self.current_section();
        if let AssemblerNode::Section(name, vec) = section {
            vec.push(AssemblerNode::Op(AssemblerOp::StaticallyKnown(op)));
        } else {
            panic!()
        }
    }

    fn label(&mut self, name: &'text str) {
        let section = self.current_section().get_vec_mut();
        section.push(AssemblerNode::Label(name))
    }

    fn emit_call(&mut self, n: usize, address: AssemblerAddress<'text>) {
        match address {
            AssemblerAddress::Known(addr) => self.emit_op(Op::CallDirect(n, addr)),
            AssemblerAddress::Lookup(lookup) => {
                let section = self.current_section().get_vec_mut();
                let op: AssemblerOp = VariableOp::CallDirect(n, lookup).into();
                section.push(op.into())
            }
        }
    }

    fn emit_jump(&mut self, lookup: Lookup<'text>) {
        let section = self.current_section().get_vec_mut();
        section.push(VariableOp::Jump(lookup).into())
    }

    fn dirty(&mut self) {
        self.state = IntermediateState::Dirty
    }

    fn generate(&mut self) -> Result<(), ()> {
        let state: Assembly = todo!("Draw the rest of the owl");

        if state.fixups.len() > 0 {
            self.state = IntermediateState::Sized(state)
        } else {
            self.state = IntermediateState::Complete(state)
        }

        todo!()
    }

    pub fn assemble(&mut self) -> Result<Binary, MissingLabels<'text>> {
        self.get_or_generate();
        todo!()
    }

    fn get_or_generate(&mut self) -> Result<&mut Assembly<'text>, ()> {
        Ok(match self.state {
            IntermediateState::Dirty => {
                self.generate()?;
                self.get_or_generate().unwrap()
            }
            IntermediateState::Sized(ref mut a) => a,
            IntermediateState::Complete(ref mut a) => a,
        })
    }

    fn address_of_label(&mut self, name: &[&str]) -> Result<CodeAddress, ()> {
        Ok(self.get_or_generate()?.labels[name])
    }
}

#[derive(Default, Debug)]
enum IntermediateState<'text> {
    #[default]
    Dirty,
    Complete(Assembly<'text>),
    Sized(Assembly<'text>),
}

#[derive(Debug, Default)]
struct Assembly<'text> {
    labels: HashMap<&'text [&'text str], CodeAddress>,
    generated: Vec<u8>,
    fixups: Vec<Fixup<'text>>,
}

#[test]
fn test_assembler() {
    /*
    :start
       :loop
           push 69
           push 420
           call 2, first
           yield
       ;loop
       jump ./loop
    ;start

    :first
       pop
       ret
    ;first
    */

    let mut asm = Assembler::new();

    asm.with_section("start", |mut asm| {
        asm.with_section("loop", |mut asm| {
            asm.emit_op(Op::PushPrimitive(69.into()));
            asm.emit_op(Op::PushPrimitive(420.into()));
            asm.emit_call(2, "first".into());
            asm.emit_op(Op::Yield);
        });
        asm.emit_jump(Lookup::Relative(["loop"].into()))
    });

    asm.with_section("first", |mut asm| {
        asm.emit_op(Op::Pop);
        asm.emit_op(Op::Ret);
    });

    dbg!(&asm);
    dbg!(asm.address_of_label(&["start"]));
    dbg!(asm.address_of_label(&["start", "loop"]));
    dbg!(asm.address_of_label(&["loop"]));
}
