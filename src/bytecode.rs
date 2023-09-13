use crate::common::{CodeAddress, StringAddress};
use crate::Arity;
use std::borrow::Cow;
use std::collections::HashMap;

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

const fn opcode(op: &Op) -> u8 {
    use Op::*;
    match op {
        Dup => 0,
        Pop => 1,
        Peek(_) => 2,
        ReadField(_) => 3,
        WriteField(_) => 4,
        PushArg(_) => 5,
        PushLocal(_) => 6,
        PopIntoLocal(_) => 7,
        PushGlobal(_) => 8,
        PopIntoGlobal(_) => 9,
        PushPrimitive(p) => match p {
            Primitive::Null => 0x10,
            Primitive::Number(_) => 0x11,
            Primitive::Boolean(_) => 0x12,
        },
        PushThis => 0x18,
        PopThis => 0x19,
        Jump(_) => 0x1a,
        JumpIf(_) => 0x1b,
        CallDirect(_, _) => 0x1c,
        CallNamed(_) => 0x1d,
        Ret => 0x1e,
        RetNull => 0x1f,
        Yield => 0x20,
        YieldNull => 0x21, // Are these necessary?
        NativeCall(_) => 0x22,
    }
}

impl Op {
    fn len(&self) -> usize {
        use Op::*;
        match self {
            PushPrimitive(_) => 9,
            CallDirect(_, _) => 9,
            Jump(_) => 5,
            _ => 1,
        }
    }

    const fn opcode(&self) -> u8 {
        opcode(self)
    }

    fn serialize(&self, output: &mut Vec<u8>) {
        use Op::*;
        let len = output.len();
        output.push(opcode(self));
        match self {
            PushPrimitive(prim) => match prim {
                Primitive::Number(f) => output.extend_from_slice(&f.to_le_bytes()),
                Primitive::Boolean(b) => output.extend_from_slice(&(*b as u32).to_le_bytes()),
                Primitive::Null => output.extend_from_slice(&0u64.to_le_bytes()),
            },
            CallDirect(arity, address) => {
                let arity: u32 = (*arity).try_into().unwrap();
                output.extend_from_slice(&arity.to_le_bytes());
                output.extend_from_slice(&address.to_le_bytes());
            }
            Jump(offset) => output.extend_from_slice(&offset.to_le_bytes()),
            Yield | Pop | Ret => {}
            x => todo!("Serialize {x:?}"),
        }
        assert_eq!(output.len(), len + self.len());
    }
}

#[derive(Debug)]
pub struct Binary {
    bytes: Vec<u8>,
}
/*
TODO: Add more to Binary
pub struct Binary {
    instructions: [u8],
    strings: Vec<[u8]>,
    methods: Map<Signature, CodeAddress>,

    // Keep track of how many global objects there are
    variables: usize

    start: CodeAddress
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
pub enum AssemblerOffset<'a> {
    Known(i32),
    Lookup(Lookup<'a>),
}

impl<'a> From<Lookup<'a>> for AssemblerOffset<'a> {
    fn from(l: Lookup<'a>) -> AssemblerOffset<'a> {
        AssemblerOffset::Lookup(l)
    }
}

#[derive(Debug)]
enum AssemblerNode<'a> {
    Section(Cow<'a, str>, Vec<AssemblerNode<'a>>),
    Label(Cow<'a, str>),
    Op(AssemblerOp<'a>),
}

#[derive(Debug)]
pub struct Section<'a> {
    node: AssemblerNode<'a>,
}

impl PartialEq for Section<'_> {
    fn eq(&self, _: &Section<'_>) -> bool {
        false
    }
}

impl<'text> AssemblerNode<'text> {
    fn get_vec(&self) -> &Vec<AssemblerNode<'text>> {
        match self {
            AssemblerNode::Section(_, v) => v,
            _ => panic!(),
        }
    }

    fn get_vec_mut(&mut self) -> &mut Vec<AssemblerNode<'text>> {
        match self {
            AssemblerNode::Section(_, v) => v,
            _ => panic!(),
        }
    }
}

#[derive(Hash, PartialEq, Debug, Clone)]
pub enum Lookup<'a> {
    Absolute(Vec<Cow<'a, str>>),
    Relative(Vec<Cow<'a, str>>),
}

impl<'text> Lookup<'text> {
    fn resolve<S>(&self, base: &[S]) -> Vec<Cow<'text, str>>
    where
        S: Into<Cow<'text, str>> + Clone,
    {
        match self {
            Lookup::Absolute(v) => v.clone(),
            Lookup::Relative(v) => {
                let mut v2 = vec![];
                v2.extend(base.iter().map(|s| (*s).clone().into()));
                v2.extend_from_slice(&v);
                v2
            }
        }
    }
}

impl<'a> From<&'a str> for Lookup<'a> {
    fn from(s: &'a str) -> Lookup<'a> {
        Lookup::Relative(vec![s.into()])
    }
}

impl<'a> From<&'a str> for AssemblerAddress<'a> {
    fn from(s: &'a str) -> AssemblerAddress<'a> {
        AssemblerAddress::Lookup(s.into())
    }
}

#[derive(Debug)]
pub struct MissingLabels {
    labels: Vec<String>,
}

impl std::fmt::Display for MissingLabels {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> Result<(), std::fmt::Error> {
        todo!()
    }
}

impl std::error::Error for MissingLabels {}

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
    key: Vec<Cow<'a, str>>,
}

#[derive(Debug)]
pub struct Assembler<'text> {
    root: AssemblerNode<'text>,
    current_path: Vec<Cow<'text, str>>,
    state: IntermediateState<'text>,
}

impl<'text> Assembler<'text> {
    pub fn new() -> Self {
        Assembler {
            root: AssemblerNode::Section("".into(), vec![]),
            current_path: vec![],
            state: Default::default(),
        }
    }

    fn current_section(&mut self) -> &mut AssemblerNode<'text> {
        self.borrow_section_mut(Lookup::Absolute(
            self.current_path.iter().map(|s| (*s).clone()).collect(),
        ))
    }

    pub fn with_section<S, F>(&mut self, name: S, mut f: F)
    where
        F: FnMut(&mut Self),
        S: Into<Cow<'text, str>>,
    {
        let name = name.into();
        let cur = self.current_section();

        let new_section = AssemblerNode::Section(name.clone(), vec![]);
        cur.get_vec_mut().push(new_section);

        self.current_path.push(name.into());

        f(self);

        self.current_path.pop();
    }

    pub fn emit_op(&mut self, op: Op) {
        let section = self.current_section().get_vec_mut();
        section.push(AssemblerNode::Op(AssemblerOp::StaticallyKnown(op)));
    }

    pub fn label(&mut self, name: Cow<'text, str>) {
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

    pub fn emit_jump(&mut self, offset: AssemblerOffset<'text>) {
        match offset {
            AssemblerOffset::Known(off) => self.emit_op(Op::Jump(off)),
            AssemblerOffset::Lookup(lookup) => {
                let section = self.current_section().get_vec_mut();
                section.push(VariableOp::Jump(lookup).into())
            }
        }
    }

    pub fn emit_jump_if(&mut self, offset: AssemblerOffset<'text>) {
        match offset {
            AssemblerOffset::Known(off) => self.emit_op(Op::JumpIf(off)),
            AssemblerOffset::Lookup(lookup) => {
                let section = self.current_section().get_vec_mut();
                section.push(VariableOp::JumpIf(lookup).into())
            }
        }
    }

    // FIXME: dirty is never called
    fn dirty(&mut self) {
        self.state = IntermediateState::Dirty
    }

    fn generate(&mut self) -> Result<(), ()> {
        let mut current_section = vec![];
        let mut output = vec![];
        let mut labels = HashMap::new();
        let mut fixups = vec![];

        fn generate_node<'text>(
            node: &mut AssemblerNode<'text>,
            current_section: &mut Vec<Cow<'text, str>>,
            output: &mut Vec<u8>,
            labels: &mut HashMap<Vec<Cow<'text, str>>, CodeAddress>,
            fixups: &mut Vec<Fixup<'text>>,
        ) {
            match node {
                AssemblerNode::Section(name, vec) => {
                    current_section.push(name.clone());
                    if let Some(existing) = labels.insert(
                        current_section.clone(),
                        output
                            .len()
                            .try_into()
                            .expect("Assembly overflowed CodeAddress"),
                    ) {
                        // TODO: ExistingLabel error
                        panic!("Label {current_section:?} already points to address {existing}")
                    }
                    for inner in vec {
                        generate_node(inner, current_section, output, labels, fixups)
                    }
                    current_section.pop();
                }
                AssemblerNode::Label(name) => {
                    current_section.push((*name).clone());
                    if let Some(existing) = labels.insert(
                        current_section.clone(),
                        output
                            .len()
                            .try_into()
                            .expect("Assembly overflowed CodeAddress"),
                    ) {
                        // TODO: ExistingLabel error
                        panic!("Label {current_section:?} already points to address {existing}")
                    }
                    current_section.pop();
                }
                AssemblerNode::Op(op) => {
                    match op {
                        AssemblerOp::StaticallyKnown(op) => {
                            op.serialize(output);
                        }
                        AssemblerOp::Variable(v) => {
                            match v {
                                VariableOp::Jump(lookup) | VariableOp::JumpIf(lookup) => {
                                    let offset: i32;
                                    let absolute_key = lookup.resolve(current_section);
                                    let target = labels.get(&absolute_key);
                                    if let Some(shortcut) = target {
                                        // The IP will have advanced past this opcode
                                        // 1 byte + 4 bytes for the offset itself
                                        let start: i32 = (output.len() + 5).try_into().unwrap();
                                        let target: i32 = (*shortcut).try_into().unwrap();
                                        offset = target - start;
                                    } else {
                                        // Placeholder value to fixup later
                                        offset = 0;
                                        fixups.push(Fixup {
                                            key: absolute_key,
                                            location: output.len() + 1, // Account for the Jump opcode
                                            typ: FixupType::CodeOffset,
                                        });
                                    }

                                    match v {
                                        VariableOp::Jump(_) => Op::Jump(offset).serialize(output),
                                        VariableOp::JumpIf(_) => {
                                            Op::JumpIf(offset).serialize(output)
                                        }
                                        _ => unreachable!(),
                                    }
                                }
                                VariableOp::CallDirect(arity, lookup) => {
                                    let address: CodeAddress;
                                    let absolute_key = lookup.resolve(current_section);
                                    let target = labels.get(&absolute_key);
                                    if let Some(shortcut) = target {
                                        address = *shortcut;
                                    } else {
                                        // Placeholder to be fixed up later
                                        address = 0;
                                        fixups.push(Fixup {
                                            key: absolute_key,
                                            location: output.len() + 5, // Account for the Call opcode and the arity
                                            typ: FixupType::CodeAddress,
                                        });
                                    }

                                    Op::CallDirect(*arity, address).serialize(output);
                                }
                            }
                        }
                    }
                }
            }
        }

        // Avoid the awkward problem of the root's name being in the path
        for node in self.root.get_vec_mut() {
            generate_node(
                node,
                &mut current_section,
                &mut output,
                &mut labels,
                &mut fixups,
            );
        }

        fixups.retain(|fixup| {
            let target = labels.get(&fixup.key);
            if let Some(target) = target {
                match &fixup.typ {
                    FixupType::CodeAddress => {
                        (&mut output[fixup.location..fixup.location + 4])
                            .copy_from_slice(&target.to_le_bytes());
                    }
                    x => todo!("Fixup {x:?}"),
                }
                return false; // Delete this fixup as it is now resolved
            } else {
                return true; // This fixup can't be resolved
            }
        });

        let state = Assembly {
            generated: output,
            labels,
            fixups,
        };

        if state.fixups.len() > 0 {
            self.state = IntermediateState::Sized(state)
        } else {
            self.state = IntermediateState::Complete(state)
        }
        Ok(())
    }

    pub fn assemble(&mut self) -> Result<Binary, MissingLabels> {
        self.get_or_generate();
        match &self.state {
            IntermediateState::Sized(assembly) => Err(MissingLabels {
                labels: assembly.fixups.iter().map(|f| f.key.join("/")).collect(),
            }),
            IntermediateState::Complete(assembly) => Ok(Binary {
                bytes: assembly.generated.clone(),
            }),
            IntermediateState::Dirty => unreachable!(),
        }
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

    // TODO: Return Result
    fn borrow_section_mut(&mut self, path: Lookup<'text>) -> &mut AssemblerNode<'text> {
        self.dirty();
        let path = path.resolve(&self.current_path);
        let mut current = &mut self.root;

        for name in &path {
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

    fn borrow_section(&self, path: Lookup<'text>) -> &AssemblerNode<'text> {
        let path = path.resolve(&self.current_path);
        let mut current = &self.root;

        for name in &path {
            let vec = current.get_vec();
            match vec.iter().find(|node| {
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

    pub fn into_tree(self) -> Section<'text> {
        Section { node: self.root }
    }

    pub fn insert_tree(&mut self, path: Lookup<'text>, tree: Section<'text>) {
        let path = path.resolve(&self.current_path);
        todo!("Unwrap and insert the section into our tree")
    }

    fn address_of_label<'a, S>(&mut self, name: &'a [S]) -> Result<CodeAddress, ()>
    where
        S: Into<Cow<'a, str>> + Clone,
    {
        Ok(self.get_or_generate()?.labels
            [&name.iter().map(|s| (*s).clone().into()).collect::<Vec<_>>()])
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
    labels: HashMap<Vec<Cow<'text, str>>, CodeAddress>,
    fixups: Vec<Fixup<'text>>,
    generated: Vec<u8>,
}

#[test]
fn test_assembler() {
    /*
    Pseudo-code
    fn first(a, b) {
        return a
    }

    fn main() {
        while true {
            yield first(69, 420)
        }
    }
    */

    /*
    Pseudo-assembler
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

    /*
     * Assembler API
     */
    let mut asm = Assembler::new();

    asm.with_section("start", |mut asm| {
        asm.with_section("loop", |mut asm| {
            asm.emit_op(Op::PushPrimitive(69.into()));
            asm.emit_op(Op::PushPrimitive(420.into()));
            asm.emit_call(2, "first".into());
            asm.emit_op(Op::Yield);
        });
        asm.emit_jump(Lookup::Relative(vec!["loop".into()]).into())
    });

    asm.with_section("first", |mut asm| {
        asm.emit_op(Op::Pop);
        asm.emit_op(Op::Ret);
    });

    dbg!(asm.assemble());
    assert_eq!(asm.address_of_label(&["start"]), Ok(0));
    assert_eq!(asm.address_of_label(&["start", "loop"]), Ok(0));
    assert_eq!(asm.address_of_label(&["first"]), Ok(33));
}
