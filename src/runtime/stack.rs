use crate::runtime::Value;
use crate::CodeAddress;
use std::error::Error;

#[derive(Debug)]
pub struct Stack {
    vec: Vec<Value>,
    frame_start: usize,
}

#[derive(Debug)]
pub enum StackError {
    Underflow,
}

impl std::fmt::Display for StackError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> Result<(), std::fmt::Error> {
        write!(f, "{:?}", self)
    }
}

impl Error for StackError {}

impl Stack {
    fn new() -> Self {
        Stack {
            vec: vec![],
            frame_start: 0,
        }
    }

    fn full_depth(&self) -> usize {
        self.vec.len()
    }

    fn local_depth(&self) -> usize {
        self.vec.len() - self.frame_start
    }

    fn start_frame(&mut self, n: usize) -> usize {
        self.frame_start = self.full_depth() - n; // TODO: Underflow
        self.frame_start
    }

    pub fn push(&mut self, value: Value) {
        self.vec.push(value)
    }

    pub fn pop(&mut self) -> Result<Value, StackError> {
        if self.vec.len() < self.frame_start {
            panic!("Something is very wrong. The object stack has been lowered past the current frame in a previous step and went unnoticed.")
        }

        if self.vec.len() == self.frame_start {
            Err(StackError::Underflow)
        } else {
            Ok(self.vec.pop().unwrap_or_else(||panic!("Stack.pop underflowed the underlying vec without underflowing the stack frame. {self:?}")))
        }
    }

    pub fn top(&self) -> &Value {
        self.peek_from_top(0)
    }

    // TODO: Error if below frame start?
    pub fn peek_from_top(&self, n: usize) -> &Value {
        &self.vec[self.vec.len() - (n + 1)]
    }

    pub fn peek_from_frame(&self, n: usize) -> &Value {
        &self.vec[self.frame_start + n]
    }
}

#[derive(Debug)]
struct Frame {
    stack_depth: usize,
    ip: CodeAddress,
    this: Option<Value>,
}

#[derive(Debug)]
struct CallStack {
    vec: Vec<Frame>,
}

impl CallStack {
    fn new() -> Self {
        CallStack { vec: vec![] }
    }

    fn pop(&mut self) -> Option<Frame> {
        self.vec.pop()
    }

    fn push(&mut self, frame: Frame) {
        self.vec.push(frame)
    }
}

#[derive(Debug)]
pub struct ExecutionContext {
    pub stack: Stack,
    call_stack: CallStack,
    pub ip: CodeAddress,
    pub this: Option<Value>,
}

impl ExecutionContext {
    pub fn new(ip: CodeAddress) -> Self {
        ExecutionContext {
            stack: Stack::new(),
            call_stack: CallStack::new(),
            this: None,
            ip,
        }
    }

    pub fn call(&mut self, n: usize, address: CodeAddress) {
        // The top n elements on the stack are arguments
        // When returning from this call, the stack should be shortened to
        let stack: &mut Stack = &mut self.stack;
        self.call_stack.push(Frame {
            stack_depth: stack.frame_start,
            ip: self.ip,
            this: self.this.clone(),
        });
        stack.frame_start = stack.start_frame(n);
        self.this = None;
        self.ip = address;
    }

    pub fn tail_call(&mut self, n: usize, address: CodeAddress) {
        // A, B, C, D, E, F
        //        ^
        //        |------- stack.frame_start
        //
        // tail_call(2)
        //
        // Delete all items between frame_start and the top n items
        //
        // A, B, C, E, F
        //        ^
        //        |------- stack.frame_start

        let stack = &mut self.stack;

        if n > stack.local_depth() {
            panic!("Stack underflow")
        }

        {
            let vec = &mut stack.vec;

            // Copy the n args from the top of the stack into the base of the stack frame
            let arg_start = vec.len() - n;
            let (destination, args) = vec.split_at_mut(arg_start);
            destination[stack.frame_start..].swap_with_slice(args);

            // Delete the rest of the stack frame in preparation for the call
            vec.truncate(stack.frame_start + n)
        }

        // Tailcall, don't preserve the previous IP
        self.this = None;
        self.ip = address;
    }

    pub fn ret(&mut self) {
        let frame = self
            .call_stack
            .pop()
            .expect("Tried to return with no call frame on the stack!");
        self.ip = frame.ip;
        self.this = frame.this;

        let stack = &mut self.stack;

        let retval = stack.top().clone();

        // Unwind back to the previous stack frame
        stack.vec.truncate(stack.frame_start);

        stack.push(retval);

        // Reset the stack's current frame pointer to the previous one
        self.stack.frame_start = frame.stack_depth;
    }
}
