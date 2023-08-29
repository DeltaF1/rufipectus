use crate::runtime::Value;
use crate::CodeAddress;

#[derive(Debug)]
pub struct Stack {
    vec: Vec<Value>,
    frame_start: usize,
}

#[derive(Debug)]
enum StackError {
    Underflow,
}

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

    fn push(&mut self, value: Value) {
        self.vec.push(value)
    }

    fn pop(&mut self) -> Result<Value, StackError> {
        if self.vec.len() < self.frame_start {
            panic!("Something is very wrong. The object stack has been lowered past the current frame in a previous step and went unnoticed.")
        }

        if self.vec.len() == self.frame_start {
            return Err(StackError::Underflow);
        } else {
            Ok(self.vec.pop().expect("Stack.pop underflowed the underlying vec without underflowing the stack frame. {self:?}"))
        }
    }

    fn top(&self) -> &Value {
        &self.vec[self.vec.len()]
    }
}

struct Frame {
    stack_depth: usize,
    ip: CodeAddress,
    this: Value,
}

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

struct ExecutionContext {
    stack: Stack,
    call_stack: CallStack,
    ip: CodeAddress,
    this: Value,
}

impl ExecutionContext {
    fn new(ip: CodeAddress, this: Value) -> Self {
        ExecutionContext {
            stack: Stack::new(),
            call_stack: CallStack::new(),
            this,
            ip,
        }
    }

    fn call(&mut self, n: usize, address: CodeAddress) {
        // The top n elements on the stack are arguments
        // When returning from this call, the stack should be shortened to
        let stack: &mut Stack = &mut self.stack;
        self.call_stack.push(Frame {
            stack_depth: stack.frame_start,
            ip: self.ip,
            this: self.this.clone(),
        });
        stack.frame_start = stack.start_frame(n);

        // ABI is arg0, arg1, .. argn, this
        self.this = stack.pop().unwrap();
    }

    fn tail_call(&mut self, n: usize, address: CodeAddress) {
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

        // Normal calling ABI begins
        self.this = stack.pop().unwrap();

        // Tailcall, don't preserve the previous IP
        self.ip = address
    }

    fn ret(&mut self) {
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
