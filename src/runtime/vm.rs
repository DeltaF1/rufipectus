use crate::bytecode;
use crate::bytecode::{NativeCall, Op};
use crate::runtime;
use crate::runtime::SafeFloatToInt;
use crate::runtime::Value;
use crate::CodeAddress;
use std::error::Error;

// TODO: if Op is variable length on-disk, then CodeAddress either needs to point to byte
// locations, or we need to decode the whole thing into Ops ahead of time
fn run(code: &[Op], address: CodeAddress) -> Result<Value, Box<dyn Error>> {
    let mut ctx = runtime::ExecutionContext::new(address);
    let mut i = 0;
    loop {
        let op = &code[ctx.ip as usize];
        ctx.ip += 1;
        //dbg!(&ctx, op);
        match op {
            Op::Dup => {
                let top = ctx.stack.top().clone();
                ctx.stack.push(top);
            }
            Op::Pop => {
                ctx.stack.pop()?;
            }
            Op::Peek(n) => {
                let peeked = ctx.stack.peek_from_top(*n).clone();
                ctx.stack.push(peeked);
            }
            Op::ReadField(n) => {
                match ctx
                    .this
                    .as_ref()
                    .expect("Tried to read field {n} outside of a method")
                {
                    Value::Object(ref object_ref) => {
                        let fields = object_ref.borrow_fields();
                        let value = fields[*n].clone();
                        ctx.stack.push(value);
                    }
                    x => panic!("Tried to read field {n} of non-object {x:?}"),
                }
            }
            Op::WriteField(n) => {
                match ctx
                    .this
                    .as_ref()
                    .expect("Tried to write field {n} outside of a method")
                {
                    Value::Object(ref object_ref) => {
                        let mut fields = object_ref.borrow_fields_mut();
                        let value = ctx.stack.pop()?;
                        fields[*n] = value;
                    }
                    x => panic!("Tried to write field {n} of non-object {x:?}"),
                }
            }
            Op::PushArg(n) => {
                let value = ctx.stack.peek_from_frame(*n).clone();
                ctx.stack.push(value);
            }
            Op::PushLocal(_n) | Op::PopIntoLocal(_n) => todo!("Where are locals stored..."),
            Op::PushGlobal(n) => {
                ctx.stack.push(unsafe { runtime::GLOBAL_STATE[*n].clone() });
            }
            Op::PopIntoGlobal(n) => {
                let len = unsafe { runtime::GLOBAL_STATE.len() };

                if *n < len {
                    unsafe {
                        runtime::GLOBAL_STATE[*n] = ctx.stack.pop()?;
                    }
                } else {
                    unsafe {
                        runtime::GLOBAL_STATE.resize_with(*n, Value::null);
                        runtime::GLOBAL_STATE.push(ctx.stack.pop()?);
                    }
                }
            }
            Op::PushPrimitive(primitive) => {
                let value = match primitive {
                    bytecode::Primitive::Null => Value::null(),
                    bytecode::Primitive::Number(f) => {
                        Value::Primitive(runtime::PrimitiveValue::Number(*f))
                    }
                    bytecode::Primitive::Boolean(b) => {
                        Value::Primitive(runtime::PrimitiveValue::Boolean(*b))
                    }
                };
                ctx.stack.push(value);
            }
            Op::PushThis => ctx.stack.push(
                ctx.this
                    .clone()
                    .expect("Tried to reference this outside of a method"),
            ), // TODO: ok_or NoThisError
            Op::PopThis => ctx.this = Some(ctx.stack.pop()?),
            Op::Jump(offset) => ctx.ip = ctx.ip.wrapping_add_signed(*offset),
            Op::JumpIf(offset) => {
                let value = ctx.stack.pop()?;
                if value.truthy() {
                    ctx.ip = ctx.ip.wrapping_add_signed(*offset)
                }
            }
            Op::CallDirect(arity, address) => ctx.call(*arity, *address),
            Op::CallNamed(_signature) => {
                todo!("Runtime method lookup")
            }
            Op::Ret => ctx.ret(),
            Op::RetNull => {
                ctx.stack.push(Value::null());
                ctx.ret();
            }
            Op::Yield => return Ok(ctx.stack.pop()?),
            Op::YieldNull => return Ok(Value::null()),
            Op::NativeCall(tag) => {
                match tag {
                    NativeCall::NewObject => {
                        let class: runtime::ObjectRef = ctx.stack.pop()?.try_into()?;
                        let num_fields: f64 = ctx.stack.pop()?.try_into()?;

                        let obj = runtime::ObjectRef::new(class, exact_repeat::exact_repeat(num_fields.to_int()?, Value::null()));
                        ctx.stack.push(obj.into());
                    },
                    NativeCall::Multiply => {
                        let b: f64 = ctx.stack.pop()?.try_into()?;
                        let a: f64 = ctx.stack.pop()?.try_into()?;
                        let c = a * b;
                        ctx.stack.push(c.into());
                    },
                    NativeCall::Unimplemented => panic!("Tried to execute an unimplemented built-in method. This binary may be out-of-date with the bytecode"),
                    NativeCall::UserDefined(tag) => todo!("User-pluggable native functions")
                }
            }
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::runtime::GlobalClassSlots;
    #[test]
    fn stack_ops() {
        let code = vec![
            Op::PushPrimitive(bytecode::Primitive::Number(69.0)),
            Op::PushPrimitive(bytecode::Primitive::Number(420.0)),
            Op::CallDirect(2, 4),
            Op::Yield,
            // fn first(a, b) {
            //      return a
            //  }
            Op::Pop,
            Op::Ret,
        ];

        let output = run(&code, 0).unwrap();
        assert_eq!(output, 69.0.into());
    }

    #[test]
    fn area_example() {
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
         s.area

        */
        let code: Vec<bytecode::Op> = vec![
            /* Class */
            // TODO: Some of these methods should be un-reachable by user code. Putting a space in
            // the name seems to be how Wren does it for init methods and metaclasses
            // TODO: Dynamic methods pointer should be set here as well
            /* new(num_fields,supertype) */
            /* [0] */
            Op::PopThis,
            // Number of fields for instances of this class
            Op::ReadField(0),
            Op::PushThis,
            // Stack looks like: arg0, arg1, num_fields, this
            Op::NativeCall(NativeCall::NewObject),
            // Stack looks like: arg0, arg1, newobj
            // TODO: This method can be global and then do a Jump to the correct init?
            Op::CallDirect(3, (6)),
            Op::Ret,
            /* new init(num_fields, supertype) */
            /* [6] */ Op::PopThis,
            Op::WriteField(1),
            Op::WriteField(0),
            Op::PushThis,
            Op::Ret,
            /* Num */
            /* *(_) */
            /* [11] */
            Op::NativeCall(NativeCall::Multiply),
            Op::Ret,
            /* Rectangle */
            /* width */
            // Normal method prelude
            /* [13] */
            Op::PopThis,
            Op::ReadField(0),
            Op::Ret,
            /* height */
            /* [16] */ Op::PopThis,
            Op::ReadField(1),
            Op::Ret,
            /* new init (width,height) */
            /* [19] */ Op::PopThis,
            Op::PushArg(0), // Can be optimized since args are already on top of stack
            Op::WriteField(0),
            Op::PushArg(1),
            Op::WriteField(1),
            // Standard init epilogue
            Op::PushThis,
            Op::Ret,
            /* area() */
            /* [26] */ Op::PopThis,
            Op::ReadField(1),
            Op::ReadField(0),
            Op::CallDirect(2, (11)), /* Num *(_) */
            Op::Ret,
            /* Rectangle metaclass */
            /* new(_,_) */
            /* [31] */
            Op::PopThis,
            // Number of fields for instances of this class
            Op::ReadField(0),
            Op::PushThis,
            // Stack looks like: arg0, arg1, num_fields, this
            Op::NativeCall(NativeCall::NewObject),
            // Stack looks like: arg0, arg1, newobj
            // TODO: This method can be global and then do a Jump to the correct init?
            Op::CallDirect(3, (19)), /* Rectangle new init(_, _) */
            Op::Ret,
            /* Square */
            /* new init(_) */
            /* [37] */
            Op::PopThis, // Can be peephole optimized as Op::Dup, Op::PopThis
            //Op::PushThis,
            //Op::PushPrimitive("Square".into()),
            //Op::PopIntoGlobal(100), todo!("Store in class obj"),
            Op::PushArg(0), // Can be optimized since arg0 is already top of stack
            Op::PushArg(0),
            Op::PushThis,
            Op::CallDirect(3, (19)), /* Rectangle new init(_, _) */
            Op::Ret,
            /* foo */
            // No need to PopThis since we're calling into the method and don't need to do anything
            // with `this`
            /* [43] */
            Op::CallDirect(1, (16)), /* Rectangle height */
            Op::Ret,
            /* Square metaclass */
            /* new(_) */
            /* [45] */
            Op::PopThis,
            Op::ReadField(0),
            Op::PushThis,
            Op::NativeCall(NativeCall::NewObject),
            Op::CallDirect(2, (37)), /* Square new init(_) */
            Op::Ret,
            // TODO: Generate static strings table
            // TODO: Generate ClassDef method tables

            /* _start */
            // Rectangle metaclass
            /* [51] */
            Op::PushPrimitive(4.into()),
            Op::PushGlobal(GlobalClassSlots::Class as usize),
            Op::Dup,
            Op::CallDirect(3, (0)), /* Class new(_,_) */
            // Rectangle
            Op::PushPrimitive(2.into()), // _width, _height
            Op::PushGlobal(GlobalClassSlots::Object as usize), // Rectangle is Object
            Op::Peek(2),                 // Get the metaclass
            // TODO: Op::Yoink(n) to grab without copying
            Op::CallDirect(3, (0)),   /* Class new(_,_) */
            Op::PopIntoGlobal((100)), /* Random free slot to hold Rectangle */
            // Square metaclass
            Op::PushPrimitive(5.into()), // 4 normal class + one for static member
            Op::PushGlobal(GlobalClassSlots::Class as usize),
            Op::PushGlobal(GlobalClassSlots::Class as usize),
            Op::CallDirect(3, (0)), /* Class new(_,_) */
            // Square
            Op::PushPrimitive(2.into()), // _width, _height
            Op::PushGlobal((100)),       /* Square is Rectangle */
            Op::Peek(2),                 // Get the metaclass
            Op::CallDirect(3, (0)),      /* Class new(_,_) */
            Op::PopIntoGlobal((101)),    /* Random free slot to hold Square */
            /* main */
            Op::PushPrimitive(10.into()),
            Op::PushGlobal((101)),
            Op::CallDirect(2, (45)), /* Square new(_) */
            // Pairs of pop, push on the same target
            // can be optimized to a Dup then pop
            Op::PopIntoGlobal((102)), /* address of var s */
            Op::PushGlobal((102)),
            Op::CallDirect(1, (26)), /* Rectangle area */
            Op::Yield,
        ];

        let start = (51); /* _start */

        let (class, object, _) = runtime::bootstrap_class();

        unsafe {
            runtime::GLOBAL_STATE.resize_with(GlobalClassSlots::End as usize, Value::null);
            runtime::GLOBAL_STATE[GlobalClassSlots::Object as usize] = object.into();
            runtime::GLOBAL_STATE[GlobalClassSlots::Class as usize] = class.into();
        }

        let output = run(&code, start);
        dbg!(&output);
        assert_eq!(output.unwrap(), 100.0.into());
    }
}