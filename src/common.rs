pub type CodeAddress = u32;
pub type StringAddress = u32;

// TODO: Put this in common for use by the compiler
#[repr(usize)]
pub enum GlobalClassSlots {
    /* The cyclical powerhouse */
    Object = 0,
    Class,

    /* Primitive classes */
    Bool,
    Num,
    String,

    Null,

    /* Built-in classes */
    Sequence,
    Range,
    List,
    Map,
    Fn,
    Fiber,
    System,

    End,
}

impl TryFrom<usize> for GlobalClassSlots {
    type Error = ();
    fn try_from(u: usize) -> Result<Self, Self::Error> {
        if u >= (Self::End as usize) {
            Err(())
        } else {
            Ok(unsafe { std::mem::transmute(u) })
        }
    }
}

pub static GlobalClassNames: [&'static str; GlobalClassSlots::End as usize] = [
    /* The cyclical powerhouse */
    "Object", "Class", /* Primitive classes */
    "Bool", "Num", "String", "Null", /* Built-in classes */
    "Sequence", "Range", "List", "Map", "Fn", "Fiber", "System",
];
