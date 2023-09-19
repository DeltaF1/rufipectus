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

pub static GlobalClassNames: [&'static str; GlobalClassSlots::End as usize] = [
    /* The cyclical powerhouse */
    "Object", "Class", /* Primitive classes */
    "Bool", "Num", "String", "Null", /* Built-in classes */
    "Sequence", "Range", "List", "Map", "Fn", "Fiber", "System",
];
