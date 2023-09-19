class Object {
    static same(obj1, obj2) {
        return ;asm (obj1, obj2) {
            /* native ObjectSame */
        }
    }

    ! { false }

    is(class) {

    }

    toString { "Object" }

    type {
        return ;asm(this) {
            /* class */
        }
    }
}

class Class is Object {
    name {
        return ;asm(this) {
            /* read_field ClassStructure::Name */
        }
    }

    supertype { ;asm(this) { /* read_field ClassStructure::Supertype */ } }
}

/* Primitive classes */
class Bool {
    ! {
        if this {
            return false
        } else {
            return true
        }
    }

    toString {
        if this {
            return "true"
        } else {
            return "false"
        }
    }
}

class Num {
    *(other) {
        return ;asm(this, other) {
            /* native Multiply */
			0x22 0x01 0x00 0x00 0x00
        }
    }
}

class String {}
class Null {
    ! { true }
}

class Sequence {}
class Range is Sequence {}
class List is Sequence {}
class Map is Sequence {}
class Fn {}
class Fiber {}
class System {}
