class Object {
    static same(obj1, obj2) {
        return #asm (obj1, obj2) {
            native ObjectSame
        }
    }

    ! { false }

    is(class) {

    }

    toString { "Object" }

    type {
        return #asm(this) {
            class
        }
    }
}

class Class {
    // TODO: Class constructor magic
    construct new(num_fields, supertype) {
        _numFields = num_fields
        _supertype = supertype
        _name = ""
        _methods = null
    }

    name {
        return #asm(this) {
            read_field ClassStructure::Name
        }
    }

    supertype { #asm(this) { read_field ClassStruct::Supertype } }
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

class Num {}
class String {}
class Range {}
class Null

class Sequence {}
class List is Sequence {}
class Map is Sequence {}
class Fn {}
class Fiber {}
class System {}
