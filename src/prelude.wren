class Object {
    static same(obj1, obj2) {
        return ;asm (obj1, obj2) {
            /* native ObjectSame */
			0x22 0x01 0x00 0x00 0x00
        }
    }

    ! { false }

    is(class) {
		return this.type.subclass_of(class)
    }

    toString { "Object" }

    type {
        return ;asm(this) {
            /* class */
			0x1f
        }
    }
}

class Class is Object {
    name {
        return ;asm(this) {
            /* read_field ClassStructure::Name */
			0x03 0x02 0x00 0x00 0x00
        }
    }

	subclass_of(class) {
		_Class_tmp_1 = this
		while (_Class_tmp_1) {
			if Object.same(_Class_tmp_1, class) {
				return true
			}
			_Class_tmp_1 = _Class_tmp_1.supertype
		}
		return false
	}

    supertype { ;asm { 0x03 0x01 0x00 0x00 0x00 /* read_field ClassStructure::Supertype */ } }
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
			0x22 0x00 0x01 0x00 0x00
        }
    }

	+(other) {
		// FIXME: This is multiplying
		return ;asm(this, other) {
			0x22 0x00 0x01 0x00 0x00
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
class System {
	static print(s) {
		;asm(s) {
			/* native Print */
			0x22 0x01 0x01 0x00 0x00	
		}
	}
}
