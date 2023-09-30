class Object {
    static same(obj1, obj2) {
        return ;asm (obj1, obj2) {
            /* native ObjectSame */
			0x22 0x01 0x00 0x00 0x00
        }
    }

	!=(other) { !(this == other) }
	==(other) { Object.same(this, other) }

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
	
	tmp_1=(x) { _tmp_1 = x }
	tmp_1 { _tmp_1 }
	

	subclass_of(class) {
		Class.tmp_1 = this
		while (Class.tmp_1) {
			if (Object.same(Class.tmp_1, class)) {
				return true
			}
			Class.tmp_1 = Class.tmp_1.supertype
		}
		return false
	}

    supertype { ;asm { 0x03 0x01 0x00 0x00 0x00 /* read_field ClassStructure::Supertype */ } }
}

/* Primitive classes */
class Bool {
    ! {
        if (this) {
            return false
        } else {
            return true
        }
    }

    toString {
        if (this) {
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
		return ;asm(this, other) {
			0x22 0x01 0x01 0x00 0x00
		}
	}

	- {
		return ;asm(this) {
			0x22 0x04 0x01 0x00 0x00
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

class Fn {
	static new(f) {
		if (!(f is Fn)) {
			// TODO: error "Argument must be function"
		}
		return f
	}
}

/*
var c = ...
var f = Fn.new {|a, b|
	do some shit with a, b,
	and closed value c
}

->

Class 'Closure {random_id}' is Fn {
	new(c) {
		_0 = c
	}

	call(a,b) {
		do some shit with a,b
		and _0
	}
}
*/

class Fiber {}
class System {
	static print(s) {
		return ;asm(s) {
			/* native Print */
			0x22 0x00 0x02 0x00 0x00
			/* push arg 0 */
			0x05 0x00 0x00 0x00 0x00
		}
	}
}
