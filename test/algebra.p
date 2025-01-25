module Algebra {
  theory Carrier {
    type U
  }
  theory Magma {
    include Carrier
    op: (U,U) -> U
  }
  theory Semigroup {
    include Magma
    assoc: |- forall x,y,z. op(op(x,y),z) == op(x,op(y,z))
  }
  theory Monoidal {
    include Magma
    e: U
  }
  intAdd = Magma {type U = int, op = (x,y) -> x+y}
  intMult = Magma {type U = int, op = (x,y) -> x*y}
  theory BiMagma {
    include Carrier
    add  : Magma {type U = U}
    mult : Magma {type U = U}
  }
}

// int = BiMagma {type U = int, add = intAdd, mult = intMult}