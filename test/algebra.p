module Algebra {
  theory Carrier {
    type univ
  }
  theory Magma {
    include Carrier
    op: (univ,univ) -> univ
  }
  theory Semigroup {
    include Magma
    assoc: |- forall x,y,z. op(op(x,y),z) == op(x,op(y,z))
  }
  theory Monoidal {
    include Magma
    e: univ
  }
  intAdd = Magma {type univ = int, op = (x,y) -> x+y}
  intMult = Magma {type univ = int, op = (x,y) -> x*y}
  theory BiMagma {
    include Carrier
    add  : Magma {type univ = ..univ}
    mult : Magma {type univ = ..univ}
  }
  intAddMult = BiMagma {type univ = int, add = intAdd, mult = intMult}
}