module Algebra {
  class Carrier {
    type U
  }
  class Magma {
    include Carrier
    op: (U,U) -> U
  }
  class Semigroup {
    include Magma
    assoc: |- forall x,y,z. op(op(x,y),z) == op(x,op(y,z))
  }
  class Monoidal {
    include Magma
    e: U
  }
  intAdd = Magma {type U = int, op = (x,y) -> x+y}
  intMult = Magma {type U = int, op = (x,y) -> x*y}
  class BiMagma {
    include Carrier
    add  : Magma {type U = U}
    mult : Magma {type U = U}
  }
}