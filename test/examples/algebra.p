module Algebra {
  theory Carrier {
    type univ
  }
  theory Relation {
    include Carrier
    rel: (univ,univ) -> bool # infix %  // # declares notation
  }
  theory Reflexive {
    include Relation
    refl:--- x % x  // :--- abbreviates axiom for universal closure
  }
  theory Transitive {
    include Relation
    trans:--- x%y & y%z => x%z
  }
  theory Symmetric {
    include Relation
    sym:--- x%y => y%x
  }
  theory Preorder {
    include Reflexive
    include Transitive
  }
  theory PER {
    include Symmetric
    include Transitive
  }
  theory Equivalence {
    include PER
    include Preorder
  }
  theory SubCarrier {
    include Carrier
    per: PER {type univ = ..univ}  // .. accesses surrounding theory
    perapply # infix % = per.rel
  }
  theory Magma {
    include Carrier
    op: (univ,univ) -> univ # infix ∘
  }
  theory SubMagma {
    include SubCarrier
    include Magma
    op_per:--- x1 % y1 & x2 % y2 => (x1∘y1) % (x2∘y2)
  }
  theory Semigroup {
    include Magma
    assoc:--- x∘(y∘z) == (x∘y)∘z
  }
  theory Abelian {
    include Magma
    comm:--- x∘y == y∘x
  }
  theory Pointed {
    include Magma
    e: univ
  }
  theory Monoid {
    include Pointed
    neutL:--- e∘x==x
    neutR:--- x∘e==x
  }
  theory SubMonoid {
    include SubMagma
    include Monoid
    e_per:--- e % e
  }
  theory Idempotent {
    include Magma
    idem:--- x∘x==x
  }
  theory Semilattice {
    include Abelian
    include Idempotent
  }
  theory BoundedSemilattice {
    include Semilattice
    include Monoid
  }
  theory Group {
    include Monoid
    inv: univ -> univ # postfix ⁻
    invL:--- x∘x⁻ == e
    invR:--- x⁻ ∘ x == e
  }
  theory SubGroup {
    include SubMonoid
    include Group
    inv_per:--- x % y => x⁻ % y⁻
  }
  theory AbelianGroup {
    include Group
    include Abelian
  }

  // for theory H:
  // H {d1, ...} abbreviates {include H, d1, ...}
  theory BiMagma {
    include Carrier
    // add must be a model of {type univ == ..univ, op: (univ,univ) -> univ}
    add  : Magma {type univ = ..univ} // .. accesses surrounding theory
    mult : Magma {type univ = ..univ}
  }
  // intAdd is a model of Magma, by extending it with definitions for all abstract fields
  intAdd  = Magma {type univ = int, op = (x,y) -> x+y}
  intMult = Magma {type univ = int, op = (x,y) -> x*y}
  intAddMult = BiMagma {type univ = int, add = intAdd, mult = intMult}

  theory Rng {
    include BiMagma
    add:  AbelianGroup
    mult: Semigroup
  }
  theory Ring {
    include Rng
    mult: Monoid
  }
  theory AbelianRing {
    include Ring
    mult: Abelian
  }
  theory SemiField {
    include AbelianRing
    mult: SubGroup {
      per = PER {
        rel = (x,y) -> x == y & x != e
        sym = ???
        trans = ???
      }
    }
    inv_zero:--- mult.inv(add.e) == add.e
  }
  theory Field {
    include SemiField
    mult: Abelian
  }
}