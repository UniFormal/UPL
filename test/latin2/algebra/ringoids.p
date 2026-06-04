module ringoids {
    // redundant
    theory Magma {
        include .relations.Carrier
        op: (univ,univ) -> univ # infix ∘
    }
    
    theory BiMagma {
        include .relations.Carrier
        // add must be a model of {type univ == ..univ, op: (univ,univ) -> univ}
        add: Magma {type univ = ..univ} // .. accesses surrounding theory
        mult: Magma {type univ = ..univ}
    }

    theory Ringoid {
        include BiMagma
        left_distrib:--- mult.op(r, add.op(x, y)) == add.op(mult.op(r, x), mult.op(r, y))
        right_distrib:--- mult.op(add.op(x, y), r) == add.op(mult.op(x, r), mult.op(y, r))
    }

    theory CommRingoid {
        include Ringoid
        mult: .magmas.CommSemigroup
    }

    theory MonoidalRingoid {
        include Ringoid
        add: .monoids.Monoid
    }

    theory BiMonoid {
        include MonoidalRingoid
        mult: .monoids.Monoid 
    }

    theory NonZeroInvertible {
        include BiMonoid
        multinverse:--- (x != add.e) => exists y. mult.inverse(x, y)
    }

    theory NoZeroDividers {
        include BiMonoid
        no_zero_div:--- (mult.op(x, y) == add.e) => ((x == add.e) | (y == add.e))
    }

    theory NonTrivialRing {
        include BiMonoid
        neq01: |- add.e != mult.e
    }

    theory Semiring {
        include BiMonoid
        add: .monoids.Commutative
    }

    theory CommSemiring {
        include Semiring
        include .magmas.Commutative
    }

    theory NearRing {
        include BiMonoid 
        add: .groups.Group
    }

    theory CommNearRing {
        include NearRing
        include CommRingoid
    }

    theory Ring {
        include NearRing
        add: .magmas.Commutative
    }

    theory BooleanRing {
        include Ring
        mult: IdempotentMonoid
    }

    theory CommRing {
        include Ring
        include .magmas.Commutative
    }

    theory IntegralDomain {
        include CommGroup
        include NoZeroDividers
    }

    theory SkewField {
        include Ring
        include NonZeroInvertible
        include NonTrivialRing
    }

    theory Field {
        include SkewField
        include CommRingoid
    }

    theory BilinearRingoid {
        include Ringoid
        f: (univ, univ) -> univ
        bilinear:--- f(add.op(x, y), z) == add.op(f(x, z),f(y, z)) 
    }
}