module ringoids {
    theory BiMagma {
        include .relations.Carrier
        add: .magmas.Magma {type univ = ..univ} 
        mult: .magmas.Magma {type univ = ..univ}
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
        add: .monoids.CommMonoid
    }

    theory CommSemiring {
        include Semiring
        mult: .monoids.CommMonoid
    }

    theory LeftNearRing {
        include BiMagma 
        add: .groups.Group
        mult: .magmas.Semigroup
        left_distrib:--- mult.op(r, add.op(x, y)) == add.op(mult.op(r, x), mult.op(r, y))
    }

    theory RightNearRing {
        include BiMagma 
        add: .groups.Group
        mult: .magmas.Semigroup
        right_distrib:--- mult.op(add.op(x, y), r) == add.op(mult.op(x, r), mult.op(y, r))
    }

    theory CommLeftNearRing {
        include LeftNearRing
        mult: .magmas.CommSemigroup
    }

    theory CommRightNearRing {
        include RightNearRing
        mult: .magmas.CommSemigroup
    }

    theory Ring {
        include Semiring
        add: .groups.CommGroup
    }

    theory BooleanRing {
        include Ring
        mult: .monoids.IdempotentMonoid
    }

    theory CommRing {
        include Ring
        mult: .monoids.CommMonoid
    }

    theory IntegralDomain {
        include CommRing
        include NoZeroDividers
    }

    theory SkewField {
        include Ring
        include NonZeroInvertible
        include NonTrivialRing
    }

    theory Field {
        include SkewField
        mult: .monoids.CommMonoid
    }

    // The traditional definition of a Lie ring
    theory LieRing {
        include .relations.Carrier
        add: .groups.CommGroup {type univ = ..univ}
        bracket: (univ, univ) -> univ # circumfix ⟨
        bilinear:--- (⟨add.op(x, y), z⟩ == add.op(⟨x, z⟩,⟨y, z⟩)) & (⟨x, add.op(y, z)⟩ == add.op(⟨x, y⟩,⟨x, z⟩))
        alternating:--- ⟨x, x⟩ == add.e
        jacobi:--- add.op(⟨x, ⟨y, z⟩⟩, add.op(⟨y, ⟨z, x⟩⟩, ⟨z, ⟨x, y⟩⟩)) == add.e
    }

    // The Lie ring obtained from a ring by defining the bracket as the commutator
    theory CommutatorLieRing {
        include Ring
        bracket: (univ, univ) -> univ # circumfix ⟨
        // bracket is defined as the commutator, i.e. ⟨x, y⟩ == x*y - y*x
        bracket_defn:--- ⟨x, y⟩ == add.op(mult.op(x, y), add.inv(mult.op(y, x)))

        // derivable from the above
        bilinear:--- (⟨add.op(x, y), z⟩ == add.op(⟨x, z⟩,⟨y, z⟩)) & (⟨x, add.op(y, z)⟩ == add.op(⟨x, y⟩,⟨x, z⟩))
        alternating:--- ⟨x, x⟩ == add.e
        jacobi:--- add.op(⟨x, ⟨y, z⟩⟩, add.op(⟨y, ⟨z, x⟩⟩, ⟨z, ⟨x, y⟩⟩)) == add.e

        // not homogen (for homogen mult needs to be commutative, but then we have ⟨x, y⟩ == add.e, which makes the Lie ring trivial)
    }

    // definitions in MMT

    // theory BilinearRingoid {
    //     include Ringoid
    //     f: (univ, univ) -> univ
    //     bilinear:--- (f(add.op(x, y), z) == add.op(f(x, z),f(y, z))) & (f(x, add.op(y, z)) == add.op(f(x, y),f(x, z)))
    //     homogen:--- (f(mult.op(r, x), y) == mult.op(r, f(x, y))) & (f(x, mult.op(r, y)) == mult.op(r, f(x, y)))
    // }

    // theory LieRing {
    //     include Ring
    //     include BilinearRingoid
    //     bracket: (univ, univ) -> univ # circumfix ⟨
    //     bracket = f
    //     bracket_defn:--- ⟨x, y⟩ == add.op(mult.op(x, y), add.inv(mult.op(y, x)))
    //     jacobi:--- add.op(⟨x, ⟨y, z⟩⟩, add.op(⟨y, ⟨z, x⟩⟩, ⟨z, ⟨x, y⟩⟩)) == add.e
    //     alternating:--- ⟨x, x⟩ == add.e
    // }
}