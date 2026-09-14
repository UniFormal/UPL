module magmas {
    theory Magma {
        include .sets.Set
    }

    theory MagmaHom {
        include .sets.SetHom
    }

    theory SubMagma {
        include .sets.SubSet
    }

    theory Commutative {
        include Magma
    }

    // OppositeMagma: Magma -> Magma = m -> §{
    // }

    theory Idempotent {
        include Magma
    }

    // OppositeCommMagma: Commutative -> Commutative = m -> §{
    //     include OppositeMagma
    // }

    theory PowerAssociative {
        include Magma
    }

    theory Semigroup {
        include Magma
    }

    // OppositeSemigroup: Semigroup -> Semigroup = s -> §{
    //     include OppositeMagma
    // }

    theory CommSemigroup {
        include Semigroup
        include Commutative
    }

    theory Band {
        include Semigroup
        include Idempotent
    }

    theory CommIdempotent {
        include Idempotent
        include Commutative
    }

    theory Semilattice {
        include CommSemigroup
        include Band
        include CommIdempotent
    }

    theory Pointed {
        include .sets.Set
    }

    theory AbsorbingElement {
        include Magma
    }

    theory RightAbsorptive {
        include AbsorbingElement
    }

    theory LeftAbsorptive {
        include AbsorbingElement
    }

    theory Absorptive {
        include LeftAbsorptive
        include RightAbsorptive
    }
}
