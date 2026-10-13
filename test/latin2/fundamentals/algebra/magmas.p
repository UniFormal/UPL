module meta_magmas {    
    theory Magma {
        include .relations.EqualityType
        op: (carrier, carrier) -> carrier # infix ∘
    }

    // theory MagmaHom {
    //     include .sets.SetHom
    //     domain : Magma
    //     codomain : Magma

    //     op: ??? // (x) -> tequal(codomain.U, U domain.op(x, y), codomain.op(U x, U y))
    // }

    // theory SubMagma {
    //     include .sets.SubSet
    //     parent: Magma
    //     op: ???
    // }

    theory Commutative {
        include Magma
        comm: ??? // (x:carrier,y:carrier) -> (x∘y) == (y∘x)
    }

    // OppositeMagma: Magma -> Magma = m -> §{
    // }

    theory Idempotent {
        include Magma
        idem:--- (x∘x) == x
    }

    // OppositeCommMagma: Commutative -> Commutative = m -> §{
    //     include OppositeMagma
    // }

    theory PowerAssociative {
        include Magma
        power_assoc: ??? // (x) -> (x∘x)∘x == x∘(x∘x)
    }

    theory Semigroup {
        include Magma
        assoc: ??? // (x) -> x∘(y∘z) == (x∘y)∘z
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
        include Commutative
        include Idempotent
    }

    theory Semilattice {
        include CommSemigroup
        include Band
        include CommIdempotent
    }

    theory Pointed {
        include Magma
        point: carrier
    }

    theory AbsorbingElement {
        include Magma
        abs : carrier
        realize Pointed
        point = abs
    }

    theory RightAbsorptive {
        include AbsorbingElement
        absorbR: ??? // (x) -> x∘abs == x
    }

    theory LeftAbsorptive {
        include AbsorbingElement
        absorbL: ??? // (x) -> abs∘x == x
    }

    theory Absorptive {
        include LeftAbsorptive
        include RightAbsorptive
    }
}