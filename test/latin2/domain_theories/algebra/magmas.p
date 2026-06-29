module magmas {
    include .sfol.SFOLEQND
    
    theory Magma {
        include .sets.Set
        op: (U, U) -> U # infix ∘

        // divisibility: .relations.Relation {
        //     type carrier = U
        //     // rel = (x, z) -> texist universe (y -> tequal(universe, x∘y, z))
        // }
    }

    theory MagmaHom {
        include .sets.SetHom
        domain : Magma
        codomain : Magma

        op: ??? // (x) -> tequal(codomain.U, U domain.op(x, y), codomain.op(U x, U y))
    }

    theory SubMagma {
        include .sets.SubSet
        parent: Magma
        op: ???
    }

    theory Commutative {
        include Magma
        comm: ??? // (x) -> x∘y == y∘x
    }

    OppositeMagma: Magma -> Magma = m -> Magma {
        universe = m.universe
        // type U = m.U
        op = (x, y) -> m.op(y,x)
    }

    theory Idempotent {
        include Magma
        idem: ??? // (x) -> x∘x == x
    }

    theory PowerAssociative {
        include Magma
        power_assoc: ??? // (x) -> (x∘x)∘x == x∘(x∘x)
    }

    theory Semigroup {
        include Magma
        assoc: ??? // (x) -> x∘(y∘z) == (x∘y)∘z
    }

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
        point: U
    }

    theory AbsorbingElement {
        include Magma
        abs : U
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