module magmas {
    theory Magma {
        include .relations.Carrier
        op: (univ,univ) -> univ # infix ∘
    }

    theory MagmaHom {
        M : Magma
        N : Magma
        univ : M -> N
        op:--- univ(x∘y) == univ(x)∘univ(y)
    }

    theory SubMagma {
        include .relations.SubCarrier
        include Magma
        op_rel:--- (x1 % y1) & (x2 % y2) => (x1∘y1) % (x2∘y2)
    }

    theory Commutative {
        include Magma
        comm:--- x∘y == y∘x
    }

    OppositeMagma: Magma -> Magma = m -> Magma {
        type univ = m.univ,
        op = (x, y) -> m.op(y,x)
    }

    theory Idempotent {
        include Magma
        idem:--- x∘x == x
    }

    theory PowerAssociative {
        include Magma
        power_assoc:--- (x∘x)∘x == x∘(x∘x)
    }

    theory Semigroup {
        include Magma
        assoc:--- x∘(y∘z) == (x∘y)∘z
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
        point: univ
    }

    theory AbsorbingElement {
        include Magma
        abs : univ
        realize Pointed
        point = abs
    }

    theory RightAbsorptive {
        include AbsorbingElement
        absorbR:--- x∘abs == x
    }

    theory LeftAbsorptive {
        include AbsorbingElement
        absorbL:--- abs∘x == x
    }

    theory Absorptive {
        include LeftAbsorptive
        include RightAbsorptive
    }
}