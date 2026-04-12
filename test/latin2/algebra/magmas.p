module magmas {
    theory Magma {
        include .relations.Carrier
        op: (univ,univ) -> univ # infix ∘
    }

    theory SubMagma {
        include .relations.SubCarrier
        include Magma
        op_rel:--- x1 % y1 & x2 % y2 => (x1∘y1) % (x2∘y2)
    }

    theory Abelian {
        include Magma
        comm:--- x∘y == y∘x
    }

    theory Idempotent {
        include Magma
        idem:--- x∘x == x
    }

    theory Semigroup {
        include Magma
        assoc:--- x∘(y∘z) == (x∘y)∘z
    }

    theory AbelianSemigroup {
        include Semigroup
        include Abelian
    }

    theory AbelianIdempotent {
        include Abelian
        include Idempotent
    }

    theory Pointed {
        include Magma
        e: univ
    }
}