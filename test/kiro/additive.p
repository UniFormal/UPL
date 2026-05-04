module additive {
    theory Carrier {
        type univ
    }

    theory Magma {
        include Carrier
        op: (univ,univ) -> univ # infix ∘
    }

    theory Commutative {
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

//-------------------------------------------------------

    theory AdditiveMagma {
        include Magma
        add # infix + = op
    }

    theory AdditiveCommutative {
        include Commutative
        include AdditiveMagma
    }

    theory AdditiveIdempotent {
        include Idempotent
        include AdditiveMagma
    }

    theory AdditiveSemigroup {
        include Semigroup
        include AdditiveMagma
    }

}