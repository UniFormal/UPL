module combine {
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

    // Commutative + Idempotent
    theory CommutativeIdempotent {
        include Commutative
        include Idempotent
    }

    // Commutative + Semigroup
    theory CommutativeSemigroup {
        include Commutative
        include Semigroup
    }

    // Idempotent + Semigroup (a semigroup where every element is idempotent is called a Band)
    theory Band {
        include Idempotent
        include Semigroup
    }

    // Commutative + Idempotent + Semigroup (a commutative band is called a Semilattice)
    theory Semilattice {
        include CommutativeIdempotent
        include Semigroup
    }
}