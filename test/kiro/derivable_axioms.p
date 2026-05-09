module derivable_axioms {
    theory Carrier {
        type univ
    }
    theory Magma {
        include Carrier
        op: (univ,univ) -> univ # infix ∘
    }
    theory Semigroup {
        include Magma
        assoc:--- x∘(y∘z) == (x∘y)∘z
    }
    theory Monoid {
        include Semigroup
        e: univ
        neutL:--- e∘x==x
        neutR:--- x∘e==x
    }
    theory Group {
        include Monoid
        inv: univ -> univ # postfix ⁻
        invL:--- x∘x⁻ == e
        invR:--- x⁻ ∘ x == e
    }

    theory HomMagma {
        M : Magma
        N : Magma
        univ : M -> N
        op:--- univ(x∘y) == univ(x)∘univ(y)
    }

//---------------------------------------------------------------

    theory HomSemigroup {
        include HomMagma
        M : Semigroup
        N : Semigroup
    }

    theory HomMonoid {
        include HomSemigroup
        M : Monoid
        N : Monoid
        e:--- univ(M.e) == N.e
    }

    theory HomGroup {
        include HomMagma
        M : Group
        N : Group
        // e and inv axioms are derivable from op in the context of groups
    }
}