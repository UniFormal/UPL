module derivable_axioms_2 {
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
        include HomMagma  // Changed from HomMonoid - only need operation preservation
        M : Group
        N : Group
        // Identity preservation is derivable:
        //   univ(M.e)∘univ(M.e) = univ(M.e∘M.e) = univ(M.e), so univ(M.e) is idempotent
        //   In a group, only the identity is idempotent, thus univ(M.e) = N.e
        // Inverse preservation is derivable:
        //   univ(x)∘univ(M.inv(x)) = univ(x∘M.inv(x)) = univ(M.e) = N.e
        //   univ(M.inv(x))∘univ(x) = univ(M.inv(x)∘x) = univ(M.e) = N.e
        //   So univ(M.inv(x)) is the inverse of univ(x), thus univ(M.inv(x)) = N.inv(univ(x))
    }

}