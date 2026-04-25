module hom {
    theory Carrier {
        type univ
    }


    theory Relation {
        include Carrier
        rel: (univ,univ) -> bool # infix %
    }
    theory Transitive {
        include Relation
        trans:--- x%y & y%z => x%z
    }
    theory Symmetric {
        include Relation
        sym:--- x%y => y%x
    }
    theory PER {
        include Symmetric
        include Transitive
    }

    theory Magma {
        include Carrier
        op: (univ,univ) -> univ # infix ∘
    }

    theory HomMagma {
        M : Magma
        N : Magma
        h : M -> N
        isHom:--- h(x∘y) == h(x)∘h(y)
    }


    theory Semigroup {
        include Magma
        assoc:--- x∘(y∘z) == (x∘y)∘z
    }

    theory HomSemigroup {
        include HomMagma
        M : Semigroup
        N : Semigroup
    }

    theory Pointed {
        include Carrier
        e: univ
    }
    theory Monoid {
        include Semigroup
        include Pointed
        neutL:--- e∘x==x
        neutR:--- x∘e==x
    }
    theory Group {
        include Monoid
        inv: univ -> univ # postfix ⁻
        invL:--- x∘x⁻ == e
        invR:--- x⁻ ∘ x == e
    }

}