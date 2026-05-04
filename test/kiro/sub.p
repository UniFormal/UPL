module sub {
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
    theory Semigroup {
        include Magma
        assoc:--- x∘(y∘z) == (x∘y)∘z
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

    theory SubCarrier {
        include Carrier
        per: PER {type univ = ..univ}
        perapply # infix % = per.rel
    }

//----------------------------------------------------------

    theory SubMagma {
        include Magma
        include SubCarrier
        clos:--- (x%u & y%v) => (x∘y)%(u∘v)
    }

    theory SubSemigroup {
        include Semigroup
        include SubMagma
    }

    theory SubMonoid {
        include Monoid
        include SubSemigroup
        unitClosed:--- e%e
    }

    theory SubGroup {
        include Group
        include SubMonoid
        invClosed:--- x%u => (x⁻)%(u⁻)
    }

}