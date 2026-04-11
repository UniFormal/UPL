module relations {
    theory Carrier {
        type univ
    }

    theory Relation {
        include Carrier
        rel: (univ,univ) -> bool # infix %
    }

    theory Reflexivity {
        include Relation
        refl:--- x % x
    }

    theory Symmetry {
        include Relation
        sym:--- x % y => y % x
    }

    theory Transitivity {
        include Relation
        trans:--- (x % y) => (y % z) => (x % z)
    }

    theory Preorder {
        include Reflexivity
        include Transitivity
    }

    theory PER {
        include Symmetry
        include Transitivity
    }

    theory SubCarrier {
        include Carrier
        per: PER {type univ = ..univ}
        perapply # infix % = per.rel
    }

    theory EquivalenceRelation {
        include Preorder
        include Symmetry
    }

    theory Congruence {
        include Relation
        congT:--- (x % y) => forall T. (T(x) % T(y))
    }

    theory EquivalenceCongruence {
        include EquivalenceRelation
        include Congruence
    }

    theory AntiSymmetry {
        include Relation
        antisym:--- (x % y) => (y % x) => (x == y)
    }

    theory PartialOrder {
        include Preorder
        include AntiSymmetry
    }

    theory Totality {
        include Relation
        total:--- (x % y) | (y % x)
    }

    theory TotalOrder {
        include PartialOrder
        include Totality
    }
}