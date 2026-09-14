module rel_basics {
    theory Relation {
        include .sets.Set
    }

    theory Reflexivity {
        include Relation
    }

    theory Symmetry {
        include Relation
    }

    theory Transitivity {
        include Relation
    }

    theory Preorder {
        include Reflexivity
        include Transitivity
    }

    theory EquivalenceRelation {
        include Preorder
        include Symmetry
    }

    theory AntiSymmetry {
        include Relation
    }
}
