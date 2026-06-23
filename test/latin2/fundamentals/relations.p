module relations {
    theory OneTyped {
        type carrier
    }

    theory Relation {
        include OneTyped
        rel: (carrier,carrier) -> bool # infix $
    }

    theory Reflexivity {
        include Relation
        refl:--- x$x
    }

    theory Symmetry {
        include Relation
        sym:--- x$y => y$x
    }

    theory Transitivity {
        include Relation
        trans:--- x$y => y$z => x$z
        // trans3:--- x$y => y$z => z$w => x$w
        // trans4:--- x$y => y$z => z$w => w$v => x$v
    }

    theory Preorder {
        include Reflexivity
        include Transitivity
    }

    theory PER {
        include Symmetry
        include Transitivity
    }

    theory SubOneTyped {
        include OneTyped
        per: PER {type carrier = ..carrier}
        perapply # infix $ = per.rel
    }

    theory EquivalenceRelation {
        include Preorder
        include Symmetry
    }

    theory Congruence {
        include Relation
        congT:--- x$y => forall T. T x $ T y
    }

    theory EquivalenceCongruence {
        include EquivalenceRelation
        include Congruence
    }

    // Equality is an equivalence-congruence.
    // But semantic equality is even stronger: it allows substitution in objects of any type so that equal objects can never be distinguished.
    // This is different from the syntactic equality used inside a logic, where equal objets cannot be distinguished by logical formulas but might be distinguishable by other judgments.
    theory SemanticEquality {
        include EquivalenceRelation
        cong:--- x$y => forall A:(carrier -> bool). A x => A y
        // realizes Congruence
        congT:--- x$y => forall T:(carrier -> carrier). T x $ T y
    }

    theory EqualityType {
        include OneTyped
        equalityRel: EquivalenceRelation {type carrier = ..carrier}
        relapply # infix $ = equalityRel.rel
    }

    theory AntiSymmetry {
        include EqualityType
        include Relation
        antisym:--- x$y => y$x => equalityRel.rel(x, y)
    }

    theory PartialOrder {
        include Preorder
        include AntiSymmetry
    }

    theory Totality {
        include Relation
        total:--- x$y | y$x
    }

    theory TotalOrder {
        include PartialOrder
        include Totality
    }
}