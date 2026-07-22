module relations {
    theory OneTyped {
        type carrier
    }

    theory Relation {
        include OneTyped
        type rel(c1: carrier, c2: carrier) // # infix $
    }

    theory Reflexivity {
        include Relation
        refl: x -> rel(x, x)
    }

    theory Symmetry {
        include Relation
        sym: (x,y) -> rel(x, y) -> rel(y, x)
    }

    theory Transitivity {
        include Relation
        trans: (x,y,z) -> rel(x, y) -> rel(y, z) -> rel(x, z)
        // trans3: (x,y,z,w) -> rel(x, y) -> rel(y, z) -> rel(z, w) -> rel(x, w)
        // trans4: (x,y,z,w,v) -> rel(x, y) -> rel(y, z) -> rel(z, w) -> rel(w, v) -> rel(x, v)
    }

    theory Preorder {
        include Reflexivity
        include Transitivity
    }

    theory PER {
        include Symmetry
        include Transitivity
    }

    theory EquivalenceRelation {
        include Preorder
        include Symmetry
    }

    theory Congruence {
        include Relation
        congT: (x, y) -> rel(x, y) -> T -> rel(T x, T y)
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
        // cong: (x, y) -> rel(x, y) -> (A: carrier -> bool) -> |- A x -> |- A y
        cong: (x, y) -> rel(x, y) -> (A: carrier -> bool) -> |- A x -> |- A y

        realize Congruence
        congT = (x, y) -> p -> T -> cong(x,y) p (u -> inhabited@(rel(T x, T u))) refl
    }

    theory EqualityType {
        include OneTyped
        equalityRel: EquivalenceRelation {type carrier = ..carrier}
    }

    theory AntiSymmetry {
        include EqualityType
        include Relation
        // this doesn't work
        antisym: (x, y) -> rel(x, y) -> rel(y, x) -> equalityRel{rel(x, y)}
    }

    theory Order {
        include Preorder
        include AntiSymmetry
    }
}