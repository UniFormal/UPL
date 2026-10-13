module groups {
    theory Quasigroup {
        include .magmas.Magma
    }

    theory Loop {
        include Quasigroup
        include .monoids.Monoid
    }

    theory InverseOperator {
        include .magmas.Semigroup
    }

    // weaker variant of unique inverse element, formulated without neutral element
    // usually union of X and WeakInverse usually called InverseX in the literature
    theory WeakInverse {
        include InverseOperator
    }

    theory InverseFun {
        include .monoids.Monoid
        include InverseOperator
    }

    theory InverseExistence {
        include .monoids.Monoid
    }

    theory Group {
        include .monoids.Monoid
        include InverseFun
    }

    theory CommGroup {
        include Group
        include .monoids.CommMonoid
    }

    theory GroupHom {
        include .magmas.MagmaHom
    }
}
