module groups {
    theory Quasigroup {
        include .magmas.Magma
        div_left:--- exists a. a∘x == y
        div_right:--- exists b. b∘x == y
    }

    theory Loop {
        include Quasigroup
        include .monoids.Monoid
    }

    theory InverseOperator {
        include .magmas.Semigroup
        inv: univ -> univ # postfix ⁻
        is_weak_inverse: (univ, univ) -> bool = (x, y) -> x∘(y∘x) == x & y∘(x∘y) == y
    }

    theory WeakInverse {
        include InverseOperator
        weak_inverse:--- is_weak_inverse(x, x⁻)
    }

    theory InverseFun {
        include .monoids.Monoid
        include InverseOperator
        inverseLeft:--- (x⁻)∘x == e
        inverseRight:--- x∘(x⁻) == e
        div: (univ, univ) -> univ = (x, y) -> x∘(y⁻)
        inverse_inv:--- inverse(x, x⁻)
        inv_unit: |- e⁻ == e
        inv_inv:--- (x⁻)⁻ == x
        inv_op:--- (x∘y)⁻ == (y⁻)∘(x⁻)
    }

    theory InverseExistence {
        include .monoids.Monoid
        inverseLeft:--- exists i. i∘x == e
        inverseRight:--- exists i. x∘i == e
    }

    theory Group {
        include .monoids.Monoid
        include InverseFun
    }

    theory CommGroup {
        include Group
        include .magmas.Commutative
    }

    theory GroupHom {
        include .magmas.MagmaHom
        M: Group
        N: Group
    }
}