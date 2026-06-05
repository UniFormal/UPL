module monoids {
    theory UnitElement {
        include .magmas.Magma
        e : univ
        realize .magmas.Pointed
        point = e
        involution : univ -> bool = x -> (x∘x == e)
    }

    theory RightUnital {
        include UnitElement
        neutralR:--- x∘e == x
    }

    theory LeftUnital {
        include UnitElement
        neutralL:--- e∘x == x
    }

    theory Unital {
        include LeftUnital
        include RightUnital
    }

    theory FirstNonNeutral {
        include Unital
        FirstNonNeutral:--- x != e => forall y. x∘y == x
    }

    theory LastNonNeutral {
        include Unital
        LastNonNeutral:--- y != e => forall x. x∘y == y
    }

    theory Powers {
        include .magmas.PowerAssociative
        include Unital
        power: (univ, nat) -> univ
        power_zero:--- power(x,0) == e
        // power_succ:--- power(x, n+1) == power(x, n) ∘ x
    }

    theory Monoid {
        include .magmas.Semigroup
        include Unital
        inverse: (univ, univ) -> bool = (x, y) -> (x∘y == e) & (y∘x == e)
        inverse_sym:--- inverse(x, y) => inverse(y, x)
        inverse_unique:--- inverse(x, y1) & inverse(x, y2) => (y1 == y2)
        inverse_neutral:--- inverse(e, e)
        inverse_op:--- inverse(x1, x2) & inverse(y1, y2) => inverse(x1∘y1, x2∘y2) 
        involution_inverse:--- (involution(x) => inverse(x, x)) & (inverse(x, x) => involution(x))
    }

    theory Involutory {
        include Monoid
        involutory:--- involution(x)
        inverse_refl:--- inverse(x,x)
        inverse_ident:--- inverse(x,y) => (x == y)
    }

    theory IdempotentMonoid {
        include Monoid
        include .magmas.Band
    }

    theory CommMonoid {
        include Monoid
        include .magmas.CommSemigroup
    }

    theory BoundedSemilattice {
        include .magmas.Semilattice
        include CommMonoid
    }
}