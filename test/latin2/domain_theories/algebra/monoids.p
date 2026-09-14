module monoids {
    theory UnitElement {
        include .magmas.Magma
    }

    theory RightUnital {
        include UnitElement
    }

    theory LeftUnital {
        include UnitElement
    }

    theory Unital {
        include LeftUnital
        include RightUnital
    }

    // Two variants of magmas in which the composition of some elements returns the first/last one that is not the neutral element.
    // These are rather uninteresting theories, but they are helpful in the Option monad (with None as the neutral element).
    theory FirstNonNeutral {
        include Unital
    }

    theory LastNonNeutral {
        include Unital
    }

    theory Powers {
        include .magmas.PowerAssociative
        include Unital
        include .nat_axiomatic.NatLiterals
    }

    theory Monoid {
        include .magmas.Semigroup
        include Unital
    }

    theory Involutory {
        include Monoid
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
