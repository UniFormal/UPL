module cartesian_product {
    theory OrderedPairs {
        include .setbase.SetBase
    }

    theory Img {
        include OrderedPairs
    }

    theory CartesianProduct {
        include OrderedPairs
    }

    // The Cartesian product with an empty set results in the empty set
    theory CartEmpty {
        include CartesianProduct
        include .finite_sets.EmptySet
    }

    theory CartInter {
        include CartesianProduct
        include .lattice_operations.Intersection
    }

    theory CartUnion {
        include CartesianProduct
        include .lattice_operations.Union
    }

    theory Sigma {
        include OrderedPairs
    }

    theory SigmaEmpty {
        include Sigma
        include .finite_sets.EmptySet
    }

    theory SigmaMod {
        include OrderedPairs
    }
}
