module kuratowski {
    theory KuratowskiPairs {
        // (a,b) = {{a}, {a, b}}
        include .finite_sets.Singletons
        include .finite_sets.UnorderedPairs
        include .lattice_operations.BigIntersection
        include .lattice_operations.BigUnion
        include .operations.Filter
    }
}
