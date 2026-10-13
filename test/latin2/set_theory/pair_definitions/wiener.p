module wiener {
    theory WienerPairs {
        // (a,b) = {{{a},empty},{{b}}}
        include .finite_sets.EmptySet
        include .finite_sets.Singletons
        include .finite_sets.UnorderedPairs
        include .lattice_operations.BigUnion
        include .operations.Filter
    }
}
