module views_finite_sets {
    // The views currently still need single theories as a domain and codomain, which
    // forces us to provide spurious named theories. This should be refactored when
    // multi-theory domains and codomains are possible.

    // Views for EmptySet
    theory ExistFilter {
        include .operations.Filter
        include .setbase.EmptyDefinitions
    }

    // EmptyExistFilter: ExistFilter -> .finite_sets.EmptySet = e -> §{
    //     include .setbase.SetBase
    //     include .setbase.EmptyDefinitions
    // }

    theory ComplementIntersection {
        include .lattice_operations.Complement
        include .lattice_operations.Intersection
        include .setbase.EmptyDefinitions
    }

    // EmptyIntersection: ComplementIntersection -> .finite_sets.EmptySet = e -> §{
    //     include .setbase.SetBase
    //     include .setbase.EmptyDefinitions
    // }

    theory ExistDifference {
        include .lattice_operations.Difference
        include .setbase.EmptyDefinitions
    }

    // SelfDifference: ExistDifference -> .finite_sets.EmptySet = e -> §{
    //     include .setbase.SetBase
    //     include .setbase.EmptyDefinitions
    // }

    // Views for Singletons
    // SelfPair: .finite_sets.UnorderedPairs -> .finite_sets.Singletons = s -> §{
    //     include .setbase.SetBase
    // }

    theory EmptyAdjoin {
        include .operations.Adjoin
        include .finite_sets.EmptySet
    }

    // SingleAdjoin: EmptyAdjoin -> .finite_sets.Singletons = s -> §{
    //     include .setbase.SetBase
    // }

    // Views for Uopairs
    // UopairFromAxiom: .axioms.PairingAx -> .finite_sets.UnorderedPairs = u -> §{
    //     include .setbase.SetBase
    // }

    theory SingletonUnion {
        include .finite_sets.Singletons
        include .lattice_operations.Union
    }

    // UopairUnion: SingletonUnion -> .finite_sets.UnorderedPairs = u -> §{
    //     include .setbase.SetBase
    // }

    theory AdjoinSingletons {
        include .operations.Adjoin
        include .finite_sets.Singletons
    }

    // UopairAdjointSingleton: AdjoinSingletons -> .finite_sets.UnorderedPairs = u -> §{
    //     include .setbase.SetBase
    // }
}
