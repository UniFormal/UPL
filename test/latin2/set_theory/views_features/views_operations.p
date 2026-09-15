module views_operations {
    // care, UnionFilter got defined in views_lattice_operations. So if this file gets renamed,
    // the dependency might fail!

    // The views currently still need single theories as a domain and codomain, which
    // forces us to provide spurious named theories. This should be refactored when
    // multi-theory domains and codomains are possible.

    // This would belong in another file, but I cannot move it now
    theory RegularityUopair {
        include .axioms.RegularityAx
        include .finite_sets.UnorderedPairs
    }

    // AcyclicUopair: RegularityUopair -> .axioms.Acyclic = a -> §{
    //     include .setbase.SetBase
    // }

    // Views for Filter
    // FilterFromAxiom: .axioms.ComprehensionAx -> .operations.Filter = f -> §{
    //     include .setbase.SetBase
    // }

    // Views for Replace
    // ReplaceFromAxiom: .axioms.ReplacementAx -> .operations.Replace = r -> §{
    //     include .setbase.SetBase
    //     include .setbase.RelationDefinitions
    // }

    // Views for Image
    // ImageReplace: .operations.Replace -> .operations.Image = i -> §{
    //     include .setbase.SetBase
    // }

    // Views for SymmetricDifference
    theory UnionDifference {
        include .lattice_operations.Difference
        include .lattice_operations.Union
    }

    // SymUnion: UnionDifference -> .operations.SymmetricDifference = s -> §{
    //     include .setbase.SetBase
    // }

    theory UnionIntersectionDifference {
        include UnionDifference
        include .lattice_operations.Intersection
    }

    // SymDifference: UnionIntersectionDifference -> .operations.SymmetricDifference = s -> §{
    //     include .setbase.SetBase
    // }

    // SymFilter: .views_lattice_operations.UnionFilter -> .operations.SymmetricDifference = s -> §{
    //     include .setbase.SetBase
    // }

    // Views for Adjoin
    theory UnionSingleton {
        include .lattice_operations.Union
        include .finite_sets.Singletons
    }

    // AdjoinUnion: UnionSingleton -> .operations.Adjoin = a -> §{
    //     include .setbase.SetBase
    // }

    // Views for Remove
    // RemoveFilter: .operations.Filter -> .operations.Remove = r -> §{
    //     include .setbase.SetBase
    // }

    theory SingletonDifference {
        include .lattice_operations.Difference
        include .finite_sets.Singletons
    }

    // RemoveDifference: SingletonDifference -> .operations.Remove = r -> §{
    //     include .setbase.SetBase
    // }
}
