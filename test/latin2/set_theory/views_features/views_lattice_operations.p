module views_lattice_operations {
    // The views currently still need single theories as a domain and codomain, which
    // forces us to provide spurious named theories. This should be refactored when
    // multi-theory domains and codomains are possible.

    // Views for Union
    theory BigUnionUnorderedPairs {
        include .lattice_operations.BigUnion
        include .finite_sets.UnorderedPairs
    }

    // UnionAsBigUnion: BigUnionUnorderedPairs -> .lattice_operations.Union = u -> §{
    //     include .setbase.SetBase
    // }

    // Views for Intersection
    theory BigIntersectionUnorderedPairs {
        include .lattice_operations.BigIntersection
        include .finite_sets.UnorderedPairs
    }

    // IntersectionAsBigIntersection: BigIntersectionUnorderedPairs -> .lattice_operations.Intersection = i -> §{
    //     include .setbase.SetBase
    // }

    theory UnionFilter {
        include .operations.Filter
        include .lattice_operations.Union
    }

    // IntersectionFilter: UnionFilter -> .lattice_operations.Intersection = i -> §{
    //     include .setbase.SetBase
    // }

    // Views for BigUnion
    // BigUnionFromAxiom: .axioms.UnionAx -> .lattice_operations.BigUnion = b -> §{
    //     include .setbase.SetBase
    // }

    // Views for BigIntersection
    theory BigUnionFilterEmptyDefinition {
        include .lattice_operations.BigUnion
        include .setbase.EmptyDefinitions
        include .operations.Filter
    }

    // BigIntersectionFilter: BigUnionFilterEmptyDefinition -> .lattice_operations.BigIntersection = b -> §{
    //     include .setbase.SetBase
    //     include .setbase.EmptyDefinitions
    // }

    // Views for Difference
    // DifFilter: .operations.Filter -> .lattice_operations.Difference = d -> §{
    //     include .setbase.SetBase
    // }

    // Views for Complement
    // ComplementFilter: .operations.Filter -> .lattice_operations.Complement = c -> §{
    //     include .setbase.SetBase
    // }

    // ComplementDifference: .lattice_operations.Difference -> .lattice_operations.Complement = c -> §{
    //     include .setbase.SetBase
    // }
}
