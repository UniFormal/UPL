module finite_sets {
    theory EmptySet {
        include .setbase.SetBase
        include .setbase.EmptyDefinitions
    }

    theory Singletons {
        include .setbase.SetBase
    }

    theory UnorderedPairs {
        include .setbase.SetBase
    }
}
