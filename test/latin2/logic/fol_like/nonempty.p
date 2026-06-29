module nonempty {
    theory UniverseNonEmpty {
        include .base_languages.UntypedLogic

        // the universe is non-empty, i.e., we can pick fresh elements at any point in a proof
        univ_nonempty: C -> (term -> ded C) -> ded C
    }

    theory TypesNonEmpty {
        include .base_languages.TypedLogic

        // all types are non-empty, i.e., we can pick fresh elements at any point in a proof
        type_nonempty: A -> C -> (tm A -> ded C) -> ded C
    }
}