module set_sem_fundamentals {
    theory TypesSet {
        include .typebase.TypeBase
    }

    theory TypedTermsSet {
        include TypesSet
    }

    theory SoftTypedTermsSet {
        include .concepts.Propositions
        include .concepts.Terms
        include TypesSet
    }

    theory TypedLogicSet {
        include .concepts.Propositions
        include .concepts.Proofs
        include TypedTermsSet
    }

    theory SoftTypedLogicSet {
        include .concepts.Propositions
        include .concepts.Terms
        include .concepts.Proofs
        include SoftTypedTermsSet
    }

    theory TypedEqualitySet {
        include .concepts.Propositions
        include .concepts.Proofs
        include TypedLogicSet
    }

    theory TypedEqualityNDSet {
        include .concepts.Propositions
        include .concepts.Proofs
        include TypedEqualitySet
    }

    theory TypeEqualityNDSet {
        include .concepts.Propositions
        include .concepts.Proofs
        include TypesSet
    }

    theory DependentTypeEqualitySet {
        include .concepts.Propositions
        include .concepts.Proofs
        include TypeEqualityNDSet
        include TypedEqualityNDSet
    }
}
