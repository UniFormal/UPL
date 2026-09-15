module set_sem_predicate_subtypes {
    theory TypedPredicateSubtypesSet {
        include .concepts.Propositions
        include .concepts.Proofs
        include .set_sem_fundamentals.TypedLogicSet
        include .set_sem_fundamentals.TypedEqualitySet
        include .operations.Filter
    }

    theory SoftTypedPredicateSubtypesSet {
        include .concepts.Propositions
        include .concepts.Terms
        include .concepts.Proofs
        include .set_sem_fundamentals.SoftTypedLogicSet
        include .operations.Filter
    }
}
