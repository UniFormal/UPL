module set_sem_sfol {
    theory TypedUniversalQuantificationSet {
        include .concepts.Propositions
        include .concepts.Proofs
        include .set_sem_fundamentals.TypedLogicSet
    }

    theory TypedUniversalQuantificationNDSet {
        include .concepts.Propositions
        include .concepts.Proofs
        include TypedUniversalQuantificationSet
    }

    theory TypedExistentialQuantificationSet {
        include .concepts.Propositions
        include .concepts.Proofs
        include .set_sem_fundamentals.TypedLogicSet
    }

    theory TypedExistentialQuantificationNDSet {
        include .concepts.Propositions
        include .concepts.Proofs
        include TypedExistentialQuantificationSet
    }
}
