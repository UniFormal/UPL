module set_sem_power_types {
    theory PowerTypesSet {
        include .concepts.Propositions
        include .concepts.Proofs
        include .pl.Equivalence
        include .pl.EquivalenceNDI
        include .pl.EquivalenceNDE
        include .set_sem_fundamentals.TypedEqualityNDSet
        include .powersets.Powersets
        include .operations.Filter
    }

    // powertypes/Map is defined already. Therefore I skipped it

    theory ExtensionalitySet {
        include .concepts.Propositions
        include .concepts.Proofs
        include .pl.Equivalence
        include .pl.EquivalenceNDI
        include .pl.EquivalenceNDE
        include PowerTypesSet
        include .set_sem_sfol.TypedUniversalQuantificationNDSet
    }
}
