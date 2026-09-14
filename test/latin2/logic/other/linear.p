module other_linear {
    theory LinearLogic {
        include .sequent.Cut
        include .sequent.Exchange
        include .sequent.SequentProofs
        include .sequent.SequentBase
        include .sequent.SequentNegation
        include .sequent.ContextMap
    }

    theory LinearDuals {
        include LinearLogic
    }
}
