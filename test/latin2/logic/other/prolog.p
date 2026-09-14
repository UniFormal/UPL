module prolog {
    theory Prolog {
        include .defaults.Skeptical
        include .sequent.SequentProofs
        include .sequent.Exchange
        include .sequent.Weakening
        include .sequent.SequentBigConjunction
        include .sequent.SequentImplication
        include .fol.UniversalQuantification
        include .sequent.Contraction
        include .sequent.SequentTruthRight
    }

    theory PrologExample {
        include Prolog
    }

    theory NegationAsFailure {
        include Prolog
        include .sequent.SequentTruthRightWeakened
        include .sequent.SequentNegationRight
        include .sequent.SequentNegationLeft
        include .sequent.InContext
        include .refutation.RefutationNegationLeft
        include .refutation.RefutationNegationRight
        include .refutation.RefutationImplication
        include .refutation.RefutationConjunctionRight
    }

    theory NAFExample {
        include NegationAsFailure
    }
}
