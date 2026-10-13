module defaults {
    // Source : P.A. Bonatti, N. Olivetti : Sequent Calculi for Propositional Nonmonotonic Logics,
    // AMC Transactions on Computational Logic, Vol. 3, No.2, April 2002

    theory CredProof {
        include .concepts.Propositions
        include .sequent.Contexts
    }

    theory Default {
        include .concepts.Propositions
    }

    theory ResidueCalc {
        include CredProof
        include .sequent.SequentProofs
        include .refutation.Antisequent 
    }

    theory DefaultProvable {
        include .concepts.Propositions
    }

    theory Credulous {
        include ResidueCalc
        include .pl.Negation
        include DefaultProvable
        include Default
    }

    // Example 4.12
    theory CredulousExample {
        include Credulous
        include .refutation.PLRefutation 
        include .sequent.InContext
    }

    theory Skeptical {
        include ResidueCalc
        include .pl.Negation
        include DefaultProvable
        include Default
    }

    // Example 4.17
    theory SkepticalExample {
        include Skeptical
        include .sequent.SequentNegation
        include .sequent.SequentImplication
        include .sequent.SequentDisjunctionRight
        include .sequent.InContext
        include .sequent.Exchange
        include .sequent.Weakening
        include .refutation.PLRefutation 
        include .sequent.SequentTruthRightWeakened
    }
}
