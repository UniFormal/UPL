module fol {
    theory UniversalQuantification {
        include .base_languages.UntypedLogic

        uforall: (term -> prop) -> prop     # bindfix ∀
    }

    theory UniversalQuantificationNDI {
        include UniversalQuantification

        uforallI:--- (forall X. ⊦P(X)) => ⊦ ∀x. P(x)
    }

    theory UniversalQuantificationNDE {
        include UniversalQuantification

        uforallE:--- ⊦ (∀x. P(x)) => (forall X. ⊦P(X))
        // uforallE:--- ⊦ ∀x. P(x) => ⊦ P(Y) // does this also work?
    }

    theory UniversalQuantificationND {
        include UniversalQuantificationNDI
        include UniversalQuantificationNDE
    }

    theory ExistentialQuantification {
        include .base_languages.UntypedLogic

        uexists : (term -> prop) -> prop    # bindfix ∃
    }

    theory ExistentialQuantificationNDI {
        include ExistentialQuantification

        uexistsI:--- ⊦P(X) => ⊦ ∃x. P(x)
    }

    theory ExistentialQuantificationNDE {
        include ExistentialQuantification

        uexistsE:--- ⊦ (∃x. P(x)) => (forall X. ⊦P(X) => ⊦C) => ⊦C 
    }

    theory ExistentialQuantificationND {
        include ExistentialQuantificationNDI
        include ExistentialQuantificationNDE
    }

    theory IFOL {
        include .pl.IPL
        include UniversalQuantificationND
        include ExistentialQuantificationND
    }

    theory IFOLND {
        include IFOL
        include IPLND
        include UniversalQuantificationND
        include ExistentialQuantificationND
    }

    theory IFOLEQ {
        include IFOL
        include UntypedEquality
    }

    theory IFOLEQND {
        include IFOLEQ
        include IFOLND
        include UntypedEqualityND
    }

    theory FOL {
        include .pl.PL
        include IFOL
    }

    theory FOLND {
        include FOL
        include PLND
        include IFOLND
    }

    theory FOLEQ {
        include FOL
        include UntypedEquality
    }

    theory FOLEQND {
        include FOLEQ
        include FOLND
        include UntypedEqualityND
    }
}