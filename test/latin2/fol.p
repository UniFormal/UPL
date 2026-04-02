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
        include .pl.IPLND
        include UniversalQuantificationND
        include ExistentialQuantificationND
    }

    theory IFOLEQ {
        include IFOL
        include .equality.UntypedEquality
    }

    theory IFOLEQND {
        include IFOLEQ
        include IFOLND
        include .equality.UntypedEqualityND
    }

    theory FOL {
        include .pl.PL
        include IFOL
    }

    theory FOLND {
        include FOL
        include .pl.PLND
        include IFOLND
    }

    theory FOLEQ {
        include FOL
        include .equality.UntypedEquality
    }

    theory FOLEQND {
        include FOLEQ
        include FOLND
        include .equality.UntypedEqualityND
    }

    theory RelativizedUniversalQuantification {
        include .concepts.SoftTypedTerms
        include FOLEQ

        rforall : tp -> (term -> prop) -> prop = (A, P) -> ∀X. of(X, A) ⇒ P(X)
    }

    theory RelativizedUniversalQuantificationND {
        include RelativizedUniversalQuantification
        include FOLEQND

        rforallI:--- (forall X. ⊦of(X,A) => ⊦F(X)) => rforall(A)(F)
        rforallE:--- rforall(A)(F) => forall X. ⊦of(X,A) => ⊦F(X)
    }
}