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
        uexists: (term -> prop) -> prop    # bindfix ∃
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
        rforall: (tp, (term -> prop)) -> prop = (A, P) -> ∀x. of(x, A) ⇒ P(x)
    }

    theory RelativizedUniversalQuantificationND {
        include RelativizedUniversalQuantification
        include FOLEQND
        rforallI:--- (forall X. ⊦of(X,A) => ⊦F(X)) => ⊦rforall(A, F)
        rforallE:--- ⊦rforall(A, F) => forall X. ⊦of(X,A) => ⊦F(X)
    }

    theory RelativizedExistentialQuantification {
        include .concepts.SoftTypedTerms
        include .FOLEQ
        rexists: (tp, (term -> prop)) -> prop = (A, P) -> ∃X. of(X, A) ∧ P(X)
    }

    theory RelativizedExistentialQuantificationND {
        include RelativizedExistentialQuantification
        include FOLEQND
        rexistsI:--- forall X. ⊦of(X,A) => ⊦F(X) => ⊦rexists(A, F)
        rexistsE:--- ⊦rexists(A, F) => (forall X. ⊦of(X,A) => ⊦F(X) => ⊦C) => ⊦C
    }

    theory UniqueExistentialQuantification {
        include ExistentialQuantification
        include .equality.UntypedEquality
        uexistsUnique: (term -> prop) -> prop
    }

    theory UniqueExistentialQuantificationND {
        include UniqueExistentialQuantification
        uexistsUniqueI:--- ⊦P(X) => (forall Y. ⊦P(Y) => ⊦(X ≐ Y)) => ⊦uexistsUnique(P)
        uexistsUniqueE:--- ⊦uexistsUnique(P) => (forall X. ⊦P(X) => (forall Y. ⊦P(Y) => ⊦(X ≐ Y)) => ⊦C) => ⊦C
    }

    theory Description {
        include .concepts.Logic
        include UniqueExistentialQuantificationND
        the: ???
        the_ax: ???
    }

    theory Choice {
        include .concepts.Logic
        include ExistentialQuantificationND
        include .equality.UntypedEquality
        some: ???
        some_ax: ???
        some_eq: ???
    }

    theory TotalChoice {
        include .concepts.Logic
        include ExistentialQuantificationND
        include .equality.UntypedEquality
        anyTC: (term -> prop) -> term
        any_ax:--- ⊦(∃x. P x) => ⊦(P (anyTC p))
        any_eq:--- (⊦(P x) => ⊦(Q x)) => (⊦(Q x) => ⊦(P x)) => ⊦(anyTC P ≐ anyTC Q)

        realize Choice
        some = ???
        some_ax = ???
        some_eq = ???
    }

    theory FOLEQDesc {
        include FOLEQ
        include Description
    }

    theory FOLEQDescND {
        include FOLEQDesc
        include FOLEQND
    }

    theory DependentFOLEQDesc {
        include FOLEQDesc
        include .dependent_pl.DependentConjunction
        include .dependent_pl.DependentDisjunction
        include .dependent_pl.DependentImplication
    }

    theory DependentFOLEQDescND {
        include DependentFOLEQDesc
        include FOLEQDescND
        include .dependent_pl.DependentConjunctionND
        include .dependent_pl.DependentDisjunctionND
        include .dependent_pl.DependentImplicationND
    }
}