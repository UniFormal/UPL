module fol {
    theory UniversalQuantification {
        include .base_languages.UntypedLogic
        uforall: (term -> prop) -> prop # bindfix ∀ᵘ
    }

    theory UniversalQuantificationNDI {
        include UniversalQuantification
        uforallI: P -> (x -> ded (P x)) -> ded (∀ᵘx. P x) 
    }

    theory UniversalQuantificationNDE {
        include UniversalQuantification
        uforallE: (P, X) -> ded (∀ᵘx. P x) -> ded (P X)
    }

    theory UniversalQuantificationND {
        include UniversalQuantificationNDI
        include UniversalQuantificationNDE
    }

    theory ExistentialQuantification {
        include .base_languages.UntypedLogic
        uexists: (term -> prop) -> prop # bindfix ∃ᵘ
    }

    theory ExistentialQuantificationNDI {
        include ExistentialQuantification
        uexistsI: (P,X) -> ded (P X) -> ded (∃ᵘx. P x)
    }

    theory ExistentialQuantificationNDE {
        include ExistentialQuantification 
        uexistsE: (P,C) -> ded (∃ᵘx. P x) -> (x -> ded (P x) -> ded C) -> ded C 
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
        rforall: (tp, (term -> prop)) -> prop 
        rforall = (A, P) -> ∀ᵘx. x∶A ⇒ P x
    }

    theory RelativizedUniversalQuantificationND {
        include RelativizedUniversalQuantification
        include FOLEQND
        rforallI: (A,F) -> (x -> ded x∶A -> ded (F x)) -> ded rforall(A, F)
        rforallE: (A,F) -> ded rforall(A, F) -> x -> ded x∶A -> ded (F x)
    }

    theory RelativizedExistentialQuantification {
        include .concepts.SoftTypedTerms
        include .FOLEQ
        rexists: (tp, (term -> prop)) -> prop 
        rexsits = (A, P) -> ∃ᵘx. x∶A ∧ P x
    }

    theory RelativizedExistentialQuantificationND {
        include RelativizedExistentialQuantification
        include FOLEQND
        rexistsI: (A,F) -> x -> ded x∶A -> ded (F x) -> ded rexists(A, F)
        rexistsE: (A,F,C) -> ded rexists(A, F) -> (x -> ded x∶A -> ded (F x) -> ded C) -> ded C
    }

    theory UniqueExistentialQuantification {
        include ExistentialQuantification
        include .equality.UntypedEquality
        uexistsUnique: (term -> prop) -> prop
    }

    theory UniqueExistentialQuantificationND {
        include UniqueExistentialQuantification
        uexistsUniqueI: P -> x -> ded (P x) -> (y -> ded (P y) -> ded x≐y) -> ded (uexistsUnique P)
        uexistsUniqueE: (P,C) -> ded (uexistsUnique P) -> (x -> ded (P x) -> (y -> ded (P y) -> ded x≐y) -> ded C) -> ded C
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
        any_ax: (P,p) -> ded (∃ᵘx. P x) -> ded (P (anyTC p))
        any_eq: (P, Q) -> (x -> ded (P x) -> ded (Q x)) -> (x -> ded (Q x) -> ded (P x)) -> ded (anyTC P ≐ anyTC Q)

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

    TotalChoiceYieldsNonempty: TotalChoice -> .nonempty.UniverseNonEmpty = t -> .nonempty.UniverseNonEmpty {
        univ_nonempty = (C, P) -> P (t.anyTC (x -> x≐x))
    }

    ChoiceYieldsDescription: (Choice, UniqueExistentialQuantificationND) -> Description = (c, u) -> Description {
        the = ???
        the_ax = ???
    }
}