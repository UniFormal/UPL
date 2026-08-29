module sfol {
    theory TypedUniversalQuantification {
        include .base_languages.TypedLogic
        tforall: A -> (tm A -> prop) -> prop
    }

    theory TypedUniversalQuantificationND {
        include TypedUniversalQuantification
        tforallI: (A, P) -> (x -> ded (P x)) -> ded (tforall A P)
        tforallE: (A, P) -> ded (tforall A P) -> x -> ded (P x)
    }

    theory TypedExistentialQuantification {
        include .base_languages.TypedLogic
        texists : A -> (tm A -> prop) -> prop
    }

    theory TypedExistentialQuantificationND {
        include TypedExistentialQuantification
        texistsI: (A,P) -> x -> ded (P x) -> ded (texists A P)
        texistsE: (A,P,C) -> ded (texists A P) -> (x -> ded (P x) -> ded C) -> ded C
    }

    theory ISFOL {
        include .concepts.TypedTerms
        include .pl.IPL
        include TypedUniversalQuantification
        include TypedExistentialQuantification
    }

    theory ISFOLND {
        include ISFOL
        include .pl.IPLND
        include TypedUniversalQuantificationND
        include TypedExistentialQuantificationND
    }

    theory SFOL {
        include .pl.PL
        include ISFOL
    }

    theory SFOLND {
        include SFOL
        include .pl.PLND
        include ISFOLND
    }

    theory SFOLEQ {
        include SFOL
        include .equality.TypedEquality
        notequal : (A, tm A, tm A) -> prop
        notequal = (A,x,y) -> ¬tequal(A, x, y)
    }

    theory ISFOLEQND {
        include SFOLEQ 
        include ISFOLND 
        include .equality.TypedEqualityND
    }

    theory SFOLEQND {
        include ISFOLEQND
        include SFOLND
    }

    theory TypedUniqueExistentialQuantification {
        include TypedExistentialQuantification
        include .equality.TypedEquality
        texistsUnique: (A) -> (tm A -> prop) -> prop
    }

    theory TypedUniqueExistentialQuantificationND {
        include TypedUniqueExistentialQuantification
        texistsUniqueI: ???
        texistsUniqueE: ???
    }

    theory TypedDescription {
        include .base_languages.TypedLogic
        include TypedUniqueExistentialQuantification
        tthe: ???
        tthe_ax: ???
    }

    theory TypedChoice {
        include .base_languages.TypedLogic
        include TypedExistentialQuantification
        include .equality.TypedEquality
        tsome: ???
        tsome_ax: ???
        tsome_eq: ???
    }

    // The variant of choice that always returns a value and whose defining axiom is relativized by existence; only sound if types are guaranteed to be non-empty.
    theory TypedTotalChoice {
        include .base_languages.TypedLogic
        include TypedExistentialQuantification
        include .equality.TypedEquality
        tany: ???
        tany_ax: ???
        tany_eq: ???

        realize TypedChoice
        tsome = ???
        tsome_ax = ???
        tsome_eq = ???
    }

    theory BigSFOL {
        include SFOLEQND
        include TypedDescription
        include .ifte.IfThenElse
    }
}