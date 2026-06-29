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
}