module sfol {
    theory TypedUniversalQuantification {
        include .base_languages.TypedLogic
        tforall: A -> (tm A -> prop) -> prop
    }

    theory TypedUniversalQuantificationND {
        include TypedUniversalQuantification
        tforallI:--- forall P: tm A -> prop. (forall x: tm A. ⊦(P x)) => ⊦(tforall A P)
        tforallE:--- forall P: tm A -> prop. ⊦(tforall A P) => forall x: tm A. ⊦(P x)
    }

    theory TypedExistentialQuantification {
        include .base_languages.TypedLogic
        texists : A -> (tm A -> prop) -> prop
    }

    theory TypedExistentialQuantificationND {
        include TypedExistentialQuantification
        texistsI:--- forall P: tm A -> prop, x: tm A. ⊦(P x) => ⊦(texists A P)
        texistsE:---  forall P: tm A -> prop. ⊦(texists A P) => (forall x: tm A. ⊦(P x) => ⊦C) => ⊦C
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