module hol {
    theory InternalEquality {
        include .base_languages.InternalLogic
        include .equality.TypedEquality
        include .function_types.SimpleFunctions

        equalConstant: A -> tm (A → (A → boolean))
            = A -> simplambda(A, A → boolean) (x -> simplambda(A, boolean) (y -> tequal(A, x, y)))
    }

    theory IHOL {
        include InternalEquality
        include .booleans.InternalTruthValues
        include .sfol.ISFOL
    }

    theory IHOLND {
        include IHOL
        include .sfol.ISFOLND
        include .equality.PropositionalExtensionality

        eq_equiv: (F, G) -> ded tequal(boolean, F, G) -> ded equiv(F, G)
            = ???

        equiv_eq: (F, G) -> ded equiv(F, G) -> ded tequal(boolean, F, G)
            = (F, G) -> p -> propext(F, G) (q -> equivEl(F, G) p q) (q -> equivEr(F, G) p q)

        eq_thm: (F, G) -> ded tequal(boolean, F, G) -> ded F -> ded G
            = (F, G) -> p -> q -> equivEl(F, G) (eq_equiv(F, G) p) q

        thm_true: F -> ded F -> ded tequal(boolean, F, tt)
            = F -> p -> propext(F, tt) (q -> trueI) (q -> p)

        true_thm: F -> ded tequal(boolean, F, tt) -> ded F
            = F -> p -> eq_thm(tt, F) (tsym(boolean, F, tt) p) trueI
    }

    theory HOL {
        include IHOL
    }

    theory HOLND {
        include HOL
        include IHOLND
        include .sfol.SFOLND
        include .function_types.SimpleFunctionsEta
    }

    theory PowerHOLND {
        include HOLND

        // realize powertypes.PowerTypes
        power = a -> a → boolean
        pfilter = (A, P) -> simplambda(A, boolean) P
        in = (A, x, S) -> simpapply(A, boolean) S x
        compute = (A, P, x) -> ???
        expand = (A, S) -> eta(A, boolean, S)
    }


    // Diaconescu's theorem, following the Wikipedia article
    theory ClassicalViaChoice {
        include .HOLND
        include .sfol.TypedChoice

        Forbot = F -> x -> or(F, tequal(boolean, x, ff))
        exists_Forbot: F -> ded (texists boolean (Forbot F))
            = ???
        Fortop = F -> x -> or(F, tequal(boolean, x, tt))
        
        exists_Fortop: F -> ded (texists boolean (Fortop F))
            = ???
        tnd_choice: F -> ded (or(F, not F))
            = ???
    }

    theory IfThenElseViaChoice {
        include .HOLND
        include .sfol.TypedTotalChoice

        realize .ifte.IfThenElse

        ifte_prop: (A, b, x, y, u) -> prop
            = (A, b, x, y, u) -> or(and(b, tequal(A, u, x)), and(not b, tequal(A, u, y)))

        ifte = A -> b -> x -> y -> tany(A) (u -> ifte_prop(A, b, x, y, u))

        ifte_exists: (A, B, X, Y) -> ded (texists A (u -> ifte_prop(A, B, X, Y, u)))
            = ???

        ifte_unique: (A, B, X, Y, u) -> ded (ifte_prop(A, B, X, Y, u)) -> (v) -> ded (ifte_prop(A, B, X, Y, v)) -> ded tequal(A, u, v)
            = ???

        ifte_true: (A, B, X, Y) -> ded B -> ded tequal(A, ifte A B X Y, X)
            = ???

        ifte_false: (A, B, X, Y) -> ded (not B) -> ded tequal(A, ifte A B X Y, Y)
            = ???
    }
}