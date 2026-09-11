module dhol {
    theory InternalEqualityD {
        include .base_languages.InternalLogic
        include .booleans.InternalTruthValues
        include .equality.TypedEquality
        include .function_types.DependentFunctions
    }

    theory DependentLogic {
        include InternalEqualityD
        include .dependent_pl.DependentImplication
        include .dependent_pl.DependentConjunction
        // rule rules.DependentImplicationInferenceRule
        // rule rules.DependentConjunctionInferenceRule
    }

    theory InternalBooleanExtensionality {
        include .base_languages.InternalLogic
        include .pl.Truth
        include .pl.Falsity
        include .function_types.DependentFunctionsExtensionality
    }

    // HOL with pi-types and predicate subtypes
    theory DIHOL {
        // for this and the next include: 
        // This includes the theory Propositions and hence includes a type of propositions
        // However this type should just be tm bool
        // But this applies also for other parts of LATIN2, including HOL itself
        // TODO: Check if this is ok
        include DependentLogic
        include .sfol.ISFOL
        include .equality.PropositionalExtensionality
        // rule rules.ProverBasedTypeEquality
        // rule rules.PiApplicationSimplificationRule
    }

    // HOL with pi-types and predicate subtypes
    theory DHOL {
        include DIHOL
        include .booleans.BooleanExtensionality
        include .function_types.DependentFunctionsExtensionality
        // exten2: (A, B) -> ded (tforall (depfun A B) (f -> tforall (depfun A B) (g -> tforall A (x -> dimpl (tequal (B x, depapply(A,B) f x, depapply(A,B) g x), p -> tequal (depfun A B, f, g))))))
    }

    theory DHOLND {
        include DHOL
        include .sfol.ISFOLND

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

    theory DPHOL {
        include DHOL
        include .predicate_subtypes.TypedPredicateSubtypes
        // rule rules.ProverBasedPredicateSubtypeEquality
    }

    theory DPIHOL {
        include DIHOL
        include .predicate_subtypes.TypedPredicateSubtypes
        // rule rules.ProverBasedPredicateSubtypeEquality
    }

    theory DPHOLND {
        include DHOLND
        include .predicate_subtypes.TypedPredicateSubtypes
    }
}
