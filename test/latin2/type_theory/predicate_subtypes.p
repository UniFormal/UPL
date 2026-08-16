module predicate_subtypes {
    theory TypedPredicateSubtypes {
        include .base_languages.TypedLogic
        include .equality.TypedEquality

        predsub: A -> (tm A -> prop) -> tp
        predsubI: (A,P,x) -> ded(P x) -> tm(predsub A P)
        predsubEl: (A,P,x) -> tm A
        predsubEr: (A,P,x) -> ded(P (predsubEl(A,P,x)))

        predsubElBeta: (A,P,a,p) -> ded(tequal(A, predsubEl(A,P,(predsubI(A,P,a) p)), a))
        // cannot express predsubErBeta here, what should equality on ded be? 
    }

    theory SoftTypedPredicateSubtypes {
        include .base_languages.SoftTypedLogic

        predsub: A -> (term -> prop) -> tp
        predsubI: (A,P,x) -> ded(x ∶ A) -> ded(P x) -> ded(x ∶ (predsub A P))
        predsubEl: (A,P,x) -> ded(x ∶ (predsub A P)) -> ded(x ∶ A)  
        predsubEr: (A,P,x) -> ded(x ∶ (predsub A P)) -> ded(P x)
    }
}