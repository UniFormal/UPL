module empty_type {
    theory EmptyType {
        include .equality.TypedEqualityND
        void: tp

        // computationally, the empty type can be seen as the type of exceptions
        // in that case, its universal arrow can be seen as throwing an exception to obtain a term of any type
        throw: tm void -> A -> tm A
        // the universal property states that any computation after throwing is ignored
        voidUnique: (A,B,F:tm A -> tm B,e) -> ded tequal(B, F (throw e), throw e)
    }
}