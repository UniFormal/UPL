module function_types {
    theory SimpleFunctionTypes {
        include .concepts.Types
        simpfun: (tp, tp) -> tp # infix →
    }

    theory DependentFunctionTypes {
        include .concepts.TypedTerms
        depfun: A -> (tm A -> tp) -> tp

        realize SimpleFunctionTypes
        simpfun = (A,B) -> depfun A (x -> B)
    }

    theory SoftDependentFunctionTypes {
        include .concepts.SoftTypedTerms
        softfun: tp -> (term -> tp) -> tp
    }

    theory SimpleFunctions {
        include SimpleFunctionTypes
        include .equality.TypedEqualityND

        simplambda: (A,B) -> (tm A -> tm B) -> tm A→B
        simpapply: (A,B) -> tm A→B -> tm A -> tm B
        simpbeta : (A,B,F,X) -> ded (tequal(B, simpapply(A,B) (simplambda(A,B) F) X, F X))
    }
}