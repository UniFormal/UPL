module function_types {
    theory SimpleFunctionTypes {
        include .concepts.Types
        simpfun: (tp, tp) -> tp # infix →
    }

    theory DependentFunctionTypes {
        include .concepts.TypedTerms
        depfun: A -> (tm A -> tp) -> tp

        // maybe change realize to a total structure
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

        // missing
    }

    theory DependentFunctions {
        include DependentFunctionTypes
        include .equality.TypedEqualityND

        deplambda: (A,B) -> ((x:tm A) -> tm (B x)) -> tm (depfun A B)
        depapply: (A,B) -> tm (depfun A B) -> (x:tm A) -> tm (B x)
        depbeta : (A,B,F,X) -> ded tequal(B X, depapply(A,B) (deplambda(A,B) F) X, F X)

        // missing
    }

    theory SoftTypedFunctions {
        include .concepts.Terms
        include .equality.UntypedEquality

        lambda: (term -> term) -> term // # bindfix λ // doesn't work
        apply: (term, term) -> term # infix @
        beta: (F,X) -> ded ((lambda F) @ X ≐ F X)
    }

    theory SoftTypedSimpleFunctions {
        include .concepts.SoftTypedTerms
        include SoftTypedFunctions
        include SimpleFunctionTypes

        fun_typing: (A,B,F) -> (x -> ded x∶A -> ded ((F x)∶B)) -> ded ((lambda F)∶(A → B))
    }

    theory SoftTypedDependentFunctions {
        include .concepts.SoftTypedTerms
        include SoftTypedFunctions
        include SoftDependentFunctionTypes

        fun_typing: (A,B,F) -> (x -> ded x∶A -> ded ((F x)∶(B x))) -> ded ((lambda F)∶(softfun A B))
    }

    theory SimpleFunctionsEta {
        include SimpleFunctions
        eta: (A,B,F) -> ded tequal(A → B, F, simplambda(A,B) (x -> simpapply(A,B) F x))
    }

    theory DependentFunctionsEta {
        include DependentFunctions
        eta: (A,B,F) -> ded tequal(depfun A B, F, deplambda(A,B) (x -> depapply(A,B) F x))
    }

    theory SoftTypedFunctionsEta {
        include SoftTypedFunctions
        eta: F -> ded (F ≐ (lambda (x -> apply(F, x))))
    }

    theory SimpleFunctionsExtensionality {
        include SimpleFunctions
        exten: (A,B,F,G) -> (x -> ded tequal(B, simpapply(A,B) F x, simpapply(A,B) G x)) -> ded tequal(A → B, F, G)
    }

    theory DependentFunctionsExtensionality {
        include DependentFunctions
        exten: (A,B,F,G) -> (x -> ded tequal(B x, depapply(A,B) F x, depapply(A,B) G x)) -> ded tequal(depfun A B, F, G)
    }

    theory SoftTypedFunctionsExtensionality {
        include SoftTypedFunctions
        exten: (F,G) -> (x -> ded (apply(F, x) ≐ apply(G, x))) -> ded (F ≐ G)
    }

    // doesn't work yet

    // FE: SimpleFunctionsEta -> SimpleFunctionsExtensionality = e -> SimpleFunctionsExtensionality {
    //     include SimpleFunctions
    //     exten = ???
    // }

    // EF: SimpleFunctionsExtensionality -> SimpleFunctionsEta = e -> SimpleFunctionsEta {
    //     include SimpleFunctions
    //     eta = ???
    // }
}