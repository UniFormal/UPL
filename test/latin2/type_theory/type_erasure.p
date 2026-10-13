module type_erasure {
    TypeErasTerms: .concepts.SoftTypedTerms -> .concepts.TypedTerms = s -> .concepts.TypedTerms {
        type tp = s.tp
        type tm(a: tp) = s.term
    } 

    // doesn't work yet

    // TypeErasEquality: .equality.SoftTypedEquality -> .equality.TypedEquality = s -> .equality.TypedEquality {
    //     include .concepts.TypedTerms = TypeErasTerms(s)
    //     include .concepts.Logic
    //     tequal = (A,x,y) ->  s.requal(A,x,y)
    // } 

    // View currently not total
    // TypeErasSimpleFunctions: .function_types.SoftTypedSimpleFunctions -> .function_types.SimpleFunctions = s -> .function_types.SimpleFunctions {
    //     include .concepts.TypedTerms = TypeErasTerms(s)
    //     include .equality.TypedEquality = TypeErasEquality(s)
    //     simpfun = (A,B) -> s.simpfun(A,B)
    //     simplambda = (A,B,F) -> s.softlambda(F)
    //     simpapply = (A,B,F,X) -> s.softapply(F,X)
    // }

    // View currently not total
    // TypeErasDependentFunctions: .function_types.SoftTypedDependentFunctions -> .function_types.DependentFunctions = s -> .function_types.DependentFunctions {
    //     include .concepts.TypedTerms = TypeErasTerms(s)
    //     include .equality.TypedEquality = TypeErasEquality(s)
    //     depfun = (A,B) -> s.softfun(A,B)
    //     deplambda = (A,B,F) -> s.softlambda(F)
    //     depapply = (A,B,F,X) -> s.softapply(F,X)
    // }
}