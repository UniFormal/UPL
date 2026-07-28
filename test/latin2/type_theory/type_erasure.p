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

    // TypeErasSimpleFunctions: .function_types.SoftTypedSimpleFunctions -> .function_types.SimpleFunctions = s -> .function_types.SimpleFunctions {
    //     include .concepts.TypedTerms = TypeErasTerms(s)
    //     include .equality.TypedEquality = TypeErasEquality(s)
    //     simplambda = (A,B,F) -> s.softlambda(A,B,F)
    //     simpapply = (A,B,f,x) -> s.softapply(A,B,f,x)
    //     simpbeta = (A,B,F,X) -> ded tequal(B, simpapply(A,B) (simplambda(A,B) F) X, F X)
    // }
}