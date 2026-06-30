module type_erasure {
    TypeErasTerms: .concepts.SoftTypedTerms -> .concepts.TypedTerms = s -> .concepts.TypedTerms {
        type tp = s.tp
        type tm(a: tp) = s.term
    } 

    TypeErasEquality: .equality.SoftTypedEquality -> .equality.TypedEquality = s -> .equality.TypedEquality {
        type tp = s.tp
        type tm(a: tp) = s.term
        type prop = s.prop
        type ded(p: prop) = ded p
        // doesn't work, why?
        // type ded(p: prop) = s.ded(p)
        lemma = s.lemma
        tequal = (A,x,y) ->  s.requal(A,x,y)
    } 
}