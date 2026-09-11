module hol_andrews {
    // Andrews-style HOL developed from only equality
    theory HOLAndrews {
        include .hol.InternalEquality
        include .equality.PropositionalExtensionality

        realize .hol.IHOLND
        
        tt = tequal(boolean → boolean, simplambda(boolean, boolean) (x -> x), simplambda(boolean, boolean) (x -> x))
        trueI = ???

        ff = tequal(boolean → boolean, simplambda(boolean, boolean) (x -> x), simplambda(boolean, boolean) (x -> tt))
        falseE = ???

        not = F -> tequal(boolean, F, ff)
        notI = ???
        notE = ???

        tforall = A -> F -> tequal(A → boolean, simplambda(A, boolean) (x -> F x), simplambda(A, boolean) (x -> tt))
        tforallI = ???
        tforallE = ???

        and = (F, G) -> tforall (boolean → (boolean → boolean)) (h -> tequal(boolean, simpapply(boolean, boolean) (simpapply(boolean, boolean → boolean) h F) G, simpapply(boolean, boolean) (simpapply(boolean, boolean → boolean) h tt) tt))
        andI = ???
        andEl = ???
        andEr = ???

        impl = (F, G) -> tequal(boolean, and(F, G), F)
        implI = ???
        implE = ???

        or = (F, G) -> tforall boolean (H -> impl(impl(F, H), impl(impl(G, H), H)))
        orIl = ???
        orIr = ???
        orE = ???

        equiv = (F, G) -> and(impl(F, G), impl(G, F))
        equivI = ???
        equivEl = ???
        equivEr = ???

        texists = A -> F -> tforall boolean (H -> impl(tforall A (x -> impl(F x, H)), H))
        texistsI = ???
        texistsE = ???
    }
}
