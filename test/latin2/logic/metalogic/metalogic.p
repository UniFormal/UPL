module metalogic {
    // AS: This could be done with ͫ (combined m). But I am not sure, if this is wanted
    theory MetaLevelUniversalQuantification {
        include .concepts.Logic
        // needs inhabation I think
        forall: ???
    }

    theory MetaLevelExistentialQuantification {
        include .concepts.Logic
        exists: ???
    }

    theory MetaLevelEquality {
        include .concepts.Logic
        equal: ???
        refl: (A,x) -> ded equal(A,x,x)
        transport: ???
        cong: (A,B,x,y) -> ded equal(A,x,y) -> (F) -> ded equal(B, F x, F y) = ???
    }

    theory MetaLogic {
        include MetaLevelEquality
        realize .pl.IPL
        realize MetaLevelUniversalQuantification
        realize MetaLevelExistentialQuantification
        truth = ???
        falsity = ???
        not = ???
        forall = ???
        and = ???
        impl = ???
        or = ???
        equiv = ???
        exists = ???
    }
}