module pl_sfol {
    theory PLModel {
        include .sfol.SFOLEQND
        include .concepts.Booleans
    }

    // View currently not total
    
    // PLSemantics: PLModel -> .pl.PLND = pl -> .pl.PLND {
    //     type prop = tm bool
    //     ded(p: prop) = ded(pl.uequal(p, tt))

    //     truth = tt
    //     falsity = ff

    //     and = ???
    //     or = ???
    //     impl = ???
    //     not = ???
    //     equiv = ???

    //     trueI = refl
    //     falseE = ???
    //     andI = ???
    // }
}