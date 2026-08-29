module booleans {
    theory TrueFalse {
        include .concepts.Booleans
        tt: tm boolean
        ff: tm boolean
    }

    theory InternalTruthValues {
        include .concepts.InternalPropositions
        include TrueFalse
        realize .pl.Truth
        truth = tt
        realize .pl.Falsity
        falsity = ff
    }

    theory BooleanExtensionality {
        include .sfol.SFOLEQND
        include InternalTruthValues

        bool_nontrivial: ded tequal(boolean, not ff, tt)
        boolext: (F) -> ded(F tt) -> ded(F ff) -> (x) -> ded(F x)
        bool_tnd: ??? = ???
    }
}