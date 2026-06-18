module dependent_pl {
    theory DependentConjunction {
        include .concepts.Logic
        dand: F -> (dedT(F) -> prop) -> prop

        con: .pl.Conjunction {
            and = (F, G) -> dand(F, (x) -> G)
        }
    }

    theory DependentConjunctionND {
        include DependentConjunction
    }

    theory DependentDisjunction {

    }

    theory DependentDisjunctionND {
        include DependentDisjunction
    }

    theory DependentImplication {

    }

    theory DependentImplicationND {
        include DependentImplication
    }
}