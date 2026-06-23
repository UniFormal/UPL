module dependent_pl {
    // Conjunction where the second conjunct's well-formedness may depend on the truth of the first conjunct
    // Curry-Howard analogue of Sigma types
    theory DependentConjunction {
        include .concepts.Logic
        dand: (F, dedT F -> prop) -> prop

        con: .pl.Conjunction {
            and = (F, G) -> dand(F, x -> G)
        }
    }

    theory DependentConjunctionND {
        include DependentConjunction
        dandI: ???
        dandEl: ???
        dandEr: ???

        conND: .pl.ConjunctionND {
            andI = ???
            andEl = ???
            andEr = ???
        }
    }

    // Disjunction where the second disjunct's well-formedness may depend on the falsity of the first disjunct
    // Curry-Howard analogue of an unusual union type where the second argument is only considered if the first one is empty
    theory DependentDisjunction {
        include .concepts.Logic
        dor: (F, (dedT F -> inconsistent) -> prop) -> prop

        dis: .pl.Disjunction {
            or = (F, G) -> dor(F, x -> G)
        }
    }

    theory DependentDisjunctionND {
        include DependentDisjunction
        dorIl: ???
        dorIr: ???
        dorE: ???

        disND: .pl.DisjunctionND {
            orIl = ???
            orIr = ???
            orE = ???
        }
    }

    // Implication where the implicate's well-formedness may depend on the truth of the implicant
    // Curry-Howard analogue of Pi types
    theory DependentImplication {
        dimpl: (F, dedT F -> prop) -> prop

        imp: .pl.Implication {
            impl = (F, G) -> dimpl(F, x -> G)
        }
    }

    theory DependentImplicationND {
        include DependentImplication
        dimplI: ???
        dimplE: ???

        impND: .pl.ImplicationND {
            implI = ???
            implE = ???
        }
    }
}