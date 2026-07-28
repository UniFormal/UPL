module logic_to_type_theory {
    // Curry-Howard correspondence as morphisms XCH that translate logical theories X to type-theoretical theories
    
    PropositionsAsTypes: .concepts.Types -> .concepts.Propositions = t -> .concepts.Propositions {
        type prop = t.tp
    }

    // doesn't work yet

    // ProofsAsTerms: .concepts.TypedTerms -> .concepts.Proofs = t -> .concepts.Proofs {
    //     include .concepts.Propositions = PropositionsAsTypes(t)
    //     type ded(p: prop) = t{tm p}
    // }

    // LogicCH: .concepts.TypedTerms -> .concepts.Logic = t -> .concepts.Logic {
    //     include .concepts.Proofs = ProofsAsTerms(t)
    // }

    // falsity as empty type
    // FalsityCH: .empty_type.EmptyType -> .pl.Falsity = e -> .pl.Falsity {
    //     include .concepts.Propositions = PropositionsAsTypes(e)
    //     falsity = e.void
    // }

    // FaslityNDCH: .empty_type.EmptyType -> .pl.FalsityND = e -> .pl.FalsityND {
    //     include .concepts.Logic = LogicCH(e)
    //     include .pl.Falsity = FalsityCH(e)
    //     falseE = e.throw
    // }

    // truth as unity type
    // TruthCH: .unit_type.UnitType -> .pl.Truth = u -> .pl.Truth {
    //     include .concepts.Propositions = PropositionsAsTypes(u)
    //     truth = u.unitType
    // }

    // TruthNDCH: .unit_type.UnitType -> .pl.TruthND = u -> .pl.TruthND {
    //     include .concepts.Logic = LogicCH(u)
    //     include .pl.Truth = TruthCH(u)
    //     trueI = u.unit
    // }
}