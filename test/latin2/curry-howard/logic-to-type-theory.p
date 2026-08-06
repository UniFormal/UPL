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

    // conjunctions as product types
    // ConjunctionCH: .product_types.SimpleProductTypes -> .pl.Conjunction = p -> .pl.Conjunction {
    //     include .concepts.Propositions = PropositionsAsTypes(p)
    //     and = p.simpprod
    // }

    // ConjunctionNDCH: .product_types.SimpleProducts -> .pl.ConjunctionND = p -> .pl.ConjunctionND {
    //     include .pl.Conjunction = ConjunctionCH(p)
    //     include .concepts.Proofs = ProofsAsTerms(t)
    //     andI = p.simppair
    //     andEl = p.simppi1
    //     andEr = p.simppi2
    // }

    // dependent conjunctions as dependent product types 
    // DependentConjunctionCH : .product_types.DependentProductTypes -> .dependent_pl.DependentConjunction = p -> .dependent_pl.DependentConjunction {
    //     include .concepts.Logic = LogicCH(p)
    //     dand = p.depprod
    // }

    // DependentConjunctionNDCH : .product_types.DependentProducts -> .dependent_pl.DependentConjunctionND = p -> .dependent_pl.DependentConjunctionND {
    //     include .dependent_pl.DependentConjunction = DependentConjunctionCH(p)
    //     dandI = p.deppair
    //     dandEl = p.deppi1
    //     dandEr = p.deppi2
    // }

    // implications as functions types
    // ImplicationCH: .function_types.SimpleFunctionTypes -> .pl.Implication = f -> .pl.Implication {
    //     include .concepts.Propositions = PropositionsAsTypes(f)
    //     impl = f.simpfun
    // }

    // ImplicationNDCH: .function_types.SimpleFunctions -> .pl.ImplicationND = f -> .pl.ImplicationND {
    //     include .pl.Implication = ImplicationCH(f)
    //     include .concepts.Proofs = ProofsAsTerms(f)
    //     implI = f.simplambda
    //     implE = f.simpapply
    // }

    // dependent implication as dependent function types
    // DependentImplicationCH : .function_types.DependentFunctionTypes -> .dependent_pl.DependentImplication = f -> .dependent_pl.DependentImplication {
    //     include .concepts.Logic = LogicCH(f)
    //     dimpl = f.depfun
    // }

    // DependentImplicationNDCH : .function_types.DependentFunctions -> .dependent_pl.DependentImplicationND = f -> .dependent_pl.DependentImplicationND {
    //     include .dependent_pl.DependentImplication = DependentImplicationCH(f)
    //     dimplI = f.deplambda
    //     dimplE = f.depapply
    // }

    // disjunction as coproduct types
    // DisjunctionCH: .coproduct_types.CoproductTypes -> .pl.Disjunction = c -> .pl.Disjunction {
    //     include .concepts.Propositions = PropositionsAsTypes(c)
    //     or = c.coprod
    // }

    // DisjunctionNDCH: .coproduct_types.Coproducts -> .pl.DisjunctionND = c -> .pl.DisjunctionND {
    //     include .concepts.Logic = LogicCH(f)
    //     include .pl.Disjunction = DisjunctionCH(c)
    //     orI1 = c.inj1
    //     orI2 = c.inj2
    //     orE = c.cases
    // }
}