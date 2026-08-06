module type_theory_to_logic {
    TypesAsPropositions: .concepts.Propositions -> .concepts.Types = p -> .concepts.Types {
        type tp = p.prop
    }

    // TermsAsProofs: .concepts.Proofs -> .concepts.TypedTerms = p -> .concepts.TypedTerms {
    //     include .concepts.Types = TypesAsPropositions(p)
    //     type tm(a: tp) = p{ded a}
    // }

    // TypedEqualityCH: (.concepts.Logic, .pl.ProofIrrelevance) -> .equality.TypedEqualityND = (l, p) -> .equality.TypedEqualityND {
    //     include .concpets.TypedTerms = TermsAsProofs(l)
    //     //  propositions in type theory mostly occur as equalities between terms
    //     //  Thus, we need a type that can hold equalities between proofs of F. 
    //     //  In the presence of proof irrelevance, they are equal anyway and we can simply use F.
    //     tequal = (F, pf1, pf2) -> F
    //     trefl = ???
    //     tcongB = (A,B,X,Y) -> p -> P -> q -> q
    // }

    // DependentTypeEqualityCH: (.concepts.Logic, .pl.EquivalenceND, .pl.ProofIrrelevance) -> .type_equality.DependentTypeEquality = (l, e, p) -> .type_equality.DependentTypeEquality {
    //     include .equality.TypedEqualityND = TypedEqualityCH(l, p)
    //     // type equality is mapped to equivalence of propositions
    //     tpeq.uequal = (F, G) -> e.equiv(F, G)
    //     tpeq.urefl = (x) -> e.equiv_equivalence.refl
    //     // The substitution property for equivalence can only be proved on the meta-level.
    //     tpeq.ucongP = ???
    //     transport = e.equivEl
    //     transport_refl = ???
    //     // This proof succeeds trivially, but only if its expected type can be computed, which requires translating tpeq.ucongP.
    //     transport_trans = ???
    // }

    // EmptyTypeCH: (.pl.FalsityND, .pl.ProofIrrelevance) -> .empty_type.EmptyType = (f, p) -> .empty_type.EmptyType {
    //     include .equality.TypedEqualityND = TypedEqualityCH(f, p)
    //     void = f.falsity
    //     throw = f.falseE
    //     voidUnique = (A,B,F,e) -> (falseE e) B
    // }

    // UnitTypeCH: (.pl.TruthND, .pl.ProofIrrelevance) -> .unit_type.UnitType = (t, p) -> .unit_type.UnitType {
    //     include .equality.TypedEqualityND = TypedEqualityCH(t, p)
    //     unitType = t.truth
    //     unit = t.trueI
    //     unitUnique = ???
    // }

    // SimpleFunctionsCH: (.pl.ImplicationND, .pl.ProofIrrelevance) -> .function_types.SimpleFunctions = (i, p) -> .function_types.SimpleFunctions {
    //     include .equality.TypedEqualityND = TypedEqualityCH(i, p)
    //     simpfun = i.impl
    //     simplambda = i.implI
    //     simpapply = i.implE
    //     simpbeta = ???
    // }

    // SimpleProductsCH: (.pl.ConjunctionND, .pl.ProofIrrelevance) -> .product_types.SimpleProducts = (c, p) -> .product_types.SimpleProducts {
    //     include .equality.TypedEqualityND = TypedEqualityCH(c, p)
    //     simpprod = c.and
    //     simppair = c.andI
    //     simppi1 = c.andEl
    //     simppi2 = c.andEr
    //     compute1 = ???
    //     compute2 = ???
    // }

    // CoproductsCH: (.pl.DisjunctionND, .pl.ProofIrrelevance) -> .coproduct_types.Coproducts = (d, p) -> .coproduct_types.Coproducts {
    //     include .equality.TypedEqualityND = TypedEqualityCH(d, p)
    //     coprod = d.or
    //     inj1 = d.orIl
    //     inj2 = d.orIr
    //     cases = d.orE
    //     compute1 = (A,B,C,a,f,g) -> f a
    //     compute2 = (A,B,C,b,f,g) -> g b
    // }

    // DependentFunctionsCH: (.dependent_pl.DependentImplicationND, .pl.ProofIrrelevance) -> .function_types.DependentFunctions = (i, p) -> .function_types.DependentFunctions {
    //     include .equality.TypedEqualityND = TypedEqualityCH(i, p)
    //     // We have depfun: {A: tp} (tm A ⟶ tp) ⟶ tp
    //     // and thus need to {p: prop} (⊦ p ⟶ prop) ⟶ prop.
    //     // The intuitive map of depfun to ∀ does not work because we would need to translate
    //     // - the domain type to a logical type
    //     // - the codomain type to a proposition
    //     // Instead, the CH-analog of depfun is dependent implication.
    //     depfun = i.dimpl
    //     deplambda = i.dimplI
    //     depapply = i.dimplE
    //     depbeta = ???
    // }

    // DependentProductsCH: (.dependent_pl.DependentConjunctionND, .pl.EquivalenceND, .pl.ProofIrrelevance) -> .product_types.DependentProducts = (c, e, p) -> .product_types.DependentProducts {
    //     include .equality.TypedEqualityND = TypedEqualityCH(c, p)
    //     .type_equality.DependentTypeEquality = DependentTypeEqualityCH(c, e, p)
    //     depprod = c.dand
    //     deppair = c.dandI
    //     deppi1 = c.dandEl
    //     deppi2 = c.dandEr
    //     compute1 = compute1
    //     // this requires mapping type-equality to equivalence of propositions
    //     compute2 = ???
    // }
}