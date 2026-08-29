module pl_views {
    // The views currently still need single theories as a domain and codomain, which 
    // forces us to provide spurious named theories. This should be refactored when
    // multi-theory domains and codomains are possible.

    theory NegationTruth {
        include .pl.Negation
        include .pl.Truth
    }

    theory NegationFalsity {
        include .pl.Negation
        include .pl.Falsity
    }

    theory NegationTruthND {
        include NegationTruth
        include .pl.NegationNDE
        include .pl.TruthND
    }

    theory NegationFalsityND {
        include NegationFalsity
        include .pl.NegationND
        include .pl.FalsityND
    }

    FalsityNegTruth: NegationTruth -> .pl.Falsity = nt -> .pl.Falsity {
        //include .concepts.Propositions
        type prop = nt.prop
        falsity = nt.not(nt.truth)
    }

    FalsityNegTruthND: NegationTruthND -> .pl.FalsityND = nt -> .pl.FalsityND {
        //include .pl.Falsity = FalsityNegTruth(nt)
        //include .concepts.Proofs
        type prop = nt.prop
        type ded(p: prop) = nt{ded p}
        falseE = ???
    }

    // TruthNegFalsity: NegationFalsity -> .pl.Truth = nf -> .pl.Truth {
    //     include .concepts.Propositions
    //     truth = nf.not(nf.falsity)
    // }

    // TruthNegFalsityND: NegationFalsityND -> .pl.TruthND = nf -> .pl.TruthND {
    //     include .concepts.Propositions
    //     include .concepts.Proofs
    //     include .pl.Truth = TruthNegFalsity(nf)
    //     trueI = ???
    // }

    theory NegationConjunction {
        include .pl.Negation
        include .pl.Conjunction
    }

    // DisjNegConj: NegationConjunction -> .pl.Disjunction = nc -> .pl.Disjunction {
    //     include .concepts.Propositions
    //     or = (a,b) -> nc.not(nc.and(nc.not(a),nc.not(b)))
    // }

    theory NegationDisjunction {
        include .pl.Negation
        include .pl.Disjunction
    }

    // ConjNegDisj: NegationDisjunction -> .pl.Conjunction = nd -> .pl.Conjunction {
    //     include .concepts.Propositions
    //     and = (a,b) -> nd.not(nd.or(nd.not(a),nd.not(b)))
    // }

    theory NegationImplication {
        include .pl.Negation
        include .pl.Implication
    }

    // DisjNegImpl: NegationImplication -> .pl.Disjunction = ni -> .pl.Disjunction {
    //     include .concepts.Propositions
    //     or = (a,b) -> ni.impl(ni.not(a), b)
    // }

    // ImplNegDisj: NegationDisjunction -> .pl.Implication = nd -> .pl.Implication {
    //     include .concepts.Propositions
    //     impl = (a,b) -> nd.or(nd.not(a), b)
    // }

    // ImplNegConj: NegationConjunction -> .pl.Implication = nc -> .pl.Implication {
    //     include .concepts.Propositions
    //     impl = (a,b) -> nc.not(nc.and(a, nc.not(b)))
    // }

    theory ImplicationConjunction {
        include .pl.Implication
        include .pl.Conjunction
    }

    // EquivImplConj: ImplicationConjunction -> .pl.Equivalence = ic -> .pl.Equivalence {
    //     include .concepts.Propositions
    //     equiv = (a,b) -> ic.and(ic.impl(a,b), nc.impl(b,a))
    // }

    theory ImplicationFalsity {
        include .pl.Implication
        include .pl.Falsity
    }

    // NegImplFalsity: ImplicationFalsity -> .pl.Negation = imf -> .pl.Negation {
    //     include .concepts.Propositions
    //     not = (a) -> imf.impl(a, imf.falsity)
    // }
}