module pl_hilbert {
    // Hilbert calculi for propositional and first-order logic. 
    // Here we formalize a version that is rule-maximal, i.e. we include 
    // as many rules from natural deduction a we can, i.e. all rules that 
    // do not use hypothetical reasoning. The ones that do, we reformulate 
    // into axioms, where all the function types become implications. 
    
    // Unfortunately, this means that we cannot be fully modular, since we 
    // need a treatment of implication in all cases.

    theory ImplicationHilbert {
        include .pl.ImplicationNDE
        K_ax: (F,G) -> ded (F ⇒ (G ⇒ F))
        S_ax: (F,G,H) -> ded ((F ⇒ (G ⇒ H)) ⇒ ((F ⇒ G) ⇒ (F ⇒ H)))
    }

    theory NegationHilbert {
        include .pl.NegationNDE
        include ImplicationHilbert
        notI_ax: (F) -> ded ((F ⇒ ¬F) ⇒ ¬F)
    }

    theory DisjunctionHilbert {
        include .pl.DisjunctionNDI
        include ImplicationHilbert
        orE_ax: (F,G,H) -> ded ((F ∨ G) ⇒ ((F ⇒ H) ⇒ ((G ⇒ H) ⇒ H)))
    }

    theory EquivalenceHilbert {
        include .pl.EquivalenceNDE
        include ImplicationHilbert
        equivI_ax: (F,G) -> ded ((F ⇒ G) ⇒ ((G ⇒ F) ⇒ (F ⇔ G)))
    }

    theory PLHilbert {
        include .pl.PL
        include ImplicationHilbert
        include .pl.TruthND
        include .pl.FalsityND
        include .pl.ConjunctionND
        include NegationHilbert
        include DisjunctionHilbert
        include EquivalenceHilbert
        include .pl.Classical
    }

    // ImplicationHilbert2ND: .pl.ImplicationND -> ImplicationHilbert = i -> ImplicationHilbert {
    //     include .pl.ImplicationNDE
    //     K_ax = ???
    //     S_ax = ???
    // }

    // NegationHilbert2ND: .pl.PLND -> NegationHilbert = p -> NegationHilbert {
    //     include .pl.NegationNDE
    //     include ImplicationHilbert = ImplicationHilbert2ND(p)
    //     notI_ax = ???
    // }

    // DisjunctionHilbert2ND: .pl.PLND -> DisjunctionHilbert = p -> DisjunctionHilbert {
    //     include .pl.DisjunctionNDI
    //     include ImplicationHilbert = ImplicationHilbert2ND(p)
    //     orE_ax = ???
    // }

    // EquivalenceHilbert2ND: .pl.PLND -> EquivalenceHilbert = p -> EquivalenceHilbert {
    //     include .pl.EquivalenceNDE
    //     include ImplicationHilbert = ImplicationHilbert2ND(p)
    //     equivI_ax = ???
    // }

    // PLHilbert2ND: .pl.PLND -> PLHilbert = p -> PLHilbert {
    //     include .pl.PL
    //     include ImplicationHilbert = ImplicationHilbert2ND(p)
    //     include .pl.TruthND
    //     include .pl.FalsityND
    //     include .pl.ConjunctionND
    //     include NegationHilbert = NegationHilbert2ND(p)
    //     include DisjunctionHilbert = DisjunctionHilbert2ND(p)
    //     include EquivalenceHilbert = EquivalenceHilbert2ND(p)
    //     include .pl.Classical
    // }
}