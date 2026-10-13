module pl_tableaux {
    theory Tableaux {
        include .concepts.Propositions
        type marktrue(p: prop)
        type markfalse(p: prop)
        type closedbranch = (p) -> marktrue p

        // We could define many of the rules below by defining P⁰ = P¹ ⟶ ⊥

        closebranch: (P) -> marktrue P -> markfalse P -> closedbranch
        closebranch2: (P) -> markfalse P -> marktrue P -> closedbranch = (P) -> p0 -> p1 -> closebranch P p1 p0
        
        proofstart: (P) -> (markfalse P -> closedbranch) -> marktrue P
        refutationstart: (P) -> (marktrue P -> closedbranch) -> markfalse P

        classicality: (P) -> ((marktrue P -> closedbranch) -> closedbranch) -> marktrue P
    }

    // We need classicality to prove proofstart
    // Tableaux2Proofs: .pl.Classical -> Tableaux = c -> Tableaux {
    //     type prop = c.prop
    //     type marktrue(p: prop) = c{ded p}
    //     type markfalse(p: prop) = c{ded p} -> c.inconsistent
    //     // type closedbranch = c.inconsistent
    //     closebranch = (P) -> p1 -> p0 -> p0 p1
    //     proofstart = c.classical
    //     classicality = c.classical
    //     refutationstart = (P) -> pr -> pr
    // }

    Proofs2Tableaux: Tableaux -> .concepts.Proofs = t -> .concepts.Proofs {
        type prop = t.prop
        type ded(p: prop) = t{marktrue p}
        // classical = classicality
    }

    theory NegationTab {
        include .pl.Negation
        include Tableaux
        negationTab0: (P) -> (markfalse (¬P)) -> (marktrue P -> closedbranch) -> closedbranch
        negationTab1: (P) -> (marktrue (¬P)) -> (markfalse P -> closedbranch) -> closedbranch
    }

    // NegationTab2ND: .pl.PLND -> NegationTab = p -> NegationTab {
    //     include Tableaux = Tableaux2Proofs(p)
    //     not = p.not
    //     negationTab0 = ???
    //     negationTab1 = ???
    // }

    // NegationND2Tab: NegationTab -> .pl.NegationND = n -> .pl.NegationND {
    //     include .concepts.Proofs = Proofs2Tableaux(n)
    //     not = n.not
    //     notI = ???
    //     notE = ???
    // }

    theory ConjunctionTab {
        include .pl.Conjunction
        include Tableaux
        conjunctionTab0: (A,B) -> markfalse(A ∧ B) -> (markfalse A -> closedbranch) -> (markfalse B -> closedbranch) -> closedbranch
        conjunctionTab1: (A,B) -> marktrue(A ∧ B) -> (marktrue A -> marktrue B -> closedbranch) -> closedbranch
    }

    // ConjunctionTab2ND: .pl.PLND -> ConjunctionTab = p -> ConjunctionTab {
    //     and = p.and
    // }

    theory DisjunctionTab {
        include .pl.Disjunction
        include Tableaux
        disjunctionTab0: (A,B) -> markfalse(A ∨ B) -> (markfalse A -> markfalse B -> closedbranch) -> closedbranch
        disjunctionTab1: (A,B) -> marktrue(A ∨ B) -> (marktrue A -> closedbranch) -> (marktrue B -> closedbranch) -> closedbranch
    }

    theory ImlicationTab {
        include .pl.Implication
        include Tableaux
        implicationTab0: (A,B) -> markfalse(A ⇒ B) -> (marktrue A -> markfalse B -> closedbranch) -> closedbranch
        implicationTab1: (A,B) -> marktrue(A ⇒ B) -> (markfalse A -> closedbranch) -> (marktrue B -> closedbranch) -> closedbranch
    }

    theory EquivalenceTab {
        include .pl.Equivalence
        include Tableaux
        equivalenceTab0: (A,B) -> markfalse(A ⇔ B) -> (markfalse A -> marktrue B -> closedbranch) -> (marktrue A -> markfalse B -> closedbranch) -> closedbranch
        equivalenceTab1: (A,B) -> marktrue(A ⇔ B) -> (markfalse A -> markfalse B -> closedbranch) -> (marktrue A -> marktrue B -> closedbranch) -> closedbranch
    }
}