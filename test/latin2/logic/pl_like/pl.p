

module pl {
    theory Equivalence {
        include .concepts.Propositions

        equiv : (prop, prop) -> prop    # infix ⇔
    }

    theory EquivalenceNDI {
        include Equivalence
        include .concepts.Logic

        equivI:--- (⊦F => ⊦G) => (⊦G => ⊦F) => ⊦(F ⇔ G)
    }

    theory EquivalenceNDE {
        include Equivalence
        include .concepts.Logic

        equivEl:--- ⊦(F ⇔ G) => (⊦F => ⊦G)
        equivEr:--- ⊦(F ⇔ G) => (⊦G => ⊦F)
    }

    theory EquivalenceND {
        include EquivalenceNDI
        include EquivalenceNDE
    }

    theory Lindenbaum {
        include EquivalenceND
        // missing
    }

    theory Truth {
        include .concepts.Propositions

        verum : prop 
    }

    theory TruthND {
        include Truth
        include .concepts.Logic

        trueI : |- ⊦ verum
    }

    theory Falsity {
        include .concepts.Propositions

        falsum : prop 
    }

    theory FalsityND {
        include Falsity
        include .concepts.Logic

        falseE : |- (⊦falsum) => inconsistent
    }

    theory Negation {
        include .concepts.Propositions

        not: prop -> prop   # prefix ¬ 
    }

    theory NegationNDI {
        include Negation
        include .concepts.Logic

        notI:--- (⊦F => inconsistent) => ⊦(¬F)
    }

    theory NegationNDE {
        include Negation
        include .concepts.Logic

        notE:--- ⊦(¬F) => ⊦F => inconsistent
        notE_done:--- ⊦(¬F) => ⊦F => ⊦G
    }

    theory NegationND {
        include NegationNDI
        include NegationNDE
    }

    theory Disjunction {
        include .concepts.Propositions

        or: (prop, prop) -> prop    # infix ∨
    }

    theory DisjunctionNDI {
        include Disjunction
        include .concepts.Logic

        orIl:--- ⊦F => ⊦(F ∨ G)
        orIr:--- ⊦G => ⊦(F ∨ G)
    }

    theory DisjunctionNDE {
        include Disjunction
        include .concepts.Logic

        orE:--- ⊦(F ∨ G) => (⊦F => ⊦C) => (⊦G => ⊦C) => ⊦C
    }

    theory DisjunctionND {
        include DisjunctionNDI
        include DisjunctionNDE

        or_swap:--- ⊦(F ∨ G) => ⊦(G ∨ F)
    }

    theory Conjunction {
        include .concepts.Propositions

        and: (prop, prop) -> prop    # infix ∧
    }

    theory ConjunctionNDI {
        include Conjunction
        include .concepts.Logic

        andI:--- ⊦F => ⊦G => ⊦(F ∧ G)
    }

    theory ConjunctionNDE {
        include Conjunction
        include .concepts.Logic

        andEl:--- ⊦(F ∧ G) => ⊦F 
        andEr:--- ⊦(F ∧ G) => ⊦G 
    }

    theory ConjunctionND {
        include ConjunctionNDI
        include ConjunctionNDE

        and_swap:--- ⊦(F ∧ G) => ⊦(G ∧ F)
    }

    theory Implication {
        include .concepts.Propositions

        impl : (prop, prop) -> prop    # infix ⇒
    }

    theory ImplicationNDI {
        include Implication
        include .concepts.Logic

        implI:--- (⊦F => ⊦G) => ⊦(F ⇒ G)
    }

    theory ImplicationNDE {
        include Implication
        include .concepts.Logic

        implE:--- ⊦(F ⇒ G) => ⊦F => ⊦G
    }

    theory ImplicationND {
        include ImplicationNDI
        include ImplicationNDE
    }

    theory IPL {
        include .concepts.Propositions
        include Truth
        include Falsity
        include Negation
        include Conjunction
        include Disjunction
        include Implication
        include Equivalence
    }

    theory IPLND {
        include IPL
        include .concepts.Logic
        include TruthND
        include FalsityND
        include NegationND
        include ConjunctionND
        include DisjunctionND
        include ImplicationND
        include EquivalenceND

        not_or_left:--- ⊦(¬(F ∨ G)) => ⊦(¬F)
        not_or_right:--- ⊦(¬(F ∨ G)) => ⊦(¬G)
        nntnd:--- ⊦(¬(¬(F ∨ ¬F)))
    }

    theory Classical {
        include .concepts.Logic

        classical:--- ((⊦F => inconsistent) => inconsistent) => ⊦F
    }

    theory ProofIrrelevance {
        include .concepts.Logic
        // missing
    }

    theory PL {
        include IPL
    }

    theory PLND {
        include PL
        include IPLND
        include ProofIrrelevance
        include Classical

        impl_flip:--- ⊦(F ⇒ G) => ⊦(¬G ⇒ ¬F)
        indirect:--- (⊦(¬F) => inconsistent) => ⊦F
        dne:--- ⊦(¬(¬F)) => ⊦F
        tnd:--- ⊦(F ∨ ¬F)
    }

    // doesn't work

    // nnf : PLND.prop -> PLND.prop
    // nnf = F -> F match {
    //     PLND.and(a,b) -> PLND.and(nnf(a), nnf(b))
    //     PLND.neg(a) -> nnf(a)
    // }
}