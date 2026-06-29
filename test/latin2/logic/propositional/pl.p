// A fully modular specification of intuitionistic and classical propositional logics.
//
// Every connective and all proof rules are specified in their own theories to maximize reusability.
// Proof rules follow natural deduction except that a judgment for inconsistency is used in some rules.

module pl {
    theory Equivalence {
        include .concepts.Propositions
        equiv : (prop, prop) -> prop # infix ⇔
    }

    theory EquivalenceNDI {
        include Equivalence
        include .concepts.Proofs
        equivI: (F,G) -> (ded F -> ded G) -> (ded G -> ded F) -> ded F⇔G
    }

    theory EquivalenceNDE {
        include Equivalence
        include .concepts.Proofs
        equivEl: (F,G) -> ded F⇔G -> ded F -> ded G
        equivEr: (F,G) -> ded F⇔G -> ded G -> ded F
    }

    theory EquivalenceND {
        include EquivalenceNDI
        include EquivalenceNDE

        // equiv_equivalence: .relations.EquivalenceRelation {
        //     type carrier = prop
        //     // type rel = (x, y) -> ded x⇔y
        //     refl = ???
        //     sym = ???
        //     trans = ???
        // }

        // lindenbaum: .relations.EqualityType {
        //     type carrier = prop
        //     equalityRel = equiv_equivalence
        // }
    }

    theory Lindenbaum {
        include EquivalenceND
        // include .relations.EqualityType = EquivalenceND.lindenbaum
    }

    theory Truth {
        include .concepts.Propositions
        truth : prop # nullfix ⊤
    }

    theory TruthND {
        include Truth
        include .concepts.Logic
        trueI : ded (⊤)
    }

    theory Falsity {
        include .concepts.Propositions
        falsity : prop # nullfix ⊥
    }

    theory FalsityND {
        include Falsity
        include .concepts.Logic
        falseE : ded (⊥) -> inconsistent
    }

    theory Negation {
        include .concepts.Propositions
        not: prop -> prop # prefix ¬ 
    }

    theory NegationNDI {
        include Negation
        include .concepts.Logic
        notI: (F,G) -> (ded F -> inconsistent) -> ded (¬F)
    }

    theory NegationNDE {
        include Negation
        include .concepts.Logic
        notE: F -> ded (¬F) -> ded F -> inconsistent
        notE_done: (F,G) -> ded (¬F) -> ded F -> ded G
    }

    theory NegationND {
        include NegationNDI
        include NegationNDE
    }

    theory Disjunction {
        include .concepts.Propositions
        or: (prop, prop) -> prop # infix ∨
    }

    theory DisjunctionNDI {
        include Disjunction
        include .concepts.Logic
        orIl: (F,G) -> ded F -> ded F∨G
        orIr: (F,G) -> ded G -> ded F∨G
    }

    theory DisjunctionNDE {
        include Disjunction
        include .concepts.Logic
        orE: (F,G,C) -> ded F∨G -> (ded F -> ded C) -> (ded G -> ded C) -> ded C
    }

    theory DisjunctionND {
        include DisjunctionNDI
        include DisjunctionNDE
        or_swap: (F,G) -> ded F∨G -> ded G∨F
    }

    theory Conjunction {
        include .concepts.Propositions
        and: (prop, prop) -> prop # infix ∧
    }

    theory ConjunctionNDI {
        include Conjunction
        include .concepts.Logic
        andI: (F,G) -> ded F -> ded G -> ded F∧G
    }

    theory ConjunctionNDE {
        include Conjunction
        include .concepts.Proofs
        andEl: (F,G) -> ded F∧G -> ded F 
        andEr: (F,G) -> ded F∧G -> ded G 
    }

    theory ConjunctionND {
        include ConjunctionNDI
        include ConjunctionNDE
        and_swap: (F,G) -> ded F∧G -> ded G∧F
    }

    theory Implication {
        include .concepts.Propositions
        impl : (prop, prop) -> prop # infix ⇒
    }

    theory ImplicationNDI {
        include Implication
        include .concepts.Logic
        implI: (F,G) -> (ded F -> ded G) -> ded (F ⇒ G)
    }

    theory ImplicationNDE {
        include Implication
        include .concepts.Logic
        implE: (F,G) -> ded (F ⇒ G) -> ded F -> ded G
    }

    theory ImplicationND {
        include ImplicationNDI
        include ImplicationNDE

        // impl_order: .relations.Preorder  {
        //     type carrier = prop
        //     // type rel = (x,y) -> ded x⇒y
        //     refl = ???
        //     trans = ???
        // }
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

        not_or_left: (F,G) -> ded (¬(F∨G)) -> ded ((¬F))
        not_or_right: (F,G) -> ded (¬(F∨G)) -> ded (¬G)
        nntnd: F -> ded (¬¬(F∨(¬F)))

        // impl_order : .relations.PartialOrder {
        //     type carrier = impl_preorder.carrier
        //     // type rel = impl_preorder.rel
        //     refl = impl_preorder.refl
        //     trans = impl_preorder.trans

        //     equalityRel = equiv_equivalence
        //     antisym = ???
        // }
    }

    theory Classical {
        include .concepts.Logic
        classical: F -> ((ded F -> inconsistent) -> inconsistent) -> ded F
    }

    theory ProofIrrelevance {
        include .concepts.Logic
        proofIrrelevance: F -> (x,y::ded F) -> bool = F -> (x,y) -> x==y
    }

    theory PL {
        include IPL
    }

    theory PLND {
        include PL
        include IPLND
        include ProofIrrelevance
        include Classical

        impl_flip: (F,G) -> ded F⇒G -> ded (¬G ⇒ (¬F))
        indirect: (F,G) -> (ded ((¬F)) -> inconsistent) -> ded F
        dne: (F,G) -> ded (¬(¬F)) -> ded F
        tnd: (F,G) -> ded F∨(¬F)
    }

    // doesn't work
    // nnf : PLND.prop -> PLND.prop
    // nnf = F -> F match {
    //     PLND.and(a,b) -> PLND.and(nnf(a), nnf(b))
    //     PLND.neg(a) -> nnf(a)
    // }
}