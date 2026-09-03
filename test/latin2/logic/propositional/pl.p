// A fully modular specification of intuitionistic and classical propositional logics.
//
// Every connective and all proof rules are specified in their own theories to maximize reusability.
// Proof rules follow natural deduction except that a judgment for inconsistency is used in some rules.

module pl {
    theory Equivalence {
        include .concepts.Propositions
        equiv : (prop, prop) -> prop # infix-right ⇔
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
        //     //equalityRel = equiv_equivalence
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
        or: (prop, prop) -> prop # infix-right ∨
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
        and: (prop, prop) -> prop # infix-right ∧
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
        impl : (prop, prop) -> prop # infix-right ⇒
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

    theory PLTest {
        include PLND

        A: prop
        B: prop
        C: prop
        D: prop
    }

    // nnf : PLTest.prop -> PLTest.prop
    // nnf = F -> F match {
    //     // Handle equivalence by expanding to conjunction of implications
    //     PLTest.equiv(a,b) -> nnf(PLTest.and(PLTest.impl(a,b), PLTest.impl(b,a)))
        
    //     // Handle negations first (more specific patterns)
    //     PLTest.not(PLTest.not(a)) -> nnf(a)
    //     PLTest.not(PLTest.impl(a,b)) -> nnf(PLTest.and(a, PLTest.not(b)))
    //     PLTest.not(PLTest.equiv(a,b)) -> nnf(PLTest.not(PLTest.and(PLTest.impl(a,b), PLTest.impl(b,a))))
    //     PLTest.not(PLTest.and(a,b)) -> nnf(PLTest.or(PLTest.not(a), PLTest.not(b)))
    //     PLTest.not(PLTest.or(a,b)) -> nnf(PLTest.and(PLTest.not(a), PLTest.not(b)))
        
    //     // Handle positive connectives
    //     PLTest.impl(a,b) -> nnf(PLTest.or(PLTest.not(a), b))
    //     PLTest.and(a,b) -> PLTest.and(nnf(a), nnf(b))
    //     PLTest.or(a,b) -> PLTest.or(nnf(a), nnf(b))
        
    //     // Base case: atoms, truth, falsity, or negated atoms
    //     a -> a
    // }

    nnf2 : PLTest.prop -> bool -> PLTest.prop
    nnf2 = F -> pos -> F match {
        PLTest.not(a) -> nnf2 a (!pos)
        PLTest.and(a,b) -> if(pos) PLTest.and(nnf2 a true, nnf2 b true) else PLTest.or(nnf2 a false, nnf2 b false)
        PLTest.or(a,b) -> if(pos) PLTest.or(nnf2 a true, nnf2 b true) else PLTest.and(nnf2 a false, nnf2 b false)
        PLTest.impl(a,b) -> if(pos) PLTest.or(nnf2 a false, nnf2 b true) else PLTest.and(nnf2 a true, nnf2 b false)
        PLTest.equiv(a,b) -> if(pos) PLTest.and(PLTest.or(nnf2 a false, nnf2 b true), PLTest.or(nnf2 b false, nnf2 a true)) else PLTest.or(PLTest.and(nnf2 a true, nnf2 b false), PLTest.and(nnf2 b true, nnf2 a false))
        a -> if(pos) a else PLTest.not(a)
    }
    
    phi = PLTest{equiv}(
        PLTest{and}(
            PLTest{not}(PLTest{not}(PLTest{A})),
            PLTest{not}(PLTest{and}(PLTest{B}, PLTest{C}))
        ),
        PLTest{or}(
            PLTest{impl}(PLTest{C}, PLTest{D}),
            PLTest{not}(PLTest{or}(PLTest{A}, PLTest{B}))
        )
    )
    
    expected_phi = PLTest{and}(
        PLTest{or}(
            PLTest{or}(PLTest{not}(PLTest{A}), PLTest{and}(PLTest{B}, PLTest{C})),
            PLTest{or}(PLTest{or}(PLTest{not}(PLTest{C}), PLTest{D}), PLTest{and}(PLTest{not}(PLTest{A}), PLTest{not}(PLTest{B})))
        ),
        PLTest{or}(
            PLTest{and}(PLTest{and}(PLTest{C}, PLTest{not}(PLTest{D})), PLTest{or}(PLTest{A}, PLTest{B})),
            PLTest{and}(PLTest{A}, PLTest{or}(PLTest{not}(PLTest{B}), PLTest{not}(PLTest{C})))
        )
    )

    test = ASSERT(nnf2 phi true, expected_phi)
}