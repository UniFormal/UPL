module test {

    theory Propositions {
        type prop
    }

    theory Proofs {
        include Propositions
        type ded(p: prop)
        lemma: (F, G) -> ded F -> (ded F -> ded G) -> ded G = (F, G) -> p -> Q -> Q p
    }

    theory PL {
        type prop
        not: prop -> prop 
        or: (prop, prop) -> prop
        and: (prop, prop) -> prop
    }

    nnf : PL.prop -> PL.prop
    nnf = F -> F match {
        PL.not(PL.not(a)) -> nnf(a)
        PL.not(PL.and(a,b)) -> nnf(PL.or(PL.not(a), PL.not(b)))
        PL.not(PL.or(a,b)) -> nnf(PL.and(PL.not(a), PL.not(b)))
        // and so on...
    }



}





module meta_magmas {    
    theory Magma {
        include .relations.EqualityType
        op: (carrier, carrier) -> carrier # infix ∘
    }
}

module magmas {
    include .sfol.SFOLEQND

    theory Magma {
        include .sets.Set
        op: (U, U) -> U # infix ∘
    }
}

module pl2 {
    theory ProofIrrelevance {
        include .concepts.Logic
        proofIrrelevance: F -> (x,y::ded F) -> bool 
            = F -> (x,y) -> x==y
    }


    theory FOL {
        include .base_languages.UntypedLogic
        
        falsity: prop # nullfix ⊥
        not: prop -> prop # prefix ¬
        // this doesn't work
        // and: prop -> prop -> prop # infix-right ∧
        and: (prop, prop) -> prop # infix-right ∧
        forall: (term -> prop) -> prop # bindfix ∀
    }



    theory HardSubtyping {
        include .concepts.TypedTerms
        include .equality.TypedEquality
        include Subtyping
        include SubtypingPreorder

        inject: (A, B, ded A⪽B, tm A) -> tm B
        inject_trans: (A,B,C,x,P,Q) -> 
            ded tequal(C, inject(B, C, Q, inject(A, B, P, x)), 
            inject(A, C, sub.trans(P,Q), x)) 
    }


    PropositionsAsTypes: .concepts.Types -> .concepts.Propositions = t -> §{
        type prop = t.tp
    }
    
    ProofsAsTerms: .concepts.TypedTerms -> .concepts.Proofs = t -> §{
        include .concepts.Propositions = PropositionsAsTypes(t)
        type ded(p: prop) = t{tm p}
    }


    theory EquivalenceND {
        include EquivalenceNDI
        include EquivalenceNDE

        equiv_equivalence: .relations.EquivalenceRelation {
            type carrier = prop
            type rel(c1:carrier, c2:carrier) = ded(c1 ⇔ c2)
            refl = ???
            sym = ???
            trans = ???
        }
    }


    theory PLTest {
        include PLND
        A: prop
        B: prop
    }

    nnf : PL.prop -> PL.prop
    nnf = F -> F match {
        // omitted
    }

    // phi = A ⇔ B
    phi = PLTest{equiv}(PLTest{A}, PLTest{B}) 
    
    // phi_nnf = (¬A ∨ B) ∧ (¬B ∨ A)
    phi_nnf = PLTest{and}(
        PLTest{or}(PLTest{not}(PLTest{A}),PLTest{B}),
        PLTest{or}(PLTest{not}(PLTest{B}),PLTest{A}))

    test = {ASSERT(nnf phi, phi_nnf)}
}


