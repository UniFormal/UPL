module fol_derived {
	theory Forall2 {
        include .fol.FOLND

        forall2 : (term -> term -> prop) -> prop = ???
		forall2E : (P,X,Y) -> ded (forall2 P) -> ded (P X Y) = ???
		forall2I : (P) -> ((x,y) -> ded (P x y))  -> ded (forall2 P) = ???
    }

    theory Flexary_forall {
		include .fol.FOLND
		
		forallF : ???
		forallFE : ???
		forallFI : ???
    }

    theory Exists2 {
        include .fol.FOLND
            
        exists2 : (term -> term -> prop) -> prop = ???
        exists2I : (P,X,Y) -> ded (P X Y) -> ded (exists2 P) = ???
        exists2E : (P,C) -> ded (exists2 P) ->  ((x,y) -> ded (P x y) -> ded C) -> ded C = ???
    }

    theory Flexary_exists {
        include .fol.FOLND
            
        existsF : ???
        existsFE : ???
        existsFI : ???
    }

    theory Flexary_FOL {
        include .fol.FOLND
        include .pl_derived.Flexary_PL
        include Flexary_exists
        include Flexary_forall
    }

    theory Derived_forall {
        include Forall2
        forall_modes_ponens : (P,Q,Y) -> ded (∀ᵘ (x -> P x ⇒ Q x)) -> ded (P Y) -> ded (Q Y) = ???
    }

    theory Derived_exists {
        include Exists2
    }

    theory Derived_forall_and {
        include .fol.IFOLND
        
        distrib_forall_and_in: (P,B) -> ded (∀ᵘ(x -> P x ∧ B x )) -> ded (∀ᵘ(x -> P x) ∧ ∀ᵘ(x -> B x)) = ???
        distrib_forall_and_out: (P,B) ->  ded (∀ᵘ(x -> P x) ∧ ∀ᵘ(x -> B x)) -> ded (∀ᵘ(x -> P x ∧ B x)) = ???
        distrib_forall_and : (P,B) -> ded (∀ᵘ(x -> P x ∧ B x) ⇔ ((∀ᵘ(x -> P x)) ∧ (∀ᵘ(x -> B x)))) = ???
        distrib_and_forall_out : (P,B) -> ded ((∀ᵘ(x -> P x)) ∧ B) -> ded (∀ᵘ(x ->(P x ∧ B))) = ???
    }

    theory Derived_exists_and {
        include .fol.IFOLND

        distrib_exists_and_in :  (P,B) -> ded (∃ᵘ(x -> P x  ∧ B x)) -> ded ((∃ᵘ(x -> P x)) ∧ (∃ᵘ(x -> B x))) = ???
        distrib_and_exists_out : (P,B) -> ded ((∃ᵘ(x -> P x)) ∧ B)-> ded (∃ᵘ(x -> P x ∧ B)) = ???
    }                                 

    theory Derived_forall_or {
        include .fol.IFOLND

        distrib_forall_or_out: (P,B) -> ded ((∀ᵘ(x -> P x )) ∨ (∀ᵘ(x -> B x))) -> ded (∀ᵘ(x -> P x ∨ B x)) = ???
        distrib_or_forall_out : (P,B) -> ded ((∀ᵘ(x -> P x )) ∨ B) -> ded (∀ᵘ(x -> P x ∨ B)) = ???
    }

    theory Derived_exists_or {
        include .fol.IFOLND
            
        distrib_exists_or_in: (P,B) -> ded (∃ᵘ(x -> P x ∨ B x)) -> ded ((∃ᵘ(x -> P x)) ∨ (∃ᵘ(x -> B x)))  = ???
        distrib_exists_or_out : (P,B) -> ded ((∃ᵘ(x -> P x)) ∨ (∃ᵘ(x -> B x))) -> ded (∃ᵘ(x -> P x ∨ B x)) = ??? 
        distrib_exists_or : (P,B) -> ded ((∃ᵘ(x -> P x ∨ B x)) ⇔ ((∃ᵘ( x -> P x )) ∨ (∃ᵘ(x -> B x)))) = ???
        distrib_or_exists_out : (P,B) -> ded ((∃ᵘ(x -> P x)) ∨ B) -> ded (∃ᵘ(x -> P x ∨ B)) = ???
    }

    theory Derived_IFOL {
        include .fol.IFOLND
        include Derived_forall
        include Derived_exists
        include Derived_forall_and
        include Derived_exists_and
        include Derived_forall_or
        include Derived_exists_or
        
        exists_forall_flip : (P) -> ded (∃ᵘ(x -> ∀ᵘ(y -> P x y))) -> ded (∀ᵘ(y -> ∃ᵘ(x -> P x y))) = ???
        forall_flip : (P) -> ded (∀ᵘ(x -> ∀ᵘ(y -> P x y))) -> ded (∀ᵘ(y -> ∀ᵘ(x -> P x y))) = ???
        equal_forall_flip: (P) -> ded ((∀ᵘ(x -> ∀ᵘ(y -> P x y))) ⇔ (∀ᵘ(y -> ∀ᵘ(x -> P x y)))) = ???     
        exists_flip : (P) -> ded (∃ᵘ(x -> ∃ᵘ(y -> P x y))) -> ded (∃ᵘ(y -> ∃ᵘ(x -> P x y))) = ???
        equal_exists_flip: (P) -> ded ((∃ᵘ(x -> ∃ᵘ(y -> P x y))) ⇔ (∃ᵘ(y -> ∃ᵘ(x -> P x y)))) = ???
    }

    theory Derived_FOL {
        include .fol.FOLND
        include Derived_IFOL
    }

    theory Nnf_exists {
        include .fol.FOLND
        
        nnf_exists_out: (P) -> ded (∀ᵘ(x -> ¬(P x))) -> ded (¬∃ᵘ(x -> P x)) = ???
        nnf_exists_in: (P) -> ded (¬∃ᵘ(x ->P x)) -> ded (∀ᵘ(x -> ¬(P x))) = ???
        nnf_exists : (P) -> ded ((¬∃ᵘ(x -> P x)) ⇔ (∀ᵘ(x -> ¬(P x)))) = ???
    }

    theory Nnf_forall {
        include .fol.FOLND
        nnf_forall_out: (P) -> ded (∃ᵘ( x -> ¬(P x))) ->  ded (¬(∀ᵘ(x -> P x))) = ???
    }

    theory Nnf_IFOL {
        include .fol.IFOLND
        include .pl_derived.Nnf_PL
        include Nnf_exists
        include Nnf_forall
    }

    theory Nnf_forall_classic {
        include .fol.FOLND
        include Nnf_forall
        include Nnf_exists
            
        nnf_forall_in: (P) -> ded (¬∀ᵘ(x -> P x)) -> ded (∃ᵘ( x -> ¬(P x))) = ???  
        nnf_forall : (P) -> ded ((¬∀ᵘ(x -> P x)) ⇔ (∃ᵘ(x -> ¬(P x)))) = ???
    }

    theory Nnf_FOL {
        include .fol.FOLND
        include Nnf_IFOL
        include Nnf_forall_classic
    }

    theory Tnd_inductive {
        include .fol.FOLND
        include .pl_derived.Nnf_or
        
        tnd_true : ded (⊤ ∨ ¬⊤) = ???
        tnd_false : ded (⊥ ∨ ¬⊥) = ???
        tnd_neg: (F) -> ded (F ∨ ¬F) -> ded (¬F ∨ ¬¬F) = ???
        tnd_and : (F,G) -> ded (F ∨ ¬F) -> ded (G ∨ ¬G) -> ded ((F ∧ G) ∨ ¬(F ∧ G)) = ???
        tnd_or : (F,G) -> ded (F ∨ ¬F) -> ded (G ∨ ¬G) -> ded ((F ∨ G) ∨ ¬(F ∨ G)) = ???
    }

    theory Equiv_Subs_inductive {
        include .fol.FOLND
        
        equiv_subs_true : ded (⊤ ⇔ ⊤) = ???  
        equiv_subs_false : ded (⊥ ⇔ ⊥) = ???             
        equiv_subs_neg : (F,F2) -> ded (F ⇔ F2) -> ded (¬F ⇔ ¬F2) = ???             
        equiv_subs_and : (F,F2,G,G2) -> ded (F ⇔ F2) -> ded (G ⇔ G2) -> ded ((F ∧ G) ⇔ (F2 ∧ G2)) = ???
        equiv_subs_or: (F,F2,G,G2) -> ded (F ⇔ F2) -> ded (G ⇔ G2) -> ded ((F ∨ G) ⇔ (F2 ∨ G)) = ???
        equiv_subs_impl: (F,F2,G,G2) -> ded (F ⇔ F2) -> ded (G ⇔ G2) -> ded ((F ⇒ G) ⇔ (F2 ⇒ G2)) = ??? 	
        equiv_subs_forall : (F,F2) -> ((x) -> ded ((F x) ⇔ (F2 x))) -> ded ((∀ᵘ(x -> F x)) ⇔ (∀ᵘ(x -> F2 x)))  = ??? 
        equiv_subs_exists : (F,F2) ->((x) -> ded ((F x) ⇔ (F2 x))) -> ded ((∃ᵘ(x -> F x)) ⇔ (∃ᵘ(x -> F2 x))) = ??? 
    }

    theory Forall_functor {
        include .fol.FOLND
        forall_functor: (P,F) -> ded (∀ᵘ(x -> P x)) -> (y -> ded (P y) -> ded (F y)) -> ded (∀ᵘ(x -> F x)) = ???
    }


    theory Exists_functor {
        include .fol.FOLND
        exists_functor: (P,F) -> ded (∃ᵘ(x -> P x)) -> (y -> ded (P y) -> ded (F y)) -> ded (∃ᵘ( x -> F x)) = ???
    }
}