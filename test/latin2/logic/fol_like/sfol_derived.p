module sfol_derived {
    theory Tforall2 {
        include .sfol.ISFOLND
    
        tforall2 : (A,B) -> (tm A -> tm B -> prop) -> prop = ???
        tforall2E : (A,B,P,X,Y) ->  ded (tforall2(A,B) P) -> ded (P X Y) = ???
        tforall2I : (A,B,P) -> ((x,y) -> ded (P x y)) -> ded (tforall2(A,B) P) = ???
    }

    theory Texists2 {
        include .sfol.ISFOLND

        texists2 : (A,B) -> (tm A -> tm B -> prop) -> prop = ???
        texists2I : (A,B,P,X,Y) -> ded (P X Y) -> ded (texists2(A,B) P) = ???
        texists2E : (A,B,P,C) -> ded (texists2(A,B) P) ->  ((x,y) -> ded (P x y) -> ded C) -> ded C = ???
    }

    theory Derived_tforall {
        include .sfol.ISFOLND
        include Tforall2

        tforall_flip : ??? = ???
        equal_tforall_flip: ??? = ???
        tforall_modes_ponens : ??? = ???
    }

    theory Derived_texists {
        include .sfol.ISFOLND
        include Texists2

        texists_flip : ??? = ???
        equal_texists_flip: ??? = ???
    }

    theory Derived_tforall_and {
        include.sfol. SFOLND
        
        distrib_tforall_and_in: ??? = ???
        distrib_tforall_and_out: ??? = ???
        distrib_tforall_and : ??? = ???
        distrib_and_tforall_out : ??? = ???
    }

    theory Derived_texists_and {
        include .sfol.ISFOLND

        distrib_texists_and_in : ??? = ???
        distrib_and_texists_out : ??? = ???
    }

    theory Derived_tforall_or {
        include .sfol.ISFOLND

        distrib_tforall_or_out: ??? = ???
        distrib_or_tforall_out : ??? = ???
}


    theory Derived_texists_or {
        include .sfol.ISFOLND
        
        distrib_texists_or_in: ??? = ???
        distrib_texists_or_out : ??? = ???
        distrib_texists_or : ??? = ???
        distrib_or_texists_out : ??? = ???
    }

    theory Derived_ISFOL {
        include .sfol.ISFOLND
        include Derived_tforall
        include Derived_texists
        include Derived_tforall_and
        include Derived_texists_and
        include Derived_tforall_or
        include Derived_texists_or 
        
        exists_tforall_flip : ??? = ???
    }

    theory Derived_SFOL {
        include .sfol.SFOLND
        include Derived_ISFOL
    }

    theory Nnf_texists {
        include .sfol.ISFOLND
        
        nnf_texists_out: ??? = ???
        nnf_texists_in: ??? = ???
        nnf_texists : ??? = ???
    }

    theory Nnf_tforall {
        include .sfol.ISFOLND
        nnf_tforall_out: ??? = ???
    }

    theory Nnf_ISFOL {
        include .sfol.ISFOL
        include Nnf_texists
        include Nnf_tforall

    }

    theory Nnf_tforall_classic {
        include .sfol.SFOLND
        include Nnf_tforall
        include Nnf_texists

        nnf_tforall_in: ??? = ???
        nnf_tforall : ??? = ???
    }

    theory Nnf_FOL {
        include .fol.FOLND
        include .fol_derived.Nnf_IFOL
        include Nnf_tforall_classic
    }

    theory Tnd_inductive {
        include .sfol.ISFOLND
        include .pl_derived.Nnf_or
        
        tnd_true : ded (⊤ ∨ ¬⊤) = ???
        tnd_false : ded (⊥ ∨ ¬⊥) = ???
        tnd_neg: (F) -> ded (F ∨ ¬F) -> ded (¬F ∨ ¬¬F) = ???
        tnd_and : (F,G) -> ded (F ∨ ¬F) -> ded (G ∨ ¬G) -> ded ((F ∧ G) ∨ ¬(F ∧ G)) = ???
        tnd_or : (F,G) -> ded (F ∨ ¬F) -> ded (G ∨ ¬G) -> ded ((F ∨ G) ∨ ¬(F ∨ G)) = ???
    }

    theory Equiv_Subs_inductive {
        include .sfol.ISFOLND
        
        equiv_subs_true : ded (⊤ ⇔ ⊤) = ???  
        equiv_subs_false : ded (⊥ ⇔ ⊥) = ???             
        equiv_subs_neg : (F,F2) -> ded (F ⇔ F2) -> ded (¬F ⇔ ¬F2) = ???             
        equiv_subs_and : (F,F2,G,G2) -> ded (F ⇔ F2) -> ded (G ⇔ G2) -> ded ((F ∧ G) ⇔ (F2 ∧ G2)) = ???
        equiv_subs_or: (F,F2,G,G2) -> ded (F ⇔ F2) -> ded (G ⇔ G2) -> ded ((F ∨ G) ⇔ (F2 ∨ G)) = ???
        equiv_subs_impl: (F,F2,G,G2) -> ded (F ⇔ F2) -> ded (G ⇔ G2) -> ded ((F ⇒ G) ⇔ (F2 ⇒ G2)) = ??? 
        equiv_subs_tforall : ??? = ???
        equiv_subs_texists : ??? = ???
    }

    theory Tforall_functor {
        include .sfol.ISFOLND
        tforall_functor: ??? = ???
    }


    theory Texists_functor {
        include .sfol.ISFOLND
        texists_functor: ??? = ???
    }
}