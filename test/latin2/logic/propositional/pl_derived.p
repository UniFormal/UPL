module pl_derived {
    theory Flexary_and {
        include .pl.IPLND
        andF: ???
        andFI: ???
        andFE: ???
    }

    theory Flexary_or {
        include .pl.IPLND
        orF: ???
        orFI: ???
        orFE: ???
    }

    theory Flexary_impl {
        include .pl.IPLND
        implF: ???
        implFI: ???
        implFE: ???
    }

    theory Flexary_PL {
        include .pl.PLND
        include Flexary_and
        include Flexary_or
        include Flexary_impl
    }

    theory And3 {
        include .pl.IPLND
        and3: prop -> prop -> prop -> prop = A -> B -> C -> A ∧ B ∧ C
        and3E1: (A,B,C) -> ded(and3 A B C) -> ded A = ???
        and3E2: (A,B,C) -> ded(and3 A B C) -> ded B = ???
        and3E3: (A,B,C) -> ded(and3 A B C) -> ded C = ???
        and3I: (A,B,C) -> ded A -> ded B -> ded C -> ded(and3 A B C) = ???
    }

    theory Or3 {
        include .pl.IPLND
        or3: prop -> prop -> prop -> prop = A -> B -> C -> A ∨ B ∨ C
        or3E: (A,B,C,D) -> ded(or3 A B C) -> (ded A -> ded D) -> (ded B -> ded D) -> (ded C -> ded D) -> ded D = ???
        or3I1: (A,B,C) -> ded A -> ded(or3 A B C) = ???
        or3I2: (A,B,C) -> ded B -> ded(or3 A B C) = ???
        or3I3: (A,B,C) -> ded C -> ded(or3 A B C) = ???
    }

    theory Impl2 {
        include .pl.IPLND
        impl2: prop -> prop -> prop -> prop = A -> B -> C -> A ⇒ B ⇒ C
        impl2E: (A,B,C) -> ded(impl2 A B C) -> ded A -> ded B -> ded C = ???
        impl2I: (A,B,C) -> (ded A -> (ded B -> ded C)) -> ded(impl2 A B C) = ??? 
    }

    theory Derived_and {
        include .pl.IPLND
        include And3
        assoc_and: (A,B,C) -> ded(A ∧ (B ∧ C) ⇔ (A ∧ B) ∧ C) = ???
    }

    theory Derived_or {
        include .pl.IPLND
        include Or3
        assoc_or: (A,B,C) -> ded(A ∨ (B ∨ C) ⇔ (A ∨ B) ∨ C) = ???
    }

    theory Derived_impl {
        include Impl2
    }

    theory Derived_and_or {
        include .pl.IPLND
        distrib_and_or_right_in: (A,B,C) -> ded(A ∧ (B ∨ C)) -> ded((A ∧ B ) ∨ (A ∧ C)) = ???
        distrib_and_or_right_out : (A,B,C) -> ded((A ∧ B ) ∨ (A ∧ C)) -> ded(A ∧ (B ∨ C)) = ???
        distrib_and_or_right : (A,B,C) -> ded (A ∧ (B ∨ C) ⇔ (A  ∧ B ) ∨ (A ∧ C)) = ???
        distrib_or_and_right_in : (A,B,C) -> ded (A ∨ (B ∧ C)) -> ded ((A ∨ B ) ∧ (A ∨ C)) = ???
        distrib_or_and_right_out : (A,B,C) -> ded ((A ∨ B) ∧ (A ∨ C)) -> ded (A ∨ (B ∧ C)) = ???
        distrib_or_and_right: (A,B,C) -> ded (A ∨ (B ∧ C) ⇔ (A ∨ B) ∧ (A ∨ C)) = ???
    }

    theory Derived_impl_or {
        include .pl.IPLND
        distrib_impl_or_left_in: (A,B,C) -> ded((A ∨ B) ⇒ C) -> ded  ((A ⇒ C) ∧ (B ⇒ C)) = ???
        distrib_impl_or_left_out: (A,B,C) -> ded((A ⇒ C )∧ ( B ⇒ C)) -> ded  ((A ∨ B) ⇒ C) = ???
        distrib_impl_or_left: (A,B,C) -> ded((A ∨ B) ⇒ C ⇔ (A ⇒ C ) ∧ (B ⇒ C)) = ???
        distrib_or_impl_left_in: (A,B,C) -> ded((A ⇒ B) ∨ (A ⇒ C)) -> ded(A ⇒ (B ∨ C)) = ???
    }

    theory Derived_impl_and {
        include .pl.IPLND
        distrib_impl_and_right_in : (A,B,C) -> ded(A ⇒ (B ∧ C)) -> ded ((A ⇒ B) ∧ (A ⇒ C)) = ???
        distrib_impl_and_right_out : (A,B,C) -> ded ((A ⇒ B) ∧ (A ⇒ C)) -> ded(A ⇒ (B ∧ C)) = ???
        distrib_impl_and_right: (A,B,C) -> ded(A ⇒ (B ∧ C) ⇔ (A ⇒ B) ∧ (A ⇒ C)) = ???
    }

    theory Derived_IPL {
        include .pl.IPLND
        include Derived_and
        include Derived_or
        include Derived_impl
        include Derived_and_or
        include Derived_impl_or
        include Derived_impl_and
    }

    theory Derived_impl_classical {
        include .pl.IPLND
        impl_via_or_not_in: (A,B) -> ded(B ⇒ A) -> ded(A ∨ ¬ B) = ???
        impl_via_or_not_out: (A,B) -> ded(A ∨ ¬ B) -> ded(B ⇒ A) = ???
        impl_via_or_not: (A,B) -> ded(B ⇒ A ⇔ A ∨ ¬ B) = ???
    }

    theory Derived_impl_and_classical {
        include .pl.IPLND
        distrib_impl_and_left_in: (A,B,C) -> ded ((A ∧ B) ⇒ C) -> ded ((A ⇒ C) ∨ (B ⇒ C)) = ???
        distrib_impl_and_left_out: (A,B,C) -> ded ((A ⇒ C) ∨ (B ⇒ C)) -> ded ((A ∧ B) ⇒ C) = ???
        distrib_impl_and_left : (A,B,C) -> ded ((A ∧ B) ⇒ C ⇔ (A ⇒ C) ∨ (B ⇒ C)) = ???
    }

    theory Derived_PL {
        include .pl.PLND
		include Derived_IPL		
		include Derived_impl_classical		
		include Derived_impl_and_classical
    }

    theory Nnf_or {
        include .pl.IPLND
        nnf_or_in: (A,B) -> ded (¬(A ∨ B)) ->  ded (¬A  ∧ ¬ B) = ???
        nnf_or_out : (A,B) -> ded ((¬A) ∧ (¬ B)) -> ded (¬ (A ∨ B)) = ???
        nnf_or: (A,B) -> ded (¬ (A ∨ B) ⇔ (¬A ∧ ¬B)) = ???
    }

    theory Nnf_and {
        include .pl.IPLND
        nnf_and_out : (A,B) -> ded(¬A ∨ ¬B)  -> ded (¬(A ∧ B)) = ???
    }

    theory Nnf_IPL {
        include .pl.IPLND
        include Nnf_or
		include Nnf_and
    }

    theory Nnf_and_classic {
        include .pl.PLND
        include Nnf_and
        nnf_and_in: (A,B) -> ded (¬ (A ∧ B)) -> ded(¬A  ∨ ¬ B) = ???
        nnf_and: (A,B) -> ded(¬(A ∧ B) ⇔ ¬A ∨ ¬ B) = ???
    }

    theory Nnf_PL {
        include .pl.PLND
        include Nnf_IPL
		include Nnf_and_classic
    }

    theory And_functor {
        include .pl.IPLND
        and_functor_right : (A,B,C) -> ded(A ∧ B) -> (ded B -> ded C) -> ded(A ∧ C) = ???
        and_functor_left : (A,B,C) -> ded(A ∧ B) -> (ded A -> ded C) -> ded(C ∧ B) = ???
    }

    theory Or_functor {
        include .pl.IPLND
        or_functor_right : (A,B,C) -> ded(A ∨ B) -> (ded B -> ded C) -> ded(A ∨ C) = ???
        or_functor_left : (A,B,C) -> ded(A ∨ B) -> (ded A -> ded C) -> ded(C ∨ B) = ???
    }

    theory Implication_functor {
        include .pl.IPLND
        implication_functor_right : (A,B,C) -> ded(A ⇒ B) -> (ded B -> ded C) -> ded(A ⇒ C) = ???
    }
}