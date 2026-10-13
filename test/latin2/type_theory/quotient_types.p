module quotient_types {
    theory TypedQuotients {
        include .base_languages.TypedLogic
        include .equality.TypedEquality
        quotient: A -> (tm A -> tm A -> prop) -> tp
        class: (A,R) -> tm A -> tm (quotient A R)
        equiv: (A,R,x,y) -> ded(R x y) -> ded(tequal(quotient A R, class(A,R) x, class(A,R) y))
        welldefined: (A,R) -> tm (quotient A R) -> (B,F) -> ((x,y) -> ded(R x y) -> ded(tequal(B, F x, F y))) -> tm B
    }

    // A special form of quotient types for type-dependent equality.
    // Because the equality of elements at the quotient type can deviate from the equality at the base type,
    // this formulation allows for the usual mathematical practice of
    // reusing the elements of the base type as elements of the quotient.
    // Thus, (like for predicate subtypes) no computation is needed for projection and lifting - the two functions are just type-casts.
    
    // Maybe surprisingly, the quotient type technically becomes a super-type of the base type:
    // indeed, the projection function preserves typing and equality.
    // In particular, using a larger relation produces larger quotients and
    // - the smallest (= empty) relation yields the smallest quotient, one isomorphic to the base set
    // - the biggest (= universal) relation yields the biggest (terminal) type, i.e., a singleton.
    // This is dual to the properties of predicate subtypes.
    theory SoftTypedQuotients {
        include .base_languages.SoftTypedLogic
        include .equality.SoftTypedEquality
        quotient: tp -> (term -> term -> prop) -> tp
        class: (A, R, x) -> ded (x ∶ A) -> ded (x ∶ quotient A R)
        equiv: (A, R, x, y) -> ded (x ∶ A) -> ded (y ∶ A) -> ded (R x y) -> ded (requal(quotient A R, x, y))
        // ugly without implicit args
        welldefined: ???
    }

    // Set theory-like quotients

    // The theory is intended to be realized in set theory.
    // However, set theory's key conception of a class as a set of equivalent elements
    // is abstracted from and considered an impelmentation detail of set theory
    // (akin to how, e.g., the definition of pairs as Kuratowski pairs is abstracted from).
    // In particular, there are no axioms governing what the elements of a class.
    theory InternallyTypedQuotients {
        include .base_languages.InternallyTypedLogic
        include .equality.UntypedEquality
        // All declarations in this theory take first arguments
        // [A:term,R:term->term->prop] where $A$ is the base set and $R$ is relation to quotient $A$ by.

        // the quotient
        quotient: term -> (term -> term -> prop) -> term
        // the projection function mapping elements to classes in the quotient
        class: term -> (term -> term -> prop) -> term -> term 
        // the lifting function that maps functions out of the base set to a well-defined function out of the quotient
        welldefined: term -> (term -> term -> prop) -> (term -> term) -> term -> term 

        // Contrary to set theory, we do not require that [R:term->term->prop] is an equivalence relation.
        // Instead, we use an additional axiom that makes the kernel of the projection (which is always an equivalence) an extension of $R$.
        // Then, the typing rule of lifting applies to any function whose kernel extends $R$ (and thus extends the equivalence closure of $R$); that ensures that the kernel of the projection is minimal.
        
        // related elements have equal classes 
        equiv: (A,R,x,y) -> ded (R x y) -> ded ((class A R x) ≐ (class A R y))
        // the typing rule for the projection: The projection of an element of the base set is in the quotient.
        quotientI: (A,R,x) -> ded (x⋵A) -> ded ((class A R x) ⋵ (quotient A R))
        // the typing rule for the lifting: Given [A:term,R:term->term->prop,B:term,F:term->term] if $F$ is a function from $A$ to $B$ that preserves $R$, then its lifting is the function from $A⧸R$ to $B$ defined by $F$.
        quotientE : (A,R,B,F) -> (x -> ded (x⋵A) -> ded (F x ⋵ B)) -> ((x,y) -> ded (x⋵A) -> ded (y⋵A) -> ded (R x y) -> ded (F x ≐ F y)) -> (x) -> ded (x ⋵ quotient A R) -> ded (welldefined A R F x ≐ F x)
    }
}