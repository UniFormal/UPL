module stfol {
	// AS: maybe this needs some extra notation
    theory SoftTypedDefinedFOL {
        // include .concepts.InternalTypes
        include .base_languages.SoftTypedLogic
        include .pl.Conjunction
        include .pl.Negation
        include .pl.Truth
        include .pl.Falsity
        include .equality.UntypedEquality
        include .fol.UniversalQuantification

        or: (prop, prop) -> prop # infix ∨ = (a,b) -> ¬ (¬ a ∧ ¬ b) 
        implies: (prop, prop) -> prop # infix ⇒ = (a,b) -> ¬ (a ∧ (¬ b)) 
        iff: (prop, prop) -> prop # infix ⇔ = (a,b) -> (a ⇒ b) ∧ (b ⇒ a)  	
        exists: (term -> prop) -> prop # bindfix ∃ = (p) -> ¬ (∀ᵘ ((x) -> (¬ (p x))))  
        existsUnique: (term -> prop) -> prop  = (pred) -> (∃ pred) ∧ (∀ᵘ ((x:term) -> ∀ᵘ ((y:term) -> (pred x ⇒ pred y ⇒ (x ≐ y))))) 
        forST: (A:tp, p: term -> prop) -> prop = (A, p) -> ∀ᵘ ((x) -> x ∶ A ⇒ p x) 
        ex: (A:tp, p: term -> prop) -> prop = (A, p) -> ∃ ((x) -> (x ∶ A) ∧ (p x)) 
    }

    theory SoftTypedFOL {
        include .base_languages.SoftTypedLogic 
        include .fol.IFOLEQ 
        include .fol.UniqueExistentialQuantification 
        include .fol.RelativizedExistentialQuantification 
        include .fol.RelativizedUniversalQuantification 
    }

    // MizarView: SoftTypedDefinedFOL -> SoftTypedFOL = s -> SoftTypedFOL {
    //     include .base_languages.SoftTypedLogic 
    //     include .pl.Conjunction 
    //     include .pl.Negation 
    //     include .pl.Truth 
    //     include .pl.Falsity 
    //     include .equality.UntypedEquality 
    //     include .fol.UniversalQuantification 

    //     or = s.or 
    //     impl = s.implies 
    //     equiv = s.iff 
    //     uexists = s.exists 
    //     uexistsUnique = s.existsUnique 
    //     rforall  = s.forST 
    //     rexists = s.ex 
    // }
}