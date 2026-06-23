// This file introduces the fundamental concepts of formal languages.

module concepts {
    // base theory for any language that has propositions
    theory Propositions {
        type prop
    }

    // base theory for any language that has proofs of propositions
    theory Proofs {
        include Propositions

        ded: prop -> bool   # prefix ⊦
        type dedT(p: prop)
        
        // which one?
        lemma:--- ⊦F => (⊦F => ⊦G) => ⊦G
        // lemma: F -> G -> dedT F -> (dedT F -> dedT G) -> dedT G
    }

    // base theory for any logic with a judgment for disprovable propositions
    theory Disproofs {
        include Propositions
        disproof: prop -> bool
    }

    // base theory for any logic, i.e., a language with propositions and proofs
    theory Logic {
        include Propositions
        include Proofs

        inconsistent : bool = forall F. ⊦F 
        inconsistentE:--- inconsistent => forall F. ⊦F

        realize Disproofs
        disproof = F -> (⊦F => inconsistent)
    }

    // base theory for any language that has terms that do not carry a type

    // This includes both the case where there are no types and the case where terms exist independent of their types.
    theory Terms {
        type term
    }

    // base theory for any language that has types, usually in the absence of a universe hierarchy
    theory Types {
        type tp
    }

    // base theory for any language that has type-carrying terms

    // These are also called Church-style, intrinsically typed, or hard-typed.
    // Their key quality is that typing is a function terms to types, i.e.,
    // every term has a unique type that can be inferred from it.
    // This is stricter than soft-typed terms but enables shallow representations of typing function:
    // The typing of the object language is represented via typing of the logical framework. 
    // If the latter is decidable, so must be the former.
    theory TypedTerms {
        include Types
        type tm(a: tp)
    }

    // base theory for any language that has typed terms whose type depends on the environment

    // These are also called Curry-style, extrinsically typed, or soft-typed.
    // Their key quality is that typing is a relation on terms and types, i.e.,
    // terms may have no or multiple types, and type inference may be ambiguous.
    // This is more general than hard-typed terms but requires deep representations:
    // The typing of the object language is represented via inhabitation of the logical framework.
    // The latter is unusually undecidable, which complicates the treatment if the former is decidable.
    theory SoftTypedTerms {
        include Terms
        include Types
        include Propositions

        of: (term, tp) -> prop # infix ∶ 
    }

    // base theory for any language that has kinds, usually in addition to types but in the absence of a universe hierarchy
    theory Kinds {
        type kd
    }

    // base theory for any language that has hard-kinded types
    theory KindedTypes {
        include Kinds
        type tf(k: kd)
        tpk: kd

        realize Types
        type tp = tf(tpk)
    }

    // base theory for any language that has propositions as boolean terms

    // This is a special case of having types and propositions.
    // It eliminates much special treatment of propositions as all
    // - propositions are terms
    // - polymorphic operators are also applicable to the type of propositions
    
    // Extending languages can be soft-typed but are usually hard-typed, most importantly higher-order logic.
    theory Booleans {
        include TypedTerms
        boolean: tp
    }

    theory InternalPropositions {
        include Booleans

        realize Propositions 
        type prop = tm boolean
    }

    // base theory for any language in which soft typing is an emergent feature
    // obtained from unary predicates on terms
    theory TypesAsPredicates {
        include Terms
        include Logic

        typesAsPredicates : SoftTypedTerms {
            type tp = term -> prop
            of = (X, A) -> (A X)
        }
    }

    // base theory for any language that has types as certain terms

    // It eliminates much special treatment of types as
    // - the language is fundamentally untyped
    // - typing is recovered as a derived concept
    
    // Instead of typing, extending languages use a binary relation between terms.
    // The properties of this relation are unspecified, but most extending languages 
    // use an undecidable relation in which all terms can occur on both sides of the relation,
    // most importantly in set theory.
    theory InternalTypes {
        include Terms
        include Propositions

        // Should be included/realized in set theory
        iin: (term, term) -> prop

        realize SoftTypedTerms
        type tp = term
        of = iin
    }
}