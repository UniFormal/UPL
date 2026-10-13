module product_types {
    theory SimpleProductTypes {
        include .concepts.Types
        simpprod: tp -> tp -> tp
    }

    theory DependentProductTypes {
        include .concepts.TypedTerms
        depprod: A -> (tm A -> tp) -> tp

        // maybe do a total structure
        realize SimpleProductTypes
        simpprod = A -> B -> depprod A (x -> B)
    }

    theory SoftDependentProductTypes {
        include .concepts.SoftTypedTerms
        softprod: tp -> (term -> tp) -> tp
    }

    theory SimpleProducts {
        include SimpleProductTypes
        include .equality.TypedEqualityND

        simppair: (A,B) -> (tm A, tm B) -> tm (simpprod A B)
        simppi1: (A,B) -> tm (simpprod A B) -> tm A
        simppi2: (A,B) -> tm (simpprod A B) -> tm B

        compute1: (A,B,a,b) -> ded tequal(A, simppi1(A,B) (simppair(A,B) (a,b)), a)
        compute2: (A,B,a,b) -> ded tequal(B, simppi2(A,B) (simppair(A,B) (a,b)), b)
    }

    theory DependentProducts {
        include DependentProductTypes
        include .equality.TypedEquality
        include .type_equality.DependentTypeEquality 

        // maybe ascribe these dᵗ, but this would look pretty bad
        deppair: (A,B,a) -> (tm (B a)) -> tm (depprod A B)
        deppi1: (A,B) -> tm (depprod A B) -> tm A
        deppi2: (A,B,u) -> tm (B (deppi1(A,B) u))

        compute1: (A,B,a,b) -> ded tequal(A, deppi1(A,B) (deppair(A,B,a) (b)), a)
        // ugly without implicit args
        compute2: ???
    }

    theory SoftTypedProducts {
        include .concepts.Terms
        include .equality.UntypedEquality

        pair: term -> term -> term
        pi1: term -> term
        pi2: term -> term

        compute1: (a,b) -> ded (pi1(pair a b) ≐ a)
        compute2: (a,b) -> ded (pi2(pair a b) ≐ b)
    }

    theory SoftTypedSimpleProducts {
        include .concepts.SoftTypedTerms
        include SoftTypedProducts
        include SimpleProductTypes

        fun_typing: (A,B,a,b) -> ded(a ∶ A) -> ded(b ∶ B) -> ded(pair a b ∶ simpprod A B)
    }

    theory SoftTypedDependentProducts {
        include .concepts.SoftTypedTerms
        include SoftTypedProducts
        include SoftDependentProductTypes

        fun_typing: (A,B,a,b) -> ded(a ∶ A) -> ded(b ∶ B a) -> ded(pair a b ∶ softprod A B)
    }

    theory SimpleProductsExpand {
        include SimpleProducts
        expand: (A,B,u) -> ded tequal(simpprod A B, simppair(A,B) (simppi1(A,B) u, simppi2(A,B) u), u)
    }

    theory DependentProductsExpand {
        include DependentProducts
        expand: (A,B,u) -> ded tequal(depprod A B, deppair(A,B,deppi1(A,B) u) (deppi2(A,B,u)), u)
    }

    theory SoftTypedProductsExpand {
        include SoftTypedProducts
        expand: (u) -> ded (u ≐ (pair (pi1 u) (pi2 u)))
    }

    theory SimpleProductsExtensionality {
        include SimpleProducts
        exten: (A,B,u,v) -> ded tequal(A, simppi1(A,B) u, simppi1(A,B) v) -> ded tequal(B, simppi2(A,B) u, simppi2(A,B) v) -> ded tequal(simpprod A B, u, v)
    }

    theory DependentProductsExtensionality {
        include DependentProducts
        // ugly without implicit args
        exten: ???
    }

    theory SoftTypedProductsExtensionality {
        include SoftTypedProducts
        exten: (u,v) -> ded (pi1 u ≐ pi1 v) -> ded (pi2 u ≐ pi2 v) -> ded (u ≐ v)
    }
}