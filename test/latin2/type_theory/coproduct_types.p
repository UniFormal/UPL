module coproduct_types {
    theory CoproductTypes {
        include .concepts.Types
        coprod: tp -> tp -> tp
    }

    theory Coproducts {
        include CoproductTypes
        include .equality.TypedEqualityND

        inj1: (A,B) -> tm A -> tm (coprod A B)
        inj2: (A,B) -> tm B -> tm (coprod A B)
        cases: (A,B,C) -> tm (coprod A B) -> (tm A -> tm C) -> (tm B -> tm C) ->  tm C

        compute1: (A,B,C,a,f,g) -> ded tequal(C, cases(A,B,C) (inj1(A,B) a) f g, f a)
        compute2: (A,B,C,b,f,g) -> ded tequal(C, cases(A,B,C) (inj2(A,B) b) f g, g b)
    }

    theory CoproductsExpand {
        include Coproducts
        expand: (A,B,c) -> ded tequal(coprod A B, cases(A,B,coprod A B) c (a -> inj1(A,B) a) (b -> inj2(A,B) b), c)
    }

    theory CoproductsExtensionality {
        include Coproducts
        extensionality: (A,B,C,u,v) -> ((f,g) -> ded tequal(C, cases(A,B,C) u f g, cases(A,B,C) v f g)) -> ded tequal(coprod A B, u, v)
    }
}