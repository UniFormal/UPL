module FunST {

    // make use of theory CategoryST from categoryst.p
    import test.categories.categoryst
    
    theory FunctorST {
        // A functor is a mapping between categories.
        // It maps objects to objects and morphisms to morphisms.
        // preserves structure, i.e., identity morphisms and composition of morphisms.
        
        include CategoryST

        // Map category C to category D.
        // C = CategoryST {} 
        // D = CategoryST {}
        type Category
        C: Category
        D: Category
        
        // Functor maps objects of C to objects of D.
        // object a in C is mapped to Fa in D.
        Functor_objects: Category -> Category
        // Functor maps morphisms of C to morphisms of D.
        // morphism f:a->b in C is mapped to Ff:Fa->Fb in D.
        Functor_morphisms: Category -> Category

        // Functor preserves identity morphisms.
        // F id_a == id_Fa
        forall a: C.object. Functor_morphisms(C.id(a)) == D.id(Functor_objects(a))
        // Functor preserves composition of morphisms.
        // if f:a->b, g:b->c then F (g . f) == F g . F f
        forall m1, m2: C.morphism. composable(m1, m2) =>
                Functor_morphisms(compose(m1, m2)) == compose(Functor_morphisms(m1), Functor_morphisms(m2))
    }

    theory EndofunctorST {
        // An endofunctor is a functor from a category to itself.
        include FunctorST
        // The source and target category are the same.
        C == D
    }

}