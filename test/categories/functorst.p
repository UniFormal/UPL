module FunST {

    // make use of theory CategoryST from categoryst.p
    import test.categories.categoryst
    
    theory FunctorST {
        // A functor is a mapping between categories.
        // It maps objects to objects and morphisms to morphisms.
        // preservation of structure, i.e., identity morphisms and composition of morphisms.
        
        include CategoryST

        // Map category C to category D.
        // C = CategoryST {} 
        // D = CategoryST {}
        type Category
        C: Category
        D: Category
        
        // Functor maps objects of C to objects of D.
        Functor_objects: Category -> Category
        // Functor maps morphisms of C to morphisms of D.
        Functor_morphisms: Category -> Category

        // Functor preserves identity morphisms.
        forall x: C.object. Functor_morphisms(C.id(x)) == D.id(Functor_objects(x))
        // Functor preserves composition of morphisms.
        forall m1, m2: C.morphism. Functor_morphisms(op(m1, m2)) == op(Functor_morphisms(m1), Functor_morphisms(m2))
    }

    theory EndofunctorST {
        // An endofunctor is a functor from a category to itself.
        include FunctorST
        // The source and target category are the same.
        C == D
    }

}