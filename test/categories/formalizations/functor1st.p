module FunST {
    theory FunctorST {
        // A functor is a mapping between categories.
        // It maps objects to objects and morphisms to morphisms.
        // preserves structure, i.e., identity morphisms and composition of morphisms.
        
        C: CatST.CategoryST
        D: CatST.CategoryST
        
        // Functor maps objects of C to objects of D.
        // object a in C is mapped to Fa in D.
        Fo: C.object -> D.object

        // Functor maps morphisms of C to morphisms of D.
        // morphism f:a->b in C is mapped to Ff:Fa->Fb in D.
        Fm: C.morphism -> D.morphism

        // fromto
        fromto_axiom: |- forall f,a,b. C.fromTo(f,a,b) => D.fromTo(Fm(f),Fo(a),Fo(b))


        // Functor preserves identity morphisms.
        // F id_a == id_Fa
        law1: |- forall a. Fm(C.id(a)) == D.id(Fo(a))

        // Functor preserves composition of morphisms.
        // if f:a->b, g:b->c then F (g . f) == F g . F f
        law2: |- forall m1, m2. C.composable(m1, m2) =>
                Fm(C.compose(m1, m2)) == D.compose(Fm(m1), Fm(m2))
    }

    theory EndofunctorST {
        // An endofunctor is a functor from a category to itself.
        include FunctorST
        // The source and target category are the same.
        D = C // def better than axiom
    }

}