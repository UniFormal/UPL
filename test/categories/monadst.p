module MonST {

    // make use of theory EndofunctorST from functorst.p
    import test.categories.categoryst
    import test.categories.functorst

    theory MonadST {
        // A monad is a special kind of endofunctor with additional structure.
        include EndofunctorST
        // Monad has a unit operation that maps an object to a morphism.
        type unit: C.object -> C.morphism
        // Monad has a bind operation that maps a morphism to a morphism.
        type bind: C.morphism -> C.morphism
        // Monad preserves identity morphisms.
        forall x: C.object. bind(unit(x)) == C.id(x)
        // Monad preserves composition of morphisms.
        forall m1, m2: C.morphism. bind(op(m1, m2)) == op(bind(m1), bind(m2))
    }
}