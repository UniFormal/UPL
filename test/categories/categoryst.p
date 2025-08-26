module CatST {

    // alternative formalization that uses only simple types
    theory CategoryST {
        type object
        type morphism
        domain: morphism -> object
        codomain: morphism -> object

        fromTo = (f,a,b) -> domain(f) == a & codomain(f) == b
        composable = (f,g) -> codomain(f) == domain(g)

        id: object -> morphism
        id_fromto: |- forall a. fromTo(id(a),a,a)

        // this must be a partial function, compose(f,g) is defined only if composable(f,g)
        compose: (morphism,morphism) -> morphism
        compose_fromto: |- forall f,g. composable(f,g) => fromTo(compose(f,g), domain(f), codomain(g))

        // optionally: we make composition formally a total function by assigning an arbitrary result
        // alternatively, wihtout this axiom, the composition of non-composable morphisms is simply unspecified
        compose_total: |- forall f,g. !composable(f,g) => compose(f,g) == f

        neutLeft:  |- forall a,f. domain(f) == a => compose(id(a), f) == f
        neutRight: |- forall a,f. codomain(f) == a => compose(f,id(a)) == f
        assoc: |- forall f,g,h. composable(f,g) & composable(g,h) => compose(compose(f,g), h) == compose(f, compose(g,h))
    }

    singletonCat = CategoryST {
        type object = int
        singleton_object: object = 0
        singleton_morphism: morphism = id(singleton_object)
        domain = x -> singleton_object
        codomain = x -> singleton_object
        id = a -> singleton_morphism
        //compose = (f,g) -> singleton_morphism
        //neutLeft = ???
        //neutRight = ???
        //assoc = ???
    }

    test = {
        1 == 1
    }

}