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
        // alternatively, without this axiom, the composition of non-composable morphisms is simply unspecified
        compose_total: |- forall f,g. !composable(f,g) => compose(f,g) == f

        neutLeft:  |- forall a,f. domain(f) == a => compose(id(a), f) == f
        neutRight: |- forall a,f. codomain(f) == a => compose(f,id(a)) == f
        // may omit composable(g,h), because compose(compose(f,g), h) == compose(f,g) == compose(f, compose(g,h))
        assoc: |- forall f,g,h. composable(f,g) & composable(g,h) => compose(compose(f,g), h) == compose(f, compose(g,h))
    }

    // hom-set function
    // locally small categories: morphism between two objects form a set
    // hom-set: Category -> (object, object) -> set[morphism]

    //emptyCat = CategoryST {
        //type object = Null
        //type morphism = Nothing
        // no possibility of calling functions because there are no objects and morphisms
        //domain = x -> ()
        //codomain = x -> ()
        //id = x -> ()
        //id_fromto = ???
        //compose = (f,g) -> ()
        //compose_total = ???
        //compose_fromto = ???
        //neutLeft = ???
        //neutRight = ???
        //assoc = ???
    //}

    // Monoid as Category is a single-object category
    theory Monoid {
        include CategoryST
        type object = ()
    }

    // singletonCat can become a Monoid
    // singletonCat = Monoid {
    singletonCat = CategoryST {
        type object = ()
        type morphism = ()
        singleton_object: object = ()
        singleton_morphism: morphism = ()
        domain = x -> singleton_object
        codomain = x -> singleton_object
        id = x -> singleton_morphism
        id_fromto = ???
        compose = (f,g) -> singleton_morphism
        compose_total = ???
        compose_fromto = ???
        neutLeft = ???
        neutRight = ???
        assoc = ???
    }

    singletonCatAsMonoid = Monoid {
        type morphism = ()
        singleton_object: object = ()
        singleton_morphism: morphism = ()
        domain = x -> singleton_object
        codomain = x -> singleton_object
        id = x -> singleton_morphism
        id_fromto = ???
        compose = (f,g) -> singleton_morphism
        compose_total = ???
        compose_fromto = ???
        neutLeft = ???
        neutRight = ???
        assoc = ???
    }

    // Nat with add1 und add0

    // Monoid


    test = {
        val obj = singletonCat.singleton_object
        val mpm = singletonCat.singleton_morphism
        obj == () & mpm == ()
    }

}