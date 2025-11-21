module CatST {

    // formalization that uses only simple types
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

    emptyCat = CategoryST {
        type object = empty
        type morphism = empty
        // no possibility of calling functions because there are no objects and morphisms
        domain = x -> x
        codomain = x -> x
        id = x -> x
        id_fromto = ???
        compose = (f,g) -> f
        compose_total = ???
        compose_fromto = ???
        neutLeft = ???
        neutRight = ???
        assoc = ???
    }

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

    // Discrete Categories
    theory DiscreteCategory {
        include CategoryST
        // only identity morphisms
        id_only: |- forall a,f. fromTo(f,a,a)
    }

    singletonCatAsDiscrete = DiscreteCategory {
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
        id_only = ???
    }

    twoObjDiscrete = DiscreteCategory {
         type object = int[0;2]
         type morphism = int[0;2]
         obj1: object = 0
         obj2: object = 1
         id1: morphism = 0
         id2: morphism = 1
         domain = x -> x
         codomain = x -> x
         id = x -> x
         id_fromto = ???
         compose = (f,g) -> f
         compose_total = ???
         compose_fromto = ???
         neutLeft = ???
         neutRight = ???
         assoc = ???
         id_only = ???
                         }

    // Two simple example categories
    // 1. category with two objects and a single morphism between them

    // 2. category with four objects, commuting square with extra diagonal morphism

    // category of sets and functions
    theory CatSet {
        type X
        type object = set[X]
    }

    singletonCatSetInt = CatSet {
        type X = int
        type morphism = ()
        singleton_object: object = []
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
        id_only = ???
    }

    // think about: category of groups and group homomorphisms Grp


    // Monoid
    // Monoid as Category is a single-object category
    theory Monoid {
        include CategoryST
        type object = ()
    }

    // singletonCat can become a Monoid
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

    // a small one-object category with only isomorphisms is a group
    theory Group {
        include Monoid
        only_isos: |- forall f. exists g. compose(f,g) == id(domain(f))
    }

    // singleton group
    singletonGroup = Group {
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
        only_isos = ???
    }



    test = {
        val obj = singletonCat.singleton_object
        val mpm = singletonCat.singleton_morphism
        obj == () & mpm == ()
    }

}