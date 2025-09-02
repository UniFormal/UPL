module Cat {

    theory Type {
       type univ
    }

    theory Category {
        // A category consists of objects and morphisms (arrows) between them.
        type object
        // This would be something "type morphism(object,object)" if UPL supported dependent base types
        morphism: (object, object) -> Type

        // total function, every object must have an identity morphism
        id: (a:object) -> morphism(a,a)
        // composition operator, every composable pair of morphism yields a new morphism - their composition
        // the three objects seem redundant, I don't know if there is a way to eliminate them
        // for example similar to scala generics/generic types/type parameters:
        // op[a:object,b:object,c:object]: (f: morphism(a,b), g:morphism(b,c)) -> morphism(a,c)
        op: (a:object,b:object,c:object, f: morphism(a,b), g:morphism(b,c)) -> morphism(a,c)

        // algebraic laws of a category: identity is the neutral element and associativity of composition
        neutLeft:  |- forall a,b, f: morphism(a,b). op(a,a,b,id(a), f) == f
        neutRight: |- forall a,b, f: morphism(a,b). op(a,b,b,f,id(b)) == f
        assoc: |- forall a,b,c,d, f: morphism(a,b), g: morphism(b,c), h: morphism(c,d). op(a,b,d,f,op(b,c,d,g,h)) == op(a,c,d,op(a,b,c,f,g), h)
    }

    unitCat = Category {
        type object = ()
        morphism = (a,b) -> Type {univ = ()}
        identity = a -> ()
        op = (a,b,c,f,g) -> ()

        neutLeft = ???
        neutRight = ???
        assoc = ???
    }

    test = {
        unitCat.op((),(),(),(),()) == ()
    }




}