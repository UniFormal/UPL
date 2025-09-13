module NaturalTransformation {

    theory NatTransST {
        //Given categories C,D and functors F,G from C to D, a natural transformations is a family of morphisms in D

        // Have two functors F and G, which must be defined on the same two categories
        F: FunST.FunctorST
        G: FunST.FunctorST {C = F.C, D = F.D}
        // problems of computability, term level definition in type declaration,
        // java generics
        // feld zugriff

        // A natural transformation must associate for every object X in C a morphism nX: F(X) -> G(X) in D
        nX: F.C.object -> G.D.morphism
        fromto_axiom: |- forall x: F.C.object. G.D.fromTo(nX(x), F.Fo(x), G.Fo(x))

        // commutative diagram: For every morphism f:X->Y in C we have G(f) . nX == nY . F(f)
        // naturality_condition: |- forall a,b,f: C.fromTo(f,a,b) => D.compose(nX(a),G.Fm(f)) == D.compose(F.Fm(f),nX(b))
    }




}