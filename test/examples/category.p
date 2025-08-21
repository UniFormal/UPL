module Cat {

    theory Category {
        // A category consists of objects and morphisms (arrows) between them.
        type object
        type morphism = (object, object)

        // 1. identity: every object has an identity morphism
        // declare id as subtype of morphism?
        is_id_morphism: morphism -> bool = m -> {
            m match {
                (obj1, obj2) -> obj1 == obj2
            }
        }
        is_source: morphism -> object -> bool = m -> o -> {
            m match {
                (src, tgt) -> src == o
            }
        }
        // in a category, every object has an identity morphism
        identity: |- forall o: object. exists m: morphism. is_source(m)(o) & is_id_morphism(m)

        // 2. composition: morphisms compose
        // composition operator
        op: (morphism, morphism) -> morphism = (m1, m2) -> {
            // m1 and m2 must be compatible, i.e., the target of m1 must match the source of m2
            (m1, m2) match {
                ((src1, tgt1), (src2, tgt2)) -> (src1, tgt2)
            }
        }

        // category is closed under composition: the composition of two morphisms must exists
        comp: |- forall m1, m2: morphism. exists m3: morphism. m3 == op(m1, m2)

        // identity morphism is a neutral element for composition

        // 3. composition is associative
        assoc: |- forall x,y,z: morphism. op(op(x,y),z) == op(x,op(y,z))
    }

    unitCat = Category {
        type object = ()
        identity = |- forall o: object. exists m: morphism. is_source(m)(o) & is_id_morphism(m)
        comp = |- forall m1, m2: morphism. exists m3: morphism. m3 == op(m1, m2)
        assoc = |- forall x, y, z: morphism. op(op(x, y), z) == op(x, op(y, z))
    }

    test = {
        obj = ()
        id1 = (obj, obj) // identity morphism for unitCat
        obj2 = unitCat.object
        id2 = unitCat.morphism
        Cat.is_id_morphism(id1) &&
        (obj2, obj2) == id2
    }


}