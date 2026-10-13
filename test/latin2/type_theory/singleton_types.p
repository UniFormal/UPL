module singleton_types {
    theory SingletonTypes {
        include .equality.TypedEqualityND
        singletonType : (A) -> tm A -> tp
        singletonIntro: (A,x) -> tm (singletonType A x)
        singletonElim: (A,x) -> tm (singletonType A x) -> tm A
        
        singleton_compute : (A,x,e) -> ded tequal(A, singletonElim(A,x) e, x)
        singleton_expand  : (A,x,e) -> ded tequal(singletonType A x, e, singletonIntro(A,x))
        singleton_exten   : (A,x,e,f) -> ded tequal(singletonType A x, e, f)
    }
}