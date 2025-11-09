module Monad {

    theory Monad {

        M: Type -> Type  // means M is a type constructor with one type argument, of kind * -> *

        return: (A:Type) -> A -> M(A) // but want this for all types including B, not just A

        bind: (A:Type,B:Type) -> M(A) -> (A -> M(B)) -> M(B)

    }

    OptionMonad = Monad {
        realize Monad
        // X is an arbitrary type
        // type M[X] = Option[X]
        // scala sometimes does underscore magic
        M = X -> option[X]

        // do = ...

        return: int -> option[int] = (x: int) -> [x]

        bind: option[int] -> (x:int -> option[_]) -> option[_]
    }

    theory OptionMonad {
      realize Monad
      type M[X] = ...
      do = ...
      return = ...
    }

    IntOptionMonad = OptionMonad {
        type X = int

        return: int -> option[int] = (x: int) -> [x]

        bind: option[int] -> (x:int -> option[_]) -> option[_]
    }
}