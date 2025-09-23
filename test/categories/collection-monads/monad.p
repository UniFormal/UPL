module Monad {

    theory Monad {

        type A
        type B
        type M[_]  // means M is a type constructor with one type argument, of kind * -> *

        return: A -> M[A] // but want this for all types including B, not just A

        bind: M[A] -> (A -> M[B]) -> M[B]

    }

    OptionMonad = Monad {

        // X is an arbitrary type
        // type M[X] = Option[X]
        // scala sometimes does underscore magic
        type M[_] = option[_]

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