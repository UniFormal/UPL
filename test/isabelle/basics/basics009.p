module Basics009 {

    // Equality == and inequality != are polymorphic and can be used for every type.
    // Evaluation is attempted but may fail if equality is undecidable.
    returns_true = ((x:int) -> x) == ((x:int) -> x) // reflexivity of == always succeeds
    would_fail = () -> ((x:int) -> x+1) == ((x:int) -> x)



}