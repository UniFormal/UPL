module monadic_function_types {
  theory PurityLambdaCalculus {
      include .equality.TypedEquality
      include .function_types.SimpleFunctionTypes
      include .undefinedness.UndefinedTypedTerms
  }

  // there could now be a view LambdaCalculus -> PurityLambdaCalculus+Monad

  theory MonadicLambdaCalculus {
      include .function_types.SimpleFunctions
      include .function_types.SimpleFunctionsEta
      include .monads.Monad
  }
}
