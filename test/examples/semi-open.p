// modules may include theories (semi-open worlds)

module Effects {
  // effectful operations can be formalized as theories
  theory IO {
    print: string -> ()
    read:  () -> string
  }
}

module EffectsExample {
  include .Effects.IO // current module includes a theory; prog can only be accessed from places where IO is available
  prog = {print("Hello World")}
}

module HandledEffectsExample {
  notAllowed = EffectsExample.prog  // not allowed because IO is not included
  theory h {
    include .Effects.IO
    allowed = EffectsExample.prog   // allowed because IO is included
  }

  handler : .Effects.IO = ???            // some handler of effects
  allowed = handler{EffectsExample.prog} // projection out of handler, allowed because IO is available in handler 
}

module ConservativeExtensionExample {
  // some theory
  theory Magma {
    type univ
    op: (univ,univ) -> univ
  }
}

module ConservativeExtensionExample2 {
  // conservatively extended as a semi-open module
  module Squaring {
    include .ConservativeExtensionExample.Magma
    square = x -> op(x,x)
  }
}

module ConservativeExtensionExample3 {
  // some model
  m = .ConservativeExtensionExample.Magma {type univ = int, op = (x,y) -> x*y}
  
  // conservative extensions can be pulled in from anywhere
  test = m{ConservativeExtensionExample2.Squaring.square}(3)  // returns 9
  
  // note: no name clash if multiple conservative extensions add the same name
  // because the added names are accessed as qualified names
}