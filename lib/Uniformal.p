// the uniformal namespace contains all built in functions. Every file has direct access to it.
module Uniformal {
  // mprints the string to stdout
  print: string -> ()
  read: () -> string

  type int_64 = int
  
  addi: (int,int) -> int
  addf: (float,float) -> float
  
  module Lists {
    type LL@e = list[e]
    empty@e: LL@e = []
    head@e: LL@e -> e = l -> l(0)
    
    type Array@e(initCap: nat) = list[e]
    
  }  
}
