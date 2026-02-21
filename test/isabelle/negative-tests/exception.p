module Exception {


   // Exceptions are declared by creating functions that return exn.
   // This is one of the cases where definition-less declarations in a module make sense.
   error: string -> exn
   divide = (x:int,y:int) -> {
     if (y==0) throw error("second argument must be non-zero")
     x/y
   } catch {
     error(_) -> 0
   }

}