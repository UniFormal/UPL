module Basics005 {

  mutivar(v:bool, w,x,y:::int, z:bool) = w+x+y // Three colons => w,x and y have type int.
  mutivar2(v,x,y::int) = mutivar(v,x,x,x,v) // Two colons => x and y have type int; the type of v is inferred separately.
  // That also works if the types are omitted:
  mutivar3(v,x,y::_) = mutivar(v,x,y,x,v)

}