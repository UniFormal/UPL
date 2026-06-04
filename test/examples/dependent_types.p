// test file for quotation
module DepTypes {
  theory STT {
    type tp
    type tm(a: tp)
    fun: (tp,tp) -> tp # infix →
    lam: (a,b) -> (tm a -> tm b) -> tm(a→b)
    app: (a,b) -> tm (a→b) -> tm a -> tm b
    beta: (a,b,T,X) -> |- app(a,b) (lam(a,b) T) X == (T X)
    eta: (a,b,f) -> |- lam(a,b) (x -> app(a,b) f x) == f
  }

  theory Vectors {
    type vec@a(n: nat)
    empty@a: vec@a 0
    single@a: a -> vec@a 1
    concat@a: (m,n) -> (vec@a m, vec@a n) -> vec@a (m+n)

    nat1: nat = 1 // workaround to avoid inferring 1 as an integer in 1+n below
    cons@a: n -> (a, vec@a n) -> vec@a (nat1+n) = n -> (x,v) -> concat(1,n)(single x, v)
  }
}