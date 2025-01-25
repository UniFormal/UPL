module Numbers {
  theory Nat {
    type num
    z: num
    s: num -> num
    o = s(z)
    plus: (num,num) -> num
    plus_z: |- forall x. plus(x,z)==x
    plus_s: |- forall x,n. plus(x,s(n))== s(plus(x,n))
    times: (num,num) -> num
    times_z: |- forall x. times(x,z)==z
    times_s: |- forall x,n. times(x,s(n))== plus(times(x,n), x)
    square = x -> times(x,x)
  }
  theory Int {
    include Nat
    p: num -> num
    ps: |- forall x. p(s(x)) == x
    sp: |- forall x. s(p(x)) == x

    plus_p: |- forall x,n. plus(x,p(n)) == p(plus(x,n))

    uminus: num -> num
    uminus_z: |- uminus(z) == z
    uminus_s: |- forall n. uminus(s(n)) == p(uminus(n))
    uminus_p: |- forall n. uminus(p(n)) == s(uminus(n))
    minus = (x,y) -> plus(x,uminus(y))

    times_p: |- forall x,n. times(x,s(n)) == minus(times(x,n), x)
  }
  theory Rat {
    include Int
    frac: (num,num) -> num
    inv = x -> frac(o,x)

    int_embed: |- forall x. frac(x,o) == x
    frac_zero: |- forall x. frac(z,x) == z

    cancel: |- forall xe,xd,ye,yd. (frac(xe,xd) == frac(ye,yd)) == (times(xe,yd) == times(ye,xd))

    succ_frac:        |- forall e,d.   s(frac(e,d))       == frac(plus(e,d),d)
    pred_frac:        |- forall e,d.   p(frac(e,d))       == frac(minus(e,d),d)
    plus_frac_left:   |- forall e,d,x. plus(frac(e,d),x)  == frac(plus(e,times(d,x)),d)
    plus_frac_right:  |- forall e,d,x. plus(x,frac(e,d))  == frac(plus(times(x,d),e),d)
    uminus_frac:      |- forall e,d.   uminus(frac(e,d))  == frac(uminus(e),d)
    times_frac_left:  |- forall e,d,x. times(frac(e,d),x) == frac(times(e,x),d)
    times_frac_right: |- forall e,d,x. times(x,frac(e,d)) == frac(times(x,e),d)
    frac_frac_left:   |- forall e,d,x. frac(x,frac(e,d))  == frac(times(x,d),e)
    frac_frac_right:  |- forall e,d,x. frac(frac(e,d),x)  == frac(e,times(d,x))
  }
  theory Complex {
    include Rat

    comp: (num,num) -> num

    rat_embed: |- forall r. comp(r,z) == r

    succ_comp:        |- forall r,i.   s(comp(r,i)) == comp(s(r),i)
    pred_comp:        |- forall r,i.   p(comp(r,i)) == comp(p(r),i)
    plus_comp_left:   |- forall r,i,x. plus(comp(r,i),x)  == comp(plus(r,x),i)
    plus_comp_right:  |- forall r,i,x. plus(x,comp(r,i))  == comp(plus(x,r),i)
    uminus_comp:      |- forall r,i.   uminus(comp(r,i))  == comp(uminus(r),uminus(i))
    times_comp_left:  |- forall r,i,x. times(comp(r,i),x) == comp(times(r,x),times(i,x))
    times_comp_right: |- forall r,i,x. times(x,comp(r,i)) == comp(times(x,r),times(x,i))
    frac_comp_left:   |- forall r,i,x. frac(x,comp(r,i))  == frac(times(x,comp(r,uminus(i))), minus(square(r),square(i)))
    frac_comp_right:  |- forall r,i,x. frac(comp(r,i),x)  == comp(frac(r,x),frac(i,x))
    comp_comp_left:   |- forall r,i,x. comp(comp(r,i),x)  == comp(r,plus(i,x))
    comp_comp_right:  |- forall r,i,x. comp(x,comp(r,i))  == comp(minus(x,i),r)

    conj: num -> num
    conj_comp: |- forall r,i. conj(comp(r,i)) == comp(r,uminus(i))
  }
}