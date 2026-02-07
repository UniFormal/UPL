theory Test021_target
  imports Main
begin

definition l1 :: "int list" where "l1 = [1, 2, 2, 3]"
definition l2 :: "int list" where "l2 = 0 # l1"        (* Cons: prepends 0 *)
definition l3 :: "int list" where "l3 = l1 @ [4, 5]"   (* Append *)
definition l4 :: "int list" where "l4 = replicate 3 1" (* [1, 1, 1] *)

end