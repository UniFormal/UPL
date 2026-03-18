theory Test025_target
  imports Main
begin

definition l1 :: "int list" where 
  "l1 = [1, 2, 3]"

(* You don't put 'distinct' in the definition; you prove it as a lemma *)
lemma l1_distinct: "distinct l1"
  by (simp add: l1_def)

end