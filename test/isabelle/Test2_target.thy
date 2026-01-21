theory Test2_target
  imports Main
begin

fun id1 :: "int \<Rightarrow> int" where
"id1 x = x"

fun id2 :: "int \<Rightarrow> int" where
"id2 = \<lambda>x. x"

end