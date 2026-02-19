theory Test101
  imports Main
begin

locale Partial_order =
  fixes le :: "'a => 'a => bool"
  assumes refl: "le x x"
  assumes antisym: "((le x y \<and> le y x) \<longrightarrow> x = y)"
  assumes trans: "((le x y \<and> le y z) \<longrightarrow> le x z)"




end