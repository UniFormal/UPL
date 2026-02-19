theory Test103
  imports Main
begin

locale partial_order =
  fixes le :: "a => a => bool"
  assumes refl: le x x
  assumes anti_sym: ((le x y \<and> le y x) \<longrightarrow> (x = y))
  assumes trans: ((le x y \<and> le y z) \<longrightarrow> le x z)


locale total_order =
  partial_order +
  assumes total: (le x y \<or> le y x)



end