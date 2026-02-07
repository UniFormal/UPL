theory Test1_target
  imports Main
begin

definition "a = true \<and> false"
definition "b = true \<or> false"
definition "c = \<not> false"
definition "d = false \<longrightarrow> true"
definition "c = 1 < 2"
definition "d = 1 \<le> 2"
definition "n = 1 + 2"

end