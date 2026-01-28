
theory Test5_target
  imports Main
begin


locale partial_order =
  fixes le :: "'a \<Rightarrow> 'a \<Rightarrow> bool" (infixl \<open>\<sqsubseteq>\<close> 50)
  assumes refl [intro, simp]: "x \<sqsubseteq> x"
    and anti_sym [intro]: "\<lbrakk> x \<sqsubseteq> y; y \<sqsubseteq> x \<rbrakk> \<Longrightarrow> x = y"
    and trans [trans]: "\<lbrakk> x \<sqsubseteq> y; y \<sqsubseteq> z \<rbrakk> \<Longrightarrow> x \<sqsubseteq> z"

locale partial_order2 =
  fixes le :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
  assumes refl [intro, simp]: "le x x"
  assumes anti_sym [intro]: "\<lbrakk> le x y; le y x \<rbrakk> \<Longrightarrow> x = y"
    and trans [trans]: "\<lbrakk> le x y; le y z \<rbrakk> \<Longrightarrow> le x z"

end