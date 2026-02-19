theory Test050
  imports Complex_Main
begin

definition a :: "bool" where
  "a = (True \<and> False)"
definition b :: "bool" where
  "b = (True \<or> False)"
definition c :: "bool" where
  "c = (\<not> False)"
definition d :: "bool" where
  "d = (False \<longrightarrow> True)"
definition e :: "int" where
  "e = (1 + 2)"
definition f :: "int" where
  "f = (1 - 2)"
definition g :: "int" where
  "g = (21 * 2)"
definition h :: "rat" where
  "h = (21 / 2)"
definition i :: "int" where
  "i = (min 10 (- 10))"
definition j :: "int" where
  "j = (max 10 (- 10))"
definition k :: "complex" where
  "k = (2 ^ 3)"
definition l :: "int" where
  "l = (- (- (- 10)))"
definition m :: "bool" where
  "m = (1 < 2)"
definition n :: "bool" where
  "n = (1 \<le> 2)"
definition oo :: "bool" where
  "oo = (1 > 2)"
definition p :: "bool" where
  "p = (1 \<ge> 2)"
definition q :: "int list" where
  "q = [1,2,3,4,5]"
definition r :: "int list" where
  "r = (q @ q)"
definition s :: "bool" where
  "s = (1 \<in> {1,2,3,4,5})"
definition t :: "int list" where
  "t = (0 # q)"
definition u :: "int list" where
  "u = (q @ 6)"
definition v :: "bool" where
  "v = (0 = 1)"
definition w :: "bool" where
  "w = (0 \<noteq> 1)"

end