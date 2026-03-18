
theory reserved_names_target
  imports Complex_Main
begin

definition bool :: bool where
  "bool = True"

definition int :: int where
  "int = 1"

type_synonym bool = int

definition True :: int where
  "True = 1"

definition if' :: int where
  "if' = 1"

definition let' :: int where
  "let' = 1"

definition "theory" :: int where
  "theory = 1"

definition "fun" :: int where
  "fun = 1"

definition "lemma" :: int where
  "lemma = 1"

definition "apply" :: int where
  "apply = 1"

definition "by" :: int where
  "by = 1"

definition "done" :: int where
  "done = 1"

definition auto :: int where
  "auto = 1"

definition blast :: int where
  "blast = 1"

definition "proof" :: int where
  "proof = 1"

definition "have" :: int where
  "have = 1"

definition "qed" :: int where
  "qed = 1"

definition Main :: int where
  "Main = 1"

definition o' :: int where
  "o' = 1"

definition hd :: int where
  "hd = 1"

definition add :: int where
  "add = 1"

definition Suc :: int where
  "Suc = 1"

value "hd [1,2,3]"


end