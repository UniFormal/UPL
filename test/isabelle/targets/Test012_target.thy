theory Test012_target
  imports Main
begin

typedef interval0_10 = "{0..10:: int}"
  by auto

definition n :: interval0_10 where
  "n = 0"