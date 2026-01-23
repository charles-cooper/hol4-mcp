(*
  HOL script that fails to build - for testing build failure logs.
*)

open HolKernel Parse boolLib bossLib;

val _ = new_theory "fail";

(* This will fail - undefined identifier *)
Theorem will_fail:
  undefined_thing = T
Proof
  simp[]
QED

val _ = export_theory();
