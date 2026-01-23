(*
  Minimal HOL4 test script for unit tests.
  Contains proved theorems and theorems with cheats for testing.
*)

open HolKernel Parse boolLib bossLib;

val _ = new_theory "test";

(* Simple proved theorem *)
Theorem add_zero:
  !n. n + 0 = n
Proof
  simp[]
QED

(* Theorem with cheat for testing cheat detection *)
Theorem needs_proof:
  !x y. x + y = y + x
Proof
  cheat
QED

(* Theorem with partial proof before cheat *)
Theorem partial_proof:
  !n. n * 1 = n
Proof
  rw[] \\
  cheat
QED

(* Another proved theorem *)
Theorem zero_add:
  !n. 0 + n = n
Proof
  simp[]
QED

(* Triviality example *)
Triviality helper_lemma:
  T
Proof
  simp[]
QED

val _ = export_theory();
