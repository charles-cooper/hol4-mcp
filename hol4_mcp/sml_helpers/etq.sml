(* etq.sml - "Evaluate Tactic Quoted" for goaltree mode

   Mirrors HOL's etqLib but with output optimizations:
   - Returns unit (not proof) to avoid REPL auto-printing the proof tree
   - Prints only goal count + first goal (not all goals)

   Usage:
     gt `A /\ B ==> B /\ A`;
     etq "DISCH_TAC";
     etq "CONJ_TAC";
     etq "ASM_REWRITE_TAC []";
     p();  (* Shows: DISCH_TAC \\ CONJ_TAC >- (...) >- (...) *)
*)

val _ = load "smlExecute";

(* Print just goal conclusion, not assumptions - keeps output small *)
fun print_goal_concl (_, g) = print (Parse.term_to_string g ^ "\n");

fun print_goals [] = print "Goal proved.\n"
  | print_goals [g] = (print "1 goal:\n"; print_goal_concl g)
  | print_goals (g::gs) =
      (print (Int.toString (1 + length gs) ^ " goals. First:\n"); print_goal_concl g);

fun etq_tmo timeout s =
  let
    val _ = proofManagerLib.et (s, smlExecute.tactic_of_sml timeout s)
    val goals = proofManagerLib.top_goals ()
  in
    print_goals goals
  end
  handle e => raise mk_HOL_ERR "etq" "etq" (Feedback.exn_to_string e);

val etq = etq_tmo 30.0;

(* Apply tactic to nth goal (1-indexed) using NTH_GOAL *)
fun etq_nth n s = etq ("NTH_GOAL (" ^ s ^ ") " ^ Int.toString n);
