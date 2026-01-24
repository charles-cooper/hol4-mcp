(* cheat_finder.sml - Linearize tactics with spans for cursor navigation

   Usage:
     linearize_with_spans_json "conj_tac >- simp[] \\\\ gvs[]"
     => [{"t":"conj_tac","s":0,"e":8},{"t":"simp[]","s":12,"e":18}]

   Used by FileProofCursor to map file positions to proof state.
*)

(* Simple JSON string escaping for tactic text *)
fun json_escape_char c =
  case c of
    #"\"" => "\\\""
  | #"\\" => "\\\\"
  | #"\n" => "\\n"
  | #"\r" => "\\r"
  | #"\t" => "\\t"
  | _ => if Char.ord c < 32
         then "\\u" ^ StringCvt.padLeft #"0" 4 (Int.fmt StringCvt.HEX (Char.ord c))
         else String.str c

fun json_escape_string s =
  String.concat (map json_escape_char (String.explode s))

(* Convert tactic span to JSON object: {"t":"text","s":start,"e":end,"a":use_eall} *)
fun tactic_span_to_json (text, start_off, end_off, use_eall) =
  "{\"t\":\"" ^ json_escape_string text ^ 
  "\",\"s\":" ^ Int.toString start_off ^ 
  ",\"e\":" ^ Int.toString end_off ^
  ",\"a\":" ^ (if use_eall then "true" else "false") ^ "}"

(* Convert list of tactic spans to JSON array *)
fun tactic_spans_to_json spans =
  "[" ^ String.concatWith "," (map tactic_span_to_json spans) ^ "]"

(* Convert a string to JSON string with quotes *)
fun json_string s = "\"" ^ json_escape_string s ^ "\""

(* Convert list of strings to JSON array *)
fun json_string_array strs =
  "[" ^ String.concatWith "," (map json_string strs) ^ "]"

(* JSON result helpers: {"ok": ...} or {"err": "message"} *)
fun json_ok payload = "{\"ok\":" ^ payload ^ "}"
fun json_err msg = "{\"err\":" ^ json_string msg ^ "}"

(* Convert a single goal (assumptions, conclusion) to JSON object *)
fun goal_to_json (asms, concl) =
  "{\"asms\":" ^ json_string_array (map term_to_string asms) ^
  ",\"goal\":" ^ json_string (term_to_string concl) ^ "}"

(* Convert list of goals to JSON array *)
fun goals_to_json_array goals =
  "[" ^ String.concatWith "," (map goal_to_json goals) ^ "]"

(* Print current goals as JSON: {"ok":[{"asms":[...],"goal":"..."},...]}} *)
fun goals_json () = 
  let val goals = top_goals()
  in print (json_ok (goals_to_json_array goals) ^ "\n") end
  handle e => print (json_err (exnMessage e) ^ "\n");

(* linearize_with_spans - Return list of (tactic, start, end, use_eall) for navigation

   Linearization semantics:
   - Split at >- boundaries (each arm becomes separate tactic)
   - Split >> chains but mark subsequent items with use_eall=true
   - use_eall=true means the tactic should apply to ALL goals (for replay)
   - Processes ALL tactics (no cheat stopping)
   - Returns spans for each tactic (char offsets into source)
*)
fun linearize_with_spans source = let
  val tree = TacticParse.parseTacticBlock source

  fun text_at (s, e) =
    if s >= 0 andalso e <= String.size source andalso s < e then
      String.substring (source, s, e - s)
    else ""

  (* Get span of a node - returns (start, end) or (0, 0) if no span *)
  fun node_span (TacticParse.Group (_, span, _)) = span
    | node_span (TacticParse.Opaque (_, span)) = span
    | node_span (TacticParse.LOpaque (_, span)) = span
    | node_span (TacticParse.OOpaque (_, span)) = span
    | node_span (TacticParse.Subgoal span) = span  (* by/suffices_by quotation *)
    | node_span (TacticParse.LThen1 inner) = node_span inner
    | node_span (TacticParse.Try inner) = node_span inner
    | node_span (TacticParse.LTry inner) = node_span inner
    | node_span (TacticParse.Repeat inner) = node_span inner
    | node_span (TacticParse.LRepeat inner) = node_span inner
    | node_span (TacticParse.LAllGoals inner) = node_span inner
    | node_span (TacticParse.LHeadGoal inner) = node_span inner
    | node_span (TacticParse.LLastGoal inner) = node_span inner
    | node_span (TacticParse.LTacsToLT inner) = node_span inner
    | node_span (TacticParse.LNullOk inner) = node_span inner
    | node_span (TacticParse.LFirstLT inner) = node_span inner
    | node_span (TacticParse.LNthGoal (inner, _)) = node_span inner
    | node_span node = case TacticParse.topSpan node of
        SOME span => span | NONE => (0, 0)

  (* Get text and span of a node *)
  fun node_text_span node = let
    val (s, e) = node_span node
    val txt = text_at (s, e)
  in (txt, s, e) end

  (* Check if a node's base is ultimately a Subgoal (for by/suffices_by detection) *)
  fun is_subgoal_base (TacticParse.Subgoal _) = true
    | is_subgoal_base (TacticParse.Group (_, _, inner)) = is_subgoal_base inner
    | is_subgoal_base (TacticParse.ThenLT (base, _)) = is_subgoal_base base
    | is_subgoal_base _ = false

  (* Check if a node is a >- structure (needs splitting) *)
  fun is_split_node (TacticParse.ThenLT (base, _)) = not (is_subgoal_base base)
    | is_split_node (TacticParse.LThen _) = true
    | is_split_node (TacticParse.Group (_, _, inner)) = is_split_node inner
    | is_split_node _ = false

  (* Flatten a >- node into (text, start, end, use_eall) tuples - handles left-associative nesting
     Note: ThenLT with Subgoal base is `by`/`suffices_by` - keep atomic
     Within each >- arm, >> chains get use_eall=true for non-first items *)
  fun flatten_split_spans (TacticParse.ThenLT (base, arms)) =
        if is_subgoal_base base then
          (* by/suffices_by: return as single atomic tactic, use_eall=false *)
          let
            val (_, base_s, _) = node_text_span base
            fun last_span [] = (0, 0)
              | last_span [x] = node_span x
              | last_span (_::xs) = last_span xs
            val (_, arm_e) = last_span arms
            val t = text_at (base_s, arm_e)
          in if t = "" then [] else [(t, base_s, arm_e, false)] end
        else
          (* Each arm is a separate context, so each arm starts fresh with use_eall=false *)
          flatten_split_spans base @ List.concat (List.map flatten_arm_spans arms)
    | flatten_split_spans (TacticParse.LThen (base, arms)) =
        flatten_split_spans base @ List.concat (List.map flatten_arm_spans arms)
    | flatten_split_spans (TacticParse.LThen1 inner) = flatten_split_spans inner
    | flatten_split_spans (TacticParse.Then items) =
        (* >> chain: first item use_eall=false, rest use_eall=true *)
        flatten_then_chain items
    | flatten_split_spans (TacticParse.Group (_, span, inner)) =
        if is_split_node inner then
          flatten_split_spans inner
        else
          let val t = text_at span in if t = "" then [] else [(t, #1 span, #2 span, false)] end
    | flatten_split_spans node =
        let val (t, s, e) = node_text_span node
        in if t = "" then [] else [(t, s, e, false)] end

  (* Flatten a >> chain: first item gets use_eall=false, rest get use_eall=true *)
  and flatten_then_chain [] = []
    | flatten_then_chain [x] = flatten_split_spans x  (* Single item keeps its own eall flag *)
    | flatten_then_chain (first::rest) =
        let
          (* First item: use_eall stays false (unless it's itself a >> chain) *)
          val first_spans = flatten_split_spans first
          (* Rest items: base spans get use_eall=true, but >- arm spans stay false *)
          val rest_spans = List.concat (List.map flatten_rest_item rest)
        in
          first_spans @ rest_spans
        end

  (* Flatten a rest item in >> chain: leaf base gets use_eall=true, >- arms stay false
     For nested ThenLT like (b >- c) >- d, only b (the leaf base) gets use_eall=true,
     while c and d (all arms at any nesting level) stay use_eall=false. *)
  and flatten_rest_item node =
        let
          (* Extract leaf base and all arms from nested ThenLT structure *)
          fun collect_thenlt (TacticParse.ThenLT (base, arms)) =
                if is_subgoal_base base then
                  (* by/suffices_by: return entire construct as leaf *)
                  (SOME (TacticParse.ThenLT (base, arms)), [])
                else
                  let val (leaf, inner_arms) = collect_thenlt base
                  in (leaf, inner_arms @ arms) end
            | collect_thenlt (TacticParse.LThen (base, arms)) =
                let val (leaf, inner_arms) = collect_thenlt base
                in (leaf, inner_arms @ arms) end
            | collect_thenlt (TacticParse.Group (_, _, inner)) =
                if is_split_node inner then collect_thenlt inner
                else (SOME node, [])
            | collect_thenlt other = (SOME other, [])
        in
          case collect_thenlt node of
            (NONE, _) => []
          | (SOME leaf, []) =>
              (* No arms - just a simple node, force use_eall=true *)
              List.map (fn (t,s,e,_) => (t,s,e,true)) (flatten_split_spans leaf)
          | (SOME (TacticParse.ThenLT (base, arms)), all_arms) =>
              if is_subgoal_base base then
                (* by/suffices_by as leaf: atomic with use_eall=true, plus outer arms *)
                let
                  val (_, base_s, _) = node_text_span base
                  fun last_span [] = (0, 0)
                    | last_span [x] = node_span x
                    | last_span (_::xs) = last_span xs
                  val (_, arm_e) = last_span arms
                  val t = text_at (base_s, arm_e)
                  val by_span = if t = "" then [] else [(t, base_s, arm_e, true)]
                  val outer_arm_spans = List.concat (List.map flatten_arm_spans all_arms)
                in by_span @ outer_arm_spans end
              else
                (* Should not happen - collect_thenlt recurses through non-subgoal ThenLT *)
                []
          | (SOME leaf, all_arms) =>
              (* Leaf base gets use_eall=true, all arms stay use_eall=false *)
              let
                val leaf_spans = List.map (fn (t,s,e,_) => (t,s,e,true)) (flatten_split_spans leaf)
                val arm_spans = List.concat (List.map flatten_arm_spans all_arms)
              in leaf_spans @ arm_spans end
        end

  (* Flatten a >- arm: each arm starts fresh (use_eall=false for first item) *)
  and flatten_arm_spans node = flatten_split_spans node

  (* Main traversal - returns reversed list of (text, start, end, use_eall) *)
  fun go (TacticParse.Then []) acc = acc
    | go (TacticParse.Then items) acc =
        (* Split >> chains: first item use_eall=false, rest use_eall=true *)
        let val spans = flatten_then_chain items
            val acc' = List.foldl (fn ((t,s,e,a), acc) => if t = "" then acc else (t,s,e,a) :: acc) acc spans
        in acc' end
    | go (TacticParse.LThen (base, arms)) acc = let
        (* Recursively flatten the whole >- structure *)
        val all_items = flatten_split_spans (TacticParse.LThen (base, arms))
        val acc' = List.foldl (fn ((t,s,e,a), acc) => if t = "" then acc else (t,s,e,a) :: acc) acc all_items
      in acc' end
    | go (TacticParse.ThenLT (base, arms)) acc =
        if is_subgoal_base base then
          (* by/suffices_by: emit as single atomic tactic *)
          let
            val (_, base_s, _) = node_text_span base
            fun last_span [] = (0, 0)
              | last_span [x] = node_span x
              | last_span (_::xs) = last_span xs
            val (_, arm_e) = last_span arms
            val s = base_s
            val e = arm_e
            val t = text_at (s, e)
          in if t = "" then acc else (t, s, e, false) :: acc end
        else let
          val all_items = flatten_split_spans (TacticParse.ThenLT (base, arms))
          val acc' = List.foldl (fn ((t,s,e,a), acc) => if t = "" then acc else (t,s,e,a) :: acc) acc all_items
        in acc' end
    | go (TacticParse.Group (_, span, inner)) acc =
        (* Check if inner needs splitting (ThenLT/LThen without Subgoal base).
           If so, recurse to flatten. Otherwise emit Group as single atomic tactic.
           This preserves wrappers like rpt, TRY, etc. *)
        if is_split_node inner then
          go inner acc
        else
          let val t = text_at span in if t = "" then acc else (t, #1 span, #2 span, false) :: acc end
    | go (TacticParse.First items) acc =
        List.foldl (fn (item, a) => go item a) acc items
    | go (TacticParse.LFirst items) acc =
        List.foldl (fn (item, a) => go item a) acc items
    | go (TacticParse.Try inner) acc = go inner acc
    | go (TacticParse.LTry inner) acc = go inner acc
    | go (TacticParse.Repeat inner) acc = go inner acc
    | go (TacticParse.LRepeat inner) acc = go inner acc
    | go (TacticParse.LThen1 inner) acc = go inner acc
    | go (TacticParse.LAllGoals inner) acc = go inner acc
    | go (TacticParse.LHeadGoal inner) acc = go inner acc
    | go (TacticParse.LLastGoal inner) acc = go inner acc
    | go (TacticParse.LTacsToLT inner) acc = go inner acc
    | go (TacticParse.LNullOk inner) acc = go inner acc
    | go (TacticParse.LNthGoal (inner, _)) acc = go inner acc
    | go (TacticParse.LFirstLT inner) acc = go inner acc
    | go (TacticParse.LSplit (_, a, b)) acc = go b (go a acc)
    | go (TacticParse.LSelectThen (a, b)) acc = go b (go a acc)
    | go (TacticParse.List (_, items)) acc =
        List.foldl (fn (item, a) => go item a) acc items
    | go (TacticParse.MapEvery (_, items)) acc =
        List.foldl (fn (item, a) => go item a) acc items
    | go (TacticParse.MapFirst (_, items)) acc =
        List.foldl (fn (item, a) => go item a) acc items
    | go (TacticParse.LThenLT items) acc =
        List.foldl (fn (item, a) => go item a) acc items
    | go (TacticParse.RepairGroup (_, _, inner, _)) acc = go inner acc
    (* Terminal cases - all use_eall=false by default *)
    | go (TacticParse.Opaque (_, (s, e))) acc =
        let val t = text_at (s, e) in if t = "" then acc else (t, s, e, false) :: acc end
    | go (TacticParse.LOpaque (_, (s, e))) acc =
        let val t = text_at (s, e) in if t = "" then acc else (t, s, e, false) :: acc end
    | go (TacticParse.OOpaque (_, (s, e))) acc =
        let val t = text_at (s, e) in if t = "" then acc else (t, s, e, false) :: acc end
    | go _ acc = acc
in
  List.rev (go tree [])
end;

(* JSON output version: {"ok":[...]} or {"err":"message"} *)
fun linearize_with_spans_json source =
  print (json_ok (tactic_spans_to_json (linearize_with_spans source)) ^ "\n")
  handle e => print (json_err (exnMessage e) ^ "\n");
