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

(* Convert tactic span to JSON object: {"t":"text","s":start,"e":end} *)
fun tactic_span_to_json (text, start_off, end_off) =
  "{\"t\":\"" ^ json_escape_string text ^ 
  "\",\"s\":" ^ Int.toString start_off ^ 
  ",\"e\":" ^ Int.toString end_off ^ "}"

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

(* linearize_with_spans - Return list of (tactic, start, end) for navigation

   Linearization semantics:
   - Split at >- boundaries (each arm becomes separate tactic)
   - Keep >> chains together (they form single compound tactic)
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

  (* Flatten a >- node into (text, start, end) tuples - handles left-associative nesting
     Note: ThenLT with Subgoal base is `by`/`suffices_by` - keep atomic *)
  fun flatten_split_spans (TacticParse.ThenLT (base, arms)) =
        if is_subgoal_base base then
          (* by/suffices_by: return as single atomic tactic *)
          (* ThenLT has no span itself - compute from base and arms *)
          let
            val (_, base_s, _) = node_text_span base
            fun last_span [] = (0, 0)
              | last_span [x] = node_span x
              | last_span (_::xs) = last_span xs
            val (_, arm_e) = last_span arms
            val t = text_at (base_s, arm_e)
          in if t = "" then [] else [(t, base_s, arm_e)] end
        else
          flatten_split_spans base @ List.concat (List.map flatten_split_spans arms)
    | flatten_split_spans (TacticParse.LThen (base, arms)) =
        flatten_split_spans base @ List.concat (List.map flatten_split_spans arms)
    | flatten_split_spans (TacticParse.LThen1 inner) = flatten_split_spans inner
    | flatten_split_spans (TacticParse.Then items) =
        List.concat (List.map flatten_split_spans items)
    | flatten_split_spans (TacticParse.Group (_, span, inner)) =
        (* Check if inner is by/suffices_by - if so, emit Group as atomic *)
        if is_subgoal_base inner then
          let val t = text_at span in if t = "" then [] else [(t, #1 span, #2 span)] end
        else flatten_split_spans inner
    | flatten_split_spans node =
        let val (t, s, e) = node_text_span node
        in if t = "" then [] else [(t, s, e)] end

  (* Emit items with spans: keep >> chains together, split at >- boundaries *)
  fun emit_with_spans items = let
    fun take_non_split [] = ([], [])
      | take_non_split (x::xs) =
          if is_split_node x then ([], x::xs)
          else let val (took, rest) = take_non_split xs in (x::took, rest) end

    (* Compute combined span for >> chain *)
    fun chain_span [] = (0, 0)
      | chain_span items = let
          val spans = List.map node_span items
          val s = foldl Int.min (String.size source) (List.map #1 spans)
          val e = foldl Int.max 0 (List.map #2 spans)
        in (s, e) end

    fun process [] = []
      | process items = let
          val (non_split, rest) = take_non_split items
          val (s, e) = chain_span non_split
          val txt = text_at (s, e)
          val prefix = if txt = "" then [] else [(txt, s, e)]
        in
          case rest of
            [] => prefix
          | (x::xs) => prefix @ flatten_split_spans x @ process xs
        end
  in
    process items
  end

  (* Main traversal - returns reversed list of (text, start, end) *)
  fun go (TacticParse.Then []) acc = acc
    | go (TacticParse.Then items) acc =
        (* Split >> chains into individual tactics for position mapping *)
        List.foldl (fn (item, a) => go item a) acc items
    | go (TacticParse.LThen (base, arms)) acc = let
        (* Recursively flatten the whole >- structure *)
        val all_items = flatten_split_spans (TacticParse.LThen (base, arms))
        val acc' = List.foldl (fn ((t,s,e), a) => if t = "" then a else (t,s,e) :: a) acc all_items
      in acc' end
    | go (TacticParse.ThenLT (base, arms)) acc =
        if is_subgoal_base base then
          (* by/suffices_by: emit as single atomic tactic *)
          (* ThenLT has no span itself - compute from base and arms *)
          let
            val (_, base_s, _) = node_text_span base
            fun last_span [] = (0, 0)
              | last_span [x] = node_span x
              | last_span (_::xs) = last_span xs
            val (_, arm_e) = last_span arms
            val s = base_s
            val e = arm_e
            val t = text_at (s, e)
          in if t = "" then acc else (t, s, e) :: acc end
        else let
          val all_items = flatten_split_spans (TacticParse.ThenLT (base, arms))
          val acc' = List.foldl (fn ((t,s,e), a) => if t = "" then a else (t,s,e) :: a) acc all_items
        in acc' end
    | go (TacticParse.Group (_, span, inner)) acc =
        (* Check if inner is by/suffices_by - if so, emit Group as atomic *)
        if is_subgoal_base inner then
          let val t = text_at span in if t = "" then acc else (t, #1 span, #2 span) :: acc end
        else go inner acc
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
    (* Terminal cases *)
    | go (TacticParse.Opaque (_, (s, e))) acc =
        let val t = text_at (s, e) in if t = "" then acc else (t, s, e) :: acc end
    | go (TacticParse.LOpaque (_, (s, e))) acc =
        let val t = text_at (s, e) in if t = "" then acc else (t, s, e) :: acc end
    | go (TacticParse.OOpaque (_, (s, e))) acc =
        let val t = text_at (s, e) in if t = "" then acc else (t, s, e) :: acc end
    | go _ acc = acc
in
  List.rev (go tree [])
end;

(* JSON output version: {"ok":[...]} or {"err":"message"} *)
fun linearize_with_spans_json source =
  print (json_ok (tactic_spans_to_json (linearize_with_spans source)) ^ "\n")
  handle e => print (json_err (exnMessage e) ^ "\n");
