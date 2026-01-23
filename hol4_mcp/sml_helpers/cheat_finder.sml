(* cheat_finder.sml - Extract tactics before cheat using TacticParse

   Usage:
     extract_before_cheat "strip_tac \\\\ simp[] >- cheat"
     => "strip_tac \\\\ simp[]"

     linearize_to_cheat "strip_tac >- (simp[] \\\\ cheat)"
     => ["strip_tac", "simp[]"]
*)

(* dropWhile is not in HOL's List structure *)
fun dropWhile _ [] = []
  | dropWhile p (x::xs) = if p x then dropWhile p xs else x::xs;

(* Find start position of first "cheat" in AST; returns NONE if not found.
   is_cheat: span -> bool checks if span text equals "cheat" *)
fun find_cheat_pos (is_cheat: int * int -> bool)
      (TacticParse.Opaque (_, span: int * int)) =
      if is_cheat span then SOME (#1 span) else NONE
  | find_cheat_pos is_cheat (TacticParse.LOpaque (_, span: int * int)) =
      if is_cheat span then SOME (#1 span) else NONE
  | find_cheat_pos is_cheat (TacticParse.OOpaque (_, span: int * int)) =
      if is_cheat span then SOME (#1 span) else NONE
  | find_cheat_pos _ (TacticParse.Then []) = NONE
  | find_cheat_pos is_cheat (TacticParse.Then items) =
      let fun loop [] = NONE
            | loop (x::xs) = case find_cheat_pos is_cheat x of SOME p => SOME p | NONE => loop xs
      in loop items end
  | find_cheat_pos is_cheat (TacticParse.ThenLT (base, arms)) =
      (case find_cheat_pos is_cheat base of
         SOME pos => SOME pos
       | NONE => let fun loop [] = NONE
                       | loop (x::xs) = case find_cheat_pos is_cheat x of SOME p => SOME p | NONE => loop xs
                 in loop arms end)
  | find_cheat_pos is_cheat (TacticParse.LThen (base, arms)) =
      (case find_cheat_pos is_cheat base of
         SOME pos => SOME pos
       | NONE => let fun loop [] = NONE
                       | loop (x::xs) = case find_cheat_pos is_cheat x of SOME p => SOME p | NONE => loop xs
                 in loop arms end)
  | find_cheat_pos is_cheat (TacticParse.First items) =
      let fun loop [] = NONE
            | loop (x::xs) = case find_cheat_pos is_cheat x of SOME p => SOME p | NONE => loop xs
      in loop items end
  | find_cheat_pos is_cheat (TacticParse.LFirst items) =
      let fun loop [] = NONE
            | loop (x::xs) = case find_cheat_pos is_cheat x of SOME p => SOME p | NONE => loop xs
      in loop items end
  | find_cheat_pos is_cheat (TacticParse.Group (_, _, inner)) = find_cheat_pos is_cheat inner
  | find_cheat_pos is_cheat (TacticParse.Try inner) = find_cheat_pos is_cheat inner
  | find_cheat_pos is_cheat (TacticParse.LTry inner) = find_cheat_pos is_cheat inner
  | find_cheat_pos is_cheat (TacticParse.Repeat inner) = find_cheat_pos is_cheat inner
  | find_cheat_pos is_cheat (TacticParse.LRepeat inner) = find_cheat_pos is_cheat inner
  | find_cheat_pos is_cheat (TacticParse.LAllGoals inner) = find_cheat_pos is_cheat inner
  | find_cheat_pos is_cheat (TacticParse.LHeadGoal inner) = find_cheat_pos is_cheat inner
  | find_cheat_pos is_cheat (TacticParse.LLastGoal inner) = find_cheat_pos is_cheat inner
  | find_cheat_pos is_cheat (TacticParse.LThenLT items) =
      let fun loop [] = NONE
            | loop (x::xs) = case find_cheat_pos is_cheat x of SOME p => SOME p | NONE => loop xs
      in loop items end
  | find_cheat_pos is_cheat (TacticParse.LThen1 inner) = find_cheat_pos is_cheat inner
  | find_cheat_pos is_cheat (TacticParse.LTacsToLT inner) = find_cheat_pos is_cheat inner
  | find_cheat_pos is_cheat (TacticParse.LNullOk inner) = find_cheat_pos is_cheat inner
  | find_cheat_pos is_cheat (TacticParse.LNthGoal (inner, _)) = find_cheat_pos is_cheat inner
  | find_cheat_pos is_cheat (TacticParse.LFirstLT inner) = find_cheat_pos is_cheat inner
  | find_cheat_pos is_cheat (TacticParse.LSplit (_, a, b)) =
      (case find_cheat_pos is_cheat a of SOME p => SOME p | NONE => find_cheat_pos is_cheat b)
  | find_cheat_pos is_cheat (TacticParse.LSelectThen (a, b)) =
      (case find_cheat_pos is_cheat a of SOME p => SOME p | NONE => find_cheat_pos is_cheat b)
  | find_cheat_pos is_cheat (TacticParse.List (_, items)) =
      let fun loop [] = NONE
            | loop (x::xs) = case find_cheat_pos is_cheat x of SOME p => SOME p | NONE => loop xs
      in loop items end
  | find_cheat_pos is_cheat (TacticParse.MapEvery (_, items)) =
      let fun loop [] = NONE
            | loop (x::xs) = case find_cheat_pos is_cheat x of SOME p => SOME p | NONE => loop xs
      in loop items end
  | find_cheat_pos is_cheat (TacticParse.MapFirst (_, items)) =
      let fun loop [] = NONE
            | loop (x::xs) = case find_cheat_pos is_cheat x of SOME p => SOME p | NONE => loop xs
      in loop items end
  | find_cheat_pos is_cheat (TacticParse.RepairGroup (_, _, inner, _)) = find_cheat_pos is_cheat inner
  (* Remaining cases have no inner tac_expr to search *)
  | find_cheat_pos _ (TacticParse.Subgoal _) = NONE
  | find_cheat_pos _ (TacticParse.Rename _) = NONE
  | find_cheat_pos _ (TacticParse.LSelectGoal _) = NONE
  | find_cheat_pos _ (TacticParse.LSelectGoals _) = NONE
  | find_cheat_pos _ TacticParse.LReverse = NONE
  | find_cheat_pos _ (TacticParse.RepairEmpty _) = NONE;

(* Check if AST contains RepairGroup (unbalanced delimiters) or RepairEmpty *)
fun has_repair (TacticParse.RepairGroup _) = true
  | has_repair (TacticParse.RepairEmpty _) = true
  | has_repair (TacticParse.Then items) = List.exists has_repair items
  | has_repair (TacticParse.ThenLT (base, arms)) =
      has_repair base orelse List.exists has_repair arms
  | has_repair (TacticParse.LThen (base, arms)) =
      has_repair base orelse List.exists has_repair arms
  | has_repair (TacticParse.First items) = List.exists has_repair items
  | has_repair (TacticParse.LFirst items) = List.exists has_repair items
  | has_repair (TacticParse.Group (_, _, inner)) = has_repair inner
  | has_repair (TacticParse.Try inner) = has_repair inner
  | has_repair (TacticParse.LTry inner) = has_repair inner
  | has_repair (TacticParse.Repeat inner) = has_repair inner
  | has_repair (TacticParse.LRepeat inner) = has_repair inner
  | has_repair (TacticParse.LAllGoals inner) = has_repair inner
  | has_repair (TacticParse.LHeadGoal inner) = has_repair inner
  | has_repair (TacticParse.LLastGoal inner) = has_repair inner
  | has_repair (TacticParse.LThenLT items) = List.exists has_repair items
  | has_repair (TacticParse.LThen1 inner) = has_repair inner
  | has_repair (TacticParse.LTacsToLT inner) = has_repair inner
  | has_repair (TacticParse.LNullOk inner) = has_repair inner
  | has_repair (TacticParse.LNthGoal (inner, _)) = has_repair inner
  | has_repair (TacticParse.LFirstLT inner) = has_repair inner
  | has_repair (TacticParse.LSplit (_, a, b)) = has_repair a orelse has_repair b
  | has_repair (TacticParse.LSelectThen (a, b)) = has_repair a orelse has_repair b
  | has_repair (TacticParse.List (_, items)) = List.exists has_repair items
  | has_repair (TacticParse.MapEvery (_, items)) = List.exists has_repair items
  | has_repair (TacticParse.MapFirst (_, items)) = List.exists has_repair items
  | has_repair _ = false;

fun extract_before_cheat source =
  let
    val tree = TacticParse.parseTacticBlock source

    (* Extract text at span (s, e) *)
    fun text_at (s, e) =
      if s >= 0 andalso e <= String.size source andalso s < e then
        String.substring (source, s, e - s)
      else ""

    (* Check if this span contains "cheat" (case-insensitive to match parser) *)
    fun is_cheat span = String.map Char.toLower (text_at span) = "cheat"

    (* Trim trailing whitespace *)
    fun trim_right s =
      String.implode (List.rev (dropWhile Char.isSpace (List.rev (String.explode s))))

    (* Check and strip trailing separator *)
    fun ends_with str suffix =
      let val slen = String.size str val plen = String.size suffix in
        slen >= plen andalso String.substring (str, slen - plen, plen) = suffix
      end

    fun strip_trailing_sep str =
      if ends_with str "\\\\" then String.substring (str, 0, String.size str - 2)
      else if ends_with str ">>" then String.substring (str, 0, String.size str - 2)
      else if ends_with str ">-" then String.substring (str, 0, String.size str - 2)
      else str

    (* Repeatedly trim whitespace and separators *)
    fun clean s =
      let
        val s1 = trim_right s
        val s2 = strip_trailing_sep s1
        val s3 = trim_right s2
      in
        if s3 = s then s else clean s3
      end
  in
    case find_cheat_pos is_cheat tree of
      NONE => ""  (* No cheat found *)
    | SOME pos =>
        if pos = 0 then ""
        else
          let val prefix = clean (String.substring (source, 0, pos))
              val prefix_tree = TacticParse.parseTacticBlock prefix
          in
            (* Reject unbalanced syntax - prefix must parse without repair nodes *)
            if has_repair prefix_tree then "" else prefix
          end
  end
  handle _ => "";

(* linearize_to_cheat - Return list of tactics to replay via sequential etq,
   plus the character offset of the cheat (for line number calculation).

   Key insight: sequential etq uses >- semantics (leftmost goal only).
   So we split at >- boundaries but keep >> chains as compounds.

   Example: "strip_tac >- (simp[] \\ cheat)" => (["strip_tac", "simp[]"], SOME 25)
   Example: "a >> b \\ cheat" => (["a >> b"], SOME 10)
   Example: "simp[]" => ([], NONE)  -- no cheat
*)
fun linearize_to_cheat source = let
  val tree = TacticParse.parseTacticBlock source

  fun text_at (s, e) =
    if s >= 0 andalso e <= String.size source andalso s < e then
      String.substring (source, s, e - s)
    else ""

  fun is_cheat_span span = String.map Char.toLower (text_at span) = "cheat"

  (* Find cheat position upfront - this is the authoritative location *)
  val cheat_pos = find_cheat_pos is_cheat_span tree

  (* Get text of a node - special handling for Then which has no span *)
  fun node_text (TacticParse.Then items) =
        String.concatWith " >> " (List.map node_text items)
    | node_text (TacticParse.Group (_, (s, e), _)) = text_at (s, e)
    | node_text node = case TacticParse.topSpan node of
        NONE => "" | SOME (s, e) => text_at (s, e)

  (* Check if node contains a cheat *)
  fun has_cheat node = find_cheat_pos is_cheat_span node <> NONE

  (* Check if a node's base is ultimately a Subgoal (for by/suffices_by detection) *)
  fun is_subgoal_base (TacticParse.Subgoal _) = true
    | is_subgoal_base (TacticParse.Group (_, _, inner)) = is_subgoal_base inner
    | is_subgoal_base (TacticParse.ThenLT (base, _)) = is_subgoal_base base
    | is_subgoal_base _ = false

  (* Check if a node is a >- structure (needs splitting)
     Note: ThenLT with Subgoal base is `by`/`suffices_by` construct, which is atomic *)
  fun is_split_node (TacticParse.ThenLT (base, _)) = not (is_subgoal_base base)
    | is_split_node (TacticParse.LThen _) = true
    | is_split_node (TacticParse.Group (_, _, inner)) = is_split_node inner
    | is_split_node _ = false

  (* Flatten a >- node into its components *)
  fun flatten_split (TacticParse.ThenLT (base, arms)) =
        node_text base :: List.concat (List.map flatten_split arms)
    | flatten_split (TacticParse.LThen (base, arms)) =
        node_text base :: List.concat (List.map flatten_split arms)
    | flatten_split (TacticParse.LThen1 inner) = flatten_split inner
    | flatten_split (TacticParse.Group (_, _, inner)) = flatten_split inner
    | flatten_split node = [node_text node]

  (* Emit prefix items: keep >> chains together, split at >- boundaries *)
  fun emit_prefix items =
    let
      (* Take consecutive non-split items from front *)
      fun take_non_split [] = ([], [])
        | take_non_split (x::xs) =
            if is_split_node x then ([], x::xs)
            else let val (took, rest) = take_non_split xs in (x::took, rest) end

      (* Process items into string list *)
      fun process [] = []
        | process items =
            let val (non_split, rest) = take_non_split items
                val compound = String.concatWith " >> " (List.map node_text non_split)
                val prefix = if compound = "" then [] else [compound]
            in
              case rest of
                [] => prefix
              | (x::xs) => prefix @ flatten_split x @ process xs
            end
    in
      process items
    end

  (* Main traversal - returns reversed list of tactic strings *)
  fun go (TacticParse.Then []) acc = acc
    | go (TacticParse.Then items) acc = let
        (* Find index of item containing cheat *)
        fun find_idx [] _ = NONE
          | find_idx (x::xs) i = if has_cheat x then SOME i else find_idx xs (i+1)
      in
        case find_idx items 0 of
          NONE => acc
        | SOME idx => let
            val prefix_items = List.take (items, idx)
            (* Emit prefix items, flattening >- structures *)
            val emitted = emit_prefix prefix_items
            val acc' = List.foldl (fn (s, a) => if s = "" then a else s :: a) acc emitted
          in
            go (List.nth (items, idx)) acc'
          end
      end
    | go (TacticParse.LThen (base, arms)) acc =
        if has_cheat base then
          go base acc
        else let
          (* Find arm containing cheat *)
          fun find_arm [] = NONE
            | find_arm (a::as') = if has_cheat a then SOME a else find_arm as'
          val base_text = node_text base
          val acc' = if base_text = "" then acc else base_text :: acc
        in
          case find_arm arms of NONE => acc' | SOME arm => go arm acc'
        end
    | go (TacticParse.ThenLT (base, arms)) acc =
        if has_cheat base then
          go base acc
        else let
          fun find_arm [] = NONE
            | find_arm (a::as') = if has_cheat a then SOME a else find_arm as'
          val base_text = node_text base
          val acc' = if base_text = "" then acc else base_text :: acc
        in
          case find_arm arms of NONE => acc' | SOME arm => go arm acc'
        end
    | go (TacticParse.Group (_, _, inner)) acc = go inner acc
    | go (TacticParse.First items) acc = let
        fun find_item [] = NONE
          | find_item (x::xs) = if has_cheat x then SOME x else find_item xs
      in
        case find_item items of NONE => acc | SOME item => go item acc
      end
    | go (TacticParse.LFirst items) acc = let
        fun find_item [] = NONE
          | find_item (x::xs) = if has_cheat x then SOME x else find_item xs
      in
        case find_item items of NONE => acc | SOME item => go item acc
      end
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
    | go (TacticParse.LSplit (_, a, b)) acc =
        if has_cheat a then go a acc else go b acc
    | go (TacticParse.LSelectThen (a, b)) acc =
        if has_cheat a then go a acc else go b acc
    | go (TacticParse.List (_, items)) acc = let
        (* Find index of item containing cheat *)
        fun find_idx [] _ = NONE
          | find_idx (x::xs) i = if has_cheat x then SOME i else find_idx xs (i+1)
      in
        case find_idx items 0 of
          NONE => acc
        | SOME idx => let
            (* Emit items before the one with cheat *)
            val prefix_items = List.take (items, idx)
            val prefix_texts = List.map node_text prefix_items
            val acc' = List.foldl (fn (s, a) => if s = "" then a else s :: a) acc prefix_texts
          in
            go (List.nth (items, idx)) acc'
          end
      end
    | go (TacticParse.MapEvery (_, items)) acc = let
        fun find_item [] = NONE
          | find_item (x::xs) = if has_cheat x then SOME x else find_item xs
      in
        case find_item items of NONE => acc | SOME item => go item acc
      end
    | go (TacticParse.MapFirst (_, items)) acc = let
        fun find_item [] = NONE
          | find_item (x::xs) = if has_cheat x then SOME x else find_item xs
      in
        case find_item items of NONE => acc | SOME item => go item acc
      end
    | go (TacticParse.LThenLT items) acc = let
        fun find_item [] = NONE
          | find_item (x::xs) = if has_cheat x then SOME x else find_item xs
      in
        case find_item items of NONE => acc | SOME item => go item acc
      end
    | go (TacticParse.RepairGroup (_, _, inner, _)) acc = go inner acc
    (* Terminal cases *)
    | go (TacticParse.Opaque (_, span)) acc =
        if is_cheat_span span then acc else text_at span :: acc
    | go (TacticParse.LOpaque (_, span)) acc =
        if is_cheat_span span then acc else text_at span :: acc
    | go (TacticParse.OOpaque (_, span)) acc =
        if is_cheat_span span then acc else text_at span :: acc
    | go _ acc = acc
in
  (List.rev (go tree []), cheat_pos)
end handle _ => ([], NONE);
