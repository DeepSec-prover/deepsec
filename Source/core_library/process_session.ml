(* Process manipulation for equivalence by session *)

open Extensions
open Term
open Display

type 'a one_or_two =
  | Single of 'a
  | Double of ('a * 'a)

module Label = struct
  type t =
    { label : int list;
      mutable link : t option;
      prefix : t option
    }
  let initial = { label = [0]; link = None; prefix = None }
  let add_position (prefix:t) (position:int) : t = { label = prefix.label @ [position]; link = None; prefix = Some prefix }
  let to_string (lab:t) : string =
    match lab.label with
    | [] -> Config.internal_error "[process_session.ml >> Label.to_string] Unexpected case."
    | h :: t ->
      List.fold_left (Printf.sprintf "%s.%d") (string_of_int h) t
  let rec independent (l:int list) (ll:int list) : int =
    match l,ll with
    | [], _ -> 0
    | _, [] -> 0
    | t1::q1, t2::q2 ->
        match compare t1 t2 with
          | 0 -> independent q1 q2
          | i -> i

  let lexico lbl1 lbl2 =
    let rec cmp_lexico l1 l2 = match l1, l2 with
      | [], [] -> 0
      | [], _ -> -1
      | _, [] -> 1
      | t1::q1, t2::q2 ->
          match compare t1 t2 with
            | 0 -> cmp_lexico q1 q2
            | i -> i
    in
    cmp_lexico lbl1.label lbl2.label

  let check_prefix (lbl1:t) (lbl2:t) : int option =
    let rec explore l1 l2 = match l1,l2 with
      | [],[i] -> Some i
      | h1::t1, h2::t2 when h1 = h2 -> explore t1 t2
      | _ -> None
    in
    explore lbl1.label lbl2.label

  let last_position l =
    let rec explore = function
      | [] -> Config.internal_error "[process_session.ml >> Label.last_position] Empty labels."
      | [h] -> h
      | _::t -> explore t
    in
    explore l.label

  let independent lbl1 lbl2 = independent lbl1.label lbl2.label

  type t_alias = t

  module Set = Set.Make(struct type t = t_alias let compare lbl1 lbl2 = compare lbl1.label lbl2.label end)

  let compare = independent

  let linked_labels = ref []

  let find_and_remove x lbl_set =
    let lbl_set' = Set.remove x lbl_set in
    if lbl_set == lbl_set'
    then None
    else Some lbl_set'

  let of_position_list label l =
    List.fold_left (fun acc i ->
      Set.add (add_position label i) acc
    ) Set.empty l

  let match_label lbl1 lbl2 =
    Config.debug (fun () -> Config.print_in_log (Printf.sprintf "Label.match_label : %s and %s\n" (to_string lbl1) (to_string lbl2)));
    match lbl1.link with
    | None ->
        (* We first check the prefix: We assume that prefix are always matched before. *)
        begin match lbl1.prefix, lbl2.prefix with
          | None, None -> ();
          | Some prefix1, Some prefix2 ->
              begin match prefix1.link with
                | None -> Config.internal_error "[Label.match_label] The prefix of labels should already be matched."
                | Some prefix2' ->
                    if prefix2 != prefix2'
                    then raise No_Match
              end
          | _, _ -> raise No_Match
        end;
        (* Since the prefix corresponds, we can link the labels. *)
        lbl1.link <- Some lbl2;
        linked_labels := lbl1 :: !linked_labels
    | Some lbl2' when lbl2 == lbl2' -> ()
    | _ -> raise No_Match

  let auto_cleanup f =
    let tmp_linked_labels = !linked_labels in
    linked_labels := [];

    try
      let r = f () in
      List.iter (fun lbl -> lbl.link <- None) !linked_labels;
      linked_labels := tmp_linked_labels;
      r
    with No_Match ->
      List.iter (fun lbl -> lbl.link <- None) !linked_labels;
      linked_labels := tmp_linked_labels;
      raise No_Match

  let independent_list lab_list1 lab_list2 =
    if
      List.exists (fun lab1 ->
        List.exists (fun lab2 -> independent lab1 lab2 = 0) lab_list2
      ) lab_list1
    then 0
    else independent (List.hd lab_list1) (List.hd lab_list2)

  (******* Display function ********)

  let display lbl = display_list string_of_int "." lbl.label
end

(* a module for representing blocks *)
module Block = struct
  module IntSet = Set.Make(struct type t = int let compare = compare end)

  type t = {
    label : Label.t list; (* Warning : the labels in label are not necessarily independent. FOr sorting, use Label.lexico *)
    recipes : snd_ord_variable list; (* There should always be variables *)
    bounds_axiom : (int * int) option; (* lower and upper bound on the axiom index used *)
    maximal_var : int;
    used_axioms : IntSet.t;
    used_variables : snd_ord_variable list;
      (* The [recipes] are the free variables whereas [used_variables] are the remaining
         variables after instantiation of the solutions of the constraint system, i.e.,
         they are variables in deduction facts of the constraint system. *)

    proper : bool (* Indicates whether the block is proper or not *)
  }

  let get_label t = t.label

  let print b =
    let ax = match b.bounds_axiom with
      | None -> "No"
      | Some (i,j) -> Printf.sprintf "[%d,%d]" i j in
    let axset =
      IntSet.fold (Printf.sprintf "%d %s") b.used_axioms "" in
    let snd =
      List.fold_left (fun s x -> s^" "^Variable.display Terminal Recipe x) "" b.recipes in
    Printf.sprintf "Block: labels:%s, axioms: %s, used axioms: %s, variables: %s, maximal var: %d" (List.fold_left (fun s lab -> s^" "^Label.to_string lab) "" b.label) ax axset snd b.maximal_var

  let create (label:Label.t list) : t = {
      label = List.fast_sort Label.lexico label;
      recipes = [];
      bounds_axiom = None;
      maximal_var = 0;
      used_axioms = IntSet.empty;
      used_variables = [];
      proper = true
  }

  let add_variable (snd_var:snd_ord_variable) (block:t) : t =
    { block with recipes = (snd_var :: block.recipes) }

  let add_axiom (ax:axiom) (block:t) : t =
    match block.bounds_axiom with
    | None ->
      let b = Axiom.index_of ax in
      {block with bounds_axiom = Some (b,b)}
    | Some (i,_) ->
      {block with bounds_axiom = Some (i,Axiom.index_of ax)}

  let add_labels (lab_list:Label.t list) (block:t) : t =
    {block with label = List.sort_uniq Label.lexico (List.rev_append lab_list block.label)}


  let rec is_faulty_block (block:t) (block_list:t list) : bool * snd_ord_variable list =
    match block_list with
    | [] -> false, []
    | b_i::q ->
      let comp_lab = Label.independent_list block.label b_i.label in
      if comp_lab < 0 then
        match b_i.bounds_axiom with
        | None -> true, []
        | Some (min_ax,max_ax) ->
            if IntSet.for_all (fun ax -> ax < min_ax || ax > max_ax) block.used_axioms
            then
              (* If faulty then it is necessary due to variables *)
              if block.maximal_var < min_ax
              then true, []
              else false, List.filter (fun v -> Variable.type_of v >= min_ax) block.used_variables
            else false, [] (* A real non faulty since there are axioms from block_i used by block *)
      else if comp_lab > 0 then is_faulty_block block q
      else false, []

  (* applies a snd order substitution on a block list and computes the bound
  fields of the block type *)
  let apply_snd_subst_on_block (snd_subst:(snd_ord,axiom) Subst.t) (block_list:t list) : t list =
    Subst.apply snd_subst block_list (fun l f ->
      List.map (fun block ->
        let used_variables = ref [] in
        let max_var = ref 0 in
        let used_axioms = ref IntSet.empty in
        List.iter (fun var ->
          let r' = f (Term.of_variable var) in
          Term.iter_variables_and_axioms (fun ax_op var_op ->
            match ax_op,var_op with
            | Some ax, None ->
              used_axioms := IntSet.add (Axiom.index_of ax) !used_axioms
            | None, Some v ->
              max_var := max !max_var (Variable.type_of v);
              (* Should be changed with linked for faster results. *)
              if not (List.memq v !used_variables)
              then used_variables := v :: !used_variables
            | _, _ ->
              Config.internal_error "[process_session.ml >> apply_snd_subst_on_block] The function Term.iter_variables_and_axioms should return one filled option."
          ) r';
        ) block.recipes;

        {block with used_axioms = !used_axioms; maximal_var = !max_var; used_variables = !used_variables }
      ) l
    )

  let is_authorised (block_list:t list) (cur_block:t) (snd_subst:(snd_ord,axiom) Subst.t) : bool * snd_ord_variable list =
    let block_list_upd =
      apply_snd_subst_on_block snd_subst (cur_block::block_list) in
    (* Printf.printf "AUTHORISATION CHECK:\n";
    List.iter (fun b -> Printf.printf "%s\n" (print b)) block_list_upd; *)
    match block_list with
    | [] -> true, []
    | _ ->
      let rec explore_block block_list =
        match block_list with
        | []
        | [_] -> true, []
        | block::q ->
            let is_faulty, vars_to_check = is_faulty_block block q in
            if is_faulty
            then false, []
            else
              let r, vars_to_check2 = explore_block q in
              if r
              then
                let vars_to_check3 =
                  List.fold_left (fun acc v ->
                    if List.memq v acc
                    then acc
                    else v::acc
                  ) vars_to_check2 vars_to_check
                in
                true,vars_to_check3
              else false, []
      in
      explore_block block_list_upd

  let rec match_list f_next block_l1 block_l2 = match block_l1, block_l2 with
    | [], [] -> f_next ()
    | _, [] | [],_ -> Config.internal_error "[process_sessions.ml >> Block.match_list] Number of blocks should be equal."
    | b1::q1, b2::q2 ->
        match_list (fun () ->
          Label.match_label (List.hd b1.label) (List.hd b2.label);
          f_next ()
        ) q1 q2

  let match_labels f_next block_l1 block_l2 =
    Config.debug (fun () -> Config.print_in_log "match_labels\n");
    if !Label.linked_labels <> []
    then
      begin
        Config.debug (fun () -> Config.print_in_log "[Block.match_labels] There should not be any linked labels.\n");
        Config.internal_error "[Block.match_labels] There should not be any linked labels.";

      end;

    (* The two block list are in reverse order so we need to start matching from the end. *)
    Label.auto_cleanup (fun () ->
      match_list (fun () -> f_next !Label.linked_labels) block_l1 block_l2
    )

  type subsume_result =
    | Left
    | Right
    | Both

  let rec check_block_labels = function
    | [] -> ()
    | lbl1::q ->
        let linked_lbl1 = match lbl1.Label.link with
          | None -> Config.internal_error "[Block.check_block_labels] Labels should be linked."
          | Some lbl1' -> lbl1'
        in

        List.iter (fun lbl2 ->
          let linked_lbl2 = match lbl2.Label.link with
            | None -> Config.internal_error "[Block.check_block_labels] Labels should be linked (2)."
            | Some lbl2' -> lbl2'
          in

          if (Label.independent lbl1 lbl2) <> (Label.independent linked_lbl1 linked_lbl2)
          then raise No_Match
        ) q;

        check_block_labels q

  let rec check_process_labels subsume_result block_labels = function
    | [] -> subsume_result
    | p_lbl::q ->
        let linked_p_lbl = match p_lbl.Label.link with
          | None -> Config.internal_error "[Block.check_block_labels] Labels should be linked."
          | Some lbl -> lbl
        in

        let subsume_result1 =
          List.fold_left (fun subsume_result' b_lbl ->
            let linked_b_lbl = match b_lbl.Label.link with
              | None -> Config.internal_error "[Block.check_block_labels] Labels should be linked (2)."
              | Some lbl -> lbl
            in

            match subsume_result' with
              | Left ->
                  let c = Label.independent linked_b_lbl linked_p_lbl in
                  if c = 1 || (Label.independent b_lbl p_lbl = c)
                  then Left
                  else raise No_Match
              | Right ->
                  let c = Label.independent b_lbl p_lbl in
                  if c = 1 || (Label.independent linked_b_lbl linked_p_lbl = c)
                  then Right
                  else raise No_Match
              | Both ->
                  let c = Label.independent b_lbl p_lbl in
                  let c_linked = Label.independent linked_b_lbl linked_p_lbl in
                  if c = c_linked
                  then Both
                  else
                    if c_linked = 1
                    then Left
                    else if c = 1
                    then Right
                    else raise No_Match
          ) subsume_result block_labels
        in
        check_process_labels subsume_result1 block_labels q

  let check_labels labels_block labels_process =
    check_block_labels labels_block;

    not (check_process_labels Both labels_block labels_process = Right)

  (******* Display ********)

  let display out block =
    let str_label_list = match block.label with
      | [] -> Config.internal_error "[process_session.ml >> Block.display] The block should contain at least one label."
      | [lbl] -> Label.display lbl
      | _ ->
          Printf.sprintf "%s %s %s"
            (lcurlybracket out)
            (display_list Label.display "; " block.label)
            (rcurlybracket out)
    in
    let str_bound_axioms = match out, block.bounds_axiom with
      | _ , None -> ""
      | Latex, Some(ax_min,ax_max) ->
          Printf.sprintf ", \\mathsf{ax}_{%d \\rightarrow %d}" ax_min ax_max
      | HTML, Some(ax_min,ax_max) ->
          Printf.sprintf ", <span class=\"mathsf\">ax</span><sub>%d %s %d</sub>" ax_min (rightarrow HTML) ax_max
      | _,Some(ax_min,ax_max) ->
          Printf.sprintf ", ax_%d %s ax_%d" ax_min (rightarrow out) ax_max
    in

    let str_recipes =
      if block.recipes = []
      then ""
      else
        Printf.sprintf ", %s %s %s"
          (lcurlybracket out)
          (display_list (fun r -> Variable.display out Recipe r) "; " block.recipes)
          (rcurlybracket out)
    in

    (lbrace out)^str_label_list^str_bound_axioms^str_recipes^(rbrace out)
end

(* multisets of unacessible private channels *)
module Channel = struct
  type t =
    | Symbol of symbol
    | Name of name

  let compare (x:t) (y:t) : int =
    match x,y with
    | Symbol f, Symbol g -> Symbol.order f g
    | Name n, Name m -> Name.order n m
    | Symbol _, _ -> -1
    | Name _, _ -> -1

  let equal (c:t) (d:t) : bool =
    match c,d with
    | Symbol f, Symbol g -> Symbol.is_equal f g
    | Name n, Name m -> Name.is_equal n m
    | _, _ -> false

  let is_public (c:t) : bool =
    match c with
    | Symbol f -> Symbol.is_public f
    | Name _ -> false

  let to_string (c:t) : string =
    let b = is_public c in
    let display =
      match c with
      | Symbol f -> Symbol.display Terminal f
      | Name n -> Name.display Terminal n in
    if b then display
    else Printf.sprintf "<%s>" display

  let from_term (t:protocol_term) : t =
    if Term.is_function t then Symbol (Term.root t)
    else if Term.is_name t then Name (Term.name_of t)
    else (
      Printf.printf "Error! The term %s is used as a channel. Only public/private [constants] and [new names] are supported as channels for queries of equivalence by session.\n" (Term.display Terminal Protocol t);
      exit 0
    )

  let apply_renaming (rho:Name.Renaming.t) (c:t) : t =
    match c with
    | Symbol _ -> c
    | Name n ->
      Name (Term.name_of (Name.Renaming.apply_on_terms rho (Term.of_name n) (fun x f -> f x)))

  let match_channels t1 t2 = match t1,t2 with
    | Symbol ch1, Symbol ch2 when Term.Symbol.is_equal ch1 ch2 -> ()
    | Name n1, Name n2 -> match_names n1 n2
    | _ -> raise No_Match

  type elt = t

  module Set = struct
    include Set.Make(struct type t = elt let compare = compare end)
    let apply_renaming rho set =
      map (apply_renaming rho) set
  end

  (******* Display ********)

  let display out = function
    | Symbol f -> Symbol.display out f
    | Name n -> Name.display out n
end

(* a module for labelled processes *)
module Labelled_process = struct
  type t = {
    proc : plain;
    label : Label.t option; (* None if the label has not been attributed yet *)
  }
  and plain =
    | Start of t * id (* a symbol that will only be found at the very toplevel of the initial processes, for convinience. Treated as an input action. *)
    | Input of Channel.t * fst_ord_variable * t * Channel.Set.t * id
    | Output of Channel.t * protocol_term * t * Channel.Set.t * id
    | OutputSure of Channel.t * protocol_term * t * Channel.Set.t * id
    | If of protocol_term * protocol_term * t * t
    | Let of protocol_term * protocol_term * protocol_term * t * t
    | New of name * t
    | Par of t list
    | Bang of bang_status * t list * t list (* The two lists model the replicated processes, the first one being reserved for processes where symmetries are temporarily broken due to the execution of outputs. *)
  and id = int
  and bang_status =
    | Strong (* symmetry up to structural equivalence *)
    | Partial (* symmetry up to channel renaming, or obtained after refactorisation during the analysis. Can only be used for enumerating the traces to be matched, and not for enumerating the traces that match them *)

  let nil (p:t) : bool =
    match p.proc with
    | Par []
    | Bang (_,[],[]) -> true
    | _ -> false

  let rec occurs v proc = match proc.proc with
    | Start(p,_)
    | Input(_,_,p,_,_)
    | New(_,p) -> occurs v p
    | Output(_,t,p,_,_)
    | OutputSure(_,t,p,_,_) -> var_occurs v t || occurs v p
    | If(u1,u2,p1,p2) ->
        var_occurs v u1 || var_occurs v u2 || occurs v p1 || occurs v p2
    | Let(u1,u2,u3,p1,p2) ->
        var_occurs v u1 || var_occurs v u2 || var_occurs v u3 || occurs v p1 || occurs v p2
    | Par l -> List.exists (occurs v) l
    | Bang(_,l1,l2) ->  List.exists (occurs v) l1 || List.exists (occurs v) l2

  let rec contain_only_public_channel proc = match proc.proc with
    | Input(ch,_,_,_,_)
    | Output(ch,_,_,_,_)
    | OutputSure(ch,_,_,_,_) when not (Channel.is_public ch) -> false
    | Start(p,_)
    | Input(_,_,p,_,_)
    | New(_,p)
    | Output(_,_,p,_,_)
    | OutputSure(_,_,p,_,_) -> contain_only_public_channel p
    | If(_,_,p1,p2)
    | Let(_,_,_,p1,p2) ->
        contain_only_public_channel p1 && contain_only_public_channel p2
    | Par l -> List.for_all contain_only_public_channel l
    | Bang(_,l1,l2) ->
        List.for_all contain_only_public_channel l1 &&
        List.for_all contain_only_public_channel l2

  let rec get_improper_labels f_next imp_labels imp_procs proc =  match proc.proc with
    | Start _
    | Output _
    | OutputSure _
    | If _
    | Let _
    | New _ -> f_next imp_labels imp_procs proc
    | Input(_,_,{ proc = Par []; _},_,_)
    | Input(_,_,{ proc = Bang(_,[],[]); _},_,_) ->
        begin match proc.label with
          | None -> Config.internal_error "[process_session.ml] Should have a label"
          | Some lbl -> f_next (lbl::imp_labels) (proc::imp_procs) { proc = Par [] ; label = None }
        end
    | Input _ -> f_next imp_labels imp_procs proc
    | Par l_proc ->
        get_improper_labels_list (fun imp_labels1 imp_procs1 l_proc1 ->
          f_next imp_labels1 imp_procs1 { proc = Par l_proc1; label = None }
        ) imp_labels imp_procs l_proc
    | Bang(b,[],l_proc) ->
        get_improper_labels_list (fun imp_labels1 imp_procs1 l_proc1 ->
          match l_proc1 with
            | [] | [_] ->  f_next imp_labels1 imp_procs1 { proc = Par l_proc1; label = None }
            | _ -> f_next imp_labels1 imp_procs1 { proc = Bang(b,[],l_proc1); label = None }
        ) imp_labels imp_procs l_proc
    | _ -> Config.internal_error "[process_session.ml >> get_improper_labels] The function should only be applied before a focus step."

  and get_improper_labels_list f_next imp_labels imp_procs = function
    | [] -> f_next imp_labels imp_procs []
    | proc::q ->
        get_improper_labels (fun imp_labels1 imp_procs1 proc' ->
          get_improper_labels_list (fun imp_labels2 imp_procs2 q' ->
            if proc'.proc = Par []
            then f_next imp_labels2 imp_procs2 q'
            else f_next imp_labels2 imp_procs2 (proc'::q')
          ) imp_labels1 imp_procs1 q
        ) imp_labels imp_procs proc

  let empty (lab:Label.t) : t = {proc = Par []; label = Some lab}

  let get_label (p:t) : Label.t =
    match p.label with
    | None -> Config.internal_error "[process_session.ml >> Label.Process.get_label] Unassigned label."
    | Some lab -> lab
  let get_proc (p:t) : plain = p.proc

  (* formatting function *)
  let bold_red s = Printf.sprintf "\\033[1;31m%s\\033[0m" s
  let tab i = Func.loop (fun _ s -> s^"   ") "" 1 i
  let string_of_bang b n =
    match b with
    | Strong -> Printf.sprintf "!^%d" n
    | Partial -> Printf.sprintf "!A^%d" n
  let string_of_broken_bang b =
    match b with
    | Strong -> "X"
    | Partial -> "Xc"

  (* conversion into a string *)
  let print ?labels:(print_labs:bool=false) ?solution:(fst_subst:(fst_ord, name) Subst.t=Subst.identity) ?highlight:(idh:id list=[]) (p:t) : string =
    let on_id i s = if List.mem i idh then bold_red s else s in
    let semicolon s = if s = "" then "" else ";" in
    let rec browse sol bound indent p f_cont =
      let lab delim =
        match p.label with
        | None -> ""
        | Some _ when not print_labs -> ""
        | Some l -> Printf.sprintf "lab=%s%s" (Label.to_string l) delim in
      match p.proc with
      | Start (pp,id) ->
        browse sol bound indent pp (fun s ->
          let instr = on_id id (Printf.sprintf "start(%s)" (lab "")) in
          f_cont (Printf.sprintf "\n%s%s%s%s" (tab indent) instr (semicolon s) s)
        )
      | Input(c,x,pp,_,id) ->
        let sol = Subst.restrict sol (fun y -> not (Variable.is_equal x y)) in
        browse sol (x::bound) indent pp (fun s ->
          let instr =
            on_id id (Printf.sprintf "in(%s%s,%s)" (lab ",") (Channel.to_string c) (Variable.display Terminal Protocol x)) in
          f_cont (Printf.sprintf "\n%s%s%s%s" (tab indent) instr (semicolon s) s)
        )
      | Output(c,t,pp,_,_) ->
        let t =
          Subst.apply sol t (fun t f -> Rewrite_rules.normalise (f t)) in
        browse sol bound indent pp (fun s ->
          f_cont (Printf.sprintf "\n%sout(%s%s,%s)%s%s" (tab indent) (lab ",") (Channel.to_string c) (Term.display Terminal Protocol t) (semicolon s) s)
        )
      | OutputSure(c,t,pp,_,id) ->
        let t =
          Subst.apply sol t (fun t f -> Rewrite_rules.normalise (f t)) in
        browse sol bound indent pp (fun s ->
          let instr =
            on_id id (Printf.sprintf "out(%s%s,%s)" (lab ",") (Channel.to_string c) (Term.display Terminal Protocol t)) in
          f_cont (Printf.sprintf "\n%s%s%s%s" (tab indent) instr (semicolon s) s)
        )
      | If(u,v,p1,p2) ->
        let (u,v) =
          Subst.apply sol (u,v) (fun (u,v) f ->
            Rewrite_rules.normalise (f u),Rewrite_rules.normalise (f v)
          ) in
        browse sol bound (indent+1) p1 (fun s1 ->
          browse sol bound (indent+1) p2 (fun s2 ->
            let else_branch =
              if s2 = "" then ""
              else Printf.sprintf "\n%selse%s" (tab indent) s2 in
            f_cont (Printf.sprintf "\n%sif %s = %s then%s%s" (tab indent) (Term.display Terminal Protocol u) (Term.display Terminal Protocol v) s1 else_branch)
          )
        )
      | Let(u,_,v,p1,p2) ->
        let new_vars = get_vars_not_in Protocol u bound in
        let sol_restr =
          Subst.restrict sol (fun x -> not (List.mem x new_vars)) in
        let (u,v) =
          Subst.apply sol_restr (u,v) (fun (u,v) f ->
            Rewrite_rules.normalise (f u),Rewrite_rules.normalise (f v)
          ) in
        browse sol bound (indent+1) p2 (fun s2 ->
          if s2 = "" then
            browse sol_restr (List.rev_append new_vars bound) indent p1 (fun s1 ->
              f_cont (Printf.sprintf "\n%slet %s = %s in%s" (tab indent) (Term.display Terminal Protocol u) (Term.display Terminal Protocol v) s1)
            )
          else
            browse sol_restr (List.rev_append new_vars bound) (indent+1) p1 (fun s1 ->
              f_cont (Printf.sprintf "\n%slet %s = %s in%s\n%selse%s" (tab indent) (Term.display Terminal Protocol u) (Term.display Terminal Protocol v) s1 (tab indent) s2)
            )
        )
      | New(n,pp) ->
        browse sol bound indent pp (fun s ->
          f_cont (Printf.sprintf "\n%snew %s%s%s" (tab indent) (Name.display Terminal n) (semicolon s) s)
        )
      | Par []
      | Bang(_,[],[]) -> f_cont ""
      | Par [p]
      | Bang(_,[p],[])
      | Bang(_,[],[p]) -> browse sol bound indent p f_cont
      | Par (p::t) ->
        browse sol bound (indent+1) p (fun s ->
          browse_list sol bound "|" indent t (fun sl ->
            f_cont (Printf.sprintf "%s%s" s sl)
          )
        )
      | Bang(b,[],p::t) ->
        browse sol bound (indent+1) p (fun s ->
          f_cont (Printf.sprintf "\n%s%s%s" (tab indent) (string_of_bang b (List.length t+1)) s)
        )
      | Bang(b,p::t,[]) ->
        browse sol bound (indent+1) p (fun s ->
          browse_list sol bound (string_of_broken_bang b) indent t (fun sl ->
            f_cont (Printf.sprintf "%s%s" s sl)
          )
        )
      | Bang(b,p1::t1,p2::t2) ->
        browse sol bound (indent+1) p1 (fun s1 ->
          browse sol bound (indent+1) p2 (fun s2 ->
            browse_list sol bound (string_of_broken_bang b) indent t1 (fun sl1 ->
              f_cont (Printf.sprintf "%s%s\n%s%s%s" s1 sl1 (tab indent) (string_of_bang b (List.length t2+1)) s2)
            )
          )
        )

      and browse_list sol bound delim indent l f_cont =
        match l with
        | [] -> f_cont ""
        | p :: t ->
          browse sol bound (indent+1) p (fun s ->
            browse_list sol bound delim indent t (fun sl ->
              f_cont (Printf.sprintf "\n%s%s%s%s" (tab indent) delim s sl)
            )
          ) in

    browse fst_subst [] 0 p (fun s -> s)

  (* checks whether a normalised process contains an executable public output. Cannot be run on a start process *)
  let rec contains_public_output_toplevel (lp:t) : bool =
    match lp.proc with
    | Input _ -> false
    | OutputSure (c,_,_,_,_) -> Channel.is_public c
    | Par l -> List.exists contains_public_output_toplevel l
    | Bang (_,l1,l2) -> List.exists contains_public_output_toplevel (l1@l2)
    | Start _ -> Config.internal_error "[process_session.ml >> contains_output_toplevel] Unexpected Start constructor."
    | _ -> Config.internal_error "[process_session.ml >> contains_output_toplevel] Should only be applied on normalised processes."

  let not_pure_io_toplevel (lp:t) : bool =
    match lp.proc with
    | Input _
    | OutputSure _ -> false
    | Par _
    | Bang _ -> true
    | Start _ -> Config.internal_error "[process_session.ml >> not_pure_io] Unexpected Start constructor."
    | _ -> Config.internal_error "[process_session.ml >> not_pure_io] Should only be applied on normalised processes."

  let rec map_term proc f = match proc.proc with
    | Start(p,id) -> {proc with proc = Start(map_term p f,id) }
    | Input(ch,x,p,ch_set,id) -> {proc with proc = Input(ch,x,map_term p f ,ch_set,id) }
    | Output(ch,t,p,ch_set,id) -> {proc with proc = Output(ch,f t, map_term p f, ch_set,id)}
    | OutputSure(ch,t,p,ch_set,id) -> {proc with proc = OutputSure(ch,f t, map_term p f, ch_set, id)}
    | If(u,v,p1,p2) -> { proc with proc = If(f u, f v, map_term p1 f, map_term p2 f) }
    | Let(u,u',v,p1,p2) -> { proc with proc = Let(f u, f u', f v, map_term p1 f, map_term p2 f) }
    | New(n,p) -> { proc with proc = New(n,map_term p f) }
    | Par p_list -> { proc with proc = Par(List.map (fun p -> map_term p f) p_list) }
    | Bang(b,p_list,p_list') ->
      { proc with proc = Bang(b,List.map (fun p -> map_term p f) p_list,List.map (fun p -> map_term p f) p_list') }

  let apply_substitution subst p = Subst.apply subst p map_term

  module Skeleton = struct
    type t = { (* each component (ch,mult,l) indicates [mult] action on the channel [ch], on labels of last positions in [l] *)
      input_skel : (Channel.t * int * int list) list ;
      output_skel : (Channel.t * int * int list) list ;
      private_input_skel : int * int list ;
      private_output_skel : int * int list ;
    }
    let empty =
      { input_skel = [];
        output_skel = [];
        private_input_skel = (0,[]);
        private_output_skel = (0,[]) }

    let rec add_in_process_skel_symbol ch label skel_list =
      match skel_list with
      | [] -> [ch,1,[Label.last_position label]]
      | ((ch',size,list_label) as t)::q ->
        let cmp_ch = Channel.compare ch ch' in
        if cmp_ch < 0 then (ch,1,[Label.last_position label])::skel_list
        else if cmp_ch = 0 then (ch',size+1,Label.last_position label::list_label)::q
        else t::(add_in_process_skel_symbol ch label q)
    let add_action is_out ch label proc_skel =
      if is_out then
        if Channel.is_public ch then
          {proc_skel with output_skel = add_in_process_skel_symbol ch label proc_skel.output_skel}
        else
          let (nb,l) = proc_skel.private_output_skel in
          {proc_skel with private_output_skel = (nb+1,Label.last_position label::l)}
      else if Channel.is_public ch then
        {proc_skel with input_skel = add_in_process_skel_symbol ch label proc_skel.input_skel}
      else
        let (nb,l) = proc_skel.private_input_skel in
        {proc_skel with private_input_skel = (nb+1,Label.last_position label::l)}

    let print_list_skel (tag:string) (s:(Channel.t * int * int list) list) : string =
      List.fold_left (fun s (ch,mult,_) ->
        Printf.sprintf "%s, %d %s on %s" s mult tag (Channel.to_string ch)
      ) "" s

    let print (s:t) : string =
      Printf.sprintf "%s%s, %d private inputs, %d private outputs" (print_list_skel "inputs" s.input_skel) (print_list_skel "outputs" s.output_skel) (fst s.private_input_skel) (fst s.private_output_skel)

    let rec link_lists l1 l2 accu =
      match l1,l2 with
      | [],[] -> Some accu
      | (ch1,mult1,pos_list1)::t1, (ch2,mult2,pos_list2)::t2 when Channel.equal ch1 ch2 && mult1 = mult2 ->
        link_lists t1 t2 ((pos_list1,pos_list2)::accu)
      | _ -> None

    let link s1 s2 =
      match link_lists s1.input_skel s2.input_skel [] with
      | None -> None
      | Some ac1 ->
        match link_lists s1.output_skel s2.output_skel ac1 with
        | None -> None
        | Some ac2 ->
          match s1.private_input_skel, s2.private_input_skel with
          | (mult1,in_list1),(mult2,in_list2) when mult1 = mult2 ->
            begin match s1.private_output_skel, s2.private_output_skel with
              | (mult1',out_list1),(mult2',out_list2) when mult1' = mult2' ->
                let ac3 =
                  if mult1 = 0 then ac2 else (in_list1,in_list2)::ac2 in
                let ac4 =
                  if mult1' = 0 then ac3 else (out_list1,out_list2)::ac3 in
                Some ac4
              | _ -> None
            end
          | _ -> None
  end

  let labelling (prefix:Label.t) (lbl_proc:t) : t * Skeleton.t =

    let rec assign process_skel next_i lbl_proc f_cont =
      match lbl_proc.proc with
      | OutputSure(c,_,_,_,_) ->
        let label = Label.add_position prefix next_i in
        let process_skel1 = Skeleton.add_action true c label process_skel in
        f_cont {lbl_proc with label = Some label} process_skel1 (next_i+1)
      | Input(c,_,_,_,_) ->
        let label = Label.add_position prefix next_i in
        let process_skel1 = Skeleton.add_action false c label process_skel in
        f_cont { lbl_proc with label = Some label } process_skel1 (next_i+1)
      | Par list_lbl_proc ->
        assign_list process_skel next_i list_lbl_proc (fun list_lbl_proc1 process_skel1 next_i1 ->
          f_cont { proc = Par list_lbl_proc1; label = None } process_skel1 next_i1
        )
      | Bang(b,[],list_lbl_proc) ->
        assign_list process_skel next_i list_lbl_proc (fun list_lbl_proc1 process_skel1 next_i1 ->
          f_cont { proc = Bang(b,[],list_lbl_proc1); label = None } process_skel1 next_i1
        )
      | _ -> Config.internal_error "[process_sessions.ml >> labelling] Labelling is done only on normalised process without broken symmetry."

    and assign_list process_skel next_i list_proc f_cont =
      match list_proc with
      | [] -> f_cont [] process_skel next_i
      | p :: t ->
        assign process_skel next_i p (fun p1 process_skel1 next_i1 ->
          assign_list process_skel1 next_i1 t (fun t1 process_skel2 next_i2 ->
            f_cont (p1 :: t1) process_skel2 next_i2
          )
        )
    in

    Config.debug (fun () ->
      if lbl_proc.label <> None then
        Config.internal_error "[process_session.ml >> labelling] Already labelled process."
    );
    match lbl_proc.proc with
    | Input(ch,_,_,_,_) ->
      { lbl_proc with label = Some prefix },
      Skeleton.add_action false ch prefix Skeleton.empty
    | OutputSure(ch,_,_,_,_) ->
      { lbl_proc with label = Some prefix },
      Skeleton.add_action true ch prefix Skeleton.empty
    | Par _
    | Bang _ ->
      assign Skeleton.empty 0 lbl_proc (fun proc proc_skel _ -> proc,proc_skel)
    | Output _
    | If _
    | Let _
    | New _ -> Config.internal_error "[process_session.ml >> labelling] Only normalised processes should be assigned with labels."
    | Start _ -> Config.internal_error "[process_session.ml >> labelling] Unexpected Start constructor."

  let elements ?(init=[]) (lp:t) : t list =
    let rec gather accu lp = match lp with
      | {proc = Par l; _} -> List.fold_left gather accu l
      | {proc = Bang (_,l1,l2); _} -> List.fold_left gather (List.fold_left gather accu l1) l2
      | _ -> lp :: accu in
    gather init lp

  (* application of renaming. Useful for generating fresh copies of processes *)
  let apply_renaming_on_term (rho:Name.Renaming.t) (t:Term.protocol_term) : Term.protocol_term =
    Name.Renaming.apply_on_terms rho t (fun x f -> f x)

  let apply_alpha_on_term (rho:(fst_ord, name) Variable.Renaming.t) (t:Term.protocol_term) : Term.protocol_term =
    Variable.Renaming.apply_on_terms rho t (fun x f -> f x)

  let fresh_vars_and_renaming (accu:(fst_ord, name) Variable.Renaming.t) (l:fst_ord_variable list) : (fst_ord, name) Variable.Renaming.t * fst_ord_variable list =
    List.fold_left (fun (accu,l) x ->
      let xx = Variable.fresh_from x in
      Variable.Renaming.compose accu x xx, x::l
    ) (accu,[]) l

  (* generates several copies of a process with freshly renamed New names, input variables, and positions *)
  let fresh_copy (nb:int) (p:t) (id:id) (f_cont:id->Channel.Set.t->t list->'a) : 'a =
    let rec browse rho_v rho_n bound_vars p id f_cont =
      let apply t = apply_renaming_on_term rho_n (apply_alpha_on_term rho_v t) in
      match p.proc with
      | Input(c,x,p,nontop_channels,_) ->
        Config.debug (fun () ->
          if Variable.quantifier_of x != Free
          then Config.internal_error "[process_sessions.ml >> fresh_copy] All variables should be free."
        );
        let nontop_channels_fresh =
          Channel.Set.apply_renaming rho_n nontop_channels in
        let xx = Variable.fresh_from x in
        browse (Variable.Renaming.compose rho_v x xx) rho_n (x::bound_vars) p (id+1) (fun id_max _ p_fresh ->
          f_cont id_max nontop_channels_fresh {proc = Input(Channel.apply_renaming rho_n c,xx,p_fresh,nontop_channels_fresh,id); label = None}
        )
      | Output(c,t,p,nontop_channels,_) ->
        let nontop_channels_fresh =
          Channel.Set.apply_renaming rho_n nontop_channels in
        browse rho_v rho_n bound_vars p (id+1) (fun id_max _ p_fresh ->
          f_cont id_max nontop_channels_fresh {proc = Output(Channel.apply_renaming rho_n c,apply t,p_fresh,nontop_channels_fresh,id); label = None}
        )
      | OutputSure _ ->
        Config.internal_error "[process_session.ml >> fresh_copy] Outputs should not be sure before the analysis starts."
      | If(u,v,p1,p2) ->
        let uu = apply u in
        let vv = apply v in
        browse rho_v rho_n bound_vars p1 id (fun id1 chans1 p1_fresh ->
          browse rho_v rho_n bound_vars p2 id1 (fun id2 chans2 p2_fresh ->
            f_cont id2 (Channel.Set.union chans1 chans2) {proc = If(uu,vv,p1_fresh,p2_fresh); label = None}
          )
        )
      | Let(u,_,v,p1,p2) ->
        (* VINCENT: Improve that part. I think we could have something more linear. Add that in terms.ml. I leave the warning for now. *)
        let bound_vars_u = Term.get_vars_not_in Protocol u bound_vars in
        let fresh' = Variable.Renaming.fresh Protocol bound_vars_u Universal in
        let (rho_v',new_bounds) = fresh_vars_and_renaming rho_v bound_vars_u in
        let uu =
          apply_renaming_on_term rho_n (apply_alpha_on_term rho_v' u) in
        let uu' = apply_alpha_on_term fresh' (apply u) in
        let vv = apply v in
        browse rho_v' rho_n (List.rev_append new_bounds bound_vars) p1 id (fun id1 chans1 p1_fresh ->
          browse rho_v rho_n bound_vars p2 id1 (fun id2 chans2 p2_fresh ->
            f_cont id2 (Channel.Set.union chans1 chans2) {proc = Let(uu,uu',vv,p1_fresh,p2_fresh); label = None}
          )
        )
      | New(n,p) ->
        let nn = Name.fresh_from n in
        browse rho_v (Name.Renaming.compose rho_n n nn) bound_vars p id (fun id_max chans p_fresh ->
          f_cont id_max chans {proc = New(nn,p_fresh); label = None}
        )
      | Par l ->
        browse_list rho_v rho_n bound_vars l id (fun id_max chans l_fresh ->
          f_cont id_max chans {proc = Par l_fresh; label = None}
        )
      | Bang(Strong,[],l) ->
        browse_list rho_v rho_n bound_vars l id (fun id_max chans l_fresh ->
          f_cont id_max chans {proc = Bang(Strong,[],l_fresh); label = None}
        )
      | Bang _ -> Config.internal_error "[process_session.ml >> fresh_copy] Unexpected type of bang."
      | Start _ -> Config.internal_error "[process_session.ml >> fresh_copy] Unexpected Start constructor."

    and browse_list rho_v rho_n bound_vars l id f_cont = match l with
      | [] -> f_cont id Channel.Set.empty []
      | p :: t ->
          browse rho_v rho_n bound_vars p id (fun id_max chans p_fresh ->
            browse_list rho_v rho_n bound_vars t id_max (fun id_l chans_l l_fresh ->
              f_cont id_l (Channel.Set.union chans chans_l) (p_fresh::l_fresh)
            )
          )
    in

    let rec browse_iter nb p id f_cont =
      if nb = 0 then f_cont id Channel.Set.empty []
      else
        browse Variable.Renaming.identity Name.Renaming.identity [] p id (fun id_max chans p_fresh ->
          browse_iter (nb-1) p id_max (fun id_final chans_final l_fresh ->
            f_cont id_final (Channel.Set.union chans chans_final) (p_fresh::l_fresh)
          )
        ) in

    browse_iter nb p id f_cont

  (* conversion from expansed processes
  TODO. include a check that no names used as private channels are output
  TODO. test this function (in particular the computation of the set of in-depth private channels) *)
  let of_expansed_process ?(preprocessing:t->t=fun x->x) (p:Process.expansed_process) : t =
    let rec browse bound_vars p id f_cont =
      match p with
      | Process.Nil ->
        f_cont id Channel.Set.empty {proc = Par []; label = None}
      | Process.Output(ch,t,pp) ->
        browse bound_vars pp (id+1) (fun id_max chans p_conv ->
          let ch_conv = Channel.from_term ch in
          let new_chans =
            if Channel.is_public ch_conv then chans
            else Channel.Set.add ch_conv chans in
          f_cont id_max new_chans {proc = Output(ch_conv,t,p_conv,chans,id); label = None}
        )
      | Process.Input(ch,x,pp) ->
        browse (x::bound_vars) pp (id+1) (fun id_max chans p_conv ->
          let ch_conv = Channel.from_term ch in
          let new_chans =
            if Channel.is_public ch_conv then chans
            else Channel.Set.add ch_conv chans in
          f_cont id_max new_chans {proc = Input(ch_conv,x,p_conv,chans,id); label = None}
        )
      | Process.IfThenElse(t1,t2,pthen,pelse) ->
        browse bound_vars pthen id (fun id1 chans1 pthen ->
          browse bound_vars pelse id1 (fun id2 chans2 pelse ->
            f_cont id2 (Channel.Set.union chans1 chans2) {proc = If(t1,t2,pthen,pelse); label = None}
          )
        )
      | Process.Let(t1,t2,pthen,pelse) ->
        let bound_vars_t1 = Term.get_vars_not_in Protocol t1 bound_vars in
        let fresh = Variable.Renaming.fresh Protocol bound_vars_t1 Universal in
        let tt1 = Variable.Renaming.apply_on_terms fresh t1 (fun x f -> f x) in
        browse (List.rev_append bound_vars_t1 bound_vars) pthen id (fun id1 chans1 pthen ->
          browse bound_vars pelse id1 (fun id2 chans2 pelse ->
            f_cont id2 (Channel.Set.union chans1 chans2) {proc = Let(t1,tt1,t2,pthen,pelse); label = None}
          )
        )
      | Process.New(n,pp) ->
        browse bound_vars pp id (fun id_max chans p_conv ->
          f_cont id_max chans {proc = New(n,p_conv); label = None}
        )
      | Process.Par lp ->
        browse_list bound_vars lp id (fun id_max chans l_conv ->
          match l_conv with
          | [p] -> f_cont id_max chans p
          | l -> f_cont id_max chans {proc = Par l; label = None}
        )
      | Process.Choice _ -> Config.internal_error "[process_session.ml >> plain_process_of_expansed_process] *Choice* not implemented yet for equivalence by session."

    and browse_list bound_vars l id f_cont =
      match l with
      | [] -> f_cont id Channel.Set.empty []
      | (pp,i) :: t ->
        browse bound_vars pp id (fun id_max chans1 p_conv ->
          browse_list bound_vars t id_max (fun id_l chans2 l_conv ->
            let chans = Channel.Set.union chans1 chans2 in
            if i = 1 then f_cont id_l chans (p_conv :: l_conv)
            else
              fresh_copy i p_conv id_l (fun id_final chans l_fresh ->
                f_cont id_final chans ({proc = Bang(Strong,[],l_fresh); label = None} :: l_conv)
              )
          )
        ) in

    browse [] p 1 (fun _ _ p_conv ->
      preprocessing {proc = Start (p_conv,0); label = Some Label.initial}
    )

  let of_process_list (l:t list) : t =
    match l with
    | [p] -> p
    | l -> {proc = Par l; label = None}

  (* browse executable inputs and outputs of a normalised process *)
  let unfold_with_leftovers (optim:bool) (accu:'a) (add_to_accu:t->t list->bool->'a->'a)  (p:t) (leftovers:t list) : 'a =
    let rec unfold forall accu leftovers p f_cont =
      match p.proc with
      | OutputSure _
      | Input _ ->
        f_cont (add_to_accu p leftovers forall accu)
      | Par l ->
        unfold_list forall accu leftovers l f_cont
      | Bang(_,[],[]) ->
        f_cont accu
      | Bang(_,_::_,_) ->
        Config.internal_error "[process_session.ml >> unfold_with_leftovers] Symmetries should not be broken."
      | Bang(b,[],pp::tl) ->
        let leftovers_pp = if tl = [] then leftovers
        else {proc = Bang(b,[],tl); label = None}::leftovers in
        if b = Strong || optim then unfold forall accu leftovers_pp pp f_cont
        else
          unfold forall accu leftovers_pp pp (fun accu  ->
            unfold_bang [pp] accu leftovers tl f_cont
          )
      | New _
      | If _
      | Let _
      | Output _ ->
        Config.internal_error "[process_session.ml >> unfold_with_leftovers] Unfolding should only be applied on normalised processes."
      | Start _ -> Config.internal_error "[process_session.ml >> unfold_with_leftovers] Unexpected Start constructor."

    and unfold_list forall accu leftovers l f_cont =
      match l with
      | [] -> f_cont accu
      | pp :: t ->
        unfold forall accu (List.rev_append t leftovers) pp (fun accu1 ->
          unfold_list forall accu1 (pp::leftovers) t f_cont
        )

    and unfold_bang memo accu leftovers l f_cont =
      match l with
      | [] -> f_cont accu
      | pp :: t ->
        let leftovers_pp =
          {proc = Bang(Partial,[],List.rev_append memo t); label = None} :: leftovers in
        unfold false accu leftovers_pp pp (fun accu1 ->
          unfold_bang (pp::memo) accu1 leftovers t f_cont
        ) in

    unfold true accu leftovers p (fun accu -> accu)

  (******* Display ********)

  let retrieve_labels proc_list =

    let rec browse accu proc =
      let accu1 = match proc.label with
        | None -> accu
        | Some lbl -> lbl :: accu
      in
      match proc.proc with
        | Start _
        | Input _
        | Output _
        | OutputSure _
        | If _
        | Let _
        | New _ -> accu1
        | Par p_l -> List.fold_left browse accu1 p_l
        | Bang(_,p_l1,p_l2) ->
            let accu2 = List.fold_left browse accu1 p_l1 in
            List.fold_left browse accu2 p_l2
    in
    List.fold_left browse [] proc_list

  let fresh_display_id =
    let counter = ref 0 in
    let f () =
      incr counter;
      !counter
    in
    f

  let display out ?(tab=0) ?(out_ch=stdout) ?(label=true) ?(start=true) ?(hidden=false) ?(highlight=[]) ?(id=1) ?(id_link=1) proc = match out with
    | HTML ->
        let do_highlight str pos =
          if List.mem pos highlight
          then Printf.sprintf "<span class=\"highlight\">%s</span>" str
          else str
        in

        let display_subprocess tab str =
          Printf.fprintf out_ch "%s<div class=\"sub_process\">%s</div>\n" (create_tab tab) str
        in

        let rec browse tab proc =
          let str_label = match proc.label with
            | Some lbl when label -> Printf.sprintf " <span class=\"label\">[%s]</span>" (Label.display lbl)
            | _ -> ""
          in
          match proc.proc with
            | Start(p,pos) ->
                if start || label
                then display_subprocess tab ((do_highlight "start;" pos)^str_label);

                browse tab p
            | Input(ch,x,p,_,pos) ->
                let str = Printf.sprintf "in(%s,%s);" (Channel.display out ch) (Variable.display out Protocol x) in
                display_subprocess tab ((do_highlight str pos)^str_label);
                browse tab p
            | Output(ch,t,p,_,pos)
            | OutputSure(ch,t,p,_,pos) ->
                let str = Printf.sprintf "out(%s,%s);" (Channel.display out ch) (Term.display out Protocol t) in
                display_subprocess tab ((do_highlight str pos)^str_label);
                browse tab p
            | If(u,v,pthen,{ proc = Par []; _}) ->
                let str = Printf.sprintf "if %s = %s then" (Term.display out Protocol u) (Term.display out Protocol v) in
                display_subprocess tab str;
                browse tab pthen
            | If(u,v,pthen,pelse) ->
                let str_then = Printf.sprintf "if %s = %s then" (Term.display out Protocol u) (Term.display out Protocol v) in
                unfold tab str_then pthen;
                unfold tab "else" pelse;
            | Let(u,_,v,pthen,{ proc = Par []; _}) ->
                let str = Printf.sprintf "let %s = %s in" (Term.display out Protocol u) (Term.display out Protocol v) in
                display_subprocess tab str;
                browse tab pthen
            | Let(u,_,v,pthen,pelse) ->
                let str_then = Printf.sprintf "let %s = %s in" (Term.display out Protocol u) (Term.display out Protocol v) in
                unfold tab str_then pthen;
                unfold tab "else" pelse;
            | New(n,p) ->
                let str = Printf.sprintf "new %s;" (Name.display out n) in
                display_subprocess tab str;
                browse tab p
            | Par [] -> display_subprocess tab "0"
            | Par [p] -> browse tab p
            | Par (p::q_p) ->
                unfold tab "(" p;
                List.iter (unfold tab ") | (") q_p;
                display_subprocess tab ")"
            | Bang(Strong,[],[]) -> display_subprocess tab "0"
            | Bang(Strong,[],[p]) -> browse tab p
            | Bang(Strong,[],l_p) ->
                let str_label =
                  if label
                  then
                    let label_list = retrieve_labels l_p in
                    Printf.sprintf " <span class=\"label\">%s</span>" (display_list (fun lbl -> "["^(Label.display lbl)^"]") ", " label_list)
                  else ""
                in
                unfold tab (Printf.sprintf "!<sup>%d</sup> %s" (List.length l_p) str_label) (List.hd l_p)
            | Bang(Partial,lp,lp') -> browse tab { proc with proc = Par (lp@lp') }
            | Bang(Strong,lp,lp') -> browse tab { proc with proc = Par (lp@[{proc with proc = Bang(Strong,[],lp')}]) }

        and unfold tab str proc =
          let id_unfold = fresh_display_id () in
          let str = Printf.sprintf "%s <a id=\"unfold_button%d\" href=\"javascript:unfold_one('%d');\">&#9663;</a>" str id_unfold id_unfold in
          display_subprocess tab str;
          Printf.fprintf out_ch "%s<div class=\"unfold\" id=\"unfold%d\">\n" (create_tab tab) id_unfold;
          browse (tab+1) proc;
          Printf.fprintf out_ch "%s</div>\n" (create_tab tab)
        in
        let style =
          if hidden
          then " style=\"display:none;\""
          else ""
        in
        Printf.fprintf out_ch "%s<div class=\"process\" id=\"process%d\"%s><span class=\"mathcal\">P</span><sub>%d</sub> = \n" (create_tab tab) id_link style id;
        browse (tab+1) proc;
        Printf.fprintf out_ch "%s</div>\n" (create_tab tab)
    | _ -> Config.internal_error "[process_session.ml >> Labelled_process.display] Only HTML display is implemented yet."

  module Output = struct
    type data = {
      channel : Channel.t;
      term : protocol_term;
      optim : bool;
      lab : Label.t;
      context : t -> t;
      id : id;
    }

    (* Processes in given to [unfold_output] should all be normalised. Unfolding an output p in a Bang(b,l1,p::l2) will temporarily break the symmetry, i.e. p will be transferred into l1. *)
    let unfold ?(optim=false) (lp:t) : (t * data) list =

      let rec unfold accu p rebuild f_cont =
        match p.proc with
        | Input _ -> f_cont accu
        | OutputSure(c,_,_,_,_) when not (Channel.is_public c) -> f_cont accu
        | OutputSure(c,t,pp,_,id) ->
          let res = {
            channel = c;
            term = t;
            optim = false;
            lab = get_label p;
            context = rebuild;
            id = id;
          } in
          if optim then [pp,res]
          else f_cont ((pp,res)::accu)
        | If _
        | Let _
        | New _
        | Output _ ->
          Config.internal_error "[process_session.ml >> unfold_output] Should only be called on normalised processes."
        | Start _ -> Config.internal_error "[process_session.ml >> unfold_output] Unexpected Start constructor."
        | Par l ->
          let add_par l = rebuild {proc = Par l; label = None} in
          unfold_list accu [] l add_par f_cont
        | Bang(Partial,brok,l) ->
          let add_bang x =
            rebuild {proc = Bang(Partial,x,l); label = None} in
          let add_broken_bang x y =
            rebuild {proc = Bang(Partial,brok@x,y); label = None} in
          unfold_list accu [] brok add_bang (fun ac ->
            unfold_list_and_break ac [] l add_broken_bang f_cont
          )
        | Bang(Strong,brok,[]) ->
          let add_bang x =
            rebuild {proc = Bang(Strong,x,[]); label = None} in
          unfold_list accu [] brok add_bang f_cont
        | Bang(Strong,brok,(pp::t as l)) ->
          let add_bang x =
            rebuild {proc = Bang(Strong,x,l); label = None} in
          let add_broken_bang x =
            rebuild {proc = Bang(Strong,brok@[x],t); label = None} in
          unfold_list accu [] brok add_bang (fun ac ->
            unfold ac pp add_broken_bang f_cont
          )

      and unfold_list accu memo l rebuild f_cont =
        match l with
        | [] -> f_cont accu
        | pp :: t ->
          let add_list_to_rebuild p =
            rebuild (List.rev_append memo (if nil p then t else p::t)) in
          unfold accu pp add_list_to_rebuild (fun acp ->
            unfold_list acp (pp::memo) t rebuild f_cont
          )

      and unfold_list_and_break accu memo l rebuild f_cont =
        match l with
        | [] -> f_cont accu
        | pp :: t ->
          let add_list_to_rebuild p =
            rebuild (List.rev (if nil p then memo else p::memo)) t in
          unfold accu pp add_list_to_rebuild (fun acp ->
            unfold_list_and_break acp (pp::memo) t rebuild f_cont
          ) in

      (* final call. The list is reversed to unsure that smallest labels are unfolded first.
      NB. the code below is not equivalent to:
       unfold [] lp (fun p -> p) (fun accu -> match List.rev accu with [...]
      This is because unfold doesn't always call its continuation *)
      match unfold [] lp (fun p -> p) List.rev with
      | [] -> Config.internal_error "[process_session.ml >> unfold_output] No output could be unfolded."
      | (p,odata) :: t -> (p,{odata with optim = true}) :: t

    let rec restaure_sym (lp:t) : t =
      match lp.proc with
      | Input _
      | OutputSure _
      | Bang(_,[],_) -> (* no restauration needed *)
        lp
      | Par l -> {lp with proc = Par (List.map restaure_sym l)}
      | Bang(_,l1,l2) -> (* non trivial restauration: symmetry cannot be restaured to Strong *)
        {lp with proc = Bang (Partial,[],List.map restaure_sym l1 @ l2)}
      | Let _
      | If _
      | New _
      | Output _ -> Config.internal_error "[process_session.ml >> restaure_sym] Should only be applied on normalised processes."
      | Start _ -> Config.internal_error "[process_session.ml >> restaure_sym] Unexpected Start constructor."
  end

  module Input = struct
    type data = {
      channel : Channel.t;
      var : fst_ord_variable;
      optim : bool;
      lab : Label.t;
      leftovers : t list;
      id : id;
    }
  end

  module PrivateComm = struct
    type data = {
      channel : Channel.t;
      var : fst_ord_variable;
      term : protocol_term;
      optim : bool;
      labs : Label.t * Label.t;
      leftovers : t list;
      ids : id * id;
      conflict_toplevel : bool;
      conflict_future : bool;
    }

    (* inserts an internal communication in a sorted list, and checks for toplevel conflicts at the same time. Assumes that comm.toplevel = true *)
    let replace_conflict (p_in,p_out,data) b =
      (p_in,p_out,{data with conflict_toplevel = b})
    let rec insert (comm:t*t*data) (l:(t*t*data) list) : (t*t*data) list =
      match l with
      | [] -> [replace_conflict comm false]
      | ((_,_,data1) as h) :: t ->
        let (_,_,data) = comm in
        let comp_ch = Channel.compare data.channel data1.channel in
        if comp_ch < 0 then replace_conflict comm false :: l
        else if comp_ch > 0 then h :: insert comm t
        else if data1.conflict_toplevel then comm :: l
        else comm :: replace_conflict h true :: t


    let refine_conflict_future future_channels (p_in,p_out,data) =
      (p_in,p_out,{data with conflict_future = Channel.Set.mem data.channel future_channels})

    (* priority level of different types of internal communication *)
    let priority comm =
      let (_,_,data) = comm in
      match data.conflict_future, data.conflict_toplevel, data.optim with
      | true, _, false -> 0
      | true, _, true -> 1
      | false, true, false -> 2
      | false, true, true -> 3
      | false, false, _ -> 4

    (* decreasing order of priority *)
    let compare_comm comm1 comm2 =
      compare (priority comm2) (priority comm1)

    (* final operations on unfolded inputs and (sorted by decreasing priority) internal communication. Assigns the forall labels. *)
    let mark_forall optim l_in l_comm =
      let rec mark i l =
        match l with
        | [] -> []
        | ((p_in,p_out,data) as h) :: t ->
          if priority h = i then
            (p_in,p_out,{data with optim = true}) :: mark i t
          else if optim then []
          else List.rev_map (fun (p_in,p_out,data) -> (p_in,p_out,{data with optim = false})) t in
      match l_comm with
      | [] -> l_in,[]
      | h :: t ->
        let score = priority h in
        let input_list =
          if score >= 2 then
            if optim then []
            else List.rev_map (fun (p,data) -> (p,{data with Input.optim = false})) l_in
          else l_in in
        let comm_list =
          if score = 4 then
            if optim then [h]
            else h :: List.rev_map (fun (p_in,p_out,data) -> (p_in,p_out,{data with optim = false})) t
          else h :: mark score t in
        input_list,comm_list

    (* applies a substitution of an input variable in a process. No normalisation performed. *)
    let substitute (x:fst_ord_variable) (t:protocol_term) (p:t) : t =
      let subst = Subst.create Protocol x t in
      let apply t = Subst.apply subst t (fun x f -> f x) in
      let rec browse p =
        match p.proc with
        | Start _ -> Config.internal_error "[process_session.ml >> Labelled_process.apply_substitution] Unexpected Start."
        | Input(ch,x,pp,chans,id) -> {p with proc = Input(ch,x,browse pp,chans,id)}
        | Output(ch,t,pp,chans,id) -> {p with proc = Output(ch,apply t,browse pp,chans,id)}
        | OutputSure(ch,t,pp,chans,id) -> {p with proc = OutputSure(ch,apply t,browse pp,chans,id)}
        | If(u,v,p1,p2) -> {p with proc = If(apply u, apply v, browse p1, browse p2)}
        | Let(u,uu,v,p1,p2) -> {p with proc = Let(apply u,apply uu,apply v,browse p1, browse p2)}
        | New(n,pp) -> {p with proc = New(n,browse pp)}
        | Par l -> {p with proc = Par (List.map browse l)}
        | Bang(b,[],l) -> {p with proc = Bang(b,[],List.map browse l)}
        | Bang(_,_::_,_) -> Config.internal_error "[process_session.ml >> Labelled_process.apply_substitution] Bangs should not be broken outside of negative phases." in
      browse p

    (* unfolds public inputs and internal communications *)
    let unfold ?(improper=None) ?(optim=false) (l:t list) : (t * Input.data) list * (t * t * data) list =
      let (pub_input,internal_comm,future_channels) =
        List.fold_left_with_memo (fun accu p leftovers_left leftovers_right ->
          unfold_with_leftovers optim accu (fun proc leftovers forall (ac_pub,ac_priv,ac_chan) ->
            if improper <> None
            then
              match proc.proc with
                | Input(c,x,pp,_,id) when Channel.is_public c ->
                  let res : Input.data = {
                    Input.channel = c;
                    Input.var = x;
                    Input.optim = false;
                    Input.lab = get_label proc;
                    Input.leftovers = leftovers;
                    Input.id = id;
                  } in
                  (pp,res)::ac_pub,ac_priv,ac_chan
                | _ -> ac_pub,ac_priv,ac_chan
            else
              match proc.proc with
              | Input(c,x,pp,chans_in,id) when Channel.is_public c ->
                let res : Input.data = {
                  Input.channel = c;
                  Input.var = x;
                  Input.optim = forall;
                  Input.lab = get_label proc;
                  Input.leftovers = leftovers;
                  Input.id = id;
                } in
                let ac_chan' = Channel.Set.union chans_in ac_chan in
                (pp,res)::ac_pub,ac_priv,ac_chan'
              | Input(_,_,_,chans_in,_) ->
                ac_pub,ac_priv,Channel.Set.union chans_in ac_chan
              | OutputSure(c_out,t,pp_out,chans_out,id_out) when not (Channel.is_public c_out) ->
                let ac_priv_upd =
                  List.fold_left_with_memo (fun ac_priv1 proc1 leftovers1_left leftovers1_right ->
                    unfold_with_leftovers optim ac_priv1 (fun proc2 leftovers_proc2 forall_in ac_priv2 ->
                      match proc2.proc with
                      | Input(c_in,x,pp_in,_,id_in) when Channel.equal c_in c_out ->
                        let res = {
                          channel = c_in;
                          var = x;
                          term = t;
                          optim = forall && forall_in;
                          labs = get_label proc2, get_label proc;
                          leftovers = leftovers_proc2;
                          ids = id_in,id_out;
                          conflict_toplevel = true;
                          conflict_future = true;
                        } in
                        insert (substitute x t pp_in,pp_out,res) ac_priv2
                      | _ -> ac_priv2
                    ) proc1 (List.rev_append leftovers1_left leftovers1_right)
                  ) ac_priv leftovers in
                ac_pub,ac_priv_upd,Channel.Set.union chans_out ac_chan
              | _ -> Config.internal_error "[process_session.ml >> Labelled_process.PrivateComm.unfold] Non-atomic or non-normalised process unfolded."
          ) p (List.rev_append leftovers_left leftovers_right)
        ) ([],[],Channel.Set.empty) l in
      let internal_comm_refined = List.rev_map (refine_conflict_future future_channels) internal_comm in
      let internal_comm_sorted = List.fast_sort compare_comm internal_comm_refined in
      match improper with
        | None -> mark_forall optim pub_input internal_comm_sorted
        | Some lbl ->
            let rec find_bigger_lbl = function
              | [] ->
                  (* We haven't found a label bigger than the improper label.
                     Thus, all the input transition can only be used for an exist transition *)
                  []
              | (pp,res)::q ->
                  if Label.independent_list lbl [res.Input.lab] < 0
                  then
                    (* The selected input process is bigger than the improper label so
                       we select it for an forall transition. *)
                    (pp,{ res with Input.optim = true })::(find_bigger_lbl q)
                  else
                    (pp,res)::(find_bigger_lbl q)
            in
            (find_bigger_lbl pub_input,[])
  end

  module Optimisation = struct
    (* removing subprocesses that cannot trigger observable actions (for optimisation purposes; does not affect the decision of equivalence) *)
    let void = {proc = Par []; label = None}
    (* VINCENT: Possible new function for remove_non_observable. CAREFUL: Your function is never called. *)
    let rec remove_non_observable p0 =
      match p0.proc with
      | Start(p,id) -> { p0 with proc = Start(remove_non_observable p,id) }
      | Output(c,t,p,chans,id) -> { p0 with proc = Output(c,t,remove_non_observable p,chans,id) }
      | OutputSure _ -> Config.internal_error "[process_sessions.ml >> Optimisation.remove_non_observable] Should only be applied at the beginning of the verification."
      | Input(c,x,p,chans,id) -> { p0 with proc = Input(c,x,remove_non_observable p,chans,id) }
      | If(u,v,p1,p2) ->
        let p1' = remove_non_observable p1
        and p2' = remove_non_observable p2 in
        if nil p1' && nil p2'
        then void
        else { p0 with proc = If(u,v,p1',p2') }
      | Let(pat,pat_uni,u, p1, p2) ->
        let p1' = remove_non_observable p1
        and p2' = remove_non_observable p2 in
        if nil p1' && nil p2'
        then void
        else { p0 with proc = Let(pat,pat_uni,u,p1',p2') }
      | New(n,p) ->
        let p' = remove_non_observable p in
        if nil p'
        then void
        else { p0 with proc = New(n,p') }
      | Par l_proc ->
        let l_proc' = remove_non_observable_list l_proc in
        if l_proc' = []
        then void
        else { p0 with proc = Par l_proc' }
      | Bang(Strong,[],l_proc) ->
        let l_proc' = remove_non_observable_list l_proc in
        if l_proc' = []
        then void
        else { p0 with proc = Bang(Strong,[],l_proc') }
      | Bang _ ->  Config.internal_error "[process_sessions.ml >> Optimisation.remove_non_observable] All replication should be strong without broken symmetry at the beginning of the verification."

    and remove_non_observable_list = function
      | [] -> []
      | p::q ->
          let p' = remove_non_observable p in
          if nil p'
          then remove_non_observable_list q
          else p'::(remove_non_observable_list q)

    let flatten (p:t) : t = p
    let factor (p:t) : t = p
    let factor_up_to_renaming p1 p2 = p1 , p2

    let rec match_processes proc1 proc2 = match proc1.proc, proc2.proc with
      | Start(p1,_), Start(p2,_) -> match_processes p1 p2
      | Output(c1,t1,p1,_,_), Output(c2,t2,p2,_,_)
      | OutputSure(c1,t1,p1,_,_), OutputSure(c2,t2,p2,_,_) ->
          Channel.match_channels c1 c2;
          match_variables_and_names_in_terms t1 t2;
          match_processes p1 p2
      | Input(c1,x1,p1,_,_), Input(c2,x2,p2,_,_) ->
          Channel.match_channels c1 c2;
          match_variables x1 x2;
          match_processes p1 p2
      | If(u1,v1,pthen1,pelse1), If(u2,v2,pthen2,pelse2) ->
          match_variables_and_names_in_terms u1 u2;
          match_variables_and_names_in_terms v1 v2;
          match_processes pthen1 pthen2;
          match_processes pelse1 pelse2
      | Let(pat1,pat_uni1,u1,pthen1,pelse1), Let(pat2,pat_uni2,u2,pthen2,pelse2) ->
          match_variables_and_names_in_terms pat1 pat2;
          match_variables_and_names_in_terms pat_uni1 pat_uni2;
          match_variables_and_names_in_terms u1 u2;
          match_processes pthen1 pthen2;
          match_processes pelse1 pelse2
      | New(n1,p1), New(n2,p2) ->
          match_names n1 n2;
          match_processes p1 p2
      | Par(p_list1), Par(p_list2) ->
          List.iter2 match_processes p_list1 p_list2
      | Bang(_,p_broken_list1,p_list1), Bang(_,p_broken_list2,p_list2) ->
          List.iter2 match_processes p_list1 p_list2;
          List.iter2 match_processes p_broken_list1 p_broken_list2
      | _ -> raise No_Match
  end

  module Normalise = struct
    type equation = (fst_ord, name) Subst.t
    type disequation = (fst_ord, name) Diseq.t
    type constraints = {
      equations : equation;
      disequations : disequation list;
    }
    let equations (c:constraints) : equation = c.equations
    let disequations (c:constraints) : disequation list = c.disequations
    let constraints_of_equations (eqn:(fst_ord, name) Subst.t) : constraints =
      {equations = eqn; disequations = []}

    exception Bot_disequations

    type modulo_result =
      | EqBot
      | EqTop
      | EqList of (fst_ord, name) Subst.t list

    type dismodulo_result =
      | DiseqBot
      | DiseqTop
      | DiseqList of (fst_ord, name) Diseq.t list

    let rec normalise (proc:t) (cstr:constraints) (f_cont:constraints->t->(unit->unit)->unit) (f_next:unit->unit) : unit =
      match proc.proc with
      | OutputSure _
      | Input _ -> f_cont cstr proc f_next
      | Output(ch,t,p,chans,id) ->
        let tt = Rewrite_rules.normalise (Subst.apply cstr.equations t (fun x f -> f x)) in

        let eqn_modulo_list_result =
          try
            EqList (Modulo.syntactic_equations_of_equations [Modulo.create_equation tt tt])
          with
            | Modulo.Bot -> EqBot
            | Modulo.Top -> EqTop in

        begin match eqn_modulo_list_result with
          | EqBot -> f_cont cstr {p with proc = Par []} f_next
          | EqTop -> f_cont cstr {p with proc = OutputSure(ch,t,p,chans,id)} f_next
          | EqList eqn_modulo_list ->
            let f_next_equations =
              List.fold_left (fun acc_f_next equations_modulo ->
                let new_disequations_op =
                  try
                    let new_disequations =
                      List.fold_left (fun acc diseq ->
                        let new_diseq = Diseq.apply_and_normalise Protocol equations_modulo diseq in
                        if Diseq.is_top new_diseq then acc
                        else if Diseq.is_bot new_diseq then raise Bot_disequations
                        else new_diseq::acc
                      ) [] cstr.disequations in
                    Some new_disequations
                  with
                    | Bot_disequations -> None in

                match new_disequations_op with
                 | None -> acc_f_next
                 | Some new_diseqn ->
                    let new_eqn = Subst.compose cstr.equations equations_modulo in
                    fun () -> f_cont {equations = new_eqn; disequations = new_diseqn} {proc with proc = OutputSure(ch,t,p,chans,id)} acc_f_next
              ) f_next eqn_modulo_list
            in

            let f_next_disequation f_next =
              let diseqn_modulo =
                try
                  Modulo.syntactic_disequations_of_disequations (Modulo.create_disequation tt tt)
                with
                | Modulo.Bot
                | Modulo.Top -> Config.internal_error "[process_session.ml >> normalise] The disequations cannot be top or bot." in
              let new_diseqn = List.rev_append cstr.disequations diseqn_modulo in
              f_cont {cstr with disequations = new_diseqn} {proc with proc = Par []} f_next in

            f_next_disequation f_next_equations
        end
      | If(u,v,pthen,pelse) ->
        let (u_1,v_1) = Subst.apply cstr.equations (u,v) (fun (x,y) f -> f x, f y) in

        let eqn_modulo_list_result =
          try
            EqList (Modulo.syntactic_equations_of_equations [Modulo.create_equation u_1 v_1])
          with
          | Modulo.Bot -> EqBot
          | Modulo.Top -> EqTop in

        begin match eqn_modulo_list_result with
          | EqBot -> normalise pelse cstr f_cont f_next
          | EqTop -> normalise pthen cstr f_cont f_next
          | EqList eqn_modulo_list ->
            let f_next_equations =
              List.fold_left (fun acc_f_next equations_modulo ->
                let new_disequations_op =
                  try
                    let new_disequations =
                      List.fold_left (fun acc deq ->
                        let new_deq = Diseq.apply_and_normalise Protocol equations_modulo deq in
                        if Diseq.is_top new_deq then acc
                        else if Diseq.is_bot new_deq then raise Bot_disequations
                        else new_deq::acc
                      ) [] cstr.disequations
                    in
                    Some new_disequations
                  with
                    | Bot_disequations -> None in

                match new_disequations_op with
                  | None -> acc_f_next
                  | Some new_disequations ->
                    let new_equations = Subst.compose cstr.equations equations_modulo in
                    (fun () -> normalise pthen {equations = new_equations; disequations = new_disequations} f_cont acc_f_next)
              ) f_next eqn_modulo_list in

            let else_next f_next =
              let disequations_modulo =
                try
                  Modulo.syntactic_disequations_of_disequations (Modulo.create_disequation u_1 v_1)
                with
                  | Modulo.Bot
                  | Modulo.Top -> Config.internal_error "[process_session.ml >> normalise] The disequations cannot be top or bot (2)." in

              let new_diseqn = List.rev_append disequations_modulo cstr.disequations in
              normalise pelse {cstr with disequations = new_diseqn} f_cont f_next in

            else_next f_next_equations
        end
      | Let(u,uelse,v,pthen,pelse) ->
        let (u,uelse,v) =
          Subst.apply cstr.equations (u,uelse,v) (fun (x,y,z) f -> f x, f y, f z) in

        let positive_branch f_next =
          let eqn_modulo_list_result =
            try
              EqList (Modulo.syntactic_equations_of_equations [Modulo.create_equation u v])
            with
              | Modulo.Bot -> EqBot
              | Modulo.Top -> EqTop in

          match eqn_modulo_list_result with
          | EqBot -> f_next()
          | EqTop -> normalise pthen cstr f_cont f_next
          | EqList eqn_modulo_list ->
            let f_next_equations =
              List.fold_left (fun acc_f_next eqn_modulo ->
                let new_diseqn_op =
                  try
                    let new_diseqn =
                      List.fold_left (fun acc diseqn ->
                        let new_diseqn =
                          Diseq.apply_and_normalise Protocol eqn_modulo diseqn in
                        if Diseq.is_top new_diseqn then acc
                        else if Diseq.is_bot new_diseqn then
                          raise Bot_disequations
                        else new_diseqn::acc
                      ) [] cstr.disequations in
                    Some new_diseqn
                  with
                  | Bot_disequations -> None in
                match new_diseqn_op with
                  | None -> acc_f_next
                  | Some new_diseqn ->
                    let new_eqn = Subst.compose cstr.equations eqn_modulo in
                    let new_cstr =
                      {equations = new_eqn; disequations = new_diseqn} in
                    (fun () -> normalise pthen new_cstr f_cont acc_f_next)
              ) f_next eqn_modulo_list in
            f_next_equations () in

        let negative_branch f_next =
          let diseqn_modulo_result =
            try
              DiseqList (Modulo.syntactic_disequations_of_disequations (Modulo.create_disequation uelse v))
            with
            | Modulo.Bot -> DiseqBot
            | Modulo.Top -> DiseqTop in

          match diseqn_modulo_result with
          | DiseqBot -> f_next ()
          | DiseqTop -> normalise pelse cstr f_cont f_next
          | DiseqList diseqn_modulo ->
            let new_diseqn = List.rev_append diseqn_modulo cstr.disequations in
            normalise pelse {cstr with disequations = new_diseqn} f_cont f_next in

        positive_branch (fun () -> negative_branch f_next)
      | New(_,p) -> normalise p cstr f_cont f_next
      | Par l ->
        normalise_list l cstr (fun gather l_norm f_next1 ->
          match l_norm with
            | [p] -> f_cont gather p f_next1
            | _ -> f_cont gather {proc with proc = Par l_norm} f_next1
        ) f_next
      | Bang(b,l1,l2) ->
        normalise_list l1 cstr (fun gather1 l1_norm f_next1 ->
          normalise_list l2 gather1 (fun gather2 l2_norm f_next2 ->
            match l1_norm,l2_norm with
            | [],[p] -> f_cont gather2 p f_next2
            | _::_,_ -> Config.internal_error "[process_session.ml >> normalise] Broken bang should not occur during normalisation."
            | _ -> f_cont gather2 {proc with proc = Bang(b,l1_norm,l2_norm)} f_next2
            ) f_next1
        ) f_next
      | Start _ -> Config.internal_error "[process_session.ml >> normalise] Unexpected Start constructor."

    and normalise_list (l:t list) (cstr:constraints) (f_cont:constraints->t list->(unit->unit)->unit) (f_next:unit->unit) : unit =
      match l with
      | [] -> f_cont cstr [] f_next
      | p :: t ->
        normalise p cstr (fun gather1 p_norm f_next1 ->
          normalise_list t gather1 (fun gather2 l_norm f_next2 ->
            let l_tot_norm =
              match p_norm.proc with
              | Par [p]
              | Bang(_,[],[p]) -> p :: l_norm
              | Par [] | Bang(_,[],[]) -> l_norm
              | Bang(_,_::_,_) -> Config.internal_error "[process_session.ml >> normalise_list] Broken bang should not occur during normalisation."
              | _ -> p_norm :: l_norm
            in
            f_cont gather2 l_tot_norm f_next2
          ) f_next1
        ) f_next
  end
end


(* a module for representing and manipulating sets of process matchings *)
module BijectionSet = struct
  (* sets of bijections with the skeleton-compatibility requirement *)
  (* TODO. may ake the datastructure more efficient. Could be more practical when there are a lot of singletons to handle the operation "get all potential labels matching with a given label l". *)
  type t =
    (Label.Set.t * Label.Set.t) list

  (* the initial bijection set *)
  let initial : t =
    [Label.Set.singleton Label.initial, Label.Set.singleton Label.initial]
  (* prints a bijection set *)
  let print (bset:t) : unit =
    List.iter (fun (s1,s2) ->
      Label.Set.iter (fun lab -> Printf.printf "%s;" (Label.to_string lab)) s1;
      Printf.printf "   [MATCHABLE WITH]   ";
      Label.Set.iter (fun lab -> Printf.printf "%s;" (Label.to_string lab)) s2;
      print_endline "";
    ) bset

  (* updates a bijection set after two matched transitions on labels (l1,l2). Returns None if this update is not possible (incompatible labels or skeletons). *)
  let update (l1:Label.t) (l2:Label.t) (s1:Labelled_process.Skeleton.t) (s2:Labelled_process.Skeleton.t) (bset:t) : t option =
    let rec search memo s = match s with
      | [] -> None
      | (ll1,ll2) :: t ->
          assert (not (Label.Set.is_empty ll1) && not (Label.Set.is_empty ll2));
          match Label.find_and_remove l1 ll1, Label.find_and_remove l2 ll2 with
            | None, None -> search ((ll1,ll2) :: memo) t
            | Some ll1', Some ll2' ->
                if Label.Set.is_empty ll1' then Some (List.rev_append memo t)
                else Some (List.rev_append memo ((ll1',ll2')::t))
            | _ -> None
    in
    match Labelled_process.Skeleton.link s1 s2 with
      | None -> None
      | Some ([[_],[_]]) -> search [Label.Set.singleton l1, Label.Set.singleton l2] bset
      | Some linked_positions ->
          let new_pairings =
            List.rev_map (fun (pos_list1,pos_list2) ->
              Label.of_position_list l1 pos_list1, Label.of_position_list l2 pos_list2
            ) linked_positions
          in
          search new_pairings bset

  type matching_index =
    {
      id : int;
      mutable link : (int * Labelled_process.t list * Labelled_process.t list) option
    }

  let rec match_one_process f_next p1 prev = function
    | [] -> raise No_Match
    | p2::q2 ->
        try
          Term.auto_cleanup_matching (fun () ->
            Labelled_process.Optimisation.match_processes p1 p2;
            f_next (List.rev_append prev q2)
          )
        with No_Match -> match_one_process f_next p1 (p2::prev) q2

  let rec match_list_processes f_next proc_list1 proc_list2 = match proc_list1 with
    | [] -> f_next ()
    | p1::q1 ->
        match_one_process (fun remain_proc_list2 ->
          match_list_processes f_next q1 remain_proc_list2
        ) p1 [] proc_list2

  let rec match_list_list_processes f_next = function
    | [] -> f_next ()
    | (pl1,pl2)::q ->
        match_list_processes (fun () ->
          match_list_list_processes f_next q
        ) pl1 pl2

  let match_processes f_next proc_list1 proc_list2 bset1 bset2 =
      Config.debug (fun () -> Config.print_in_log "match_processes\n");
      let list_pairs2 = ref [] in
      let list_pairs1 = ref [] in
      let counter = ref 0 in
      let list_index = ref [] in
      List.iter (fun (set1,set2) ->
        let id_set = { id = !counter; link = None } in
        list_index := id_set :: !list_index;
        incr counter;
        let elts1 = Label.Set.elements set1 in
        let elts2 = Label.Set.elements set2 in
        List.iter2 (fun lbl1 lbl2 ->
          Config.debug (fun () -> Config.print_in_log "Find\n");
          let p =
            List.find (fun t -> (Labelled_process.get_label t) = lbl2) proc_list1 in
          list_pairs1 := (lbl1, id_set, p) :: !list_pairs1
        ) elts1 elts2
      ) bset1;
      Config.debug (fun () -> Config.print_in_log "match_processes2\n");
      List.iter (fun (set1,set2) ->
        let id_set =  !counter in
        incr counter;
        let elts1 = Label.Set.elements set1 in
        let elts2 = Label.Set.elements set2 in
        List.iter2 (fun lbl1 lbl2 ->
          let p = List.find (fun t -> (Labelled_process.get_label t) = lbl2) proc_list2 in
          list_pairs2 := (lbl1, id_set, p) :: !list_pairs2
        ) elts1 elts2
      ) bset2;
      list_pairs1 := List.sort (fun (lbl1,_,_) (lbl2,_,_) -> Label.independent lbl1 lbl2) !list_pairs1;
      list_pairs2 := List.sort (fun (lbl1,_,_) (lbl2,_,_) -> Label.independent lbl1 lbl2) !list_pairs2;
      Config.debug (fun () -> Config.print_in_log "match_processes3\n");
      let rec explore list1 list2 = match list1, list2 with
        | [], [] -> ()
        | _, [] | [],_ -> Config.internal_error "[process_session.ml >> BijectionSet.match_processes] The lists should be of same size."
        | (_,match_index,p1)::q1, (_,id_set2,p2)::q2 ->
            begin match match_index.link with
              | None -> match_index.link <- Some (id_set2,[p1],[p2])
              | Some (id_set1,p_list1,p_list2) ->
                  if id_set1 <> id_set2
                  then raise No_Match;
                  match_index.link <- Some(id_set1,p1::p_list1,p2::p_list2)
            end;
            explore q1 q2
      in

      explore !list_pairs1 !list_pairs2;

      let proc_list_list = ref [] in

      List.iter (function
        | { link = Some (_,pl1,pl2); _} -> proc_list_list := (pl1,pl2) :: !proc_list_list
        | _ -> Config.internal_error "[process_session.ml >> BijectionSet.match_processes] Match index should be linked."
      ) !list_index;

      match_list_list_processes f_next !proc_list_list

  let rec match_one_forall_process f_next p1 prev = function
    | [] -> raise No_Match
    | p2::q2 ->
        try
          Term.auto_cleanup_matching (fun () ->
            Label.auto_cleanup (fun () ->
              Label.match_label (Labelled_process.get_label p1) (Labelled_process.get_label p2);
              Labelled_process.Optimisation.match_processes p1 p2;
              f_next (List.rev_append prev q2)
            )
          )
        with No_Match -> match_one_forall_process f_next p1 (p2::prev) q2

  let rec match_forall_list_processes f_next proc_list1 proc_list2 = match proc_list1 with
    | [] -> f_next ()
    | p1::q1 ->
        match_one_forall_process (fun remain_proc_list2 ->
          match_forall_list_processes f_next q1 remain_proc_list2
        ) p1 [] proc_list2

  type sorted_bset =
    | Sorted of t
    | Unsorted of t

  let match_forall_processes f_next p1 p2 block_list1 block_list2 exist_list1 exist_list2 =
    if List.length exist_list1 <> List.length exist_list2
    then raise No_Match;

    let sorted_exists1 = List.sort (fun (id1,_) (id2,_) -> compare id1 id2) exist_list1 in
    let sorted_exists2 = List.sort (fun (id1,_) (id2,_) -> compare id1 id2) exist_list2 in

    List.iter2 (fun (_,bset1) (_,bset2) ->
      if List.length bset1 <> List.length bset2
      then raise No_Match;
    ) sorted_exists1 sorted_exists2;

    (* Could use the inclusion but not sure it is useful *)
    List.iter2 (fun (id1,_) (id2,_) -> if id1 <> id2 then raise No_Match) sorted_exists1 sorted_exists2;

    let ref_exists2 = List.map (fun (_,bset) -> ref (Unsorted bset)) sorted_exists2 in

    let rec check_exists_correspondence exists1 exists2 = match exists1, exists2 with
      | [],[] -> ()
      | [],_ | _,[] -> Config.internal_error "[BijectionSet.match_forall_processes] Unexpecting lists of same size."
      | (_,bset1)::q1, bset2_ref::q2 ->

          let sorted_bset2 = match !bset2_ref with
            | Sorted bset -> bset
            | Unsorted bset ->
                let bset' = List.sort (fun (lbl_set1,_) (lbl_set2,_) -> Label.Set.compare lbl_set1 lbl_set2) bset in
                bset2_ref := Sorted bset';
                bset'
          in

          let matched_bset1 =
            List.map (fun (lbl_set1,lbl_set2) ->
              let lbl_set1' =
                Label.Set.map (fun lbl -> match lbl.Label.link with
                  | None -> Config.internal_error "[BijectionSet.match_forall_processes] All the labels of the first bset should have been matched."
                  | Some lbl' -> lbl'
                ) lbl_set1
              in

              (lbl_set1',lbl_set2)
            ) bset1
          in

          let sorted_bset1 = List.sort (fun (lbl_set1,_) (lbl_set2,_) -> Label.Set.compare lbl_set1 lbl_set2) matched_bset1 in

          List.iter2 (fun (lbl_set_fa1, lbl_set_ex1) (lbl_set_fa2,lbl_set_ex2) ->
            if not ((Label.Set.equal lbl_set_fa1 lbl_set_fa2) && (Label.Set.equal lbl_set_ex1 lbl_set_ex2))
            then raise No_Match
          ) sorted_bset1 sorted_bset2;

          check_exists_correspondence q1 q2
    in

    Config.debug (fun () -> Config.print_in_log "Block.match_labels\n");
    (* We start by matching the labels of the block *)
    Block.match_labels (fun linked_label_blocks ->
      (* I assume p1 and p2 are already split *)
      let list_labels1 = List.rev_map Labelled_process.get_label p1 in
      Config.debug (fun () -> Config.print_in_log "match_forall_list_processes\n");
      match_forall_list_processes (fun () ->
        Config.debug (fun () -> Config.print_in_log "check_labels\n");
        (* We check if the labels satisfy the desired properties. (may raise No_Match neither side are smaller)*)
        let does_first_subsume = Block.check_labels linked_label_blocks list_labels1 in

        Config.debug (fun () -> Config.print_in_log "check_exists_correspondence\n");
        (* We check that the exist_list corresponds. *)
        check_exists_correspondence sorted_exists1 ref_exists2;

        f_next does_first_subsume
      ) p1 p2
    ) block_list1 block_list2

  let check_and_remove_improper_labels bset imp_labels_fa imp_labels_ex =
    let bset',imp_labels_fa1,imp_labels_ex1 =
      List.fold_left (fun (accu_bset,accu_fa,accu_ex) (set_fa,set_ex) ->
        let one_lbl = Label.Set.choose set_fa in
        if List.exists (fun lbl -> one_lbl.Label.label = lbl.Label.label) accu_fa
        then
          let accu_fa' =
            Label.Set.fold (fun lbl_fa acc1 ->
              List.remove (fun lbl -> lbl_fa.Label.label = lbl.Label.label) acc1
            ) set_fa accu_fa
          in
          let accu_ex' =
            Label.Set.fold (fun lbl_ex acc1 ->
              List.remove (fun lbl -> lbl_ex.Label.label = lbl.Label.label) acc1
            ) set_ex accu_ex
          in
          (accu_bset,accu_fa',accu_ex')
        else (set_fa,set_ex)::accu_bset, accu_fa,accu_ex
      ) ([],imp_labels_fa,imp_labels_ex) bset
    in
    if imp_labels_ex1 = [] && imp_labels_fa1 = []
    then bset'
    else raise Not_found

  (******* Display ********)

  let display out ?(tab = 0) ?(out_ch=stdout) ?(id_link=0) ?(title="Bijection Set") bset =
    let display_set set =
      if Label.Set.is_empty set
      then emptyset out
      else
        begin
          let first = ref true in
          let acc = ref "" in
          Label.Set.iter (fun lbl ->
            if !first
            then ( acc := !acc ^ (Label.display lbl); first := false )
            else acc := !acc ^ "; " ^ (Label.display lbl)
          ) set;
          Printf.sprintf "%s %s %s" (lcurlybracket out) !acc (rcurlybracket out)
        end
    in

    Printf.fprintf out_ch "%s<div class=\"bijectionset\" id=\"bijectionset%d\" style=\"display:none;\">%s: %s</div>\n"
      (create_tab tab)
      id_link
      title
      (display_list (fun (set1,set2) ->
        Printf.sprintf "%s %s %s" (display_set set1) (rightarrow out) (display_set set2)
      ) ", " bset)
end

(* type for representing internal states *)
module Configuration = struct
  (* Change state for the current_proc. Too costly to do all these operations just for the trace reconstruction. Do it later when there is an attack. *)

  type state = {
    current_proc : t;
    id : Labelled_process.id;
    label : Label.t;
  }
  and action =
    | InAction of Channel.t * snd_ord_variable * protocol_term * state
    | OutAction of Channel.t * axiom * protocol_term * state
    | ComAction of Channel.t * state * state

  and t = {
    input_proc : Labelled_process.t list;
    focused_proc : (Labelled_process.t * Label.t) option;
    sure_output_proc : Labelled_process.t list;
    to_normalise : (Labelled_process.t * Label.t) list;
    trace : action list;
    ongoing_block : Block.t;
    previous_blocks : Block.t list;
    improper_collector : Labelled_process.t list;
    ongoing_improper_label : Label.t list option (* equal to None when we haven't found an improper block yet. *)
  }


  let contain_only_public_channel conf = match conf.focused_proc with
    | None -> Config.internal_error "[process_session.ml >> contain_only_public_channel] Should only be applied on initial configuration."
    | Some(p,_) -> Labelled_process.contain_only_public_channel p

  (* Function to only apply on configuration corresponding to a node of the
     partition tree (i.e. normalised) *)
  let occurs_in_process v subst conf =
    let test_function p =
      let p' = Labelled_process.apply_substitution subst p in
      Labelled_process.occurs v p'
    in
    List.exists test_function conf.input_proc ||
    List.exists test_function conf.sure_output_proc ||
    begin match conf.focused_proc with
      | None -> false
      | Some (p,_) ->
          let p' = Labelled_process.apply_substitution subst p in
          Labelled_process.occurs v p'
    end

  let get_improper_labels f_next conf =
    Labelled_process.get_improper_labels_list (fun imp_labels imp_procs proc_list ->
      f_next imp_labels { conf with input_proc = proc_list; improper_collector = List.rev_append imp_procs conf.improper_collector }
    ) [] [] conf.input_proc

  let get_ongoing_improper_label conf = conf.ongoing_improper_label

  let is_improper_phase conf = conf.ongoing_improper_label <> None

  let is_focused conf = match conf.focused_proc with
    | None -> false
    | _ -> true

  let get_block_list t = t.ongoing_block :: t.previous_blocks

  let display_blocks conf =
    Printf.sprintf "-- Previous Blocks =\n%s--Ongoing Block = %s" (Display.display_list (fun b -> Printf.sprintf "%s\n" (Block.print b)) ";" (List.rev conf.previous_blocks)) (Block.print conf.ongoing_block)

  let to_process (conf:t) : Labelled_process.t =
    let l = conf.input_proc @ conf.sure_output_proc @ conf.improper_collector in
    match conf.focused_proc with
    | None -> Labelled_process.of_process_list l
    | Some (p,_) -> Labelled_process.of_process_list (p::l)

  let elements (conf:t) : Labelled_process.t list =
    let accu1 = List.fold_left (fun accu lp -> Labelled_process.elements ~init:accu lp) [] conf.input_proc in
    let accu2 = List.fold_left (fun accu lp -> Labelled_process.elements ~init:accu lp) accu1 conf.sure_output_proc in
    match conf.focused_proc with
      | None -> accu2
      | Some (p,_) -> Labelled_process.elements ~init:accu2 p

  (* color printing *)
  let bold_blue s = Printf.sprintf "\\033[1;34m%s\\033[0m" s

  let print_action (fst_subst:(fst_ord,name) Subst.t) (snd_subst:(snd_ord,axiom) Subst.t) (act:action) : string =
    match act with
    | InAction(ch,var_X,x,s) ->
      let recipe =
        Subst.apply snd_subst (of_variable var_X) (fun x f -> f x) in
      let input =
        Rewrite_rules.normalise (Subst.apply fst_subst x (fun x f -> f x)) in
      let msg =
        Printf.sprintf "input on channel %s of %s = %s\n" (Channel.to_string ch) (Term.display Terminal Recipe recipe) (Term.display Terminal Protocol input) in
      Printf.sprintf "%s%s" (bold_blue msg) (Labelled_process.print ~labels:true ~solution:fst_subst ~highlight:[s.id] (to_process s.current_proc))
    | OutAction(ch,ax,t,s) ->
      let output =
        Rewrite_rules.normalise (Subst.apply fst_subst t (fun x f -> f x)) in
      let msg =
        Printf.sprintf "output on channel %s of %s, referred as %s\n" (Channel.to_string ch) (Term.display Terminal Protocol output) (Axiom.display Terminal ax) in
      Printf.sprintf "%s%s" (bold_blue msg) (Labelled_process.print ~labels:true ~solution:fst_subst ~highlight:[s.id] (to_process s.current_proc))
    | ComAction(ch,s_in,s_out) ->
      let msg =
        Printf.sprintf "internal communication on channel %s\n" (Channel.to_string ch) in
      Printf.sprintf "%s%s" (bold_blue msg) (Labelled_process.print ~labels:true ~solution:fst_subst ~highlight:[s_in.id;s_out.id] (to_process s_in.current_proc))

  let print_trace (fst_subst:(fst_ord,name) Subst.t) (snd_subst:(snd_ord,axiom) Subst.t) (conf:t) : string =
    snd (
      List.fold_left (fun (count,accu) act ->
        count-1,Printf.sprintf "\n\n%s %s%s" (bold_blue (Printf.sprintf "%d)" count)) (print_action fst_subst snd_subst act) accu
      ) (List.length conf.trace,"") conf.trace
    )

  let check_block (snd_subst:(snd_ord,axiom) Subst.t) (c:t) : bool * snd_ord_variable list =
    Block.is_authorised c.previous_blocks c.ongoing_block snd_subst

  let inputs (conf:t) : Labelled_process.t list =
    conf.input_proc

  let outputs (conf:t) : Labelled_process.t list =
    conf.sure_output_proc

  let of_expansed_process (p:Process.expansed_process) : t =
    (* Printf.printf "converting %s\n" (Labelled_process.print (Labelled_process.of_expansed_process p)); *)
    {
      input_proc = [];
      focused_proc = Some (Labelled_process.of_expansed_process ~preprocessing:Labelled_process.Optimisation.remove_non_observable p, Label.initial);
      sure_output_proc = [];
      to_normalise = [];
      trace = [];

      ongoing_block = Block.create [Label.initial];
      previous_blocks = [];
      improper_collector = [];
      ongoing_improper_label = None
    }

  (* We assume that the configuration was create by [of_expansed_process]*)
  let get_initial_label conf = match conf.focused_proc with
    | Some(_,lbl) -> lbl
    | _ -> Config.internal_error "[process_session.ml >> get_initial_label] Expect an intial configuration."

  let normalise ?context:(rebuild:Labelled_process.t->Labelled_process.t=fun t->t) (conf:t) (eqn:(fst_ord, name) Subst.t) (f_cont:Labelled_process.Normalise.constraints->t->Labelled_process.Skeleton.t list->unit) : unit =

    let rec normalise_all conf skel_list gather f_cont =
      match conf.to_normalise, conf.focused_proc with
        | [], None -> f_cont gather conf skel_list
        | [], Some (p,prefix) ->
          Labelled_process.Normalise.normalise p gather (fun gather1 p_norm f_next ->
            let (labelled_p,skel) = Labelled_process.labelling prefix p_norm in
            f_cont gather1 {conf with focused_proc = Some (labelled_p,prefix)} [skel];
            f_next ()
          ) (fun () -> ())
        | (p,prefix) :: t, None ->
          Labelled_process.Normalise.normalise p gather (fun gather1 p_norm f_next ->
            let (labelled_p,skel) = Labelled_process.labelling prefix p_norm in
            let pp = rebuild labelled_p in
            let conf_base = {conf with to_normalise = t} in
            let conf_final =
              if Labelled_process.nil pp then conf_base
              else if Labelled_process.contains_public_output_toplevel pp then
                {conf_base with sure_output_proc = pp::conf_base.sure_output_proc}
              else
                {conf_base with input_proc = Labelled_process.Output.restaure_sym pp::conf_base.input_proc} in
            normalise_all conf_final (skel::skel_list) gather1 f_cont;
            f_next ()
          ) (fun () -> ())
        | _, _ -> Config.internal_error "[process_session.ml >> normalise] A configuration cannot be released and focused at the same time." in

    let eqn_cast = Labelled_process.Normalise.constraints_of_equations eqn in
    normalise_all conf [] eqn_cast f_cont

  (* [release_skeleton conf] updates the configuration by releasing
     the focus when needed. When [conf.first_improper_label <> None], it also
     transfers the non-input on public channels processes inside the improper
     collector of the configuration. When an impropoer block is detected, it
     update first_improper_label with the label of process.  *)
  let release_skeleton (conf:t) : t = match conf.focused_proc with
    | None -> conf
    | Some (p,_) ->
        match Labelled_process.get_proc p with
          | Labelled_process.Input(ch,_,_,_,_) when Channel.is_public ch ->
              (* Next transition type will be positive *)
              conf
          | _ ->
              if Labelled_process.nil p
              then { conf with focused_proc = None; ongoing_improper_label = Some (Block.get_label conf.ongoing_block) }
              else
                if conf.ongoing_improper_label = None
                then
                  if Labelled_process.contains_public_output_toplevel p
                  then { conf with focused_proc = None; sure_output_proc = p::conf.sure_output_proc }
                  else { conf with focused_proc = None; input_proc = p::conf.input_proc }
                else raise No_Match

  module Transition = struct
    type kind =
      | RFocus
      | RPos
      | RNeg
      | RStart

    let print_kind (t:kind option) : unit =
      let s =
        match t with
        | None -> "None"
        | Some RFocus -> "Focus"
        | Some RPos -> "Pos"
        | Some RNeg -> "Neg"
        | Some RStart -> "Start" in
      print_endline ("***************************************\n>> Transition: "^s^"\n***************************************")

    (* given the shape of a configuration, find the next type of to apply *)
    let next (c:t) : kind option =
      match c.focused_proc with
      | Some (p,_) ->
        begin match Labelled_process.get_proc p with
          | Labelled_process.Input _ -> Some RPos
          | Labelled_process.Start _ -> Some RStart
          | _ ->
            Config.internal_error "[process_session.ml >> Configuration.Transition.next] Ill-formed focused state, should have been released or normalised."
        end
      | None ->
        if c.sure_output_proc <> [] then Some RNeg
        else match c.input_proc with
          | [] -> None
          | _ -> Some RFocus

    (* syntactic transformation of a configuration at the start of the analysis *)
    let apply_start (conf:t) : t =
      match conf.focused_proc with
      | Some (p,l) ->
        begin match Labelled_process.get_proc p with
        | Labelled_process.Start (pp,_) -> {conf with focused_proc = Some (pp,l)}
        | _ -> Config.internal_error "[process_session.ml Configuration.Transition.apply_start] Error during the initialisation of processes. (1)"
        end
      | _ ->
        Config.internal_error "[process_session.ml >> Configuration.Transition.apply_start] Error during the initialisation of processes. (2)"

    (* syntactic transformation of a configuration after executing an output *)
    let apply_neg (ax:axiom) (p:Labelled_process.t) (od:Labelled_process.Output.data) (leftovers:Labelled_process.t list) (conf:t) : t =
      let state = {
        current_proc = conf;
        id = od.Labelled_process.Output.id;
        label = od.Labelled_process.Output.lab;
      } in
      let ch = od.Labelled_process.Output.channel in
      let term = od.Labelled_process.Output.term in
      { conf with
        to_normalise = [p,od.Labelled_process.Output.lab];
        sure_output_proc = leftovers;
        trace = OutAction(ch,ax,term,state)::conf.trace;
        ongoing_block = Block.add_axiom ax conf.ongoing_block }

    (* syntactic transformation of a configuration after executing a focused input. Also retrieves and returns the input_data of the focus state. *)
    let apply_pos (var_X:snd_ord_variable) (conf:t) : Labelled_process.Input.data * t =
      match conf.focused_proc with
      | Some (p,prefix) ->
        begin match Labelled_process.get_proc p with
        | Labelled_process.Input(ch,x,pp,_,id) when Channel.is_public ch ->
          let idata : Labelled_process.Input.data = {
            Labelled_process.Input.channel = ch;
            Labelled_process.Input.var = x;
            Labelled_process.Input.lab = Labelled_process.get_label p;
            Labelled_process.Input.id = id;
            Labelled_process.Input.leftovers = []; (* field not relevant here *)
            Labelled_process.Input.optim = true; (* field not relevant here *)
          } in
          let state : state = {
            current_proc = conf;
            id = idata.Labelled_process.Input.id;
            label = idata.Labelled_process.Input.lab;
          } in
          let conf_app = {conf with
            focused_proc = Some (pp,prefix);
            trace = InAction(ch,var_X,Term.of_variable x,state) :: conf.trace;
            ongoing_block = Block.add_variable var_X conf.ongoing_block;
          } in
          idata,conf_app
        | _ -> Config.internal_error "[process_session.ml >> Configuration.Transition.apply_pos] Ill-formed focus state." end
      | _ ->
        Config.internal_error "[process_session.ml >> Configuration.Transition.apply_pos] Process should be focused."

    (* syntactic transformation of a configuration after focusing an input *)
    let apply_focus (var_X:snd_ord_variable) (focus:Labelled_process.t * Labelled_process.Input.data) (conf:t) : t =
      Config.debug (fun () ->
        if conf.focused_proc <> None then
          Config.internal_error "[process_session.ml >> add_focus] Unexpected case."
      );
      let (pp,idata) = focus in
      let state = {
        current_proc = conf;
        id = idata.Labelled_process.Input.id;
        label = idata.Labelled_process.Input.lab;
      } in
      {conf with
        input_proc = idata.Labelled_process.Input.leftovers;
        focused_proc = Some (pp,idata.Labelled_process.Input.lab);
        ongoing_block = Block.add_variable var_X (Block.create [idata.Labelled_process.Input.lab]);
        previous_blocks = conf.ongoing_block :: conf.previous_blocks;
        trace = InAction(idata.Labelled_process.Input.channel,var_X,Term.of_variable idata.Labelled_process.Input.var,state) :: conf.trace;
      }

    (* syntactic transformation of a configuration after executing an internal communication *)
    let apply_comm (com:Labelled_process.t * Labelled_process.t * Labelled_process.PrivateComm.data) (conf:t) : t =
      let (p_in,p_out,cdata) = com in
      let (label_in,label_out) = cdata.Labelled_process.PrivateComm.labs in
      (* Printf.printf "Transforming configuration for internal communication between input %s\n(label %s)\nand output %s\n(label %s)\n" (Labelled_process.print ~labels:true p_in) (Label.to_string label_in) (Labelled_process.print ~labels:true p_out) (Label.to_string label_out); *)
      let is_deterministic =
        not cdata.Labelled_process.PrivateComm.conflict_toplevel && not cdata.Labelled_process.PrivateComm.conflict_future in
      let state_in = {
        current_proc = conf;
        id = fst cdata.Labelled_process.PrivateComm.ids;
        label = label_in;
      } in
      let state_out = {
        current_proc = conf;
        id = snd cdata.Labelled_process.PrivateComm.ids;
        label = label_out;
      } in
      let new_action = ComAction(cdata.Labelled_process.PrivateComm.channel, state_in, state_out) in
      if is_deterministic then
        { conf with
          to_normalise = [p_out,label_out; p_in,label_in];
          input_proc = cdata.Labelled_process.PrivateComm.leftovers;
          ongoing_block = Block.add_labels [label_in; label_out] conf.ongoing_block;
          trace = new_action :: conf.trace }
      else
        { conf with
          to_normalise = [p_out,label_out; p_in,label_in];
          input_proc = cdata.Labelled_process.PrivateComm.leftovers;
          ongoing_block = Block.create [label_in; label_out];
          previous_blocks = conf.ongoing_block :: conf.previous_blocks;
          trace = new_action :: conf.trace }
  end
end
