(* Process manipulation for equivalence by session *)

open Extensions
open Term


(* a module for representing process labels *)
module Label : sig
  type t
  val initial : t (* an initial, empty label *)
  val add_position : t -> int -> t (* adds a position at the end of a label *)
  val independent : t -> t -> int (* returns 0 if one label is prefix of the other, and compares them lexicographically otherwise *)
  val to_string : t -> string (* conversion to printable *)
  (* operations on sets of labels *)
  module Set : Set.S with type elt = t
end = struct
  type t = int list
  let initial = [0]
  let add_position (prefix:t) (position:int) : t = prefix @ [position]
  let to_string (lab:t) : string =
    match lab with
    | [] -> Config.internal_error "[process_session.ml >> Label.to_string] Unexpected case."
    | h :: t ->
      List.fold_left (Printf.sprintf "%s.%d") (string_of_int h) t
  let rec independent (l:t) (ll:t) : int =
    match l,ll with
    | [], _ -> 0
    | _, [] -> 0
    | t1::q1, t2::q2 ->
        match compare t1 t2 with
          | 0 -> independent q1 q2
          | i -> i
  let to_list x = x
  module Set = Set.Make(struct type t = int list let compare = compare end)
end


(* a module for representing blocks *)
module Block : sig
  type t
  val create : Label.t -> t (* creation of a new empty block *)
  val add_variable : snd_ord_variable -> t -> t (* adds a second order variable in a block *)
  val add_axiom : axiom -> t -> t (* adds an axiom in a block *)
  val is_authorised : t list -> t -> (snd_ord, axiom) Subst.t -> bool (* checks whether a block is authorised after a list of blocks *)
  val print : t -> string (* converts a block into a string *)
end = struct
  module IntSet = Set.Make(struct type t = int let compare = compare end)

  type t = {
    label : Label.t;
    recipes : snd_ord_variable list; (* There should always be variables *)
    bounds_axiom : (int * int) option; (* lower and upper bound on the axiom index used *)
    maximal_var : int;
    used_axioms : IntSet.t
  }

  let print b =
    let ax = match b.bounds_axiom with
      | None -> "No"
      | Some (i,j) -> Printf.sprintf "[%d,%d]" i j in
    let axset =
      IntSet.fold (Printf.sprintf "%d %s") b.used_axioms "" in
    let snd =
      List.fold_left (fun s x -> s^" "^Variable.display Terminal Recipe x) "" b.recipes in
    Printf.sprintf "Block: label: %s, axioms: %s, used axioms: %s, variables: %s, maximal var: %d" (Label.to_string b.label) ax axset snd b.maximal_var

  let create (label:Label.t) : t = {
      label = label;
      recipes = [];
      bounds_axiom = None;
      maximal_var = 0;
      used_axioms = IntSet.empty
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

  let rec is_faulty_block (block:t) (block_list:t list) : bool =
    match block_list with
    | [] -> false
    | b_i::q ->
      let comp_lab = Label.independent block.label b_i.label in
      if comp_lab < 0 then
        match b_i.bounds_axiom with
        | None -> true
        | Some (min_ax,max_ax) ->
          block.maximal_var < min_ax &&
          IntSet.for_all (fun ax -> ax < min_ax || ax > max_ax) block.used_axioms
      else if comp_lab > 0 then is_faulty_block block q
      else false

  (* applies a snd order substitution on a block list and computes the bound
  fields of the block type *)
  let apply_snd_subst_on_block (snd_subst:(snd_ord,axiom) Subst.t) (block_list:t list) : t list =
    Subst.apply snd_subst block_list (fun l f ->
      List.map (fun block ->
        let max_var = ref 0 in
        let used_axioms = ref IntSet.empty in
        List.iter (fun var ->
          let r' = f (Term.of_variable var) in
          Term.iter_variables_and_axioms (fun ax_op var_op ->
            match ax_op,var_op with
            | Some ax, None ->
              used_axioms := IntSet.add (Axiom.index_of ax) !used_axioms
            | None, Some v ->
              max_var := max !max_var (Variable.type_of v)
            | _, _ ->
              Config.internal_error "[process_session.ml >> apply_snd_subst_on_block] The function Term.iter_variables_and_axioms should return one filled option."
          ) r';
        ) block.recipes;

        {block with used_axioms = !used_axioms; maximal_var = !max_var}
      ) l
    )

  let is_authorised (block_list:t list) (cur_block:t) (snd_subst:(snd_ord,axiom) Subst.t) : bool =
    let block_list_upd =
      apply_snd_subst_on_block snd_subst (cur_block::block_list) in
    (* Printf.printf "AUTHORISATION CHECK:\n";
    List.iter (fun b -> Printf.printf "%s\n" (print b)) block_list_upd; *)
    match block_list with
    | [] -> true
    | _ ->
      let rec explore_block block_list =
        match block_list with
        | []
        | [_] -> true
        | block::q -> not (is_faulty_block block q) && explore_block q in
      explore_block block_list_upd
end

(* multisets of unacessible private channels *)
module Channel : sig
  type t
  val equal : t -> t -> bool
  val compare : t -> t -> int
  val is_public : t -> bool
  val to_string : t -> string
  val from_term : protocol_term -> t
  val apply_renaming : Name.Renaming.t -> t -> t
  module Set : Set.S with type elt = t
end = struct
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
    else Config.internal_error "[process_session.ml >> Channel.from_term] Channels should be names or symbols."
  let apply_renaming (rho:Name.Renaming.t) (c:t) : t =
    match c with
    | Symbol _ -> c
    | Name n ->
      Name (Term.name_of (Name.Renaming.apply_on_terms rho (Term.of_name n) (fun x f -> f x)))
  type elt = t
  module Set = Set.Make(struct type t = elt let compare = compare end)
end

module NonToplevelChannels = Multiset.Make(Channel)

(* a module for labelled processes *)
module Labelled_process : sig
  type t
  type id
  type bang_status
  type plain =
    | Start of t * id
    | Input of Channel.t * fst_ord_variable * t * id
    | Output of Channel.t * protocol_term * t * id
    | OutputSure of Channel.t * protocol_term * t * id
    | If of protocol_term * protocol_term * t * t
    | Let of protocol_term * protocol_term * protocol_term * t * t
    | New of name * t
    | Par of t list
    | Bang of bang_status * t list * t list

  val print : ?labels:bool -> ?solution:((fst_ord, name) Subst.t) -> ?highlight:id -> t -> string (* converts a process into a string, while highlighting the instruction at the given identifier *)
  val of_expansed_process : ?preprocessing:(t -> t) -> Process.expansed_process -> t (* converts an expansed process into a process starting with a Start constructor and label [initial]. Also attributes id to all observable instructions. *)
  val of_process_list : t list -> t (* groups a list of processes together *)
  val elements : ?init:(t list) -> t -> t list (* extracts the list of parallel subprocesses *)
  val nil : t -> bool (* checks if this represents the null process *)
  val empty : Label.t -> t (* a labelled process with empty data. For typing purposes (only way to construct a Labelled_process.t outside of this module) *)
  val contains_public_output_toplevel : t -> bool (* checks whether a normalised process contains an executable output *)
  val not_pure_io_toplevel : t -> bool (* checks whether a normalised process does not start right away by an input or an output *)
  type process_skel = {
    input_skel : (Channel.t * int * Label.t list) list ;
    output_skel : (Channel.t * int * Label.t list) list
  }

  val labelling2 : Label.t -> t -> t * process_skel
  val labelling : Label.t -> t -> t (* assigns labels to the parallel processes at toplevel, with a given label prefix *)
  val get_label : t -> Label.t (* gets the label of a process, and returns an error message if it has not been assigned *)
  val get_proc : t -> plain


  (* extraction of inputs from processes *)
  module Input : sig
    type data = {
      channel : Channel.t; (* channel on which the input is performed *)
      var : fst_ord_variable; (* variable bound by the input *)
      optim : bool; (* whether this input is needed for forall processes *)
      lab : Label.t; (* label of the executed input *)
      leftovers : t list; (* what remains after the input is executed *)
      id : id; (* the id of the executed instruction *)
    }
    val unfold : ?optim:bool -> t list -> (t * data) list (* function computing all potential ways of unfolding one input from a list of processes. *)
  end

  (* extraction of outputs from processes *)
  module Output : sig
    type data = {
      channel : Channel.t; (* channel on which the output is performed *)
      term : protocol_term; (* output term *)
      optim : bool; (* whether this output is needed for forall processes *)
      lab : Label.t; (* label of the executed output *)
      context : t -> t; (* suroundings of the executed output *)
      id : id; (* the id of the executed instruction *)
    }
    val unfold : ?optim:bool -> t -> (t * data) list (* function computing all potential ways of unfolding one output from a process.
    NB. Unfolding outputs break symmetries (just as symmetries), but they can be restaured at the end of negative phases (see function [restaure_sym]). *)
    val restaure_sym : t -> t (* restaures symmetries that have been temporarily broken by unfolding outputs *)
  end

  (* extraction of private communications and public inputs (using the module Input) *)
  module PrivateComm : sig
    type data = {
      channel : Channel.t; (* channel on which the output is performed *)
      var : fst_ord_variable; (* variable bound by the input *)
      term : protocol_term; (* output term *)
      optim : bool; (* whether this input is needed for forall processes *)
      labs : Label.t * Label.t; (* labels of the executed input *)

      leftovers : t list; (* what remains after the input is executed *)
      ids : id * id; (* the ids of the executed instructions *)
      conflict_toplevel : bool;
      conflict_future : bool;
    }
    val unfold : ?optim:bool -> t list -> (t * Input.data) list * (t * t * data) list (* computes all potential unfolding of private communications and public inputs *)
  end

  (* operations on initial labelled process that do not affect the decision of equivalence but make it more efficient *)
  module Optimisation : sig
    val remove_non_observable : t -> t (* removes subprocesses that do not contain observable actions *)
    val flatten : t -> t (* push new names as deep as possible to facilitate the detection of symmetries, and flatten unecessary nested constructs *)
    val factor : t -> t (* factors structurally equivalent parallel processes *)
    val factor_up_to_renaming : t -> t -> t * t (* factors at toplevel parallel processes that are structurally equivalent up to bijective channel channel renaming. This factorisation has to be common to the two processes under equivalence check, therefore the two arguments *)
  end

  (* comparison of process skeletons *)
  module Skeleton : sig
    val compare_atomic : t -> t -> int (* compares the skeleton of two processes having no parallel operators at toplevel *)
    val equal : t list -> t list -> bool (* checks whether two processes have the same action at toplevel (after unfolding of parallel operators) *)
  end

  (* normalisation of processes (i.e. execution of instructions other than inputs and outputs) *)
  module Normalise : sig
    type constraints
    val equations : constraints -> (fst_ord, name) Subst.t
    val disequations : constraints -> (fst_ord, name) Diseq.t list
    val constraints_of_equations : (fst_ord, name) Subst.t -> constraints
    exception Bot_disequations
    val normalise : t -> constraints -> (constraints->t->(unit->unit)->unit) -> (unit->unit) -> unit
  end
end = struct

  type t = {
    proc : plain;
    label : Label.t option; (* None if the label has not been attributed yet *)
  }
  and plain =
    | Start of t * id (* a symbol that will only be found at the very toplevel of the initial processes, for convinience. Treated as an input action. *)
    | Input of Channel.t * fst_ord_variable * t * id
    | Output of Channel.t * protocol_term * t * id
    | OutputSure of Channel.t * protocol_term * t * id
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
  let print ?labels:(print_labs:bool=false) ?solution:(fst_subst:(fst_ord, name) Subst.t=Subst.identity) ?highlight:(idh:id= -1) (p:t) : string =
    let on_id i s = if i = idh then bold_red s else s in
    let semicolon s = if s = "" then "" else ";" in
    let rec browse sol bound indent p f_cont =
      let lab delim =
        match p.label with
        | None -> ""
        | Some l when not print_labs -> ""
        | Some l -> Printf.sprintf "lab=%s%s" (Label.to_string l) delim in
      match p.proc with
      | Start (pp,id) ->
        browse sol bound indent pp (fun s ->
          let instr = on_id id (Printf.sprintf "start(%s)" (lab "")) in
          f_cont (Printf.sprintf "\n%s%s%s%s" (tab indent) instr (semicolon s) s)
        )
      | Input(c,x,pp,id) ->
        let sol = Subst.restrict sol (fun y -> not (Variable.is_equal x y)) in
        browse sol (x::bound) indent pp (fun s ->
          let instr =
            on_id id (Printf.sprintf "in(%s%s,%s)" (lab ",") (Channel.to_string c) (Variable.display Terminal Protocol x)) in
          f_cont (Printf.sprintf "\n%s%s%s%s" (tab indent) instr (semicolon s) s)
        )
      | Output(c,t,pp,_) ->
        let t =
          Subst.apply sol t (fun t f -> Rewrite_rules.normalise (f t)) in
        browse sol bound indent pp (fun s ->
          f_cont (Printf.sprintf "\n%sout(%s%s,%s)%s%s" (tab indent) (lab ",") (Channel.to_string c) (Term.display Terminal Protocol t) (semicolon s) s)
        )
      | OutputSure(c,t,pp,id) ->
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
    | OutputSure (c,_,_,_) -> Channel.is_public c
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

  (* The labeled process [lp] should not already have a label, i.e. [lp.label = None]
      No broken symmetries are allowed too.
      Note that only the outputs and input receive a label. The intermediary Bang and Par do not have labels.*)
  let labelling (prefix:Label.t) (lp:t) : t =
    let rec assign i lp f_cont =
      match lp.proc with
      | Par l ->
        assign_list i l (fun l_labelled i_max ->
          f_cont {proc = Par l_labelled; label = None} i_max
        )
      | Bang(b,[],l) ->
        assign_list i l (fun l_labelled i_max ->
            f_cont {proc = Bang(b,[],l_labelled); label = None} i_max
        )
      | Bang _ -> Config.internal_error "[process_session.ml >> labelling] Symmetries should not be broken when labelling."
      | Input _
      | OutputSure _ ->
        f_cont {lp with label = Some (Label.add_position prefix i)} (i+1)
      | New _
      | If _
      | Let _
      | Output _ -> Config.internal_error "[process_session.ml >> labelling] Only normalised processes should be assigned with labels."
      | Start _ -> Config.internal_error "[process_session.ml >> labelling] Unexpected Start constructor."

    and assign_list i l f_cont =
      match l with
      | [] -> f_cont [] i
      | p :: t ->
        assign i p (fun p_labelled i_max ->
          assign_list i_max t (fun l_labelled j_max ->
            f_cont (p_labelled :: l_labelled) j_max
          )
        )
    in

    Config.debug (fun () ->
      if lp.label <> None then
        Config.internal_error "[process_session.ml >> labelling] Already labelled process."
    );
    match lp.proc with
    | Input _
    | OutputSure _ -> {lp with label = Some prefix}
    | Output _
    | If _
    | Let _
    | New _ ->
      Config.internal_error "[process_session.ml >> labelling] Only normalised processes should be assigned with labels."
    | Start _ -> Config.internal_error "[process_session.ml >> labelling] Unexpected Start constructor."
    | Par _
    | Bang _ -> assign 0 lp (fun proc _ -> proc)


  type process_skel = {
    input_skel : (Channel.t * int * Label.t list) list ;
    output_skel : (Channel.t * int * Label.t list) list
  }

  let rec add_in_process_skel_symbol ch label skel_list =
    match skel_list with
    | [] -> [ch,1,[label]]
    | ((ch',size,list_label) as t)::q ->
      let cmp_ch = Symbol.order ch ch' in
      if cmp_ch < 0 then (ch,1,[label])::skel_list
      else if cmp_ch = 0 then (ch',size+1,label::list_label)::q
      else t::(add_in_process_skel_symbol ch label q)

  let add_in_process_skel is_out ch label proc_skel =
    if is_out then
      {proc_skel with output_skel = add_in_process_skel_symbol ch label proc_skel.output_skel}
    else
      {proc_skel with input_skel = add_in_process_skel_symbol ch label proc_skel.input_skel}

  let labelling2 (prefix:Label.t) (lbl_proc:t) : t * process_skel =

    let process_skel = ref {input_skel = []; output_skel = []} in

    let rec assign f_cont next_i lbl_proc  =
      match lbl_proc.proc with
      | OutputSure(c,_,_,_) ->
        let label = Label.add_position prefix next_i in
        process_skel := add_in_process_skel true c label !process_skel;
        f_cont { lbl_proc with label = Some label } (next_i+1)
      | Input(c,_,_,_) ->
        let label = Label.add_position prefix next_i in
        process_skel := add_in_process_skel false c label !process_skel;
        f_cont { lbl_proc with label = Some label } (next_i+1)
      | Par list_lbl_proc ->
        assign_list (fun list_lbl_proc1 next_i1->
          f_cont { proc = Par list_lbl_proc1; label = None } next_i1
        ) next_i list_lbl_proc
      | Bang(b,[],list_lbl_proc) ->
        assign_list (fun list_lbl_proc1 next_i1 ->
          f_cont { proc = Bang(b,[],list_lbl_proc1); label = None } next_i1
        ) next_i list_lbl_proc
      | _ -> Config.internal_error "[process_sessions.ml >> labelling] Labelling is done only on normalised process without broken symmetry."

    and assign_list f_cont next_i = function
      | [] -> f_cont [] next_i
      | p :: t ->
        assign (fun p1 next_i1 ->
          assign_list (fun t1 next_i2 ->
            f_cont (p1 :: t1) next_i2
          ) next_i1 t
        ) next_i p
    in

    Config.debug (fun () ->
      if lbl_proc.label <> None then
        Config.internal_error "[process_session.ml >> labelling] Already labelled process."
    );
    match lbl_proc.proc with
    | Input(ch,_,_,_) ->
      {lbl_proc with label = Some prefix}, { input_skel = [ch,1,[prefix]]; output_skel = [] }
    | OutputSure(ch,_,_,_) ->
      {lbl_proc with label = Some prefix}, { input_skel = []; output_skel = [ch,1,[prefix]] }
    | Par _
    | Bang _ ->
    let lbl_proc' = assign (fun proc _ -> proc) 0 lbl_proc in
      lbl_proc', !process_skel
    | Output _
    | If _
    | Let _
    | New _ -> Config.internal_error "[process_session.ml >> labelling] Only normalised processes should be assigned with labels."
    | Start _ -> Config.internal_error "[process_session.ml >> labelling] Unexpected Start constructor."

  let elements ?init:(init:t list=[]) (lp:t) : t list =
    let rec gather accu lp = match lp with
      | {proc = Par l; _} -> List.fold_left gather accu l
      | {proc = Bang (_,l1,l2); _} -> List.fold_left gather accu (l1@l2)
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
      Variable.Renaming.compose accu x xx, xx::l
    ) (accu,[]) l

  (* generates several copies of a process with freshly renamed New names, input variables, and positions *)
  let fresh_copy (nb:int) (p:t) (id:id) (f_cont:id->t list->'a) : 'a =
    let rec browse rho_v rho_n bound_vars p id f_cont =
      let apply t = apply_renaming_on_term rho_n (apply_alpha_on_term rho_v t) in
      match p.proc with
      | Input(c,x,p,_) ->
        Config.debug (fun () ->
          if Variable.quantifier_of x != Free
          then Config.internal_error "[process_sessions.ml >> fresh_copy] All variables should be free."
        );
        let xx = Variable.fresh_from x in
        browse (Variable.Renaming.compose rho_v x xx) rho_n (xx::bound_vars) p (id+1) (fun id_max p_fresh ->
          f_cont id_max {proc = Input(Channel.apply_renaming rho_n c,xx,p_fresh,id); label = None}
        )
      | Output(c,t,p,_) ->
        browse rho_v rho_n bound_vars p (id+1) (fun id_max p_fresh ->
          f_cont id_max {proc = Output(Channel.apply_renaming rho_n c,apply t,p_fresh,id); label = None}
        )
      | OutputSure(c,t,p,_) ->
        Config.internal_error "[process_session.ml >> fresh_copy] Outputs should not be sure before the analysis starts."
      | If(u,v,p1,p2) ->
        let uu = apply u in
        let vv = apply v in
        browse rho_v rho_n bound_vars p1 id (fun id1 p1_fresh ->
          browse rho_v rho_n bound_vars p2 id1 (fun id2 p2_fresh ->
            f_cont id2 {proc = If(uu,vv,p1_fresh,p2_fresh); label = None}
          )
        )
      | Let(u,u',v,p1,p2) ->
        (* VINCENT: Improve that part. I think we could have something more linear. Add that in terms.ml. I leave the warning for now. *)
        let bound_vars_u = Term.get_vars_not_in Protocol u bound_vars in
        let fresh' = Variable.Renaming.fresh Protocol bound_vars_u Universal in
        let (rho_v',new_bounds) = fresh_vars_and_renaming rho_v bound_vars_u in
        let uu =
          apply_renaming_on_term rho_n (apply_alpha_on_term rho_v' u) in
        let uu' = apply_alpha_on_term fresh' (apply u) in
        let vv = apply v in
        browse rho_v' rho_n (List.rev_append new_bounds bound_vars) p1 id (fun id1 p1_fresh ->
          browse rho_v rho_n bound_vars p2 id1 (fun id2 p2_fresh ->
            f_cont id2 {proc = Let(uu,uu',vv,p1_fresh,p2_fresh); label = None}
          )
        )
      | New(n,p) ->
        let nn = Name.fresh_from n in
        browse rho_v (Name.Renaming.compose rho_n n nn) bound_vars p id (fun id_max p_fresh ->
          f_cont id_max {proc = New(nn,p_fresh); label = None}
        )
      | Par l ->
        browse_list rho_v rho_n bound_vars l id (fun id_max l_fresh ->
          f_cont id_max {proc = Par l_fresh; label = None}
        )
      | Bang(Strong,[],l) ->
        browse_list rho_v rho_n bound_vars l id (fun id_max l_fresh ->
          f_cont id_max {proc = Bang(Strong,[],l_fresh); label = None}
        )
      | Bang _ -> Config.internal_error "[process_session.ml >> fresh_copy] Unexpected type of bang."
      | Start _ -> Config.internal_error "[process_session.ml >> fresh_copy] Unexpected Start constructor."

    and browse_list rho_v rho_n bound_vars l id f_cont = match l with
      | [] -> f_cont id []
      | p :: t ->
          browse rho_v rho_n bound_vars p id (fun id_max p_fresh ->
            browse_list rho_v rho_n bound_vars t id_max (fun id_l l_fresh ->
              f_cont id_l (p_fresh::l_fresh)
            )
          )
    in

    let rec browse_iter nb p id f_cont =
      if nb = 0 then f_cont id []
      else
        browse Variable.Renaming.identity Name.Renaming.identity [] p id (fun id_max p_fresh ->
          browse_iter (nb-1) p id_max (fun id_final l_fresh ->
            f_cont id_final (p_fresh::l_fresh)
          )
        ) in

    browse_iter nb p id f_cont

  (* conversion from expansed processes
  TODO. include a check that no names used as private channels are output *)
  let of_expansed_process ?preprocessing:(preprocessing:t->t=fun x->x) (p:Process.expansed_process) : t =
    let rec browse bound_vars p id f_cont =
      match p with
      | Process.Nil ->
        f_cont id {proc = Par []; label = None}
      | Process.Output(ch,t,pp) ->
        browse bound_vars pp (id+1) (fun id_max p_conv ->
          f_cont id_max {proc = Output(Channel.from_term ch,t,p_conv,id); label = None}
        )
      | Process.Input(ch,x,pp) ->
        browse (x::bound_vars) pp (id+1) (fun id_max p_conv ->
          f_cont id_max {proc = Input(Channel.from_term ch,x,p_conv,id); label = None}
        )
      | Process.IfThenElse(t1,t2,pthen,pelse) ->
        browse bound_vars pthen id (fun id1 pthen' ->
          browse bound_vars pelse id1 (fun id2 pelse' ->
            f_cont id2 {proc = If(t1,t2,pthen',pelse'); label = None}
          )
        )
      | Process.Let(t1,t2,pthen,pelse) ->
        let bound_vars_t1 = Term.get_vars_not_in Protocol t1 bound_vars in
        let fresh = Variable.Renaming.fresh Protocol bound_vars_t1 Universal in
        let tt1 = Variable.Renaming.apply_on_terms fresh t1 (fun x f -> f x) in
        browse (List.rev_append bound_vars_t1 bound_vars) pthen id (fun id1 pthen ->
          browse bound_vars pelse id1 (fun id2 pelse ->
            f_cont id2 {proc = Let(t1,tt1,t2,pthen,pelse); label = None}
          )
        )
      | Process.New(n,pp) ->
        browse bound_vars pp id (fun id_max p_conv ->
          f_cont id_max {proc = New(n,p_conv); label = None}
        )
      | Process.Par lp ->
        browse_list bound_vars lp id (fun id_max l_conv ->
          match l_conv with
          | [p] -> f_cont id_max p
          | l -> f_cont id_max {proc = Par l; label = None}
        )
      | Process.Choice _ -> Config.internal_error "[process_session.ml >> plain_process_of_expansed_process] *Choice* not implemented yet for equivalence by session."

    and browse_list bound_vars l id f_cont =
      match l with
      | [] -> f_cont id []
      | (pp,i) :: t ->
        browse bound_vars pp id (fun id_max p_conv ->
          browse_list bound_vars t id_max (fun id_l l_conv ->
            if i = 1 then f_cont id_l (p_conv :: l_conv)
            else
              fresh_copy i p_conv id_l (fun id_final l_fresh ->
                f_cont id_final ({proc = Bang(Strong,[],l_fresh); label = None} :: l_conv)
              )
          )
        ) in

    browse [] p 1 (fun _ p_conv ->
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
        let leftovers_pp = if tl = [] then leftovers else {proc = Bang(b,[],tl); label = None}::leftovers in
        if b = Strong || optim then
          unfold forall accu leftovers_pp pp f_cont
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
      | p :: t ->
        unfold forall accu (List.rev_append t leftovers) p (fun accu1 ->
          unfold_list forall accu1 (p::leftovers) t f_cont
        )

    and unfold_bang memo accu leftovers t f_cont =
      let leftovers1 =
        {proc = Bang(Partial,[],List.rev_append memo t); label = None} :: leftovers in
      unfold false accu leftovers1 p (fun accu1 ->
        unfold_bang (p::memo) accu1 leftovers t f_cont
      ) in

    unfold optim accu leftovers p (fun accu -> accu)


  module Input = struct
    type data = {
      channel : Channel.t;
      var : fst_ord_variable;
      optim : bool;
      lab : Label.t;
      leftovers : t list;
      id : id;
    }
    (* Processes given to [unfold_input] should all be normalised. Moreover, [unfold_input] is applied when there is no more public output available, hence no public output at top-level. *)
    (* let unfold ?(optim=false) (priv:t->data->'a list->'a list) (l:t list) : (t * data) list * 'a list =
      let add_accu f p leftovers forall accu =
        match p.proc with
        | OutputSure _ -> accu
        | Input(ch,x,pp,id) ->
          let idata = {
            channel = ch;
            var = x;
            optim = forall;
            lab = get_label p;
            leftovers = leftovers;
            id = id;
          } in
          f pp idata accu in
      unfold_with_leftovers optim [] (add_accu (fun x y l -> (x,y)::l)) [] (add_accu priv) l *)
    let unfold = failwith "to remove"
  end

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
        | OutputSure(c,_,_,_) when not (Channel.is_public c) -> f_cont accu
        | OutputSure(c,t,pp,id) ->
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
      | Bang(b,l1,l2) -> (* non trivial restauration: symmetry cannot be restaured to Strong *)
        {lp with proc = Bang (Partial,[],List.map restaure_sym l1 @ l2)}
      | Let _
      | If _
      | New _
      | Output _ -> Config.internal_error "[process_session.ml >> restaure_sym] Should only be applied on normalised processes."
      | Start _ -> Config.internal_error "[process_session.ml >> restaure_sym] Unexpected Start constructor."
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
    let unfold ?(optim=false) (l:t list) : (t * Input.data) list * (t * t * data) list =
      List.fold_left_with_memo (fun accu p leftovers_left leftovers_right ->
        let leftovers = List.rev_append leftovers_left leftovers_right in
        unfold_with_leftovers optim accu (fun proc leftovers_proc forall (ac_pub,ac_priv) ->
          match proc.proc with
          | Input(c,x,pp,id) when Channel.is_public c ->
            let res : Input.data = {
              channel = c;
              var = x;
              optim = forall;
              lab = get_label proc;
              leftovers = leftovers_proc;
              id = id;
            } in
            (pp,res)::ac_pub,ac_priv
          | OutputSure(c_out,t,pp_out,id_out) when not (Channel.is_public c_out) ->
            let ac_priv_upd =
              List.fold_left_with_memo (fun ac_priv1 proc1 leftovers1_left leftovers1_right ->
                unfold_with_leftovers optim ac_priv1 (fun proc2 leftovers_proc2 forall_in ac_priv2 ->
                  match proc2.proc with
                  | Input(c_in,x,pp_in,id_in) when Channel.equal c_in c_out ->
                    let res = {
                      channel = c_in;
                      var = x;
                      term = t;
                      optim = forall && forall_in;
                      labs = get_label proc, get_label proc2;
                      leftovers = leftovers_proc2;
                      ids = id_in,id_out;
                      conflict_toplevel = false;
                      conflict_future = false; (* TODO implem the optim? *)
                    } in
                    (pp_in,pp_out,res) :: ac_priv2
                  | _ -> ac_priv2
                ) proc1 (List.rev_append leftovers1_left leftovers1_right)
              ) ac_priv leftovers_proc in
            ac_pub,ac_priv_upd
        ) p leftovers
      ) ([],[]) l
  end

  module Optimisation = struct
    (* removing subprocesses that cannot trigger observable actions (for optimisation purposes; does not affect the decision of equivalence) *)
    let void = {proc = Par []; label = None}
    let replace (p:t) (plain:plain) : t = {p with proc = plain}
    (* VINCENT: Possible new function for remove_non_observable. CAREFUL: Your function is never called. *)
    let rec remove_non_observable p0 =
      match p0.proc with
      | Start(p,id) -> { p0 with proc = Start(remove_non_observable p,id) }
      | Output(c,t,p,id) -> { p0 with proc = Output(c,t,remove_non_observable p,id) }
      | OutputSure _ -> Config.internal_error "[process_sessions.ml >> Optimisation.remove_non_observable] Should only be applied at the beginning of the verification."
      | Input(c,x,p,id) -> { p0 with proc = Input(c,x,remove_non_observable p,id) }
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
  end

  (* TODO : SKELETON NEEDS TO BE UPDATED FOR PRIVATE CHANNELS *)
  module Skeleton = struct
    (* comparison of skeletons (parallel operators excluded) *)
    let compare_atomic (p1:t) (p2:t) : int =
      match p1.proc, p2.proc with
      | OutputSure _ , Input _  -> -1
      | Input _, OutputSure _ -> 1
      | Input(c1,_,_,_), Input(c2,_,_,_)
      | OutputSure(c1,_,_,_), OutputSure(c2,_,_,_) -> Channel.compare c1 c2
      | _ -> Config.internal_error "[process_session.ml >> compare_io_process] Unexpected case."

    (* Checks whether two lists of atomic processes have identical skeletons.
    TODO: current implementation quite naive (does not take symmetries into account), may be improved. *)
    let equal (p1:t list) (p2:t list) : bool =
      let sort = List.fast_sort (fun p q -> compare_atomic p q) in
      let elts l = List.fold_left (fun accu p -> elements ~init:accu p) [] l in
      let l1 = sort (elts p1) in
      let l2 = sort (elts p2) in
      try List.for_all2 (fun p q -> compare_atomic p q = 0) l1 l2
      with Invalid_argument _ -> false
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
      | Output(ch,t,p,id) ->
        let tt = Rewrite_rules.normalise (Subst.apply cstr.equations t (fun x f -> f x)) in

        let eqn_modulo_list_result =
          try
            EqList (Modulo.syntactic_equations_of_equations [Modulo.create_equation tt tt])
          with
            | Modulo.Bot -> EqBot
            | Modulo.Top -> EqTop in

        begin match eqn_modulo_list_result with
          | EqBot -> f_cont cstr {p with proc = Par []} f_next
          | EqTop -> f_cont cstr {p with proc = OutputSure(ch,t,p,id)} f_next
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
                    fun () -> f_cont {equations = new_eqn; disequations = new_diseqn} {proc with proc = OutputSure(ch,t,p,id)} acc_f_next
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
module BijectionSet : sig
  type t
  val initial : t (* a singleton containing the unique matching between two processes of label Label.initial *)
  val update : Label.t -> Label.t -> Labelled_process.t -> Labelled_process.t -> t -> t option (* [update l1 l2 p1 p2 bset] restricts the set [bset] to the bijections mapping [l1] to [l2]. In case [l1] is not in the domain of these bijections, the domain of [bset] is also extended to allow matchings of labels of p1 and p2 *)
  val print : t -> unit
end = struct
  (* sets of bijections with the skeleton-compatibility requirement *)
  (* TODO. may ake the datastructure more efficient. Could be more practical when there are a lot of singletons to handle the operation "get all potential labels matching with a given label l". *)
  type t = (Label.Set.t * Label.Set.t) list

  (* the initial bijection set *)
  let initial : t =
    [Label.Set.singleton Label.initial, Label.Set.singleton Label.initial]

  (* partitions a list in equiv. classes wrt to some equivalence relation *)
  type 'a partition = 'a list list
  let equivalence_classes (equiv:'a->'a->bool) (l:'a list) : 'a partition =
    let rec insert memo partition x =
      match partition with
      | [] -> [x] :: memo
      | [] :: t -> Config.internal_error "[process_session.ml >> equivalence_classes] Unexpected case"
      | (y::_ as equiv_class) :: t ->
        if equiv x y then List.rev_append memo ((x::equiv_class) :: t)
        else insert (equiv_class :: memo) t x in
    List.fold_left (insert []) [] l

  (* links two equivalence relations to form a bijection set. Returns None if the resulting set is empty. *)
  let link_partitions (equiv:'a->'a->bool) (p1:'a partition) (p2:'a partition) : ('a list * 'a list) list option =
    let rec browse accu p1 p2 =
      match p1 with
      | [] -> if p2 <> [] then None else Some accu
      | [] :: _ ->
        Config.internal_error "[process_session >> link_partitions] Unexpected case"
      | (x::_ as ec1) :: p1' ->
        match List.find_and_remove (fun ec2 -> equiv x (List.hd ec2)) p2 with
        | None,_ -> None
        | Some ec2,p2' ->
          if List.length ec1 <> List.length ec2 then None
          else browse ((ec1,ec2)::accu) p1' p2' in
    browse [] p1 p2

  (* creates the bijection_set containing the possible matchings of two lists of
  parallel processes. *)
  let init (accu:t) (fp1:Labelled_process.t) (fp2:Labelled_process.t) : t option =
    let check_skel lp1 lp2 =
      Labelled_process.Skeleton.compare_atomic lp1 lp2 = 0 in
    let partition lp =
      equivalence_classes check_skel (Labelled_process.elements lp) in
    match link_partitions check_skel (partition fp1) (partition fp2) with
    | None -> None
    | Some l ->
      let convert procs =
        Label.Set.of_list (List.rev_map Labelled_process.get_label procs) in
      Some (List.fold_left (fun ac (ec1,ec2) -> (convert ec1, convert ec2) :: ac) accu l)

  (* prints a bijection set *)
  let print (bset:t) : unit =
    List.iter (fun (s1,s2) ->
      Label.Set.iter (fun lab -> Printf.printf "%s;" (Label.to_string lab)) s1;
      Printf.printf "   [MATCHABLE WITH]   ";
      Label.Set.iter (fun lab -> Printf.printf "%s;" (Label.to_string lab)) s2;
      print_endline "";
    ) bset


  (* updates a bijection set after two matched transitions on labels (l1,l2), where the subprocesses reduced by the transition become p1 and p2 respectively. *)
  let update (l1:Label.t) (l2:Label.t) (p1:Labelled_process.t) (p2:Labelled_process.t) (bset:t) : t option =
    let rec search memo s =
      match s with
      | [] -> None
      | (ll1,ll2) :: t ->
        match Label.Set.find_opt l1 ll1, Label.Set.find_opt l2 ll2 with
        | None,None -> search ((ll1,ll2) :: memo) t
        | Some _,Some _ ->
          let label_discardable =
            Labelled_process.not_pure_io_toplevel p1 || Labelled_process.not_pure_io_toplevel p2 in
          let bset_upd =
            if Label.Set.is_singleton ll1 then
              if label_discardable then List.rev_append memo t
              else List.rev_append memo ((ll1,ll2)::t)
            else
              let ll1' = Label.Set.remove l1 ll1 in
              let ll2' = Label.Set.remove l2 ll2 in
              let single1 = Label.Set.singleton l1 in
              let single2 = Label.Set.singleton l2 in
              if label_discardable then List.rev_append memo ((ll1',ll2')::t)
              else List.rev_append memo ((single1,single2)::(ll1',ll2')::t) in
          if label_discardable then
            init bset_upd p1 p2
          else Some bset_upd
        | _ -> None in
    search [] bset


  (* given a bijection set and a label l, computes the set of labels that are
  compatible with l wrt one bijection.
  NB. Not used anymore in the current version *)
  let get_compatible_labels (l:Label.t) (s:t) : Label.t list =
    match List.find_opt (fun (labset,_) -> Label.Set.mem l labset) s with
    | None -> Config.internal_error "[process_session.ml >> get_compatible_labels] Unexpected case"
    | Some pair -> Label.Set.elements (snd pair)
end


(* type for representing internal states *)
module Configuration : sig
  type t
  val print_trace : (fst_ord, name) Subst.t -> (snd_ord, axiom) Subst.t -> t -> string (* returns a string displaying the trace needed to reach this configuration *)
  val to_process : t -> Labelled_process.t (* conversion into a process, for interface purpose *)
  val check_block : (snd_ord, axiom) Subst.t -> t -> bool (* verifies the blocks stored in the configuration are authorised *)
  val inputs : t -> Labelled_process.t list (* returns the available inputs *)
  val outputs : t -> Labelled_process.t list (* returns the available outputs (in particular they are executable, i.e. they output a message). *)
  val of_expansed_process : Process.expansed_process -> t (* converts a process as obtained from the parser into a configuration. This includes some cleaning procedure as well as factorisation. *)
  val normalise : ?context:(Labelled_process.t->Labelled_process.t) -> Label.t -> t -> (fst_ord, name) Subst.t -> (Labelled_process.Normalise.constraints->t->Labelled_process.t->unit) -> unit (* normalises a configuration, labels the new process, and puts it in standby for skeleton checks. In case an output has just been executed, the optional ?context argument gives the process context of the execution in order to reconstruct the symmetries afterwards. *)
  val check_skeleton : t -> t -> bool (* compares two skeletons in standby *)
  val release_skeleton : t -> t option (* assuming all skeletons have been checked, marks them as not in standby anymore. *)

  (* a module for operating on transitions *)
  module Transition : sig
    type kind =
      | RFocus
      | RPos
      | RNeg
      | RStart
    val print_kind : kind option -> unit
    val next : t -> kind option (* computes the next kind of transition to apply (None if the process has no transition possible). *)
    val apply_neg : axiom -> Labelled_process.t -> Labelled_process.Output.data -> Labelled_process.t list -> t -> t (* executes an output in a configuration *)
    val apply_pos : snd_ord_variable -> t -> Labelled_process.Input.data * t (* executes a focused input in a configuration *)
    val apply_focus : snd_ord_variable -> (Labelled_process.t * Labelled_process.Input.data) -> t -> t (* focuses an input in a configuration *)
    val apply_start : t -> t (* removes the start at the beginning of the process *)
  end
end = struct
  type state = {
    current_proc : Labelled_process.t;
    id : Labelled_process.id;
    label : Label.t;
  }
  type action =
    | InAction of Channel.t * snd_ord_variable * protocol_term * state
    | OutAction of Channel.t * axiom * protocol_term * state

  type t = {
    input_proc : Labelled_process.t list;
    focused_proc : Labelled_process.t option;
    sure_output_proc : Labelled_process.t list;
    sure_unchecked_skeletons : (Labelled_process.t * (Labelled_process.t -> Labelled_process.t)) option;
    to_normalise : Labelled_process.t option;
    trace : action list;
    ongoing_block : Block.t;
    previous_blocks : Block.t list;
  }

  let to_process (conf:t) : Labelled_process.t =
    let l = conf.input_proc @ conf.sure_output_proc in
    match conf.focused_proc with
    | None -> Labelled_process.of_process_list l
    | Some p -> Labelled_process.of_process_list (p::l)

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
      Printf.sprintf "%s%s" (bold_blue msg) (Labelled_process.print ~solution:fst_subst ~highlight:s.id s.current_proc)
    | OutAction(ch,ax,t,s) ->
      let output =
        Rewrite_rules.normalise (Subst.apply fst_subst t (fun x f -> f x)) in
      let msg =
        Printf.sprintf "output on channel %s of %s, referred as %s\n" (Channel.to_string ch) (Term.display Terminal Protocol output) (Axiom.display Terminal ax) in
      Printf.sprintf "%s%s" (bold_blue msg) (Labelled_process.print ~solution:fst_subst ~highlight:s.id s.current_proc)

  let print_trace (fst_subst:(fst_ord,name) Subst.t) (snd_subst:(snd_ord,axiom) Subst.t) (conf:t) : string =
    snd (
      List.fold_left (fun (count,accu) act ->
        count-1,Printf.sprintf "\n\n%s %s%s" (bold_blue (Printf.sprintf "%d)" count)) (print_action fst_subst snd_subst act) accu
      ) (List.length conf.trace,"") conf.trace
    )

  let check_block (snd_subst:(snd_ord,axiom) Subst.t) (c:t) : bool =
    Block.is_authorised c.previous_blocks c.ongoing_block snd_subst

  let inputs (conf:t) : Labelled_process.t list =
    conf.input_proc

  let outputs (conf:t) : Labelled_process.t list =
    conf.sure_output_proc

  let of_expansed_process (p:Process.expansed_process) : t =
    (* Printf.printf "converting %s\n" (Labelled_process.print (Labelled_process.of_expansed_process p)); *)
    {
      input_proc = [];
      focused_proc = Some (Labelled_process.of_expansed_process p);
      sure_output_proc = [];
      sure_unchecked_skeletons = None;
      to_normalise = None;
      trace = [];

      ongoing_block = Block.create Label.initial;
      previous_blocks = [];
    }

  let normalise ?context:(rebuild:Labelled_process.t->Labelled_process.t=fun t->t) (prefix:Label.t) (conf:t) (eqn:(fst_ord, name) Subst.t) (f_cont:Labelled_process.Normalise.constraints->t->Labelled_process.t->unit) : unit =
    Config.debug (fun () ->
      if conf.sure_unchecked_skeletons <> None then
        Config.internal_error "[process_session.ml >> normalise_configuration] Sure unchecked should be empty."
    );

    let eqn_cast = Labelled_process.Normalise.constraints_of_equations eqn in
    match conf.to_normalise, conf.focused_proc with
      | None, None -> f_cont eqn_cast conf (Labelled_process.empty prefix)
      | None, Some p ->
        Labelled_process.Normalise.normalise p eqn_cast (fun gather p_norm f_next ->
          let labelled_p = Labelled_process.labelling prefix p_norm in
          f_cont gather {conf with focused_proc = Some labelled_p} labelled_p;
          f_next ()
        ) (fun () -> ())
      | Some p, None ->
        Labelled_process.Normalise.normalise p eqn_cast (fun gather p_norm f_next ->
          let labelled_p = Labelled_process.labelling prefix p_norm in
          let conf_rel = {conf with
            sure_unchecked_skeletons = Some (labelled_p,rebuild);
            to_normalise = None;
          } in
          f_cont gather conf_rel labelled_p;
          f_next ()
        ) (fun () -> ())
      | _, _ -> Config.internal_error "[process_session.ml >> normalise] A configuration cannot be released and focused at the same time."

  let check_skeleton (conf1:t) (conf2:t) : bool =
    match conf1.focused_proc, conf2.focused_proc, conf1.sure_unchecked_skeletons, conf2.sure_unchecked_skeletons with
    | Some p1, Some p2, None, None
    | None, None, Some (p1,_), Some (p2,_) ->
      Labelled_process.Skeleton.equal [p1] [p2]
    | _ ->
      Config.internal_error "[process_session.ml >> check_skeleton] Comparing processes in inconsistent states."

  let release_skeleton (c:t) : t option =
    match c.focused_proc, c.sure_unchecked_skeletons with
    | Some p, _ ->
      begin match Labelled_process.get_proc p with
      | Labelled_process.Input _ -> Some c
      | Labelled_process.OutputSure _ ->
        Some {c with focused_proc = None; sure_output_proc = p::c.sure_output_proc}
      | _ ->
        if Labelled_process.nil p then None
        else if Labelled_process.contains_public_output_toplevel p then
          Some {c with focused_proc = None; sure_output_proc = p::c.sure_output_proc}
        else
          Some {c with focused_proc = None; input_proc = p::c.input_proc} end
    | _, Some (p,rebuild) ->
      let pp = rebuild p in
      begin match Labelled_process.get_proc pp with
      | Labelled_process.Input _ ->
        Some {c with sure_unchecked_skeletons = None; input_proc = pp::c.input_proc}
      | Labelled_process.OutputSure _ ->
        Some {c with sure_unchecked_skeletons = None; sure_output_proc = pp::c.sure_output_proc}
      | _ ->
        if Labelled_process.nil pp then
          Some {c with sure_unchecked_skeletons = None}
        else if Labelled_process.contains_public_output_toplevel pp then
          Some {c with sure_unchecked_skeletons = None; sure_output_proc = pp::c.sure_output_proc}
        else
          Some {c with sure_unchecked_skeletons = None; input_proc = Labelled_process.Output.restaure_sym pp::c.input_proc} end
    | _, _ ->
        Config.internal_error "[process_session.ml >> release_skeleton] A process is either focused or released."

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
      | Some p ->
        begin match Labelled_process.get_proc p with
        | Labelled_process.Input _ -> Some RPos
        | Labelled_process.Start _ -> Some RStart
        | _ ->
          Config.internal_error "[process_session.ml >> Configuration.Transition.next] Ill-formed focused state, should have been released or normalised." end
      | None ->
        if c.sure_output_proc <> [] then Some RNeg
        else match c.input_proc with
          | [] -> None
          | _ -> Some RFocus

    (* syntactic transformation of a configuration at the start of the analysis *)
    let apply_start (conf:t) : t =
      match conf.focused_proc with
      | Some p ->
        begin match Labelled_process.get_proc p with
        | Labelled_process.Start (pp,_) -> {conf with focused_proc = Some pp}
        | _ -> Config.internal_error "[process_session.ml Configuration.Transition.apply_start] Error during the initialisation of processes. (1)" end
      | _ ->
        Config.internal_error "[process_session.ml >> Configuration.Transition.apply_start] Error during the initialisation of processes. (2)"

    (* syntactic transformation of a configuration after executing an output *)
    let apply_neg (ax:axiom) (p:Labelled_process.t) (od:Labelled_process.Output.data) (leftovers:Labelled_process.t list) (conf:t) : t =
      let state = {
        current_proc = to_process conf;
        id = od.id;
        label = od.lab;
      } in
      let ch = od.channel in
      let term = od.term in
      {conf with
        to_normalise = Some p;
        sure_output_proc = leftovers;
        trace = OutAction(ch,ax,term,state)::conf.trace;
        ongoing_block = Block.add_axiom ax conf.ongoing_block;
      }

    (* syntactic transformation of a configuration after executing a focused input. Also retrieves and returns the input_data of the focus state. *)
    let apply_pos (var_X:snd_ord_variable) (conf:t) : Labelled_process.Input.data * t =
      match conf.focused_proc with
      | Some p ->
        begin match Labelled_process.get_proc p with
        | Labelled_process.Input(ch,x,pp,id) ->
          let idata : Labelled_process.Input.data = {
            channel = ch;
            var = x;
            lab = Labelled_process.get_label p;
            id = id;
            leftovers = []; (* field not relevant here *)
            optim = true; (* field not relevant here *)
          } in
          let state : state = {
            current_proc = to_process conf;
            id = idata.id;
            label = idata.lab;
          } in
          let conf_app = {conf with
            focused_proc = Some pp;
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
        current_proc = to_process conf;
        id = idata.id;
        label = idata.lab;
      } in
      {conf with
        input_proc = idata.leftovers;
        focused_proc = Some pp;
        ongoing_block = Block.add_variable var_X (Block.create idata.lab);
        previous_blocks = conf.ongoing_block :: conf.previous_blocks;
        trace = InAction(idata.channel,var_X,Term.of_variable idata.var,state) :: conf.trace;
      }
  end
end
