(* Process manipulation for equivalence by session *)

open Term
open Display
open Extensions



(* a module for representing process labels *)
module Label : sig
  type t
  val initial : t (* an initial, empty label *)
  val add_position : t -> int -> t (* adds a position at the end of a label *)
  val independent : t -> t -> int (* returns 0 if one label is prefix of the other, and compares them lexicographically otherwise *)
  val to_string : t -> string
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
    | [],_
    | _,[] -> 0
    | p::l,pp::ll when p <> pp -> compare p pp
    | _::l,_::ll -> independent l ll
end


(* a module for representing blocks *)
module Block : sig
  type t
  val create : Label.t -> t (* creation of a new empty block *)
  val add_variable : snd_ord_variable -> t -> t (* adds a second order variable in a block *)
  val add_axiom : axiom -> t -> t (* adds an axiom in a block *)
  val is_authorised : t list -> t -> (snd_ord, axiom) Subst.t -> bool (* checks whether a block is authorised after a list of blocks *)
end = struct
  module IntSet = Set.Make(struct type t = int let compare = compare end)

  type t = {
    label : Label.t;
    recipes : snd_ord_variable list; (* There should always be variables *)
    bounds_axiom : (int * int) option; (* lower and upper bound on the axiom index used *)
    maximal_var : int;
    used_axioms : IntSet.t
  }

  (* creates an empty block *)
  let create (label:Label.t) : t = {
      label = label;
      recipes = [];
      bounds_axiom = None;
      maximal_var = 0;
      used_axioms = IntSet.empty
  }

  (* adds a second-order variable in the recipes of a block *)
  let add_variable (snd_var:snd_ord_variable) (block:t) : t =
    { block with recipes = (snd_var :: block.recipes) }

  (* adds an axiom in a block and updates the bounds *)
  let add_axiom (ax:axiom) (block:t) : t =
    match block.bounds_axiom with
    | None ->
      let b = Axiom.index_of ax in
      {block with bounds_axiom = Some (b,b)}
    | Some (i,_) ->
      {block with bounds_axiom = Some (i,Axiom.index_of ax)}

  (* checking whether a block is not allowed after a block list *)
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

  (* checking whether a block is authorised after a block list *)
  let is_authorised (block_list:t list) (cur_block:t) (snd_subst:(snd_ord,axiom) Subst.t) : bool =
    match block_list with
    | [] -> true
    | _ ->
      let block_list_upd =
        apply_snd_subst_on_block snd_subst (cur_block::block_list) in
      let rec explore_block block_list =
        match block_list with
        | []
        | [_] -> true
        | block::q -> not (is_faulty_block block q) && explore_block q in
      explore_block block_list_upd
end


(* a module for labelled processes *)
module Labelled_process : sig
  type t

  type bang_status
  type plain =
    | Start of t
    | Input of symbol * fst_ord_variable * t
    | Output of symbol * protocol_term * t
    | OutputSure of symbol * protocol_term * t
    | If of protocol_term * protocol_term * t * t
    (* | Let of protocol_term * protocol_term * labelled_process * labelled_process *)
    | New of name * t
    | Par of t list
    | Bang of bang_status * t list * t list

  val print : t -> string
  val of_expansed_process : Process.expansed_process -> t (* converts an expansed process into a process, starting with a Start constructor and label [initial]. *)
  val elements : ?init:(t list) -> t -> t list (* extracts the list of parallel subprocesses *)
  val nil : t -> bool (* checks if this represents the null process *)
  val empty : Label.t -> t (* a labelled process with empty data. For typing purposes (only way to construct a Labelled_process.t outside of this module) *)
  val contains_output : t -> bool (* checks whether a normalised process contains an executable output *)
  val contains_par : t -> bool (* checks whether a normalised process does not start right away by an input or an output *)
  type input_data = {
    channel : symbol; (* channel on which the input is performed *)
    var : fst_ord_variable; (* variable bound by the input *)
    optim : bool; (* whether this input is needed for forall processes *)
    lab : Label.t; (* label of the executed input *)
    leftovers : t list; (* what remains after the input is executed *)
  }
  val unfold_input : ?optim:bool -> t list -> (t * input_data) list (* function computing all potential ways of unfolding one input from a list of processes. *)
  type output_data = {
    channel : symbol; (* channel on which the output is performed *)
    term : protocol_term; (* output term *)
    optim : bool; (* whether this output is needed for forall processes *)
    lab : Label.t; (* label of the executed output *)
    context : t -> t; (* suroundings of the executed output *)
  }
  val unfold_output : ?optim:bool -> t -> (t * output_data) list (* function computing all potential ways of unfolding one output from a process.
  NB. Unfolding outputs break symmetries (just as symmetries), but they can be restaured at the end of negative phases (see function [restaure_sym]). *)
  val restaure_sym : t -> t (* restaures symmetries that have been temporarily broken by unfolding outputs *)
  val labelling : Label.t -> t -> t (* assigns labels to the parallel processes at toplevel, with a given label prefix *)
  val get_label : ?error_msg:string -> t -> Label.t (* gets the label of a process, and returns an error message if it has not been assigned *)
  val get_proc : t -> plain

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
    | Start of t (* a symbol that will only be found at the very toplevel of the initial processes, for convinience. Treated as an input action. *)
    | Input of symbol * fst_ord_variable * t
    | Output of symbol * protocol_term * t
    | OutputSure of symbol * protocol_term * t
    | If of protocol_term * protocol_term * t * t
    (* | Let of protocol_term * protocol_term * labelled_process * labelled_process *)
    | New of name * t
    | Par of t list
    | Bang of bang_status * t list * t list (* The two lists model the replicated processes, the first one being reserved for processes where symmetries are temporarily broken due to the execution of outputs. *)

  and bang_status =
    | Repl (* symmetry up to structural equivalence *)
    | Channel (* symmetry up to structural equivalence and channel renaming *)

  (* checks whether a process models the nil process *)
  let nil (p:t) : bool =
    match p.proc with
    | Par []
    | Bang (_,[],[]) -> true
    | _ -> false

  (* en empty process *)
  let empty (lab:Label.t) : t = {proc = Par []; label = Some lab}

  (* extracts the data of a process *)
  let get_label ?error_msg:(s="[process_session.ml >> Label.Process.get_label] Unassigned label.") (p:t) : Label.t =
    match p.label with
    | None -> Config.internal_error s
    | Some lab -> lab

  let get_proc (p:t) : plain = p.proc


  let print (p:t) : string =
    let lab =
      match p.label with
      | None -> "X"
      | Some l -> Label.to_string l in
    let rec browse p f_cont =
      match p.proc with
      | Start pp ->
        browse pp (fun s ->
          f_cont (Printf.sprintf "Start(lab=%s); %s" lab s)
        )
      | Input(c,x,pp) ->
        browse pp (fun s ->
          f_cont (Printf.sprintf "In(lab=%s,%s,%s); %s" lab (Symbol.display Latex c) (Variable.display Latex Protocol x) s)
        )
      | Output(c,t,pp) ->
        browse pp (fun s ->
          f_cont (Printf.sprintf "OutUNSURE(lab=%s,%s,%s); %s" lab (Symbol.display Latex c) (Term.display Latex Protocol t) s)
        )
      | OutputSure(c,t,pp) ->
        browse pp (fun s ->
          f_cont (Printf.sprintf "Out(lab=%s,%s,%s); %s" lab (Symbol.display Latex c) (Term.display Latex Protocol t)s)
        )
      | If(u,v,p1,p2) ->
        browse p1 (fun s1 ->
          browse p2 (fun s2 ->
            f_cont (Printf.sprintf "if %s=%s then (%s) else (%s)" (Term.display Latex Protocol u) (Term.display Latex Protocol v) s1 s2)
          )
        )
      | New(n,pp) ->
        browse pp (fun s ->
          f_cont (Printf.sprintf "new %s; %s" (Name.display Latex n) s)
        )
      | Par l ->
        f_cont (List.fold_left (fun accu pp ->
          accu ^ browse pp (fun s -> "\n| "^s)
        ) "" l)
      | Bang(b,l1,l2) ->
        f_cont (
          List.fold_left (fun accu pp ->
            accu ^ browse pp (fun s -> "\n! "^s)
          ) "" l2 ^
          List.fold_left (fun accu pp ->
            accu ^ browse pp (fun s -> "\n!X "^s)
          ) "" l1
        ) in
    browse p (fun s -> s)

  (* restaures all broken symmetries at toplevel
  NB. the sorting is here to unsure a sound combination of symmetries and the reduced semantics *)
  let rec restaure_sym (lp:t) : t =
    match lp.proc with
    | Input _
    | OutputSure _ -> lp
    | Par l -> {lp with proc = Par (List.map restaure_sym l)}
    | Bang(b,l1,l2) ->
      {lp with proc = Bang (Repl,[],List.map restaure_sym l1 @ l2)}
    | If _
    | New _
    | Output _ -> Config.internal_error "[process_session.ml >> restaure_sym] Should only be applied on normalised processes."
    | Start _ -> Config.internal_error "[process_session.ml >> restaure_sym] Unexpected Start constructor."

  (* checks whether the process contains an output at toplevel.
  Should not take the symmetries into account while doing so. *)
  let rec contains_output (lp:t) : bool =
    match lp.proc with
    | Input _ -> false
    | OutputSure _ -> true
    | Par l -> List.exists contains_output l
    | Bang (_,l1,l2) -> List.exists contains_output (l1@l2)
    | Start _ -> Config.internal_error "[process_session.ml >> contains_output] Unexpected Start constructor."
    | _ -> Config.internal_error "[process_session.ml >> contains_output] Should only be applied on normalised processes."

  (* checks parallels at toplevel *)
  let contains_par (lp:t) : bool =
    match lp.proc with
    | Input _
    | OutputSure _ -> false
    | Par _
    | Bang _ -> true
    | Start _ -> Config.internal_error "[process_session.ml >> contains_par] Unexpected Start constructor."
    | _ -> Config.internal_error "[process_session.ml >> contains_output] Should only be applied on normalised processes."

  (* adding labels to normalised processes *)
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
        ) in

    Config.debug (fun () ->
      if lp.label <> None then
        Config.internal_error "[process_session.ml >> labelling] Already labelled process."
    );
    match lp.proc with
    | Input _
    | OutputSure _ -> {lp with label = Some prefix}
    | Output _
    | If _
    | New _ ->
      Config.internal_error "[process_session.ml >> labelling] Only normalised processes should be assigned with labels."
    | Start _ -> Config.internal_error "[process_session.ml >> labelling] Unexpected Start constructor."
    | Par _
    | Bang _ -> assign 0 lp (fun proc pos -> proc)

  (* extracts the list of parallel labelled_process from a labelled_process *)
  let elements ?init:(init:t list=[]) (lp:t) : t list =
    let rec gather accu lp = match lp with
      | {proc = Par l; _} -> List.fold_left gather accu l
      | {proc = Bang (_,l1,l2); _} -> List.fold_left gather accu (l1@l2)
      | _ -> lp :: accu in
    gather init lp

  (* conversion from a usual process *)
  let apply_renaming_on_term (rho:Name.Renaming.t) (t:Term.protocol_term) : Term.protocol_term =
    Name.Renaming.apply_on_terms rho t (fun x f -> f x)

  let apply_renaming_on_name (rho:Name.Renaming.t) (n:Term.name) : Term.name =
    Name.Renaming.apply_on_terms rho n (fun n f ->
      Term.name_of (f (Term.of_name n))
    )

  let rec fresh_copy_of (lp:t) : t =
    let rec browse rho p =
      match p.proc with
      | Input(c,x,p) ->
        {proc = Input(c,x,browse rho p); label = None}
      | Output(c,t,p) ->
        {proc = Output(c,apply_renaming_on_term rho t,browse rho p); label = None}
      | OutputSure(c,t,p) ->
        {proc = OutputSure(c,apply_renaming_on_term rho t,browse rho p); label = None}
      | If(u,v,p1,p2) ->
        let uu = apply_renaming_on_term rho u in
        let vv = apply_renaming_on_term rho v in
        {proc = If(uu,vv,browse rho p1,browse rho p2); label = None}
      | New(n,p) ->
        let nn = Name.fresh() in
        {proc = New(nn,browse (Name.Renaming.compose rho n nn) p); label = None}
      | Par l ->
        {proc = Par(List.map (browse rho) l); label = None}
      | Bang(b,[],l) ->
        {proc = Bang(b,[],List.map (browse rho) l); label = None}
      | Bang _ -> Config.internal_error "[process_session.ml >> fresh_copy] Unexpected case."
      | Start _ -> Config.internal_error "[process_session.ml >> fresh_copy] Unexpected Start constructor." in
    browse (Name.Renaming.identity) lp

  (* conversion from expansed processes
  TODO: verify during testing that nested bangs (without news/ifs in between) are collapsed *)
  let of_expansed_process (p:Process.expansed_process) : t =
    let rec browse p =
      match p with
      | Process.Nil -> {proc = Par []; label = None}
      | Process.Output(ch,_,_)
      | Process.Input(ch,_,_) when not (is_function ch) ->
        Config.internal_error "[process_session.ml >> of_expansed_process] Inputs/Outputs should only be done on atomic channels."
      | Process.Output(ch,t,pp) ->
        {proc = Output(root ch,t,browse pp); label = None}
      | Process.Input(ch,x,pp) ->
        {proc = Input(root ch,x,browse pp); label = None}
      | Process.IfThenElse(t1,t2,pthen,pelse) ->
        let p_then = browse pthen in
        let p_else = browse pelse in
        {proc = If(t1,t2,p_then,p_else); label = None}
      | Process.New(n,pp) ->
        {proc = New(n,browse pp); label = None}
      | Process.Par lp ->
        let lll =
          List.rev_map (fun (pp,i) ->
            let proc = browse pp in
            if i = 1 then proc
            else
              let l = Func.loop (fun _ ac -> fresh_copy_of proc :: ac) [] 0 (i-1) in
              {proc = Bang (Repl,[],l); label = None}
          ) lp in
        {proc = Par lll; label = None}
      | Process.Choice _
      | Process.Let _ -> Config.internal_error "[process_session.ml >> plain_process_of_expansed_process] *Choice* and *Let* not implemented yet for equivalence by session." in

    {proc = Start (browse p); label = Some Label.initial}

  let factor (p:t) : t = p


  (* executing inputs with symmetries. Returns a list of (c,x,lab,p,li) where [li] is the leftovers after executing an input binding of [x] on channel [c], with label [lab].
  NB. The extracted inputs are consumed. *)
  type input_data = {
    channel : symbol;
    var : fst_ord_variable;
    optim : bool;
    lab : Label.t;
    leftovers : t list;
  }
  let unfold_input ?optim:(optim:bool=false) (l:t list) : (t * input_data) list =

    let rec unfold forall accu leftovers p f_cont =
      match p.proc with
      | OutputSure _ ->
        Config.internal_error "[process_session.ml >> unfold_input] Ill-formed process, focus should not be applied in this case."
      | Par l -> unfold_list forall accu leftovers l f_cont
      | Bang(_,[],[]) -> f_cont accu
      | Bang(_,_::_,_) -> Config.internal_error "[process_session.ml >> unfold_input] Symmetries should not be broken when executing inputs."
      | Bang(b,[],pp::tl) ->
        let left_pp = {proc = Bang(b,[],tl); label = None} in
        let leftovers_pp = if tl = [] then leftovers else left_pp::leftovers in
        if b = Repl || optim then
          unfold forall accu leftovers_pp pp f_cont
        else
          unfold forall accu leftovers_pp pp (fun accu_pp ->
            unfold_list ~bang:(Some ([pp],Channel)) false accu_pp leftovers tl f_cont
          )
      | Input (ch,x,pp) ->
        let res = {
          channel = ch;
          var = x;
          optim = forall;
          lab = get_label p;
          leftovers = leftovers;
        } in
        f_cont ((pp,res)::accu)
      | New _
      | If _
      | Output _ ->
        Config.internal_error "[process_session.ml >> unfold_input] Unfolding should only be applied on normalised processes."
      | Start _ -> Config.internal_error "[process_session.ml >> unfold_input] Unexpected Start constructor."

    and unfold_list ?bang:(memo=None) forall accu leftovers l f_cont =
      match l with
      | [] -> f_cont accu
      | p :: t ->
        match memo with
        | None -> (* case of a list of parallel processes *)
          unfold forall accu (List.rev_append t leftovers) p (fun accu1 ->
            unfold_list forall accu1 (p::leftovers) t f_cont
          )
        | Some (memo,b) -> (* case of a list of replicated processes *)
          let lefts = List.rev_append memo t in
          let leftovers1 =
            if lefts = [] then leftovers
            else {proc = Bang(b,[],lefts); label = None} :: leftovers in
          unfold forall accu leftovers1 p (fun accu1 ->
            unfold_list ~bang:(Some (p::memo,b)) forall accu1 leftovers t f_cont
          ) in

    unfold_list true [] [] l (fun accu -> accu)

  (* executing outputs with symmetries. Returns a list of ([c],[t],[lab],[l]) where [l] is the leftovers left after executing an output of [t] on channel [c], with label [lab].
  NB. the extracted outputs are consumed. *)
  type output_data = {
    channel : symbol;
    term : protocol_term;
    optim : bool;
    lab : Label.t;
    context : t -> t;
  }
  let unfold_output ?optim:(optim:bool=false) (lp:t) : (t * output_data) list =

    let rec unfold accu p rebuild f_cont =
      match p.proc with
      | Input _ -> f_cont accu
      | OutputSure(c,t,pp) ->
        let res = {
          channel = c;
          term = t;
          optim = false;
          lab = get_label p;
          context = rebuild
        } in
        if optim then [pp,res]
        else f_cont ((pp,res)::accu)
      | If _
      | New _
      | Output _ ->
        Config.internal_error "[process_session.ml >> unfold_output] Should only be called on normalised processes."
      | Start _ -> Config.internal_error "[process_session.ml >> unfold_output] Unexpected Start constructor."
      | Par l ->
        let add_par l = rebuild {proc = Par l; label = None} in
        unfold_list accu [] l add_par f_cont
      | Bang(b,brok,[]) ->
        let add_bang l = rebuild {proc = Bang(b,l,[]); label = None} in
        unfold_list accu [] brok add_bang f_cont
      | Bang(Channel,brok,l) ->
        let add_bang1 x = rebuild {proc = Bang(Channel,brok,x); label = None} in
        let add_bang2 x = rebuild {proc = Bang(Channel,x,l); label = None} in
        unfold_list accu [] l add_bang1 (fun ac ->
          unfold_list ac [] brok add_bang2 f_cont
        )
      | Bang(Repl,brok,pp::t) ->
        let add_bang h = rebuild {proc = Bang(Repl,h::brok,t); label = None} in
        unfold accu pp add_bang f_cont

    and unfold_list accu memo l rebuild f_cont =
      match l with
      | [] -> f_cont accu
      | pp :: t ->
        let add_list_to_rebuild p =
          if nil p then rebuild (List.rev_append memo t)
          else rebuild (List.rev_append memo (p::t)) in
        unfold accu pp add_list_to_rebuild (fun acp ->
          unfold_list acp (pp::memo) t rebuild f_cont
        ) in

    match unfold [] lp (fun p -> p) (fun accu -> accu) with
    | [] -> Config.internal_error "[process_session.ml >> unfold_output] No output could be unfolded."
    | (p,odata) :: accu -> (p,{odata with optim = true}) :: accu

  module Skeleton = struct
    (* comparison of skeletons (parallel operators excluded) *)
    let compare_atomic (p1:t) (p2:t) : int =
      match p1.proc, p2.proc with
      | OutputSure _ , Input _  -> -1
      | Input _, OutputSure _ -> 1
      | Input(c1,_,_), Input(c2,_,_)
      | OutputSure(c1,_,_), OutputSure(c2,_,_) -> Symbol.order c1 c2
      | _ -> Config.internal_error "[process_session.ml >> compare_io_process] Unexpected case."

    (* Checks whether two lists of atomic processes have identical skeletons.
    TODO: current implementation quite naive (does not take symmetries into account), may be improved. *)
    let rec equal (p1:t list) (p2:t list) : bool =
      let sort = List.fast_sort (fun p q -> compare_atomic p q) in
      let elts l = List.fold_left (fun accu p -> elements ~init:accu p) [] l in
      let l1 = sort (elts p1) in
      let l2 = sort (elts p2) in
      try List.for_all2 (fun p q -> compare_atomic p q = 0) l1 l2
      with Invalid_argument _ -> false

    (* compares the skeletons of two processes and updates *)
    let compare (p1:t) (p2:t) = 0
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


    let rec normalise (p:t) (cstr:constraints) (f_cont:constraints->t->(unit->unit)->unit) (f_next:unit->unit) : unit =
      match p.proc with
      | OutputSure _
      | Input _ -> f_cont cstr p f_next
      | Output(ch,t,p) ->
        let tt =
          Rewrite_rules.normalise (Subst.apply cstr.equations t (fun x f -> f x)) in

        let eqn_modulo_list_result =
          try
            EqList (Modulo.syntactic_equations_of_equations [Modulo.create_equation tt tt])
          with
          | Modulo.Bot -> EqBot
          | Modulo.Top -> EqTop in

        begin match eqn_modulo_list_result with
        | EqBot -> f_cont cstr {p with proc = Par []} f_next
        | EqTop -> f_cont cstr {p with proc = OutputSure(ch,t,p)} f_next
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
                  fun () -> f_cont {equations = new_eqn; disequations = new_diseqn} {p with proc = OutputSure(ch,t,p)} acc_f_next
            ) f_next eqn_modulo_list in

          let f_next_disequation f_next =
            let diseqn_modulo =
              try
                Modulo.syntactic_disequations_of_disequations (Modulo.create_disequation tt tt)
              with
              | Modulo.Bot
              | Modulo.Top -> Config.internal_error "[process_session.ml >> normalise] The disequations cannot be top or bot." in
            let new_diseqn = List.rev_append cstr.disequations diseqn_modulo in
            f_cont {cstr with disequations = new_diseqn} {p with proc = Par []} f_next in

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
      | New(_,p) -> normalise p cstr f_cont f_next
      | Par l ->
        normalise_list l cstr (fun gather l_norm f_next1 ->
          match l_norm with
            | [p] -> f_cont gather p f_next1
            | _ -> f_cont gather {p with proc = Par l_norm} f_next1
        ) f_next
      | Bang(b,l1,l2) ->
        normalise_list l1 cstr (fun gather1 l1_norm f_next1 ->
          normalise_list l2 gather1 (fun gather2 l2_norm f_next2 ->
              match l1_norm,l2_norm with
              | [],[p]
              | [p],[] -> f_cont gather2 p f_next1
              | _ -> f_cont gather2 {p with proc = Bang(b,l1_norm,l2_norm)} f_next2
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
              | Par ll -> List.rev_append ll l_norm
              | Bang(_,[],[p])
              | Bang(_,[p],[]) -> p :: l_norm
              | _ -> p_norm :: l_norm in
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
  (* TODO. make the datastructure more efficient. Could be more practical when there are a lot of singletons to handle the operation "get all potential labels matching with a given label l". *)
  module LabelSet = Set.Make(struct type t = Label.t let compare = compare end)
  type t = (LabelSet.t * LabelSet.t) list

  (* the initial bijection set *)
  let initial : t =
    [LabelSet.singleton Label.initial, LabelSet.singleton Label.initial]

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
        LabelSet.of_list (List.rev_map Labelled_process.get_label procs) in
      Some (List.rev_map ~init:accu (fun (ec1,ec2)->convert ec1, convert ec2) l)

  (* prints a bijection set *)
  let print (bset:t) : unit =
    List.iter (fun (s1,s2) ->
      LabelSet.iter (fun lab -> Printf.printf "%s;" (Label.to_string lab)) s1;
      Printf.printf "   [MATCHABLE WITH]   ";
      LabelSet.iter (fun lab -> Printf.printf "%s;" (Label.to_string lab)) s2;
      print_endline "";
    ) bset

  (* restricts a bijection_set with the set of bijections pi such that
  pi(l1) = l2. Returns None if the resulting set is empty. Assumes that the
  argument was not already empty. *)
  let update_cont ?abort_if_fails:(stop:bool=false) (l1:Label.t) (l2:Label.t) (p1:Labelled_process.t) (p2:Labelled_process.t) (bset:t) (f_fail:t->t option->t option): t option =
    let rec search memo s =
      match s with
      | [] -> if stop then None else f_fail memo (init bset p1 p2)
      | (ll1,ll2) :: t ->
        match LabelSet.find_opt l1 ll1, LabelSet.find_opt l2 ll2 with
        | None,None -> search ((ll1,ll2) :: memo) t
        | Some _,Some _ ->
          if LabelSet.is_singleton ll1 then
            Some (List.rev_append ((ll1,ll2)::t) memo)
          else
            let ll1' = LabelSet.remove l1 ll1 in
            let ll2' = LabelSet.remove l2 ll2 in
            let single1 = LabelSet.singleton l1 in
            let single2 = LabelSet.singleton l2 in
            Some (List.rev_append ((single1,single2)::(ll1',ll2')::t) memo)
        | _ -> None in
    search [] bset


  let update (l1:Label.t) (l2:Label.t) (p1:Labelled_process.t) (p2:Labelled_process.t) (bset:t) : t option =
    update_cont l1 l2 p1 p2 bset (fun memo extended_bset ->
      match extended_bset with
      | None -> None
      | Some s ->
        match update_cont ~abort_if_fails:true l1 l2 p1 p2 s (fun _ _ -> None) with
        | None -> None
        | Some res -> Some (List.rev_append res memo)
    )


  (* given a bijection set and a label l, computes the set of labels that are
  compatible with l wrt one bijection. *)
  let get_compatible_labels (l:Label.t) (s:t) : Label.t list =
    match List.find_opt (fun (labset,_) -> LabelSet.mem l labset) s with
    | None -> Config.internal_error "[process_session.ml >> get_compatible_labels] Unexpected case"
    | Some pair -> LabelSet.elements (snd pair)
end


(* type for representing internal states *)
module Configuration : sig
  type t
  val print_trace : (fst_ord, name) Subst.t -> (snd_ord, axiom) Subst.t -> t -> string (* returns a string displaying the trace needed to reach this configuration *)
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
    val apply_neg : axiom -> Labelled_process.t -> Labelled_process.output_data -> Labelled_process.t list -> t -> t (* executes an output in a configuration *)
    val apply_pos : snd_ord_variable -> t -> Labelled_process.input_data * t (* executes a focused input in a configuration *)
    val apply_focus : snd_ord_variable -> (Labelled_process.t * Labelled_process.input_data) -> t -> t (* focuses an input in a configuration *)
    val apply_start : t -> t (* removes the start at the beginning of the process *)
  end
end = struct
  type action =
    | InAction of symbol * snd_ord_variable * protocol_term * Label.t
    | OutAction of symbol * axiom * protocol_term * Label.t

  type t = {
    input_proc : Labelled_process.t list;
    focused_proc : Labelled_process.t option;
    sure_output_proc : Labelled_process.t list;
    sure_unchecked_skeletons : Labelled_process.t option;
    to_normalise : Labelled_process.t option;
    trace : action list;
    ongoing_block : Block.t;
    previous_blocks : Block.t list;
  }

  (* for interface purposes *)
  let print_action (fst_subst:(fst_ord,name) Subst.t) (snd_subst:(snd_ord,axiom) Subst.t) (act:action) : string =
    match act with
    | InAction(ch,var_X,x,lab) ->
      let recipe =
        Subst.apply snd_subst (of_variable var_X) (fun x f -> f x) in
      let input =
        Rewrite_rules.normalise (Subst.apply fst_subst x (fun x f -> f x)) in
      Printf.sprintf "@label:%s In(%s,%s) => concrete input: %s\n" (Label.to_string lab) (Symbol.display Latex ch) (Term.display Latex Recipe recipe) (Term.display Latex Protocol input)
    | OutAction(ch,ax,t,lab) ->
      let output =
        Rewrite_rules.normalise (Subst.apply fst_subst t (fun x f -> f x)) in
      Printf.sprintf "@label:%s Out(%s,%s) => referred later as %s\n" (Label.to_string lab) (Symbol.display Latex ch) (Term.display Latex Protocol output) (Axiom.display Latex ax)

  let print_trace (fst_subst:(fst_ord,name) Subst.t) (snd_subst:(snd_ord,axiom) Subst.t) (conf:t) : string =
    snd (
      List.fold_left (fun (count,accu) act ->
        count-1,Printf.sprintf "%d) %s%s" count (print_action fst_subst snd_subst act) accu
      ) (List.length conf.trace,"") conf.trace
    )

  (* lifting operations on block to configurations *)
  let check_block (snd_subst:(snd_ord,axiom) Subst.t) (c:t) : bool =
    Block.is_authorised c.previous_blocks c.ongoing_block snd_subst

  (* returns the inputs of the process *)
  let inputs (conf:t) : Labelled_process.t list =
    conf.input_proc

  (* returns the (sure) outputs of a process *)
  let outputs (conf:t) : Labelled_process.t list =
    conf.sure_output_proc

  (* TODO. makes initial configuration simpler, helps for optimisations. Includes factorisation. *)
  let clean_inital (c:t) : t =
    c

  let of_expansed_process (p:Process.expansed_process) : t =
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
            sure_unchecked_skeletons = Some (rebuild labelled_p);
            to_normalise = None;
          } in
          f_cont gather conf_rel labelled_p;
          f_next ()
        ) (fun () -> ())
      | _, _ -> Config.internal_error "[process_session.ml >> normalise_configuration] A configuration cannot be released and focused at the same time."

  (* takes two configuration as an argument, and performs a skeleton check (on
  their focused process if any, or sure_uncheked_skeletons otherwise). *)
  let check_skeleton (conf1:t) (conf2:t) : bool =

    match conf1.focused_proc, conf2.focused_proc, conf1.sure_unchecked_skeletons, conf2.sure_unchecked_skeletons with
    | Some p1, Some p2, None, None
    | None, None, Some p1, Some p2 ->
      if Labelled_process.contains_output p1 || Labelled_process.contains_output p2 then
        Labelled_process.Skeleton.equal (p1::conf1.sure_output_proc) (p2::conf2.sure_output_proc)
      else Labelled_process.Skeleton.equal [p1] [p2]
    | _ ->
      Config.internal_error "[process_session.ml >> update_matching] Comparing processes in inconsistent states."

  (* Assuming all skeleton checks have been performed with this skeleton, removes the unchecked states and updates the focus if needed.
  Returns None at the end of improper blocks. *)
  let release_skeleton (c:t) : t option =
    match c.focused_proc, c.sure_unchecked_skeletons with
    | Some p, _ ->
      begin match Labelled_process.get_proc p with
      | Labelled_process.Input _ -> Some c
      | Labelled_process.OutputSure _ ->
        Some {c with focused_proc = None; sure_output_proc = p::c.sure_output_proc}
      | _ ->
        if Labelled_process.nil p then None
        else if Labelled_process.contains_output p then
          Some {c with focused_proc = None; sure_output_proc = p::c.sure_output_proc}
        else
          Some {c with focused_proc = None; input_proc = p::c.input_proc} end
    | _, Some p ->
      begin match Labelled_process.get_proc p with
      | Input _ ->
        Some {c with sure_unchecked_skeletons = None; input_proc = p::c.input_proc}
      | OutputSure _ ->
        Some {c with sure_unchecked_skeletons = None; sure_output_proc = p::c.sure_output_proc}
      | _ ->
        if Labelled_process.nil p then
          Some {c with sure_unchecked_skeletons = None}
        else if Labelled_process.contains_output p then
          Some {c with sure_unchecked_skeletons = None; sure_output_proc = p::c.sure_output_proc}
        else
          Some {c with sure_unchecked_skeletons = None; input_proc = Labelled_process.restaure_sym p::c.input_proc} end
    | _, _ ->
        Config.internal_error "[process_session.ml >> release_skeleton_without_check] A process is either focused or released."

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
        | Input _ -> Some RPos
        | Start _ -> Some RStart
        | _ ->
          Config.internal_error "[process_session.ml >> next_rule] Ill-formed focused state, should have been released or normalised." end
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
        | Start pp -> {conf with focused_proc = Some pp}
        | _ -> Config.internal_error "[process_session.ml Configuration.Transition.apply_start] Error during the initialisation of processes. (1)" end
      | _ ->
        Config.internal_error "[process_session.ml >> Configuration.Transition.apply_start] Error during the initialisation of processes. (2)"

    (* syntactic transformation of a configuration after executing an output *)
    let apply_neg (ax:axiom) (p:Labelled_process.t) (od:Labelled_process.output_data) (leftovers:Labelled_process.t list) (conf:t) : t =
      {conf with
        to_normalise = Some p;
        sure_output_proc = leftovers;
        trace = OutAction(od.channel,ax,od.term,od.lab)::conf.trace;
        ongoing_block = Block.add_axiom ax conf.ongoing_block;
      }

    (* syntactic transformation of a configuration after executing a focused input. Also retrieves and returns the input_data of the focus state. *)
    let apply_pos (var_X:snd_ord_variable) (conf:t) : Labelled_process.input_data * t =
      match conf.focused_proc with
      | Some p ->
        begin match Labelled_process.get_proc p with
        | Input(ch,x,pp) ->
          let idata = {
            Labelled_process.channel = ch;
            Labelled_process.var = x;
            Labelled_process.lab = Labelled_process.get_label p;
            Labelled_process.leftovers = []; (* field not relevant here *)
            Labelled_process.optim = true; (* field not relevant here *)
          } in
          let conf_app = {conf with
            focused_proc = Some pp;
            trace = InAction(ch,var_X,Term.of_variable x,idata.lab) :: conf.trace;
            ongoing_block = Block.add_variable var_X conf.ongoing_block;
          } in
          idata,conf_app
        | _ -> Config.internal_error "[process_session.ml >> Configuration.Transition.apply_pos] Ill-formed focus state." end
      | _ ->
        Config.internal_error "[process_session.ml >> Configuration.Transition.apply_pos] Process should be focused."

    (* syntactic transformation of a configuration after focusing an input *)
    let apply_focus (var_X:snd_ord_variable) (focus:Labelled_process.t * Labelled_process.input_data) (c:t) : t =
      Config.debug (fun () ->
        if c.focused_proc <> None then
          Config.internal_error "[process_session.ml >> add_focus] Unexpected case."
      );
      let (pp,idata) = focus in
      {c with
        input_proc = idata.leftovers;
        focused_proc = Some pp;
        ongoing_block = Block.create idata.lab;
        previous_blocks = c.ongoing_block :: c.previous_blocks;
        trace = InAction(idata.channel,var_X,Term.of_variable idata.var,idata.lab) :: c.trace;
      }
  end
end
