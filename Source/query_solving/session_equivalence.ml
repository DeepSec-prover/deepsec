(* Process manipulation for equivalence by session *)
open Extensions
open Types
open Term
open Formula
open Session_process
open Display

type permutation =
  {
    prefix : int list;
    perm_matching : int list list
      (* The lists inside the perm_matching are ordered *)
  }

type bijection_set = permutation list

type symbolic_configuration =
  {
    (* Main data *)
    origin : bool;
    mutable configuration : Configuration.t;
    mutable matching_status : Configuration.matching_status;
    trace : transition list;

    mutable forall_matched : symbolic_configuration Constraint_system.t list;
      (* When matching status is Exists or Both, the list [forall_matched] indicates the configuration
         with tag ForAll or Both that have this configuration has Exists]*)

    mutable exists_matched : (symbolic_configuration Constraint_system.t * bijection_set) list;
      (* When matching status is ForAll or Both, the list [exists_matched] indicates the configuration
         with tag Exists or Both that have this configuration has Forall]*)

    mutable forall_bset : bijection_set;

    (* Computed datas *)
    mutable link_c : configuration_link;
    transition_data : session_transition;

    improper_ref: Label.t option ref;
    sure_proper_transition : bool
  }

and configuration_link =
  | CNoLink
  | CCsys of symbolic_configuration Constraint_system.t
  | CSearch
  | CTransition of generate_transition
  | CChannelPriority of Configuration.channel_priority
  | CImproperInputs of Configuration.improper_data * Configuration.t

and session_transition =
  | TransNone
  | TransOutput of Configuration.output_transition
  | TransInComm of Configuration.input_and_comm_transition
  | TransStart of Configuration.start_transition

and generate_transition =
  {
    gt_both : symbolic_configuration Constraint_system.t list;
    gt_forall : symbolic_configuration Constraint_system.t list;
    gt_exists : symbolic_configuration Constraint_system.t list
  }

type equivalence_problem =
  {
    size_frame : int;
    forall_set : symbolic_configuration Constraint_system.t list;
    eq_recipe : Formula.R.t;
    general_blocks : Block.general_blocks;
    public_output_channels : (Channel.t * int) list (* Ordered by Channel.compare *)
  }

exception Not_Session_Equivalent of (bool * transition list)

module Bijection_set = struct

  (*** Display ***)

  let display_perm_matching =
    display_list (fun l ->
      "["^(display_list string_of_int "," l)^"]"
    ) "; "

  let display_permutation perm =
    Printf.sprintf "{ prefix = %s; matching = %s }"
      (display_list string_of_int "." perm.prefix)
      (display_perm_matching perm.perm_matching)

  let display = display_list display_permutation " "

  (*** Initial ***)

  let initial =
    let perm =
      {
        prefix = [];
        perm_matching = [[0]]
      }
    in
    [perm]

  (** Generation of bijection set for transition **)

  let perm_matching_of_skeleton skel =
    let perm_matching = ref [] in
    List.iter (fun (_,_,l)  -> perm_matching := l::!perm_matching) skel.Labelled_process.input_skel;
    List.iter (fun (_,_,l)  -> perm_matching := l::!perm_matching) skel.Labelled_process.output_skel;
    if fst skel.Labelled_process.private_input_skel <> 0
    then perm_matching := (snd skel.Labelled_process.private_input_skel)::!perm_matching;
    if fst skel.Labelled_process.private_output_skel <> 0
    then perm_matching := (snd skel.Labelled_process.private_output_skel)::!perm_matching;
    !perm_matching

  let rec extract_forall_permutation forall_label_prefix index prev_bset = function
    | [] -> Config.internal_error "[session_equivalence.ml >> Bijection_set.extract_forall_permuation] The label should occurs."
    | perm::q ->
        if forall_label_prefix = perm.prefix
        then index, perm, List.rev_append prev_bset q
        else extract_forall_permutation forall_label_prefix (index+1) (perm::prev_bset) q

  let rec extract_sub_matching (i_target:int) prev_list = function
    | [] -> None
    | i::q ->
        match compare i i_target with
          | 0 -> Some (List.rev_append prev_list q)
          | 1 -> None
          | _ -> extract_sub_matching i_target (i::prev_list) q

  let rec extract_forall_matching i_target index (prev_matching:(int list list)) = function
    | [] -> Config.internal_error "[session_equivalence.ml >> Bijection_set.extract_forall_matching] Unexpected case."
    | forall_m::q ->
        match extract_sub_matching i_target [] forall_m with
          | None -> extract_forall_matching i_target (index+1) (forall_m::prev_matching) q
          | Some forall_m' -> index, forall_m', List.rev_append prev_matching q

  let rec update_from_extract old_perm bset perm_matching = function
    | [] ->
        if perm_matching = []
        then bset
        else {old_perm with perm_matching = perm_matching }::bset
    | (lbl,skel,matching)::q ->
        let perm_matching_1 =
          if matching = []
          then perm_matching
          else matching::perm_matching
        in
        if skel.Labelled_process.par_created
        then
          let new_perm =
            {
              prefix = skel.Labelled_process.label_prefix;
              perm_matching = perm_matching_of_skeleton skel
            }
          in
          update_from_extract old_perm (new_perm::bset) perm_matching_1 q
        else
          let perm_matching_2 =
            if Labelled_process.is_skeleton_empty skel
            then perm_matching_1
            else [lbl.Label.last_index]::perm_matching_1
          in
          update_from_extract old_perm bset perm_matching_2 q

  let generate_exists forall_skel id_bset id_perm exists_label exists_skel bset =
    if forall_skel.Labelled_process.par_created = exists_skel.Labelled_process.par_created && Labelled_process.is_equal_skeletons forall_skel exists_skel
    then
      let (old_perm,bset_1) = List.extract_nth id_bset bset in
      if exists_label.Label.prefix = old_perm.prefix
      then
        let (exists_m,perm_matching) = List.extract_nth id_perm old_perm.perm_matching in
        match extract_sub_matching exists_label.Label.last_index [] exists_m  with
          | None -> None
          | Some exists_m' -> Some(update_from_extract old_perm bset_1 perm_matching [exists_label,exists_skel,exists_m'])
      else None
    else None

  let generate_forall forall_label forall_skel bset =
    let (id_bset,old_perm,bset_1) = extract_forall_permutation forall_label.Label.prefix 0 [] bset in
    let (id_perm,forall_m',perm_matching) = extract_forall_matching forall_label.Label.last_index 0 [] old_perm.perm_matching in
    generate_exists forall_skel id_bset id_perm, update_from_extract old_perm bset_1 perm_matching [forall_label,forall_skel,forall_m']

  type generated_type =
    | Same of int * int * int
    | Diff of int * int * int * int

  let generate_exists_for_comm_same forall_comm_trans (id_bset,id_perm_out,id_perm_in) exists_comm_trans bset =
    let (forall_skel_out,forall_skel_in) = forall_comm_trans.Configuration.comm_out_skeletons, forall_comm_trans.Configuration.comm_in_skeletons in
    let (exists_label_out,exists_label_in) = exists_comm_trans.Configuration.comm_out_label, exists_comm_trans.Configuration.comm_in_label in
    let (exists_skel_out,exists_skel_in) = exists_comm_trans.Configuration.comm_out_skeletons, exists_comm_trans.Configuration.comm_in_skeletons in

    if forall_skel_out.Labelled_process.par_created = exists_skel_out.Labelled_process.par_created &&
      forall_skel_in.Labelled_process.par_created = exists_skel_in.Labelled_process.par_created &&
      exists_label_out.Label.prefix = exists_label_in.Label.prefix &&
      Labelled_process.is_equal_skeletons forall_skel_out exists_skel_out &&
      Labelled_process.is_equal_skeletons forall_skel_in exists_skel_in
    then
      let (old_perm,bset_1) = List.extract_nth id_bset bset in
      if exists_label_out.Label.prefix = old_perm.prefix
      then
        let (exists_out,perm_matching_1) = List.extract_nth id_perm_out old_perm.perm_matching in
        match extract_sub_matching exists_label_out.Label.last_index [] exists_out with
          | None -> None
          | Some exists_out' ->
              let (exists_in,perm_matching_2) = List.extract_nth id_perm_in perm_matching_1 in
              match extract_sub_matching exists_label_in.Label.last_index [] exists_in with
                | None -> None
                | Some exists_in' ->
                    Some(update_from_extract old_perm bset_1 perm_matching_2 [exists_label_out,exists_skel_out,exists_out';exists_label_in,exists_skel_in,exists_in'])
      else None
    else None

  let generate_exists_for_comm_diff forall_comm_trans (id_bset_out,id_perm_out,id_bset_in,id_perm_in) exists_comm_trans bset =
    let (forall_skel_out,forall_skel_in) = forall_comm_trans.Configuration.comm_out_skeletons, forall_comm_trans.Configuration.comm_in_skeletons in
    let (exists_label_out,exists_label_in) = exists_comm_trans.Configuration.comm_out_label, exists_comm_trans.Configuration.comm_in_label in
    let (exists_skel_out,exists_skel_in) = exists_comm_trans.Configuration.comm_out_skeletons, exists_comm_trans.Configuration.comm_in_skeletons in

    if forall_skel_out.Labelled_process.par_created = exists_skel_out.Labelled_process.par_created &&
      forall_skel_in.Labelled_process.par_created = exists_skel_in.Labelled_process.par_created &&
      Labelled_process.is_equal_skeletons forall_skel_out exists_skel_out &&
      Labelled_process.is_equal_skeletons forall_skel_in exists_skel_in
    then
      let (old_perm_out,bset_1) = List.extract_nth id_bset_out bset in
      if exists_label_out.Label.prefix = old_perm_out.prefix
      then
        let (exists_out,perm_matching_out) = List.extract_nth id_perm_out old_perm_out.perm_matching in
        match extract_sub_matching exists_label_out.Label.last_index [] exists_out with
          | None -> None
          | Some exists_out' ->
              let (old_perm_in,bset_2) = List.extract_nth id_bset_in bset_1 in
              if exists_label_in.Label.prefix = old_perm_in.prefix
              then
                let (exists_in,perm_matching_in) = List.extract_nth id_perm_in old_perm_in.perm_matching in
                match extract_sub_matching exists_label_in.Label.last_index [] exists_in with
                  | None -> None
                  | Some exists_in' ->
                      let bset_3 = update_from_extract old_perm_out bset_2 perm_matching_out [exists_label_out,exists_skel_out,exists_out'] in
                      let bset_4 = update_from_extract old_perm_in bset_3 perm_matching_in [exists_label_in,exists_skel_in,exists_in'] in
                      Some bset_4
              else None
      else None
    else None

  let generate_forall_for_comm forall_comm_trans bset =
    let (forall_label_out,forall_label_in) = forall_comm_trans.Configuration.comm_out_label, forall_comm_trans.Configuration.comm_in_label in
    let (forall_skel_out,forall_skel_in) = forall_comm_trans.Configuration.comm_out_skeletons, forall_comm_trans.Configuration.comm_in_skeletons in

    if forall_label_out.Label.prefix = forall_label_in.Label.prefix
    then
      let (id_bset,old_perm,bset_1) = extract_forall_permutation forall_label_out.Label.prefix 0 [] bset in
      let (id_perm1,forall_out',perm_matching_1) = extract_forall_matching forall_label_out.Label.last_index 0 [] old_perm.perm_matching in
      let (id_perm2,forall_in',perm_matching_2) = extract_forall_matching forall_label_in.Label.last_index 0 [] perm_matching_1 in

      generate_exists_for_comm_same forall_comm_trans(id_bset,id_perm1,id_perm2), update_from_extract old_perm bset_1 perm_matching_2 [forall_label_out,forall_skel_out,forall_out';forall_label_in,forall_skel_in,forall_in']
    else
      let (id_bset_out,old_perm_out,bset_1) = extract_forall_permutation forall_label_out.Label.prefix 0 [] bset in
      let (id_perm_out,forall_out',perm_matching_out) = extract_forall_matching forall_label_out.Label.last_index 0 [] old_perm_out.perm_matching in
      let (id_bset_in,old_perm_in,bset_2) = extract_forall_permutation forall_label_in.Label.prefix 0 [] bset_1 in
      let (id_perm_in,forall_in',perm_matching_in) = extract_forall_matching forall_label_in.Label.last_index 0 [] old_perm_in.perm_matching in
      let bset_3 = update_from_extract old_perm_out bset_2 perm_matching_out [forall_label_out,forall_skel_out,forall_out'] in
      let bset_4 = update_from_extract old_perm_in bset_3 perm_matching_in [forall_label_in,forall_skel_in,forall_in'] in
      generate_exists_for_comm_diff forall_comm_trans (id_bset_out,id_perm_out,id_bset_in,id_perm_in), bset_4

  let generate_in_comm forall_in_comm_trans forall_bset = match forall_in_comm_trans.Configuration.in_comm_type with
    | Configuration.TInput forall_in_trans ->
        let (in_gen_bset,forall_bset1) = generate_forall forall_in_trans.Configuration.in_label forall_in_trans.Configuration.in_skeletons forall_bset in

        let gen_bset exists_in_comm_trans bset = match exists_in_comm_trans.Configuration.in_comm_type with
          | Configuration.TInput exists_in_trans -> in_gen_bset exists_in_trans.Configuration.in_label exists_in_trans.Configuration.in_skeletons bset
          | _ -> None
        in
        gen_bset,forall_bset1
    | Configuration.TComm forall_comm_trans ->
        let (comm_gen_bset,forall_bset1) = generate_forall_for_comm forall_comm_trans forall_bset in

        let gen_bset exists_in_comm_trans bset = match exists_in_comm_trans.Configuration.in_comm_type with
          | Configuration.TComm exists_comm_trans -> comm_gen_bset exists_comm_trans bset
          | _ -> None
        in
        gen_bset,forall_bset1

  (** Suppression of improper inputs **)

  (* We assume the forall_m and exists_m have same size. *)
  let rec check_and_remove_perm_matching_forall cur_index prev_id prev_matching imp_matching = function
    | [] -> Config.internal_error "[session_equivalence.ml >> Bijection_set.check_and_remove_perm_matching_forall] All the index should have been taken care of."
    | matching::q_m ->
        try
          let imp_matching' = IntList.included_diff imp_matching matching in
          if imp_matching' == imp_matching
          then check_and_remove_perm_matching_forall (cur_index+1) prev_id (matching::prev_matching) imp_matching q_m
          else
            if imp_matching' = []
            then List.rev_append prev_id [cur_index], List.rev_append prev_matching q_m
            else check_and_remove_perm_matching_forall (cur_index+1) (cur_index::prev_id) prev_matching imp_matching' q_m
        with IntList.Not_included -> raise Not_found

  let rec check_and_remove_perm_matching_exists cur_index id_l imp_matching matching_l = match id_l, matching_l with
    | [], _ -> matching_l
    | _, [] -> Config.internal_error "[session_equivalence.ml >> Bijection_set.check_and_remove_perm_matchin_exists] All index should have been found."
    | i::_,matching::q_m when i <> cur_index -> matching::(check_and_remove_perm_matching_exists (cur_index+1) id_l imp_matching q_m)
    | _::q_i,matching::q_m ->
        try
          let imp_matching' = IntList.included_diff imp_matching matching in
          if imp_matching' == imp_matching
          then raise Not_found
          else
            if imp_matching' = []
            then q_m
            else check_and_remove_perm_matching_exists (cur_index+1) q_i imp_matching' q_m
        with IntList.Not_included -> raise Not_found

  let rec check_and_remove_forall cur_index forall_imp = function
    | [] -> Config.internal_error "[session_equivalence.ml >> Bijection_set.main_check_and_remove_forall] All the prefix should have been taken care of."
    | perm::q_bset ->
        let extract_done = ref false in
        try
          let ((_,(f_nb_id:int),f_matching),forall_imp') = List.extract (fun (prefix,_,_) -> prefix = perm.prefix) forall_imp in
          extract_done := true;
          let (id_perm_l,perm_matching') = check_and_remove_perm_matching_forall 0 [] [] f_matching perm.perm_matching in
          if forall_imp' = []
          then [(cur_index,f_nb_id,id_perm_l)], { perm with perm_matching = perm_matching' } :: q_bset
          else
            let (id_bset_l,bset') = check_and_remove_forall (cur_index+1) forall_imp' q_bset in
            (cur_index,f_nb_id,id_perm_l)::id_bset_l, { perm with perm_matching = perm_matching' } :: bset'
        with Not_found ->
          if !extract_done
          then raise Not_found
          else
            let (id_bset_l,bset') = check_and_remove_forall (cur_index+1) forall_imp q_bset in
            (id_bset_l,perm::bset')

  let rec check_and_remove_exists cur_index id_bset_l exists_imp bset = match id_bset_l,bset with
    | [],_ -> bset
    | _, [] -> Config.internal_error "[session_equivalence.ml >> Bijection_set.main_check_and_remove_exists] All the prefix should have been taken care of."
    | (i,_,_)::_,perm::q_bset when i <> cur_index -> perm::(check_and_remove_exists (cur_index+1) id_bset_l exists_imp q_bset)
    | (_,f_nb_id,id_perm_l)::q_i, perm::q_bset ->
        let ((_,e_nb_id,e_matching),exists_imp') = List.extract (fun (prefix,_,_) -> prefix = perm.prefix) exists_imp in
        if f_nb_id = e_nb_id
        then
          let perm_matching' = check_and_remove_perm_matching_exists 0 id_perm_l e_matching perm.perm_matching in
          if q_i = []
          then { perm with perm_matching = perm_matching' } :: q_bset
          else { perm with perm_matching = perm_matching' } :: (check_and_remove_exists (cur_index+1) q_i exists_imp' q_bset)
        else raise Not_found

end

let iter_forall_both f gen_trans =
  List.iter f gen_trans.gt_both;
  List.iter f gen_trans.gt_forall

let iter_exists_both f gen_trans =
  List.iter f gen_trans.gt_both;
  List.iter f gen_trans.gt_exists

(** Display **)

type selected_transition_debug =
  | SDInput of position option
  | SDOutput of position option
  | SDComm of (position * position) option

let display_matching_status = function
  | Configuration.ForAll -> "Forall"
  | Configuration.Exists -> "Exists"
  | Configuration.Both -> "Both"

let display_constraint_system_set csys_set =
  display_list (fun csys ->
    if csys.Constraint_system.additional_data.matching_status <> Configuration.Exists
    then
    display_object 2 (Some "Symbolic Csys") [
      "origin", string_of_bool csys.Constraint_system.additional_data.origin;
      "configuration", Configuration.display 3 csys.Constraint_system.additional_data.configuration;
      "trace", display_list Process.display_transition "." csys.Constraint_system.additional_data.trace;
      "constraint_system", Constraint_system.display_constraint_system 3 csys;
      "matching_status", display_matching_status csys.Constraint_system.additional_data.matching_status
    ]
    else ""
  ) "" csys_set.Constraint_system.set

let display_forall_set forall_set =
  let csys_ref = ref [] in
  let counter = ref 1 in

  let add_csys csys =
    if not (List.mem_assq csys !csys_ref)
    then
      begin
        csys_ref := (csys,!counter)::!csys_ref;
        incr counter
      end
  in

  List.iter (fun csys ->
    add_csys csys;
    List.iter (fun (csys',_) -> add_csys csys') csys.Constraint_system.additional_data.exists_matched
  ) forall_set;

  csys_ref := List.rev !csys_ref;

  let str = ref "" in
  str := !str^"Forall set\n";

  str := !str^(display_with_tab 1 "Matching = ");

  List.iter (fun f_csys ->
    let f_i = List.assq f_csys !csys_ref in
    str := !str ^ display_with_tab 2 (Printf.sprintf "Forall %d with bset = %s" f_i (Bijection_set.display f_csys.Constraint_system.additional_data.forall_bset));
    List.iter (fun (e_csys,bset) ->
      let e_i = List.assq e_csys !csys_ref in
      str := !str ^ display_with_tab 3 (Printf.sprintf "Exists %d with bset = %s" e_i (Bijection_set.display bset));
    ) f_csys.Constraint_system.additional_data.exists_matched
  ) forall_set;

  (*** Display the constraint system ***)

  str := !str^(display_with_tab 1 "All the constraint systems with configuration = ");

  List.iter (fun (csys,i) ->
    let csys_str =
      display_object 2 (Some "Symbolic Csys") [
        "Identifier", string_of_int i;
        "origin", string_of_bool csys.Constraint_system.additional_data.origin;
        "configuration", Configuration.display 3 csys.Constraint_system.additional_data.configuration;
        "trace", display_list Process.display_transition "." csys.Constraint_system.additional_data.trace;
        "constraint_system", Constraint_system.display_constraint_system 3 csys;
        "matching_status", display_matching_status csys.Constraint_system.additional_data.matching_status
      ]
    in
    if csys.Constraint_system.additional_data.matching_status <> Configuration.Exists
    then str := !str ^ csys_str
  ) !csys_ref;

  !str

let display_equivalence_problem equiv_pbl =

  let csys_ref = ref [] in
  let counter = ref 1 in

  let add_csys csys =
    if not (List.mem_assq csys !csys_ref)
    then
      begin
        csys_ref := (csys,!counter)::!csys_ref;
        incr counter
      end
  in

  List.iter (fun csys ->
    add_csys csys;
    List.iter (fun (csys',_) -> add_csys csys') csys.Constraint_system.additional_data.exists_matched
  ) equiv_pbl.forall_set;

  csys_ref := List.rev !csys_ref;

  let str = ref "" in
  str := !str^"Equivalence problem\n";
  str := !str^(display_with_tab 1 (Printf.sprintf "Size frame = %d" equiv_pbl.size_frame));
  str := !str^(display_with_tab 1 (Printf.sprintf "Eq recipe = %s" (Formula.R.display Terminal equiv_pbl.eq_recipe)));
  str := !str^(Block.display_general_blocks 1 equiv_pbl.general_blocks);
  str := !str^(display_with_tab 1 (Printf.sprintf "Public outputs = %s" (display_list (fun (ch,i) -> (Channel.display ch)^","^string_of_int i) "; " equiv_pbl.public_output_channels)));

  str := !str^(display_with_tab 1 "Matching = ");

  List.iter (fun f_csys ->
    let f_i = List.assq f_csys !csys_ref in
    str := !str ^ display_with_tab 2 (Printf.sprintf "Forall %d with bset = %s" f_i (Bijection_set.display f_csys.Constraint_system.additional_data.forall_bset));
    List.iter (fun (e_csys,bset) ->
      let e_i = List.assq e_csys !csys_ref in
      str := !str ^ display_with_tab 3 (Printf.sprintf "Exists %d with bset = %s" e_i (Bijection_set.display bset));
    ) f_csys.Constraint_system.additional_data.exists_matched
  ) equiv_pbl.forall_set;

  (*** Display the constraint system ***)

  str := !str^(display_with_tab 1 "All the constraint systems with configuration = ");

  List.iter (fun (csys,i) ->
    let csys_str =
      display_object 2 (Some "Symbolic Csys") [
        "Identifier", string_of_int i;
        "origin", string_of_bool csys.Constraint_system.additional_data.origin;
        "configuration", Configuration.display 3 csys.Constraint_system.additional_data.configuration;
        "trace", display_list Process.display_transition "." csys.Constraint_system.additional_data.trace;
        "constraint_system", Constraint_system.display_constraint_system 3 csys;
        "matching_status", display_matching_status csys.Constraint_system.additional_data.matching_status
      ]
    in
      str := !str ^ csys_str
  ) !csys_ref;

  !str

(** Linking symbolic configuration **)

let linked_symbolic_configuration = ref []

let auto_cleanup_symbolic_configuration f =
  Config.debug (fun () ->
    if !linked_symbolic_configuration <> []
    then Config.internal_error "[session_equivalence.ml >> auto_cleanup_symbolic_configuration] No configuration should be linked."
  );
  let r = f () in
  List.iter (fun symb -> symb.link_c <- CNoLink) !linked_symbolic_configuration;
  linked_symbolic_configuration := [];
  r

let link_symbolic_configuration symb link =
  Config.debug (fun () ->
    if symb.link_c <> CNoLink
    then Config.internal_error "[session_equivalence.ml >> link_symbolic_configuration] The symbolic configuration is already linked."
  );
  symb.link_c <- link;
  linked_symbolic_configuration := symb :: !linked_symbolic_configuration

let link_constraint_systems csys_solved =
  List.iter (fun csys ->
    let symb_conf = csys.Constraint_system.additional_data in
    let symb_conf' =
      { symb_conf with
        forall_matched = [];
        exists_matched = [];
        forall_bset = [];
        link_c = CNoLink;
        transition_data = TransNone
      }
    in
    let csys' = { csys with Constraint_system.additional_data = symb_conf' } in
    link_symbolic_configuration symb_conf (CCsys csys')
  ) csys_solved.Constraint_system.set

(** Debug checking **)

type select_trace =
  | SIn of position
  | SOut of position

let select_specified_trace equiv_pbl =
  let selected_trace =
    []
  in
  let rec select_specified_trace target_trace_list trace_list = match target_trace_list, trace_list with
    | [], _ -> true
    | SIn pos :: qtt, AInput(_,_,pos') :: qt
    | SOut pos :: qtt, AOutput(_,pos') :: qt when pos = pos' -> select_specified_trace qtt qt
    | _ -> false
  in
  List.exists (fun csys ->
    select_specified_trace selected_trace (List.rev csys.Constraint_system.additional_data.trace)
  ) equiv_pbl.forall_set

(** Check that the forall_matched and exists_matched are properly formed *)
let debug_forall_exists_matched msg forall_set =

  let rec check_on_csys csys =
    let symb_conf = csys.Constraint_system.additional_data in
    match symb_conf.link_c with
      | CSearch -> ()
      | CNoLink ->
          link_symbolic_configuration symb_conf CSearch;
          if symb_conf.exists_matched <> [] && List.for_all (fun csys' -> csys != csys') forall_set
          then Config.internal_error (msg^": All constraint system with existential matching should occur in forall_set.");
          List.iter (fun (e_csys,_) ->
            check_on_csys e_csys;
            if List.for_all (fun f_csys' -> f_csys' != csys) e_csys.Constraint_system.additional_data.forall_matched
            then Config.internal_error (msg^": A constraint system csys1 has a csys2 in its exists_matched but csys2 does not have csys1 in its forall_matched.");
          ) symb_conf.exists_matched;

          List.iter (fun f_csys' ->
            check_on_csys f_csys';
            if List.for_all (fun f_csys'' -> f_csys'' != f_csys') forall_set
            then Config.internal_error (msg^": All constraint system occuring in a forall_matched field should appear in the forall_set.");
            if List.for_all (fun (e_csys,_) -> csys != e_csys) f_csys'.Constraint_system.additional_data.exists_matched
            then Config.internal_error (msg^": A constraint system csys1 has a csys2 in its forall_matched but csys2 does not have csys1 in its exists_matched.")
          ) symb_conf.forall_matched
    | _ -> Config.internal_error (msg^": The constraint systems should not have been linked.")
  in

  auto_cleanup_symbolic_configuration (fun () ->
    List.iter (fun f_csys ->
      let symb_conf = f_csys.Constraint_system.additional_data in
      if symb_conf.matching_status = Configuration.Exists
      then Config.internal_error (msg^": Constraint system in forall_set should not have Exists as matching status.");
      check_on_csys f_csys
    ) forall_set
  )

let debug_equivalence_problem msg equiv_pbl =
  debug_forall_exists_matched msg equiv_pbl.forall_set

(** Initialisation **)

let generate_initial_equivalence_problem is_equiv_query proc1 proc2 =
  let sproc1 = Labelled_process.of_process proc1 in
  let sproc2 = Labelled_process.of_process proc2 in

  let init_complete_lbl = Label.LStd Label.initial in
  let blocks = { Block.local_proper_blocks = [init_complete_lbl]; Block.local_improper_blocks = [] } in

  let make_conf p =
    {
      Configuration.input_and_private_proc = [p];
      Configuration.output_proc = [];
      Configuration.focused_proc = None;
      Configuration.pure_improper_proc = [];
      Configuration.blocks = blocks;
      private_channels = []
    }
  in
  let conf1 = make_conf sproc1 in
  let conf2 = make_conf sproc2 in

  let symb_conf1 =
    {
      origin = true;
      configuration = conf1;
      matching_status = if is_equiv_query then Configuration.Both else Configuration.ForAll;
      trace = [];
      forall_matched = [];
      exists_matched = [];
      forall_bset = [];
      link_c = CNoLink;
      transition_data = TransNone;
      improper_ref = ref None;
      sure_proper_transition = false
    }
  in
  let symb_conf2 =
    {
      origin = false;
      configuration = conf2;
      matching_status = if is_equiv_query then Configuration.Both else Configuration.Exists;
      trace = [];
      forall_matched = [];
      exists_matched = [];
      forall_bset = [];
      link_c = CNoLink;
      transition_data = TransNone;
      improper_ref = ref None;
      sure_proper_transition = false;
    }
  in
  let csys1 = Constraint_system.empty symb_conf1 in
  let csys2 = Constraint_system.empty symb_conf2 in

  let general_blocks = Block.empty_general in

  if is_equiv_query
  then
    begin
      symb_conf1.forall_matched <- [csys2];
      symb_conf1.exists_matched <- [csys2,Bijection_set.initial];
      symb_conf1.forall_bset <- Bijection_set.initial;
      symb_conf2.forall_matched <- [csys1];
      symb_conf2.exists_matched <- [csys1,Bijection_set.initial];
      symb_conf2.forall_bset <- Bijection_set.initial;
      {
        size_frame = 0;
        forall_set = [csys1;csys2];
        eq_recipe = Formula.R.Top;
        general_blocks = general_blocks;
        public_output_channels = []
      }
    end
  else
    begin
      symb_conf1.exists_matched <- [csys2,Bijection_set.initial];
      symb_conf1.forall_bset <- Bijection_set.initial;
      symb_conf2.forall_matched <- [csys1];
      {
        size_frame = 0;
        forall_set = [csys1];
        eq_recipe = Formula.R.Top;
        general_blocks = general_blocks;
        public_output_channels = []
      }
    end

(** Generation of the attack traces **)

let rec instantiate_trace acc = function
  | [] -> acc
  | AOutput(r,pos)::q -> instantiate_trace (AOutput(Recipe.instantiate r,pos)::acc) q
  | AInput(r1,r2,pos)::q -> instantiate_trace (AInput(Recipe.instantiate r1, Recipe.instantiate r2,pos)::acc) q
  | AEaves(r,pos1,pos2)::q -> instantiate_trace (AEaves(Recipe.instantiate r,pos1,pos2)::acc) q
  | t::q -> instantiate_trace (t::acc) q

let generate_attack_trace csys =
  (* We instantiate the variables of csys with attacker name *)
  let df = csys.Constraint_system.deduction_facts in
  Data_structure.DF.iter (fun bfact ->
    Recipe_Variable.link_recipe bfact.Data_structure.bf_var (RFunc(Symbol.fresh_attacker_name (), []));
  ) df;

  (csys.Constraint_system.additional_data.origin,instantiate_trace [] csys.Constraint_system.additional_data.trace)

(** Split of constraint system list **)

let split_forall_set csys_list f_continuation (f_next:unit->unit) =

  let marked_conf = ref [] in
  let all_csys = ref [] in

  let rec mark csys =
    let conf = csys.Constraint_system.additional_data in
    match conf.link_c with
      | CNoLink ->
          all_csys := csys :: !all_csys;
          conf.link_c <- CSearch;
          marked_conf := conf::!marked_conf;
          List.iter mark conf.forall_matched;
          List.iter (fun (csys',_) -> mark csys') conf.exists_matched
      | _ -> ()
  in

  let rec explore csys_list_1 f_next_1 = match csys_list_1 with
    | [] -> f_next_1 ()
    | csys::q ->
        mark csys;
        let (marked,not_marked) = List.partition_unordered (fun csys' -> csys'.Constraint_system.additional_data.link_c = CSearch) q in
        let marked_1 = csys::marked in
        let csys_to_solve = !all_csys in
        (* Cleanup *)
        all_csys := [];
        List.iter (fun conf -> conf.link_c <- CNoLink) !marked_conf;
        marked_conf := [];
        (* Apply next *)
        f_continuation marked_1 csys_to_solve (fun () ->
          explore not_marked f_next_1
        )
  in

  explore csys_list f_next

(** Cleaning of variables and names **)

let clean_variables_names =
  List.rev_map (fun csys ->
    let conf = csys.Constraint_system.additional_data in
    Configuration.link_used_data (fun () ->
      let original_subst = List.filter (fun (x,_) -> x.link = SLink) csys.Constraint_system.original_substitution in
      let original_names = List.filter (fun (x,_) -> x.link = SLink) csys.Constraint_system.original_names in
      { csys with Constraint_system.original_substitution = original_subst; Constraint_system.original_names = original_names }
    ) conf.configuration
  )

(** Addiing axiom in block **)

let add_axiom_in_blocks blocks csys_set =
  let csys = List.hd csys_set.Constraint_system.set in
  let type_max = Data_structure.IK.get_max_type_recipe csys.Constraint_system.knowledge csys.Constraint_system.incremented_knowledge in
  Block.add_axiom_after_constraint_solving type_max blocks

(** Cleaning constraint systems **)

let generate_matching_status forall_matched exists_match = match forall_matched, exists_match with
  | [],_ -> Configuration.ForAll
  | _,[] -> Configuration.Exists
  | _ -> Configuration.Both

let linked_improper_reference = ref []

let update_improper_reference symb_conf =
  let imp_ref = symb_conf.improper_ref in
  let last_improper_label = match symb_conf.configuration.Configuration.blocks.Block.local_improper_blocks with
    | [] ->
        (* The improper block hasn't been transfered yet *)
        Label.get_label_of_standard_complete (List.hd symb_conf.configuration.Configuration.blocks.Block.local_proper_blocks)
    | clbl::_ -> Label.get_label_of_standard_complete clbl
  in
  match !imp_ref with
    | None ->
        imp_ref := Some last_improper_label;
        linked_improper_reference := imp_ref :: !linked_improper_reference;
        true
    | Some label' ->
        if Label.independent last_improper_label label' < 0
        then
          begin
            imp_ref := Some last_improper_label;
            true
          end
        else false

let check_improper_reference symb_conf =
  let imp_ref = symb_conf.improper_ref in
  let last_improper_label = match symb_conf.configuration.Configuration.blocks.Block.local_improper_blocks with
    | [] ->
        (* The improper block hasn't been transfered yet *)
        Label.get_label_of_standard_complete (List.hd symb_conf.configuration.Configuration.blocks.Block.local_proper_blocks)
    | clbl::_ -> Label.get_label_of_standard_complete clbl
  in
  match !imp_ref with
    | None -> Config.internal_error "[session_equivalence >> check_improper_reference] The reference should have been instantiate."
    | Some complete' -> last_improper_label = complete'

let instantiate_clean_generate_forall_set is_proper_phase cur_was_modified was_modified last_ground_index general_blocks csys_solved =
  let updated_current_block = ref None in
  let all_sure_proper = ref true in

  let get_update_current_block () = match !updated_current_block with
    | Some (gen_block,cur_modified) -> gen_block,cur_modified
    | None ->
        match general_blocks.Block.current_recipe_block with
          | None -> Config.internal_error "[session_equivalence.ml >> instantiate_clean_generate_forall_set] We should be in proper phase."
          | Some c_block ->
              let (c_block',_,cur_modified) = Block.update_recipe c_block in
              let gen_block = { general_blocks with Block.current_recipe_block = Some c_block' } in
              updated_current_block := Some (gen_block,cur_modified);
              gen_block,cur_modified
  in

  let is_next_phase_improper_focus =
    let one_csys = List.hd csys_solved.Constraint_system.set in
    let conf = one_csys.Constraint_system.additional_data.configuration in
    conf.Configuration.output_proc = [] &&
    conf.Configuration.focused_proc = None &&
    (general_blocks.Block.current_recipe_block = None || not general_blocks.Block.current_block_sure_proper)
  in

  let (gen_current_to_check_and_general_block,may_modify) =
    if general_blocks.Block.current_block_sure_proper
    then
      let current_to_check = is_proper_phase && cur_was_modified in
      (fun _ -> current_to_check,general_blocks),false
    else
      if is_proper_phase
      then
        (fun symb ->
          if symb.sure_proper_transition
          then
            let (gen_block,cur_modified) = get_update_current_block () in
            (cur_modified,gen_block)
          else
            begin
              all_sure_proper := false;
              false,general_blocks
            end
        ),true
      else (fun _ -> false,general_blocks),false
  in

  let (update_improper_block, check_smallest) =
    if is_next_phase_improper_focus
    then update_improper_reference, check_improper_reference
    else (fun _ -> true), (fun _ -> true)
  in

  let forall_set_1 =
    List.fold_left (fun acc old_csys -> match old_csys.Constraint_system.additional_data.link_c with
      | CCsys new_csys ->
          let new_symb_conf = new_csys.Constraint_system.additional_data in
          let old_symb_conf = old_csys.Constraint_system.additional_data in

          if old_symb_conf.exists_matched <> []
          then
            let (current_to_check,gen_blocks) = gen_current_to_check_and_general_block old_symb_conf in
            (* Important : Block.is_authorised must be done before update_improper_block *)
            if Block.is_authorised current_to_check was_modified last_ground_index gen_blocks new_symb_conf.configuration.Configuration.blocks && update_improper_block new_symb_conf
            then
              begin
                (* Must find forall *)
                let new_exists_matched_1 =
                  List.fold_left (fun acc' (old_csys',bset) -> match old_csys'.Constraint_system.additional_data.link_c with
                    | CCsys new_csys' -> (new_csys',bset)::acc'
                    | _ -> acc'
                  ) [] old_symb_conf.exists_matched
                in
                if new_exists_matched_1 = []
                then raise (Not_Session_Equivalent (generate_attack_trace new_csys));
                new_symb_conf.exists_matched <- new_exists_matched_1;
                new_symb_conf.forall_bset <- old_symb_conf.forall_bset;
                new_csys::acc
              end
            else acc
          else acc
      | _ -> Config.internal_error "[session_equivalence.ml >> instantiate_clean_generate_forall_set] All constraint system should be linked."
    ) [] csys_solved.Constraint_system.set
  in

  let forall_set_2 =
    if is_next_phase_improper_focus
    then
      List.fold_left (fun acc new_csys ->
        let new_symb_conf = new_csys.Constraint_system.additional_data in
        if check_smallest new_csys.Constraint_system.additional_data
        then new_csys::acc
        else
          begin
            new_symb_conf.exists_matched <- [];
            new_symb_conf.forall_bset <- [];
            acc
          end
      ) [] forall_set_1
    else forall_set_1
  in

  List.iter (fun imp_ref -> imp_ref := None) !linked_improper_reference;
  linked_improper_reference := [];

  List.iter (fun old_csys -> match old_csys.Constraint_system.additional_data.link_c with
    | CCsys new_csys ->
        let new_symb_conf = new_csys.Constraint_system.additional_data in
        let old_symb_conf = old_csys.Constraint_system.additional_data in
        let new_forall_matched =
          List.fold_left (fun acc' old_csys' -> match old_csys'.Constraint_system.additional_data.link_c with
            | CCsys new_csys' ->
                if new_csys'.Constraint_system.additional_data.exists_matched = []
                then acc'
                else
                  begin
                    Config.debug (fun () ->
                      if List.for_all (fun (csys,_) -> csys != new_csys) new_csys'.Constraint_system.additional_data.exists_matched
                      then Config.internal_error "[session_equivalence.ml >> instantiate_clean_generate_forall_set] If new_csys has not been downgraded by Block.is_authorised then the constraint system should occur."
                    );
                    new_csys'::acc'
                  end
            | _ -> acc'
          ) [] old_symb_conf.forall_matched
        in
        new_symb_conf.forall_matched <- new_forall_matched;
        new_symb_conf.matching_status <- generate_matching_status new_forall_matched new_symb_conf.exists_matched
    | _ -> Config.internal_error "[session_equivalence.ml >> instantiate_clean_generate_forall_set] All constraint system should be linked (2)."
  ) csys_solved.Constraint_system.set;

  if may_modify && !all_sure_proper
  then
    match !updated_current_block with
      | Some(gen_block,_) -> forall_set_2,gen_block
      | _ -> forall_set_2, general_blocks
  else forall_set_2, general_blocks

(** Computing channel priority **)

let determine_channel_priority forall_set =
  let all_priority = ref true in
  List.iter (fun csys ->
    let sym_conf = csys.Constraint_system.additional_data in
    match Configuration.determine_channel_priority sym_conf.configuration with
      | None ->
          all_priority := false;
          link_symbolic_configuration sym_conf (CChannelPriority Configuration.ChNone)
      | Some ch ->
          link_symbolic_configuration sym_conf (CChannelPriority (Configuration.ChPriority(ch,false)))
  ) forall_set;

  if !all_priority
  then
    List.iter (fun csys ->
      let sym_conf = csys.Constraint_system.additional_data in
      match sym_conf.link_c with
        | CChannelPriority (Configuration.ChPriority(ch,false)) -> sym_conf.link_c <- CChannelPriority (Configuration.ChPriority(ch,true))
        | _ -> ()
    ) forall_set;

  !all_priority

(** Determine proper status **)

let is_proper_block_neg_phase out_trans =
  let skel = out_trans.Configuration.out_skeletons in
  skel.Labelled_process.input_skel <> [] || skel.Labelled_process.private_channels <> []

let is_proper_block_pos_focus_phase_in in_trans =
  let skel = in_trans.Configuration.in_skeletons in
  match skel.Labelled_process.input_skel with
    | [(_,1,_)] -> skel.Labelled_process.output_skel <> [] || skel.Labelled_process.private_channels <> []
    | [] -> skel.Labelled_process.private_channels <> []
    | _ -> true

let is_proper_block_pos_focus_phase_comm comm_trans =
  let out_skel = comm_trans.Configuration.comm_out_skeletons in
  let in_skel = comm_trans.Configuration.comm_in_skeletons in

  in_skel.Labelled_process.input_skel <> [] ||
  out_skel.Labelled_process.input_skel <> [] ||
  in_skel.Labelled_process.private_channels <> [] ||
  out_skel.Labelled_process.private_channels <> []

let is_proper_block_start_phase start_trans =
  let skel = start_trans.Configuration.start_skeletons in
  match skel.Labelled_process.input_skel with
    | [(_,1,_)] -> skel.Labelled_process.output_skel <> [] || skel.Labelled_process.private_channels <> []
    | [] -> skel.Labelled_process.private_channels <> []
    | _ -> true

(** Computation before focus phase
    We need to compute the following before applying a focus phase:
      - Removal of trivial improper inputs
**)

let get_improper_inputs symb = match symb.link_c with
  | CNoLink ->
      let (imp_data, conf) = Configuration.get_improper_inputs symb.configuration in
      let old_conf = symb.configuration in
      symb.configuration <- conf;
      link_symbolic_configuration symb (CImproperInputs(imp_data,old_conf));
      imp_data
  | CImproperInputs(imp_data,_) -> imp_data
  | _ -> Config.internal_error "[session_equivalence.ml >> link_symbolic_configuration_with_improper_inputs] Unexpected links"

let compute_before_focus_phase equiv_pbl =

  let record_improper_conf = ref [] in

  let rec explore_forall_set = function
    | [] ->
        (* Not exception was raised meaning that we managed to match every improper inputs. *)
        List.iter (fun symb -> symb.link_c <- CNoLink) !linked_symbolic_configuration;
        linked_symbolic_configuration := [];
        record_improper_conf := []
    | forall_csys::q_csys ->
        let forall_symb_conf = forall_csys.Constraint_system.additional_data in
        let forall_imp_data = get_improper_inputs forall_symb_conf in
        let exists_matched_1 = forall_symb_conf.exists_matched in
        let forall_bset = forall_symb_conf.forall_bset in
        let (id_bset_l,forall_bset') = Bijection_set.check_and_remove_forall 0 forall_imp_data.Configuration.imp_labels forall_bset in

        let exists_matched_2 =
          List.rev_map (fun (exists_csys,bset_exists) ->
            let exists_imp_data = get_improper_inputs exists_csys.Constraint_system.additional_data in
            if forall_imp_data.Configuration.nb_labels = exists_imp_data.Configuration.nb_labels &&
              forall_imp_data.Configuration.nb_prefix = exists_imp_data.Configuration.nb_prefix
            then
              let bset_exists' = Bijection_set.check_and_remove_exists 0 id_bset_l exists_imp_data.Configuration.imp_labels bset_exists in
              (exists_csys,bset_exists')
            else raise Not_found
          ) exists_matched_1
        in
        record_improper_conf := (forall_symb_conf,forall_bset,forall_symb_conf.exists_matched)::!record_improper_conf;
        forall_symb_conf.exists_matched <- exists_matched_2;
        forall_symb_conf.forall_bset <- forall_bset';
        explore_forall_set q_csys
  in

  try
    explore_forall_set equiv_pbl.forall_set
  with Not_found ->
    (* Clean and restaure *)
    List.iter (fun symb -> match symb.link_c with
      | CImproperInputs(_,conf) -> symb.configuration <- conf
      | _ -> Config.internal_error "[session_equivalence.ml >> compute_before_focus_phase] Symbolic configuration should be link."
    ) !linked_symbolic_configuration;
    linked_symbolic_configuration := [];
    List.iter (fun (symb,forall_bset,exists_matched) ->
      symb.exists_matched <- exists_matched;
      symb.forall_bset <- forall_bset
    ) !record_improper_conf;
    record_improper_conf := []

(** Application of transitions **)

let apply_neg_phase equiv_pbl f_continuation f_next =
  Config.debug (fun () ->
    if equiv_pbl.forall_set = []
    then Config.internal_error "[session_equivalence.ml >> apply_neg_phase] The set of constraint system should not be empty.";
    if equiv_pbl.public_output_channels = []
    then Config.internal_error "[session_equivalence.ml >> apply_neg_phase] The function should only be applied when there are public channels.";
    if !linked_symbolic_configuration <> []
    then Config.internal_error "[session_equivalence.ml >> apply_neg_phase] No symbolic configuration should be linked.";
    debug_equivalence_problem "[session_equivalence.ml >> apply_neg_phase]" equiv_pbl;

    if select_specified_trace equiv_pbl
    then Config.log_in_debug Config.Process "[session_equivalence.ml] Apply neg phase"
  );

  let is_in_improper_phase = equiv_pbl.general_blocks.Block.current_recipe_block = None in

  let generate_next_public_output =
    if is_in_improper_phase
    then Configuration.next_neg_improper_phase
    else Configuration.next_neg_phase
  in

  let target_ch = fst (List.hd equiv_pbl.public_output_channels) in
  let target_ch_recipe = Channel.recipe_of target_ch in

  let axiom = equiv_pbl.size_frame + 1 in

  let generate_transitions csys =
    let symb_conf = csys.Constraint_system.additional_data in
    match symb_conf.link_c with
      | CNoLink ->

          let transitions_forall = ref [] in
          let transitions_exists = ref [] in
          let transitions_both = ref [] in

          Variable.auto_cleanup_with_reset_notail (fun () ->
            List.iter (fun (x,t) -> Variable.link_term x t) csys.Constraint_system.original_substitution;
            List.iter (fun (x,n) -> Variable.link_term x (Name n)) csys.Constraint_system.original_names;

            generate_next_public_output symb_conf.matching_status target_ch csys.Constraint_system.original_substitution csys.Constraint_system.original_names symb_conf.configuration (fun out_trans conf_1 ->
              let eq_uniformity = Formula.T.instantiate_and_normalise_full csys.Constraint_system.eq_uniformity in
              if eq_uniformity = Formula.T.Bot
              then ()
              else
                let symb_conf_1 =
                  { symb_conf with
                    configuration = conf_1;
                    matching_status = out_trans.Configuration.out_matching_status;
                    trace = AOutput(target_ch_recipe,out_trans.Configuration.out_position) :: symb_conf.trace;
                    transition_data = TransOutput out_trans;
                    link_c = CNoLink;
                    forall_matched = [];
                    exists_matched = [];
                    sure_proper_transition = out_trans.Configuration.out_skeletons.Labelled_process.sure_proper
                  }
                in
                let csys_1 = Constraint_system.add_axiom csys axiom out_trans.Configuration.out_term in
                let csys_2 =
                  { csys_1 with
                    Constraint_system.eq_term = out_trans.Configuration.out_gathering_normalise.Labelled_process.disequations;
                    Constraint_system.original_substitution = out_trans.Configuration.out_gathering_normalise.Labelled_process.original_subst;
                    Constraint_system.original_names = out_trans.Configuration.out_gathering_normalise.Labelled_process.original_names;
                    Constraint_system.eq_uniformity = eq_uniformity;
                    Constraint_system.additional_data = symb_conf_1
                  }
                in
                let csys_3 = Constraint_system.prepare_for_solving_procedure true csys_2 in

                match out_trans.Configuration.out_matching_status with
                  | Configuration.Exists -> transitions_exists := csys_3::!transitions_exists
                  | Configuration.ForAll -> transitions_forall := csys_3::!transitions_forall
                  | Configuration.Both -> transitions_both := csys_3::!transitions_both
            )
          );

          let gen_trans =
            {
              gt_forall = clean_variables_names !transitions_forall;
              gt_exists = clean_variables_names!transitions_exists;
              gt_both = clean_variables_names !transitions_both
            }
          in
          link_symbolic_configuration symb_conf (CTransition gen_trans);
          gen_trans
      | CTransition gen_trans -> gen_trans
      | _ -> Config.internal_error "[session_equivalence.ml >> apply_public_output] Unexpected link during generation of transitions."
  in

  (* Generate the new matching set *)

  let forall_set_1 = ref [] in

  auto_cleanup_symbolic_configuration (fun () ->
    List.iter (fun forall_csys ->
      let gen_forall_transitions = generate_transitions forall_csys in
      iter_forall_both (fun forall_csys_1 ->
        let forall_trans = match forall_csys_1.Constraint_system.additional_data.transition_data with
          | TransOutput trans -> trans
          | _ -> Config.internal_error "[session_equivalence.ml >> apply_public_out] Expecting an output transition."
        in
        let (generate_bset_exists,forall_bset) = Bijection_set.generate_forall forall_trans.Configuration.out_label forall_trans.Configuration.out_skeletons forall_csys.Constraint_system.additional_data.forall_bset in

        List.iter (fun (exists_csys,exists_bset) ->
          let gen_exists_transitions = generate_transitions exists_csys in
          iter_exists_both (fun exists_csys_1 ->
            let exists_trans = match exists_csys_1.Constraint_system.additional_data.transition_data with
              | TransOutput trans -> trans
              | _ -> Config.internal_error "[session_equivalence.ml >> apply_public_out] Expecting an output transition (2)."
            in
            match generate_bset_exists exists_trans.Configuration.out_label exists_trans.Configuration.out_skeletons exists_bset with
              | None -> ()
              | Some exists_bset1 ->
                  exists_csys_1.Constraint_system.additional_data.forall_matched <- forall_csys_1 :: exists_csys_1.Constraint_system.additional_data.forall_matched;
                  forall_csys_1.Constraint_system.additional_data.exists_matched <- (exists_csys_1,exists_bset1) :: forall_csys_1.Constraint_system.additional_data.exists_matched;
                  forall_csys_1.Constraint_system.additional_data.forall_bset <- forall_bset
          ) gen_exists_transitions;
        ) forall_csys.Constraint_system.additional_data.exists_matched;
        forall_set_1 := forall_csys_1 :: !forall_set_1
      ) gen_forall_transitions
    ) equiv_pbl.forall_set;
  );

  (* Apply the first split *)

  split_forall_set !forall_set_1 (fun forall_set_2 csys_to_solve f_next_1 ->
    (* We first calculate the new public_output_channels and we check if we can determine whether
       the current block is surely proper. *)
    let (public_output_channels,general_blocks_1) =
      let csys = List.hd forall_set_2 in
      match csys.Constraint_system.additional_data.transition_data with
        | TransOutput out_trans ->
            let general_blocks =
              if is_proper_block_neg_phase out_trans
              then { equiv_pbl.general_blocks with Block.current_block_sure_proper = true }
              else equiv_pbl.general_blocks
            in
            let pub_output = Configuration.update_public_output_channel_out_transition target_ch out_trans equiv_pbl.public_output_channels in
            (pub_output,general_blocks)
        | _ -> Config.internal_error "[session_equivalence.ml >> apply_public_output] Output transition data expected."
    in

    let csys_set =
      {
        Constraint_system.eq_recipe = equiv_pbl.eq_recipe;
        Constraint_system.set = csys_to_solve
      }
    in

    Constraint_system.Rule.apply_rules_after_output false (fun csys_solved_1 f_next_2 ->
      if csys_solved_1.Constraint_system.set = []
      then f_next_2 ()
      else
        Constraint_system.Rule.instantiate_useless_deduction_facts (fun csys_solved_2 f_next_3 ->
          (* We start by adding the axiom in the block *)
          match add_axiom_in_blocks general_blocks_1 csys_solved_2 with
            | None ->
                (* In such a case, we are in improper phase and the axiom is not useless *)
                f_next_3 ()
            | Some general_blocks_2 ->
                (* We update the recipes of general blocks *)
                let last_ground_index = general_blocks_2.Block.ground_index in

                let (general_blocks_3,was_modified,cur_was_modified) = Block.update_recipes_in_general_block general_blocks_2 in
                (* We remove the constraint systems that are not authorised and
                   we link the authorised one with fresh copy *)
                let (forall_set_3,general_blocks_4) =
                  auto_cleanup_symbolic_configuration (fun () ->
                    link_constraint_systems csys_solved_2;
                    instantiate_clean_generate_forall_set (not is_in_improper_phase) cur_was_modified was_modified last_ground_index general_blocks_3 csys_solved_2
                  )
                in

                split_forall_set forall_set_3 (fun forall_set_4 _ f_next_4 ->
                  let equiv_pbl_1 =
                    {
                      size_frame = equiv_pbl.size_frame + 1;
                      forall_set = forall_set_4;
                      eq_recipe = csys_solved_2.Constraint_system.eq_recipe;
                      general_blocks = general_blocks_4;
                      public_output_channels = public_output_channels
                    }
                  in
                  f_continuation equiv_pbl_1 f_next_4
                ) f_next_3
        ) csys_solved_1 f_next_2
    ) csys_set f_next_1
  ) f_next

(* We assume that the current block has not been closed.
  It should be done during the generation of transition. *)
let apply_focus_phase equiv_pbl f_continuation f_next =
  Config.debug (fun () ->
    if equiv_pbl.forall_set = []
    then Config.internal_error "[session_equivalence.ml >> apply_focus_phase] The set of constraint system should not be empty.";
    if equiv_pbl.public_output_channels <> []
    then Config.internal_error "[session_equivalence.ml >> apply_focus_phase] The function should only be applied when there are no public channels.";
    if !linked_symbolic_configuration <> []
    then Config.internal_error "[session_equivalence.ml >> apply_focus_phase] No symbolic configuration should be linked.";
    debug_equivalence_problem "[session_equivalence.ml >> apply_focus_phase]" equiv_pbl;

    Config.log_in_debug Config.Process "[session_equivalence.ml] Apply focus phase"
  );

  let is_in_improper_phase =
    equiv_pbl.general_blocks.Block.current_recipe_block = None ||
    not equiv_pbl.general_blocks.Block.current_block_sure_proper
  in

  let is_transition_from_proper_to_improper =
    equiv_pbl.general_blocks.Block.current_recipe_block <> None &&
    not equiv_pbl.general_blocks.Block.current_block_sure_proper
  in

  let general_blocks_0 = Block.close_current_recipe_block equiv_pbl.general_blocks in

  let type_max =
    let csys = List.hd equiv_pbl.forall_set in
    (Data_structure.IK.get_max_type_recipe csys.Constraint_system.knowledge csys.Constraint_system.incremented_knowledge)
  in
  let var_X_t = Recipe_Variable.fresh Free type_max in

  (* Generate the new matching set *)

  let forall_set_1 = ref [] in

  auto_cleanup_symbolic_configuration (fun () ->
    let only_private =
      if is_in_improper_phase
      then false
      else determine_channel_priority equiv_pbl.forall_set
    in

    let generate_next_public_input_comm_nolink  =
      if is_in_improper_phase
      then Configuration.next_focus_improper_phase
      else
        if only_private
        then Configuration.next_focus_phase Configuration.ChOnlyPrivate
        else Configuration.next_focus_phase Configuration.ChNone
    in

    let generate_transitions csys =
      let symb_conf = csys.Constraint_system.additional_data in
      let generate_next_public_input_comm = match symb_conf.link_c with
        | CChannelPriority ch -> Configuration.next_focus_phase ch
        | _ -> generate_next_public_input_comm_nolink
      in
      match symb_conf.link_c with
        | CNoLink | CChannelPriority _ ->
            let improper_ref = ref None in

            let transitions_forall = ref [] in
            let transitions_exists = ref [] in
            let transitions_both = ref [] in

            let closed_configuration =
              if is_transition_from_proper_to_improper
              then { symb_conf.configuration with Configuration.blocks = Block.transition_proper_to_improper_phase symb_conf.configuration.Configuration.blocks }
              else symb_conf.configuration
            in

            Variable.auto_cleanup_with_reset_notail (fun () ->
              List.iter (fun (x,t) -> Variable.link_term x t) csys.Constraint_system.original_substitution;
              List.iter (fun (x,n) -> Variable.link_term x (Name n)) csys.Constraint_system.original_names;

              generate_next_public_input_comm symb_conf.matching_status csys.Constraint_system.original_substitution csys.Constraint_system.original_names closed_configuration (fun in_comm_trans conf_1 ->
                let eq_uniformity = Formula.T.instantiate_and_normalise_full csys.Constraint_system.eq_uniformity in
                if eq_uniformity = Formula.T.Bot
                then ()
                else
                  match in_comm_trans.Configuration.in_comm_type with
                    | Configuration.TInput in_trans ->
                        let symb_conf_1 =
                          { symb_conf with
                            configuration = conf_1;
                            matching_status = in_comm_trans.Configuration.in_comm_matching_status;
                            trace = AInput(in_trans.Configuration.in_channel,RVar var_X_t,in_trans.Configuration.in_position) :: symb_conf.trace;
                            transition_data = TransInComm in_comm_trans;
                            link_c = CNoLink;
                            forall_matched = [];
                            exists_matched = [];
                            improper_ref = improper_ref;
                            sure_proper_transition = in_trans.Configuration.in_skeletons.Labelled_process.sure_proper
                          }
                        in
                        let dfact_t = { Data_structure.bf_var = var_X_t; Data_structure.bf_term = in_trans.Configuration.in_term  } in
                        let csys_1 =
                          { csys with
                            Constraint_system.deduction_facts = Data_structure.DF.add_multiple_max_type csys.Constraint_system.deduction_facts [dfact_t];
                            Constraint_system.eq_term = in_comm_trans.Configuration.in_comm_gathering_normalise.Labelled_process.disequations;
                            Constraint_system.original_substitution =in_comm_trans.Configuration.in_comm_gathering_normalise.Labelled_process.original_subst;
                            Constraint_system.original_names = in_comm_trans.Configuration.in_comm_gathering_normalise.Labelled_process.original_names;
                            Constraint_system.eq_uniformity = eq_uniformity;
                            Constraint_system.additional_data = symb_conf_1
                          }
                        in
                        let csys_2 = Constraint_system.prepare_for_solving_procedure false csys_1 in

                        begin match in_comm_trans.Configuration.in_comm_matching_status with
                          | Configuration.Exists -> transitions_exists := csys_2::!transitions_exists
                          | Configuration.ForAll -> transitions_forall := csys_2::!transitions_forall
                          | Configuration.Both -> transitions_both := csys_2::!transitions_both
                        end
                    | Configuration.TComm comm_trans ->
                        let symb_conf_1 =
                          { symb_conf with
                            configuration = conf_1;
                            matching_status = in_comm_trans.Configuration.in_comm_matching_status;
                            trace = AComm(comm_trans.Configuration.comm_out_position,comm_trans.Configuration.comm_in_position) :: symb_conf.trace;
                            transition_data = TransInComm in_comm_trans;
                            link_c = CNoLink;
                            forall_matched = [];
                            exists_matched = [];
                            improper_ref = improper_ref;
                            sure_proper_transition = comm_trans.Configuration.comm_out_skeletons.Labelled_process.sure_proper || comm_trans.Configuration.comm_in_skeletons.Labelled_process.sure_proper
                          }
                        in
                        let csys_1 =
                          { csys with
                            Constraint_system.eq_term = in_comm_trans.Configuration.in_comm_gathering_normalise.Labelled_process.disequations;
                            Constraint_system.original_substitution = in_comm_trans.Configuration.in_comm_gathering_normalise.Labelled_process.original_subst;
                            Constraint_system.original_names = in_comm_trans.Configuration.in_comm_gathering_normalise.Labelled_process.original_names;
                            Constraint_system.eq_uniformity = eq_uniformity;
                            Constraint_system.additional_data = symb_conf_1
                          }
                        in
                        let csys_2 = Constraint_system.prepare_for_solving_procedure false csys_1 in

                        begin match in_comm_trans.Configuration.in_comm_matching_status with
                          | Configuration.Exists -> transitions_exists := csys_2::!transitions_exists
                          | Configuration.ForAll -> transitions_forall := csys_2::!transitions_forall
                          | Configuration.Both -> transitions_both := csys_2::!transitions_both
                        end
              )
            );

            let gen_trans =
              {
                gt_forall = clean_variables_names !transitions_forall;
                gt_exists = clean_variables_names !transitions_exists;
                gt_both = clean_variables_names !transitions_both
              }
            in

            if symb_conf.link_c = CNoLink
            then link_symbolic_configuration symb_conf (CTransition gen_trans)
            else symb_conf.link_c <- CTransition gen_trans;
            gen_trans
        | CTransition gen_trans -> gen_trans
        | _ -> Config.internal_error "[session_equivalence.ml >> apply_public_output] Unexpected link during generation of transitions."
    in

    List.iter (fun forall_csys ->
      let gen_forall_transitions = generate_transitions forall_csys in
      iter_forall_both (fun forall_csys_1 ->
        let forall_trans = match forall_csys_1.Constraint_system.additional_data.transition_data with
          | TransInComm trans -> trans
          | _ -> Config.internal_error "[session_equivalence.ml >> apply_focus_phase] Expecting an in/comm transition."
        in
        let (generate_bset_exists,forall_bset) = Bijection_set.generate_in_comm forall_trans forall_csys.Constraint_system.additional_data.forall_bset in
        List.iter (fun (exists_csys,exists_bset) ->
          let gen_exists_transitions = generate_transitions exists_csys in
          iter_exists_both (fun exists_csys_1 ->
            let exists_trans = match exists_csys_1.Constraint_system.additional_data.transition_data with
              | TransInComm trans -> trans
              | _ -> Config.internal_error "[session_equivalence.ml >> apply_focus_phase] Expecting an in/comm transition (2)."
            in
            match generate_bset_exists exists_trans exists_bset with
              | None -> ()
              | Some exists_bset1 ->
                  exists_csys_1.Constraint_system.additional_data.forall_matched <- forall_csys_1 :: exists_csys_1.Constraint_system.additional_data.forall_matched;
                  forall_csys_1.Constraint_system.additional_data.exists_matched <- (exists_csys_1,exists_bset1) :: forall_csys_1.Constraint_system.additional_data.exists_matched;
                  forall_csys_1.Constraint_system.additional_data.forall_bset <- forall_bset
          ) gen_exists_transitions;
        ) forall_csys.Constraint_system.additional_data.exists_matched;
        forall_set_1 := forall_csys_1 :: !forall_set_1
      ) gen_forall_transitions
    ) equiv_pbl.forall_set;
  );

  Config.debug (fun () ->
    debug_forall_exists_matched "[session_equivalence.ml >> apply_focus_phase >> After transition generated]" !forall_set_1;
  );

  (* Apply the first split *)

  split_forall_set !forall_set_1 (fun forall_set_2 csys_to_solve f_next_1 ->
    (* We first calculate the new public_output_channels and we check if we can determine whether
       the current block is surely proper. *)
     Config.debug (fun () ->
       debug_forall_exists_matched "[session_equivalence.ml >> apply_focus_phase >> After first split]" forall_set_2;
     );

    let (public_output_channels,general_blocks_1) =
      let csys = List.hd forall_set_2 in
      match csys.Constraint_system.additional_data.transition_data with
        | TransInComm { Configuration.in_comm_type = Configuration.TInput in_trans; _ } ->
            let general_blocks =
              if is_in_improper_phase
              then general_blocks_0
              else
                if is_proper_block_pos_focus_phase_in in_trans
                then Block.add_input_variable var_X_t { general_blocks_0 with Block.current_block_sure_proper = true }
                else Block.add_input_variable var_X_t general_blocks_0
            in

            let pub_output = Configuration.update_public_output_channel_in_transition in_trans equiv_pbl.public_output_channels in
            (pub_output,general_blocks)
        | TransInComm { Configuration.in_comm_type = Configuration.TComm comm_trans; _ } ->
            let general_blocks =
              if is_in_improper_phase
              then general_blocks_0
              else { general_blocks_0 with Block.current_block_sure_proper = true }
            in

            let pub_output = Configuration.update_public_output_channel_comm_transition comm_trans equiv_pbl.public_output_channels in
            (pub_output,general_blocks)
        | _ -> Config.internal_error "[session_equivalence.ml >> apply_focus_phase] In/comm transition is expected."
    in

    let csys_set =
      {
        Constraint_system.eq_recipe = equiv_pbl.eq_recipe;
        Constraint_system.set = csys_to_solve
      }
    in

    Constraint_system.Rule.apply_rules_after_input false (fun csys_solved_1 f_next_2 ->
      if csys_solved_1.Constraint_system.set = []
      then f_next_2 ()
      else
        Constraint_system.Rule.instantiate_useless_deduction_facts (fun csys_solved_2 f_next_3 ->
          (* We update the recipes of general blocks *)
          let last_ground_index = general_blocks_1.Block.ground_index in
          let (general_blocks_2,was_modified,cur_was_modified) = Block.update_recipes_in_general_block general_blocks_1 in

          (* We remove the constraint systems that are not authorised and
             we link the authorised one with fresh copy *)
          let (forall_set_3,general_blocks_3) =
            auto_cleanup_symbolic_configuration (fun () ->
              link_constraint_systems csys_solved_2;
              instantiate_clean_generate_forall_set (not is_in_improper_phase) cur_was_modified was_modified last_ground_index general_blocks_2 csys_solved_2
            )
          in

          Config.debug (fun () ->
            debug_forall_exists_matched "[session_equivalence.ml >> apply_focus_phase >> After cleaning]" forall_set_3;
          );

          split_forall_set forall_set_3 (fun forall_set_4 _ f_next_4 ->
            Config.debug (fun () ->
              debug_forall_exists_matched "[session_equivalence.ml >> apply_focus_phase >> After second split]" forall_set_4;
            );

            let equiv_pbl_1 =
              { equiv_pbl with
                forall_set = forall_set_4;
                eq_recipe = csys_solved_2.Constraint_system.eq_recipe;
                general_blocks = general_blocks_3;
                public_output_channels = public_output_channels
              }
            in
            f_continuation equiv_pbl_1 f_next_4
          ) f_next_3
        ) csys_solved_1 f_next_2
    ) csys_set f_next_1
  ) f_next

let apply_pos_phase equiv_pbl f_continuation f_next =
  Config.debug (fun () ->
    if equiv_pbl.forall_set = []
    then Config.internal_error "[session_equivalence.ml >> apply_pos_phase] The set of constraint system should not be empty.";
    if equiv_pbl.public_output_channels <> []
    then Config.internal_error "[session_equivalence.ml >> apply_pos_phase] The function should only be applied when there are no public channels.";
    if !linked_symbolic_configuration <> []
    then Config.internal_error "[session_equivalence.ml >> apply_pos_phase] No symbolic configuration should be linked.";
    debug_equivalence_problem "[session_equivalence.ml >> apply_pos_phase]" equiv_pbl;

    Config.log_in_debug Config.Process "[session_equivalence.ml] Apply Pos Phase"
  );

  let is_in_improper_phase = equiv_pbl.general_blocks.Block.current_recipe_block = None in

  let generate_next_public_input =
    if is_in_improper_phase
    then Configuration.next_pos_input_improper_phase
    else Configuration.next_pos_input
  in

  let type_max =
    let csys = List.hd equiv_pbl.forall_set in
    (Data_structure.IK.get_max_type_recipe csys.Constraint_system.knowledge csys.Constraint_system.incremented_knowledge)
  in
  let var_X_t = Recipe_Variable.fresh Free type_max in

  let generate_transitions csys =
    let symb_conf = csys.Constraint_system.additional_data in
    match symb_conf.link_c with
      | CNoLink ->
          let transitions_forall = ref [] in
          let transitions_exists = ref [] in
          let transitions_both = ref [] in

          Variable.auto_cleanup_with_reset_notail (fun () ->
            List.iter (fun (x,t) -> Variable.link_term x t) csys.Constraint_system.original_substitution;
            List.iter (fun (x,n) -> Variable.link_term x (Name n)) csys.Constraint_system.original_names;

            generate_next_public_input symb_conf.matching_status csys.Constraint_system.original_substitution csys.Constraint_system.original_names symb_conf.configuration (fun in_comm_trans conf_1 ->
              let eq_uniformity = Formula.T.instantiate_and_normalise_full csys.Constraint_system.eq_uniformity in
              if eq_uniformity = Formula.T.Bot
              then ()
              else
                match in_comm_trans.Configuration.in_comm_type with
                  | Configuration.TInput in_trans ->
                      let symb_conf_1 =
                        { symb_conf with
                          configuration = conf_1;
                          matching_status = in_comm_trans.Configuration.in_comm_matching_status;
                          trace = AInput(in_trans.Configuration.in_channel,RVar var_X_t,in_trans.Configuration.in_position) :: symb_conf.trace;
                          transition_data = TransInComm in_comm_trans;
                          link_c = CNoLink;
                          forall_matched = [];
                          exists_matched = [];
                          sure_proper_transition = in_trans.Configuration.in_skeletons.Labelled_process.sure_proper
                        }
                      in
                      let dfact_t = { Data_structure.bf_var = var_X_t; Data_structure.bf_term = in_trans.Configuration.in_term  } in
                      let csys_1 =
                        { csys with
                          Constraint_system.deduction_facts = Data_structure.DF.add_multiple_max_type csys.Constraint_system.deduction_facts [dfact_t];
                          Constraint_system.eq_term = in_comm_trans.Configuration.in_comm_gathering_normalise.Labelled_process.disequations;
                          Constraint_system.original_substitution =in_comm_trans.Configuration.in_comm_gathering_normalise.Labelled_process.original_subst;
                          Constraint_system.original_names = in_comm_trans.Configuration.in_comm_gathering_normalise.Labelled_process.original_names;
                          Constraint_system.eq_uniformity = eq_uniformity;
                          Constraint_system.additional_data = symb_conf_1
                        }
                      in
                      let csys_2 = Constraint_system.prepare_for_solving_procedure false csys_1 in

                      begin match in_comm_trans.Configuration.in_comm_matching_status with
                        | Configuration.Exists -> transitions_exists := csys_2::!transitions_exists
                        | Configuration.ForAll -> transitions_forall := csys_2::!transitions_forall
                        | Configuration.Both -> transitions_both := csys_2::!transitions_both
                      end
                  | _ -> Config.internal_error "[session_equivalence.ml >> apply_pos_phase] We can only have input transition during the pos phase."
            )
          );

          let gen_trans =
            {
              gt_forall = clean_variables_names !transitions_forall;
              gt_exists = clean_variables_names!transitions_exists;
              gt_both = clean_variables_names !transitions_both
            }
          in
          link_symbolic_configuration symb_conf (CTransition gen_trans);
          gen_trans
      | CTransition gen_trans -> gen_trans
      | _ -> Config.internal_error "[session_equivalence.ml >> apply_pos_phase] Unexpected link during generation of transitions."
  in

  (* Generate the new matching set *)

  let forall_set_1 = ref [] in

  auto_cleanup_symbolic_configuration (fun () ->
    List.iter (fun forall_csys ->
      let gen_forall_transitions = generate_transitions forall_csys in
      iter_forall_both (fun forall_csys_1 ->
        let forall_trans = match forall_csys_1.Constraint_system.additional_data.transition_data with
          | TransInComm trans -> trans
          | _ -> Config.internal_error "[session_equivalence.ml >> apply_pos_phase] Expecting an in/comm transition."
        in
        let (generate_bset_exists,forall_bset) = Bijection_set.generate_in_comm forall_trans forall_csys.Constraint_system.additional_data.forall_bset in

        List.iter (fun (exists_csys,exists_bset) ->
          let gen_exists_transitions = generate_transitions exists_csys in
          iter_exists_both (fun exists_csys_1 ->
            let exists_trans = match exists_csys_1.Constraint_system.additional_data.transition_data with
              | TransInComm trans -> trans
              | _ -> Config.internal_error "[session_equivalence.ml >> apply_pos_phase] Expecting an in/comm transition (2)."
            in
            match generate_bset_exists exists_trans exists_bset with
              | None -> ()
              | Some exists_bset1 ->
                  exists_csys_1.Constraint_system.additional_data.forall_matched <- forall_csys_1 :: exists_csys_1.Constraint_system.additional_data.forall_matched;
                  forall_csys_1.Constraint_system.additional_data.exists_matched <- (exists_csys_1,exists_bset1) :: forall_csys_1.Constraint_system.additional_data.exists_matched;
                  forall_csys_1.Constraint_system.additional_data.forall_bset <- forall_bset
          ) gen_exists_transitions;
        ) forall_csys.Constraint_system.additional_data.exists_matched;
        forall_set_1 := forall_csys_1 :: !forall_set_1
      ) gen_forall_transitions
    ) equiv_pbl.forall_set;
  );

  (* Apply the first split *)

  split_forall_set !forall_set_1 (fun forall_set_2 csys_to_solve f_next_1 ->
    (* We first calculate the new public_output_channels and we check if we can determine whether
       the current block is surely proper. *)
    let (public_output_channels,general_blocks_1) =
      let csys = List.hd forall_set_2 in
      match csys.Constraint_system.additional_data.transition_data with
        | TransInComm { Configuration.in_comm_type = Configuration.TInput in_trans; _ } ->
            let general_blocks =
              if is_in_improper_phase
              then equiv_pbl.general_blocks
              else
                if is_proper_block_pos_focus_phase_in in_trans
                then Block.add_input_variable var_X_t { equiv_pbl.general_blocks with Block.current_block_sure_proper = true }
                else Block.add_input_variable var_X_t equiv_pbl.general_blocks
            in

            let pub_output = Configuration.update_public_output_channel_in_transition in_trans equiv_pbl.public_output_channels in
            (pub_output,general_blocks)
        | _ -> Config.internal_error "[session_equivalence.ml >> apply_pos_phase] Input transition is expected."
    in

    let csys_set =
      {
        Constraint_system.eq_recipe = equiv_pbl.eq_recipe;
        Constraint_system.set = csys_to_solve
      }
    in

    Constraint_system.Rule.apply_rules_after_input false (fun csys_solved_1 f_next_2 ->
      if csys_solved_1.Constraint_system.set = []
      then f_next_2 ()
      else
        Constraint_system.Rule.instantiate_useless_deduction_facts (fun csys_solved_2 f_next_3 ->
          (* We update the recipes of general blocks *)
          let last_ground_index = general_blocks_1.Block.ground_index in
          let (general_blocks_2,was_modified,cur_was_modified) = Block.update_recipes_in_general_block general_blocks_1 in

          (* We remove the constraint systems that are not authorised and
             we link the authorised one with fresh copy *)
          let (forall_set_3,general_blocks_3) =
            auto_cleanup_symbolic_configuration (fun () ->
              link_constraint_systems csys_solved_2;
              instantiate_clean_generate_forall_set (not is_in_improper_phase) cur_was_modified was_modified last_ground_index general_blocks_2 csys_solved_2
            )
          in

          split_forall_set forall_set_3 (fun forall_set_4 _ f_next_4 ->
            let equiv_pbl_1 =
              { equiv_pbl with
                forall_set = forall_set_4;
                eq_recipe = csys_solved_2.Constraint_system.eq_recipe;
                general_blocks = general_blocks_3;
                public_output_channels = public_output_channels
              }
            in
            f_continuation equiv_pbl_1 f_next_4
          ) f_next_3
        ) csys_solved_1 f_next_2
    ) csys_set f_next_1
  ) f_next

let apply_start equiv_pbl f_continuation f_next =
  Config.debug (fun () ->
    if !linked_symbolic_configuration <> []
    then Config.internal_error "[session_equivalence.ml >> apply_start] No symbolic configuration should be linked.";
    debug_equivalence_problem "[session_equivalence.ml >> apply_start]" equiv_pbl;

    Config.log_in_debug Config.Process "[session_equivalence.ml] Apply start";
  );

  let generate_transitions csys =
    let symb_conf = csys.Constraint_system.additional_data in
    match symb_conf.link_c with
      | CNoLink ->
          let improper_ref = ref None in
          let transitions_forall = ref [] in
          let transitions_exists = ref [] in
          let transitions_both = ref [] in

          Variable.auto_cleanup_with_reset_notail (fun () ->
            List.iter (fun (x,t) -> Variable.link_term x t) csys.Constraint_system.original_substitution;
            List.iter (fun (x,n) -> Variable.link_term x (Name n)) csys.Constraint_system.original_names;

            Configuration.next_start_phase symb_conf.matching_status csys.Constraint_system.original_substitution csys.Constraint_system.original_names symb_conf.configuration (fun start_trans conf_1 ->
              let eq_uniformity = Formula.T.instantiate_and_normalise_full csys.Constraint_system.eq_uniformity in
              if eq_uniformity = Formula.T.Bot
              then ()
              else
                let symb_conf_1 =
                  { symb_conf with
                    configuration = conf_1;
                    matching_status = start_trans.Configuration.start_matching_status;
                    transition_data = TransStart start_trans;
                    link_c = CNoLink;
                    forall_matched = [];
                    exists_matched = [];
                    improper_ref = improper_ref;
                    sure_proper_transition = start_trans.Configuration.start_skeletons.Labelled_process.sure_proper
                  }
                in
                let csys_1 =
                  { csys with
                    Constraint_system.eq_term = start_trans.Configuration.start_gathering_normalise.Labelled_process.disequations;
                    Constraint_system.original_substitution = start_trans.Configuration.start_gathering_normalise.Labelled_process.original_subst;
                    Constraint_system.original_names = start_trans.Configuration.start_gathering_normalise.Labelled_process.original_names;
                    Constraint_system.eq_uniformity = eq_uniformity;
                    Constraint_system.additional_data = symb_conf_1
                  }
                in
                let csys_2 = Constraint_system.prepare_for_solving_procedure false csys_1 in

                begin match start_trans.Configuration.start_matching_status with
                  | Configuration.Exists -> transitions_exists := csys_2::!transitions_exists
                  | Configuration.ForAll -> transitions_forall := csys_2::!transitions_forall
                  | Configuration.Both -> transitions_both := csys_2::!transitions_both
                end
            )
          );

          let gen_trans =
            {
              gt_forall = clean_variables_names !transitions_forall;
              gt_exists = clean_variables_names!transitions_exists;
              gt_both = clean_variables_names !transitions_both
            }
          in
          link_symbolic_configuration symb_conf (CTransition gen_trans);
          gen_trans
      | CTransition gen_trans -> gen_trans
      | _ -> Config.internal_error "[session_equivalence.ml >> apply_pos_phase] Unexpected link during generation of transitions."
  in

  (* Generate the new matching set *)

  let forall_set_1 = ref [] in

  auto_cleanup_symbolic_configuration (fun () ->
    List.iter (fun forall_csys ->
      let gen_forall_transitions = generate_transitions forall_csys in
      iter_forall_both (fun forall_csys_1 ->
        let forall_trans = match forall_csys_1.Constraint_system.additional_data.transition_data with
          | TransStart trans -> trans
          | _ -> Config.internal_error "[session_equivalence.ml >> apply_pos_phase] Expecting an in/comm transition."
        in
        let (generate_bset_exists, forall_bset) = Bijection_set.generate_forall Label.initial forall_trans.Configuration.start_skeletons forall_csys.Constraint_system.additional_data.forall_bset in
        List.iter (fun (exists_csys,exists_bset) ->
          let gen_exists_transitions = generate_transitions exists_csys in
          iter_exists_both (fun exists_csys_1 ->
            let exists_trans = match exists_csys_1.Constraint_system.additional_data.transition_data with
              | TransStart trans -> trans
              | _ -> Config.internal_error "[session_equivalence.ml >> apply_pos_phase] Expecting an in/comm transition (2)."
            in
            match generate_bset_exists Label.initial exists_trans.Configuration.start_skeletons exists_bset with
              | None -> ()
              | Some exists_bset1 ->
                  exists_csys_1.Constraint_system.additional_data.forall_matched <- forall_csys_1 :: exists_csys_1.Constraint_system.additional_data.forall_matched;
                  forall_csys_1.Constraint_system.additional_data.exists_matched <- (exists_csys_1,exists_bset1) :: forall_csys_1.Constraint_system.additional_data.exists_matched;
                  forall_csys_1.Constraint_system.additional_data.forall_bset <- forall_bset
          ) gen_exists_transitions;
        ) forall_csys.Constraint_system.additional_data.exists_matched;
        forall_set_1 := forall_csys_1 :: !forall_set_1
      ) gen_forall_transitions
    ) equiv_pbl.forall_set;
  );

  (* Apply the first split *)

  split_forall_set !forall_set_1 (fun forall_set_2 csys_to_solve f_next_1 ->
    (* We first calculate the new public_output_channels and we check if we can determine whether
       the current block is surely proper. *)
    let (public_output_channels,general_blocks_1) =
      let csys = List.hd forall_set_2 in
      match csys.Constraint_system.additional_data.transition_data with
        | TransStart start_trans ->
            let general_blocks =
              if is_proper_block_start_phase start_trans
              then { equiv_pbl.general_blocks with Block.current_block_sure_proper = true }
              else equiv_pbl.general_blocks
            in

            let pub_output = Configuration.update_public_output_channel_start_transition start_trans equiv_pbl.public_output_channels in
            (pub_output,general_blocks)
        | _ -> Config.internal_error "[session_equivalence.ml >> apply_pos_phase] Input transition is expected."
    in

    let csys_set =
      {
        Constraint_system.eq_recipe = equiv_pbl.eq_recipe;
        Constraint_system.set = csys_to_solve
      }
    in

    Constraint_system.Rule.apply_rules_after_input false (fun csys_solved_1 f_next_2 ->
      if csys_solved_1.Constraint_system.set = []
      then f_next_2 ()
      else
        Constraint_system.Rule.instantiate_useless_deduction_facts (fun csys_solved_2 f_next_3 ->
          (* We update the recipes of general blocks *)
          let last_ground_index = general_blocks_1.Block.ground_index in
          let (general_blocks_2,_,cur_was_modified) = Block.update_recipes_in_general_block general_blocks_1 in
          (* We remove the constraint systems that are not authorised and
             we link the authorised one with fresh copy *)
          let (forall_set_3,general_blocks_3) =
            auto_cleanup_symbolic_configuration (fun () ->
              link_constraint_systems csys_solved_2;
              instantiate_clean_generate_forall_set true cur_was_modified true last_ground_index general_blocks_2 csys_solved_2
            )
          in

          split_forall_set forall_set_3 (fun forall_set_4 _ f_next_4 ->
            let equiv_pbl_1 =
              { equiv_pbl with
                forall_set = forall_set_4;
                eq_recipe = csys_solved_2.Constraint_system.eq_recipe;
                general_blocks = general_blocks_3;
                public_output_channels = public_output_channels
              }
            in
            f_continuation equiv_pbl_1 f_next_4
          ) f_next_3
        ) csys_solved_1 f_next_2
    ) csys_set f_next_1
  ) f_next

(** Apply all transitions **)

let apply_one_step equiv_pbl f_continuation f_next =

  (*** Cleaning of memory ***)

  Config.debug (fun () ->
    if equiv_pbl.forall_set = []
    then Config.internal_error "[session_equivalence.ml >> apply_one_step] The equivalence problem should not be empty.";

    if select_specified_trace equiv_pbl
    then
      begin
        Config.log_in_debug Config.Process "[session_equivalence.ml] Apply one step";
        Config.log_in_debug Config.Process ("[session_equivalence.ml] "^(display_equivalence_problem equiv_pbl))
      end;
  );

  let one_csys = List.hd equiv_pbl.forall_set in
  let conf = one_csys.Constraint_system.additional_data.configuration in

  if conf.Configuration.output_proc <> []
  then apply_neg_phase equiv_pbl f_continuation f_next
  else
    match conf.Configuration.focused_proc with
      | Some _ -> apply_pos_phase equiv_pbl f_continuation f_next
      | None ->
          match conf.Configuration.input_and_private_proc with
            | [Labelled_process.PStart _] -> apply_start equiv_pbl f_continuation f_next
            | _ ->
                compute_before_focus_phase equiv_pbl;
                apply_focus_phase equiv_pbl f_continuation f_next

(*** Import / Export of equivalence problem ***)

(* The general block and eq_recipe should been fully instantiated when applying this function. *)
let export_equivalence_problem equiv_pbl =
  Config.debug (fun () -> debug_equivalence_problem "[session_equivalence.ml >> export_equivalence_problem]" equiv_pbl);

  let symb_conf_to_update = ref [] in

  let instantiate_csys csys = match csys.Constraint_system.additional_data.link_c with
    | CCsys _ -> ()
    | CNoLink ->
        let csys' = Constraint_system.instantiate csys in
        symb_conf_to_update := csys.Constraint_system.additional_data :: !symb_conf_to_update;
        link_symbolic_configuration csys.Constraint_system.additional_data (CCsys csys')
    | _ -> Config.internal_error "[session_equivalence.ml >> export_equivalence_problem] Unexpected link."
  in

  let get_instantiated_csys csys = match csys.Constraint_system.additional_data.link_c with
    | CCsys csys' -> csys'
    | _ -> Config.internal_error "[session_equivalence.ml >> export_equivalence_problem] Unexpected link 2."
  in

  let equiv_pbl' =
    auto_cleanup_symbolic_configuration (fun () ->
      (* Instantiate the constraint system *)
      let forall_set' =
        List.rev_map (fun csys ->
          instantiate_csys csys;
          List.iter (fun (csys',_) -> instantiate_csys csys') csys.Constraint_system.additional_data.exists_matched;
          get_instantiated_csys csys
        ) equiv_pbl.forall_set
      in

      (* Update the symbolic_configurations *)
      List.iter (fun symb_conf ->
        symb_conf.forall_matched <- List.rev_map get_instantiated_csys symb_conf.forall_matched;
        symb_conf.exists_matched <- List.rev_map (fun (csys,bset) -> get_instantiated_csys csys,bset) symb_conf.exists_matched
      ) !symb_conf_to_update;

      { equiv_pbl with forall_set = forall_set' }
    )
  in

  let recipe_subst =
    List.fold_left (fun acc trans -> match trans with
      | AOutput _
      | AComm _ -> acc
      | AInput(_,RVar v,_) ->
          begin match Recipe.instantiate (RVar v) with
            | RVar v' when v == v' -> acc
            | r -> (v,r)::acc
          end
      | _ -> Config.internal_error "[session_equivalence.ml >> export_equivalence_problem] Unexpected transition."
    ) [] (List.hd equiv_pbl.forall_set).Constraint_system.additional_data.trace
  in


  equiv_pbl', recipe_subst

let import_equivalence_problem f_next equiv_pbl recipe_subst =
  Config.debug (fun () ->  debug_equivalence_problem "[session_equivalence.ml >> import_equivalence_problem]" equiv_pbl);

  let set_up_deducible_name i r t = match t with
    | Name ({ deducible_n = None; _} as n) ->
        Name.set_deducible n (CRFunc(i,r))
    | _ -> ()
  in

  let set_up_csys csys = match csys.Constraint_system.additional_data.link_c with
    | CNoLink ->
        Data_structure.K.iteri set_up_deducible_name csys.Constraint_system.knowledge;
        Data_structure.IK.iteri set_up_deducible_name csys.Constraint_system.incremented_knowledge;
        link_symbolic_configuration csys.Constraint_system.additional_data CSearch
    | CSearch -> ()
    | _ -> Config.internal_error "[session_equivalence.ml >> import_equivalence_problem] Unexpected link."
  in

  Recipe_Variable.auto_cleanup_with_reset_notail (fun () ->
    (* We link the recipe substitution *)
    List.iter (fun (x,r) -> Recipe_Variable.link_recipe x r) recipe_subst;

    (* Set up the deducible names *)

    Name.auto_deducible_cleanup_with_reset_notail (fun () ->
      auto_cleanup_symbolic_configuration (fun () ->
        List.iter (fun csys ->
          set_up_csys csys;
          List.iter (fun (csys',_) -> set_up_csys csys') csys.Constraint_system.additional_data.exists_matched
        ) equiv_pbl.forall_set;
      );

      f_next ()
    )
  )
