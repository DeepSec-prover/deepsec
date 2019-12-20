(* Process manipulation for equivalence by session *)
open Extensions
open Types
open Term
open Formula
open Session_process

type bijection_permutation =
  {
    prefix_forall : int list;
    prefix_exists : int list;
    perm_matching : (int list (* forall *)* int list (* exists*)) list
      (* The lists inside the perm_matching are ordered *)
  }

type bijection_set = bijection_permutation list

type symbolic_configuration =
  {
    (* Main data *)
    origin : bool;
    configuration : Configuration.t;
    matching_status : Configuration.matching_status;
    trace : transition list;

    mutable forall_matched : symbolic_configuration Constraint_system.t list;
      (* When matching status is Exists or Both, the list [forall_matched] indicates the configuration
         with tag ForAll or Both that have this configuration has Exists]*)

    mutable exists_matched : (symbolic_configuration Constraint_system.t * bijection_set) list;
      (* When matching status is ForAll or Both, the list [exists_matched] indicates the configuration
         with tag Exists or Both that have this configuration has Forall]*)

    (* Computed datas *)
    mutable link_c : configuration_link;
    mutable transitions : generate_transition option;
    mutable transition_data : transition_data
  }

and configuration_link =
  | CNoLink
  | CCsys of symbolic_configuration Constraint_system.t
  | CSplit

and transition_data =
  | TNone
  | TOutput of Channel.t * Labelled_process.gathering_skeletons

and session_transition =
  | TransOutput of Configuration.output_transition
  | TransInComm of Configuration.input_and_comm_transition

and generate_transition =
  {
    gt_both : (session_transition * symbolic_configuration Constraint_system.t) list;
    gt_forall : (session_transition * symbolic_configuration Constraint_system.t) list;
    gt_exists : (session_transition * symbolic_configuration Constraint_system.t) list
  }

type equivalence_problem =
  {
    size_frame : int;
    matching_set : (symbolic_configuration Constraint_system.t * (symbolic_configuration Constraint_system.t * bijection_set) list) list;
    public_output_channels : (Channel.t * int) list (* Ordered by Channel.compare *)
  }

module Bijection_set = struct

  let rec extract_sub_matching (i_target:int) prev_list = function
    | [] -> None
    | i::q ->
        match compare i i_target with
          | 0 -> Some (List.rev_append prev_list q)
          | 1 -> None
          | _ -> extract_sub_matching i_target (i::prev_list) q

  let perm_matching_of_skeleton forall_skel exists_skel =
    let perm_matching = ref [] in

    List.iter2 (fun (_,_,l1) (_,_,l2) -> perm_matching := (l1,l2)::!perm_matching) forall_skel.Labelled_process.input_skel exists_skel.Labelled_process.input_skel;
    List.iter2 (fun (_,_,l1) (_,_,l2) -> perm_matching := (l1,l2)::!perm_matching) forall_skel.Labelled_process.output_skel exists_skel.Labelled_process.output_skel;
    perm_matching := (snd forall_skel.Labelled_process.private_input_skel,snd exists_skel.Labelled_process.private_input_skel)::!perm_matching;
    perm_matching := (snd forall_skel.Labelled_process.private_output_skel, snd exists_skel.Labelled_process.private_output_skel)::!perm_matching;

    !perm_matching

  let generate forall_label forall_skel bset =

    let rec extract_matching (prev_list:(int list * int list) list) = function
      | [] -> Config.internal_error "[session_equivalence.ml >> Bijection_set.extract_permutation] Unexpected case."
      | (forall_m,exists_m) as t::q ->
          match extract_sub_matching forall_label.Label.last_index [] forall_m with
            | None -> extract_matching (t::prev_list) q
            | Some forall_m' -> forall_m', exists_m, List.rev_append prev_list q
    in

    let rec explore prev_list = function
      | [] -> Config.internal_error "[session_equivalence.ml >> Bijection_set.extract_permutation] The label should occurs."
      | perm::q ->
          if forall_label.Label.prefix = perm.prefix_forall
          then perm, List.rev_append prev_list q
          else explore (perm::prev_list) q
    in

    let (perm,bset1) = explore [] bset in
    let (forall_m',exists_m,perm_matching) = extract_matching [] perm.perm_matching in

    if forall_skel.Labelled_process.par_created
    then
      let gen_bset exists_label exists_skel =
        if exists_skel.Labelled_process.par_created && exists_label.Label.prefix = perm.prefix_exists
        then
          match extract_sub_matching exists_label.Label.last_index [] exists_m with
            | None -> None
            | Some exists_m' ->
                if Labelled_process.is_equal_skeletons forall_skel exists_skel
                then
                  let old_perm = { perm with perm_matching = (forall_m',exists_m')::perm_matching } in
                  let new_perm =
                    {
                      prefix_forall = forall_skel.Labelled_process.label_prefix;
                      prefix_exists = exists_skel.Labelled_process.label_prefix;
                      perm_matching = perm_matching_of_skeleton forall_skel exists_skel
                    }
                  in
                  Some (new_perm::old_perm::bset1)
                else None
        else None
      in
      gen_bset
    else
      let gen_bset exists_label exists_skel =
        if not (exists_skel.Labelled_process.par_created) && exists_label.Label.prefix = perm.prefix_exists
        then
          match extract_sub_matching exists_label.Label.last_index [] exists_m with
            | None -> None
            | Some exists_m' ->
                if Labelled_process.is_equal_skeletons forall_skel exists_skel
                then
                  let new_perm = { perm with perm_matching = ([forall_label.Label.last_index],[exists_label.Label.last_index])::(forall_m',exists_m')::perm_matching } in
                  Some (new_perm::bset1)
                else None
        else None
      in
      gen_bset
end

(** Split of extended matching set **)
(*
let split_extended_matching_set matching_set f_continuation f_next =

  let rec mark_configuration csys =
    if csys.Constraint_system.additional_data.split_not_marked
    then
      begin
        csys.Constraint_system.additional_data.split_not_marked <- false;
        List.iter (mark_configuration i) conf.forall_matched;
        List.iter (mark_configuration i) conf.exists_matched;
        conf.forall_matched <- [];
        conf.exists_matched <- []
      end
  in

  let rec explore_matching_set m_set i f_next_1 = match m_set with
    | [] -> f_next_1
    | (forall_skel,forall_csys,exists_matching_set)::q ->
        mark_configuration i forall_csys;



(** Application of transitions **)

let apply_public_output equiv_pbl f_continuation f_next =
  Config.debug (fun () ->
    if equiv_pbl.matching_set = []
    then Config.internal_error "[session_equivalence.ml >> apply_public_output] The matching set should not be empty.";
    if equiv_pbl.public_output_channels = []
    then Config.internal_error "[session_equivalence.ml >> apply_public_output] The function should only be applied when there are public channels.";
  );

  let target_ch = fst (List.hd equiv_pbl.public_output_channels) in
  let target_ch_recipe = Channel.recipe_of target_ch in

  let axiom = equiv_pbl.size_frame + 1 in

  let generate_transitions csys =
    let symb_conf = csys.Constraint_system.additional_data in
    match symb_conf.transitions with
      | None ->
          let transitions_forall = ref [] in
          let transitions_exists = ref [] in

          Variable.auto_cleanup_with_reset_notail (fun () ->
            List.iter (fun (x,t) -> Variable.link_term x t) csys.Constraint_system.original_substitution;
            List.iter (fun (x,n) -> Variable.link_term x (Name n)) csys.Constraint_system.original_names;

            Configuration.next_public_output symb_conf.matching_status target_ch csys.Constraint_system.original_substitution csys.Constraint_system.original_names symb_conf.configuration (fun out_trans conf_1 ->
              let eq_uniformity = Formula.T.instantiate_and_normalise_full csys.Constraint_system.eq_uniformity in
              if eq_uniformity = Formula.T.Bot
              then ()
              else
                let symb_conf_1 =
                  { symb_conf with
                    configuration = conf_1;
                    matching_status = out_trans.Configuration.out_matching_status;
                    trace = AOutput(target_ch_recipe,out_trans.Configuration.out_position) :: symb_conf.trace;
                    channel_priority = Configuration.ChNone;
                    transitions = None;
                    split_not_marked = true;
                    forall_matched = [];
                    exists_matched = []
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

                let session_transition = TransOutput out_trans in

                if out_trans.Configuration.out_matching_status = Configuration.Exists
                then transitions_exists := (session_transition,csys_3)::!transitions_exists
                else transitions_forall := (session_transition,csys_3)::!transitions_forall
            )
          );

          (** TODO: Include the cleaning of variables and names in the constraint systems. *)
          let gen_trans = { gt_forall = !transitions_forall; gt_exists = !transitions_exists } in
          symb_conf.transitions <- Some gen_trans;
          gen_trans
      | Some gen_trans -> gen_trans
  in

  (* Generate the new matching set *)

  let new_matching_set = ref [] in

  List.iter (fun (forall_csys,exists_match) ->
    let gen_forall_transitions = generate_transitions forall_csys in
    List.iter (fun (exists_csys,bset) ->
      let gen_exists_transitions = generate_transitions exists_csys in

      (* Generate the matching *)
      List.iter (fun (forall_sess_trans,forall_csys_1) ->
        let forall_trans = match forall_sess_trans with
          | TransOutput trans -> trans
          | _ -> Config.internal_error "[session_equivalence.ml >> apply_public_out] Expecting an output transition."
        in
        let generate_bset = Bijection_set.generate forall_trans.Configuration.out_label forall_trans.Configuration.out_gathering_skeleton bset in
        let exists_matching_set = ref [] in
        List.iter (fun (exists_sess_trans,exists_csys_1) ->
          let exists_trans = match exists_sess_trans with
            | TransOutput trans -> trans
            | _ -> Config.internal_error "[session_equivalence.ml >> apply_public_out] Expecting an output transition (2)."
          in
          match generate_bset exists_trans.Configuration.out_label exists_trans.Configuration.out_gathering_skeleton with
            | None -> ()
            | Some bset1 ->
                exists_matching_set := (exists_csys_1,bset1) :: !exists_matching_set;
                exists_csys_1.Constraint_system.additional_data.forall_matched <- forall_csys_1.Constraint_system.additional_data :: exists_csys_1.Constraint_system.additional_data.forall_matched;
                forall_csys_1.Constraint_system.additional_data.exists_matched <- exists_csys_1.Constraint_system.additional_data :: forall_csys_1.Constraint_system.additional_data.exists_matched
        ) gen_exists_transitions.gt_exists;
        new_matching_set := (forall_trans.Configuration.out_gathering_skeleton,forall_csys_1,!exists_matching_set) :: !new_matching_set
      ) gen_forall_transitions.gt_forall
    ) exists_match;
  ) equiv_pbl.matching_set;

*)
