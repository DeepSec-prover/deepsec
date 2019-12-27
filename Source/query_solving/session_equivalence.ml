(* Process manipulation for equivalence by session *)
open Extensions
open Types
open Term
open Formula
open Session_process

type permutation =
  {
    prefix_forall : int list;
    prefix_exists : int list;
    perm_matching : (int list (* forall *)* int list (* exists*)) list
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

    (* Computed datas *)
    mutable link_c : configuration_link;
    mutable transition_data : session_transition
  }

and configuration_link =
  | CNoLink
  | CCsys of symbolic_configuration Constraint_system.t
  | CSplit
  | CTransition of generate_transition
  | CChannelPriority of Configuration.channel_priority

and session_transition =
  | TransNone
  | TransOutput of Configuration.output_transition
  | TransInComm of Configuration.input_and_comm_transition

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

  let rec extract_one_permutation prefix prev_list = function
    | [] -> Config.internal_error "[session_equivalence.ml >> Bijection_set.extract_one_permutation] The label should occurs."
    | perm::q ->
        if prefix = perm.prefix_forall
        then perm, List.rev_append prev_list q
        else extract_one_permutation prefix (perm::prev_list) q

  let generate_for_comm forall_comm_trans bset =

    let (forall_label_out,forall_label_in) = forall_comm_trans.Configuration.comm_out_label, forall_comm_trans.Configuration.comm_in_label in
    let (forall_skel_out,forall_skel_in) = forall_comm_trans.Configuration.comm_out_skeletons, forall_comm_trans.Configuration.comm_in_skeletons in

    if forall_label_out.Label.prefix = forall_label_in.Label.prefix
    then
      let (perm,bset1) = extract_one_permutation forall_label_out.Label.prefix [] bset in
      let (forall_out',exists_out,perm_matching_1) = extract_matching forall_label_out.Label.last_index [] perm.perm_matching in
      let (forall_in',exists_in,per_matching_2) = extract_matching forall_label_in.Label.last_index [] perm_matching_1 in

      let gen_bset exists_comm_trans =
        let (exists_label_out,exists_label_in) = exists_comm_trans.Configuration.comm_out_label, exists_comm_trans.Configuration.comm_in_label in
        let (exists_skel_out,exists_skel_in) = exists_comm_trans.Configuration.comm_out_skeletons, exists_comm_trans.Configuration.comm_in_skeletons in

        if exists_label_out.Label.prefix = exists_label_in.Label.prefix && exists_label_out.Label.prefix = perm.prefix_exists
        then
          match extract_sub_matching exists_label_out.Label.last_index [] exists_out with
            | None -> None
            | Some exists_out' ->
                match extract_sub_matching exists_label_in.Label.last_index [] exists_in with
                  | None -> None
                  | Some exists_in' ->
                      if Labelled_process.is_equal_skeletons forall_skel_out exists_skel_out &&
                        Labelled_process.is_equal_skeletons forall_skel_in exists_skel_in
                      then
                        match forall_skel_out.Labelled_process.par_created, forall_skel_in.Labelled_process.par_created with
                          | true,true ->
                              let old_perm = { perm with perm_matching = (forall_out',exists_out')::(forall_in',exists_in') :: perm_matching_2 } in
                              let new_perm_out =
                                {
                                  prefix_forall = forall_skel_out.Labelled_process.label_prefix;
                                  prefix_exists = exists_skel_out.Labelled_process.label_prefix;
                                  perm_matching = perm_matching_of_skeleton forall_skel_out exists_skel_out
                                }
                              in
                              let new_perm_in =
                                {
                                  prefix_forall = forall_skel_in.Labelled_process.label_prefix;
                                  prefix_exists = exists_skel_in.Labelled_process.label_prefix;
                                  perm_matching = perm_matching_of_skeleton forall_skel_in exists_skel_in
                                }
                              in
                              Some(new_perm_in::new_perm_out::old_perm::bset1)
                          | true,_ ->
                              let new_perm = { perm with perm_matching = ([forall_label.Label.last_index],[exists_label.Label.last_index])::(forall_m',exists_m')::perm_matching } in
                              Some (new_perm::bset1)



                      else None
        else None




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

  (*** Utilities ***)

  let rec extract_permutation forall_label prev_bset = function
    | [] -> Config.internal_error "[session_equivalence.ml >> Bijection_set.extract_permuation] The label should occurs."
    | perm::q ->
        if forall_label.Label.prefix = perm.prefix_forall
        then perm, List.rev_append prev_bset q
        else extract_permutation forall_label (perm::prev_bset) q

  let rec extract_sub_matching (i_target:int) prev_list = function
    | [] -> None
    | i::q ->
        match compare i i_target with
          | 0 -> Some (List.rev_append prev_list q)
          | 1 -> None
          | _ -> extract_sub_matching i_target (i::prev_list) q

  let rec extract_matching i_target (prev_matching:(int list * int list) list) = function
    | [] -> Config.internal_error "[session_equivalence.ml >> Bijection_set.extract_matching] Unexpected case."
    | (forall_m,exists_m) as t::q ->
        match extract_sub_matching i_target [] forall_m with
          | None -> extract_matching i_target (t::prev_list) q
          | Some forall_m' -> forall_m', exists_m, List.rev_append prev_list q

  let rec update_from_extract forall_skel_matching_list exists_skel_matching_list bset perm_matching = match forall_skel_matching_list,exists_skel_matching_list with
    | [], [] ->


end

let iter_forall_both f gen_trans =
  List.iter f gen_trans.gt_both;
  List.iter f gen_trans.gt_forall

let iter_exists_both f gen_trans =
  List.iter f gen_trans.gt_both;
  List.iter f gen_trans.gt_exists

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
          conf.link_c <- CSplit;
          marked_conf := conf::!marked_conf;
          List.iter mark conf.forall_matched;
          List.iter (fun (csys',_) -> mark csys') conf.exists_matched
      | _ -> ()
  in

  let rec explore csys_list_1 f_next_1 = match csys_list_1 with
    | [] -> f_next_1 ()
    | csys::q ->
        mark csys;
        let (marked,not_marked) = List.partition_unordered (fun csys' -> csys'.Constraint_system.additional_data.link_c = CSplit) q in
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
  symb.link_c <- link;
  linked_symbolic_configuration := symb :: !linked_symbolic_configuration

let link_symbolic_configuration_with_csys symb csys =
  symb.link_c <- CCsys csys;
  linked_symbolic_configuration := symb :: !linked_symbolic_configuration

let link_symbolic_configuration_with_transitions symb trans =
  symb.link_c <- CTransition trans;
  linked_symbolic_configuration := symb :: !linked_symbolic_configuration

let link_constraint_systems csys_solved =
  List.iter (fun csys ->
    let symb_conf = csys.Constraint_system.additional_data in
    let symb_conf' =
      { symb_conf with
        forall_matched = [];
        exists_matched = [];
        link_c = CNoLink
      }
    in
    let csys' = { csys with Constraint_system.additional_data = symb_conf' } in
    link_symbolic_configuration_with_csys symb_conf csys'
  ) csys_solved.Constraint_system.set

let generate_matching_status forall_matched exists_match = match forall_matched, exists_match with
  | [],_ -> Configuration.ForAll
  | _,[] -> Configuration.Exists
  | _ -> Configuration.Both

let instantiate_clean_generate_forall_set last_ground_index general_blocks csys_solved =
  List.fold_left (fun acc old_csys -> match old_csys.Constraint_system.additional_data.link_c with
    | CCsys new_csys ->
        let new_symb_conf = new_csys.Constraint_system.additional_data in
        let old_symb_conf = old_csys.Constraint_system.additional_data in
        let new_forall_matched =
          List.fold_left (fun acc' old_csys' -> match old_csys'.Constraint_system.additional_data.link_c with
            | CCsys new_csys' -> new_csys'::acc'
            | _ -> acc'
          ) [] old_symb_conf.forall_matched
        in

        let new_exists_matched = ref [] in

        begin
          if old_symb_conf.exists_matched <> []
          then
            if Block.is_authorised last_ground_index general_blocks new_symb_conf.configuration.Configuration.blocks
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
                new_symb_conf.matching_status <- generate_matching_status new_forall_matched new_exists_matched_1;
                new_exists_matched := new_exists_matched_1
              end
            else new_symb_conf.matching_status <- generate_matching_status new_forall_matched []
          else new_symb_conf.matching_status <- generate_matching_status new_forall_matched []
        end;

        new_symb_conf.forall_matched <- new_forall_matched;
        new_symb_conf.exists_matched <- !new_exists_matched;

        if !new_exists_matched = []
        then acc
        else new_csys::acc
    | _ -> Config.internal_error "[session_equivalence.ml >> instantiate_clean_generate_forall_set] All constraint system should be linked."
  ) [] csys_solved.Constraint_system.set

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

(** Application of transitions **)

let apply_neg_phase equiv_pbl f_continuation f_next =
  Config.debug (fun () ->
    if equiv_pbl.forall_set = []
    then Config.internal_error "[session_equivalence.ml >> apply_public_output] The set of constraint system should not be empty.";
    if equiv_pbl.public_output_channels = []
    then Config.internal_error "[session_equivalence.ml >> apply_public_output] The function should only be applied when there are public channels.";
  );

  let is_in_improper_phase = equiv_pbl.general_blocks.Block.current_recipe_block = None in
  let generate_next_public_output =
    if is_in_improper_phase
    then Configuration.next_public_output_improper_phase
    else Configuration.next_public_output
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
          link_symbolic_configuration_with_transitions symb_conf gen_trans;
          gen_trans
      | CTransition gen_trans -> gen_trans
      | _ -> Config.internal_error "[session_equivalence.ml >> apply_public_output] Unexpected link during generation of transitions."
  in

  (* Generate the new matching set *)

  let forall_set_1 = ref [] in

  auto_cleanup_symbolic_configuration (fun () ->
    List.iter (fun forall_csys ->
      let gen_forall_transitions = generate_transitions forall_csys in
      List.iter (fun (exists_csys,bset) ->
        let gen_exists_transitions = generate_transitions exists_csys in

        (* Generate the matching *)
        iter_forall_both (fun forall_csys_1 ->
          let forall_trans = match forall_csys_1.Constraint_system.additional_data.transition_data with
            | TransOutput trans -> trans
            | _ -> Config.internal_error "[session_equivalence.ml >> apply_public_out] Expecting an output transition."
          in
          let generate_bset = Bijection_set.generate forall_trans.Configuration.out_label forall_trans.Configuration.out_gathering_skeleton bset in
          iter_exists_both (fun exists_csys_1 ->
            let exists_trans = match exists_csys_1.Constraint_system.additional_data.transition_data with
              | TransOutput trans -> trans
              | _ -> Config.internal_error "[session_equivalence.ml >> apply_public_out] Expecting an output transition (2)."
            in
            match generate_bset exists_trans.Configuration.out_label exists_trans.Configuration.out_gathering_skeleton with
              | None -> ()
              | Some bset1 ->
                  exists_csys_1.Constraint_system.additional_data.forall_matched <- forall_csys_1 :: exists_csys_1.Constraint_system.additional_data.forall_matched;
                  forall_csys_1.Constraint_system.additional_data.exists_matched <- (exists_csys_1,bset1) :: forall_csys_1.Constraint_system.additional_data.exists_matched
          ) gen_exists_transitions;
          forall_set_1 := forall_csys_1 :: !forall_set_1
        ) gen_forall_transitions
      ) forall_csys.Constraint_system.additional_data.exists_matched;
    ) equiv_pbl.forall_set;
  );

  (* Apply the first split *)

  split_forall_set !forall_set_1 (fun forall_set_2 csys_to_solve f_next_1 ->
    (* We first calculate the new public_output_channels and we check if we can determine whether
       the current block is surely proper. *)
    let (public_output_channels,general_blocks_1) =
      let csys = List.hd forall_set_2 in
      match csys.Constraint_system.additional_data.transition_data with
        | TransOutput trans ->
            let general_blocks =
              if trans.Configuration.out_gathering_skeleton.Labelled_process.input_skel = [] && trans.Configuration.out_gathering_skeleton.Labelled_process.private_channels = []
              then equiv_pbl.general_blocks
              else { equiv_pbl.general_blocks with Block.current_block_sure_proper = true }
            in
            let pub_output = Configuration.update_public_output_channel_from_output_transition target_ch equiv_pbl.public_output_channels trans.Configuration.out_gathering_skeleton in
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
                let general_blocks_2 = Block.update_recipes_in_general_block general_blocks_2 in

                (* We remove the constraint systems that are not authorised and
                   we link the authorised one with fresh copy *)
                let forall_set_3 =
                  auto_cleanup_symbolic_configuration (fun () ->
                    link_constraint_systems csys_solved_2;
                    instantiate_clean_generate_forall_set last_ground_index general_blocks_2 csys_solved_2
                  )
                in

                split_forall_set forall_set_3 (fun forall_set_4 _ f_next_4 ->
                  let equiv_pbl_1 =
                    {
                      size_frame = equiv_pbl.size_frame + 1;
                      forall_set = forall_set_4;
                      eq_recipe = csys_solved_2.Constraint_system.eq_recipe;
                      general_blocks = general_blocks_2;
                      public_output_channels = public_output_channels
                    }
                  in
                  f_continuation equiv_pbl_1 f_next_4
                ) f_next_3
        ) csys_solved_1 f_next_2
    ) csys_set f_next_1
  ) f_next

(* We assume that the last current block has already been closed. *)
let apply_focus_phase equiv_pbl f_continuation f_next =
  Config.debug (fun () ->
    if equiv_pbl.forall_set = []
    then Config.internal_error "[session_equivalence.ml >> apply_focus_output] The set of constraint system should not be empty.";
    if equiv_pbl.public_output_channels <> []
    then Config.internal_error "[session_equivalence.ml >> apply_focus_output] The function should only be applied when there are no public channels.";
  );

  let is_in_improper_phase = equiv_pbl.general_blocks.Block.current_recipe_block = None in
  let only_private =
    if is_in_improper_phase
    then false
    else determine_channel_priority equiv_pbl.forall_set
  in

  let generate_next_public_input_comm_nolink  =
    if is_in_improper_phase
    then Configuration.next_input_and_private_comm_improper_phase
    else
      if only_private
      then Configuration.next_input_and_private_comm Configuration.ChOnlyPrivate
      else Configuration.next_input_and_private_comm Configuration.ChNone
  in

  let type_max =
    let csys = List.hd equiv_pbl.forall_set in
    (Data_structure.IK.get_max_type_recipe csys.Constraint_system.knowledge csys.Constraint_system.incremented_knowledge)
  in
  let var_X_t = Recipe_Variable.fresh Free type_max in

  let generate_transitions csys =
    let symb_conf = csys.Constraint_system.additional_data in
    let generate_next_public_input_comm = match symb_conf.link_c with
      | CChannelPriority ch -> Configuration.next_input_and_private_comm ch
      | _ -> generate_next_public_input_comm_nolink
    in
    match symb_conf.link_c with
      | CNoLink | CChannelPriority _ ->
          let transitions_forall = ref [] in
          let transitions_exists = ref [] in
          let transitions_both = ref [] in

          Variable.auto_cleanup_with_reset_notail (fun () ->
            List.iter (fun (x,t) -> Variable.link_term x t) csys.Constraint_system.original_substitution;
            List.iter (fun (x,n) -> Variable.link_term x (Name n)) csys.Constraint_system.original_names;

            generate_next_public_input_comm symb_conf.matching_status csys.Constraint_system.original_substitution csys.Constraint_system.original_names symb_conf.configuration (fun in_comm_trans conf_1 ->
              let eq_uniformity = Formula.T.instantiate_and_normalise_full csys.Constraint_system.eq_uniformity in
              if eq_uniformity = Formula.T.Bot
              then ()
              else
                match in_comm_trans.Configuration.in_comm_type with
                  | TInput in_trans ->
                      let symb_conf_1 =
                        { symb_conf with
                          configuration = conf_1;
                          matching_status = in_comm_trans.Configuration.in_comm_matching_status;
                          trace = AInput(in_trans.Configuration.in_channel,RVar var_X_t,in_trans.Configuration.in_position) :: symb_conf.trace;
                          transition_data = TransInComm in_comm_trans;
                          link_c = CNoLink;
                          forall_matched = [];
                          exists_matched = []
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
                      let csys_2 = Constraint_system.prepare_for_solving_procedure true csys_1 in

                      begin match in_comm_trans.Configuration.in_comm_matching_status with
                        | Configuration.Exists -> transitions_exists := csys_2::!transitions_exists
                        | Configuration.ForAll -> transitions_forall := csys_2::!transitions_forall
                        | Configuration.Both -> transitions_both := csys_2::!transitions_both
                      end
                  | TComm comm_trans ->
                      let symb_conf_1 =
                        { symb_conf with
                          configuration = conf_1;
                          matching_status = in_comm_trans.Configuration.in_comm_matching_status;
                          trace = AComm(comm_trans.Configuration.comm_out_position,comm_trans.Configuration.comm_in_position) :: symb_conf.trace;
                          transition_data = TransInComm in_comm_trans;
                          link_c = CNoLink;
                          forall_matched = [];
                          exists_matched = []
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
                      let csys_2 = Constraint_system.prepare_for_solving_procedure true csys_1 in

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
              gt_exists = clean_variables_names!transitions_exists;
              gt_both = clean_variables_names !transitions_both
            }
          in
          link_symbolic_configuration_with_transitions symb_conf gen_trans;
          gen_trans
      | CTransition gen_trans -> gen_trans
      | _ -> Config.internal_error "[session_equivalence.ml >> apply_public_output] Unexpected link during generation of transitions."
  in

  (* Generate the new matching set *)

  let forall_set_1 = ref [] in

  auto_cleanup_symbolic_configuration (fun () ->
    List.iter (fun forall_csys ->
      let gen_forall_transitions = generate_transitions forall_csys in
      List.iter (fun (exists_csys,bset) ->
        let gen_exists_transitions = generate_transitions exists_csys in

        (* Generate the matching *)
        iter_forall_both (fun forall_csys_1 ->
          let forall_trans = match forall_csys_1.Constraint_system.additional_data.transition_data with
            | TransInComm trans -> trans
            | _ -> Config.internal_error "[session_equivalence.ml >> apply_focus_phase] Expecting an output transition."
          in
          let generate_bset = Bijection_set.generate forall_trans.Configuration.in_comm_label forall_trans.Configuration.out_gathering_skeleton bset in
          iter_exists_both (fun exists_csys_1 ->
            let exists_trans = match exists_csys_1.Constraint_system.additional_data.transition_data with
              | TransOutput trans -> trans
              | _ -> Config.internal_error "[session_equivalence.ml >> apply_focus_phase] Expecting an output transition (2)."
            in
            match generate_bset exists_trans.Configuration.out_label exists_trans.Configuration.out_gathering_skeleton with
              | None -> ()
              | Some bset1 ->
                  exists_csys_1.Constraint_system.additional_data.forall_matched <- forall_csys_1 :: exists_csys_1.Constraint_system.additional_data.forall_matched;
                  forall_csys_1.Constraint_system.additional_data.exists_matched <- (exists_csys_1,bset1) :: forall_csys_1.Constraint_system.additional_data.exists_matched
          ) gen_exists_transitions;
          forall_set_1 := forall_csys_1 :: !forall_set_1
        ) gen_forall_transitions
      ) forall_csys.Constraint_system.additional_data.exists_matched;
    ) equiv_pbl.forall_set;
  );

  ()
