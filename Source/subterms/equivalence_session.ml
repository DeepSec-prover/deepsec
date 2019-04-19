open Term
open Display
open Process_session


type transition = {
  label : label;
  forall : bool;
}

type status = ForAll | Exists | Both

type constraint_system = symbolic_process Constraint_system.t
and constraint_system_set = symbolic_process Constraint_system.Set.t
and symbolic_process = {
  origin_process : side;
  conf : configuration;
  mutable next_transition : (transition * configuration) list option;
  status : status
}

type matching =
  (symbolic_process * (symbolic_process * bijection_set) list) list



type partition_tree_node = {
  csys_set : constraint_system_set;
  matching : matching;
  previous_blocks : block list;
  ongoing_block : block;
  size_frame : int
}

let init_partition_tree (csys_set:symbolic_process Constraint_system.Set.t) (m:matching) : partition_tree_node = {
  csys_set = csys_set;
  matching = m;
  previous_blocks = [];
  ongoing_block = create_block initial_label;
  size_frame = 0
}


type result_analysis =
  | Equivalent
  | Not_Equivalent of constraint_system

exception Not_Session_Equivalent of constraint_system


(* a type to model the result of skeleton checks *)
type skeleton_check =
  | OK of configuration * configuration * bijection_set
  | Faulty of side * configuration * action
  | Improper

let normalise_before_starting (node:partition_tree_node) (f_cont:partition_tree_node->(unit->unit)->'a) (f_next:unit->unit) : unit =

  (** normalisation of the configurations **)
  let initial_csys_set = ref Constraint_system.Set.empty in
  Constraint_system.Set.iter (fun csys ->
    let symb_proc = Constraint_system.get_additional_data csys in
    let eqn = Constraint_system.get_substitution_solution Protocol csys in

    normalise_configuration symb_proc.conf eqn (fun gathering conf ->
      try
        let csys_1 =
          Constraint_system.apply_substitution csys gathering.equations in
        let csys_2 =
          Constraint_system.add_disequations csys_1 gathering.disequations in
        let csys_3 =
          Constraint_system.replace_additional_data csys_2 {symb_proc with conf = conf} in

        initial_csys_set := Constraint_system.Set.add csys_3 !initial_csys_set
      with
        | Constraint_system.Bot -> ()
    )
  ) node.csys_set;
  let initial_csys_set = !initial_csys_set in (* to get rid of the reference *)


  (** Resolution of the constraints using the constraint solver **)

  let in_apply_final_test csys_set f_next =
    if Constraint_system.Set.is_empty csys_set then f_next ()
    else
      let csys_set_1 =
        Constraint_system.Set.optimise_snd_ord_recipes csys_set in
      let csys = Constraint_system.Set.choose csys_set_1 in
      Config.debug (fun () ->
        let same_origin csys1 csys2 =
          (Constraint_system.get_additional_data csys1).origin_process = (Constraint_system.get_additional_data csys2).origin_process in
        if Constraint_system.Set.for_all (same_origin csys) csys_set_1 then
          Config.internal_error "[equivalence_session.ml >> in_apply_final_test] Unexpected case, equivalence should not be violated after only normalising the two processes."
      );
      let (csys_left, csys_right) =
        Constraint_system.Set.find_representative csys_set (fun csys' ->
          (Constraint_system.get_additional_data csys').origin_process = Left
        ) in
      let sleft = Constraint_system.get_additional_data csys_left in
      let sright = Constraint_system.get_additional_data csys_right in
      let bs_init = void_bijection_set in

      (** skeleton test **)
      let skel_test =
        try
          let (cf_right,bs_upd) =
            check_skeleton_in_configuration 0 sleft.conf sright.conf bs_init in
          try
            let cf_left = release_skeleton_without_check sleft.conf in
            OK(cf_left,cf_right,bs_upd)
          with Improper_block -> Improper
        with Faulty_skeleton(side,conf,action) -> Faulty(side,conf,action) in

      (** final operations depending on the result of the test **)
      match skel_test with
      | Improper -> f_next ()
      | OK (conf_left, conf_right,bset) ->
        let csys_left =
          Constraint_system.replace_additional_data csys_left {sleft with conf = conf_left } in
        let csys_right =
          Constraint_system.replace_additional_data csys_right {sright with conf = conf_right} in
        let csys_set_upd =
          Constraint_system.Set.of_list [csys_left; csys_right] in
        let node_upd =
          { node with csys_set = csys_set_upd } in
        f_cont node_upd f_next
      | Faulty (side,f_conf,f_action) ->
        let (wit_csys, symb_proc) =
          if side = Left then csys_left, sleft
          else csys_right, sright in
        let eqn =
          Constraint_system.get_substitution_solution Protocol wit_csys in
        begin match f_action with
        | OutAction(_,ax,t) ->
          let wit_csys_1 =
            Constraint_system.add_axiom wit_csys ax (Subst.apply eqn t (fun x f -> f x)) in
          let wit_csys_2 =
            Constraint_system.replace_additional_data wit_csys_1 { symb_proc with conf = f_conf } in
          raise (Not_Session_Equivalent wit_csys_2)
        | InAction(_,var_X,t) ->
          let ded_fact_term = BasicFact.create var_X t in
          let wit_csys_1 =
            Constraint_system.add_basic_fact wit_csys ded_fact_term in
          let wit_csys_2 =
            Constraint_system.replace_additional_data wit_csys_1 { symb_proc with conf = f_conf } in
          raise (Not_Session_Equivalent wit_csys_2)
        end
  in

  Constraint_system.Rule.apply_rules_after_input false in_apply_final_test initial_csys_set f_next



let equivalence_by_session (conf1:configuration) (conf2:configuration) : result_analysis =

  (* Initialisation of the rewrite system *)

  Rewrite_rules.initialise_skeletons ();
  Data_structure.Tools.initialise_constructor ();

  (* Generate the initial constraint systems
  TODO. Introduce factorisation. *)

  let sp1 = {
    origin_process = Left;
    conf = clean_inital_configuration conf1;
    next_transition = None;
    status = Both;
  } in
  let sp2 = {
    origin_process = Right;
    conf = clean_inital_configuration conf2;
    next_transition = None;
    status = Both;
  } in
  let csys_set_0 =
    Constraint_system.Set.of_list [
      Constraint_system.empty sp1;
      Constraint_system.empty sp2;
    ] in
  let node0 =
    init_partition_tree csys_set_0 [todo] in

  todo
