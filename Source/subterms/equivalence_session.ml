open Extensions
open Term
open Process_session
open Display

type optimisation_parameters = bool

let optimisation_parameters = ref true

let get_optimisation_parameters () = !optimisation_parameters
let set_up_optimisation_parameters param = optimisation_parameters := param

let initialise_optimisation_parameters conf1 conf2 =
  optimisation_parameters :=
    (Configuration.contain_only_public_channel conf1) &&
    (Configuration.contain_only_public_channel conf2)

(* a module for representing symbolic processes (process with symbolic variables and constraint systems). Sets of symbolic processes are represented as mutable tables with indexes *)
module Symbolic = struct
  (* abstraction of integer indexes *)
  module Index = struct
    type t = int
    let to_string = string_of_int
  end

  module Status = struct
    type t =
      | ForAll
      | Exists
      | Both
    let init_for_equivalence = Both
    let init_for_inclusion_left = ForAll
    let init_for_inclusion_right = Exists
    let downgrade_forall (s:t) (forall:bool) : t =
      if forall then s else Exists
    let print (s:t) : unit =
      print_string (match s with
        | ForAll -> "A"
        | Exists -> "E"
        | Both -> "AE"
      )

    let display out s = match s with
      | ForAll -> forall out
      | Exists -> exists out
      | Both -> (forall out)^(exists out)
  end

  type transition_type =
    | In
    | Out
    | Comm
  type transition = {
    target : Index.t;
    skel_target : Labelled_process.Skeleton.t one_or_two;
    label : Label.t one_or_two;
    forall : bool;
    type_of : transition_type;
  }

  module Process = struct
    type process = {
      origin : string;
      conf : Configuration.t;
      next_transitions : transition list;
      status : Status.t;
    }
    type t = process Constraint_system.t
    exception Attack_Witness of t
    let get_status cs =
      (Constraint_system.get_additional_data cs).status
    let get_conf cs =
      (Constraint_system.get_additional_data cs).conf
    let replace_conf cs conf =
      let s = Constraint_system.get_additional_data cs in
      Constraint_system.replace_additional_data cs {s with conf = conf}
    let get_transitions cs =
      (Constraint_system.get_additional_data cs).next_transitions
    let set_transitions cs tr =
      let s = Constraint_system.get_additional_data cs in
      Constraint_system.replace_additional_data cs {s with next_transitions = tr}
    let get_origin_process cs =
      (Constraint_system.get_additional_data cs).origin
    let init origin conf status =
      Constraint_system.empty {
        origin = origin;
        conf = conf;
        next_transitions = [];
        status = status;
      }
    let successor cs conf status =
      let s = Constraint_system.get_additional_data cs in
      Constraint_system.replace_additional_data cs {s with conf = conf; next_transitions = []; status = status}
    let solution = Constraint_system.instantiate_when_solved

    let fresh_display_id =
      let counter = ref 0 in
      let f () =
        incr counter;
        !counter
      in
      f

    let display out ?(out_ch=stdout) ?(tab=0) ?(id=1) ?(id_link=1) symb_proc = match out with
      | HTML ->
          let proc = Constraint_system.get_additional_data symb_proc in
          let id_link_content = fresh_display_id () in

          let link_block = Printf.sprintf "<a href=\"javascript:show_single('blocks%d');\">blocks<sub>%d</sub></a>" id_link_content id in
          let link_process = Printf.sprintf "<a href=\"javascript:show_single('process%d');\"><span class=\"mathcal\">P</span><sub>%d</sub></a>" id_link_content id in
          let link_csys = Printf.sprintf "<a href=\"javascript:show_single('csys%d');\"><span class=\"mathcal\">C</span><sub>%d</sub></a>" id_link_content id in

          (* Beginning of div *)
          Printf.fprintf out_ch "%s<div class=\"symb_process\" id=\"symb_process%d\" style=\"display:none;\"> <span class=\"mathcal\">SP</span><sub>%d</sub> = (%s,%s,%s,%s,%s)  with\n"
            (create_tab tab)
            id_link id
            (Status.display HTML proc.status) proc.origin
            link_block link_process link_csys;

          (* Display blocks *)
          let blocks = Configuration.get_block_list proc.conf in
          Printf.fprintf out_ch "%s<div class=\"blocks\" id=\"blocks%d\">\n" (create_tab (tab+1)) id_link_content;
          Printf.fprintf out_ch "%sblocks<sub>%d</sub> = %s\n" (create_tab (tab+2)) id (display_list (Block.display HTML) " " (List.rev blocks));
          Printf.fprintf out_ch "%s</div>\n" (create_tab (tab+1));

          (* Display constraint system *)
          Constraint_system.display HTML ~out_ch:out_ch ~tab:(tab+1) ~hidden:false ~id_link:id_link_content ~id:id symb_proc;

          (* Display process *)
          let lbl_proc = Configuration.to_process proc.conf in
          Labelled_process.display HTML ~tab:(tab+1) ~out_ch:out_ch ~label:true ~hidden:true ~start:true ~id:id ~id_link:id_link_content lbl_proc;

          (* End of div *)
          Printf.fprintf out_ch "%s</div>\n" (create_tab tab)
      | _ -> Config.internal_error "[equivalence_session.ml >> Symbolic.Process.display] Unimplemented case."
  end

  module Matching = struct
    (* Vincent: Change that... can do much better with indexes containing links. *)
    type matching_forall_exists = Index.t * (Index.t * BijectionSet.t) list
    type t = matching_forall_exists list

    let empty = []
    let fold f m a =
      List.fold_left (fun a (cs_fa,cs_ex_list) -> f cs_fa cs_ex_list a) a m
    let iter f m =
      List.iter (fun (cs_fa,cs_ex_list) -> f cs_fa cs_ex_list) m

    let print (m:t) : unit =
      List.iter (fun (i,l) ->
        Printf.printf "Matchers for %d:\n" i;
        List.iter (fun (j,bset) ->
          Printf.printf "%d with label matching:\n" j;
          BijectionSet.print bset
        ) l
      ) m

    let add_match i l m =
      Config.debug (fun () -> Config.print_in_log "Symbolic.Matching.add_match\n");
      (i,l) :: m

    (* removes the matching involving an index i. Also checks for attacks, returning a faulty index in case there is one. *)
    let remove (m:t) (to_remove:Index.t list) : t * Index.t option =
      let rec update accu m =
        match m with
        | [] -> accu,None
        | (cs_fa,cs_ex_list) :: t ->
          if List.mem cs_fa to_remove then update accu t
          else
            match List.filter (fun (cs_ex,_) -> not (List.mem cs_ex to_remove)) cs_ex_list with
            | [] -> [],Some cs_fa
            | cs_ex_list_new -> update ((cs_fa,cs_ex_list_new)::accu) t in
      update [] m

    let clean m to_remove =
      if to_remove = [] then m
      else
        List.filter_unordered (fun (cs_fa,_) ->
          not (List.mem cs_fa to_remove)
        ) m

    let check_and_remove_improper_labels m imp_labels =
      List.map (fun (i_fa, exists) ->
        let imp_labels_fa = List.assoc i_fa imp_labels in
        let exists' =
          List.map (fun (i_ex,bset) ->
            let imp_labels_ex = List.assoc i_ex imp_labels in
            (i_ex,BijectionSet.check_and_remove_improper_labels bset imp_labels_fa imp_labels_ex)
          ) exists
        in
        i_fa,exists'
      ) m

    let fresh_display_id =
      let counter = ref 0 in
      let f () =
        incr counter;
        !counter
      in
      f

    let display out ?(out_ch=stdout) ?(tab=0) ?(rho_id=[]) ?(id=0) ?(id_link=0) m = match out with
      | HTML ->
          let get_id_csys id = match List.assoc_opt id rho_id with
            | None -> id
            | Some id' -> id'
          in

          let list_bset = ref [] in

          let display_exist id_fa (fex,bset) =
            let id_ex = get_id_csys fex in
            let id_link = fresh_display_id () in
            let title = Printf.sprintf "Bijection Set %d &rarr; %d" id_fa id_ex in
            list_bset := (title,id_link,bset) :: !list_bset;
            Printf.sprintf "<a href=\"javascript:show_single('bijectionset%d');\">%d</a>" id_link id_ex
          in

          let display_forall (fa,exist) =
            let id_fa = get_id_csys fa in

            Printf.sprintf "%d &rarr; { %s }" id_fa (display_list (display_exist id_fa) ", " exist)
          in

          Printf.fprintf out_ch "%s<div class=\"matching\" id=\"matching%d\"><span class=\"mathcal\">M</span><sub>%d</sub> = [ %s ]"
            (create_tab tab) id_link id (display_list display_forall ", " m);

          List.iter (fun (title,id_link,bset) ->
            BijectionSet.display HTML ~out_ch:out_ch ~tab:(tab+1) ~id_link:id_link ~title:title bset
          ) (List.rev !list_bset);

          Printf.fprintf out_ch "%s</div>" (create_tab tab)
      | _ -> Config.internal_error "[equivalence_session.ml >> Matching.display] Unimplemented case."

  end

  module Set = struct
    include IndexedSet.Make(struct type elt = Process.t end)

    let cast (csys_set:t) : Index.t Constraint_system.Set.t =
      Constraint_system.Set.of_list (elements (fun x cs -> Constraint_system.replace_additional_data cs x) csys_set)

    (* inverse operation: restrains a partition node based on the result of the constraint solver. Raises Attack_Witness if an attack is found. *)
    let decast (baseline:t) (matching:Matching.t) (csys_set:Index.t Constraint_system.Set.t) : t * Matching.t =
      let indexes_to_remove = ref [] in
      let new_procs =
        map_filter (fun i cs ->
          match Constraint_system.Set.find (fun cs -> i = Constraint_system.get_additional_data cs) csys_set with
          | None ->
            indexes_to_remove := i :: !indexes_to_remove;
            None
          | Some cs_upd ->
            let add_data = Constraint_system.get_additional_data cs in
            Some (Constraint_system.replace_additional_data cs_upd add_data)
        ) baseline in
      match Matching.remove matching !indexes_to_remove with
      | _, Some index ->
        (* Printf.printf "Oh, %s triggers an attack!\n" (Index.to_string index); *)
        raise (Process.Attack_Witness (find new_procs index))
      | cleared_matching, None -> new_procs,cleared_matching

    (* removing useless constraint systems (exists-only matching no forall) *)
    let clean (csys_set:t) (m:Matching.t) : t =
      let useless_existential_index index =
        List.for_all (fun (_,cs_ex_list) ->
          List.for_all (fun (cs_ex,_) -> cs_ex <> index) cs_ex_list
        ) m in
      map_filter (fun index cs ->
        let symp = Constraint_system.get_additional_data cs in
        match symp.Process.status with
        | Status.Exists
        | Status.Both when useless_existential_index index ->
          if symp.Process.status = Status.Exists then None
          else
            Some (Constraint_system.replace_additional_data cs {symp with Process.status = Status.ForAll})
        | _ -> Some cs
      ) csys_set

    let are_variables_authorising_block csys_set vars_to_check csys_fa exist =
      if vars_to_check = []
      then true
      else
        let csys_list = List.rev_map (fun (id_ex,_) -> find csys_set id_ex) exist in

        List.for_all (fun v ->
          let conf_fa = Process.get_conf csys_fa in
          let vars_fst_fa = Constraint_system.get_associated_fst_ord_var csys_fa v in
          let fst_subst_fa = Constraint_system.get_substitution_solution Protocol csys_fa in
          Constraint_system.occurs_in_frame csys_fa vars_fst_fa ||
          Configuration.occurs_in_process vars_fst_fa fst_subst_fa conf_fa ||
          List.exists (fun csys ->
            let conf = Process.get_conf csys in
            let vars_fst = Constraint_system.get_associated_fst_ord_var csys v in
            let fst_subst = Constraint_system.get_substitution_solution Protocol csys in
            Constraint_system.occurs_in_frame_full csys vars_fst ||
            Configuration.occurs_in_process vars_fst fst_subst conf
          ) csys_list
        ) vars_to_check

    (* remove configurations with unauthorised blocks, and returns the updated
    matching *)
    let remove_unauthorised_blocks check_variables (csys_set:t) (matching:Matching.t) (snd_subst:(snd_ord,axiom) Subst.t) : t * Matching.t =
      let (indexes_to_remove,new_matching) =
        List.fold_left (fun (accu_ind,accu_match) ((cs_fa,exist) as m) ->
          let cs = find csys_set cs_fa in
          let symp = Constraint_system.get_additional_data cs in
          let block_authorised, vars_to_check = Configuration.check_block snd_subst symp.Process.conf in
          if block_authorised
          then
            (* We check the variables in the constraint system *)
            if (not check_variables) || are_variables_authorising_block csys_set vars_to_check cs exist
            then accu_ind,m::accu_match
            else cs_fa::accu_ind,accu_match
          else cs_fa::accu_ind,accu_match
        ) ([],[]) matching in
      let new_procs =
        map_filter (fun i cs ->
          (* Printf.printf "index %d -> non authorised block\n" i; *)
          let symp = Constraint_system.get_additional_data cs in
          if List.mem i indexes_to_remove then
            match symp.Process.status with
            | Status.Both ->
              Some (Constraint_system.replace_additional_data cs {symp with Process.status = Status.Exists})
            | Status.ForAll -> None
            | Status.Exists ->
              Config.internal_error "[equivalence_session.ml >> remove_unauthorised_blocks] A purely-existential constraint system should not appear in the first components of matching."
          else Some cs
        ) csys_set in
      new_procs,new_matching


    let get_improper_labels csys_set =
      let accu_imp_labels = ref [] in
      let nb_imp_labels = ref 0 in

      let csys_set' =
        map (fun i proc ->
          let conf = Process.get_conf proc in
          Configuration.get_improper_labels (fun imp_labels conf' ->
            if !accu_imp_labels = []
            then
              begin
                accu_imp_labels := [i,imp_labels];
                nb_imp_labels := List.length imp_labels
              end
            else
              if List.length imp_labels <> !nb_imp_labels
              then raise Not_found
              else accu_imp_labels := (i,imp_labels) :: !accu_imp_labels;

            Process.replace_conf proc conf'
          ) conf
        ) csys_set
      in
      !accu_imp_labels,csys_set'

  end

  module Transition = struct
    (* for printing purpose *)
    let print (source:Index.t) (tr:transition) : unit =
      let string_labs =
        match tr.label with
        | Single label -> Label.to_string label
        | Double (lab1,lab2) -> Printf.sprintf "%s/%s" (Label.to_string lab1) (Label.to_string lab2) in
      let string_skels =
        match tr.skel_target with
        | Single skel -> Labelled_process.Skeleton.print skel
        | Double (skel1,skel2) -> Printf.sprintf "%s/%s" (Labelled_process.Skeleton.print skel1) (Labelled_process.Skeleton.print skel2) in
      Printf.printf "%d -> %d (lab=%s, forall=%b, after reduced subprocess:%s) " source tr.target string_labs tr.forall string_skels

    let add_transition_start (csys_set:Set.t ref) (accu:transition list ref) (conf:Configuration.t) (eqn:(fst_ord, Term.name) Subst.t) (cs:Process.t) (status:Status.t) : unit =
      let initial_label = Configuration.get_initial_label conf in
      Configuration.normalise conf eqn (fun gather conf_norm skel_list ->
        let skel =
          match skel_list with
          | [skel] -> skel
          | _ -> Config.internal_error "[equivalence_session.ml >> Symbolic.Transition.add_transition_input] Unexpected number of skeletons after normalisation." in
        let equations = Labelled_process.Normalise.equations gather in
        let disequations = Labelled_process.Normalise.disequations gather in
        try
          let cs1 = Constraint_system.apply_substitution cs equations in
          let cs2 = Constraint_system.add_disequations cs1 disequations in
          let cs3 = Process.successor cs2 conf_norm status in
          let (new_set,target) = Set.add_new_elt !csys_set cs3 in

          let transition = {
            target = target;
            skel_target = Single skel;
            label = Single initial_label;
            forall = true;
            type_of = In;
          } in
          accu := transition :: !accu;
          csys_set := new_set
        with
          | Constraint_system.Bot -> ()
      )

    let add_transition_output (csys_set:Set.t ref) (accu:transition list ref) (conf:Configuration.t) (eqn:(fst_ord, Term.name) Subst.t) (cs:Process.t) (ax:axiom) (od:Labelled_process.Output.data) (new_status:Status.t) : unit =
      Configuration.normalise ~context:od.Labelled_process.Output.context conf eqn (fun gather conf_norm skel_list ->
        let skel =
          match skel_list with
          | [skel] -> skel
          | _ -> Config.internal_error "[equivalence_session.ml >> Symbolic.Transition.add_transition_input] Unexpected number of skeletons after normalisation." in
        let equations = Labelled_process.Normalise.equations gather in
        let disequations = Labelled_process.Normalise.disequations gather in
        let t0 = Subst.apply equations od.Labelled_process.Output.term (fun x f -> f x) in

        try
          let cs1 =
            Constraint_system.apply_substitution cs equations in
          let cs2 =
            Constraint_system.add_axiom cs1 ax (Rewrite_rules.normalise t0) in
          let cs3 =
            Constraint_system.add_disequations cs2 disequations in
          let cs4 = Process.successor cs3 conf_norm new_status in
          let (new_set,target) = Set.add_new_elt !csys_set cs4 in

          let transition = {
            target = target;
            skel_target = Single skel;
            label = Single od.Labelled_process.Output.lab;
            forall = od.Labelled_process.Output.optim;
            type_of = Out;
          } in
          accu := transition :: !accu;
          csys_set := new_set
        with
          | Constraint_system.Bot -> ()
      )

    let add_transition_input (csys_set:Set.t ref) (accu:transition list ref) (conf:Configuration.t) (eqn:(fst_ord,Term.name) Subst.t) (cs:Process.t) (var_X:snd_ord_variable) (idata:Labelled_process.Input.data) (new_status:Status.t) : unit =
      Configuration.normalise conf eqn (fun gather conf_norm skel_list ->
        let skel =
          match skel_list with
          | [skel] -> skel
          | _ -> Config.internal_error "[equivalence_session.ml >> Symbolic.Transition.add_transition_input] Unexpected number of skeletons after normalisation." in
        let equations = Labelled_process.Normalise.equations gather in
        let disequations = Labelled_process.Normalise.disequations gather in
        let inp = Subst.apply equations (of_variable idata.Labelled_process.Input.var) (fun x f -> f x) in
        let ded_fact = BasicFact.create var_X inp in

        try
          let cs1 = Constraint_system.apply_substitution cs equations in
          let cs2 = Constraint_system.add_basic_fact cs1 ded_fact in
          let cs3 = Constraint_system.add_disequations cs2 disequations in
          let cs4 = Process.successor cs3 conf_norm new_status in
          let (new_set,target) = Set.add_new_elt !csys_set cs4 in

          let transition = {
            target = target;
            skel_target = Single skel;
            label = Single idata.Labelled_process.Input.lab;
            forall = idata.Labelled_process.Input.optim;
            type_of = In;
          } in
          accu := transition :: !accu;
          csys_set := new_set
        with
          | Constraint_system.Bot -> ()
      )

    let add_transition_comm (csys_set:Set.t ref) (accu:transition list ref) (conf:Configuration.t) (eqn:(fst_ord,Term.name) Subst.t) (cs:Process.t) (cdata:Labelled_process.PrivateComm.data) (new_status:Status.t) : unit =
      Configuration.normalise conf eqn (fun gather conf_norm skel_list ->
        let (skel_in,skel_out) =
          match skel_list with
          | [x;y] -> x,y
          | _ -> Config.internal_error "[equivalence_session.ml >> Symbolic.Transition.add_transition_input] Unexpected number of skeletons after normalisation." in
        let equations = Labelled_process.Normalise.equations gather in
        let disequations = Labelled_process.Normalise.disequations gather in

        try
          let cs1 = Constraint_system.apply_substitution cs equations in
          let cs2 = Constraint_system.add_disequations cs1 disequations in
          let cs3 = Process.successor cs2 conf_norm new_status in
          let (new_set,target) = Set.add_new_elt !csys_set cs3 in

          let transition = {
            target = target;
            skel_target = Double (skel_in,skel_out);
            label = Double (cdata.Labelled_process.PrivateComm.labs);
            forall = cdata.Labelled_process.PrivateComm.optim;
            type_of = Comm;
          } in
          accu := transition :: !accu;
          csys_set := new_set
        with
          | Constraint_system.Bot -> ()
      )


    let generate ?(improper=None) (v:vars) (type_of_transition:Configuration.Transition.kind option) (csys_set:Set.t ref) (cs:Process.t) : transition list =
      let status = Process.get_status cs in
      let symp = Constraint_system.get_additional_data cs in
      let accu : transition list ref = ref [] in
      begin match type_of_transition with
      | None -> ()
      | Some Configuration.Transition.RStart ->
        let conf = Configuration.Transition.apply_start symp.Process.conf in
        let eqn = Constraint_system.get_substitution_solution Protocol cs in
        add_transition_start csys_set accu conf eqn cs symp.Process.status
      | Some Configuration.Transition.RNeg ->
        let ax = get_axiom v in
        List.iter_with_memo (fun proc memo_left memo_right ->
          let memo = List.rev_append memo_left memo_right in
          List.iter (fun (pp,output_data) ->
            let conf =
              Configuration.Transition.apply_neg ax pp output_data memo symp.Process.conf in
            let eqn =
              Constraint_system.get_substitution_solution Protocol cs in
            let next_status =
              Status.downgrade_forall status output_data.Labelled_process.Output.optim in
            add_transition_output csys_set accu conf eqn cs ax output_data next_status
          ) (Labelled_process.Output.unfold ~optim:(status=Status.ForAll) proc)
        ) (Configuration.outputs symp.Process.conf)
      | Some Configuration.Transition.RFocus ->
        let var_X = get_snd_ord v in
        let (potential_focuses,potential_comm) =
          Labelled_process.PrivateComm.unfold ~improper:improper ~optim:(status=Status.ForAll) (Configuration.inputs symp.Process.conf) in
        List.iter (fun focus ->
          let conf_exec =
            Configuration.Transition.apply_focus var_X focus symp.Process.conf in
          let eqn =
            Constraint_system.get_substitution_solution Protocol cs in
          let next_status =
            Status.downgrade_forall status (snd focus).Labelled_process.Input.optim in
          add_transition_input csys_set accu conf_exec eqn cs var_X (snd focus) next_status;
          (* Printf.printf "Now there are %d transitions\n" (List.length !accu); *)
        ) potential_focuses;
        List.iter (fun ((_,_,cdata) as comm) ->
          let conf_exec =
            Configuration.Transition.apply_comm comm symp.Process.conf in
          let eqn =
            Constraint_system.get_substitution_solution Protocol cs in
          let next_status =
            Status.downgrade_forall status cdata.Labelled_process.PrivateComm.optim in
          add_transition_comm csys_set accu conf_exec eqn cs cdata next_status
        ) potential_comm
      | Some Configuration.Transition.RPos ->
        let var_X = get_snd_ord v in
        let (idata,conf_exec) =
          Configuration.Transition.apply_pos var_X symp.Process.conf in
        let eqn =
          Constraint_system.get_substitution_solution Protocol cs in
        let next_status =
          Status.downgrade_forall status idata.Labelled_process.Input.optim in
        add_transition_input csys_set accu conf_exec eqn cs var_X idata next_status end;
      List.filter_in_head (fun tr -> tr.forall) !accu
  end
end


(* Graph structure and conversion from matching *)
module Graph = struct
  (* types and functor instantiations *)
  type node = Symbolic.Index.t
  type edge = BijectionSet.t

  module Graph = Map.Make(struct type t = node let compare = compare end)
  module Targets = Set.Make(struct type t = node * edge let compare = compare end)
  type t = Targets.t Graph.t

  module ConnectedComponent = Set.Make(struct type t = node let compare = compare end)

  (* addition of (sets of) edges to a graph *)
  let add_arrow (g:t) (n:node) (n':node) (e:edge) : t =
    Graph.update n (function
      | None -> Some (Targets.singleton (n',e))
      | Some set -> Some (Targets.add (n',e) set)
    ) g

  let add_arrows (g:t) (n:node) (t:Targets.t) : t =
    Graph.update n (function
      | None -> Some t
      | Some set -> Some (Targets.union set t)
    ) g

  (* conversion from a matching to a graph *)
  let of_matching (m:Symbolic.Matching.t) : t =
    Symbolic.Matching.fold (fun n tg g0 ->
      let g1 = add_arrows g0 n (Targets.of_list tg) in
      List.fold_left (fun g2 (n',e) -> add_arrow g2 n' n e) g1 tg
    ) m Graph.empty

  (* computes the connected components of a graph *)
  let connected_components (g:t) : ConnectedComponent.t list =
    let visited = Hashtbl.create (List.length (Graph.bindings g)) in
    Graph.fold (fun node _ () -> Hashtbl.add visited node false) g ();
    let mark node = Hashtbl.replace visited node true in
    let marked node = Hashtbl.find visited node in

    let rec get_equiv_class eqc node succ =
      if marked node then eqc
      else (
        mark node;
        Targets.fold (fun (n,_) eq ->
          get_equiv_class eq n (Graph.find n g)
        ) succ (node::eqc)
      ) in

    Graph.fold (fun node succ comps ->
      match get_equiv_class [] node succ with
      | [] -> comps
      | eqc -> ConnectedComponent.of_list eqc :: comps
    ) g []
end


(* Exploration of the partition tree *)
module PartitionTree = struct
  module Node = struct
    type t = {
      csys_set : Symbolic.Set.t;
      matching : Symbolic.Matching.t;
      size_frame : int;
      id : int; (* only for debugging purposes *)
      improper : bool
    }

    let total_node = ref 0
    let only_exists = ref 0

    let test_node n =
      incr total_node;
        let found = ref false in
        let size = ref 0 in
        Symbolic.Set.iter (fun _ p ->
          Printf.printf "origin: %s, " (Symbolic.Process.get_origin_process p);
          Symbolic.Status.print (Symbolic.Process.get_status p);
          print_string "\n";
          incr size;
          flush_all ();
          if (Symbolic.Process.get_status p) = Symbolic.Status.init_for_inclusion_right
          then found := true
        ) n.csys_set;
      if !found
      then
        begin incr only_exists;
        Printf.printf "-- Total = %d, size = %d, Only_exists = %d\n" !total_node !size !only_exists;
        flush_all ()
        end
      else
        begin
        Printf.printf "-- Total = %d (size = %d)\n" !total_node !size;
        flush_all ()
        end

    let delete_equal_modulo_existential n =
      let node_deleted = ref false in

      let rec explore_one id proc_l csys bset = function
        | [] -> false
        | (_, proc_l',csys',bset')::q ->
            let equal =
              try
                Term.auto_cleanup_matching (fun () ->
                  Config.debug (fun () -> Config.print_in_log "Constraint_system.match_variables_and_names\n");
                  Constraint_system.match_variables_and_names csys csys';
                  Config.debug (fun () -> Config.print_in_log "BijectionSet.match_processes\n");
                  BijectionSet.match_processes (fun () -> ()) proc_l proc_l' bset bset';
                  true
                )
              with No_Match -> false
            in
            equal || explore_one id proc_l csys bset q
      in

      let rec explore = function
        | [] -> []
        | (id, proc_l,csys,bset)::q ->
            if explore_one id proc_l csys bset q
            then (node_deleted := true; explore q)
            else (id,bset)::(explore q)
      in

      let matching =
        Symbolic.Matching.fold (fun id_forall id_exist_list accu ->
          if List.length id_exist_list >= 2
          then
            let proc_csys_list =
              List.map (fun (id_ex,bset) ->
                Config.debug (fun () -> Config.print_in_log "Symbolic.Set.find\n");
                let csys = Symbolic.Set.find n.csys_set id_ex in
                Config.debug (fun () -> Config.print_in_log "End Symbolic.Set.find\n");
                let subst =  Constraint_system.get_substitution_solution Protocol csys in
                let conf = Symbolic.Process.get_conf csys in
                let proc_l1 = Configuration.elements conf in
                let proc_l2 = List.map (fun lp -> Labelled_process.apply_substitution subst lp) proc_l1 in
                (id_ex,proc_l2,csys,bset)
              ) id_exist_list
            in
            Config.debug (fun () -> Config.print_in_log "Starting explore\n");
            Symbolic.Matching.add_match id_forall (explore proc_csys_list) accu
          else Symbolic.Matching.add_match id_forall id_exist_list accu
        ) n.matching Symbolic.Matching.empty
      in

      if !node_deleted
      then { n with csys_set = Symbolic.Set.clean n.csys_set matching; matching = matching }
      else n

    let delete_equal_modulo_universal n =
      let symb_proc_to_downgrade = ref [] in

      let rec explore_one f_not_subsumed f_is_subsumed prev_matching ((id,proc_l,csys,exist_list,block_list) as t) = function
        | [] -> f_not_subsumed prev_matching
        | ((id',proc_l',csys',exist_list',block_list') as t')::q ->
            let result = ref None in
            begin try
              Term.auto_cleanup_matching (fun () ->
                Config.debug (fun () -> Config.print_in_log "delete_univ - Constraint_system.match_variables_and_names\n");
                Constraint_system.match_variables_and_names csys csys';
                Config.debug (fun () -> Config.print_in_log "delete_univ - BijectionSet.match_forall_processes\n");
                BijectionSet.match_forall_processes (fun does_left_subsume ->
                  result := Some does_left_subsume
                ) proc_l proc_l' block_list block_list' exist_list exist_list'
              )
            with No_Match -> ()
            end;

            match !result with
              | None -> explore_one f_not_subsumed f_is_subsumed (t'::prev_matching) t q
              | Some true ->
                  symb_proc_to_downgrade := id' :: !symb_proc_to_downgrade;
                  explore_one f_not_subsumed f_is_subsumed prev_matching t q
              | _ ->
                  symb_proc_to_downgrade := id :: !symb_proc_to_downgrade;
                  f_is_subsumed (List.rev_append prev_matching q)
      in

      let rec explore prev_matching = function
        | [] -> prev_matching
        | t::q ->
            explore_one (explore (t::prev_matching)) (explore prev_matching) [] t q
      in

      match n.matching with
        | [_] -> n
        | _ ->
          Config.debug (fun () -> Config.print_in_log "delete_univ - generate csys_proc\n");
          let list_csys_proc =
            List.map (fun (id_forall,exists_list) ->

              let csys = Symbolic.Set.find n.csys_set id_forall in
              let subst =  Constraint_system.get_substitution_solution Protocol csys in
              let conf = Symbolic.Process.get_conf csys in
              let proc_l1 = Configuration.elements conf in
              let proc_l2 = List.map (fun lp -> Labelled_process.apply_substitution subst lp) proc_l1 in
              (id_forall,proc_l2,csys,exists_list,Configuration.get_block_list conf)
            ) n.matching
          in
          Config.debug (fun () -> Config.print_in_log "delete_univ - new matching\n");
          let new_matching = explore [] list_csys_proc in

          if !symb_proc_to_downgrade = []
          then n
          else
            let new_matching' = List.rev_map (fun (id,_,_,exist_list,_) -> (id,exist_list)) new_matching in
            let new_csys_set =
              Symbolic.Set.map_filter (fun i cs ->
                let symp = Constraint_system.get_additional_data cs in
                if List.mem i !symb_proc_to_downgrade then
                  match symp.Symbolic.Process.status with
                  | Symbolic.Status.Both ->
                    Some (Constraint_system.replace_additional_data cs {symp with Symbolic.Process.status = Symbolic.Status.Exists})
                  | Symbolic.Status.ForAll -> None
                  | Symbolic.Status.Exists -> Config.internal_error "[equivalence_session.ml >> delete_equal_modulo_universal] A purely-existential constraint system should not appear in the first components of matching."
                else Some cs
              ) n.csys_set in
            { n with csys_set = new_csys_set ; matching = new_matching' }

    let remove_improper_labels n =
      try
        let index_imp_labels_list, csys_set' = Symbolic.Set.get_improper_labels n.csys_set in
        let matching' = Symbolic.Matching.check_and_remove_improper_labels n.matching index_imp_labels_list in
        { n with csys_set = csys_set'; matching = matching' }
      with Not_found -> n

    let fresh_id =
      let x = ref (-1) in
      fun () -> incr x; !x

    let print (n:t) : unit =
      if n.id <> 0
      then
      begin
        Printf.printf ">> Data node (id=%d):\n" n.id;
        Printf.printf "indexes: ";
        Symbolic.Set.iter (fun id csys ->
          Printf.printf "%s [Status " (Symbolic.Index.to_string id);
          Symbolic.Status.print (Symbolic.Process.get_status csys);
          Printf.printf ",origin %s] " (Symbolic.Process.get_origin_process csys)
        ) n.csys_set;
        Printf.printf "\nsize frame: %d\nmatching: " n.size_frame;
        Symbolic.Matching.iter (fun i l ->
          Printf.printf "%s->[%s ]; " (Symbolic.Index.to_string i) (List.fold_left (fun s (j,_) ->
            Printf.sprintf "%s %s" s (Symbolic.Index.to_string j)
          ) "" l)
        ) n.matching;
        print_endline "";
        Symbolic.Set.iter (fun id p ->
          let conf = Symbolic.Process.get_conf p in
          let p' = Configuration.to_process conf in
          let solution = Constraint_system.get_substitution_solution Protocol p in
          Printf.printf "---Process %s : %s\n" (Symbolic.Index.to_string id) (Labelled_process.print ~labels:true ~solution:solution p');
          print_string (Configuration.display_blocks conf)
        ) n.csys_set;
        flush_all ()
      end

    let init set m = {
      csys_set = set;
      matching = m;
      size_frame = 0;
      id = fresh_id ();
      improper = false
    }
    (* determines the type of the next transitions of a constraint system set, and generates the corresponding second-order variable or axiom. *)
    let data_next_transition (n:t) : Configuration.Transition.kind option * vars =
      Config.debug (fun () -> Config.print_in_log "data_next_transition\n");
      if Symbolic.Set.is_empty n.csys_set then
        None, {snd_ord = None; axiom = None}
      else
        let csys = Symbolic.Set.choose n.csys_set in
        let trans =
          Configuration.Transition.next (Symbolic.Process.get_conf csys) in
        (* Configuration.Transition.print_kind trans; *)
        match trans with
        | None
        | Some Configuration.Transition.RStart -> trans, {snd_ord = None; axiom = None}
        | Some Configuration.Transition.RFocus
        | Some Configuration.Transition.RPos ->
          let new_var =
            Variable.fresh Recipe Free (Variable.snd_ord_type n.size_frame) in
          trans, {snd_ord = Some new_var; axiom = None}
        | Some Configuration.Transition.RNeg ->
          trans, {snd_ord = None; axiom = Some (Axiom.create (n.size_frame+1))}

    let release_skeleton (n:t) : t =
      let improper = ref n.improper in
      let new_set =
        Symbolic.Set.map (fun _ csys ->
          let conf = Symbolic.Process.get_conf csys in
          let conf' = Configuration.release_skeleton conf in
          improper := Configuration.is_improper_phase conf';
          Symbolic.Process.replace_conf csys conf'
        ) n.csys_set
      in

      { n with csys_set = new_set ; improper = !improper }

    let clean (n:t) : t =
      {n with csys_set = Symbolic.Set.clean n.csys_set n.matching}

    let apply_optim n =
      Config.debug (fun () -> Config.print_in_log "apply_optim\n");
      if n.improper
      then n
      else
        let csys = Symbolic.Set.choose n.csys_set in
        let trans = Configuration.Transition.next (Symbolic.Process.get_conf csys) in
        match trans with
        | Some Configuration.Transition.RFocus ->
            Config.debug (fun () -> Config.print_in_log "remove_improper_labels\n");
            let n1 = remove_improper_labels n in
            Config.debug (fun () -> Config.print_in_log "delete_equal_modulo_universal\n");
            let n2 =
              if !optimisation_parameters
              then delete_equal_modulo_universal n1
              else n1 in
            Config.debug (fun () -> Config.print_in_log "delete_equal_modulo_existential\n");
            delete_equal_modulo_existential n2
        | _ -> n

    let single_or_double_update l1 l2 s1 s2 bset =
      match l1, l2, s1, s2 with
      | Single lfa, Single lex, Single sfa, Single sfx ->
        BijectionSet.update lfa lex sfa sfx bset
      | Double (lfa1,lfa2), Double (lex1,lex2), Double (sfa1,sfa2), Double (sfx1,sfx2) ->
        begin match BijectionSet.update lfa1 lex1 sfa1 sfx1 bset with
          | None -> None
          | Some bset_upd -> BijectionSet.update lfa2 lex2 sfa2 sfx2 bset_upd
        end
      | _ -> Config.internal_error "[equivalence_session.ml >> PartitionTree.Node.single_or_double_update] Inconsistent number of arguments."

    (* From a partition tree node, generates the transitions and creates a new node with all the resulting processes inside. A
    NB. The constraint solving and the skeleton checks remain to be done after this function call. *)
    let generate_next (n:t) : Configuration.Transition.kind option * t =
      Config.debug (fun () -> Config.print_in_log "generate_next\n");
      let new_id = fresh_id () in
      let n = apply_optim n in
      (* Generation of the transitions *)
      let (trans,vars) = data_next_transition n in
      let new_csys_set = ref Symbolic.Set.empty in
      let csys_set_with_transitions =
        Symbolic.Set.map (fun _ csys ->
          let next_transitions =
            let conf = (Constraint_system.get_additional_data csys).Symbolic.Process.conf in
            Symbolic.Transition.generate ~improper:(Configuration.get_ongoing_improper_label conf) vars trans new_csys_set csys in
          (* Printf.printf "Transitions generated from %s: \n" (Symbolic.Index.to_string i);
          List.iter (fun tr -> Symbolic.Transition.print i tr; print_endline "") next_transitions; *)
          Symbolic.Process.set_transitions csys next_transitions
        ) n.csys_set in
      let new_csys_set = !new_csys_set in
      Config.debug (fun () -> Config.print_in_log "new_matching\n");
      let new_matching =
        Symbolic.Matching.fold (fun cs_fa cs_ex_list (accu1:Symbolic.Matching.t) ->
          let symp_fa = Symbolic.Set.find csys_set_with_transitions cs_fa in
          List.fold_left_while (fun tr -> tr.Symbolic.forall) (fun (accu2:Symbolic.Matching.t) (tr_fa:Symbolic.transition) ->
            if not tr_fa.Symbolic.forall then accu2
            else
              let cs_ex_list_new =
                List.fold_left (fun (accu3:(Symbolic.Index.t*BijectionSet.t) list) (cs_ex,bset) ->
                  let symp_ex = Symbolic.Set.find csys_set_with_transitions cs_ex in
                  List.fold_left (fun (accu4:(Symbolic.Index.t*BijectionSet.t) list) (tr_ex:Symbolic.transition) ->
                    if tr_fa.Symbolic.type_of = tr_ex.Symbolic.type_of then
                      match single_or_double_update tr_fa.Symbolic.label tr_ex.Symbolic.label tr_fa.Symbolic.skel_target tr_ex.Symbolic.skel_target bset with
                      | None -> accu4
                      | Some bset_upd -> (tr_ex.Symbolic.target,bset_upd) :: accu4
                    else accu4
                  ) accu3 (Symbolic.Process.get_transitions symp_ex)
                ) [] cs_ex_list in
              Symbolic.Matching.add_match tr_fa.Symbolic.target cs_ex_list_new accu2
          ) accu1 (Symbolic.Process.get_transitions symp_fa)
        ) n.matching Symbolic.Matching.empty in

      (* final node *)
      let new_node =
        clean {n with csys_set = new_csys_set; matching = new_matching; id = new_id} in
      trans,new_node

    (* splits a partition tree node into independent component (i.e. into components whose matchings are disjoint) and applies a continuation on each of them. *)
    let split (n:t) (f_cont:t->(unit->unit)->unit) (f_next:unit->unit) : unit =
      let comps = Graph.connected_components (Graph.of_matching n.matching) in

      let add_matching_in_data_list i matchers data =
        match List.find_and_remove (fun (_,c) -> Graph.ConnectedComponent.mem i c) data with
        | None, _ -> Config.internal_error "[equivalence_session.ml >> split_partition_tree_node] Unexpected case."
        | Some (ml,c),remainder ->
          let new_matching = Symbolic.Matching.add_match i matchers ml in
          (new_matching,c) :: remainder
      in

      let new_node_data =
        Symbolic.Matching.fold add_matching_in_data_list n.matching (List.rev_map (fun c -> Symbolic.Matching.empty,c) comps)
      in

      let replace_data m c =
        let csys_set =
          Symbolic.Set.filter (fun i _ ->
            Graph.ConnectedComponent.mem i c
          ) n.csys_set in
        {n with csys_set = csys_set; matching = m; id = fresh_id()} in

      let rec branch_on_nodes l f_next =
        match l with
        | [] -> f_next()
        | (m,c) :: t ->
          let node = replace_data m c in
          (* Printf.printf "- treating node %s (father: %s, remaining after that: %d)\n" node.id n.id (List.length t); *)
          (* print node; *)
          f_cont node (fun () -> branch_on_nodes t f_next) in

      branch_on_nodes new_node_data f_next

    (* removes useless elements from the node after the constraint solving, and verify is the node is an attack node *)
    let decast (node:t) (csys_set:Symbolic.Index.t Constraint_system.Set.t) : t =
      let (csys_set_decast,matching_decast) =
        Symbolic.Set.decast node.csys_set node.matching csys_set in
      {node with
        csys_set = csys_set_decast;
        matching = matching_decast;
        id = fresh_id()}

    (* removes (forall-quantified) constraint systems with unauthorised blocks *)
    let remove_unauthorised_blocks (node:t) (csys_set:Symbolic.Index.t Constraint_system.Set.t) : t =
      if node.improper
      then node
      else
        let conf = Symbolic.Process.get_conf (Symbolic.Set.choose node.csys_set) in
        if Configuration.is_focused conf
        then node
        else
          let csys_set_opt =
            Constraint_system.Set.optimise_snd_ord_recipes csys_set in
          let csys = Constraint_system.Set.choose csys_set_opt in
          let subst = Constraint_system.get_substitution_solution Recipe csys in
          let (new_set,matching_authorised) =
            Symbolic.Set.remove_unauthorised_blocks true node.csys_set node.matching subst in
          {node with csys_set = new_set; matching = matching_authorised}

    (******* Display *******)

    let fresh_display_id =
      let counter = ref 0 in
      let f () =
        incr counter;
        !counter
      in
      f

    let display out ?(out_ch=stdout) ?(tab=0) ?(id=0) ?(id_link=0) node = match out with
      | HTML ->
          let rho_id_mapping = ref [] in
          let counter = ref 0 in
          let csys_list = ref [] in

          Printf.fprintf out_ch "%s<div class=\"node\" id=\"node%d\" style=\"display:none;\">Node <span class=\"mathcal\">N</span><sub>%d</sub> = ( %s " (create_tab tab) id_link id (lcurlybracket HTML);

          Symbolic.Set.iter (fun id_csys csys ->
            incr counter;
            rho_id_mapping := (id_csys,!counter) :: !rho_id_mapping;
            let id_link_content = fresh_display_id () in
            if !counter = 1
            then Printf.fprintf out_ch "<a href=\"javascript:show_single('symb_process%d');\"><span class=\"mathcal\">SP</span><sub>1</sub></a>" id_link_content
            else Printf.fprintf out_ch ", <a href=\"javascript:show_single('symb_process%d');\"><span class=\"mathcal\">SP</span><sub>%d</sub></a>" id_link_content !counter;
            csys_list := (!counter,id_link_content,csys) :: !csys_list
          ) node.csys_set;

          let id_link_matching = fresh_display_id () in
          Printf.fprintf out_ch " %s, <a href=\"javascript:show_single('matching%d');\"><span class=\"mathcal\">M</span><sub>%d</sub></a>) with\n" (rcurlybracket HTML) id_link_matching id;

          List.iter (fun (id,id_link,csys) ->
            Symbolic.Process.display HTML ~out_ch:out_ch ~tab:(tab+1) ~id:id ~id_link:id_link csys
          ) (List.rev !csys_list);

          Symbolic.Matching.display HTML ~out_ch:out_ch ~tab:(tab+1) ~rho_id:!rho_id_mapping ~id:id ~id_link:id_link_matching node.matching;


          Printf.fprintf out_ch "%s</div>\n" (create_tab tab)
      | _ -> Config.internal_error "[equivalence_session.ml >> Node.display] Unimplemented case"

  end

  (* construction of the successor nodes of a partition tree. This includes:
    - generating the next transitions (using module Node)
    - applying the internal constraint solver (to split in different nodes non statically equivalent constraint systems)
    - performing skeleton/block-authorisation checks on the resulting nodes.
  NB. The continuations f_cont indicates what to do with the generated nodes, and f_next what to do once all nodes have been explored. *)
  let generate_successors (n:Node.t) (f_cont:Node.t->(unit->unit)->unit) (f_next:unit->unit) : unit =
    Config.debug (fun () -> Config.print_in_log "Starting generate_successors\n");
    if Symbolic.Set.is_empty n.Node.csys_set then f_next()
    else begin
      (* Printf.printf "\n==> EXPLORATION FROM %s\n" n.Node.id;
      Node.print n; *)
      (* Invariant : When the node is flaged as improper, Node.generate_next
         should always return a RFocus or RPos transition. *)
      let (transition_type,node_to_split) = Node.generate_next n in
      (* Printf.printf "--> new node to split:\n";
      Node.print node_to_split; *)
      Node.split node_to_split (fun node f_next1 ->
        (* We detect whether the ongoing block will be an improper block.
           Moreover, when node is flaged as improper, we clean the focus
           if it does not correspond to an input on a public channel. *)
        let released_node_op =
          try
            Some (Node.release_skeleton node)
          with No_Match -> None
        in

        match released_node_op with
          | None -> f_next1 ()
          | Some released_node ->
              let csys_set = Symbolic.Set.cast released_node.Node.csys_set in
              match transition_type with
              | None ->
                (* the end of the trace: one verifies that equivalence is not violated, which concludes the analysis of this branch. *)
                let _ = Node.decast released_node in
                f_next1 ()
              | Some Configuration.Transition.RStart ->
                (* very beginning of the analysis: only a skeleton check is needed before moving on to the constructing the successor nodes (no unauthorised blocks possible). *)
                Constraint_system.Rule.apply_rules_after_input false (fun csys_set f_next2 ->
                  let node_decast = Node.decast released_node csys_set in
                  let final_node = Node.clean node_decast in
                  Node.split final_node f_cont f_next2
                ) csys_set f_next1
              | Some Configuration.Transition.RFocus ->
                (* focus and execution of an input. *)
                Constraint_system.Rule.apply_rules_after_input false (fun csys_set f_next2 ->
                  if Constraint_system.Set.is_empty csys_set then f_next2()
                  else
                    let node_decast = Node.decast released_node csys_set in
                    let node_autho = Node.remove_unauthorised_blocks node_decast csys_set in
                    let final_node = Node.clean node_autho in
                    Node.split final_node f_cont f_next2
                ) csys_set f_next1
              | Some Configuration.Transition.RPos ->
                (* execution of a focused input. The skeleton check releases the focus if necessary, and unauthorised blocks may arise due to the constraint solving. *)
                Constraint_system.Rule.apply_rules_after_input false (fun csys_set f_next2 ->
                  if Constraint_system.Set.is_empty csys_set then f_next2()
                  else
                    let node_decast = Node.decast released_node csys_set in
                    let node_autho = Node.remove_unauthorised_blocks node_decast csys_set in
                    let final_node = Node.clean node_autho in
                    Node.split final_node f_cont f_next2
                ) csys_set f_next1
              | Some Configuration.Transition.RNeg ->
                (* execution of outputs. Similar to the input case, except that the size of the frame is increased by one. *)
                Constraint_system.Rule.apply_rules_after_output false (fun csys_set f_next2 ->
                  if Constraint_system.Set.is_empty csys_set then f_next2()
                  else
                    let node_decast = Node.decast released_node csys_set in
                    let node_autho = Node.remove_unauthorised_blocks node_decast csys_set in
                    let final_node = Node.clean node_autho in
                    Node.split {final_node with Node.size_frame = node.Node.size_frame+1} f_cont f_next2
                ) csys_set f_next1
      ) f_next
    end

  let rec explore (n:Node.t) (f_next:unit->unit) : unit =
    generate_successors n explore f_next

  let explore_from (n:Node.t) : unit =
    explore n (fun () -> ())

  let test_starting_node = ref 1

  let explore_test n =
    let path_scripts = Filename.concat !Config.path_deepsec "Scripts" in
    let path_style = Filename.concat !Config.path_deepsec "Style" in
    let path_template = Filename.concat !Config.path_html_template "test.html" in
    let path_result = Filename.concat !Config.path_index "result_test.html" in

    let out_result = open_out path_result in
    let in_template = open_in path_template in

    let template_stylesheet = "<!-- Stylesheet deepsec -->" in
    let template_script = "<!-- Script deepsec -->" in
    let template_line = "<!-- Content of the file -->" in

    (* Parameters *)
    let tab_test = 4 in
    let counter_node_test = ref 0 in
    let nb_node = 20 in

    let close_files () =
      try
        while true do
          let l = input_line in_template in
          Printf.fprintf out_result "%s\n" l;
        done
      with
      | End_of_file -> close_in in_template; close_out out_result
    in

    let rec explore_with_display n f_next =
      incr counter_node_test;

      if !counter_node_test > !test_starting_node + nb_node
      then (close_files (); exit 0);

      if !counter_node_test >= !test_starting_node
      then
        begin
          let list_node = ref [] in

          generate_successors n (fun n_sons f_next1 ->
            list_node := (n_sons.Node.id, Node.fresh_display_id (), n_sons) :: !list_node;
            f_next1 ()
          ) (fun () -> ());

          let id_link_input_node = Node.fresh_display_id () in
          let id_link_input_optim_node = Node.fresh_display_id () in

          let n_optim = Node.apply_optim n in

          Printf.fprintf out_result "%s<div class=\"result_test\">Input node: <a href=\"javascript:show_single('node%d');\"><span class=\"mathcal\">N</span><sub>%d</sub></a>, "
            (create_tab tab_test)
            id_link_input_node
            n.Node.id;

          Printf.fprintf out_result "Optimised input node: <a href=\"javascript:show_single('node%d');\"><span class=\"mathcal\">N</span><sub>%d</sub></a>, Output nodes: "
            id_link_input_optim_node
            n_optim.Node.id;

          let list_node' = List.rev !list_node in
          let start = ref true in
          List.iter (fun (id,id_link,_) ->
            if !start
            then
              begin
                Printf.fprintf out_result "<a href=\"javascript:show_single('node%d');\"><span class=\"mathcal\">N</span><sub>%d</sub></a>" id_link id;
                start := false
              end
            else Printf.fprintf out_result ", <a href=\"javascript:show_single('node%d');\"><span class=\"mathcal\">N</span><sub>%d</sub></a>" id_link id
          ) list_node';

          Printf.fprintf out_result "\n";

          Node.display HTML ~out_ch:out_result ~tab:(tab_test+1) ~id:n.Node.id ~id_link:id_link_input_node n;
          Node.display HTML ~out_ch:out_result ~tab:(tab_test+1) ~id:n_optim.Node.id ~id_link:id_link_input_optim_node n_optim;
          List.iter (fun (id,id_link,n_son) ->
            Node.display HTML ~out_ch:out_result ~tab:(tab_test+1) ~id:id ~id_link:id_link n_son
          ) list_node';
          Printf.fprintf out_result "%s</div>\n" (create_tab (tab_test));

          let rec browse f_next_1 = function
            | [] -> f_next_1 ()
            | (_,_,n')::q' ->
                explore_with_display n' (fun () ->
                  browse f_next_1 q'
                )
          in
          browse f_next list_node'
        end
      else generate_successors n explore_with_display f_next
    in

    (* Display the beginning *)

    let line = ref (input_line in_template) in
    while !line <> template_stylesheet do
      Printf.fprintf out_result "%s\n" !line;
      line := input_line in_template
    done;
    Printf.fprintf out_result " <link rel=\"stylesheet\" type=\"text/css\" href=\"%s\">\n" (Filename.concat path_style "style.css");

    while !line <> template_script do
      Printf.fprintf out_result "%s\n" !line;
      line := input_line in_template
    done;
    Printf.fprintf out_result " <script src=\"%s\"></script>\n" (Filename.concat path_scripts "scripts.js");

    while !line <> template_line do
      Printf.fprintf out_result "%s\n" !line;
      line := input_line in_template
    done;

    try
      explore_with_display n (fun () -> ())
    with
      Symbolic.Process.Attack_Witness _ -> close_files ()
end

(* mapping everything to a decision procedure *)
type goal =
  | Equivalence
  | Inclusion

type result_analysis =
  | Equivalent
  | Not_Equivalent of Symbolic.Process.t

let string_of_result (goal:goal) (p1:Labelled_process.t) (p2:Labelled_process.t) (res:result_analysis) : string =
  match res with
  | Equivalent ->
    if goal = Equivalence then "Equivalent processes."
    else "Process inclusion proved."
  | Not_Equivalent csys ->
    let origin = Symbolic.Process.get_origin_process csys in
    let p = if origin = "LEFT" then p1 else p2 in
    let sp = Labelled_process.print p in
    let trace =
      let (fst,snd) = Symbolic.Process.solution csys in
      Configuration.print_trace fst snd (Symbolic.Process.get_conf csys) in
    let bold_blue s = Printf.sprintf "\\033[1;34m%s\\033[0m" s in
    if goal = Equivalence then
      Printf.sprintf "Not Equivalent processes. Attack Trace:\n%s%s%s" (bold_blue (Printf.sprintf "\nOrigin (%s process):\n" origin)) sp trace
    else
      Printf.sprintf "Process Inclusion disproved. Attack Trace:\n%s%s%s" (bold_blue "\nOrigin:\n") sp trace

(* computes the root of the partition tree *)
let compute_root (goal:goal) (conf1:Configuration.t) (conf2:Configuration.t) : PartitionTree.Node.t =
  (* initialisation of the rewrite system *)
  Rewrite_rules.initialise_skeletons ();
  Data_structure.Tools.initialise_constructor ();

  (* Initialisation of the optimisation optimisation parameters *)
  initialise_optimisation_parameters conf1 conf2;

  (* initial set of symbolic processes *)
  let csys_set_root = Symbolic.Set.empty in
  let (status_left,status_right) =
    match goal with
    | Equivalence ->
      (Symbolic.Status.init_for_equivalence, Symbolic.Status.init_for_equivalence)
    | Inclusion ->
      (Symbolic.Status.init_for_inclusion_left, Symbolic.Status.init_for_inclusion_right) in
  let symp1 = Symbolic.Process.init "LEFT" conf1 status_left in
  let (csys_set_root,index1) = Symbolic.Set.add_new_elt csys_set_root symp1 in
  let symp2 = Symbolic.Process.init "RIGHT" conf2 status_right in
  let (csys_set_root,index2) = Symbolic.Set.add_new_elt csys_set_root symp2 in
  let matching_root =
    match goal with
    | Equivalence ->
      Symbolic.Matching.add_match index1 [index2,BijectionSet.initial] (
        Symbolic.Matching.add_match index2 [index1,BijectionSet.initial] (
          Symbolic.Matching.empty
        )
      )
    | Inclusion ->
      Symbolic.Matching.add_match index1 [index2,BijectionSet.initial] (
        Symbolic.Matching.empty
      ) in
  PartitionTree.Node.init csys_set_root matching_root

(* overall analysis *)
let analysis (goal:goal) (conf1:Configuration.t) (conf2:Configuration.t) : result_analysis =
  let root = compute_root goal conf1 conf2 in
  Config.debug (fun () -> Config.print_in_log "Compute root completed\n");
  try
    Config.debug (fun () ->
      PartitionTree.explore_test root
    );
    PartitionTree.explore_from root;
    Equivalent
  with
    | Symbolic.Process.Attack_Witness symp -> Not_Equivalent symp

(* printing of the result *)
let publish_result (goal:goal) (id:int) (conf1:Process_session.Configuration.t) (conf2:Process_session.Configuration.t) (result:result_analysis) (running_time:float) : unit =
  Printf.printf "Result query %d: " id;
  flush stdout;
  let res =
    string_of_result goal (Process_session.Configuration.to_process conf1) (Process_session.Configuration.to_process conf2) result in
  ignore (Sys.command (Printf.sprintf "printf \"%s\"" res));
  print_endline (Printf.sprintf "\nRunning time: %s" (Display.mkRuntime running_time));
  ignore(Sys.command "rm -f index_old.html")
