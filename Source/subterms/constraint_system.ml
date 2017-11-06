open Term
open Data_structure
open Display
open Extensions

(*************************************
***       Constraint systems       ***
**************************************)

type history_skeleton =
  {
    destructor : symbol;
    fst_vars : (fst_ord, name) variable list;
    snd_vars : (snd_ord, axiom) variable list;
    diseq : Eq.Mixed.t
  }

type 'a t =
  {
    additional_data : 'a;

    size_frame : int;

    df : DF.t;

    private_channels : protocol_term list;

    eqfst : (fst_ord, name) Eq.t;
    eqsnd : (snd_ord, axiom) Eq.t;

    sdf : SDF.t;
    uf : UF.t;

    i_subst_fst : (fst_ord, name) Subst.t;
    i_subst_snd : (snd_ord, axiom) Subst.t;

    i_subst_ground_snd : (snd_ord, axiom) Subst.t;

    sub_cons : Uniformity_Set.t;

    (*** Lists that help determining when the rule equality needs to be applied.
      - The list equality_constructor_checked represents the elements of SDF that have been check for
        the current SDF but no mgs was found. This list must be emptyed when a new element is added to SDF
        and its previous content should be put in equality_constructor_to_checked.
      - The list equality_constructor_to_checked represents the elements of SDF that haven't been check to apply the rule equality (for constructor)
        or for which an equality fomula exists in UF but hasn't been removed yet (i.e. all recipe equivalent formula in the set are not solved.)
      - An element of SDF not appearing in both lists means that either the first order term is a name or that
        an equality formula has been successfuly added in UF and then removed.
    *)
    equality_constructor_checked : Data_structure.id_recipe_equivalent list;
    equality_constructor_to_checked : Data_structure.id_recipe_equivalent list;

    (*** Similar behaviour for the list equality_to_checked. Note that when no mgs is found, the element is removed and never put back
      even if a new element of SDF is added (since all the second order variable in the equality formula have a type stricly smaller
      then any new added element in SDF). Finally, each id in the list represents the element of SDF that is compared with the
      last entry to SDF (all the other pair would have been checked by that time.)*)
    equality_to_checked : Data_structure.id_recipe_equivalent list;

    skeletons_checked : (Data_structure.id_recipe_equivalent * int) list;
    skeletons_to_check : (Data_structure.id_recipe_equivalent * int) list;

    history_skeleton : history_skeleton list
  }

module Ordered_Snd_Ord_Variable = struct

  type t = snd_ord_variable

  let compare = Variable.order Recipe

end

exception Bot

(******** Access functions ********)

let get_vars_Term = get_vars_with_list

let get_names_Term = get_names_with_list

let get_axioms_Term = get_axioms_with_list

let get_additional_data csys = csys.additional_data

let get_substitution_solution (type a) (type b) (at: (a,b) atom) csys = match at with
  | Protocol -> (csys.i_subst_fst : (a,b) Subst.t)
  | Recipe -> ((Subst.union csys.i_subst_snd csys.i_subst_ground_snd) : (a,b) Subst.t)

let get_vars_with_list (type a) (type b) (at: (a,b) atom) csys (vars_l: (a,b) variable list) =
  let result_vars = ref vars_l in

  match at with
    | Protocol ->
        DF.iter csys.df (fun bfct -> result_vars := get_vars_with_list Protocol (BasicFact.get_protocol_term bfct) (fun _ -> true) !result_vars);
        result_vars := Eq.get_vars_with_list Protocol csys.eqfst !result_vars;
        SDF.iter csys.sdf (fun fct -> result_vars := get_vars_with_list Protocol (Fact.get_protocol_term fct) (fun _-> true) !result_vars);
        UF.iter Fact.Deduction csys.uf (fun psi -> result_vars := Fact.get_vars_with_list Protocol Fact.Deduction psi (fun _ -> true) !result_vars);
        UF.iter Fact.Equality csys.uf (fun psi -> result_vars := Fact.get_vars_with_list Protocol Fact.Equality psi (fun _ -> true) !result_vars);
        result_vars := Subst.get_vars_with_list Protocol csys.i_subst_fst (fun _ -> true) !result_vars;
        Uniformity_Set.iter csys.sub_cons (fun _ t -> result_vars := get_vars_with_list Protocol t (fun _ -> true) !result_vars);
        !result_vars
    | Recipe ->
        DF.iter csys.df (fun bfct -> result_vars := get_vars_with_list Recipe (of_variable (BasicFact.get_snd_ord_variable bfct)) (fun _ -> true) !result_vars);
        result_vars := Eq.get_vars_with_list Recipe csys.eqsnd !result_vars;
        SDF.iter csys.sdf (fun fct -> result_vars := get_vars_with_list Recipe (Fact.get_recipe fct) (fun _-> true) !result_vars);
        UF.iter Fact.Deduction csys.uf (fun psi -> result_vars := Fact.get_vars_with_list Recipe Fact.Deduction psi (fun _ -> true) !result_vars);
        UF.iter Fact.Equality csys.uf (fun psi -> result_vars := Fact.get_vars_with_list Recipe Fact.Equality psi (fun _ -> true) !result_vars);
        result_vars := Subst.get_vars_with_list Recipe csys.i_subst_ground_snd (fun _ -> true) !result_vars;
        result_vars := Subst.get_vars_with_list Recipe csys.i_subst_snd (fun _ -> true) !result_vars;
        Uniformity_Set.iter csys.sub_cons (fun r _ -> result_vars := get_vars_with_list Recipe r (fun _ -> true) !result_vars);
        !result_vars

let get_names_with_list csys names_l =
  let result_vars = ref names_l in

  DF.iter csys.df (fun bfct -> result_vars := get_names_with_list Protocol (BasicFact.get_protocol_term bfct) !result_vars);
  result_vars := Eq.get_names_with_list Protocol csys.eqfst !result_vars;
  SDF.iter csys.sdf (fun fct ->
    result_vars := get_names_with_list Protocol (Fact.get_protocol_term fct) !result_vars
  );
  UF.iter Fact.Deduction csys.uf (fun psi -> result_vars := Fact.get_names_with_list Fact.Deduction psi !result_vars);
  UF.iter Fact.Equality csys.uf (fun psi -> result_vars := Fact.get_names_with_list Fact.Equality psi !result_vars);
  result_vars := Subst.get_names_with_list Protocol csys.i_subst_fst !result_vars;
  Uniformity_Set.iter csys.sub_cons (fun _ t -> result_vars := get_names_with_list Protocol t !result_vars);
  !result_vars

let get_axioms_with_list csys ax_list =
  let result = ref ax_list in

  SDF.iter_within_var_type 0 csys.sdf (fun fct ->
    result := get_axioms_with_list (Fact.get_recipe fct) (fun _ -> true) !result
  );
  !result

(******** Scanning *****)

let is_solved csys = Tools.is_df_solved csys.df

let is_uniformity_rule_applicable csys =
  Uniformity_Set.exists_pair_with_same_protocol_term csys.sub_cons (Eq.implies Recipe csys.eqsnd)

(******** Display *******)

let id_class_csys =
  let acc = ref 0 in
  let f () =
    incr acc;
    !acc
  in
  f

let display out ?(rho=None) ?(hidden=false) ?(id=0) csys = match out with
  | HTML ->
      let str = ref "" in
      let id_j = id_class_csys () in
      let id_s = if id = 0 then "" else "_"^(string_of_int id) in
      let style =
        if hidden
        then " style=\"display:none;\""
        else ""
      in

      let display_subst_eq_fst =
        let equations = Subst.equations_of csys.i_subst_fst in
        match equations = [], Eq.is_top csys.eqfst with
          | true, true -> top Latex
          | true, false -> Eq.display Latex ~rho:rho Protocol csys.eqfst
          | false, true -> display_list (fun (x,t) -> Printf.sprintf "%s %s %s" (display Latex ~rho:rho Protocol x) (eqs Latex) (display Latex ~rho:rho Protocol t)) (Printf.sprintf " %s " (wedge Latex)) equations
          | _,_ ->
              (Eq.display Latex ~rho:rho Protocol csys.eqfst)^
              " "^(wedge Latex)^" "^
              (display_list (fun (x,t) -> Printf.sprintf "%s %s %s" (display Latex ~rho:rho Protocol x) (eqs Latex) (display Latex ~rho:rho Protocol t)) (Printf.sprintf " %s " (wedge Latex)) equations)
      in
      let display_subst_eq_snd =
        let equations = Subst.equations_of csys.i_subst_snd in
        match equations = [], Eq.is_top csys.eqsnd with
          | true, true -> top Latex
          | true, false -> Eq.display Latex ~rho:rho Recipe csys.eqsnd
          | false, true -> display_list (fun (x,t) -> Printf.sprintf "%s %s %s" (display Latex ~rho:rho Recipe x) (eqs Latex) (display Latex ~rho:rho Recipe t)) (Printf.sprintf " %s " (wedge Latex)) equations
          | _,_ ->
              (Eq.display Latex ~rho:rho Recipe csys.eqsnd)^
              " "^(wedge Latex)^" "^
              (display_list (fun (x,t) -> Printf.sprintf "%s %s %s" (display Latex ~rho:rho Recipe x) (eqs Latex) (display Latex ~rho:rho Recipe t)) (Printf.sprintf " %s " (wedge Latex)) equations)
      in

      let link_Phi = Printf.sprintf "<a href=\"javascript:show_single('Phi%d');\">\\(\\Phi%s\\)</a>"  id_j id_s in
      let link_Df = Printf.sprintf "<a href=\"javascript:show_single('Df%d');\">\\({\\sf D}%s\\)</a>" id_j id_s in
      let link_Sdf = Printf.sprintf "<a href=\"javascript:show_single('Sdf%d');\">\\({\\sf SDF}%s\\)</a>" id_j id_s in
      let link_Uf = Printf.sprintf "<a href=\"javascript:show_single('Uf%d');\">\\({\\sf UF}%s\\)</a>" id_j id_s in
      let link_Eq1 = Printf.sprintf "<a href=\"javascript:show_single('Equn%d');\">\\({\\sf E}^1%s\\)</a>" id_j id_s in
      let link_Eq2 = Printf.sprintf "<a href=\"javascript:show_single('Eqdeux%d');\">\\({\\sf E}^2%s\\)</a>" id_j id_s in
      let link_Uni = Printf.sprintf "<a href=\"javascript:show_single('Uni%d');\">\\({\\sf R}%s\\)</a>" id_j id_s in

      str := Printf.sprintf "\\( \\mathcal{C}%s =~(\\)%s, %s, %s, %s, %s, %s, %s\\()\\) &nbsp;&nbsp;&nbsp; <a href=\"javascript:show_class('csys%d');\">All</a>\n"
        id_s link_Phi link_Df link_Eq1 link_Eq2 link_Sdf link_Uf link_Uni id_j;

      str := Printf.sprintf "%s            <div class=\"csys\">\n" !str;
      str := Printf.sprintf "%s              <div class=\"elt_csys\"><div id=\"Df%d\" class=\"csys%d\"%s>\\({\\sf D}%s = %s\\)</div></div>\n" !str id_j id_j style id_s (DF.display Latex ~rho:rho csys.df);
      str := Printf.sprintf "%s              <div class=\"elt_csys\"><div id=\"Equn%d\" class=\"csys%d\"%s>\\({\\sf E}^1%s = %s\\)</div></div>\n" !str id_j id_j style id_s display_subst_eq_fst;
      str := Printf.sprintf "%s              <div class=\"elt_csys\"><div id=\"Eqdeux%d\" class=\"csys%d\"%s>\\({\\sf E}^2%s = %s\\)</div></div>\n" !str id_j id_j style id_s display_subst_eq_snd;
      str := Printf.sprintf "%s              <div class=\"elt_csys\"><div id=\"Sdf%d\" class=\"csys%d\"%s>\\({\\sf SDF}%s = %s\\)</div></div>\n" !str id_j id_j style id_s (SDF.display Latex ~rho:rho csys.sdf);
      str := Printf.sprintf "%s              <div class=\"elt_csys\"><div id=\"Uf%d\" class=\"csys%d\"%s>\\({\\sf UF}%s = %s\\)</div></div>\n" !str id_j id_j style id_s (UF.display Latex ~rho:rho csys.uf);
      str := Printf.sprintf "%s              <div class=\"elt_csys\"><div id=\"Uni%d\" class=\"csys%d\"%s>\\({\\sf R}%s = %s\\)</div></div>\n" !str id_j id_j style id_s (Uniformity_Set.display Latex ~rho:rho csys.sub_cons);

      Printf.sprintf "%s            </div>\n" !str

  | _ -> Config.internal_error "[constraint_system.ml >> display] This display mode is not implemented yet."

(********* Generators *********)

let generate_history f =
  let rec generate_vars fst_vars snd_vars = function
    | 0 -> fst_vars, snd_vars
    | n ->
        let x_fst = Variable.fresh Protocol Existential Variable.fst_ord_type in
        let x_snd = Variable.fresh Recipe Existential Variable.infinite_snd_ord_type in
        generate_vars (x_fst::fst_vars) (x_snd::snd_vars) (n-1)
  in

  let (fst_vars, snd_vars) = generate_vars [] [] (Symbol.get_arity f) in

  {
    destructor = f;
    fst_vars = fst_vars;
    snd_vars = snd_vars;
    diseq = Eq.Mixed.top
  }

let empty data =

  {
    additional_data = data;

    size_frame = 0;

    df = DF.empty;

    private_channels = [];

    eqfst = Eq.top;
    eqsnd = Eq.top;

    sdf = SDF.empty;
    uf = UF.empty;

    i_subst_fst = Subst.identity;
    i_subst_snd = Subst.identity;

    i_subst_ground_snd = Subst.identity;

    sub_cons = Uniformity_Set.empty;

    equality_constructor_checked = [];
    equality_constructor_to_checked = [];

    equality_to_checked = [];

    skeletons_checked = [];
    skeletons_to_check = [];

    history_skeleton = List.rev_map generate_history !Symbol.all_destructors
  }

let apply_substitution csys subst =
  Config.debug (fun () ->
    if not (Subst.is_extended_by Protocol csys.i_subst_fst subst)
    then Config.internal_error "[constraint_system.ml >> apply_substitution] The  substitution of the constraint system should be extended by the substitution given as argument.";

    if csys.private_channels <> []
    then Config.internal_error "[constraint_system.ml >> apply_substitution] The private channels should be added after applying the substitution."
  );

  let new_df = DF.apply csys.df subst
  and new_eqfst = Eq.apply Protocol csys.eqfst subst in

  if Eq.is_bot new_eqfst
  then raise Bot;

  let new_sdf = SDF.apply csys.sdf Subst.identity subst
  and new_uf = UF.apply csys.uf Subst.identity subst
  and new_i_subst_fst = Subst.restrict subst (fun x -> Variable.quantifier_of x = Free)
  and new_sub_cons = Uniformity_Set.apply csys.sub_cons Subst.identity subst
  and new_history =
    List.fold_left (fun acc hist ->
      { hist with diseq = Eq.Mixed.apply hist.diseq subst Subst.identity }::acc
    ) [] csys.history_skeleton
  in

  let new_csys =
    { csys with
      df = new_df;
      eqfst = new_eqfst;
      sdf = new_sdf;
      uf = new_uf;
      i_subst_fst = new_i_subst_fst;
      sub_cons = new_sub_cons;
      history_skeleton = new_history
    }
  in

  if is_uniformity_rule_applicable new_csys
  then raise Bot
  else new_csys

let add_basic_fact csys bfct =
  Config.debug (fun () ->
    let t = BasicFact.get_protocol_term bfct in

    let t' = Subst.apply csys.i_subst_fst t (fun x f -> f x) in

    if not (is_equal Protocol t t')
    then Config.internal_error "[constraint_system.ml >> add_basic_fact] The substitution of the constraint system should not instantiate the protocol term of the basic deduction fact."
  );

  { csys with
      df = DF.add csys.df bfct;
      sub_cons = Uniformity_Set.add csys.sub_cons (of_variable (BasicFact.get_snd_ord_variable bfct)) (BasicFact.get_protocol_term bfct)
  }

let add_disequations (type a) (type b) (at: (a,b) atom) csys (diseq_list: (a,b) Diseq.t list) = match at with
  | Protocol ->
      { csys with
        eqfst = List.fold_left (fun acc diseq -> Eq.wedge acc diseq) csys.eqfst diseq_list
      }
  | Recipe ->
      let new_csys =
        { csys with
          eqsnd = List.fold_left (fun acc diseq -> Eq.wedge acc diseq) csys.eqsnd diseq_list
        }
      in
      if is_uniformity_rule_applicable new_csys
      then raise Bot
      else new_csys

let add_axiom csys ax t =
  Config.debug (fun () ->
    if csys.size_frame + 1 <> Axiom.index_of ax
    then Config.internal_error "[constraint_system.ml >> add_axiom] The axiom given as argument should have an index equal to the size of the frame + 1";

    if csys.skeletons_to_check <> []
    then Config.internal_error "[constraint_system.ml >> add_axiom] All skeletons should have been checked."
  );

  let new_size = csys.size_frame + 1 in

  { csys with
    uf = UF.add_deduction csys.uf [Fact.create Fact.Deduction (Fact.create_deduction_fact (of_axiom ax) t) []];
    size_frame = new_size
  }

let instantiate_when_solved csys =
  Config.debug (fun () ->
    if not (is_solved csys)
    then Config.internal_error "[constraint_system.ml >> instantiate_when_solved] The constraint system should be solved."
  );

  let subst_fst, subst_snd =
    DF.fold (fun (acc_fst,acc_snd) bfct ->
      let k = Symbol.fresh_attacker_name () in
      let fst = Subst.create Protocol (variable_of (BasicFact.get_protocol_term bfct)) (apply_function k []) in
      let snd = Subst.create Recipe (BasicFact.get_snd_ord_variable bfct) (apply_function k []) in
      (Subst.compose acc_fst fst, Subst.compose acc_snd snd)
    ) (Subst.identity, Subst.identity) csys.df
  in

  (Subst.compose csys.i_subst_fst subst_fst, Subst.union csys.i_subst_ground_snd (Subst.compose csys.i_subst_snd subst_snd))

let add_private_channels csys pr_ch_l =
  Config.debug (fun () ->
    if csys.private_channels <> []
    then Config.internal_error "[constraint_system.ml >> add_private_channels] The current list should be empty."
  );
  { csys with private_channels = pr_ch_l }

let replace_additional_data csys data = { csys with additional_data = data }

let rec replace_history symb f_replace = function
  | [] -> Config.internal_error "[constraint_system.ml >> replace_history] Unexpected case"
  | hist::q when hist.destructor == symb -> (f_replace hist)::q
  | hist::q -> hist::(replace_history symb f_replace q)

(*****************************************
***       Most general solutions       ***
******************************************)

type simple =
  {
    simp_DF : DF.t;
    simp_EqFst : (fst_ord, name) Eq.t;
    simp_EqSnd : (snd_ord, axiom) Eq.t;
    simp_SDF : SDF.t;
    simp_Sub_Cons : Uniformity_Set.t;
    simp_Mixed_Eq : Eq.Mixed.t
  }

type mgs = (snd_ord, axiom) Subst.t * snd_ord_variable list

module Set_Snd_Ord_Variable = Set.Make(Ordered_Snd_Ord_Variable)

(**** Display *****)

let display_mgs out ?(rho=None) (subst,v_list) = match out with
  | Testing -> Printf.sprintf "({%s},%s)"
      (display_list (Variable.display out ~rho:rho Recipe ~v_type:false) ", " v_list)
      (Subst.display out ~rho:rho Recipe subst)
  | _ ->
      if v_list = []
      then Subst.display out ~rho:rho Recipe subst
      else
        Printf.sprintf "%s %s.%s"
          (exists out)
          (display_list (Variable.display out ~rho:rho Recipe ~v_type:true) ", " v_list)
          (Subst.display out ~rho:rho Recipe subst)

let display_simple out ?(rho=None) ?(hidden=false) ?(id=0) csys = match out with
  | Testing ->
      Printf.sprintf "( %s, %s, %s, %s, %s )"
        (DF.display out ~rho:rho csys.simp_DF)
        (Eq.display out ~rho:rho Protocol csys.simp_EqFst)
        (Eq.display out ~rho:rho Recipe csys.simp_EqSnd)
        (SDF.display out ~rho:rho csys.simp_SDF)
        (Uniformity_Set.display out ~rho:rho csys.simp_Sub_Cons)
  | HTML ->
      let str = ref "" in
      let id_j = id_class_csys () in
      let id_s = if id = 0 then "" else "_"^(string_of_int id) in
      let style =
        if hidden
        then " style=\"display:none;\""
        else ""
      in

      let link_Df = Printf.sprintf "<a href=\"javascript:show_single('Df%d');\">\\({\\sf D}%s\\)</a>" id_j id_s in
      let link_Sdf = Printf.sprintf "<a href=\"javascript:show_single('Sdf%d');\">\\({\\sf SDF}%s\\)</a>" id_j id_s in
      let link_Eq1 = Printf.sprintf "<a href=\"javascript:show_single('Equn%d');\">\\({\\sf E}^1%s\\)</a>" id_j id_s in
      let link_Eq2 = Printf.sprintf "<a href=\"javascript:show_single('Eqdeux%d');\">\\({\\sf E}^2%s\\)</a>" id_j id_s in
      let link_Uni = Printf.sprintf "<a href=\"javascript:show_single('Uni%d');\">\\({\\sf R}%s\\)</a>" id_j id_s in

      str := Printf.sprintf "\\( \\mathcal{C}%s =~(\\)%s, %s, %s, %s, %s\\()\\) &nbsp;&nbsp;&nbsp; <a href=\"javascript:show_class('csys%d');\">All</a>\n"
        id_s link_Df link_Eq1 link_Eq2 link_Sdf link_Uni id_j;

      str := Printf.sprintf "%s            <div class=\"csys\">\n" !str;
      str := Printf.sprintf "%s              <div class=\"elt_csys\"><div id=\"Df%d\" class=\"csys%d\"%s>\\({\\sf D}%s = %s\\)</div></div>\n" !str id_j id_j style id_s (DF.display Latex ~rho:rho csys.simp_DF);
      str := Printf.sprintf "%s              <div class=\"elt_csys\"><div id=\"Equn%d\" class=\"csys%d\"%s>\\({\\sf E}^1%s = %s\\)</div></div>\n" !str id_j id_j style id_s (Eq.display Latex ~rho:rho Protocol csys.simp_EqFst);
      str := Printf.sprintf "%s              <div class=\"elt_csys\"><div id=\"Eqdeux%d\" class=\"csys%d\"%s>\\({\\sf E}^2%s = %s\\)</div></div>\n" !str id_j id_j style id_s (Eq.display Latex ~rho:rho Recipe csys.simp_EqSnd);
      str := Printf.sprintf "%s              <div class=\"elt_csys\"><div id=\"Sdf%d\" class=\"csys%d\"%s>\\({\\sf SDF}%s = %s\\)</div></div>\n" !str id_j id_j style id_s (SDF.display Latex ~rho:rho csys.simp_SDF);
      str := Printf.sprintf "%s              <div class=\"elt_csys\"><div id=\"Uni%d\" class=\"csys%d\"%s>\\({\\sf R}%s = %s\\)</div></div>\n" !str id_j id_j style id_s (Uniformity_Set.display Latex ~rho:rho csys.simp_Sub_Cons);

      Printf.sprintf "%s            </div>\n" !str
  | _ -> Config.internal_error "[constraint_system.ml >> display] This display mode is not implemented yet."

(***** Generators ******)

let substitution_of_mgs (subst,_) = subst

let mgs csys =
  let accumulator = ref [] in

  let rec apply_rules csys mgs fst_ord_mgs snd_ord_vars f_next =

    let test_not_solved basic_fct =
      if not (is_variable (BasicFact.get_protocol_term basic_fct))
      then Some basic_fct
      else None
    in

    let apply_res basic_fct fct f_next =
      let b_term = BasicFact.get_protocol_term basic_fct
      and b_recipe = BasicFact.get_snd_ord_variable basic_fct
      and term = Fact.get_protocol_term fct
      and recipe = Fact.get_recipe fct in

      let unif_opt =
        if var_occurs b_recipe recipe
        then None
        else
          try
            Some(Subst.unify Protocol [(b_term,term)],Subst.create Recipe b_recipe recipe)
          with
            | Subst.Not_unifiable -> None
      in

      match unif_opt with
        | None -> f_next ()
        | Some(subst_fst,subst_snd) ->

            let new_eq_fst = Eq.apply Protocol csys.simp_EqFst subst_fst in
            if Eq.is_bot new_eq_fst
            then f_next ()
            else
              let new_eq_snd = Eq.apply Recipe csys.simp_EqSnd subst_snd in
              if Eq.is_bot new_eq_snd
              then f_next ()
              else
                let new_mixed = Eq.Mixed.apply csys.simp_Mixed_Eq subst_fst subst_snd in
                if Eq.Mixed.is_bot new_mixed
                then f_next ()
                else
                  begin
                    let df_1 = DF.remove csys.simp_DF b_recipe in
                    let df_2 = DF.apply df_1 subst_fst in

                    Config.debug (fun () ->
                      if not (Uniformity_Set.exists csys.simp_Sub_Cons (of_variable b_recipe) b_term)
                      then Config.internal_error "[Constraint_system.ml >> mgs] Elements of DF should always be in the uniformity set."
                    );
                    (*let sub_cons_1 = Uniformity_Set.add csys.simp_Sub_Cons recipe term in*)
                    let sub_cons_2 = Uniformity_Set.apply csys.simp_Sub_Cons subst_snd subst_fst in

                    let csys' = {
                        simp_DF = df_2;
                        simp_EqFst = new_eq_fst;
                        simp_EqSnd = new_eq_snd;
                        simp_SDF = SDF.apply csys.simp_SDF subst_snd subst_fst;
                        simp_Sub_Cons = sub_cons_2;
                        simp_Mixed_Eq = new_mixed
                      }

                    in

                    let mgs' = Subst.apply subst_snd mgs (fun mgs f -> List.fold_left (fun acc (x,r) -> (x,f r)::acc) [] mgs)
                    and snd_ord_vars' = Set_Snd_Ord_Variable.remove b_recipe snd_ord_vars in
                    (apply_rules [@tailcall]) csys' mgs' (Subst.compose fst_ord_mgs subst_fst) snd_ord_vars' f_next
                  end
    in

    let apply_cons basic_fct f_next =
      let term = BasicFact.get_protocol_term basic_fct
      and x_snd = BasicFact.get_snd_ord_variable basic_fct in

      if is_name term
      then f_next ()
      else
        let symb = root term in
        if Symbol.is_public symb
        then
          let arity = Symbol.get_arity symb in

          if arity = 0
          then
            let recipe = apply_function symb [] in
            let subst = Subst.create Recipe x_snd recipe in
            let new_eq_snd = Eq.apply Recipe csys.simp_EqSnd subst in
            if Eq.is_bot new_eq_snd
            then f_next ()
            else
              let new_mixed = Eq.Mixed.apply csys.simp_Mixed_Eq Subst.identity subst in
              if Eq.Mixed.is_bot new_mixed
              then f_next ()
              else
                let df_1 = DF.remove csys.simp_DF x_snd in
                let sub_cons_1 = Uniformity_Set.apply csys.simp_Sub_Cons subst Subst.identity in
                let csys' =
                  { csys with
                      simp_DF = df_1;
                      simp_EqSnd = new_eq_snd;
                      simp_SDF = SDF.apply csys.simp_SDF subst Subst.identity;
                      simp_Sub_Cons = sub_cons_1;
                      simp_Mixed_Eq = new_mixed
                  }
                in

                let mgs' = Subst.apply subst mgs (fun mgs f -> List.fold_left (fun acc (x,r) -> (x,f r)::acc) [] mgs)
                and snd_ord_vars' = Set_Snd_Ord_Variable.remove x_snd snd_ord_vars in
                (apply_rules [@tailcall]) csys' mgs' fst_ord_mgs snd_ord_vars' f_next
          else
            begin
              let args_of_term = get_args term in

              let vars_snd = Variable.fresh_list Recipe Existential (Variable.snd_ord_type (Variable.type_of x_snd)) arity in
              let vars_snd_as_term = List.map of_variable vars_snd in

              let recipe = apply_function symb vars_snd_as_term in
              let subst = Subst.create Recipe x_snd recipe in

              let new_eq_snd = Eq.apply Recipe csys.simp_EqSnd subst in
              if Eq.is_bot new_eq_snd
              then f_next ()
              else
                let new_mixed = Eq.Mixed.apply csys.simp_Mixed_Eq Subst.identity subst in
                if Eq.Mixed.is_bot new_mixed
                then f_next ()
                else
                  let ded_fact_list = List.map2 BasicFact.create vars_snd args_of_term in

                  let df_1 = DF.remove csys.simp_DF x_snd in
                  let df_2 = List.fold_left (fun df b_fct -> DF.add df b_fct) df_1 ded_fact_list in

                  let sub_cons_1 = Uniformity_Set.apply csys.simp_Sub_Cons subst Subst.identity in
                  let sub_cons_2 = List.fold_left2 (fun subc x t -> Uniformity_Set.add subc x t) sub_cons_1  vars_snd_as_term args_of_term in

                  let csys' = { csys with
                      simp_DF = df_2;
                      simp_EqSnd = new_eq_snd;
                      simp_SDF = SDF.apply csys.simp_SDF subst Subst.identity;
                      simp_Sub_Cons = sub_cons_2;
                      simp_Mixed_Eq = new_mixed
                    }
                  in

                  let mgs' = Subst.apply subst mgs (fun mgs f -> List.fold_left (fun acc (x,r) -> (x,f r)::acc) [] mgs)
                  and snd_ord_vars' = Set_Snd_Ord_Variable.remove x_snd snd_ord_vars in
                  let snd_ord_vars'' = List.fold_left (fun set x -> Set_Snd_Ord_Variable.add x set) snd_ord_vars' vars_snd in

                  (apply_rules [@tailcall]) csys' mgs' fst_ord_mgs snd_ord_vars'' f_next
            end
        else f_next ()
    in

    match Uniformity_Set.unify_multiple_opt csys.simp_Sub_Cons with
      | None -> f_next ()
      | Some(subst,uniset) ->
          if Subst.is_identity subst
          then
            match DF.find csys.simp_DF test_not_solved with
              | None -> accumulator := (mgs,fst_ord_mgs,Set_Snd_Ord_Variable.elements snd_ord_vars,csys) :: !accumulator; f_next ()
              | Some basic_fct ->
                  if Variable.has_infinite_type (BasicFact.get_snd_ord_variable basic_fct)
                  then (SDF.tail_iter [@tailcall]) csys.simp_SDF (apply_res basic_fct) (fun () -> (apply_cons [@tailcall]) basic_fct f_next)
                  else (SDF.tail_iter_within_var_type [@tailcall]) (Variable.type_of (BasicFact.get_snd_ord_variable basic_fct)) csys.simp_SDF (apply_res basic_fct) (fun () -> (apply_cons [@tailcall]) basic_fct f_next)
          else
            let new_eqsnd = Eq.apply Recipe csys.simp_EqSnd subst in
            if Eq.is_bot new_eqsnd
            then f_next ()
            else
              let new_mixed = Eq.Mixed.apply csys.simp_Mixed_Eq Subst.identity subst in
              if Eq.Mixed.is_bot new_mixed
              then f_next ()
              else
                let new_df,snd_ord_vars' = Subst.fold (fun (df,snd_ord) x _ -> DF.remove df x, Set_Snd_Ord_Variable.remove x snd_ord) (csys.simp_DF,snd_ord_vars) subst in
                let mgs' = Subst.apply subst mgs (fun mgs f -> List.fold_left (fun acc (x,r) -> (x,f r)::acc) [] mgs) in
                let csys' =
                  { csys with
                    simp_DF = new_df;
                    simp_EqSnd = new_eqsnd;
                    simp_SDF = SDF.apply csys.simp_SDF subst Subst.identity;
                    simp_Sub_Cons = uniset;
                    simp_Mixed_Eq = new_mixed
                  }
                in
                match DF.find csys'.simp_DF test_not_solved with
                  | None -> accumulator := (mgs',fst_ord_mgs,Set_Snd_Ord_Variable.elements snd_ord_vars',csys') :: !accumulator; f_next ()
                  | Some basic_fct ->
                      if Variable.has_infinite_type (BasicFact.get_snd_ord_variable basic_fct)
                      then (SDF.tail_iter [@tailcall]) csys'.simp_SDF (apply_res basic_fct) (fun () -> (apply_cons [@tailcall]) basic_fct f_next)
                      else (SDF.tail_iter_within_var_type [@tailcall]) (Variable.type_of (BasicFact.get_snd_ord_variable basic_fct)) csys'.simp_SDF (apply_res basic_fct) (fun () -> (apply_cons [@tailcall]) basic_fct f_next)
  in

  (* We first check if the constraint is not directly bot *)

  if Eq.is_bot csys.simp_EqFst || Eq.is_bot csys.simp_EqSnd || Eq.Mixed.is_bot csys.simp_Mixed_Eq
  then []
  else
    begin
      let init_mgs = DF.fold (fun acc b_fct ->
        let x = BasicFact.get_snd_ord_variable b_fct in
        (x, of_variable x)::acc
        ) [] csys.simp_DF
      in

      apply_rules csys init_mgs Subst.identity Set_Snd_Ord_Variable.empty (fun () -> ());
      List.fold_left (fun acc_mgs (mgs,fst_ord_mgs,var_list,csys') ->
        ((Subst.create_multiple Recipe (List.fold_left (fun acc (r_1,r_2) -> if is_equal Recipe (of_variable r_1) r_2 then acc else (r_1,r_2)::acc) [] mgs), var_list), fst_ord_mgs, csys')::acc_mgs
        ) [] !accumulator
    end

exception Found_mgs of (snd_ord_variable * recipe) list * (fst_ord, name) Subst.t * (snd_ord_variable list)  * simple

let one_mgs csys =
  let rec apply_rules csys mgs fst_ord_mgs snd_ord_vars f_next =

    let test_not_solved basic_fct =
      if not (is_variable (BasicFact.get_protocol_term basic_fct))
      then Some basic_fct
      else None
    in

    let apply_res basic_fct fct f_next =
      let b_term = BasicFact.get_protocol_term basic_fct
      and b_recipe = BasicFact.get_snd_ord_variable basic_fct
      and term = Fact.get_protocol_term fct
      and recipe = Fact.get_recipe fct in

      let unif_opt =
        if var_occurs b_recipe recipe
        then None
        else
          try
            Some(Subst.unify Protocol [(b_term,term)],Subst.create Recipe b_recipe recipe)
          with
          | Subst.Not_unifiable -> None
      in

      match unif_opt with
        | None -> f_next ()
        | Some(subst_fst,subst_snd) ->

            let new_eq_fst = Eq.apply Protocol csys.simp_EqFst subst_fst in
            if Eq.is_bot new_eq_fst
            then f_next ()
            else
              let new_eq_snd = Eq.apply Recipe csys.simp_EqSnd subst_snd in
              if Eq.is_bot new_eq_snd
              then f_next ()
              else
                let new_mixed = Eq.Mixed.apply csys.simp_Mixed_Eq subst_fst subst_snd in
                if Eq.Mixed.is_bot new_mixed
                then f_next ()
                else
                  let df_1 = DF.remove csys.simp_DF b_recipe in
                  let df_2 = DF.apply df_1 subst_fst in

                  (*let sub_cons_1 = Uniformity_Set.add csys.simp_Sub_Cons recipe term in*)
                  let sub_cons_2 = Uniformity_Set.apply csys.simp_Sub_Cons subst_snd subst_fst in

                  let csys' = {
                      simp_DF = df_2;
                      simp_EqFst = new_eq_fst;
                      simp_EqSnd = new_eq_snd;
                      simp_SDF = SDF.apply csys.simp_SDF subst_snd subst_fst;
                      simp_Sub_Cons = sub_cons_2;
                      simp_Mixed_Eq = new_mixed
                    }

                  in

                  let mgs' = Subst.apply subst_snd mgs (fun mgs f -> List.fold_left (fun acc (x,r) -> (x,f r)::acc) [] mgs)
                  and snd_ord_vars' = Set_Snd_Ord_Variable.remove b_recipe snd_ord_vars in
                  (apply_rules [@tailcall]) csys' mgs' (Subst.compose fst_ord_mgs subst_fst) snd_ord_vars' f_next
    in

    let apply_cons basic_fct f_next =
      let term = BasicFact.get_protocol_term basic_fct
      and x_snd = BasicFact.get_snd_ord_variable basic_fct in

      if is_name term
      then f_next ()
      else
        let symb = root term in
        if Symbol.is_public symb
        then
          let arity = Symbol.get_arity symb in

          if arity = 0
          then
            let recipe = apply_function symb [] in
            let subst = Subst.create Recipe x_snd recipe in

            let new_eq_snd = Eq.apply Recipe csys.simp_EqSnd subst in
            if Eq.is_bot new_eq_snd
            then f_next ()
            else
              let new_mixed = Eq.Mixed.apply csys.simp_Mixed_Eq Subst.identity subst in
              if Eq.Mixed.is_bot new_mixed
              then f_next ()
              else
                let df_1 = DF.remove csys.simp_DF x_snd in
                let sub_cons_1 = Uniformity_Set.apply csys.simp_Sub_Cons subst Subst.identity in
                let csys' =
                  { csys with
                      simp_DF = df_1;
                      simp_EqSnd = new_eq_snd;
                      simp_SDF = SDF.apply csys.simp_SDF subst Subst.identity;
                      simp_Sub_Cons = sub_cons_1;
                      simp_Mixed_Eq = new_mixed
                  }
                in

                let mgs' = Subst.apply subst mgs (fun mgs f -> List.fold_left (fun acc (x,r) -> (x,f r)::acc) [] mgs)
                and snd_ord_vars' = Set_Snd_Ord_Variable.remove x_snd snd_ord_vars in
                (apply_rules [@tailcall]) csys' mgs' fst_ord_mgs snd_ord_vars' f_next
          else
            let args_of_term = get_args term in

            let vars_snd = Variable.fresh_list Recipe Existential (Variable.snd_ord_type (Variable.type_of x_snd)) arity in
            let vars_snd_as_term = List.map of_variable vars_snd in

            let recipe = apply_function symb vars_snd_as_term in
            let subst = Subst.create Recipe x_snd recipe in

            let new_eq_snd = Eq.apply Recipe csys.simp_EqSnd subst in
            if Eq.is_bot new_eq_snd
            then f_next ()
            else
              let new_mixed = Eq.Mixed.apply csys.simp_Mixed_Eq Subst.identity subst in
              if Eq.Mixed.is_bot new_mixed
              then f_next ()
              else
                let ded_fact_list = List.map2 BasicFact.create vars_snd args_of_term in

                let df_1 = DF.remove csys.simp_DF x_snd in
                let df_2 = List.fold_left (fun df b_fct -> DF.add df b_fct) df_1 ded_fact_list in

                let sub_cons_1 = Uniformity_Set.apply csys.simp_Sub_Cons subst Subst.identity in
                let sub_cons_2 = List.fold_left2 (fun subc x t -> Uniformity_Set.add subc x t) sub_cons_1  vars_snd_as_term args_of_term in

                let csys' = { csys with
                    simp_DF = df_2;
                    simp_EqSnd = new_eq_snd;
                    simp_SDF = SDF.apply csys.simp_SDF subst Subst.identity;
                    simp_Sub_Cons = sub_cons_2;
                    simp_Mixed_Eq = new_mixed
                  }
                in

                let mgs' = Subst.apply subst mgs (fun mgs f -> List.fold_left (fun acc (x,r) -> (x,f r)::acc) [] mgs)
                and snd_ord_vars' = Set_Snd_Ord_Variable.remove x_snd snd_ord_vars in
                let snd_ord_vars'' = List.fold_left (fun set x -> Set_Snd_Ord_Variable.add x set) snd_ord_vars' vars_snd in

                (apply_rules [@tailcall]) csys' mgs' fst_ord_mgs snd_ord_vars'' f_next
        else f_next ()
    in

    match Uniformity_Set.unify_multiple_opt csys.simp_Sub_Cons with
      | None -> f_next ()
      | Some(subst,uniset) ->
          if Subst.is_identity subst
          then
            match DF.find csys.simp_DF test_not_solved with
              | None -> raise (Found_mgs (mgs,fst_ord_mgs,Set_Snd_Ord_Variable.elements snd_ord_vars,csys))
              | Some basic_fct ->
                  if Variable.has_infinite_type (BasicFact.get_snd_ord_variable basic_fct)
                  then SDF.tail_iter csys.simp_SDF (apply_res basic_fct) (fun () -> (apply_cons [@tailcall]) basic_fct f_next)
                  else SDF.tail_iter_within_var_type (Variable.type_of (BasicFact.get_snd_ord_variable basic_fct)) csys.simp_SDF (apply_res basic_fct) (fun () -> (apply_cons [@tailcall]) basic_fct f_next)
          else
            let new_eqsnd = Eq.apply Recipe csys.simp_EqSnd subst in
            if Eq.is_bot new_eqsnd
            then f_next ()
            else
              let new_mixed = Eq.Mixed.apply csys.simp_Mixed_Eq Subst.identity subst in
              if Eq.Mixed.is_bot new_mixed
              then f_next ()
              else
                let new_df,snd_ord_vars' = Subst.fold (fun (df,snd_ord) x _ -> DF.remove df x, Set_Snd_Ord_Variable.remove x snd_ord) (csys.simp_DF,snd_ord_vars) subst in
                let mgs' = Subst.apply subst mgs (fun mgs f -> List.fold_left (fun acc (x,r) -> (x,f r)::acc) [] mgs) in
                let csys' =
                  { csys with
                    simp_DF = new_df;
                    simp_EqSnd = new_eqsnd;
                    simp_SDF = SDF.apply csys.simp_SDF subst Subst.identity;
                    simp_Sub_Cons = uniset;
                    simp_Mixed_Eq = new_mixed
                  }
                in
                match DF.find csys'.simp_DF test_not_solved with
                  | None -> raise (Found_mgs (mgs',fst_ord_mgs,Set_Snd_Ord_Variable.elements snd_ord_vars',csys'))
                  | Some basic_fct ->
                      if Variable.has_infinite_type (BasicFact.get_snd_ord_variable basic_fct)
                      then (SDF.tail_iter [@tailcall]) csys'.simp_SDF (apply_res basic_fct) (fun () -> (apply_cons [@tailcall]) basic_fct f_next)
                      else (SDF.tail_iter_within_var_type [@tailcall]) (Variable.type_of (BasicFact.get_snd_ord_variable basic_fct)) csys'.simp_SDF (apply_res basic_fct) (fun () -> (apply_cons [@tailcall]) basic_fct f_next)
  in

  (* We first check if the constraint is not directly bot *)

  if Eq.is_bot csys.simp_EqFst || Eq.is_bot csys.simp_EqSnd || Eq.Mixed.is_bot csys.simp_Mixed_Eq
  then raise Not_found
  else
    begin
      let init_mgs = DF.fold (fun acc b_fct ->
        let x = BasicFact.get_snd_ord_variable b_fct in
        (x, of_variable x)::acc
        ) [] csys.simp_DF
      in

      try
        apply_rules csys init_mgs Subst.identity Set_Snd_Ord_Variable.empty (fun () -> ());
        raise Not_found
      with
      | Found_mgs (mgs,fst_ord_mgs,var_list,csys') ->
          (Subst.create_multiple Recipe (List.filter_unordered (fun (r_1,r_2) -> not (is_equal Recipe (of_variable r_1) r_2)) mgs), var_list), fst_ord_mgs, csys'
    end

let simple_of csys =
  {
    simp_DF = csys.df;
    simp_EqFst = csys.eqfst;
    simp_EqSnd = csys.eqsnd;
    simp_SDF = csys.sdf;
    simp_Sub_Cons = csys.sub_cons;
    simp_Mixed_Eq = Eq.Mixed.top
  }

let simple_of_formula csys form =
  let fst_univ = Fact.universal_variables form in

  let mgu_hypothesis = Fact.get_mgu_hypothesis form in
  let fst_renaming = Variable.Renaming.fresh Protocol fst_univ Existential in

  let mgu_hypothesis_2 = Subst.compose_restricted mgu_hypothesis (Subst.of_renaming fst_renaming) in

  let df_0 = DF.apply csys.df mgu_hypothesis_2
  and eqfst_0 = Eq.apply Protocol csys.eqfst mgu_hypothesis_2
  and sdf_0 = SDF.apply csys.sdf Subst.identity mgu_hypothesis_2
  and sub_cons_0 = Uniformity_Set.apply csys.sub_cons Subst.identity mgu_hypothesis_2 in

  {
    simp_DF = df_0;
    simp_EqFst = eqfst_0;
    simp_EqSnd = csys.eqsnd;
    simp_SDF = sdf_0;
    simp_Sub_Cons = sub_cons_0;
    simp_Mixed_Eq = Eq.Mixed.top
  }

let simple_of_disequation csys diseq =

  let subst = Diseq.substitution_of diseq in

  let df_0 = DF.apply csys.df subst
  and eqfst_0 = Eq.apply Protocol csys.eqfst subst
  and sdf_0 = SDF.apply csys.sdf Subst.identity subst
  and sub_cons_0 = Uniformity_Set.apply csys.sub_cons Subst.identity subst in

  {
    simp_DF = df_0;
    simp_EqFst = eqfst_0;
    simp_EqSnd = csys.eqsnd;
    simp_SDF = sdf_0;
    simp_Sub_Cons = sub_cons_0;
    simp_Mixed_Eq = Eq.Mixed.top
  }

let simple_of_private csys ch =

  let xsnd = Variable.fresh Recipe Existential (Variable.snd_ord_type (csys.size_frame + 1)) in
  let b_fct = BasicFact.create xsnd ch in

  {
    simp_DF = DF.add csys.df b_fct;
    simp_EqFst = csys.eqfst;
    simp_EqSnd = csys.eqsnd;
    simp_SDF = csys.sdf;
    simp_Sub_Cons = Uniformity_Set.add csys.sub_cons (of_variable xsnd) ch;
    simp_Mixed_Eq = Eq.Mixed.top
  }

let simple_of_equality_constructor csys symb term =
  let args = get_args term in
  let vars_snd = Variable.fresh_list Recipe Existential (Variable.snd_ord_type csys.size_frame) (Symbol.get_arity symb) in
  let simple_recipe = apply_function symb (List.map of_variable vars_snd) in
  let b_fct_list = List.map2 (fun x t -> BasicFact.create x t) vars_snd args in

  let df_1 = List.fold_left DF.add csys.df b_fct_list in
  let sub_cons_1 = List.fold_left (fun acc bfct -> Uniformity_Set.add acc (of_variable (BasicFact.get_snd_ord_variable bfct)) (BasicFact.get_protocol_term bfct)) csys.sub_cons b_fct_list in

  let simple_csys =
    {
      simp_DF = df_1;
      simp_EqFst = csys.eqfst;
      simp_EqSnd = csys.eqsnd;
      simp_SDF = csys.sdf;
      simp_Sub_Cons = sub_cons_1;
      simp_Mixed_Eq = Eq.Mixed.top
    }
  in

  simple_recipe, simple_csys

let simple_of_skeleton csys id_sdf id_skel =
  let fact = SDF.get csys.sdf id_sdf in

  let recipe_fact = Fact.get_recipe fact in

  let term_fact = Fact.get_protocol_term fact in
  let skel = Rewrite_rules.get_skeleton id_skel in
  let symb = root skel.Rewrite_rules.recipe in
  try
    let fst_subst = Subst.unify Protocol [term_fact,skel.Rewrite_rules.pos_term] in

    let new_eq_fst = Eq.apply Protocol csys.eqfst fst_subst in
    if Eq.is_bot new_eq_fst
    then None
    else
      let snd_subst = Subst.create Recipe skel.Rewrite_rules.pos_vars recipe_fact in

      let new_recipe = Subst.apply snd_subst skel.Rewrite_rules.recipe (fun r f -> f r) in
      let (new_lhs,new_bfct_list) =
        Subst.apply fst_subst (skel.Rewrite_rules.lhs,skel.Rewrite_rules.basic_deduction_facts) (fun (t_list,bfct_l) f ->
          List.map f t_list,
          List.fold_left (fun acc bfct ->
            if Variable.is_equal (BasicFact.get_snd_ord_variable bfct) skel.Rewrite_rules.pos_vars
            then acc
            else (BasicFact.create (BasicFact.get_snd_ord_variable bfct) (f (BasicFact.get_protocol_term bfct)))::acc
          ) [] bfct_l
        )
      in

      let hist = List.find (fun hist -> Symbol.is_equal hist.destructor symb) csys.history_skeleton in
      let fst_subst_hist = Subst.create_multiple Protocol (List.map2 (fun x t -> (x,t)) hist.fst_vars new_lhs) in
      let snd_subst_hist = Subst.create_multiple Recipe (List.map2 (fun x t -> (x,t)) hist.snd_vars (get_args new_recipe)) in
      let mixed_diseq = Eq.Mixed.apply hist.diseq fst_subst_hist snd_subst_hist in

      if Eq.Mixed.is_bot mixed_diseq
      then None
      else
        let df_0 = DF.apply csys.df fst_subst in
        let df_1 = List.fold_left DF.add df_0 new_bfct_list in
        let sdf_1 = SDF.apply csys.sdf Subst.identity fst_subst in
        let sub_cons_0 = Uniformity_Set.apply csys.sub_cons Subst.identity fst_subst in
        let sub_cons_1 = List.fold_left (fun acc bfct -> Uniformity_Set.add acc (of_variable (BasicFact.get_snd_ord_variable bfct)) (BasicFact.get_protocol_term bfct)) sub_cons_0 new_bfct_list in
        let simple_csys =
          {
            simp_DF = df_1;
            simp_EqFst = new_eq_fst;
            simp_EqSnd = csys.eqsnd;
            simp_SDF = sdf_1;
            simp_Sub_Cons = sub_cons_1;
            simp_Mixed_Eq = mixed_diseq
          }
        in
        Some (new_recipe,simple_csys)
  with Subst.Not_unifiable -> None

(***** Access *****)

let get_vars_simple_with_list (type a) (type b) (at: (a,b) atom) csys (vars_l: (a,b) variable list) =
  let result_vars = ref vars_l in

  match at with
    | Protocol ->
        DF.iter csys.simp_DF (fun bfct -> result_vars := get_vars_Term Protocol (BasicFact.get_protocol_term bfct) (fun _ -> true) !result_vars);
        result_vars := Eq.get_vars_with_list Protocol csys.simp_EqFst !result_vars;
        SDF.iter csys.simp_SDF (fun fct -> result_vars := get_vars_Term Protocol (Fact.get_protocol_term fct) (fun _-> true) !result_vars);
        Uniformity_Set.iter csys.simp_Sub_Cons (fun _ t -> result_vars := get_vars_Term Protocol t (fun _ -> true) !result_vars);
        !result_vars
    | Recipe ->
        DF.iter csys.simp_DF (fun bfct -> result_vars := get_vars_Term Recipe (of_variable (BasicFact.get_snd_ord_variable bfct)) (fun _ -> true) !result_vars);
        result_vars := Eq.get_vars_with_list Recipe csys.simp_EqSnd !result_vars;
        SDF.iter csys.simp_SDF (fun fct -> result_vars := get_vars_Term Recipe (Fact.get_recipe fct) (fun _-> true) !result_vars);
        Uniformity_Set.iter csys.simp_Sub_Cons (fun r _ -> result_vars := get_vars_Term Recipe r (fun _ -> true) !result_vars);
        !result_vars

let get_names_simple_with_list csys names_l =
  let result_vars = ref names_l in

  DF.iter csys.simp_DF (fun bfct -> result_vars := get_names_Term Protocol (BasicFact.get_protocol_term bfct) !result_vars);
  result_vars := Eq.get_names_with_list Protocol csys.simp_EqFst !result_vars;
  SDF.iter csys.simp_SDF (fun fct ->
    result_vars := get_names_Term Protocol (Fact.get_protocol_term fct) !result_vars;
    result_vars := get_names_Term Recipe (Fact.get_recipe fct) !result_vars
  );
  Uniformity_Set.iter csys.simp_Sub_Cons (fun _ t -> result_vars := get_names_Term Protocol t !result_vars);
  !result_vars

let get_axioms_simple_with_list csys ax_list =
  let result = ref ax_list in

  SDF.iter_within_var_type 0 csys.simp_SDF (fun fct ->
    result := get_axioms_Term (Fact.get_recipe fct) (fun _ -> true) !result
  );
  !result

(**** Operators *****)

let apply_mgs csys (subst_snd,list_var) =

  let new_df_1 = List.fold_left (fun df x_snd ->
    let b_fct = BasicFact.create x_snd (of_variable (Variable.fresh Protocol Existential Variable.fst_ord_type)) in
    DF.add df b_fct
    ) csys.df list_var in

  let new_df_2 = Subst.fold (fun df x _ -> DF.remove df x) new_df_1 subst_snd in

  let new_sdf_1 = SDF.apply csys.sdf subst_snd Subst.identity in

  let equations =
    Subst.fold (fun eq_l x r ->
      match DF.get csys.df x with
        | None -> Config.internal_error "[constraint_system.ml >> apply] The variabes in the domain of the mgs should be variables of the constraint system."
        | Some b_fct ->
            begin match Tools.partial_consequence Recipe new_sdf_1 new_df_2 r with
              | None -> Config.internal_error "[constraint_system.ml >> apply] The substitution is not compatible with the constraint system."
              | Some (_,t) -> (BasicFact.get_protocol_term b_fct, t)::eq_l
            end
      ) [] subst_snd
  in

  try
    let subst_fst = Subst.unify Protocol equations in

    let new_df_3 = DF.apply new_df_2 subst_fst
    and new_eqfst = Eq.apply Protocol csys.eqfst subst_fst in

    if Eq.is_bot new_eqfst
    then raise Bot;

    let new_eqsnd = Eq.apply Recipe csys.eqsnd subst_snd in

    if Eq.is_bot new_eqsnd
    then raise Bot;

    let new_sdf_2 = SDF.apply new_sdf_1 Subst.identity subst_fst
    and new_uf_1 = UF.apply csys.uf subst_snd subst_fst
    and new_i_subst_fst = Subst.compose_restricted_generic csys.i_subst_fst subst_fst (fun x -> Variable.quantifier_of x = Free)
    and new_i_subst_snd = Subst.compose_restricted_generic csys.i_subst_snd subst_snd (fun x -> Variable.quantifier_of x = Free)
    and new_sub_cons_1 = Uniformity_Set.apply csys.sub_cons subst_snd subst_fst in

    let (new_sub_cons_2,new_sdf_3) =
      Subst.fold (fun (acc_sub_cons,acc_sdf) _ r ->
        Config.debug (fun () ->
          match Tools.partial_consequence Recipe acc_sdf new_df_3 r with
            | None -> Config.internal_error "[constraint_system.ml >> apply] The recipe should be consequence."
            | Some (_,t) when Uniformity_Set.exists acc_sub_cons r t -> ()
            | _ -> Config.internal_error "[constraint_system.ml >> apply] The pair of recipe/term should already be in the uniformity set."
        );
        if is_function r && Symbol.get_arity (root r) > 0
        then List.fold_left (fun (acc_sub_cons_1,acc_sdf_1) r -> Tools.add_in_uniset acc_sub_cons_1 acc_sdf_1 new_df_3 r) (acc_sub_cons,acc_sdf) (get_args r)
        else (acc_sub_cons,acc_sdf)
      ) (new_sub_cons_1,new_sdf_2) subst_snd
    in

    let new_history =
      List.fold_left (fun acc hist ->
        { hist with diseq = Eq.Mixed.apply hist.diseq subst_fst subst_snd }::acc
      ) [] csys.history_skeleton
    in

    let new_csys =
      { csys with
        df = new_df_3;
        eqfst = new_eqfst;
        eqsnd = new_eqsnd;
        sdf = new_sdf_3;
        uf = new_uf_1;
        i_subst_fst = new_i_subst_fst;
        i_subst_snd = new_i_subst_snd;
        sub_cons = new_sub_cons_2;
        history_skeleton = new_history
      }
    in

    if is_uniformity_rule_applicable new_csys
    then raise Bot
    else new_csys
  with
    | Subst.Not_unifiable  -> raise Bot

let dummy_recipe = of_axiom (Axiom.create 1)

type data_shared =
  {
    share_sdf : (recipe * bool) array;
    share_eqsnd : (snd_ord, axiom) Eq.t;
    share_ded : recipe option ref;
    share_eq : Fact.equality option ref;
    share_i_subst_snd : (snd_ord, axiom) Subst.t
  }

let apply_mgs_and_gather csys data_shared (subst_snd,list_var) =

  let new_df_1 = List.fold_left (fun df x_snd ->
    let b_fct = BasicFact.create x_snd (of_variable (Variable.fresh Protocol Existential Variable.fst_ord_type)) in
    DF.add df b_fct
    ) csys.df list_var in

  let new_df_2 = Subst.fold (fun df x _ -> DF.remove df x) new_df_1 subst_snd in

  let new_sdf_1 = SDF.apply_snd_and_gather csys.sdf subst_snd data_shared.share_sdf in

  let equations =
    Subst.fold (fun eq_l x r ->
      match DF.get csys.df x with
        | None -> Config.internal_error "[constraint_system.ml >> apply] The variabes in the domain of the mgs should be variables of the constraint system."
        | Some b_fct ->
            begin match Tools.partial_consequence Recipe new_sdf_1 new_df_2 r with
              | None -> Config.internal_error "[constraint_system.ml >> apply] The substitution is not compatible with the constraint system."
              | Some (_,t) -> (BasicFact.get_protocol_term b_fct, t)::eq_l
            end
      ) [] subst_snd
  in

  try
    let subst_fst = Subst.unify Protocol equations in
    let new_eqfst = Eq.apply Protocol csys.eqfst subst_fst in

    if Eq.is_bot new_eqfst
    then raise Bot;

    let new_df_3 = DF.apply new_df_2 subst_fst in

    let new_sdf_2 = SDF.apply new_sdf_1 Subst.identity subst_fst
    and new_uf_1 = UF.apply_with_gathering csys.uf subst_snd subst_fst data_shared.share_ded data_shared.share_eq
    and new_i_subst_fst = Subst.compose_restricted_generic csys.i_subst_fst subst_fst (fun x -> Variable.quantifier_of x = Free)
    and new_sub_cons_1 = Uniformity_Set.apply csys.sub_cons subst_snd subst_fst in

    let (new_sub_cons_2,new_sdf_3) =
      Subst.fold (fun (acc_sub_cons,acc_sdf) _ r ->
        Config.debug (fun () ->
          match Tools.partial_consequence Recipe acc_sdf new_df_3 r with
            | None -> Config.internal_error "[constraint_system.ml >> apply] The recipe should be consequence."
            | Some (_,t) when Uniformity_Set.exists acc_sub_cons r t -> ()
            | _ -> Config.internal_error "[constraint_system.ml >> apply] The pair of recipe/term should already be in the uniformity set."
        );
        if is_function r && Symbol.get_arity (root r) > 0
        then List.fold_left (fun (acc_sub_cons_1,acc_sdf_1) r -> Tools.add_in_uniset acc_sub_cons_1 acc_sdf_1 new_df_3 r) (acc_sub_cons,acc_sdf) (get_args r)
        else (acc_sub_cons,acc_sdf)
      ) (new_sub_cons_1,new_sdf_2) subst_snd in

    let new_history =
      List.fold_left (fun acc hist ->
        { hist with diseq = Eq.Mixed.apply hist.diseq subst_fst subst_snd } :: acc
      ) [] csys.history_skeleton
    in

    let new_csys =
      { csys with
        df = new_df_3;
        eqfst = new_eqfst;
        eqsnd = data_shared.share_eqsnd;
        sdf = new_sdf_3;
        uf = new_uf_1;
        i_subst_fst = new_i_subst_fst;
        i_subst_snd = data_shared.share_i_subst_snd;
        sub_cons = new_sub_cons_2;
        history_skeleton = new_history
      }
    in

    if is_uniformity_rule_applicable new_csys
    then raise Bot
    else new_csys
  with
    | Subst.Not_unifiable  -> raise Bot

let apply_mgs_from_gathering csys data_shared (subst_snd,list_var) =

  let new_df_1 = List.fold_left (fun df x_snd ->
    let b_fct = BasicFact.create x_snd (of_variable (Variable.fresh Protocol Existential Variable.fst_ord_type)) in
    DF.add df b_fct
    ) csys.df list_var in

  let new_df_2 = Subst.fold (fun df x _ -> DF.remove df x) new_df_1 subst_snd in

  let new_sdf_1 = SDF.apply_snd_from_gathering csys.sdf data_shared.share_sdf in

  let equations =
    Subst.fold (fun eq_l x r ->
      match DF.get csys.df x with
        | None -> Config.internal_error "[constraint_system.ml >> apply] The variabes in the domain of the mgs should be variables of the constraint system."
        | Some b_fct ->
            begin match Tools.partial_consequence Recipe new_sdf_1 new_df_2 r with
              | None -> Config.internal_error "[constraint_system.ml >> apply] The substitution is not compatible with the constraint system."
              | Some (_,t) -> (BasicFact.get_protocol_term b_fct, t)::eq_l
            end
      ) [] subst_snd
  in

  try
    let subst_fst = Subst.unify Protocol equations in
    let new_eqfst = Eq.apply Protocol csys.eqfst subst_fst in

    if Eq.is_bot new_eqfst
    then raise Bot;

    let new_df_3 = DF.apply new_df_2 subst_fst in

    let new_sdf_2 = SDF.apply new_sdf_1 Subst.identity subst_fst
    and new_uf_1 = UF.apply_with_gathering csys.uf subst_snd subst_fst data_shared.share_ded data_shared.share_eq
    and new_i_subst_fst = Subst.compose_restricted_generic csys.i_subst_fst subst_fst (fun x -> Variable.quantifier_of x = Free)
    and new_sub_cons_1 = Uniformity_Set.apply csys.sub_cons subst_snd subst_fst in

    let (new_sub_cons_2,new_sdf_3) =
      Subst.fold (fun (acc_sub_cons,acc_sdf) _ r ->
        Config.debug (fun () ->
          match Tools.partial_consequence Recipe acc_sdf new_df_3 r with
            | None -> Config.internal_error "[constraint_system.ml >> apply] The recipe should be consequence."
            | Some (_,t) when Uniformity_Set.exists acc_sub_cons r t -> ()
            | _ -> Config.internal_error "[constraint_system.ml >> apply] The pair of recipe/term should already be in the uniformity set."
        );
        if is_function r && Symbol.get_arity (root r) > 0
        then List.fold_left (fun (acc_sub_cons_1,acc_sdf_1) r -> Tools.add_in_uniset acc_sub_cons_1 acc_sdf_1 new_df_3 r) (acc_sub_cons,acc_sdf) (get_args r)
        else (acc_sub_cons,acc_sdf)
      ) (new_sub_cons_1,new_sdf_2) subst_snd in

    let new_history =
      List.fold_left (fun acc hist ->
        { hist with diseq = Eq.Mixed.apply hist.diseq subst_fst subst_snd } :: acc
      ) [] csys.history_skeleton
    in

    let new_csys =
      { csys with
        df = new_df_3;
        eqfst = new_eqfst;
        eqsnd = data_shared.share_eqsnd;
        sdf = new_sdf_3;
        uf = new_uf_1;
        i_subst_fst = new_i_subst_fst;
        i_subst_snd = data_shared.share_i_subst_snd;
        sub_cons = new_sub_cons_2;
        history_skeleton = new_history
      }
    in

    if is_uniformity_rule_applicable new_csys
    then raise Bot
    else new_csys
  with
    | Subst.Not_unifiable  -> raise Bot

(**** Subsumption *****)

let exists_match_mgs csys f_pred =
  let result = ref false in

  let rec apply_rules csys f_next =

    let test_not_solved basic_fct =
      if not (is_variable (BasicFact.get_protocol_term basic_fct))
      then Some basic_fct
      else None
    in

    let apply_res basic_fct fct f_next =
      let b_term = BasicFact.get_protocol_term basic_fct
      and b_recipe = BasicFact.get_snd_ord_variable basic_fct
      and term = Fact.get_protocol_term fct
      and recipe = Fact.get_recipe fct in

      if is_equal Protocol term b_term
      then
        if var_occurs b_recipe recipe
        then f_next ()
        else
          begin
            let subst_snd = Subst.create Recipe b_recipe recipe in

            let df_1 = DF.remove csys.simp_DF b_recipe in

            Config.debug (fun () ->
              if not (Uniformity_Set.exists csys.simp_Sub_Cons (of_variable b_recipe) b_term)
              then Config.internal_error "[Constraint_system.ml >> exists_match_mgs] Elements of DF should always be in the uniformity set."
            );

            let sub_cons_1 = Uniformity_Set.apply csys.simp_Sub_Cons subst_snd Subst.identity in

            let csys' = { csys with
                simp_DF = df_1;
                simp_EqSnd = Eq.apply Recipe csys.simp_EqSnd subst_snd;
                simp_SDF = SDF.apply csys.simp_SDF subst_snd Subst.identity;
                simp_Sub_Cons = sub_cons_1
              }

            in

            (* Check that eqfst and eqsnd are not bot and that the normalisation rule for unification is not triggered *)

            if Eq.is_bot csys'.simp_EqSnd
            then f_next ()
            else (apply_rules [@tailcall]) csys' f_next
          end
      else f_next ()
    in

    let apply_cons basic_fct f_next =
      let term = BasicFact.get_protocol_term basic_fct
      and x_snd = BasicFact.get_snd_ord_variable basic_fct in

      if is_name term
      then f_next ()
      else
        let symb = root term in
        if Symbol.is_public symb
        then
          let arity = Symbol.get_arity symb in

          if arity = 0
          then
            let recipe = apply_function symb [] in
            let subst = Subst.create Recipe x_snd recipe in
            let df_1 = DF.remove csys.simp_DF x_snd in
            let sub_cons_1 = Uniformity_Set.apply csys.simp_Sub_Cons subst Subst.identity in
            let csys' =
              { csys with
                  simp_DF = df_1;
                  simp_EqSnd = Eq.apply Recipe csys.simp_EqSnd subst;
                  simp_SDF = SDF.apply csys.simp_SDF subst Subst.identity;
                  simp_Sub_Cons = sub_cons_1
              }
            in

            if Eq.is_bot csys'.simp_EqSnd
            then f_next ()
            else (apply_rules [@tailcall]) csys' f_next
          else
            begin
              let args_of_term = get_args term in

              let vars_snd = Variable.fresh_list Recipe Existential (Variable.snd_ord_type (Variable.type_of x_snd)) arity in
              let vars_snd_as_term = List.map of_variable vars_snd in

              let recipe = apply_function symb vars_snd_as_term in
              let subst = Subst.create Recipe x_snd recipe in

              let ded_fact_list = List.map2 BasicFact.create vars_snd args_of_term in

              let df_1 = DF.remove csys.simp_DF x_snd in
              let df_2 = List.fold_left (fun df b_fct -> DF.add df b_fct) df_1 ded_fact_list in

              let sub_cons_1 = Uniformity_Set.apply csys.simp_Sub_Cons subst Subst.identity in
              let sub_cons_2 = List.fold_left2 (fun subc x t -> Uniformity_Set.add subc x t) sub_cons_1  vars_snd_as_term args_of_term in

              let csys' = { csys with
                  simp_DF = df_2;
                  simp_EqSnd = Eq.apply Recipe csys.simp_EqSnd subst;
                  simp_SDF = SDF.apply csys.simp_SDF subst Subst.identity;
                  simp_Sub_Cons = sub_cons_2
                }
              in

              (* Check that eqsnd is not bot and that the normalisation rule for unification is not triggered *)

              if Eq.is_bot csys'.simp_EqSnd
              then f_next ()
              else (apply_rules [@tailcall]) csys' f_next
            end
        else f_next ()
    in

    match Uniformity_Set.unify_multiple_opt csys.simp_Sub_Cons with
      | None -> f_next ()
      | Some(subst,uniset) ->
          if Subst.is_identity subst
          then
            match DF.find csys.simp_DF test_not_solved with
              | None ->
                  if f_pred csys
                  then result := true
                  else f_next ()
              | Some basic_fct ->
                  (SDF.tail_iter_within_var_type [@tailcall]) (Variable.type_of (BasicFact.get_snd_ord_variable basic_fct)) csys.simp_SDF (apply_res basic_fct) (fun () -> (apply_cons [@tailcall]) basic_fct f_next)
          else
            let new_eqsnd = Eq.apply Recipe csys.simp_EqSnd subst in

            if Eq.is_bot new_eqsnd
            then f_next ()
            else
              let new_df = Subst.fold (fun df x _ -> DF.remove df x) csys.simp_DF subst in
              let csys' =
                { csys with
                  simp_DF = new_df;
                  simp_EqSnd = new_eqsnd;
                  simp_SDF = SDF.apply csys.simp_SDF subst Subst.identity;
                  simp_Sub_Cons = uniset
                }
              in
              match DF.find csys'.simp_DF test_not_solved with
                | None ->
                    if f_pred csys
                    then result := true
                    else f_next ()
                | Some basic_fct ->
                    (SDF.tail_iter_within_var_type [@tailcall]) (Variable.type_of (BasicFact.get_snd_ord_variable basic_fct)) csys'.simp_SDF (apply_res basic_fct) (fun () -> (apply_cons [@tailcall]) basic_fct f_next)
  in

  (* We first check if the constraint is not directly bot *)

  if Eq.is_bot csys.simp_EqFst || Eq.is_bot csys.simp_EqSnd
  then false
  else
    begin
      apply_rules csys (fun () -> ());
      !result
    end

let subsume fine_grained csys1 csys2 =
  (* We check that csys1 subsume csys2,
    i.e. solutions of csys1 include the one of csys2.
    Not that we should only take argument that we know comes from
    the same original constraint system. *)

  (* Retreive the terms and free recipes variables of csys2 *)
  let (t_list,v_list) =
    DF.fold (fun (acc_t,acc_v) bfct ->
      let v = BasicFact.get_snd_ord_variable bfct in
      if Variable.quantifier_of v = Free
      then
        let t = BasicFact.get_protocol_term bfct in
        (t::acc_t,(of_variable v)::acc_v)
      else (acc_t,acc_v)
    ) ([],[]) csys2.df
  in
  let (t_list_2,v_list') =
    Subst.fold (fun (acc_t,acc_v) x r ->
      match Tools.partial_consequence Recipe csys2.sdf csys2.df r with
        | None -> Config.internal_error "[constraint_system.ml >> subsume] The recipe should be consequence."
        | Some(_,t) -> (t::acc_t,(of_variable x)::acc_v)
    ) (t_list,v_list) csys2.i_subst_snd
  in
  let (t_list_2',v_list'') =
    Subst.fold (fun (acc_t,acc_v) x r ->
      match Tools.partial_consequence Recipe csys2.sdf csys2.df r with
        | None -> Config.internal_error "[constraint_system.ml >> subsume] The recipe should be consequence (3)."
        | Some(_,t) -> (t::acc_t,(of_variable x)::acc_v)
    ) (t_list_2,v_list') csys2.i_subst_ground_snd
  in

  (* Apply the recipe substitution of csys1 on the variable list *)
  let subst2 = Subst.union csys1.i_subst_snd csys1.i_subst_ground_snd in
  let rev_r_list = Subst.apply subst2 v_list'' (fun vl f -> List.rev_map f vl) in
  (* Compute the corresponding protocol terms in csys1 *)
  let t_list_1 =
    List.rev_map (fun r ->
      match Tools.partial_consequence Recipe csys1.sdf csys1.df r with
        | None -> Config.internal_error "[constraint_system.ml >> subsume] The recipe should be consequence (2)."
        | Some(_,t) -> t
    ) rev_r_list
  in

  (* Check if the terms are matchables *)
  match Subst.match_terms Protocol t_list_1 t_list_2' with
    | None -> false
    | Some sigma ->
        (* Apply the substitution on csys1 *)
        let new_csys1 = simple_of csys1 in
        let new_csys2 =
          { new_csys1 with
            simp_DF = DF.apply new_csys1.simp_DF sigma;
            simp_SDF = SDF.apply new_csys1.simp_SDF Subst.identity sigma;
            simp_Sub_Cons = Uniformity_Set.apply new_csys1.simp_Sub_Cons Subst.identity sigma
          }
        in

        if fine_grained
        then false
        else
          let f_pred csys =
            if Eq.is_top csys.simp_EqSnd
            then
              begin
                let term_sdf = ref [] in
                let term_cons = ref [] in
                Uniformity_Set.iter csys.simp_Sub_Cons (fun r t ->
                  if is_function r
                  then
                    if Symbol.is_constructor (root r)
                    then term_cons := t :: !term_cons
                    else term_sdf := t :: !term_sdf
                  else if is_variable r
                  then ()
                  else term_sdf := t :: !term_sdf
                );
                not (List.exists (fun t1 -> List.exists (fun t2 -> Subst.is_unifiable Protocol [t1,t2]) !term_sdf) !term_cons)
              end
            else false
          in
          exists_match_mgs new_csys2 f_pred

(**********************************
**** Set of constraint systems ****
***********************************)

module Set = struct

  (** An alias for the type of constraint systems. *)
  type 'a csys = 'a t

  type equality_type =
    | Constructor_SDF of id_recipe_equivalent * symbol (** [Constructor_SDF (id,f)] represents the formulas generated by the rule {% \Equality on the deduction fact from $\Solved$ %} with recipe equivalent id equal to [id] and with the constructor function symbol [f].*)
    | Equality_SDF of id_recipe_equivalent * id_recipe_equivalent (** [Equality_SDF (id1,id2)] represents the formulas generated by the rule {% \Equality on the deduction facts from $\Solved$ %} with recipe equivalent ids equal to [id1] and [id2].*)
    | Consequence_UF
    | No_equality

  (** The type of set of constraint systems. *)
  type 'a t =
    {
      csys_list : 'a csys list;
      ded_occurs : bool;
      eq_occurs : equality_type;
      set_private_channels : bool
    }

  let empty =
    {
      csys_list = [];
      ded_occurs = false;
      eq_occurs = No_equality;
      set_private_channels = false
    }

  let size csys_set = List.length csys_set.csys_list

  let add csys csys_set = { csys_set with csys_list = csys::csys_set.csys_list }

  let choose csys_set =
    Config.debug (fun () ->
      if csys_set.csys_list = []
      then Config.internal_error "[constraint_system.ml >> Set.choose] The set should not be empty.";
    );

    List.hd csys_set.csys_list

  let elements csys_set = csys_set.csys_list

  let find_representative csys_set predicate =
    let true_csys = ref None
    and false_csys = ref None in

    let rec explore = function
      | [] -> raise Not_found
      | csys :: q ->
          begin match predicate csys, !true_csys, !false_csys with
            | true, None, Some c -> csys, c
            | false, Some c, None -> c, csys
            | true, None, None -> true_csys := Some csys; explore q
            | false, None, None -> false_csys := Some csys; explore q
            | true, Some _, None
            | false, None, Some _ -> explore q
            | _,_,_ -> Config.internal_error "[constraint_system.ml >> Set.find_representative] Unexpected case."
          end
    in
    explore csys_set.csys_list

  let optimise_snd_ord_recipes csys_set =
    if csys_set.csys_list = []
    then { csys_set with set_private_channels = false }
    else
      let csys = List.hd csys_set.csys_list in

      let i_subst_ground_snd, i_subst_snd = Subst.split_domain_on_term csys.i_subst_snd is_ground in
      let new_i_subst_ground_snd = Subst.union i_subst_ground_snd csys.i_subst_ground_snd in

      let csys_list =
        List.fold_left (fun acc csys' ->
          { csys' with i_subst_snd = i_subst_snd; i_subst_ground_snd = new_i_subst_ground_snd }::acc
        ) [] csys_set.csys_list
      in
      { csys_set with csys_list = csys_list; set_private_channels = false }

  let initialise_for_output csys_set =
    { csys_set with ded_occurs = true }

  let set_private_channels csys_set pr_ch =
    { csys_set with set_private_channels = pr_ch }

  let for_all f csys_set = List.for_all f csys_set.csys_list

  let exists f csys_set = List.exists f csys_set.csys_list

  let is_empty csys_set = csys_set.csys_list = []

  let iter f csys_set = List.iter f csys_set.csys_list

  let display_initial id size =

    let rec go_through = function
      | 0 -> Printf.sprintf "\\mathcal{C}_%d" id
      | k -> Printf.sprintf "%s, \\mathcal{C}_%d" (go_through (k-1)) (k+id)
    in
    go_through (size-1)

  let display out ?(rho=None) ?(id=1) csys_set = match out with
    | Testing -> Printf.sprintf "{ %s }" (display_list (fun csys -> display Testing ~rho:rho csys) ", " csys_set.csys_list)
    | HTML ->
        if csys_set.csys_list = []
        then Printf.sprintf "\\(%s\\)" (emptyset Latex)
        else
          begin
            let str = ref (Printf.sprintf "\\( \\{ %s \\}\\) with </br>\n" (display_initial id (List.length csys_set.csys_list))) in

            str := Printf.sprintf "%s            <ul>\n" !str;

            List.iteri (fun i csys ->
              str := Printf.sprintf "%s              <li>%s              </li>\n" !str (display HTML ~rho:rho ~hidden:true ~id:(i+id) csys)
            ) csys_set.csys_list;

            Printf.sprintf "%s            </ul>\n" !str;
          end
    | _ -> Config.internal_error "[constraint_system.ml >> display] This display mode is not implemented yet."
end

(*************************************
***             Rules              ***
**************************************)

module Rule = struct

  type 'a continuation =
    {
      positive : 'a Set.t -> (unit -> unit) -> unit;
      negative : 'a Set.t -> (unit -> unit) -> unit;
      not_applicable : 'a Set.t -> (unit -> unit) -> unit
    }

  (* The rules *)

  let rec remove_id_from_list id = function
    | [] -> Config.internal_error "[Constraint_system.ml >> remove_id_from_list] The element to remove should be present in the list."
    | id'::q when id = id' -> q
    | id'::q -> id'::(remove_id_from_list id q)

  let check_equality_type_when_removing_eq_formula csys = function
    | Set.Equality_SDF (id_max_sdf, id_sdf) ->
        Config.debug (fun () ->
          let (_,id_last_entry) = SDF.last_entry csys.sdf in
          if id_max_sdf <> id_last_entry
          then Config.internal_error "[Constraint_system.ml >> check_equality_when_removing_eq_formula] The equality should always be about the last entry of the SDF."
        );

        { csys with equality_to_checked = remove_id_from_list id_sdf csys.equality_to_checked }
    | Set.Constructor_SDF (id_sdf,symb) ->
        Config.debug (fun () ->
          let fact = SDF.get csys.sdf id_sdf in
          if not (Symbol.is_equal (root (Fact.get_protocol_term fact)) symb)
          then Config.internal_error "[Constraint_system.ml >> check_equality_when_removing_eq_formula] The symbol should correspond to the one deduction fact in the SDF with the given id."
        );
        { csys with equality_constructor_to_checked = remove_id_from_list id_sdf csys.equality_constructor_to_checked }
    | _ -> csys

  type 'a continuation_norm_split =
    {
      no_split : 'a Set.t -> (unit -> unit) -> unit;
      split : 'a Set.t -> (unit -> unit) -> unit
    }

  let add_mixed_diseq_skeleton csys =
    Config.debug (fun () ->
      if not (UF.solved_occurs Fact.Deduction csys.uf)
      then Config.internal_error "[constraint_system.ml >> add_diseq_skeleton] There should be a solved deduction fact in UF."
    );

    let form = UF.choose_solved Fact.Deduction csys.uf in
    let recipe = Fact.get_recipe (Fact.get_head form) in

    if is_axiom recipe
    then csys
    else
      let f = root recipe in

      let new_history =
        replace_history f (fun hist ->
          let diseq = Tools.mixed_diseq_for_skeletons csys.sdf csys.df hist.fst_vars hist.snd_vars recipe in
          { hist with diseq = Eq.Mixed.wedge hist.diseq diseq }
        ) csys.history_skeleton
      in

      { csys with history_skeleton = new_history }

  let partition_csys_set eq_type_op csys_set =
    let positive = ref []
    and negative = ref [] in

    match eq_type_op with
      | None ->
          List.iter (fun csys ->
            if UF.solved_occurs Fact.Deduction csys.uf
            then positive := csys :: !positive
            else negative := csys :: !negative
          ) csys_set.Set.csys_list;
          Config.debug (fun () ->
            if List.length !positive = 0 || List.length !negative = 0
            then Config.internal_error "[Constraint_system.ml >> Rules.partition_csys_set] Partition should be 2 non empty sets."
          );
          { csys_set with Set.csys_list = !positive }, { csys_set with Set.csys_list = !negative; Set.ded_occurs = false }
      | Some Set.Consequence_UF ->
          List.iter (fun csys ->
            if UF.solved_occurs Fact.Equality csys.uf
            then
              let new_uf = UF.remove_solved Fact.Equality csys.uf in
              let csys_1 = add_mixed_diseq_skeleton csys in
              let csys_2 = { csys_1 with uf = UF.remove_solved Fact.Deduction new_uf } in
              positive := csys_2 :: !positive
            else
              begin
                Config.debug (fun () ->
                  if UF.unsolved_occurs Fact.Equality csys.uf
                  then Config.internal_error "[Constraint_system.ml >> Rules.partition_csys_set] There should not be an unsolved formula"
                );
                negative := csys :: !negative
              end
          ) csys_set.Set.csys_list;
          Config.debug (fun () ->
            if List.length !positive = 0 || List.length !negative = 0
            then Config.internal_error "[Constraint_system.ml >> Rules.partition_csys_set] Partition should be 2 non empty sets. (2)"
          );
          { csys_set with Set.csys_list = !positive; Set.eq_occurs = Set.No_equality; Set.ded_occurs = false }, { csys_set with Set.csys_list = !negative; Set.eq_occurs = Set.No_equality }
      | Some eq_type ->
          List.iter (fun csys ->
            if UF.solved_occurs Fact.Equality csys.uf
            then
              let csys_1 = { csys with uf = UF.remove_solved Fact.Equality csys.uf } in
              positive := (check_equality_type_when_removing_eq_formula csys_1 eq_type) :: !positive
            else
              begin
                Config.debug (fun () ->
                  if UF.unsolved_occurs Fact.Equality csys.uf
                  then Config.internal_error "[Constraint_system.ml >> Rules.partition_csys_set] There should not be an unsolved formula (3)"
                );
                negative := csys :: !negative
              end
          ) csys_set.Set.csys_list;
          Config.debug (fun () ->
            if List.length !positive = 0 || List.length !negative = 0
            then Config.internal_error "[Constraint_system.ml >> Rules.partition_csys_set] Partition should be 2 non empty sets. (3)"
          );
          { csys_set with Set.csys_list = !positive; Set.eq_occurs = Set.No_equality }, { csys_set with Set.csys_list = !negative; Set.eq_occurs = Set.No_equality }

  let normalisation_split_ded csys_set f_continuation f_next =

    if csys_set.Set.csys_list = [] || not (csys_set.Set.ded_occurs)
    then (f_continuation.no_split [@tailcall]) csys_set f_next
    else
      begin
        (* Check if the deduction fact is an axiom *)
        let csys = List.hd csys_set.Set.csys_list in

        match UF.choose_solved_option Fact.Deduction csys.uf with
          | Some form when is_axiom (Fact.get_recipe (Fact.get_head form)) ->
              (* When an axiom is present then the split rule can never be applied since all constraint system contains such axiom *)
              (f_continuation.no_split [@tailcall]) csys_set f_next
          | _ ->
              (* Possible application of the split rule *)
              let applicable = ref false in
              let found_deduction = ref false in

              let result = List.for_all (fun csys' ->
                let r = not (UF.unsolved_occurs Fact.Deduction csys'.uf) in

                if r && not (UF.solved_occurs Fact.Deduction csys'.uf)
                then applicable := true
                else found_deduction := true;

                r
              ) csys_set.Set.csys_list
              in

              if !found_deduction
              then
                if result && !applicable
                then
                  let (positive_set,negative_set) = partition_csys_set None csys_set in
                  (f_continuation.split [@tailcall]) positive_set (fun () -> (f_continuation.split [@tailcall]) negative_set f_next)
                else (f_continuation.no_split [@tailcall]) csys_set f_next
              else (f_continuation.no_split [@tailcall]) { csys_set with Set.ded_occurs = false } f_next
      end

  let normalisation_split_eq csys_set f_continuation f_next =
    if csys_set.Set.csys_list = [] || csys_set.Set.eq_occurs = Set.No_equality
    then (f_continuation.no_split [@tailcall]) csys_set f_next
    else
      begin
        let found_equality = ref false in
        let applicable = ref false in

        let result = List.for_all (fun csys ->
          let r = not (UF.unsolved_occurs Fact.Equality csys.uf) in

          if r && not (UF.solved_occurs Fact.Equality csys.uf)
          then applicable := true
          else found_equality := true;

          r
        ) csys_set.Set.csys_list
        in

        if !found_equality
        then
          match result, !applicable with
            | true, true ->
                let (positive_set,negative_set) = partition_csys_set (Some csys_set.Set.eq_occurs) csys_set in
                (f_continuation.split [@tailcall]) positive_set (fun () -> (f_continuation.split [@tailcall]) negative_set f_next)
            | true, false ->
                begin match csys_set.Set.eq_occurs with
                  | Set.Consequence_UF ->
                      let csys_list =
                        List.fold_left (fun acc csys ->
                          let new_uf = UF.remove_solved Fact.Equality csys.uf in
                          let csys_1 = add_mixed_diseq_skeleton csys in
                          { csys_1 with uf = UF.remove_solved Fact.Deduction new_uf } :: acc
                        ) [] csys_set.Set.csys_list
                      in
                      let csys_set' = { csys_set with Set.csys_list = csys_list ; Set.eq_occurs = Set.No_equality ; Set.ded_occurs = false } in

                      (f_continuation.no_split [@tailcall]) csys_set' f_next
                  | _ ->
                      let csys_list =
                        List.fold_left (fun acc csys ->
                          let csys_1 = check_equality_type_when_removing_eq_formula csys csys_set.Set.eq_occurs in
                          { csys_1 with uf = UF.remove_solved Fact.Equality csys_1.uf } :: acc
                        ) [] csys_set.Set.csys_list
                      in
                      let csys_set' = { csys_set with Set.csys_list = csys_list ; Set.eq_occurs = Set.No_equality } in

                      (f_continuation.no_split [@tailcall]) csys_set' f_next
                end
            | _, _ -> (f_continuation.no_split [@tailcall]) csys_set f_next
          else (f_continuation.no_split [@tailcall]) { csys_set with Set.eq_occurs = Set.No_equality } f_next
      end

  type 'a continuation_main_norm_split =
    {
      main_no_split : 'a Set.t -> (unit -> unit) -> unit;
      main_split_ded : 'a Set.t -> (unit -> unit) -> unit;
      main_split_but_not_ded : 'a Set.t -> (unit -> unit) -> unit
    }

  let normalisation_split csys_set f_continuation f_next =

    let after_split_ded csys_set_1 f_next_1 =
      normalisation_split_eq csys_set_1
        {
          split = f_continuation.main_split_ded;
          no_split = f_continuation.main_split_ded
        }
        f_next_1
    in

    let after_no_split_ded csys_set_1 f_next_1 =
      normalisation_split_eq csys_set_1
        {
          split = (fun csys_set_2 f_next_2 -> normalisation_split_ded csys_set_2 { split = f_continuation.main_split_ded; no_split = f_continuation.main_split_but_not_ded } f_next_2);
          no_split = f_continuation.main_no_split
        }
        f_next_1
    in

    normalisation_split_ded csys_set
      {
        split = after_split_ded;
        no_split = after_no_split_ded
      }
      f_next

  type 'a continuation_conseq_norm =
    {
      addition : 'a Set.t -> (unit -> unit) -> unit;
      removal : 'a Set.t -> (unit -> unit) -> unit
    }

  (* This rule should only be applied if all deduction facts are solved and if there is no equality formula in UF *)
  let normalisation_SDF_or_consequence csys_set f_continuation f_next =
    Config.debug (fun () ->
      if not (List.for_all (fun csys -> UF.solved_occurs Fact.Deduction csys.uf) csys_set.Set.csys_list)
      then Config.internal_error "[constraint_system.ml >> normalisation_SDF_or_consequence] The deduction formula should be solved.";

      if csys_set.Set.eq_occurs <> Set.No_equality
      then Config.internal_error "[constraint_system.ml >> normalisation_SDF_or_consequence] There should not be equality formulas";

      if List.exists (fun csys -> UF.solved_occurs Fact.Equality csys.uf || UF.unsolved_occurs Fact.Equality csys.uf) csys_set.Set.csys_list
      then Config.internal_error "[constraint_system.ml >> normalisation_SDF_or_consequence] There is an equality fact even though it was indicated otherwise.";

      if csys_set.Set.ded_occurs = false
      then Config.internal_error "[constraint_system.ml >> normalisation_SDF_or_consequence] The rules should only be applied with the presence of deduction formulas.";
    );

    let rec go_through_csys_set = function
      | [] -> None
      | csys::q ->
          let ded_formula = UF.choose_solved Fact.Deduction csys.uf in

          let term = Fact.get_protocol_term (Fact.get_head ded_formula) in

          match Tools.uniform_consequence csys.sdf csys.df csys.sub_cons term with
            | None -> go_through_csys_set q
            | Some recipe -> Some recipe
    in

    match go_through_csys_set csys_set.Set.csys_list with
      | None ->
            (* Addition to SDF -> add to SDF and remove from UF *)
            let new_csys_list =
              List.fold_left (fun acc_csys csys ->
                (* Update of the lists equality_constructor_checked and equality_constructor_to_checked *)

                let ded_formula = UF.choose_solved Fact.Deduction csys.uf in

                Config.debug (fun () ->
                  if not (Fact.is_fact ded_formula)
                  then Config.internal_error "[Constraint_system.ml >> normalisation_SDF_or_consequence] The formula should be a fact.";

                  if csys.equality_constructor_to_checked <> []
                  then Config.internal_error "[Constraint_system.ml >> normalisation_SDF_or_consequence] All sdf should have been checked when we add a new element to SDF, i.e.  we did not respect the order of rule Sat < Equality < Rew";

                  if csys.equality_to_checked <> []
                  then Config.internal_error "[Constraint_system.ml >> normalisation_SDF_or_consequence] All pair of deduction fact from sdf should have been checked for equalities at that point.";
                );

                let head = Fact.get_head ded_formula in

                let new_sdf = SDF.add csys.sdf csys.size_frame head in
                let id_last = SDF.last_entry_id new_sdf in

                Config.debug (fun () ->
                  if Uniformity_Set.exists_pair_with_same_protocol_term csys.sub_cons (Eq.implies Recipe csys.eqsnd)
                  then Config.internal_error "[constraint_system.ml >> normalisation_SDF_or_consequence] The uniformity check should not occur when adding an element to SDF."
                );

                let csys_1 = add_mixed_diseq_skeleton csys in

                { csys_1 with
                  skeletons_checked = [];
                  skeletons_to_check = (List.rev_append csys.skeletons_checked (List.fold_left (fun acc id_skel -> (id_last,id_skel)::acc) csys.skeletons_to_check (Rewrite_rules.get_all_skeleton_indices ())));
                  equality_to_checked = SDF.all_id csys.sdf;
                  equality_constructor_checked = [];
                  equality_constructor_to_checked = id_last::csys.equality_constructor_checked;
                  sdf = new_sdf;
                  uf = UF.remove_solved Fact.Deduction csys.uf
                } :: acc_csys
              ) [] csys_set.Set.csys_list
            in

            let new_csys_set = { csys_set with Set.csys_list = new_csys_list; Set.ded_occurs = false ; Set.eq_occurs = Set.No_equality } in


            (f_continuation.removal [@tailcall]) new_csys_set f_next
      | Some recipe_conseq ->
          (* Apply Consequence normalisation rule *)

          let new_csys_list =
            List.fold_left (fun acc csys ->
              let ded_formula = UF.choose_solved Fact.Deduction csys.uf in

              Config.debug (fun () ->
                if not (Fact.is_fact ded_formula)
                then Config.internal_error "[Constraint_system.ml >> normalisation_SDF_or_consequence] The formula should be a fact."
              );

              match Tools.partial_consequence Recipe csys.sdf csys.df recipe_conseq with
                | None -> Config.internal_error "[Constraint_system.ml >> normalisation_SDF_or_consequence] The recipe should be consequence."
                | Some (_,term_conseq) ->
                    let head = Fact.get_head ded_formula in
                    let term = Fact.get_protocol_term head in
                    let recipe = Fact.get_recipe head in

                    begin try
                      let head_eq = Fact.create_equality_fact recipe recipe_conseq in
                      let eq_form = Fact.create Fact.Equality head_eq [term,term_conseq] in
                      let simple_csys = simple_of_formula csys eq_form in

                      let _ = one_mgs simple_csys in
                      { csys with uf = UF.add_equality csys.uf eq_form } :: acc
                    with
                      | Fact.Bot | Not_found -> csys :: acc
                    end
            ) [] csys_set.Set.csys_list
          in

          let new_csys_set = { csys_set with Set.csys_list = new_csys_list ; Set.ded_occurs = true; Set.eq_occurs = Set.Consequence_UF } in

          (f_continuation.addition [@tailcall]) new_csys_set f_next

  let normalisation_mgs csys_set f_continuation f_next =
    if csys_set.Set.csys_list = []
    then f_continuation { csys_set with Set.eq_occurs = Set.No_equality; Set.ded_occurs = false } f_next
    else
      let new_csys_set_1 =
        if csys_set.Set.ded_occurs
        then
          begin
            match UF.choose_solved_option Fact.Deduction (List.hd csys_set.Set.csys_list).uf with
              | Some form when is_axiom (Fact.get_recipe (Fact.get_head form)) -> csys_set
              | _ ->
                  let ded_occurs = ref false in

                  let new_csys_list =
                    List.fold_left (fun acc_csys csys ->
                      match UF.choose_solved_option Fact.Deduction csys.uf with
                        | None ->
                            let uf_1 = UF.filter Fact.Deduction csys.uf (fun form ->
                              let simple_csys = simple_of_formula csys form in
                              try
                                let _ = one_mgs simple_csys in
                                true
                              with
                                | Not_found -> false
                              ) in

                            if not !ded_occurs && UF.unsolved_occurs Fact.Deduction uf_1
                            then ded_occurs := true;

                            { csys with uf = uf_1 } :: acc_csys
                        | Some _ -> (ded_occurs := true; csys :: acc_csys)
                    ) [] csys_set.Set.csys_list
                  in

                  { csys_set with Set.csys_list = new_csys_list; Set.ded_occurs = !ded_occurs }
          end
        else csys_set
      in

      let new_csys_set_2 =
        if new_csys_set_1.Set.eq_occurs = Set.No_equality
        then new_csys_set_1
        else
          begin
            let eq_occurs = ref false in

            let new_csys_list =
              List.fold_left (fun acc_csys csys ->
                match UF.choose_solved_option Fact.Equality csys.uf with
                  | None ->
                      begin match UF.choose_unsolved_option Fact.Equality csys.uf with
                        | None -> csys::acc_csys
                        | Some form ->
                            let simple_csys = simple_of_formula csys form in
                            begin try
                              let _ = one_mgs simple_csys in
                              eq_occurs := true;
                              csys :: acc_csys
                            with
                              | Not_found -> { csys with uf = UF.remove_unsolved_equality csys.uf } :: acc_csys
                            end
                      end
                  | Some _  -> (eq_occurs := true; csys :: acc_csys)
              ) [] new_csys_set_1.Set.csys_list
            in

            if !eq_occurs
            then { new_csys_set_1 with Set.csys_list = new_csys_list }
            else { new_csys_set_1 with Set.csys_list = new_csys_list; Set.eq_occurs = Set.No_equality }
          end
      in

      f_continuation new_csys_set_2 f_next

  let rec normalisation_NoEq_Solved_Ded csys_set f_continuation f_next =
    Config.debug (fun () ->
      if csys_set.Set.ded_occurs = false && List.exists (fun csys -> UF.solved_occurs Fact.Deduction csys.uf || UF.unsolved_occurs Fact.Deduction csys.uf) csys_set.Set.csys_list
      then Config.internal_error "[constraint_system.ml >> Rule.normalisation_NoEq_Solved_Ded] Presence of deduction even though it was indicated otherwise.";

      if csys_set.Set.eq_occurs = Set.No_equality && List.exists (fun csys -> UF.solved_occurs Fact.Equality csys.uf || UF.unsolved_occurs Fact.Equality csys.uf) csys_set.Set.csys_list
      then Config.internal_error "[constraint_system.ml >> Rule.normalisation_NoEq_Solved_Ded] Presence of equality even though it was indicated otherwise."
    );
    normalisation_SDF_or_consequence csys_set
      {
        addition = (fun csys_set_1 f_next_1 ->
          normalisation_split_eq csys_set_1
            {
              no_split = f_continuation;
              split = (fun csys_set_2 f_next_2 ->
                if csys_set_2.Set.ded_occurs
                then normalisation_NoEq_Solved_Ded csys_set_2 f_continuation f_next_2
                else f_continuation csys_set_2 f_next_2
                )
            } f_next_1
          );
        removal = f_continuation
      } f_next

  let normalisation_without_mgs_check csys_set f_continuation f_next =
    Config.debug (fun () ->
      if csys_set.Set.ded_occurs = false && List.exists (fun csys -> UF.solved_occurs Fact.Deduction csys.uf || UF.unsolved_occurs Fact.Deduction csys.uf) csys_set.Set.csys_list
      then Config.internal_error "[constraint_system.ml >> Rule.normalisation_without_mgs_check] Presence of deduction even though it was indicated otherwise."
    );

    let apply_if_NoEq_Solved_Ded csys_set_2 f_next_2 =
      if csys_set_2.Set.csys_list <> [] && csys_set_2.Set.ded_occurs && csys_set_2.Set.eq_occurs = Set.No_equality && List.for_all (fun csys -> UF.solved_occurs Fact.Deduction csys.uf) csys_set_2.Set.csys_list
      then normalisation_NoEq_Solved_Ded csys_set_2 f_continuation f_next_2
      else f_continuation csys_set_2 f_next_2
    in

    let apply_if_NoEq_Ded_occurs csys_set_2 f_next_2 =
      if csys_set_2.Set.csys_list <> [] && csys_set_2.Set.ded_occurs && csys_set_2.Set.eq_occurs = Set.No_equality
      then normalisation_NoEq_Solved_Ded csys_set_2 f_continuation f_next_2
      else f_continuation csys_set_2 f_next_2
    in

    if csys_set.Set.eq_occurs = Set.No_equality
    then
      normalisation_split_ded csys_set
        {
          split =
            (fun csys_set_1 f_next_1 ->
              if csys_set_1.Set.csys_list = [] || not (csys_set_1.Set.ded_occurs)
              then f_continuation csys_set_1 f_next_1
              else normalisation_NoEq_Solved_Ded csys_set_1 f_continuation f_next_1
            );
          no_split = apply_if_NoEq_Solved_Ded
        }
        f_next
    else
      normalisation_split csys_set
        {
          main_split_ded = apply_if_NoEq_Ded_occurs;
          main_split_but_not_ded = apply_if_NoEq_Solved_Ded;
          main_no_split = apply_if_NoEq_Solved_Ded
        } f_next

  let normalisation_after_axiom = normalisation_NoEq_Solved_Ded

  let normalisation csys_set f_continuation f_next =

    Config.debug (fun () ->
      if csys_set.Set.ded_occurs = false && List.exists (fun csys -> UF.solved_occurs Fact.Deduction csys.uf || UF.unsolved_occurs Fact.Deduction csys.uf) csys_set.Set.csys_list
      then Config.internal_error "[constraint_system.ml >> Rule.internal_normalisationm] Presence of deduction even though it was indicated otherwise."
    );

    normalisation_mgs csys_set (fun csys_set_1 f_next_1 -> normalisation_without_mgs_check csys_set_1 f_continuation f_next_1) f_next

  (**** The rule SAT ****)

  let rec sat csys_set continuation_func f_next =

    let rec explore_csys_set prev_csys_set = function
      | [] -> None
      | csys::q when is_solved csys -> (explore_csys_set [@tailcall]) (csys::prev_csys_set) q
      | csys::q -> Some (csys, List.rev_append prev_csys_set q)
    in

    match explore_csys_set [] csys_set.Set.csys_list with
      | Some (csys,other_csys) ->
          let simple_csys = simple_of csys in

          let mgs_list = mgs simple_csys in

          if mgs_list =  []
          then (sat [@tailcall]) { csys_set with Set.csys_list = other_csys } continuation_func f_next
          else
            begin
              let accumulator_diseq = ref [] in

              let new_f_next =
                List.fold_left (fun acc_f_next ((mgs,l_vars),_,_) ->
                  let diseq = Diseq.of_substitution Recipe mgs l_vars in

                  if Diseq.is_bot diseq
                  then Config.internal_error "[constraint_system.ml >> rule_sat] The disequation should not be the bot.";

                  accumulator_diseq := diseq :: !accumulator_diseq;

                  let new_eqsnd = Eq.apply Recipe csys.eqsnd mgs in
                  let new_i_subst_snd = Subst.compose_restricted_generic csys.i_subst_snd mgs (fun x -> Variable.quantifier_of x = Free) in

                  Config.debug (fun () ->
                    if Eq.is_bot new_eqsnd
                    then Config.internal_error "[constraint_system.ml >> internal_sat] If bot then we should not have had some mgs."
                  );

                  let data_shared =
                    {
                      share_sdf = (Array.make (SDF.cardinal csys.sdf) (dummy_recipe,false));
                      share_eqsnd = new_eqsnd;
                      share_ded = ref None;
                      share_eq = ref None;
                      share_i_subst_snd = new_i_subst_snd
                    }
                  in

                  let new_csys_list =
                    try
                      let csys' = apply_mgs_and_gather csys data_shared (mgs,l_vars) in
                      List.fold_left (fun set csys ->
                        try
                          (apply_mgs_from_gathering csys data_shared (mgs,l_vars))::set
                        with
                          | Bot -> set
                        ) [csys'] other_csys
                    with
                    | Bot ->
                        List.fold_left (fun set csys ->
                          try
                            (apply_mgs_from_gathering csys data_shared (mgs,l_vars))::set
                          with
                            | Bot -> set
                          ) [] other_csys
                  in

                  let new_csys_set = { csys_set with Set.csys_list = new_csys_list } in

                  (fun () -> (continuation_func.positive [@tailcall]) new_csys_set acc_f_next)
                ) f_next mgs_list in


              let new_eqsnd = List.fold_left Eq.wedge csys.eqsnd !accumulator_diseq in

              (* Do we necessarily need to chenck the uniformity for the negative part ? *)
              let negative_csys_list =
                List.fold_left (fun acc csys ->
                  let csys' = { csys with eqsnd = new_eqsnd } in
                  if Uniformity_Set.exists_pair_with_same_protocol_term csys'.sub_cons (Eq.implies Recipe csys'.eqsnd)
                  then acc
                  else csys'::acc
                ) [] other_csys
              in

              let negative_csys_set = { csys_set with Set.csys_list = negative_csys_list } in

              (continuation_func.negative [@tailcall]) negative_csys_set new_f_next
            end
      | None -> (continuation_func.not_applicable [@tailcall]) csys_set f_next

  (**** The rule SAT Private ****)

  let sat_private csys_set continuation_func f_next =
    if csys_set.Set.set_private_channels
    then
      let result_rule = ref [] in

      let rec explore_csys_set prev_csys_set = function
        | [] -> result_rule := prev_csys_set; None
        | csys::q when csys.private_channels = [] -> (explore_csys_set [@tailcall]) (csys::prev_csys_set) q
        | csys::q ->
            let ch = List.hd csys.private_channels in

            let simple_csys = simple_of_private csys ch in

            let exists_mgs =
              try
                let ((mgs,l_vars),_,_) = one_mgs simple_csys in
                let mgs_csys,_ = Subst.split_domain mgs (fun x -> Variable.type_of x <> csys.size_frame + 1) in
                let l_vars_csys = List.filter_unordered (fun x -> Variable.type_of x <> csys.size_frame + 1) l_vars in
                Some (mgs_csys, l_vars_csys)
              with Not_found -> None
            in

            begin match exists_mgs with
              | None ->
                  let new_csys = { csys with private_channels = List.tl csys.private_channels} in
                  (explore_csys_set [@tailcall]) prev_csys_set (new_csys::q)
              | Some mgs -> Some(csys, List.rev_append prev_csys_set q, mgs)
            end
      in

      match explore_csys_set [] csys_set.Set.csys_list with
        | Some(csys,other_csys,(mgs,l_vars)) ->
            let diseq = Diseq.of_substitution Recipe mgs l_vars in

            if Diseq.is_bot diseq
            then Config.internal_error "[constraint_system.ml >> internal_sat_private] The disequation should not be the bot.";

            let new_eqsnd = Eq.apply Recipe csys.eqsnd mgs in
            let new_i_subst_snd = Subst.compose_restricted_generic csys.i_subst_snd mgs (fun x -> Variable.quantifier_of x = Free) in

            Config.debug (fun () ->
              if Eq.is_bot new_eqsnd
              then Config.internal_error "[constraint_system.ml >> internal_sat_disequation] If bot then we should not have had some mgs."
            );

            let positive_csys_set =
              if other_csys = []
              then { csys_set with Set.csys_list = [] }
              else
                let one_csys = List.hd other_csys in

                let data_shared =
                  {
                    share_sdf = (Array.make (SDF.cardinal csys.sdf) (dummy_recipe,false));
                    share_eqsnd = new_eqsnd;
                    share_ded = ref None;
                    share_eq = ref None;
                    share_i_subst_snd = new_i_subst_snd
                  }
                in

                let new_csys_list =
                  try
                    let csys' = apply_mgs_and_gather one_csys data_shared (mgs,l_vars) in
                    List.fold_left (fun set csys ->
                      try
                        (apply_mgs_from_gathering csys data_shared (mgs,l_vars))::set
                      with
                        | Bot -> set
                      ) [csys'] (List.tl other_csys)
                  with
                  | Bot ->
                      List.fold_left (fun set csys ->
                        try
                          (apply_mgs_from_gathering csys data_shared (mgs,l_vars))::set
                        with
                          | Bot -> set
                        ) [] (List.tl other_csys)
                in

                { csys_set with Set.csys_list = new_csys_list }
            in

            let new_eqsnd = Eq.wedge csys.eqsnd diseq in

            let negative_csys_list =
              List.fold_left (fun acc csys ->
                let csys' = { csys with eqsnd = new_eqsnd } in
                if Uniformity_Set.exists_pair_with_same_protocol_term csys'.sub_cons (Eq.implies Recipe csys'.eqsnd)
                then acc
                else csys'::acc
              ) [] (csys::other_csys)
            in

            let negative_csys_set = { csys_set with Set.csys_list = negative_csys_list } in

            (continuation_func.positive [@tailcall]) positive_csys_set (fun () -> (continuation_func.negative [@tailcall]) negative_csys_set f_next)
        | None -> (continuation_func.not_applicable [@tailcall]) { csys_set with Set.csys_list = !result_rule } f_next
    else (continuation_func.not_applicable [@tailcall]) csys_set f_next

  (**** The rule SAT Disequation ****)

  let sat_disequation csys_set continuation_func f_next =

    let result_rule = ref [] in

    let rec explore_csys_set prev_csys_set = function
      | [] -> result_rule := prev_csys_set; None
      | csys::q when Eq.is_top csys.eqfst -> (explore_csys_set [@tailcall]) (csys::prev_csys_set) q
      | csys::q ->
          let diseq_op, eqfst_1 = Eq.extract csys.eqfst in

          let diseq = match diseq_op with
            | None -> Config.internal_error "[constraint_system.ml >> internal_sat_disequations] The formula should not be bot or top."
            | Some(diseq) -> diseq
          in
          let new_csys = { csys with eqfst = eqfst_1 } in

          let simple_csys = simple_of_disequation new_csys diseq in

          let mgs_list = mgs simple_csys in

          if mgs_list = []
          then (explore_csys_set [@tailcall]) prev_csys_set (new_csys::q)
          else Some(new_csys, List.rev_append prev_csys_set q, mgs_list)
    in

    match explore_csys_set [] csys_set.Set.csys_list with
      | Some(csys,other_csys,mgs_list) ->
          let accumulator_diseq = ref [] in

          let new_f_next =
            List.fold_left (fun acc_f_next ((mgs,l_vars),_,_) ->
              let diseq = Diseq.of_substitution Recipe mgs l_vars in

              if Diseq.is_bot diseq
              then Config.internal_error "[constraint_system.ml >> internal_sat_disequations] The disequation should not be the bot.";

              accumulator_diseq := diseq :: !accumulator_diseq;

              let new_eqsnd = Eq.apply Recipe csys.eqsnd mgs in
              let new_i_subst_snd = Subst.compose_restricted_generic csys.i_subst_snd mgs (fun x -> Variable.quantifier_of x = Free) in

              Config.debug (fun () ->
                if Eq.is_bot new_eqsnd
                then Config.internal_error "[constraint_system.ml >> internal_sat_disequation] If bot then we should not have had some mgs."
              );

              let data_shared =
                {
                  share_sdf = (Array.make (SDF.cardinal csys.sdf) (dummy_recipe,false));
                  share_eqsnd = new_eqsnd;
                  share_ded = ref None;
                  share_eq = ref None;
                  share_i_subst_snd = new_i_subst_snd
                }
              in

              let new_csys_list =
                try
                  let csys' = apply_mgs_and_gather (List.hd other_csys) data_shared (mgs,l_vars) in
                  List.fold_left (fun set csys ->
                    try
                      (apply_mgs_from_gathering csys data_shared (mgs,l_vars))::set
                    with
                      | Bot -> set
                    ) [csys'] (List.tl other_csys)
                with
                | Bot ->
                    List.fold_left (fun set csys ->
                      try
                        (apply_mgs_from_gathering csys data_shared (mgs,l_vars))::set
                      with
                        | Bot -> set
                      ) [] (List.tl other_csys)
              in

              let new_csys_set = { csys_set with Set.csys_list = new_csys_list } in

              (fun () -> (continuation_func.positive [@tailcall]) new_csys_set acc_f_next)
            ) f_next mgs_list
          in

          let new_eqsnd = List.fold_left Eq.wedge csys.eqsnd !accumulator_diseq in

          let negative_csys_list =
            List.fold_left (fun acc csys ->
              let csys' = { csys with eqsnd = new_eqsnd } in
              if Uniformity_Set.exists_pair_with_same_protocol_term csys'.sub_cons (Eq.implies Recipe csys'.eqsnd)
              then acc
              else csys'::acc
            ) [] (csys::other_csys)
          in

          let negative_csys_set = { csys_set with Set.csys_list = negative_csys_list } in

          (continuation_func.negative [@tailcall]) negative_csys_set new_f_next
      | None -> (continuation_func.not_applicable [@tailcall]) { csys_set with Set.csys_list = !result_rule } f_next

  (**** The rule SAT Formula ****)

  exception Rule_Sat_Formula_applied of mgs

  let sat_formula csys_set continuation_func f_next =

    let is_rule_sat_formula_applicable =
      try
        List.iter (fun csys ->
          match UF.choose_unsolved_option Fact.Deduction csys.uf with
            | Some form ->
                let simple_csys = simple_of_formula csys form in

                begin
                  try
                    let (mgs,_,_) = one_mgs simple_csys in
                    raise (Rule_Sat_Formula_applied mgs)
                  with
                    | Not_found -> Config.internal_error "[Constraint_system.ml >> internal_sat_formula] The unsolved formula should have at least one most general solution (it should have been removed by the normalisation rules)"
                end
            | None ->
                begin match UF.choose_unsolved_option Fact.Equality csys.uf with
                  | Some form ->
                      let simple_csys = simple_of_formula csys form in

                      begin
                        try
                          let (mgs,_,_) = one_mgs simple_csys in
                          raise (Rule_Sat_Formula_applied mgs)
                        with
                          | Not_found -> Config.internal_error "[Constraint_system.ml >> internal_sat_formula] The unsolved formula should have at least one most general solution (it should have been removed by the normalisation rules) (2)"
                      end
                  | None -> ()
                end
        ) csys_set.Set.csys_list;
        None
      with Rule_Sat_Formula_applied mgs -> Some mgs
    in

    match is_rule_sat_formula_applicable with
      | None -> (continuation_func.not_applicable [@tailcall]) csys_set f_next
      | Some (mgs,l_vars) ->
          let one_csys = List.hd csys_set.Set.csys_list in

          let new_eqsnd = Eq.apply Recipe one_csys.eqsnd mgs in
          let new_i_subst_snd = Subst.compose_restricted_generic one_csys.i_subst_snd mgs (fun x -> Variable.quantifier_of x = Free) in

          Config.debug (fun () ->
            if Subst.is_identity mgs
            then Config.internal_error "[constraint_system.ml >> internal_sat_formula] It should not be the identity mgs (otherwise the formula would have been solved)."
          );

          let data_shared =
            {
              share_sdf = (Array.make (SDF.cardinal one_csys.sdf) (dummy_recipe,false));
              share_eqsnd = new_eqsnd;
              share_ded = ref None;
              share_eq = ref None;
              share_i_subst_snd = new_i_subst_snd
            }
          in

          let positive_csys_list =
            try
              let one_csys' = apply_mgs_and_gather one_csys data_shared (mgs,l_vars) in
              List.fold_left (fun set csys ->
                try
                  (apply_mgs_from_gathering csys data_shared (mgs,l_vars))::set
                with
                  | Bot -> set
                ) [one_csys'] (List.tl csys_set.Set.csys_list)
            with
            | Bot ->
                List.fold_left (fun set csys ->
                  try
                    (apply_mgs_from_gathering csys data_shared (mgs,l_vars))::set
                  with
                    | Bot -> set
                  ) [] (List.tl csys_set.Set.csys_list)
          in

          let positive_csys_set = { csys_set with Set.csys_list = positive_csys_list } in

          let diseq = Diseq.of_substitution Recipe mgs l_vars in

          if Diseq.is_bot diseq
          then Config.internal_error "[constraint_system.ml >> rule_sat_formula] The disequation should not be the bot.";

          let new_eqsnd = Eq.wedge one_csys.eqsnd diseq in

          let negative_csys_list =
            List.fold_left (fun acc csys ->
              let csys' = { csys with eqsnd = new_eqsnd } in
              if Uniformity_Set.exists_pair_with_same_protocol_term csys'.sub_cons (Eq.implies Recipe csys'.eqsnd)
              then acc
              else csys'::acc
            ) [] csys_set.Set.csys_list
          in

          let negative_csys_set = { csys_set with Set.csys_list = negative_csys_list } in

          (normalisation [@tailcall]) negative_csys_set continuation_func.negative (fun () -> (normalisation [@tailcall]) positive_csys_set continuation_func.positive f_next)

  (**** The rule Equality Constructor ****)

  let create_eq_constructor_formula csys id_sdf recipe symbol =
    let fact = SDF.get csys.sdf id_sdf in

    let term = Fact.get_protocol_term fact in

    if is_function term
    then
      let symb = root term in

      if Symbol.is_equal symb symbol
      then
        match Tools.partial_consequence Recipe csys.sdf csys.df recipe with
          | None -> Config.internal_error "[constraint_system.ml >> create_eq_constructor_formula] The recipe should be consequence."
          | Some (_,t) ->
              let head = Fact.create_equality_fact (Fact.get_recipe fact) recipe in
              Fact.create Fact.Equality head [term,t]
      else raise Fact.Bot
    else raise Fact.Bot

  let add_when_mgs_exists_eq csys form =
    if Fact.is_fact form
    then { csys with uf = UF.add_equality csys.uf form }
    else
      let simple_csys = simple_of_formula csys form in
      try
        ignore (one_mgs simple_csys);
        { csys with uf = UF.add_equality csys.uf form }
      with
        | Not_found -> csys

  let equality_constructor csys_set continuation_func f_next =

    let rec explore_csys explored_csys_set = function
      | [] -> None, explored_csys_set
      | csys::q_csys_set ->
          if csys.equality_constructor_to_checked = []
          then explore_csys (csys::explored_csys_set) q_csys_set
          else
            begin
              let id_sdf = List.hd csys.equality_constructor_to_checked in
              let fact = SDF.get csys.sdf id_sdf in

              let term = Fact.get_protocol_term fact in

              if is_function term
              then
                begin
                  let symb = root term in

                  Config.debug (fun () ->
                    if Symbol.get_arity symb = 0 && Symbol.is_public symb
                    then Config.internal_error "[constraint_system.ml >> internal_equality_constructor] A public function symbol should not be in SDF."
                  );

                  if Symbol.is_public symb
                  then
                    begin
                      let simple_recipe, simple_csys = simple_of_equality_constructor csys symb term in

                      try
                        let ((mgs,l_vars), _, _) = one_mgs simple_csys in
                        (* Need to restrict the mgs  to the variables of the constraint system *)
                        Config.debug (fun () ->
                          if List.exists (fun x -> Variable.type_of x = csys.size_frame) l_vars
                          then Config.internal_error "[Constraint_system.ml >> rule_equality_constructor] The list l_vars should not contain second-order variable with the maximal type var."
                        );

                        let mgs_csys, mgs_form = Subst.split_domain mgs (fun x -> Variable.type_of x <> csys.size_frame) in

                        let recipe = Subst.apply mgs_form simple_recipe (fun r f -> f r) in

                        (Some (mgs_csys, l_vars, id_sdf, recipe, symb)), List.rev_append (csys::q_csys_set) explored_csys_set
                      with
                        | Not_found ->
                            explore_csys explored_csys_set (
                              { csys with
                                equality_constructor_to_checked = List.tl csys.equality_constructor_to_checked;
                                equality_constructor_checked = id_sdf::csys.equality_constructor_checked
                              } ::q_csys_set
                            )
                    end
                  else
                    explore_csys explored_csys_set (
                      { csys with
                        equality_constructor_to_checked = List.tl csys.equality_constructor_to_checked;
                        equality_constructor_checked = csys.equality_constructor_checked
                      } ::q_csys_set
                    )
                end
              else
                explore_csys explored_csys_set (
                  { csys with
                    equality_constructor_to_checked = List.tl csys.equality_constructor_to_checked;
                    equality_constructor_checked = csys.equality_constructor_checked
                  } ::q_csys_set
                )
            end
    in

    match explore_csys [] csys_set.Set.csys_list with
      | None, csys_set_1 -> (continuation_func.not_applicable [@tailcall]) { csys_set with Set.csys_list = csys_set_1 } f_next
      | Some (mgs_csys, l_vars, id_sdf, recipe, symb), csys_set_1 ->

          if Subst.is_identity mgs_csys
          then
            begin
              Config.debug (fun () ->
                if l_vars <> []
                then Config.internal_error "[Constraint_system.ml >> internal_equality] An identity substitution should imply an empty list of created variables"
              );
              let positive_csys_list = List.fold_left (fun set csys ->
                try
                  let form_1 = create_eq_constructor_formula csys id_sdf recipe symb in
                  (add_when_mgs_exists_eq csys form_1):: set
                with
                  | Fact.Bot -> csys::set
                ) [] csys_set_1
              in
              let positive_csys_set = { csys_set with Set.eq_occurs = Set.Constructor_SDF(id_sdf, symb) ; Set.csys_list = positive_csys_list } in
              (normalisation_without_mgs_check [@tailcall]) positive_csys_set continuation_func.positive f_next
            end
          else
            begin
              let one_csys = List.hd csys_set_1 in

              let new_eqsnd = Eq.apply Recipe one_csys.eqsnd mgs_csys in
              let new_i_subst_snd = Subst.compose_restricted_generic one_csys.i_subst_snd mgs_csys (fun x -> Variable.quantifier_of x = Free) in

              let data_shared =
                {
                  share_sdf = (Array.make (SDF.cardinal one_csys.sdf) (dummy_recipe,false));
                  share_eqsnd = new_eqsnd;
                  share_ded = ref None;
                  share_eq = ref None;
                  share_i_subst_snd = new_i_subst_snd
                }
              in

              let positive_csys_list =
                try
                  let one_csys' = apply_mgs_and_gather one_csys data_shared (mgs_csys,l_vars) in
                  let one_csys'' =
                    try
                      let form_1 = create_eq_constructor_formula one_csys' id_sdf recipe symb in
                      add_when_mgs_exists_eq one_csys' form_1
                    with
                      | Fact.Bot -> one_csys'
                  in
                  List.fold_left (fun set csys ->
                    try
                      let csys_1 = apply_mgs_from_gathering csys data_shared (mgs_csys,l_vars) in
                      begin try
                        let form_1 = create_eq_constructor_formula csys_1 id_sdf recipe symb in
                        (add_when_mgs_exists_eq csys_1 form_1) :: set
                      with
                        | Fact.Bot -> csys_1::set
                      end
                    with
                      | Bot -> set
                    ) [one_csys''] (List.tl csys_set_1)
                with
                | Bot ->
                    List.fold_left (fun set csys ->
                      try
                        let csys_1 = apply_mgs_from_gathering csys data_shared (mgs_csys,l_vars) in
                        begin try
                          let form_1 = create_eq_constructor_formula csys_1 id_sdf recipe symb in
                          (add_when_mgs_exists_eq csys_1 form_1) :: set
                        with
                          | Fact.Bot -> csys_1::set
                        end
                      with
                        | Bot -> set
                      ) [] (List.tl csys_set_1)
              in

              let positive_csys_set = { csys_set with Set.csys_list = positive_csys_list; eq_occurs = Set.Constructor_SDF(id_sdf, symb) } in

              let diseq = Diseq.of_substitution Recipe mgs_csys l_vars in

              let new_eqsnd = Eq.wedge one_csys.eqsnd diseq in

              let negative_csys_list =
                List.fold_left (fun acc csys ->
                  let csys' = { csys with eqsnd = new_eqsnd } in
                  if Uniformity_Set.exists_pair_with_same_protocol_term csys'.sub_cons (Eq.implies Recipe csys'.eqsnd)
                  then acc
                  else csys'::acc
                ) [] csys_set_1
              in

              let negative_csys_set = { csys_set with Set.csys_list = negative_csys_list } in

              (normalisation [@tailcall]) negative_csys_set continuation_func.negative (fun () -> (normalisation [@tailcall]) positive_csys_set continuation_func.positive f_next)
            end

  (**** The rule Equality ****)

  let equality csys_set continuation_func f_next =

    let rec explore_csys explored_csys_set = function
      | [] -> None, explored_csys_set
      | csys::q_csys_set ->
          if csys.equality_to_checked = []
          then explore_csys (csys::explored_csys_set) q_csys_set
          else
            begin
              let (last_fact,_) = SDF.last_entry csys.sdf in

              let id_sdf = List.hd csys.equality_to_checked in
              let fact = SDF.get csys.sdf id_sdf in

              let term = Fact.get_protocol_term fact in
              let last_term = Fact.get_protocol_term last_fact in

              let head = Fact.create_equality_fact (Fact.get_recipe fact) (Fact.get_recipe last_fact) in

              try
                let form = Fact.create Fact.Equality head [(term,last_term)] in

                let simple_csys = simple_of_formula csys form in

                let ((mgs,l_vars), _, _) = one_mgs simple_csys in

                Some (mgs, l_vars, id_sdf), List.rev_append (csys::q_csys_set) explored_csys_set
              with
                | Fact.Bot | Not_found -> (explore_csys [@tailcall]) explored_csys_set ({ csys with equality_to_checked = List.tl csys.equality_to_checked }::q_csys_set)
            end
    in

    match explore_csys [] csys_set.Set.csys_list with
      | None, csys_set_1 -> (continuation_func.not_applicable [@tailcall]) { csys_set with Set.csys_list = csys_set_1 } f_next
      | Some (mgs,l_vars, id_sdf), csys_set_1 ->

          if Subst.is_identity mgs
          then
            begin
              Config.debug (fun () ->
                if l_vars <> []
                then Config.internal_error "[Constraint_system.ml >> internal_equality] An identity substitution should imply an empty list of created variables"
              );
              let last_id_ref = ref 0 in

              let positive_csys_list =
                List.fold_left (fun set csys ->
                  try
                    let (last_fact,last_id) = SDF.last_entry csys.sdf in
                    last_id_ref := last_id;

                    let fact = SDF.get csys.sdf id_sdf in

                    let term = Fact.get_protocol_term fact in
                    let last_term = Fact.get_protocol_term last_fact in

                    let head = Fact.create_equality_fact (Fact.get_recipe fact) (Fact.get_recipe last_fact) in

                    let form = Fact.create Fact.Equality head [(term,last_term)] in

                    (add_when_mgs_exists_eq csys form) :: set
                  with
                    | Fact.Bot -> csys::set
                ) [] csys_set_1
              in

              let positive_csys_set = { csys_set with Set.csys_list = positive_csys_list; Set.eq_occurs = Set.Equality_SDF (!last_id_ref, id_sdf) } in

              (normalisation_without_mgs_check [@tailcall]) positive_csys_set continuation_func.positive f_next
            end
          else
            begin
              let one_csys = List.hd csys_set_1 in
              let new_eqsnd = Eq.apply Recipe one_csys.eqsnd mgs in
              let new_i_subst_snd = Subst.compose_restricted_generic one_csys.i_subst_snd mgs (fun x -> Variable.quantifier_of x = Free) in

              let last_id_ref = ref 0 in

              let data_shared =
                {
                  share_sdf = (Array.make (SDF.cardinal one_csys.sdf) (dummy_recipe,false));
                  share_eqsnd = new_eqsnd;
                  share_ded = ref None;
                  share_eq = ref None;
                  share_i_subst_snd = new_i_subst_snd
                }
              in

              let positive_csys_list =
                try
                  let one_csys' = apply_mgs_and_gather one_csys data_shared (mgs,l_vars) in
                  let one_csys'' =
                    try
                      let (last_fact,last_id) = SDF.last_entry one_csys'.sdf in
                      last_id_ref := last_id;

                      let fact = SDF.get one_csys'.sdf id_sdf in

                      let term = Fact.get_protocol_term fact in
                      let last_term = Fact.get_protocol_term last_fact in

                      let head = Fact.create_equality_fact (Fact.get_recipe fact) (Fact.get_recipe last_fact) in

                      let form = Fact.create Fact.Equality head [(term,last_term)] in

                      add_when_mgs_exists_eq one_csys' form
                    with
                      | Fact.Bot -> one_csys'
                  in
                  List.fold_left (fun set csys ->
                    try
                      let csys_1 = apply_mgs_from_gathering csys data_shared (mgs,l_vars) in
                      begin try
                        let (last_fact,_) = SDF.last_entry csys_1.sdf in

                        let fact = SDF.get csys_1.sdf id_sdf in

                        let term = Fact.get_protocol_term fact in
                        let last_term = Fact.get_protocol_term last_fact in

                        let head = Fact.create_equality_fact (Fact.get_recipe fact) (Fact.get_recipe last_fact) in

                        let form = Fact.create Fact.Equality head [(term,last_term)] in

                        (add_when_mgs_exists_eq csys_1 form) :: set
                      with
                        | Fact.Bot -> csys_1::set
                      end
                    with
                      | Bot -> set
                    ) [one_csys''] (List.tl csys_set_1)
                with
                | Bot ->
                    List.fold_left (fun set csys ->
                      try
                        let csys_1 = apply_mgs_from_gathering csys data_shared (mgs,l_vars) in
                        begin try
                          let (last_fact,last_id) = SDF.last_entry csys_1.sdf in
                          last_id_ref := last_id;

                          let fact = SDF.get csys_1.sdf id_sdf in

                          let term = Fact.get_protocol_term fact in
                          let last_term = Fact.get_protocol_term last_fact in

                          let head = Fact.create_equality_fact (Fact.get_recipe fact) (Fact.get_recipe last_fact) in

                          let form = Fact.create Fact.Equality head [(term,last_term)] in

                          (add_when_mgs_exists_eq csys_1 form) :: set
                        with
                          | Fact.Bot -> csys_1::set
                        end
                      with
                        | Bot -> set
                      ) [] (List.tl csys_set_1)
              in

              let positive_csys_set = { csys_set with Set.csys_list = positive_csys_list; eq_occurs = Set.Equality_SDF (!last_id_ref, id_sdf) } in

              let diseq = Diseq.of_substitution Recipe mgs l_vars in

              let new_eqsnd = Eq.wedge one_csys.eqsnd diseq in

              let negative_csys_list =
                List.fold_left (fun acc csys ->
                  let csys' = { csys with eqsnd = new_eqsnd } in
                  if Uniformity_Set.exists_pair_with_same_protocol_term csys'.sub_cons (Eq.implies Recipe csys'.eqsnd)
                  then acc
                  else csys'::acc
                ) [] csys_set_1
              in

              let negative_csys_set = { csys_set with Set.csys_list = negative_csys_list } in

              (normalisation [@tailcall]) negative_csys_set continuation_func.negative (fun () -> (normalisation [@tailcall]) positive_csys_set continuation_func.positive f_next)
            end

  (**** The rule Rewrite ****)

  let create_generic_skeleton_formula csys id_skel recipe =
    let lhs_recipe = get_args recipe in
    let lhs_terms =
      List.map (fun r -> match Tools.partial_consequence Recipe csys.sdf csys.df r with
        | None -> Config.internal_error "[constraint_system.ml >> create_generic_skeleton_formula] The recipe should be consequence."
        | Some (_,t) -> t
      ) lhs_recipe
    in

    List.fold_left (fun acc (lhs,r) ->
      let fact = Fact.create_deduction_fact recipe r in

      try
        let form = Fact.create Fact.Deduction fact (List.combine lhs lhs_terms) in
        form::acc
      with Fact.Bot -> acc
    ) [] (Rewrite_rules.get_compatible_rewrite_rules id_skel)

  let rewrite csys_set continuation_func f_next =

    let rec explore_csys explored_csys_set = function
      | [] -> None, explored_csys_set
      | csys::q_csys_set ->
          if csys.skeletons_to_check = []
          then (explore_csys [@taicall]) (csys::explored_csys_set) q_csys_set
          else
            begin
              let (id_sdf,id_skel) = List.hd csys.skeletons_to_check in

              match simple_of_skeleton csys id_sdf id_skel with
                | None -> explore_csys explored_csys_set ({ csys with skeletons_to_check = List.tl csys.skeletons_to_check }::q_csys_set)
                | Some (recipe,simple_csys) ->
                    let is_rule_applicable =
                      try
                        let ((mgs,l_vars), _, _) = one_mgs simple_csys in

                        let mgs_form, mgs_csys  = Subst.split_domain mgs Variable.has_infinite_type in
                        let l_vars_form, l_vars_csys = List.partition_unordered Variable.has_infinite_type l_vars in

                        let snd_vars = (Rewrite_rules.get_skeleton id_skel).Rewrite_rules.snd_vars in
                        let not_instantied_vars = Subst.not_in_domain mgs_form snd_vars in

                        let (nb_vars,eq_name_1) = List.fold_left (fun (i,acc) x -> (i+1,(x, apply_function (Symbol.get_fresh_constant i) [])::acc)) (0,[]) not_instantied_vars in
                        let (_,eq_name_2) = List.fold_left (fun (i,acc) x -> (i+1,(x, apply_function (Symbol.get_fresh_constant i) [])::acc)) (nb_vars,eq_name_1) l_vars_form in
                        let subst_name = Subst.create_multiple Recipe eq_name_2 in

                        let new_mgs_form = Subst.compose mgs_form subst_name in
                        let new_recipe = Subst.apply new_mgs_form recipe (fun r f -> f r) in

                        Some(id_skel,(mgs_csys,l_vars_csys),new_recipe)
                      with
                        | Not_found -> None
                    in

                    begin match is_rule_applicable with
                      | None -> (explore_csys [@tailcall]) explored_csys_set (
                          { csys with
                            skeletons_to_check = List.tl csys.skeletons_to_check;
                            skeletons_checked = (id_sdf,id_skel)::csys.skeletons_checked
                          }::q_csys_set)
                      | _ -> is_rule_applicable, List.rev_append (csys::q_csys_set) explored_csys_set
                    end
            end
    in

    match explore_csys [] csys_set.Set.csys_list with
      | None, csys_set_1 ->
          Config.debug (fun () ->
            if List.exists (fun csys -> csys.skeletons_to_check <> []) csys_set_1
            then Config.internal_error "[constraint_system.ml >> rewrite] Skeletons to check should be empty."
          );
          (continuation_func.not_applicable [@tailcall]) { csys_set with Set.csys_list = csys_set_1 } f_next
      | Some (id_skel, (mgs_csys,l_vars), recipe), csys_set_1 ->

          if Subst.is_identity mgs_csys
          then
            begin
              Config.debug (fun () ->
                if l_vars <> []
                then Config.internal_error "[Constraint_system.ml >> internal_equality] An identity substitution should imply an empty list of created variables"
              );
              let positive_csys_list = List.fold_left (fun set csys ->
                let form_list = create_generic_skeleton_formula csys id_skel recipe in
                if form_list = []
                then csys::set
                else { csys with uf = UF.add_deduction csys.uf form_list } :: set
                ) [] csys_set_1
              in

              let positive_csys_set = { csys_set with Set.csys_list = positive_csys_list; ded_occurs = true } in

              (normalisation [@tailcall]) positive_csys_set continuation_func.positive f_next
            end
          else
            begin
              let one_csys = List.hd csys_set_1 in
              let new_eqsnd = Eq.apply Recipe one_csys.eqsnd mgs_csys in
              let new_i_subst_snd = Subst.compose_restricted_generic one_csys.i_subst_snd mgs_csys (fun x -> Variable.quantifier_of x = Free) in

              let data_shared =
                {
                  share_sdf = (Array.make (SDF.cardinal one_csys.sdf) (dummy_recipe,false));
                  share_eqsnd = new_eqsnd;
                  share_ded = ref None;
                  share_eq = ref None;
                  share_i_subst_snd = new_i_subst_snd
                }
              in

              let positive_csys_list =
                try
                  let one_csys' = apply_mgs_and_gather one_csys data_shared (mgs_csys,l_vars) in
                  let one_csys'' =
                    let form_list = create_generic_skeleton_formula one_csys' id_skel recipe in

                    if form_list = []
                    then one_csys'
                    else { one_csys' with uf = UF.add_deduction one_csys'.uf form_list }
                  in

                  List.fold_left (fun set csys ->
                    try
                      let csys_1 = apply_mgs_from_gathering csys data_shared (mgs_csys,l_vars) in
                      let form_list = create_generic_skeleton_formula csys_1 id_skel recipe in

                      if form_list = []
                      then csys_1::set
                      else { csys_1 with uf = UF.add_deduction csys_1.uf form_list } :: set
                    with
                      | Bot -> set
                    ) [one_csys''] (List.tl csys_set_1)
                with
                | Bot ->
                    List.fold_left (fun set csys ->
                      try
                        let csys_1 = apply_mgs_from_gathering csys data_shared (mgs_csys,l_vars) in
                        let form_list = create_generic_skeleton_formula csys_1 id_skel recipe in

                        if form_list = []
                        then csys_1::set
                        else { csys_1 with uf = UF.add_deduction csys_1.uf form_list } :: set
                      with
                        | Bot -> set
                      ) [] (List.tl csys_set_1)
              in

              let positive_csys_set = { csys_set with Set.csys_list = positive_csys_list; ded_occurs = true } in

              let diseq = Diseq.of_substitution Recipe mgs_csys l_vars in

              if Diseq.is_bot diseq
              then Config.internal_error "[constraint_system.ml >> rule_equality_constructor] The disequation should not be the bot.";

              let new_eq_snd = Eq.wedge one_csys.eqsnd diseq in

              let negative_csys_list =
                List.fold_left (fun acc csys ->
                  let csys' = { csys with eqsnd = new_eq_snd } in
                  if Uniformity_Set.exists_pair_with_same_protocol_term csys'.sub_cons (Eq.implies Recipe csys'.eqsnd)
                  then acc
                  else csys'::acc
                ) [] csys_set_1
              in

              let negative_csys_set = { csys_set with Set.csys_list = negative_csys_list; ded_occurs = false } in

              (normalisation [@tailcall]) negative_csys_set continuation_func.negative (fun () -> (normalisation [@tailcall]) positive_csys_set continuation_func.positive f_next)
            end
end
