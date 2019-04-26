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

    sdf : K.t;
    ik: IK.t;
    uf : UF.t;

    i_subst_fst : (fst_ord, name) Subst.t;
    i_subst_snd : (snd_ord, axiom) Subst.t;

    i_subst_ground_snd : (snd_ord, axiom) Subst.t;

    sub_cons : (fst_ord, name) Eq.t;

    (*** Lists that help determining when the rule equality needs to be applied.
      - The list equality_constructor_checked represents the elements of SDF that have been check for
        the current SDF but no mgs was found. This list must be emptyed when a new element is added to SDF
        and its previous content should be put in equality_constructor_to_checked.
      - The list equality_constructor_to_checked represents the elements of SDF that haven't been check to apply the rule equality (for constructor)
        or for which an equality fomula exists in UF but hasn't been removed yet (i.e. all recipe equivalent formula in the set are not solved.)
      - An element of SDF not appearing in both lists means that either the first order term is a name or that
        an equality formula has been successfuly added in UF and then removed.
    *)
    equality_constructor_checked : int list;
    equality_constructor_to_checked : int list;

    equality_constructor_checked_IK : int list;
    equality_constructor_to_checked_IK : int list;

    (*** Similar behaviour for the list equality_to_checked. Note that when no mgs is found, the element is removed and never put back
      even if a new element of SDF is added (since all the second order variable in the equality formula have a type stricly smaller
      then any new added element in SDF). Finally, each id in the list represents the element of SDF that is compared with the
      last entry to SDF (all the other pair would have been checked by that time.)*)
    equality_to_checked : int list;
    equality_to_checked_IK : int list;

    skeletons_checked : (int * int) list;
    skeletons_to_check : (int * int) list;

    skeletons_checked_IK : (int * int) list;
    skeletons_to_check_IK : (int * int) list;

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
        DF.iter csys.df (fun _ t -> result_vars := get_vars_with_list Protocol t (fun _ -> true) !result_vars);
        result_vars := Eq.get_vars_with_list Protocol csys.eqfst !result_vars;
        K.iter csys.sdf (fun fct -> result_vars := get_vars_with_list Protocol (Fact.get_protocol_term fct) (fun _-> true) !result_vars);
        result_vars := Subst.get_vars_with_list Protocol csys.i_subst_fst (fun _ -> true) !result_vars;
        (* Uniformity_Set.iter csys.sub_cons (fun _ t -> result_vars := get_vars_with_list Protocol t (fun _ -> true) !result_vars); *)
        !result_vars
    | Recipe ->
        DF.iter csys.df (fun x _ -> result_vars := get_vars_with_list Recipe (of_variable x) (fun _ -> true) !result_vars);
        result_vars := Eq.get_vars_with_list Recipe csys.eqsnd !result_vars;
        K.iter csys.sdf (fun fct -> result_vars := get_vars_with_list Recipe (Fact.get_recipe fct) (fun _-> true) !result_vars);
        result_vars := Subst.get_vars_with_list Recipe csys.i_subst_ground_snd (fun _ -> true) !result_vars;
        result_vars := Subst.get_vars_with_list Recipe csys.i_subst_snd (fun _ -> true) !result_vars;
        (* Uniformity_Set.iter csys.sub_cons (fun r _ -> result_vars := get_vars_with_list Recipe r (fun _ -> true) !result_vars); *)
        !result_vars

let get_names_with_list csys names_l =
  let result_vars = ref names_l in

  DF.iter csys.df (fun _ t -> result_vars := get_names_with_list Protocol t !result_vars);
  result_vars := Eq.get_names_with_list Protocol csys.eqfst !result_vars;
  K.iter csys.sdf (fun fct ->
    result_vars := get_names_with_list Protocol (Fact.get_protocol_term fct) !result_vars
  );
  result_vars := Subst.get_names_with_list Protocol csys.i_subst_fst !result_vars;
  (* Uniformity_Set.iter csys.sub_cons (fun _ t -> result_vars := get_names_with_list Protocol t !result_vars); *)
  !result_vars

let get_axioms_with_list csys ax_list =
  let result = ref ax_list in

  K.iter_within_var_type 0 csys.sdf (fun fct ->
    result := get_axioms_with_list (Fact.get_recipe fct) (fun _ -> true) !result
  );
  !result

(******** Scanning *****)

let is_solved csys = Tools.is_solved_DF csys.df

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
        let equations = Subst.equations_of (Subst.compose csys.i_subst_ground_snd  csys.i_subst_snd) in
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
      str := Printf.sprintf "%s              <div class=\"elt_csys\"><div id=\"Sdf%d\" class=\"csys%d\"%s>\\({\\sf SDF}%s = %s\\)</div></div>\n" !str id_j id_j style id_s (K.display Latex ~rho:rho csys.sdf);
      str := Printf.sprintf "%s              <div class=\"elt_csys\"><div id=\"Uf%d\" class=\"csys%d\"%s>\\({\\sf UF}%s = %s\\)</div></div>\n" !str id_j id_j style id_s (UF.display Latex ~rho:rho csys.uf);
      str := Printf.sprintf "%s              <div class=\"elt_csys\"><div id=\"Uni%d\" class=\"csys%d\"%s>\\({\\sf R}%s = %s\\)</div></div>\n" !str id_j id_j style id_s (Eq.display Latex ~rho:rho Protocol csys.sub_cons);

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

    sdf = K.empty;
    ik = IK.empty;
    uf = UF.empty;

    i_subst_fst = Subst.identity;
    i_subst_snd = Subst.identity;

    i_subst_ground_snd = Subst.identity;

    sub_cons = Eq.top;

    equality_constructor_checked = [];
    equality_constructor_to_checked = [];

    equality_constructor_checked_IK = [];
    equality_constructor_to_checked_IK = [];

    equality_to_checked = [];
    equality_to_checked_IK = [];

    skeletons_checked = [];
    skeletons_to_check = [];

    skeletons_checked_IK = [];
    skeletons_to_check_IK = [];

    history_skeleton = List.fold_left (fun acc f -> if Symbol.is_public f then (generate_history f)::acc else acc) [] !Symbol.all_destructors
  }

let apply_substitution csys subst =
  Config.debug (fun () ->
    if not (Subst.is_extended_by Protocol csys.i_subst_fst subst)
    then Config.internal_error "[constraint_system.ml >> apply_substitution] The  substitution of the constraint system should be extended by the substitution given as argument.";

    if csys.private_channels <> []
    then Config.internal_error "[constraint_system.ml >> apply_substitution] The private channels should be added after applying the substitution.";

    if csys.ik <> IK.empty
    then Config.internal_error "[Constraint_system.ml >> apply_substitution] The set of incomplete knowledge should be empty."
  );

  let new_eqfst = Eq.apply Protocol csys.eqfst subst
  and new_sub_cons = Eq.apply Protocol csys.sub_cons subst in

  if Eq.is_bot new_eqfst || Eq.is_bot new_sub_cons
  then raise Bot;

  let new_df = DF.apply csys.df subst
  and new_sdf = K.apply csys.sdf Subst.identity subst
  and new_uf = UF.apply csys.uf subst
  and new_i_subst_fst = Subst.restrict subst (fun x -> Variable.quantifier_of x = Free)
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

  new_csys

let add_basic_fact csys bfct =
  Config.debug (fun () ->
    let t = BasicFact.get_protocol_term bfct in

    let t' = Subst.apply csys.i_subst_fst t (fun x f -> f x) in

    if not (is_equal Protocol t t')
    then Config.internal_error "[constraint_system.ml >> add_basic_fact] The substitution of the constraint system should not instantiate the protocol term of the basic deduction fact."
  );

  { csys with df = DF.add csys.df bfct }

let add_disequations csys (diseq_list: (fst_ord,name) Diseq.t list) =
  { csys with eqfst = List.fold_left (fun acc diseq -> Eq.wedge acc diseq) csys.eqfst diseq_list }

let add_axiom csys ax t =
  Config.debug (fun () ->
    if csys.size_frame + 1 <> Axiom.index_of ax
    then Config.internal_error "[constraint_system.ml >> add_axiom] The axiom given as argument should have an index equal to the size of the frame + 1";

    if csys.skeletons_to_check <> []
    then Config.internal_error "[constraint_system.ml >> add_axiom] All skeletons should have been checked."
  );

  let new_size = csys.size_frame + 1 in

  { csys with
    uf = UF.add_deduction_fact csys.uf (Fact.create_deduction_fact (of_axiom ax) t);
    size_frame = new_size
  }

let instantiate_when_solved csys =
  Config.debug (fun () ->
    if not (is_solved csys)
    then Config.internal_error "[constraint_system.ml >> instantiate_when_solved] The constraint system should be solved."
  );

  let subst_fst, subst_snd =
    DF.fold (fun (acc_fst,acc_snd) x t ->
      let k = Symbol.fresh_attacker_name () in
      let fst = Subst.create Protocol (variable_of t) (apply_function k []) in
      let snd = Subst.create Recipe x (apply_function k []) in
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
    simp_SDF : K.t;
    simp_IK : IK.t;
    simp_Sub_Cons : (fst_ord, name) Eq.t;
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
      Printf.sprintf "( %s, %s, %s, %s, %s, %s )"
        (DF.display out ~rho:rho csys.simp_DF)
        (Eq.display out ~rho:rho Protocol csys.simp_EqFst)
        (Eq.display out ~rho:rho Recipe csys.simp_EqSnd)
        (K.display out ~rho:rho csys.simp_SDF)
        (IK.display out ~rho:rho csys.simp_IK)
        (Eq.display out ~rho:rho Protocol csys.simp_Sub_Cons)
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
      let link_Ik = Printf.sprintf "<a href=\"javascript:show_single('Sdf%d');\">\\({\\sf IK}%s\\)</a>" id_j id_s in
      let link_Eq1 = Printf.sprintf "<a href=\"javascript:show_single('Equn%d');\">\\({\\sf E}^1%s\\)</a>" id_j id_s in
      let link_Eq2 = Printf.sprintf "<a href=\"javascript:show_single('Eqdeux%d');\">\\({\\sf E}^2%s\\)</a>" id_j id_s in
      let link_Uni = Printf.sprintf "<a href=\"javascript:show_single('Uni%d');\">\\({\\sf R}%s\\)</a>" id_j id_s in

      str := Printf.sprintf "\\( \\mathcal{C}%s =~(\\)%s, %s, %s, %s, %s, %s\\()\\) &nbsp;&nbsp;&nbsp; <a href=\"javascript:show_class('csys%d');\">All</a>\n"
        id_s link_Df link_Eq1 link_Eq2 link_Sdf link_Ik link_Uni id_j;

      str := Printf.sprintf "%s            <div class=\"csys\">\n" !str;
      str := Printf.sprintf "%s              <div class=\"elt_csys\"><div id=\"Df%d\" class=\"csys%d\"%s>\\({\\sf D}%s = %s\\)</div></div>\n" !str id_j id_j style id_s (DF.display Latex ~rho:rho csys.simp_DF);
      str := Printf.sprintf "%s              <div class=\"elt_csys\"><div id=\"Equn%d\" class=\"csys%d\"%s>\\({\\sf E}^1%s = %s\\)</div></div>\n" !str id_j id_j style id_s (Eq.display Latex ~rho:rho Protocol csys.simp_EqFst);
      str := Printf.sprintf "%s              <div class=\"elt_csys\"><div id=\"Eqdeux%d\" class=\"csys%d\"%s>\\({\\sf E}^2%s = %s\\)</div></div>\n" !str id_j id_j style id_s (Eq.display Latex ~rho:rho Recipe csys.simp_EqSnd);
      str := Printf.sprintf "%s              <div class=\"elt_csys\"><div id=\"Sdf%d\" class=\"csys%d\"%s>\\({\\sf SDF}%s = %s\\)</div></div>\n" !str id_j id_j style id_s (K.display Latex ~rho:rho csys.simp_SDF);
      str := Printf.sprintf "%s              <div class=\"elt_csys\"><div id=\"Sdf%d\" class=\"csys%d\"%s>\\({\\sf IK}%s = %s\\)</div></div>\n" !str id_j id_j style id_s (IK.display Latex ~rho:rho csys.simp_IK);
      str := Printf.sprintf "%s              <div class=\"elt_csys\"><div id=\"Uni%d\" class=\"csys%d\"%s>\\({\\sf R}%s = %s\\)</div></div>\n" !str id_j id_j style id_s (Eq.display Latex ~rho:rho Protocol csys.simp_Sub_Cons);

      Printf.sprintf "%s            </div>\n" !str
  | _ -> Config.internal_error "[constraint_system.ml >> display] This display mode is not implemented yet."

(***** Generators ******)

let mgs csys =
  let accumulator = ref [] in

  let rec apply_rules csys mgs snd_ord_vars f_next = match Tools.unsolved_DF csys.simp_DF with
    | Data_structure.Tools.Solved ->
        accumulator := (mgs,Set_Snd_Ord_Variable.elements snd_ord_vars) :: !accumulator;
        f_next ()
    | Data_structure.Tools.UnifyVariables subst_snd ->
        let new_eqsnd = Eq.apply Recipe csys.simp_EqSnd subst_snd in
        if Eq.is_bot new_eqsnd
        then f_next ()
        else
          begin
            let snd_ord_vars' = Subst.fold (fun snd_ord x _ -> Set_Snd_Ord_Variable.remove x snd_ord) snd_ord_vars subst_snd in
            let mgs' = Subst.apply subst_snd mgs (fun mgs f -> List.fold_left (fun acc (x,r) -> (x,f r)::acc) [] mgs) in
            accumulator := (mgs',Set_Snd_Ord_Variable.elements snd_ord_vars') :: !accumulator;
            f_next ()
          end
    | Data_structure.Tools.UnsolvedFact bfact ->
        let x_snd = BasicFact.get_snd_ord_variable bfact in
        let t = BasicFact.get_protocol_term bfact in

        Config.debug (fun () ->
          if Variable.has_infinite_type x_snd
          then Config.internal_error "[constraint_system.ml >> mgs] There should not be variable with unbound type when applying mgs_restricted. Apply mgs instead."
        );

        if is_function t && Symbol.get_arity (root t) = 0 && Symbol.is_public (root t)
        then
          let recipe : recipe = apply_function (root t) [] in
          let subst_snd = Subst.create Recipe x_snd recipe in
          let new_eq_snd = Eq.apply Recipe csys.simp_EqSnd subst_snd in
          if Eq.is_bot new_eq_snd
          then f_next ()
          else
            let df_1 = DF.remove csys.simp_DF x_snd in
            let csys' =
              { csys with
                simp_DF = df_1;
                simp_EqSnd = new_eq_snd;
                simp_SDF = K.apply_recipe csys.simp_SDF subst_snd
              }
            in
            let mgs' = Subst.apply subst_snd mgs (fun mgs f -> List.fold_left (fun acc (x,r) -> (x,f r)::acc) [] mgs)
            and snd_ord_vars' = Set_Snd_Ord_Variable.remove x_snd snd_ord_vars in
            apply_rules csys' mgs' snd_ord_vars' f_next
        else
          let var_type_x_snd = Variable.type_of x_snd in
          let acc_sub_cons = ref csys.simp_Sub_Cons in

          K.find_unifier_with_recipe csys.simp_SDF t var_type_x_snd (fun r subst_fst f_next_1 ->
            if Subst.is_identity subst_fst
            then
              begin
                let subst_snd = Subst.create Recipe x_snd r in
                let new_eq_snd = Eq.apply Recipe csys.simp_EqSnd subst_snd in
                if Eq.is_bot new_eq_snd
                then f_next () (* We need f_next and not f_next_1. This is due to the fact that this fact is the only one that can deduce the basic fact following the definition of a solution. *)
                else
                  let df_1 = DF.remove csys.simp_DF x_snd in
                  let csys' =
                    { csys with
                      simp_DF = df_1;
                      simp_EqSnd = new_eq_snd;
                      simp_SDF = K.apply_recipe csys.simp_SDF subst_snd
                    }
                  in
                  let mgs' = Subst.apply subst_snd mgs (fun mgs f -> List.fold_left (fun acc (x,r) -> (x,f r)::acc) [] mgs)
                  and snd_ord_vars' = Set_Snd_Ord_Variable.remove x_snd snd_ord_vars in
                  apply_rules csys' mgs' snd_ord_vars' f_next
              end
            else
              let diseq = Diseq.of_substitution_protocol subst_fst in
              let subst_snd = Subst.create Recipe x_snd r in
              let new_eq_fst = Eq.apply Protocol csys.simp_EqFst subst_fst in
              if Eq.is_bot new_eq_fst
              then f_next_1 ()
              else
                let new_sub_cons = Eq.apply Protocol csys.simp_Sub_Cons subst_fst in
                if Eq.is_bot new_sub_cons
                then f_next_1 ()
                else
                  begin
                    acc_sub_cons := Eq.wedge !acc_sub_cons diseq;
                    let new_eq_snd = Eq.apply Recipe csys.simp_EqSnd subst_snd in
                    if Eq.is_bot new_eq_snd
                    then f_next_1 ()
                    else
                      let df_1 = DF.remove csys.simp_DF x_snd in
                      let df_2 = DF.apply df_1 subst_fst in
                      let csys' =
                        { csys with
                          simp_DF = df_2;
                          simp_EqFst = new_eq_fst;
                          simp_EqSnd = new_eq_snd;
                          simp_SDF = K.apply csys.simp_SDF subst_snd subst_fst;
                          simp_Sub_Cons = new_sub_cons
                        }
                      in
                      let mgs' = Subst.apply subst_snd mgs (fun mgs f -> List.fold_left (fun acc (x,r) -> (x,f r)::acc) [] mgs)
                      and snd_ord_vars' = Set_Snd_Ord_Variable.remove x_snd snd_ord_vars in
                      apply_rules csys' mgs' snd_ord_vars' f_next_1
                  end
          ) (fun () ->
            if is_name t
            then f_next ()
            else
              let symb = root t in
              if Symbol.is_public symb
              then
                let args_of_term = get_args t in

                let vars_snd = Variable.fresh_list Recipe Existential (Variable.snd_ord_type var_type_x_snd) (Symbol.get_arity symb) in
                let vars_snd_as_term = List.map of_variable vars_snd in

                let recipe = apply_function symb vars_snd_as_term in
                let subst_snd = Subst.create Recipe x_snd recipe in

                let new_eq_snd = Eq.apply Recipe csys.simp_EqSnd subst_snd in
                if Eq.is_bot new_eq_snd
                then f_next ()
                else
                  let ded_fact_list = List.map2 BasicFact.create vars_snd args_of_term in

                  let df_1 = DF.remove csys.simp_DF x_snd in
                  let df_2 = List.fold_left (fun df b_fct -> DF.add df b_fct) df_1 ded_fact_list in

                  let csys' = { csys with
                      simp_DF = df_2;
                      simp_EqSnd = new_eq_snd;
                      simp_SDF = K.apply_recipe csys.simp_SDF subst_snd;
                      simp_Sub_Cons = !acc_sub_cons
                    }
                  in
                  let mgs' = Subst.apply subst_snd mgs (fun mgs f -> List.fold_left (fun acc (x,r) -> (x,f r)::acc) [] mgs)
                  and snd_ord_vars' = Set_Snd_Ord_Variable.remove x_snd snd_ord_vars in
                  let snd_ord_vars'' = List.fold_left (fun set x -> Set_Snd_Ord_Variable.add x set) snd_ord_vars' vars_snd in
                  (apply_rules [@tailcall]) csys' mgs' snd_ord_vars'' f_next
              else f_next ()
          )
  in

  (* We first check if the constraint is not directly bot *)

  Config.debug (fun () ->
    if Eq.is_bot csys.simp_EqFst || Eq.is_bot csys.simp_EqSnd || Eq.Mixed.is_bot csys.simp_Mixed_Eq || Eq.is_bot csys.simp_Sub_Cons
    then Config.internal_error "[constraint_system.ml >> one_mgs] The simple constraint system should not be bot."
  );

  let init_mgs = DF.fold (fun acc x _ -> (x, of_variable x)::acc) [] csys.simp_DF in

  apply_rules csys init_mgs Set_Snd_Ord_Variable.empty (fun () -> ());
  List.fold_left (fun acc_mgs (mgs,var_list) ->
    (Subst.create_multiple Recipe (List.filter_unordered (fun (r_1,r_2) -> not (is_equal Recipe (of_variable r_1) r_2)) mgs), var_list)::acc_mgs
    ) [] !accumulator

let one_mgs csys =
  let result = ref None in

  let rec apply_rules csys mgs snd_ord_vars f_next = match Tools.unsolved_DF csys.simp_DF with
    | Data_structure.Tools.Solved -> result := Some (mgs,Set_Snd_Ord_Variable.elements snd_ord_vars)
    | Data_structure.Tools.UnifyVariables subst_snd ->
        let new_eqsnd = Eq.apply Recipe csys.simp_EqSnd subst_snd in
        if Eq.is_bot new_eqsnd
        then f_next ()
        else
          let new_mixed = Eq.Mixed.apply csys.simp_Mixed_Eq Subst.identity subst_snd in
          if Eq.Mixed.is_bot new_mixed
          then f_next ()
          else
            begin
              let snd_ord_vars' = Subst.fold (fun snd_ord x _ -> Set_Snd_Ord_Variable.remove x snd_ord) snd_ord_vars subst_snd in
              let mgs' = Subst.apply subst_snd mgs (fun mgs f -> List.fold_left (fun acc (x,r) -> (x,f r)::acc) [] mgs) in
              result := Some (mgs',Set_Snd_Ord_Variable.elements snd_ord_vars')
            end
    | Data_structure.Tools.UnsolvedFact bfact ->
        let x_snd = BasicFact.get_snd_ord_variable bfact in
        let t = BasicFact.get_protocol_term bfact in

        if is_function t && Symbol.get_arity (root t) = 0 && Symbol.is_public (root t)
        then
          let recipe : recipe = apply_function (root t) [] in
          let subst_snd = Subst.create Recipe x_snd recipe in
          let new_eq_snd = Eq.apply Recipe csys.simp_EqSnd subst_snd in
          if Eq.is_bot new_eq_snd
          then f_next ()
          else
            let new_mixed = Eq.Mixed.apply csys.simp_Mixed_Eq Subst.identity subst_snd in
            if Eq.Mixed.is_bot new_mixed
            then f_next ()
            else
              let df_1 = DF.remove csys.simp_DF x_snd in
              let csys' =
                { csys with
                  simp_DF = df_1;
                  simp_EqSnd = new_eq_snd;
                  simp_Mixed_Eq = new_mixed;
                  simp_SDF = K.apply_recipe csys.simp_SDF subst_snd;
                  simp_IK = IK.apply_recipe csys.simp_IK subst_snd
                }
              in
              let mgs' = Subst.apply subst_snd mgs (fun mgs f -> List.fold_left (fun acc (x,r) -> (x,f r)::acc) [] mgs)
              and snd_ord_vars' = Set_Snd_Ord_Variable.remove x_snd snd_ord_vars in
              apply_rules csys' mgs' snd_ord_vars' f_next
        else
          let var_type_x_snd = Variable.type_of x_snd in
          let acc_sub_cons = ref csys.simp_Sub_Cons in

          let apply_resolution r subst_fst f_next_1 =
            if Subst.is_identity subst_fst
            then
              begin
                let subst_snd = Subst.create Recipe x_snd r in
                let new_eq_snd = Eq.apply Recipe csys.simp_EqSnd subst_snd in
                if Eq.is_bot new_eq_snd
                then f_next () (* We need f_next and not f_next_1. This is due to the fact that this fact is the only one that can deduce the basic fact following the definition of a solution. *)
                else
                  let new_mixed = Eq.Mixed.apply csys.simp_Mixed_Eq Subst.identity subst_snd in
                  if Eq.Mixed.is_bot new_mixed
                  then f_next ()
                  else
                    let df_1 = DF.remove csys.simp_DF x_snd in
                    let csys' =
                      { csys with
                        simp_DF = df_1;
                        simp_EqSnd = new_eq_snd;
                        simp_SDF = K.apply_recipe csys.simp_SDF subst_snd;
                        simp_IK = IK.apply_recipe csys.simp_IK subst_snd;
                        simp_Mixed_Eq = new_mixed
                      }
                    in
                    let mgs' = Subst.apply subst_snd mgs (fun mgs f -> List.fold_left (fun acc (x,r) -> (x,f r)::acc) [] mgs)
                    and snd_ord_vars' = Set_Snd_Ord_Variable.remove x_snd snd_ord_vars in
                    apply_rules csys' mgs' snd_ord_vars' f_next
              end
            else
              let diseq = Diseq.of_substitution_protocol subst_fst in
              let subst_snd = Subst.create Recipe x_snd r in
              let new_eq_fst = Eq.apply Protocol csys.simp_EqFst subst_fst in
              if Eq.is_bot new_eq_fst
              then f_next_1 ()
              else
                let new_sub_cons = Eq.apply Protocol csys.simp_Sub_Cons subst_fst in
                if Eq.is_bot new_sub_cons
                then f_next_1 ()
                else
                  begin
                    acc_sub_cons := Eq.wedge !acc_sub_cons diseq;
                    let new_eq_snd = Eq.apply Recipe csys.simp_EqSnd subst_snd in
                    if Eq.is_bot new_eq_snd
                    then f_next_1 ()
                    else
                      let new_mixed = Eq.Mixed.apply csys.simp_Mixed_Eq subst_fst subst_snd in
                      if Eq.Mixed.is_bot new_mixed
                      then f_next_1 ()
                      else
                        let df_1 = DF.remove csys.simp_DF x_snd in
                        let df_2 = DF.apply df_1 subst_fst in
                        let csys' =
                          {
                            simp_DF = df_2;
                            simp_EqFst = new_eq_fst;
                            simp_EqSnd = new_eq_snd;
                            simp_SDF = K.apply csys.simp_SDF subst_snd subst_fst;
                            simp_Sub_Cons = new_sub_cons;
                            simp_Mixed_Eq = new_mixed;
                            simp_IK = IK.apply csys.simp_IK subst_snd subst_fst
                          }
                        in
                        let mgs' = Subst.apply subst_snd mgs (fun mgs f -> List.fold_left (fun acc (x,r) -> (x,f r)::acc) [] mgs)
                        and snd_ord_vars' = Set_Snd_Ord_Variable.remove x_snd snd_ord_vars in
                        apply_rules csys' mgs' snd_ord_vars' f_next_1
                  end
          in

          let apply_cons () =
            if is_name t
            then f_next ()
            else
              let symb = root t in
              if Symbol.is_public symb
              then
                let args_of_term = get_args t in

                let vars_snd = Variable.fresh_list Recipe Existential (Variable.snd_ord_type var_type_x_snd) (Symbol.get_arity symb) in
                let vars_snd_as_term = List.map of_variable vars_snd in

                let recipe = apply_function symb vars_snd_as_term in
                let subst_snd = Subst.create Recipe x_snd recipe in

                let new_eq_snd = Eq.apply Recipe csys.simp_EqSnd subst_snd in
                if Eq.is_bot new_eq_snd
                then f_next ()
                else
                  let new_mixed = Eq.Mixed.apply csys.simp_Mixed_Eq Subst.identity subst_snd in
                  if Eq.Mixed.is_bot new_mixed
                  then f_next ()
                  else
                    let ded_fact_list = List.map2 BasicFact.create vars_snd args_of_term in

                    let df_1 = DF.remove csys.simp_DF x_snd in
                    let df_2 = List.fold_left (fun df b_fct -> DF.add df b_fct) df_1 ded_fact_list in

                    let csys' = { csys with
                        simp_DF = df_2;
                        simp_EqSnd = new_eq_snd;
                        simp_SDF = K.apply_recipe csys.simp_SDF subst_snd;
                        simp_Sub_Cons = !acc_sub_cons;
                        simp_Mixed_Eq = new_mixed;
                        simp_IK = IK.apply_recipe csys.simp_IK subst_snd
                      }
                    in
                    let mgs' = Subst.apply subst_snd mgs (fun mgs f -> List.fold_left (fun acc (x,r) -> (x,f r)::acc) [] mgs)
                    and snd_ord_vars' = Set_Snd_Ord_Variable.remove x_snd snd_ord_vars in
                    let snd_ord_vars'' = List.fold_left (fun set x -> Set_Snd_Ord_Variable.add x set) snd_ord_vars' vars_snd in
                    (apply_rules [@tailcall]) csys' mgs' snd_ord_vars'' f_next
              else f_next ()
          in

          K.find_unifier_with_recipe csys.simp_SDF t var_type_x_snd apply_resolution (fun () ->
            if var_type_x_snd = max_int
            then IK.find_unifier_with_recipe csys.simp_IK t apply_resolution apply_cons
            else apply_cons ()
          )
  in

  (* We first check if the constraint is not directly bot *)

  Config.debug (fun () ->
    if Eq.is_bot csys.simp_EqFst || Eq.is_bot csys.simp_EqSnd || Eq.Mixed.is_bot csys.simp_Mixed_Eq || Eq.is_bot csys.simp_Sub_Cons
    then Config.internal_error "[constraint_system.ml >> one_mgs] The simple constraint system should not be bot."
  );

  let init_mgs = DF.fold (fun acc x _ -> (x, of_variable x)::acc) [] csys.simp_DF in

  apply_rules csys init_mgs Set_Snd_Ord_Variable.empty (fun () -> ());

  match !result with
    | None -> None
    | Some (mgs,var_list) ->
        Some (Subst.create_multiple Recipe (List.filter_unordered (fun (r_1,r_2) -> not (is_equal Recipe (of_variable r_1) r_2)) mgs), var_list)

let simple_of csys =
  {
    simp_DF = csys.df;
    simp_EqFst = csys.eqfst;
    simp_EqSnd = csys.eqsnd;
    simp_SDF = csys.sdf;
    simp_IK = csys.ik;
    simp_Sub_Cons = csys.sub_cons;
    simp_Mixed_Eq = Eq.Mixed.top
  }

let simple_of_formula csys form =
  let mgu_hypothesis = Fact.get_mgu_hypothesis form in

  let eqfst_0 = Eq.apply Protocol csys.eqfst mgu_hypothesis in
  if Eq.is_bot eqfst_0
  then None
  else
    let sub_cons_0 = Eq.apply Protocol csys.sub_cons mgu_hypothesis in
    if Eq.is_bot sub_cons_0
    then None
    else
      let df_0 = DF.apply csys.df mgu_hypothesis
      and sdf_0 = K.apply_protocol csys.sdf mgu_hypothesis
      and ik_0 = IK.apply_protocol csys.ik mgu_hypothesis in

      Some {
        simp_DF = df_0;
        simp_EqFst = eqfst_0;
        simp_EqSnd = csys.eqsnd;
        simp_SDF = sdf_0;
        simp_IK = ik_0;
        simp_Sub_Cons = sub_cons_0;
        simp_Mixed_Eq = Eq.Mixed.top
      }

let simple_of_disequation csys diseq =
  let subst = Diseq.substitution_of diseq in

  let eqfst_0 = Eq.apply Protocol csys.eqfst subst in
  if Eq.is_bot eqfst_0
  then None
  else
    let sub_cons_0 = Eq.apply Protocol csys.sub_cons subst in
    if Eq.is_bot sub_cons_0
    then None
    else
      let df_0 = DF.apply csys.df subst
      and sdf_0 = K.apply_protocol csys.sdf subst
      and ik_0 = IK.apply_protocol csys.ik subst in

      Some {
        simp_DF = df_0;
        simp_EqFst = eqfst_0;
        simp_EqSnd = csys.eqsnd;
        simp_SDF = sdf_0;
        simp_IK = ik_0;
        simp_Sub_Cons = sub_cons_0;
        simp_Mixed_Eq = Eq.Mixed.top
      }

let simple_of_private csys ch =

  let xsnd = Variable.fresh Recipe Existential Variable.infinite_snd_ord_type in
  let b_fct = BasicFact.create xsnd ch in

  {
    simp_DF = DF.add csys.df b_fct;
    simp_EqFst = csys.eqfst;
    simp_EqSnd = csys.eqsnd;
    simp_SDF = csys.sdf;
    simp_IK = csys.ik;
    simp_Sub_Cons = csys.sub_cons;
    simp_Mixed_Eq = Eq.Mixed.top
  }

let simple_of_equality_constructor csys symb term stored_cons =
  let args = get_args term in
  if Eq.Mixed.is_top stored_cons.Tools.mixed_diseq
  then
    let vars_snd = stored_cons.Tools.snd_vars in
    let simple_recipe = apply_function symb (List.map of_variable vars_snd) in

    let b_fct_list = List.map2 (fun x t -> BasicFact.create x t) vars_snd args in

    let df_1 = List.fold_left DF.add csys.df b_fct_list in

    let simple_csys =
      {
        simp_DF = df_1;
        simp_EqFst = csys.eqfst;
        simp_EqSnd = csys.eqsnd;
        simp_SDF = csys.sdf;
        simp_IK = csys.ik;
        simp_Sub_Cons = csys.sub_cons;
        simp_Mixed_Eq = Eq.Mixed.top
      }
    in

    Some(simple_recipe, simple_csys)
  else
    let fst_subst = Subst.create_multiple Protocol (List.map2 (fun x t -> x,t) stored_cons.Tools.fst_vars args) in
    let new_diseq = Eq.Mixed.apply stored_cons.Tools.mixed_diseq fst_subst Subst.identity in
    if Eq.Mixed.is_bot new_diseq
    then None
    else
      let vars_snd = stored_cons.Tools.snd_vars in
      let simple_recipe = apply_function symb (List.map of_variable vars_snd) in

      let b_fct_list = List.map2 (fun x t -> BasicFact.create x t) vars_snd args in

      let df_1 = List.fold_left DF.add csys.df b_fct_list in

      let simple_csys =
        {
          simp_DF = df_1;
          simp_EqFst = csys.eqfst;
          simp_EqSnd = csys.eqsnd;
          simp_SDF = csys.sdf;
          simp_IK = csys.ik;
          simp_Sub_Cons = csys.sub_cons;
          simp_Mixed_Eq = new_diseq
        }
      in

      Some(simple_recipe, simple_csys)

let simple_of_equality_constructor_IK csys symb term =
  let args = get_args term in
  let vars_snd = Variable.fresh_list Recipe Existential Variable.infinite_snd_ord_type (Symbol.get_arity symb) in
  let simple_recipe = apply_function symb (List.map of_variable vars_snd) in

  let b_fct_list = List.map2 (fun x t -> BasicFact.create x t) vars_snd args in

  let df_1 = List.fold_left DF.add csys.df b_fct_list in

  let simple_csys =
    {
      simp_DF = df_1;
      simp_EqFst = csys.eqfst;
      simp_EqSnd = csys.eqsnd;
      simp_SDF = csys.sdf;
      simp_IK = csys.ik;
      simp_Sub_Cons = csys.sub_cons;
      simp_Mixed_Eq = Eq.Mixed.top
    }
  in

  simple_recipe, simple_csys

let simple_of_skeleton csys id_sdf id_skel =
  let fact = K.get csys.sdf id_sdf in

  let recipe_fact = Fact.get_recipe fact in

  let term_fact = Fact.get_protocol_term fact in
  let skel = Rewrite_rules.get_skeleton id_skel in
  let symb = root skel.Rewrite_rules.recipe in
  try
    let fst_subst = Subst.unify_protocol [term_fact,skel.Rewrite_rules.pos_term] in

    let new_eq_fst = Eq.apply Protocol csys.eqfst fst_subst in
    if Eq.is_bot new_eq_fst
    then None
    else
      let new_sub_cons = Eq.apply Protocol csys.sub_cons fst_subst in
      if Eq.is_bot new_sub_cons
      then None
      else
        let snd_subst = Subst.create Recipe skel.Rewrite_rules.pos_vars recipe_fact in

        let new_recipe = Subst.apply snd_subst skel.Rewrite_rules.recipe (fun r f -> f r) in
        let (new_lhs,new_bfct_list) =
          Subst.apply fst_subst (skel.Rewrite_rules.lhs,skel.Rewrite_rules.basic_deduction_facts) (fun (t_list,bfct_l) f ->
            List.map f t_list,
            List.fold_left (fun acc bfct -> (BasicFact.create (BasicFact.get_snd_ord_variable bfct) (f (BasicFact.get_protocol_term bfct)))::acc
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
          let sdf_1 = K.apply_protocol csys.sdf fst_subst in
          let ik_1 = IK.apply_protocol csys.ik fst_subst in
          let simple_csys =
            {
              simp_DF = df_1;
              simp_EqFst = new_eq_fst;
              simp_EqSnd = csys.eqsnd;
              simp_SDF = sdf_1;
              simp_IK = ik_1;
              simp_Sub_Cons = new_sub_cons;
              simp_Mixed_Eq = mixed_diseq
            }
          in
          Some (new_recipe,simple_csys)
  with Subst.Not_unifiable -> None

let simple_of_skeleton_IK csys id_ik id_skel =
  let fact = IK.get csys.ik id_ik in

  let recipe_fact = Fact.get_recipe fact in

  let term_fact = Fact.get_protocol_term fact in
  let skel = Rewrite_rules.get_skeleton id_skel in
  let symb = root skel.Rewrite_rules.recipe in
  try
    let fst_subst = Subst.unify_protocol [term_fact,skel.Rewrite_rules.pos_term] in

    let new_eq_fst = Eq.apply Protocol csys.eqfst fst_subst in
    if Eq.is_bot new_eq_fst
    then None
    else
      let new_sub_cons = Eq.apply Protocol csys.sub_cons fst_subst in
      if Eq.is_bot new_sub_cons
      then None
      else
        let snd_subst = Subst.create Recipe skel.Rewrite_rules.pos_vars recipe_fact in

        let new_recipe = Subst.apply snd_subst skel.Rewrite_rules.recipe (fun r f -> f r) in
        let (new_lhs,new_bfct_list) =
          Subst.apply fst_subst (skel.Rewrite_rules.lhs,skel.Rewrite_rules.basic_deduction_facts) (fun (t_list,bfct_l) f ->
            List.map f t_list,
            List.fold_left (fun acc bfct -> (BasicFact.create (BasicFact.get_snd_ord_variable bfct) (f (BasicFact.get_protocol_term bfct)))::acc
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
          let sdf_1 = K.apply_protocol csys.sdf fst_subst in
          let ik_1 = IK.apply_protocol csys.ik fst_subst in
          let simple_csys =
            {
              simp_DF = df_1;
              simp_EqFst = new_eq_fst;
              simp_EqSnd = csys.eqsnd;
              simp_SDF = sdf_1;
              simp_IK = ik_1;
              simp_Sub_Cons = new_sub_cons;
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
        DF.iter csys.simp_DF (fun _ t -> result_vars := get_vars_Term Protocol t (fun _ -> true) !result_vars);
        result_vars := Eq.get_vars_with_list Protocol csys.simp_EqFst !result_vars;
        K.iter csys.simp_SDF (fun fct -> result_vars := get_vars_Term Protocol (Fact.get_protocol_term fct) (fun _-> true) !result_vars);
        (* Uniformity_Set.iter csys.simp_Sub_Cons (fun _ t -> result_vars := get_vars_Term Protocol t (fun _ -> true) !result_vars); *)
        !result_vars
    | Recipe ->
        DF.iter csys.simp_DF (fun x _ -> result_vars := get_vars_Term Recipe (of_variable x) (fun _ -> true) !result_vars);
        result_vars := Eq.get_vars_with_list Recipe csys.simp_EqSnd !result_vars;
        K.iter csys.simp_SDF (fun fct -> result_vars := get_vars_Term Recipe (Fact.get_recipe fct) (fun _-> true) !result_vars);
        (* Uniformity_Set.iter csys.simp_Sub_Cons (fun r _ -> result_vars := get_vars_Term Recipe r (fun _ -> true) !result_vars); *)
        !result_vars

let get_names_simple_with_list csys names_l =
  let result_vars = ref names_l in

  DF.iter csys.simp_DF (fun _ t -> result_vars := get_names_Term Protocol t !result_vars);
  result_vars := Eq.get_names_with_list Protocol csys.simp_EqFst !result_vars;
  K.iter csys.simp_SDF (fun fct ->
    result_vars := get_names_Term Protocol (Fact.get_protocol_term fct) !result_vars;
    result_vars := get_names_Term Recipe (Fact.get_recipe fct) !result_vars
  );
  (* Uniformity_Set.iter csys.simp_Sub_Cons (fun _ t -> result_vars := get_names_Term Protocol t !result_vars); *)
  !result_vars

let get_axioms_simple_with_list csys ax_list =
  let result = ref ax_list in

  K.iter_within_var_type 0 csys.simp_SDF (fun fct ->
    result := get_axioms_Term (Fact.get_recipe fct) (fun _ -> true) !result
  );
  !result

(**** Operators *****)

let dummy_recipe = of_axiom (Axiom.create 1)

type data_shared =
  {
    share_sdf : recipe array;
    share_eqsnd : (snd_ord, axiom) Eq.t;
    share_ded : recipe list ref;
    share_eq : Fact.equality option ref;
    share_i_subst_snd : (snd_ord, axiom) Subst.t
  }

let apply_mgs_and_gather csys data_shared (subst_snd,list_var) =

  let new_df_1 = List.fold_left (fun df x_snd ->
    let b_fct = BasicFact.create x_snd (of_variable (Variable.fresh Protocol Existential Variable.fst_ord_type)) in
    DF.add df b_fct
    ) csys.df list_var in

  let new_df_2 = Subst.fold (fun df x _ -> DF.remove df x) new_df_1 subst_snd in

  let new_sdf_1 = K.apply_recipe_and_gather csys.sdf subst_snd data_shared.share_sdf in

  let (equations, new_sub_cons_1) =
    Subst.fold (fun (eq_l,acc_sub_cons) x r ->
      let t_fact = DF.get_protocol_term csys.df x in
      let (t,sub_cons) = Tools.consequence_uniform_recipe new_sdf_1 new_df_2 acc_sub_cons r in
      (t_fact,t)::eq_l, sub_cons
    ) ([],csys.sub_cons) subst_snd
  in

  try
    let subst_fst = Subst.unify_protocol equations in
    let new_eqfst = Eq.apply Protocol csys.eqfst subst_fst in

    if Eq.is_bot new_eqfst
    then raise Bot;

    let new_sub_cons_2 = Eq.apply Protocol new_sub_cons_1 subst_fst in

    if Eq.is_bot new_sub_cons_2
    then raise Bot;

    let new_df_3 = DF.apply new_df_2 subst_fst in
    let new_sdf_2 = K.apply_protocol new_sdf_1 subst_fst
    and new_ik = IK.apply csys.ik subst_snd subst_fst
    and new_uf_1 = UF.apply_with_gathering csys.uf subst_snd subst_fst data_shared.share_ded data_shared.share_eq
    and new_i_subst_fst = Subst.compose_restricted_generic csys.i_subst_fst subst_fst (fun x -> Variable.quantifier_of x = Free) in

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
        sdf = new_sdf_2;
        ik = new_ik;
        uf = new_uf_1;
        i_subst_fst = new_i_subst_fst;
        i_subst_snd = data_shared.share_i_subst_snd;
        sub_cons = new_sub_cons_2;
        history_skeleton = new_history
      }
    in

    new_csys
  with
    | Subst.Not_unifiable  -> raise Bot

let apply_mgs_from_gathering csys data_shared (subst_snd,list_var) =

  let new_df_1 = List.fold_left (fun df x_snd ->
    let b_fct = BasicFact.create x_snd (of_variable (Variable.fresh Protocol Existential Variable.fst_ord_type)) in
    DF.add df b_fct
    ) csys.df list_var in

  let new_df_2 = Subst.fold (fun df x _ -> DF.remove df x) new_df_1 subst_snd in

  let new_sdf_1 = K.apply_recipe_from_gathering csys.sdf data_shared.share_sdf in

  let (equations,new_sub_cons_1) =
    Subst.fold (fun (eq_l,acc_sub_cons) x r ->
      let t_fact = DF.get_protocol_term csys.df x in
      let (t,sub_cons) = Tools.consequence_uniform_recipe new_sdf_1 new_df_2 acc_sub_cons r in
      (t_fact,t)::eq_l, sub_cons
      ) ([],csys.sub_cons) subst_snd
  in

  try
    let subst_fst = Subst.unify_protocol equations in
    let new_eqfst = Eq.apply Protocol csys.eqfst subst_fst in

    if Eq.is_bot new_eqfst
    then raise Bot;

    let new_sub_cons_2 = Eq.apply Protocol new_sub_cons_1 subst_fst in

    if Eq.is_bot new_sub_cons_2
    then raise Bot;

    let new_df_3 = DF.apply new_df_2 subst_fst in

    let new_sdf_2 = K.apply_protocol new_sdf_1 subst_fst
    and new_ik = IK.apply csys.ik subst_snd subst_fst
    and new_uf_1 = UF.apply_with_gathering csys.uf subst_snd subst_fst data_shared.share_ded data_shared.share_eq
    and new_i_subst_fst = Subst.compose_restricted_generic csys.i_subst_fst subst_fst (fun x -> Variable.quantifier_of x = Free) in

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
        sdf = new_sdf_2;
        ik = new_ik;
        uf = new_uf_1;
        i_subst_fst = new_i_subst_fst;
        i_subst_snd = data_shared.share_i_subst_snd;
        sub_cons = new_sub_cons_2;
        history_skeleton = new_history
      }
    in

    new_csys
  with
    | Subst.Not_unifiable  -> raise Bot

(**********************************
**** Set of constraint systems ****
***********************************)

module Set = struct

  (** An alias for the type of constraint systems. *)
  type 'a csys = 'a t

  (** The type of set of constraint systems. *)
  type 'a t = 'a csys list

  let empty = []

  let size csys_set = List.length csys_set

  let add csys csys_set = csys::csys_set

  let choose csys_set =
    Config.debug (fun () ->
      if csys_set = []
      then Config.internal_error "[constraint_system.ml >> Set.choose] The set should not be empty.";
    );

    List.hd csys_set

  let elements csys_set = csys_set

  let of_list l_csys = l_csys

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
    explore csys_set

  (* Should not be applied on an empty constraint system *)
  let optimise_snd_ord_recipes csys_set =
    Config.debug (fun () ->
      if csys_set = []
      then Config.internal_error "[constraint_system.ml >> Set.optimise_snd_ord_recipes] Should not be applied on an empty set of constraint systems."
    );

    let csys = List.hd csys_set in

    let i_subst_ground_snd, i_subst_snd = Subst.split_domain_on_term csys.i_subst_snd is_ground in
    let new_i_subst_ground_snd = Subst.union i_subst_ground_snd csys.i_subst_ground_snd in

    List.rev_map (fun csys' -> { csys' with i_subst_snd = i_subst_snd; i_subst_ground_snd = new_i_subst_ground_snd }) csys_set

  let for_all f csys_set = List.for_all f csys_set

  let exists f csys_set = List.exists f csys_set

  let find f csys_set = List.find_opt f csys_set

  let is_empty csys_set = csys_set = []

  let iter f csys_set = List.iter f csys_set

  let display_initial id size =

    let rec go_through = function
      | 0 -> Printf.sprintf "\\mathcal{C}_%d" id
      | k -> Printf.sprintf "%s, \\mathcal{C}_%d" (go_through (k-1)) (k+id)
    in
    go_through (size-1)

  let display out ?(rho=None) ?(id=1) csys_set = match out with
    | Testing -> Printf.sprintf "{ %s }" (display_list (fun csys -> display Testing ~rho:rho csys) ", " csys_set)
    | HTML ->
        if csys_set = []
        then Printf.sprintf "\\(%s\\)" (emptyset Latex)
        else
          begin
            let str = ref (Printf.sprintf "\\( \\{ %s \\}\\) with </br>\n" (display_initial id (List.length csys_set))) in

            str := Printf.sprintf "%s            <ul>\n" !str;

            List.iteri (fun i csys ->
              str := Printf.sprintf "%s              <li>%s              </li>\n" !str (display HTML ~rho:rho ~hidden:true ~id:(i+id) csys)
            ) csys_set;

            Printf.sprintf "%s            </ul>\n" !str;
          end
    | _ -> Config.internal_error "[constraint_system.ml >> display] This display mode is not implemented yet."
end

(*************************************
***             Rules              ***
**************************************)

module Rule = struct

  (**** Some tools ****)

  let rec remove_id_from_list id = function
    | [] -> Config.internal_error "[Constraint_system.ml >> remove_id_from_list] The element to remove should be present in the list."
    | id'::q when id = id' -> q
    | id'::q -> id'::(remove_id_from_list id q)

  let add_mixed_diseq_skeleton csys =
    Config.debug (fun () ->
      if UF.number_of_deduction_facts csys.uf <> 1
      then Config.internal_error "[constraint_system.ml >> add_diseq_skeleton] There should be a solved deduction fact in UF."
    );

    let fact = UF.pop_deduction_fact csys.uf in
    let recipe = Fact.get_recipe fact in

    if is_axiom recipe
    then csys
    else
      let f = root recipe in

      let new_history =
        replace_history f (fun hist ->
          let diseq = Tools.mixed_diseq_for_skeletons csys.sdf csys.ik csys.df hist.fst_vars hist.snd_vars recipe in
          { hist with diseq = Eq.Mixed.wedge hist.diseq diseq }
        ) csys.history_skeleton
      in

      { csys with history_skeleton = new_history }

  (**** Uniformity Normalisation rule *****)

  (* let rec exploration_normalisation_uniformity prev_set = function
    | [] -> None, prev_set
    | csys :: q_csys_set ->
        match Uniformity_Set.unify_recipes_deducing_same_protocol_term csys.sub_cons with
          | Uniformity_Set.Not_uniform -> exploration_normalisation_uniformity prev_set q_csys_set
          | Uniformity_Set.Uniform -> exploration_normalisation_uniformity (csys::prev_set) q_csys_set
          | Uniformity_Set.Substitution(snd_subst,uniset) -> Some(snd_subst,uniset,csys,q_csys_set), prev_set

  let internal_normalisation_uniformity (checked_csys:'a Set.t) (to_check_csys:'a Set.t) (f_continuation: 'a Set.t -> (unit -> unit) -> unit) (f_next: unit -> unit) =

    let rec internal checked_csys to_check_csys f_next_1 = match exploration_normalisation_uniformity checked_csys to_check_csys with
      | None, checked_csys_1 -> f_continuation checked_csys_1 f_next_1
      | Some(snd_subst,uniset,csys,to_check_csys_1), checked_csys_1 ->
          let new_eqsnd = Eq.apply Recipe csys.eqsnd snd_subst in

          if Eq.is_bot new_eqsnd
          then internal checked_csys_1 to_check_csys_1 f_next_1
          else
            let new_i_subst_snd = Subst.compose_restricted_generic csys.i_subst_snd snd_subst (fun x -> Variable.quantifier_of x = Free) in

            let data_shared =
              {
                share_sdf = (Array.make (K.cardinal csys.sdf) (dummy_recipe,false));
                share_eqsnd = new_eqsnd;
                share_ded = ref [];
                share_eq = ref None;
                share_i_subst_snd = new_i_subst_snd
              }
            in

            let uniformity_to_apply = ref false in

            let positive_list =
              let csys' = apply_uniformity_subst_and_gather csys data_shared uniset snd_subst in

              let list_checked =
                List.fold_left (fun set csys ->
                  try
                    let new_csys = apply_mgs_from_gathering csys data_shared (snd_subst,[]) in

                    if Uniformity_Set.exists_recipes_deducing_same_protocol_term new_csys.sub_cons
                    then uniformity_to_apply := true;

                    new_csys::set
                  with Bot -> set
                  ) [csys'] checked_csys_1
              in
              List.fold_left (fun set csys ->
                try
                  let new_csys = apply_mgs_from_gathering csys data_shared (snd_subst,[]) in

                  if Uniformity_Set.exists_recipes_deducing_same_protocol_term new_csys.sub_cons
                  then uniformity_to_apply := true;

                  new_csys::set
                with Bot -> set
              ) list_checked to_check_csys_1
            in

            let diseq = Diseq.of_substitution snd_subst [] in
            let new_eqsnd = Eq.wedge csys.eqsnd diseq in

            let negative_checked_list = List.fold_left (fun acc csys -> { csys with eqsnd = new_eqsnd }::acc) [] checked_csys_1 in
            let negative_to_check_list = List.fold_left (fun acc csys -> { csys with eqsnd = new_eqsnd }::acc) [] to_check_csys_1 in

            if !uniformity_to_apply
            then internal [] positive_list (fun () -> internal negative_checked_list negative_to_check_list f_next_1)
            else f_continuation positive_list (fun () -> internal negative_checked_list negative_to_check_list f_next_1)
    in

    internal checked_csys to_check_csys f_next

  let normalisation_uniformity (csys_set:'a Set.t) (f_continuation: 'a Set.t -> (unit -> unit) -> unit) (f_next: unit -> unit) = internal_normalisation_uniformity [] csys_set f_continuation f_next *)

  (**** The rule Sat ****)

  let rec exploration_sat prev_set = function
    | [] -> None, prev_set
    | csys::q when is_solved csys -> exploration_sat (csys::prev_set) q
    | csys::q -> Some (csys,q), prev_set

  (* Uniformity check should have been applied beforehand *)
  let sat (f_continuation: 'a Set.t -> (unit -> unit) -> unit) (csys_set:'a Set.t) (f_next: unit -> unit) =

    let rec internal checked_csys to_check_csys f_next_1 = match exploration_sat checked_csys to_check_csys with
      | None, checked_csys_1 -> f_continuation checked_csys_1 f_next_1
      | Some(csys,to_check_csys_1), checked_csys_1 ->
          let simple_csys = simple_of csys in

          let mgs_list = mgs simple_csys in

          if mgs_list =  []
          then internal checked_csys_1 to_check_csys_1 f_next_1
          else
            begin
              let accumulator_diseq = ref [] in

              let new_f_next =
                List.fold_left (fun acc_f_next (mgs,l_vars) ->
                  let diseq = Diseq.of_substitution_recipe mgs l_vars in

                  accumulator_diseq := diseq :: !accumulator_diseq;

                  let new_eqsnd = Eq.apply Recipe csys.eqsnd mgs in
                  let new_i_subst_snd = Subst.compose_restricted_generic csys.i_subst_snd mgs (fun x -> Variable.quantifier_of x = Free) in

                  Config.debug (fun () ->
                    if Diseq.is_bot diseq
                    then Config.internal_error "[constraint_system.ml >> rule_sat] The disequation should not be the bot.";

                    if Eq.is_bot new_eqsnd
                    then Config.internal_error "[constraint_system.ml >> internal_sat] If bot then we should not have had some mgs."
                  );

                  let data_shared =
                    {
                      share_sdf = (Array.make (K.cardinal csys.sdf) dummy_recipe);
                      share_eqsnd = new_eqsnd;
                      share_ded = ref [];
                      share_eq = ref None;
                      share_i_subst_snd = new_i_subst_snd
                    }
                  in

                  let checked_list =
                    let csys' = apply_mgs_and_gather csys data_shared (mgs,l_vars) in
                    List.fold_left (fun set csys ->
                      try
                        (apply_mgs_from_gathering csys data_shared (mgs,l_vars))::set
                      with Bot -> set
                    ) [csys'] checked_csys_1
                  in

                  let to_check_list =
                    List.fold_left (fun set csys ->
                      try
                        (apply_mgs_from_gathering csys data_shared (mgs,l_vars))::set
                      with Bot -> set
                      ) [] to_check_csys_1
                  in

                  (fun () -> internal checked_list to_check_list acc_f_next)
                ) f_next_1 mgs_list in

              let new_eqsnd = List.fold_left Eq.wedge csys.eqsnd !accumulator_diseq in
              let negative_checked_list = List.rev_map (fun csys -> { csys with eqsnd = new_eqsnd }) checked_csys_1 in
              let negative_to_check_list = List.rev_map (fun csys -> { csys with eqsnd = new_eqsnd }) to_check_csys_1 in

              internal negative_checked_list negative_to_check_list new_f_next
            end
    in

    internal [] csys_set f_next

  (**** The rule Sat for disequation ****)

  let rec exploration_sat_disequation prev_set = function
    | [] -> None, prev_set
    | csys::q when Eq.is_top csys.eqfst -> exploration_sat_disequation (csys::prev_set) q
    | csys::q ->
        let diseq, eqfst = Eq.extract csys.eqfst in
        let new_csys = { csys with eqfst = eqfst } in
        begin match simple_of_disequation new_csys diseq with
          | None -> exploration_sat_disequation prev_set (new_csys::q)
          | Some simple_csys ->
              let mgs_list = mgs simple_csys in

              if mgs_list = []
              then exploration_sat_disequation prev_set (new_csys::q)
              else Some(new_csys, mgs_list, q), prev_set
        end

  (* Uniformity check should have been applied beforehand *)
  let sat_disequation (f_continuation: 'a Set.t -> (unit -> unit) -> unit) (csys_set:'a Set.t) (f_next: unit -> unit) =

    let rec internal checked_csys to_check_csys f_next_1 = match exploration_sat_disequation checked_csys to_check_csys with
      | None, checked_csys_1 -> f_continuation checked_csys_1 f_next_1
      | Some(csys,mgs_list,[]), [] ->
          let new_eqsnd = List.fold_left (fun acc (mgs,l_vars) -> Eq.wedge acc (Diseq.of_substitution_recipe mgs l_vars)) csys.eqsnd mgs_list in
          let negative_to_check_csys = [ { csys with eqsnd = new_eqsnd } ] in
          internal [] negative_to_check_csys f_next_1
      | Some(csys,mgs_list,[]), checked_csys_1 ->
          let accumulator_diseq = ref [] in
          let new_f_next =
            List.fold_left (fun acc_f_next (mgs,l_vars) ->
              let diseq = Diseq.of_substitution_recipe mgs l_vars in
              accumulator_diseq := diseq :: !accumulator_diseq;
              let new_eqsnd = Eq.apply Recipe csys.eqsnd mgs in
              let new_i_subst_snd = Subst.compose_restricted_generic csys.i_subst_snd mgs (fun x -> Variable.quantifier_of x = Free) in

              Config.debug (fun () ->
                if Diseq.is_bot diseq
                then Config.internal_error "[constraint_system.ml >> internal_sat_disequations] The disequation should not be the bot.";

                if Eq.is_bot new_eqsnd
                then Config.internal_error "[constraint_system.ml >> internal_sat_disequation] If bot then we should not have had some mgs."
              );

              let data_shared =
                {
                  share_sdf = (Array.make (K.cardinal csys.sdf) dummy_recipe);
                  share_eqsnd = new_eqsnd;
                  share_ded = ref [];
                  share_eq = ref None;
                  share_i_subst_snd = new_i_subst_snd
                }
              in

              let checked_list =
                try
                  let csys' = apply_mgs_and_gather (List.hd checked_csys_1) data_shared (mgs,l_vars) in

                  List.fold_left (fun set csys ->
                    try
                      (apply_mgs_from_gathering csys data_shared (mgs,l_vars))::set
                    with Bot -> set
                  ) [csys'] (List.tl checked_csys_1)
                with Bot ->
                  List.fold_left (fun set csys ->
                    try
                      (apply_mgs_from_gathering csys data_shared (mgs,l_vars))::set
                    with Bot -> set
                  ) [] (List.tl checked_csys_1)
              in

              (fun () -> f_continuation checked_list acc_f_next)
            ) f_next_1 mgs_list
          in

          let new_eqsnd = List.fold_left Eq.wedge csys.eqsnd !accumulator_diseq in
          let negative_checked_list = List.rev_map (fun csys -> { csys with eqsnd = new_eqsnd }) checked_csys_1 in
          internal negative_checked_list [{csys with eqsnd = new_eqsnd}] new_f_next
      | Some(csys,mgs_list,to_check_csys_1), checked_csys_1 ->
          let accumulator_diseq = ref [] in

          let new_f_next =
            List.fold_left (fun acc_f_next (mgs,l_vars) ->
              let diseq = Diseq.of_substitution_recipe mgs l_vars in
              accumulator_diseq := diseq :: !accumulator_diseq;
              let new_eqsnd = Eq.apply Recipe csys.eqsnd mgs in
              let new_i_subst_snd = Subst.compose_restricted_generic csys.i_subst_snd mgs (fun x -> Variable.quantifier_of x = Free) in

              Config.debug (fun () ->
                if Diseq.is_bot diseq
                then Config.internal_error "[constraint_system.ml >> internal_sat_disequations] The disequation should not be the bot.";

                if Eq.is_bot new_eqsnd
                then Config.internal_error "[constraint_system.ml >> internal_sat_disequation] If bot then we should not have had some mgs."
              );

              let data_shared =
                {
                  share_sdf = (Array.make (K.cardinal csys.sdf) dummy_recipe);
                  share_eqsnd = new_eqsnd;
                  share_ded = ref [];
                  share_eq = ref None;
                  share_i_subst_snd = new_i_subst_snd
                }
              in

              let to_check_list =
                try
                  let csys' = apply_mgs_and_gather (List.hd to_check_csys_1) data_shared (mgs,l_vars) in

                  List.fold_left (fun set csys ->
                    try
                      (apply_mgs_from_gathering csys data_shared (mgs,l_vars))::set
                    with Bot -> set
                  ) [csys'] (List.tl to_check_csys_1)
                with Bot ->
                  List.fold_left (fun set csys ->
                    try
                      (apply_mgs_from_gathering csys data_shared (mgs,l_vars))::set
                    with Bot -> set
                  ) [] (List.tl to_check_csys_1)
              in

              let checked_list =
                List.fold_left (fun set csys ->
                  try
                    (apply_mgs_from_gathering csys data_shared (mgs,l_vars))::set
                  with
                    | Bot -> set
                  ) [] checked_csys_1
              in

              (fun () -> internal checked_list to_check_list acc_f_next)
            ) f_next mgs_list
          in

          let new_eqsnd = List.fold_left Eq.wedge csys.eqsnd !accumulator_diseq in
          let negative_checked_list = List.rev_map (fun csys -> { csys with eqsnd = new_eqsnd }) checked_csys_1 in
          let negative_to_check_list = List.rev_map (fun csys -> { csys with eqsnd = new_eqsnd }) (csys::to_check_csys_1) in

          internal negative_checked_list negative_to_check_list new_f_next
    in

    internal [] csys_set f_next

  (**** The rule Sat for private channels ****)

  let rec exploration_sat_private prev_set = function
    | [] -> None, prev_set
    | csys::q when csys.private_channels = [] -> exploration_sat_private (csys::prev_set) q
    | csys::q ->
        let ch = List.hd csys.private_channels in

        let simple_csys = simple_of_private csys ch in

        begin match one_mgs simple_csys with
          | None -> exploration_sat_private prev_set ({ csys with private_channels = List.tl csys.private_channels }::q)
          | Some(mgs,l_vars) ->
              let mgs_csys = Subst.restrict mgs (fun x -> Variable.has_not_infinite_type x) in

              Config.debug (fun () ->
                if List.exists Variable.has_infinite_type l_vars
                then Config.internal_error "[constraint_system.ml >> exploration_sat_private] Unexpected case."
              );

              Some (csys,(mgs_csys, l_vars),q), prev_set
        end

  (* Uniformity check should have been applied beforehand *)
  let sat_private (f_continuation: 'a Set.t -> (unit -> unit) -> unit) (csys_set:'a Set.t) (f_next: unit -> unit) =

    let rec internal checked_csys to_check_csys f_next_1 = match exploration_sat_private checked_csys to_check_csys with
      | None, checked_csys_1 -> f_continuation checked_csys_1 f_next_1
      | Some(csys,(mgs,l_vars),[]),[] ->
          let new_eqsnd = Eq.wedge csys.eqsnd (Diseq.of_substitution_recipe mgs l_vars) in
          let negative_to_check_csys = [ { csys with eqsnd = new_eqsnd } ] in
          internal [] negative_to_check_csys f_next_1
      | Some(csys,(mgs,l_vars),[]), checked_csys_1 ->
          let diseq = Diseq.of_substitution_recipe mgs l_vars in

          let new_eqsnd = Eq.apply Recipe csys.eqsnd mgs in
          let new_i_subst_snd = Subst.compose_restricted_generic csys.i_subst_snd mgs (fun x -> Variable.quantifier_of x = Free) in

          Config.debug (fun () ->
            if Diseq.is_bot diseq
            then Config.internal_error "[constraint_system.ml >> internal_sat_private] The disequation should not be the bot.";

            if Eq.is_bot new_eqsnd
            then Config.internal_error "[constraint_system.ml >> internal_sat_disequation] If bot then we should not have had some mgs."
          );

          let data_shared =
            {
              share_sdf = (Array.make (K.cardinal csys.sdf) dummy_recipe);
              share_eqsnd = new_eqsnd;
              share_ded = ref [];
              share_eq = ref None;
              share_i_subst_snd = new_i_subst_snd
            }
          in

          let positive_checked_list =
            try
              let csys' = apply_mgs_and_gather (List.hd checked_csys_1) data_shared (mgs,l_vars) in

              List.fold_left (fun set csys ->
                try
                  (apply_mgs_from_gathering csys data_shared (mgs,l_vars))::set
                with Bot -> set
              ) [csys'] (List.tl checked_csys_1)
            with Bot ->
              List.fold_left (fun set csys ->
                try
                  (apply_mgs_from_gathering csys data_shared (mgs,l_vars))::set
                with Bot -> set
              ) [] (List.tl checked_csys_1)
          in

          let new_eqsnd = Eq.wedge csys.eqsnd diseq in
          let negative_checked_list = List.rev_map (fun csys -> { csys with eqsnd = new_eqsnd }) checked_csys_1 in

          f_continuation positive_checked_list (fun () -> internal negative_checked_list [{csys with eqsnd = new_eqsnd}] f_next_1)
      | Some(csys,(mgs,l_vars),to_check_csys_1), checked_csys_1 ->
          let diseq = Diseq.of_substitution_recipe mgs l_vars in

          let new_eqsnd = Eq.apply Recipe csys.eqsnd mgs in
          let new_i_subst_snd = Subst.compose_restricted_generic csys.i_subst_snd mgs (fun x -> Variable.quantifier_of x = Free) in

          Config.debug (fun () ->
            if Diseq.is_bot diseq
            then Config.internal_error "[constraint_system.ml >> internal_sat_private] The disequation should not be the bot.";

            if Eq.is_bot new_eqsnd
            then Config.internal_error "[constraint_system.ml >> internal_sat_private] If bot then we should not have had some mgs."
          );

          let data_shared =
            {
              share_sdf = (Array.make (K.cardinal csys.sdf) dummy_recipe);
              share_eqsnd = new_eqsnd;
              share_ded = ref [];
              share_eq = ref None;
              share_i_subst_snd = new_i_subst_snd
            }
          in

          let to_check_list =
            try
              let csys' = apply_mgs_and_gather (List.hd to_check_csys_1) data_shared (mgs,l_vars) in

              List.fold_left (fun set csys ->
                try
                  (apply_mgs_from_gathering csys data_shared (mgs,l_vars))::set
                with Bot -> set
              ) [csys'] (List.tl to_check_csys_1)
            with Bot ->
              List.fold_left (fun set csys ->
                try
                  (apply_mgs_from_gathering csys data_shared (mgs,l_vars))::set
                with Bot -> set
              ) [] (List.tl to_check_csys_1)
          in


          let checked_list =
            List.fold_left (fun set csys ->
              try
                (apply_mgs_from_gathering csys data_shared (mgs,l_vars))::set
              with
                | Bot -> set
              ) [] checked_csys_1
          in

          let new_eqsnd = Eq.wedge csys.eqsnd diseq in
          let negative_checked_list = List.rev_map (fun csys -> { csys with eqsnd = new_eqsnd }) checked_csys_1 in
          let negative_to_check_list = List.rev_map (fun csys -> { csys with eqsnd = new_eqsnd }) (csys::to_check_csys_1) in

          internal checked_list to_check_list (fun () -> internal negative_checked_list negative_to_check_list f_next_1)
    in

    internal [] csys_set f_next

  (**** The rule Sat for equality formula ****)

  let rec exploration_sat_equality_formula prev_set = function
    | [] -> None, prev_set
    | csys::q ->
        match UF.pop_equality_formula_option csys.uf with
          | None -> exploration_sat_equality_formula (csys::prev_set) q
          | Some form ->
              match simple_of_formula csys form with
                | None ->
                    let csys' = { csys with uf = UF.remove_one_unsolved_equality_formula csys.uf } in
                    exploration_sat_equality_formula (csys'::prev_set) q
                | Some simple_csys ->
                    match one_mgs simple_csys with
                      | None ->
                          let csys' = { csys with uf = UF.remove_one_unsolved_equality_formula csys.uf } in
                          exploration_sat_equality_formula (csys'::prev_set) q
                      | Some mgs -> Some(csys,mgs,q),prev_set

  (* Uniformity check should have been applied beforehand *)
  let internal_sat_equality_formula (checked_csys:'a Set.t) (to_check_csys:'a Set.t) (f_continuation: 'a Set.t -> (unit -> unit) -> unit) (f_next: unit -> unit) =

    let rec internal checked_csys to_check_csys f_next_1 = match exploration_sat_equality_formula checked_csys to_check_csys with
      | None, checked_csys_1 -> f_continuation checked_csys_1 f_next_1
      | Some(csys,(mgs,l_vars),to_check_csys_1), checked_csys_1 ->
          let diseq = Diseq.of_substitution_recipe mgs l_vars in
          let new_eqsnd = Eq.apply Recipe csys.eqsnd mgs in
          let new_i_subst_snd = Subst.compose_restricted_generic csys.i_subst_snd mgs (fun x -> Variable.quantifier_of x = Free) in

          Config.debug (fun () ->
            if Diseq.is_bot diseq
            then
              begin
                Printf.printf "The mgs = %s" (Subst.display Latex Recipe mgs);
                Config.internal_error "[constraint_system.ml >> rule_sat_formula] The disequation should not be the bot.";
              end;

            if Subst.is_identity mgs
            then Config.internal_error "[constraint_system.ml >> internal_sat_formula] It should not be the identity mgs (otherwise the formula would have been solved)."
          );

          let data_shared =
            {
              share_sdf = (Array.make (K.cardinal csys.sdf) dummy_recipe);
              share_eqsnd = new_eqsnd;
              share_ded = ref [];
              share_eq = ref None;
              share_i_subst_snd = new_i_subst_snd
            }
          in

          let positive_checked_list =
            let csys' = apply_mgs_and_gather csys data_shared (mgs,l_vars) in
            List.fold_left (fun set csys ->
              try
                (apply_mgs_from_gathering csys data_shared (mgs,l_vars))::set
              with Bot -> set
            ) [csys'] checked_csys_1
          in

          let positive_to_check_list =
            List.fold_left (fun set csys ->
              try
                (apply_mgs_from_gathering csys data_shared (mgs,l_vars))::set
              with Bot -> set
            ) [] to_check_csys_1
          in

          let new_eqsnd = Eq.wedge csys.eqsnd diseq in
          let negative_checked_list = List.rev_map (fun csys -> { csys with eqsnd = new_eqsnd }) checked_csys_1 in
          let negative_to_check_list = List.rev_map (fun csys -> { csys with eqsnd = new_eqsnd }) (csys::to_check_csys_1) in

          internal positive_checked_list positive_to_check_list (fun () -> internal negative_checked_list negative_to_check_list f_next_1)
    in

    internal checked_csys to_check_csys f_next

  let sat_equality_formula (f_continuation: 'a Set.t -> (unit -> unit) -> unit) (csys_set:'a Set.t) (f_next: unit -> unit) =
    internal_sat_equality_formula [] csys_set f_continuation f_next

  (**** The rule Sat for deduction formula ****)

  let rec exploration_sat_deduction_formula prev_set = function
    | [] -> None, prev_set
    | csys::q ->
        match UF.pop_deduction_formula_option csys.uf with
          | None -> exploration_sat_deduction_formula (csys::prev_set) q
          | Some form ->
              match simple_of_formula csys form with
                | None ->
                    let csys' = { csys with uf = UF.remove_one_unsolved_deduction_formula csys.uf } in
                    exploration_sat_deduction_formula (csys'::prev_set) q
                | Some simple_csys ->
                    match one_mgs simple_csys with
                      | None ->
                          let csys' = { csys with uf = UF.remove_one_unsolved_deduction_formula csys.uf } in
                          exploration_sat_deduction_formula (csys'::prev_set) q
                      | Some mgs -> Some(csys,mgs,q),prev_set

  (* Uniformity check should have been applied beforehand *)
  let internal_sat_deduction_formula (checked_csys:'a Set.t) (to_check_csys:'a Set.t) (f_continuation: 'a Set.t -> (unit -> unit) -> unit) (f_next: unit -> unit) =

    let rec internal checked_csys to_check_csys f_next_1 = match exploration_sat_deduction_formula checked_csys to_check_csys with
      | None, checked_csys_1 -> f_continuation checked_csys_1 f_next_1
      | Some(csys,(mgs,l_vars),to_check_csys_1), checked_csys_1 ->
          let diseq = Diseq.of_substitution_recipe mgs l_vars in
          let new_eqsnd = Eq.apply Recipe csys.eqsnd mgs in
          let new_i_subst_snd = Subst.compose_restricted_generic csys.i_subst_snd mgs (fun x -> Variable.quantifier_of x = Free) in

          Config.debug (fun () ->
            if Diseq.is_bot diseq
            then Config.internal_error "[constraint_system.ml >> rule_sat_deduction_formula] The disequation should not be the bot.";

            if Subst.is_identity mgs
            then Config.internal_error "[constraint_system.ml >> internal_sat_deduction_formula] It should not be the identity mgs (otherwise the formula would have been solved)."
          );

          let data_shared =
            {
              share_sdf = (Array.make (K.cardinal csys.sdf) dummy_recipe);
              share_eqsnd = new_eqsnd;
              share_ded = ref [];
              share_eq = ref None;
              share_i_subst_snd = new_i_subst_snd
            }
          in

          let positive_checked_list =
            let csys' = apply_mgs_and_gather csys data_shared (mgs,l_vars) in
            List.fold_left (fun set csys ->
              try
                (apply_mgs_from_gathering csys data_shared (mgs,l_vars))::set
              with Bot -> set
            ) [csys'] checked_csys_1
          in

          let positive_to_check_list =
            List.fold_left (fun set csys ->
              try
                (apply_mgs_from_gathering csys data_shared (mgs,l_vars))::set
              with Bot -> set
            ) [] to_check_csys_1
          in

          let new_eqsnd = Eq.wedge csys.eqsnd diseq in
          let negative_checked_list = List.rev_map (fun csys -> { csys with eqsnd = new_eqsnd }) checked_csys_1 in
          let negative_to_check_list = List.rev_map (fun csys -> { csys with eqsnd = new_eqsnd }) (csys::to_check_csys_1) in

          internal positive_checked_list positive_to_check_list (fun () -> internal negative_checked_list negative_to_check_list f_next_1)
    in

    internal checked_csys to_check_csys f_next

  let sat_deduction_formula (f_continuation: 'a Set.t -> (unit -> unit) -> unit) (csys_set:'a Set.t) (f_next: unit -> unit) =
    internal_sat_deduction_formula [] csys_set f_continuation f_next

  (**** The normalisation rule for splitting equality formula / facts ****)

  (* This should not be applied when there are unsolved equality formula *)
  let normalisation_split_equality (f_continuation_pos: 'a Set.t -> (unit -> unit) -> unit) (f_continuation_neg: 'a Set.t -> (unit -> unit) -> unit) (csys_set:'a Set.t) (f_next: unit -> unit) =

    let rec exploration_normalisation_split_equality neg_prev_set pos_prev_set = function
      | [] ->
          begin match neg_prev_set,pos_prev_set with
            | [], [] -> f_next ()
            | [], _ -> f_continuation_pos pos_prev_set f_next
            | _, [] -> f_continuation_neg neg_prev_set f_next
            | _,_ -> f_continuation_pos pos_prev_set (fun () -> f_continuation_neg neg_prev_set f_next)
          end
      | csys::q when UF.exists_equality_fact csys.uf -> exploration_normalisation_split_equality neg_prev_set (csys::pos_prev_set) q
      | csys::q -> exploration_normalisation_split_equality (csys::neg_prev_set) pos_prev_set q
    in

    exploration_normalisation_split_equality [] [] csys_set

  (**** The normalisation rule for splitting deduction formula / facts ****)

  let rec search_and_add_pattern (csys:'a t) pat = function
    | [] -> [pat,[csys]]
    | (pat',csys_list)::q when is_equal_pattern pat pat' -> (pat',csys::csys_list)::q
    | t::q -> t::(search_and_add_pattern csys pat q)

  (* The fonctions f_apply_pos and f_apply_neg should not raise the exception Bot. Moreover, this should not be applied when there are unsolved deduction formula. Finally there should be at most one deduction fact per constraint system.  *)
  let normalisation_split_deduction (f_continuation_pos: 'a Set.t -> (unit -> unit) -> unit) (f_continuation_neg: 'a Set.t -> (unit -> unit) -> unit) (csys_set:'a Set.t) (f_next: unit -> unit) =

    let rec exploration_normalisation_split_deduction nothing_prev_set no_pattern_prev_set pattern_prev_list = function
      | [] ->
          let apply_nothing_set =
            if nothing_prev_set = []
            then f_next
            else (fun () -> f_continuation_neg nothing_prev_set f_next)
          in

          let apply_no_pattern_set =
            if no_pattern_prev_set = []
            then apply_nothing_set
            else (fun () -> f_continuation_pos no_pattern_prev_set apply_nothing_set)
          in

          let apply_pattern_set =
            if pattern_prev_list = []
            then apply_no_pattern_set
            else
              List.fold_left (fun acc (_,csys_list) ->
                (fun () -> f_continuation_pos csys_list acc)
              ) apply_no_pattern_set pattern_prev_list
          in

          apply_pattern_set ()
      | csys::q ->
          match UF.pop_deduction_fact_option csys.uf with
            | None -> exploration_normalisation_split_deduction (csys::nothing_prev_set) no_pattern_prev_set pattern_prev_list q
            | Some fact ->
                let csys' = add_mixed_diseq_skeleton csys in
                match extract_pattern_of_deduction_fact fact with
                  | None -> exploration_normalisation_split_deduction nothing_prev_set (csys'::no_pattern_prev_set) pattern_prev_list q
                  | Some(pat,fact_list) ->
                      let csys'' = { csys' with uf = UF.replace_deduction_facts csys'.uf fact_list } in
                      let pattern_prev_list' = search_and_add_pattern csys'' pat pattern_prev_list in
                      exploration_normalisation_split_deduction nothing_prev_set no_pattern_prev_set pattern_prev_list' q
    in

    exploration_normalisation_split_deduction [] [] [] csys_set

  let normalisation_split_deduction_axiom (f_continuation: 'a Set.t -> (unit -> unit) -> unit) (csys_set:'a Set.t) (f_next: unit -> unit) =

    let rec exploration_normalisation_split_deduction no_pattern_prev_set pattern_prev_list = function
      | [] ->
          let apply_no_pattern_set =
            if no_pattern_prev_set = []
            then f_next
            else (fun () -> f_continuation no_pattern_prev_set f_next)
          in

          let apply_pattern_set =
            if pattern_prev_list = []
            then apply_no_pattern_set
            else
              List.fold_left (fun acc (_,csys_list) ->
                (fun () -> f_continuation csys_list acc)
              ) apply_no_pattern_set pattern_prev_list
          in

          apply_pattern_set ()
      | csys::q ->
          let fact = UF.pop_deduction_fact csys.uf in
          match extract_pattern_of_deduction_fact fact with
            | None -> exploration_normalisation_split_deduction (csys::no_pattern_prev_set) pattern_prev_list q
            | Some(pat,fact_list) ->
                let csys' = { csys with uf = UF.replace_deduction_facts csys.uf fact_list } in
                let pattern_prev_list' = search_and_add_pattern csys' pat pattern_prev_list in
                exploration_normalisation_split_deduction no_pattern_prev_set pattern_prev_list' q
    in

    exploration_normalisation_split_deduction [] [] csys_set

  (**** The rule Equality between two elements of SDF ****)

  type id_type =
    | IdIk of int
    | IdSDF of int

  let rec exploration_equality_SDF (prev_set:'a Set.t) = function
    | [] -> None, prev_set
    | csys::q ->
        if csys.equality_to_checked = [] && csys.equality_to_checked_IK = []
        then exploration_equality_SDF (csys::prev_set) q
        else
          let (last_id,last_fact) = IK.last_entry_with_id csys.ik in
          let last_term = Fact.get_protocol_term last_fact in
          let last_recipe = Fact.get_recipe last_fact in

          let rec sub_explore_IK = function
            | [] -> exploration_equality_SDF ({ csys with equality_to_checked_IK = []; equality_to_checked = [] } :: prev_set) q
            | (id_ik::q_id) as all_id ->
                let fact = IK.get csys.ik id_ik in
                let term = Fact.get_protocol_term fact in
                let head = Fact.create_equality_fact (Fact.get_recipe fact) last_recipe in

                let form_op =
                  try
                    Some (Fact.create Fact.Equality head [term,last_term])
                  with Fact.Bot -> None
                in

                match form_op with
                  | None -> sub_explore_IK q_id
                  | Some form ->
                      if Fact.is_fact form
                      then Some(Subst.identity,[],IdIk id_ik,last_id,{ csys with equality_to_checked_IK = all_id; equality_to_checked = [] }::q), prev_set
                      else
                        match simple_of_formula csys form with
                          | None -> sub_explore_IK q_id
                          | Some simple_csys ->
                              match one_mgs simple_csys with
                                | None -> sub_explore_IK q_id
                                | Some(mgs,l_vars) -> Some(mgs,l_vars,IdIk id_ik,last_id,{ csys with equality_to_checked_IK = all_id; equality_to_checked = [] }::q), prev_set
          in

          let rec sub_explore = function
            | [] -> sub_explore_IK csys.equality_to_checked_IK
            | (id_sdf::q_id) as all_id ->
                let fact = K.get csys.sdf id_sdf in
                let term = Fact.get_protocol_term fact in
                let head = Fact.create_equality_fact (Fact.get_recipe fact) last_recipe in

                let form_op =
                  try
                    Some (Fact.create Fact.Equality head [term,last_term])
                  with Fact.Bot -> None
                in

                match form_op with
                  | None -> sub_explore q_id
                  | Some form ->
                      if Fact.is_fact form
                      then Some(Subst.identity,[],IdSDF id_sdf,last_id,{ csys with equality_to_checked = all_id }::q), prev_set
                      else
                        match simple_of_formula csys form with
                          | None -> sub_explore q_id
                          | Some simple_csys ->
                              match one_mgs simple_csys with
                                | None -> sub_explore q_id
                                | Some(mgs,l_vars) -> Some(mgs,l_vars,IdSDF id_sdf,last_id,{ csys with equality_to_checked = all_id }::q), prev_set
          in

          sub_explore csys.equality_to_checked

  (* This rule should be applied when an element was just added to the K. Hypotheses : Only deduction facts in UF. No equality facts/formulas. *)
  let equality_SDF (f_continuation: 'a Set.t -> (unit -> unit) -> unit) (csys_set:'a Set.t) (f_next:unit -> unit) =

    let rec internal checked_csys to_check_csys f_next_1 = match exploration_equality_SDF checked_csys to_check_csys with
      | None, checked_csys_1 -> f_continuation checked_csys_1 f_next_1
      | Some(mgs,l_vars,id_type,last_id,to_check_csys_1), checked_csys_1 ->
          if Subst.is_identity mgs
          then
            begin
              Config.debug (fun () ->
                if l_vars <> []
                then Config.internal_error "[Constraint_system.ml >> internal_equality] An identity substitution should imply an empty list of created variables"
              );
              let exists_unsolved = ref false in
              let all_exists = ref true in

              let positive_checked_csys_list =
                List.fold_left (fun set csys ->
                  try
                    let last_fact = IK.last_entry csys.ik in
                    let fact = match id_type with
                      | IdIk id -> IK.get csys.ik id
                      | IdSDF id -> K.get csys.sdf id
                    in

                    let term = Fact.get_protocol_term fact in
                    let last_term = Fact.get_protocol_term last_fact in

                    let head = Fact.create_equality_fact (Fact.get_recipe fact) (Fact.get_recipe last_fact) in
                    let form = Fact.create Fact.Equality head [term,last_term] in

                    if Fact.is_fact form
                    then { csys with uf = UF.add_equality_fact csys.uf head }::set
                    else
                      begin
                        exists_unsolved := true;
                        { csys with uf = UF.add_equality_formula csys.uf form }::set
                      end
                  with Fact.Bot ->
                    all_exists := false;
                    csys::set
                ) [] checked_csys_1
              in
              let positive_all_csys_list =
                List.fold_left (fun set csys ->
                  try
                    let last_fact = IK.last_entry csys.ik in
                    let fact = match id_type with
                      | IdIk id -> IK.get csys.ik id
                      | IdSDF id -> K.get csys.sdf id
                    in

                    let term = Fact.get_protocol_term fact in
                    let last_term = Fact.get_protocol_term last_fact in

                    let head = Fact.create_equality_fact (Fact.get_recipe fact) (Fact.get_recipe last_fact) in
                    let form = Fact.create Fact.Equality head [(term,last_term)] in

                    if Fact.is_fact form
                    then { csys with uf = UF.add_equality_fact csys.uf head }::set
                    else
                      begin
                        exists_unsolved := true;
                        { csys with uf = UF.add_equality_formula csys.uf form }::set
                      end
                  with Fact.Bot ->
                    all_exists := false;
                    csys::set
                ) positive_checked_csys_list to_check_csys_1
              in

              let final_apply csys_set f_next =
                let csys_set_1 =
                  List.rev_map (fun csys ->
                    { csys with
                      equality_to_checked = [];
                      equality_to_checked_IK = [];
                      skeletons_checked_IK = List.filter (fun (id,_) -> id <> last_id) csys.skeletons_checked_IK;
                      skeletons_to_check_IK = List.filter (fun (id,_) -> id <> last_id) csys.skeletons_to_check_IK;
                      ik = IK.remove_last csys.ik;
                      uf = UF.remove_equality_fact csys.uf
                    }
                  ) csys_set
                in
                internal [] csys_set_1 f_next
              in

              if !exists_unsolved
              then sat_equality_formula (normalisation_split_equality final_apply (internal [])) positive_all_csys_list f_next_1
              else
                if !all_exists
                then final_apply positive_all_csys_list f_next_1
                else normalisation_split_equality final_apply (internal []) positive_all_csys_list f_next_1
            end
          else
            begin
              let one_csys = List.hd to_check_csys_1 in
              let new_eqsnd = Eq.apply Recipe one_csys.eqsnd mgs in
              let new_i_subst_snd = Subst.compose_restricted_generic one_csys.i_subst_snd mgs (fun x -> Variable.quantifier_of x = Free) in
              let data_shared =
                {
                  share_sdf = (Array.make (K.cardinal one_csys.sdf) dummy_recipe);
                  share_eqsnd = new_eqsnd;
                  share_ded = ref [];
                  share_eq = ref None;
                  share_i_subst_snd = new_i_subst_snd
                }
              in

              (* The formula creasted in the constraint system one_csys'' should always be a fact since it is from that constraint system
                that the most general solution was computed. *)
              let one_csys' = apply_mgs_and_gather one_csys data_shared (mgs,l_vars) in
              let last_fact = IK.last_entry one_csys'.ik in
              let fact = match id_type with
                | IdIk id -> IK.get one_csys'.ik id
                | IdSDF id -> K.get one_csys'.sdf id
              in
              let head = Fact.create_equality_fact (Fact.get_recipe fact) (Fact.get_recipe last_fact) in
              let one_csys'' = { one_csys' with uf = UF.add_equality_fact one_csys'.uf head } in

              let exists_unsolved = ref false in
              let all_exists = ref true in

              let positive_to_check_csys_list =
                List.fold_left (fun set csys ->
                  try
                    let csys_1 = apply_mgs_from_gathering csys data_shared (mgs,l_vars) in

                    begin try
                      let last_fact = IK.last_entry csys_1.ik in
                      let fact = match id_type with
                        | IdIk id -> IK.get csys_1.ik id
                        | IdSDF id -> K.get csys_1.sdf id
                      in

                      let term = Fact.get_protocol_term fact in
                      let last_term = Fact.get_protocol_term last_fact in

                      let form = Fact.create Fact.Equality head [(term,last_term)] in

                      if Fact.is_fact form
                      then { csys_1 with uf = UF.add_equality_fact csys_1.uf head }::set
                      else
                        begin
                          exists_unsolved := true;
                          { csys_1 with uf = UF.add_equality_formula csys_1.uf form }::set
                        end
                    with Fact.Bot ->
                      all_exists := false;
                      csys_1::set
                    end
                  with Bot -> set
                ) [one_csys''] (List.tl to_check_csys_1)
              in
              let positive_all_csys_list =
                List.fold_left (fun set csys ->
                  try
                    let csys_1 = apply_mgs_from_gathering csys data_shared (mgs,l_vars) in

                    begin try
                      let last_fact = IK.last_entry csys_1.ik in
                      let fact = match id_type with
                        | IdIk id -> IK.get csys_1.ik id
                        | IdSDF id -> K.get csys_1.sdf id
                      in

                      let term = Fact.get_protocol_term fact in
                      let last_term = Fact.get_protocol_term last_fact in

                      let form = Fact.create Fact.Equality head [(term,last_term)] in

                      if Fact.is_fact form
                      then { csys_1 with uf = UF.add_equality_fact csys_1.uf head }::set
                      else
                        begin
                          exists_unsolved := true;
                          { csys_1 with uf = UF.add_equality_formula csys_1.uf form }::set
                        end
                    with Fact.Bot ->
                      all_exists := false;
                      csys_1::set
                    end
                  with Bot -> set
                ) positive_to_check_csys_list (List.tl to_check_csys_1)
              in

              let diseq = Diseq.of_substitution_recipe mgs l_vars in
              let new_eqsnd = Eq.wedge one_csys.eqsnd diseq in

              let negative_checked_list = List.rev_map (fun csys -> { csys with eqsnd = new_eqsnd }) checked_csys_1 in
              let negative_to_check_list = List.rev_map (fun csys -> { csys with eqsnd = new_eqsnd }) to_check_csys_1 in

              let final_apply csys_set f_next =
                let csys_set_1 =
                  List.rev_map (fun csys ->
                    { csys with
                      equality_to_checked = [];
                      equality_to_checked_IK = [];
                      skeletons_checked_IK = List.filter (fun (id,_) -> id <> last_id) csys.skeletons_checked_IK;
                      skeletons_to_check_IK = List.filter (fun (id,_) -> id <> last_id) csys.skeletons_to_check_IK;
                      ik = IK.remove_last csys.ik;
                      uf = UF.remove_equality_fact csys.uf
                    }
                  ) csys_set
                in
                internal [] csys_set_1 f_next
              in

              let next_negative_function () = internal negative_checked_list negative_to_check_list f_next_1 in

              if !exists_unsolved
              then sat_equality_formula (normalisation_split_equality final_apply (internal [])) positive_all_csys_list next_negative_function
              else
                if !all_exists
                then final_apply positive_all_csys_list next_negative_function
                else normalisation_split_equality final_apply (internal []) positive_all_csys_list next_negative_function
            end
    in

    internal [] csys_set f_next

  (**** The normalisation rule that will look for deduction fact that are consequence ****)

  let rec exploration_normalisation_deduction_consequence = function
    | [] -> None
    | csys::q ->
        let ded_fact = UF.pop_deduction_fact csys.uf in
        let term = Fact.get_protocol_term ded_fact in
        match Tools.consequence_protocol csys.sdf csys.ik csys.df term with
          | None -> exploration_normalisation_deduction_consequence q
          | Some recipe -> Some recipe

  (* This rule should not be applied when there are equality fact or formulas. Moreover, there should only be deduction facts and the same amount in each constraint systems. *)
  let rec normalisation_deduction_consequence (f_continuation: 'a Set.t -> (unit -> unit) -> unit) (csys_set:'a Set.t) (f_next:unit -> unit) =
    if csys_set = []
    then f_next ()
    else
      let csys = List.hd csys_set in
      if UF.exists_deduction_fact csys.uf
      then
        match exploration_normalisation_deduction_consequence csys_set with
          | None ->
              (* We add in SDF *)
              let id_prev_last = IK.last_entry_id csys.ik in
              let id_last = id_prev_last + 1 in
              let new_skeletons = List.rev_map (fun id_skel -> (id_last,id_skel)) (Rewrite_rules.get_all_skeleton_indices ()) in

              let new_csys_list =
                List.rev_map (fun csys ->
                  (* Update of the lists equality_constructor_checked and equality_constructor_to_checked *)

                  let ded_fact = UF.pop_deduction_fact csys.uf in

                  Config.debug (fun () ->
                    if csys.equality_to_checked <> []
                    then Config.internal_error "[Constraint_system.ml >> normalisation_deduction_consequence] All pair of deduction fact from sdf should have been checked for equalities at that point.";
                  );

                  let new_ik = IK.add csys.ik ded_fact in

                  { csys with
                    skeletons_checked = [];
                    skeletons_to_check = (List.rev_append csys.skeletons_to_check csys.skeletons_checked);
                    skeletons_checked_IK = [];
                    skeletons_to_check_IK = (List.rev_append new_skeletons (List.rev_append csys.skeletons_to_check_IK csys.skeletons_checked_IK));
                    equality_to_checked = K.all_id csys.sdf;
                    equality_to_checked_IK = IK.all_id csys.ik;
                    ik = new_ik;
                    uf = UF.remove_one_deduction_fact csys.uf
                  }
                ) csys_set
              in

              equality_SDF (normalisation_deduction_consequence f_continuation) new_csys_list f_next
          | Some recipe_conseq ->
              (* We add an equality formula *)

              let exists_unsolved = ref false in
              let all_exists = ref true in

              let first_ded_fact = UF.pop_deduction_fact csys.uf in
              let head_eq = Fact.create_equality_fact (Fact.get_recipe first_ded_fact) recipe_conseq in

              let new_csys_list =
                List.fold_left (fun acc csys ->
                  let ded_fact = UF.pop_deduction_fact csys.uf in
                  let term_conseq = Tools.consequence_recipe_with_IK csys.sdf csys.ik csys.df recipe_conseq in
                  let term = Fact.get_protocol_term ded_fact in

                  begin try
                    let eq_form = Fact.create Fact.Equality head_eq [term,term_conseq] in

                    if Fact.is_fact eq_form
                    then { csys with uf = UF.add_equality_fact csys.uf head_eq } :: acc
                    else
                      begin
                        exists_unsolved := true;
                        { csys with uf = UF.add_equality_formula csys.uf eq_form } :: acc
                      end
                  with Fact.Bot ->
                    all_exists := false;
                    csys :: acc
                  end
                ) [] csys_set
              in

              let final_apply csys_set f_next =
                let csys_set_1 =
                  List.rev_map (fun csys ->
                    let uf_1 = UF.remove_equality_fact csys.uf in
                    { csys with uf = UF.remove_one_deduction_fact uf_1 }
                  ) csys_set
                in
                normalisation_deduction_consequence f_continuation csys_set_1 f_next
              in

              if !exists_unsolved
              then sat_equality_formula (normalisation_split_equality final_apply (normalisation_deduction_consequence f_continuation)) new_csys_list f_next
              else
                if !all_exists
                then final_apply new_csys_list f_next
                else normalisation_split_equality final_apply (normalisation_deduction_consequence f_continuation) new_csys_list f_next
      else f_continuation csys_set f_next

  (**** The rule Rewrite ****)

  exception Found_deduction_fact of Fact.deduction

  type deduction_formula_generated =
    | NoFormula
    | FoundFact of Fact.deduction
    | Unsolved of Fact.deduction_formula list

  let create_generic_skeleton_formula csys id_skel recipe =
    let lhs_recipe = get_args recipe in
    let lhs_terms = List.map (Tools.consequence_recipe_with_IK csys.sdf csys.ik csys.df) lhs_recipe in

    try
      let unsolved_deduction =
        List.fold_left (fun acc (lhs,r) ->
          let fact = Fact.create_deduction_fact recipe r in

          try
            let form = Fact.create Fact.Deduction fact (List.combine lhs lhs_terms) in

            if Fact.is_fact form
            then raise (Found_deduction_fact (Fact.get_head form));

            form::acc
          with Fact.Bot -> acc
        ) [] (Rewrite_rules.get_compatible_rewrite_rules id_skel)
      in
      if unsolved_deduction = []
      then NoFormula
      else Unsolved unsolved_deduction
    with Found_deduction_fact fact -> FoundFact fact

  let rec exploration_rewrite prev_set = function
    | [] -> None, prev_set
    | csys::q ->
        if csys.skeletons_to_check = [] && csys.skeletons_to_check_IK = []
        then exploration_rewrite (csys::prev_set) q
        else
          let rec sub_explore_IK skeletons_checked skeletons_checked_IK = function
            | [] ->
                let csys' =
                  { csys with
                    skeletons_to_check = [];
                    skeletons_to_check_IK = [];
                    skeletons_checked = skeletons_checked;
                    skeletons_checked_IK = skeletons_checked_IK
                  }
                in
                exploration_rewrite (csys'::prev_set) q
            | ((id_ik,id_skel)::q_id_skel) as all_skel ->
                match simple_of_skeleton_IK csys id_ik id_skel with
                  | None -> sub_explore_IK skeletons_checked skeletons_checked_IK q_id_skel
                  | Some (recipe,simple_csys) ->
                      match one_mgs simple_csys with
                        | None -> sub_explore_IK skeletons_checked ((id_ik,id_skel)::skeletons_checked_IK) q_id_skel
                        | Some (mgs,l_vars) ->
                            let mgs_form, mgs_csys  = Subst.split_domain mgs Variable.has_infinite_type in
                            let l_vars_form, l_vars_csys = List.partition_unordered Variable.has_infinite_type l_vars in

                            let snd_vars = (Rewrite_rules.get_skeleton id_skel).Rewrite_rules.snd_vars in
                            let not_instantied_vars = Subst.not_in_domain mgs_form snd_vars in

                            let (nb_vars,eq_name_1) = List.fold_left (fun (i,acc) x -> (i+1,(x, apply_function (Symbol.get_fresh_constant i) [])::acc)) (0,[]) not_instantied_vars in
                            let (_,eq_name_2) = List.fold_left (fun (i,acc) x -> (i+1,(x, apply_function (Symbol.get_fresh_constant i) [])::acc)) (nb_vars,eq_name_1) l_vars_form in
                            let subst_name = Subst.create_multiple Recipe eq_name_2 in

                            let new_mgs_form = Subst.compose mgs_form subst_name in
                            let new_recipe = Subst.apply new_mgs_form recipe (fun r f -> f r) in

                            let csys' =
                              { csys with
                                skeletons_to_check = [];
                                skeletons_to_check_IK = all_skel;
                                skeletons_checked = skeletons_checked;
                                skeletons_checked_IK = skeletons_checked_IK;
                              }
                            in
                            Some(id_skel,(mgs_csys,l_vars_csys),new_recipe,csys',q), prev_set
          in

          let rec sub_explore skeletons_checked = function
            | [] -> sub_explore_IK skeletons_checked csys.skeletons_checked_IK csys.skeletons_to_check_IK
            | ((id_sdf,id_skel)::q_id_skel) as all_skel ->
                match simple_of_skeleton csys id_sdf id_skel with
                  | None -> sub_explore skeletons_checked q_id_skel
                  | Some (recipe,simple_csys) ->
                      match one_mgs simple_csys with
                        | None -> sub_explore ((id_sdf,id_skel)::skeletons_checked) q_id_skel
                        | Some (mgs,l_vars) ->
                            let mgs_form, mgs_csys  = Subst.split_domain mgs Variable.has_infinite_type in
                            let l_vars_form, l_vars_csys = List.partition_unordered Variable.has_infinite_type l_vars in

                            let snd_vars = (Rewrite_rules.get_skeleton id_skel).Rewrite_rules.snd_vars in
                            let not_instantied_vars = Subst.not_in_domain mgs_form snd_vars in

                            let (nb_vars,eq_name_1) = List.fold_left (fun (i,acc) x -> (i+1,(x, apply_function (Symbol.get_fresh_constant i) [])::acc)) (0,[]) not_instantied_vars in
                            let (_,eq_name_2) = List.fold_left (fun (i,acc) x -> (i+1,(x, apply_function (Symbol.get_fresh_constant i) [])::acc)) (nb_vars,eq_name_1) l_vars_form in
                            let subst_name = Subst.create_multiple Recipe eq_name_2 in

                            let new_mgs_form = Subst.compose mgs_form subst_name in
                            let new_recipe = Subst.apply new_mgs_form recipe (fun r f -> f r) in

                            let csys' =
                              { csys with
                                skeletons_to_check = all_skel;
                                skeletons_checked = skeletons_checked
                              }
                            in
                            Some(id_skel,(mgs_csys,l_vars_csys),new_recipe,csys',q), prev_set
          in

          sub_explore csys.skeletons_checked csys.skeletons_to_check

  (* This rule should only be applied when there are no deduction or equality formula / facts. *)
  let rewrite (f_continuation: 'a Set.t -> (unit -> unit) -> unit) (csys_set:'a Set.t) (f_next:unit -> unit) =

    let rec internal checked_csys to_check_csys f_next = match exploration_rewrite checked_csys to_check_csys with
      | None, checked_csys -> f_continuation checked_csys f_next
      | Some(id_skel,(mgs_csys,l_vars),recipe,csys,to_check_csys), checked_csys ->
          if Subst.is_identity mgs_csys
          then
            begin
              Config.debug (fun () ->
                if l_vars <> []
                then Config.internal_error "[Constraint_system.ml >> rewrite] An identity substitution should imply an empty list of created variables"
              );

              let csys' = match create_generic_skeleton_formula csys id_skel recipe with
                | FoundFact fact -> { csys with uf = UF.add_deduction_fact csys.uf fact }
                | _ -> Config.internal_error "[Constraint_system.ml >> rewrite] We should always find a deduction fact on the constraint system used to compute the most general solution."
              in

              let exists_unsolved = ref false in

              let positive_to_check_list =
                List.fold_left (fun set csys -> match create_generic_skeleton_formula csys id_skel recipe with
                  | FoundFact fact -> { csys with uf = UF.add_deduction_fact csys.uf fact } :: set
                  | NoFormula -> csys :: set
                  | Unsolved form_list ->
                      exists_unsolved := true;
                      { csys with uf = UF.add_deduction_formulas csys.uf form_list } :: set
                ) [csys'] to_check_csys
              in
              let positive_all_csys_list =
                List.fold_left (fun set csys -> match create_generic_skeleton_formula csys id_skel recipe with
                  | FoundFact fact -> { csys with uf = UF.add_deduction_fact csys.uf fact } :: set
                  | NoFormula -> csys :: set
                  | Unsolved form_list ->
                      exists_unsolved := true;
                      { csys with uf = UF.add_deduction_formulas csys.uf form_list } :: set
                ) positive_to_check_list checked_csys
              in

              if !exists_unsolved
              then sat_deduction_formula (normalisation_split_deduction  (normalisation_deduction_consequence (internal [])) (internal [])) positive_all_csys_list f_next
              else normalisation_split_deduction (normalisation_deduction_consequence (internal [])) (internal []) positive_all_csys_list f_next
            end
          else
            begin
              let new_eqsnd = Eq.apply Recipe csys.eqsnd mgs_csys in
              let new_i_subst_snd = Subst.compose_restricted_generic csys.i_subst_snd mgs_csys (fun x -> Variable.quantifier_of x = Free) in
              let data_shared =
                {
                  share_sdf = (Array.make (K.cardinal csys.sdf) dummy_recipe);
                  share_eqsnd = new_eqsnd;
                  share_ded = ref [];
                  share_eq = ref None;
                  share_i_subst_snd = new_i_subst_snd
                }
              in

              let csys' = apply_mgs_and_gather csys data_shared (mgs_csys,l_vars) in
              let csys'' = match create_generic_skeleton_formula csys' id_skel recipe with
                | FoundFact fact -> { csys' with uf = UF.add_deduction_fact csys'.uf fact }
                | _ -> Config.internal_error "[Constraint_system.ml >> rewrite] We should always find a deduction fact on the constraint system used to compute the most general solution (2)."
              in

              let exists_unsolved = ref false in

              let positive_to_check_list =
                List.fold_left (fun set csys ->
                  try
                    let csys_1 = apply_mgs_from_gathering csys data_shared (mgs_csys,l_vars) in

                    match create_generic_skeleton_formula csys_1 id_skel recipe with
                      | FoundFact fact -> { csys_1 with uf = UF.add_deduction_fact csys_1.uf fact } :: set
                      | NoFormula -> csys_1 :: set
                      | Unsolved form_list ->
                          exists_unsolved := true;
                          { csys_1 with uf = UF.add_deduction_formulas csys_1.uf form_list } :: set
                  with Bot -> set
                ) [csys''] to_check_csys
              in
              let positive_all_csys_list =
                List.fold_left (fun set csys ->
                  try
                    let csys_1 = apply_mgs_from_gathering csys data_shared (mgs_csys,l_vars) in

                    match create_generic_skeleton_formula csys_1 id_skel recipe with
                      | FoundFact fact -> { csys_1 with uf = UF.add_deduction_fact csys_1.uf fact } :: set
                      | NoFormula -> csys_1 :: set
                      | Unsolved form_list ->
                          exists_unsolved := true;
                          { csys_1 with uf = UF.add_deduction_formulas csys_1.uf form_list } :: set
                  with Bot -> set
                ) positive_to_check_list checked_csys
              in

              let diseq = Diseq.of_substitution_recipe mgs_csys l_vars in
              let new_eqsnd = Eq.wedge csys.eqsnd diseq in

              let negative_checked_list = List.rev_map (fun csys -> { csys with eqsnd = new_eqsnd }) checked_csys in
              let negative_to_check_list = List.rev_map (fun csys -> { csys with eqsnd = new_eqsnd }) (csys::to_check_csys) in

              let next_negative_function () = internal negative_checked_list negative_to_check_list f_next in

              if !exists_unsolved
              then sat_deduction_formula (normalisation_split_deduction (normalisation_deduction_consequence (internal [])) (internal [])) positive_all_csys_list next_negative_function
              else normalisation_split_deduction (normalisation_deduction_consequence (internal [])) (internal []) positive_all_csys_list next_negative_function
            end
    in

    internal [] csys_set f_next

  (**** The rule Equality Constructor ****)

  let create_eq_constructor_formula csys id_sdf recipe symbol =
    let fact = K.get csys.sdf id_sdf in
    let term = Fact.get_protocol_term fact in

    if is_function term
    then
      let symb = root term in

      if Symbol.is_equal symb symbol
      then
        let t = Tools.consequence_recipe_with_IK csys.sdf csys.ik csys.df recipe in
        let head = Fact.create_equality_fact (Fact.get_recipe fact) recipe in
        Fact.create Fact.Equality head [term,t]
      else raise Fact.Bot
    else raise Fact.Bot

  let rec exploration_equality_constructor (prev_set:'a Set.t) = function
    | [] -> None, prev_set
    | csys::q ->
        if csys.equality_constructor_to_checked = []
        then exploration_equality_constructor (csys::prev_set) q
        else
          let rec sub_explore equality_constructor_checked = function
            | [] -> exploration_equality_constructor ({ csys with equality_constructor_checked = equality_constructor_checked; equality_constructor_to_checked = [] }::prev_set) q
            | id_sdf::q_id ->
                let fact = K.get csys.sdf id_sdf in
                let term = Fact.get_protocol_term fact in

                if is_function term
                then
                  let symb = root term in
                  if Symbol.is_public symb
                  then
                    let stored_constructor = Tools.get_stored_constructor symb in
                    if Eq.Mixed.is_bot stored_constructor.Tools.mixed_diseq
                    then sub_explore equality_constructor_checked q_id
                    else
                      begin match simple_of_equality_constructor csys symb term stored_constructor with
                        | None -> sub_explore equality_constructor_checked q_id
                        | Some (simple_recipe,simple_csys) ->
                            match one_mgs simple_csys with
                              | None -> sub_explore (id_sdf::equality_constructor_checked) q_id
                              | Some (mgs,l_vars) ->
                                  Config.debug (fun () ->
                                    if List.exists Variable.has_infinite_type l_vars
                                    then Config.internal_error "[Constraint_system.ml >> rule_equality_constructor] The list l_vars should not contain second-order variable with unbounded type."
                                  );
                                  let mgs_csys, mgs_form = Subst.split_domain mgs Variable.has_not_infinite_type in
                                  let recipe = Subst.apply mgs_form simple_recipe (fun r f -> f r) in
                                  let csys' =
                                    { csys with
                                      equality_constructor_checked = equality_constructor_checked;
                                      equality_constructor_to_checked = id_sdf::q_id
                                    }
                                  in
                                  Some (mgs_csys,l_vars,id_sdf,recipe,symb,csys',q), prev_set
                      end
                  else sub_explore equality_constructor_checked q_id
                else sub_explore equality_constructor_checked q_id
          in
          sub_explore csys.equality_constructor_checked csys.equality_constructor_to_checked

  let equality_constructor (f_continuation: 'a Set.t -> (unit -> unit) -> unit) (csys_set:'a Set.t) (f_next:unit -> unit) =

    let rec internal checked_csys to_check_csys f_next = match exploration_equality_constructor checked_csys to_check_csys with
      | None, checked_csys_1 -> f_continuation checked_csys_1 f_next
      | Some (mgs_csys,l_vars,id_sdf,recipe,symb,csys,to_check_csys_1), checked_csys_1 ->
          if Subst.is_identity mgs_csys
          then
            begin
              Config.debug (fun () ->
                if l_vars <> []
                then Config.internal_error "[Constraint_system.ml >> internal_equality] An identity substitution should imply an empty list of created variables"
              );
              let fact = K.get csys.sdf id_sdf in
              let head = Fact.create_equality_fact (Fact.get_recipe fact) recipe in
              let csys' = { csys with uf = UF.add_equality_fact csys.uf head } in

              let exists_unsolved = ref false in
              let all_exists = ref true in

              let positive_checked_list =
                List.fold_left (fun set csys ->
                  try
                    let form = create_eq_constructor_formula csys id_sdf recipe symb in

                    if Fact.is_fact form
                    then { csys with uf = UF.add_equality_fact csys.uf head } :: set
                    else
                      begin
                        exists_unsolved := true;
                        { csys with uf = UF.add_equality_formula csys.uf form } :: set
                      end
                  with Fact.Bot ->
                    all_exists := false;
                    csys::set
                ) [csys'] checked_csys_1
              in
              let positive_all_csys_list =
                List.fold_left (fun set csys ->
                  try
                    let form = create_eq_constructor_formula csys id_sdf recipe symb in

                    if Fact.is_fact form
                    then { csys with uf = UF.add_equality_fact csys.uf head } :: set
                    else
                      begin
                        exists_unsolved := true;
                        { csys with uf = UF.add_equality_formula csys.uf form } :: set
                      end
                  with Fact.Bot ->
                    all_exists := false;
                    csys::set
                ) positive_checked_list to_check_csys_1
              in

              let final_apply csys_set f_next =
                let csys_set_1 =
                  List.rev_map (fun csys ->
                    { csys with
                      equality_constructor_to_checked = remove_id_from_list id_sdf csys.equality_constructor_to_checked;
                      uf = UF.remove_equality_fact csys.uf
                    }
                  ) csys_set
                in
                internal [] csys_set_1 f_next
              in

              if !exists_unsolved
              then sat_equality_formula (normalisation_split_equality final_apply (internal [])) positive_all_csys_list f_next
              else
                if !all_exists
                then final_apply positive_all_csys_list f_next
                else normalisation_split_equality final_apply (internal []) positive_all_csys_list f_next
            end
          else
            begin
              let new_eqsnd = Eq.apply Recipe csys.eqsnd mgs_csys in
              let new_i_subst_snd = Subst.compose_restricted_generic csys.i_subst_snd mgs_csys (fun x -> Variable.quantifier_of x = Free) in
              let data_shared =
                {
                  share_sdf = (Array.make (K.cardinal csys.sdf) dummy_recipe);
                  share_eqsnd = new_eqsnd;
                  share_ded = ref [];
                  share_eq = ref None;
                  share_i_subst_snd = new_i_subst_snd
                }
              in
              let csys' = apply_mgs_and_gather csys data_shared (mgs_csys,l_vars) in
              let fact = K.get csys'.sdf id_sdf in
              let head = Fact.create_equality_fact (Fact.get_recipe fact) recipe in
              let csys'' = { csys' with uf = UF.add_equality_fact csys'.uf head } in

              let exists_unsolved = ref false in
              let all_exists = ref true in

              let positive_to_check_csys_list =
                List.fold_left (fun set csys ->
                  try
                    let csys_1 = apply_mgs_from_gathering csys data_shared (mgs_csys,l_vars) in

                    begin try
                      let form_1 = create_eq_constructor_formula csys_1 id_sdf recipe symb in

                      if Fact.is_fact form_1
                      then { csys with uf = UF.add_equality_fact csys.uf head } :: set
                      else
                        begin
                          exists_unsolved := true;
                          { csys with uf = UF.add_equality_formula csys.uf form_1 } :: set
                        end
                    with Fact.Bot ->
                      all_exists := false;
                      csys_1::set
                    end
                  with Bot -> set
                  ) [csys''] to_check_csys_1
              in
              let positive_all_csys_list =
                List.fold_left (fun set csys ->
                  try
                    let csys_1 = apply_mgs_from_gathering csys data_shared (mgs_csys,l_vars) in

                    begin try
                      let form_1 = create_eq_constructor_formula csys_1 id_sdf recipe symb in

                      if Fact.is_fact form_1
                      then { csys with uf = UF.add_equality_fact csys.uf head } :: set
                      else
                        begin
                          exists_unsolved := true;
                          { csys with uf = UF.add_equality_formula csys.uf form_1 } :: set
                        end
                    with Fact.Bot ->
                      all_exists := false;
                      csys_1::set
                    end
                  with Bot -> set
                  ) positive_to_check_csys_list checked_csys_1
              in

              let diseq = Diseq.of_substitution_recipe mgs_csys l_vars in
              let new_eqsnd = Eq.wedge csys.eqsnd diseq in

              let negative_checked_list = List.rev_map (fun csys -> { csys with eqsnd = new_eqsnd }) checked_csys_1 in
              let negative_to_check_list = List.rev_map (fun csys -> { csys with eqsnd = new_eqsnd }) (csys::to_check_csys_1) in

              let final_apply csys_set f_next =
                let csys_set_1 =
                  List.rev_map (fun csys ->
                    { csys with
                      equality_constructor_to_checked = remove_id_from_list id_sdf csys.equality_constructor_to_checked;
                      uf = UF.remove_equality_fact csys.uf
                    }
                  ) csys_set
                in
                internal [] csys_set_1 f_next
              in

              let next_negative_function () = internal negative_checked_list negative_to_check_list f_next in

              if !exists_unsolved
              then sat_equality_formula (normalisation_split_equality final_apply (internal [])) positive_all_csys_list next_negative_function
              else
                if !all_exists
                then final_apply positive_all_csys_list next_negative_function
                else normalisation_split_equality final_apply (internal []) positive_all_csys_list next_negative_function
            end
    in

    internal [] csys_set f_next

  (**** The rule Equality Constructor IK ****)

  let create_eq_constructor_formula_IK csys id_ik recipe symbol =
    let fact = IK.get csys.ik id_ik in
    let term = Fact.get_protocol_term fact in

    if is_function term
    then
      let symb = root term in

      if Symbol.is_equal symb symbol
      then
        let t = Tools.consequence_recipe_with_IK csys.sdf csys.ik csys.df recipe in
        let head = Fact.create_equality_fact (Fact.get_recipe fact) recipe in
        Fact.create Fact.Equality head [term,t]
      else raise Fact.Bot
    else raise Fact.Bot

  let rec exploration_equality_constructor_IK (prev_set:'a Set.t) = function
    | [] -> None, prev_set
    | csys::q ->
        if csys.equality_constructor_to_checked_IK = []
        then exploration_equality_constructor_IK (csys::prev_set) q
        else
          let rec sub_explore equality_constructor_checked_IK = function
            | [] -> exploration_equality_constructor_IK ({ csys with equality_constructor_checked_IK = equality_constructor_checked_IK; equality_constructor_to_checked_IK = [] }::prev_set) q
            | id_ik::q_id ->
                let fact = IK.get csys.ik id_ik in
                let term = Fact.get_protocol_term fact in

                if is_function term
                then
                  let symb = root term in
                  if Symbol.is_public symb
                  then
                    let (simple_recipe,simple_csys) = simple_of_equality_constructor_IK csys symb term in
                    begin match one_mgs simple_csys with
                      | None -> sub_explore (id_ik::equality_constructor_checked_IK) q_id
                      | Some (mgs,l_vars) ->
                          Config.debug (fun () ->
                            if List.exists Variable.has_infinite_type l_vars
                            then Config.internal_error "[Constraint_system.ml >> rule_equality_constructor] The list l_vars should not contain second-order variable with unbounded type."
                          );
                          let mgs_csys, mgs_form = Subst.split_domain mgs Variable.has_not_infinite_type in
                          let recipe = Subst.apply mgs_form simple_recipe (fun r f -> f r) in
                          let csys' =
                            { csys with
                              equality_constructor_checked_IK = equality_constructor_checked_IK;
                              equality_constructor_to_checked_IK = id_ik::q_id
                            }
                          in
                          Some (mgs_csys,l_vars,id_ik,recipe,symb,csys',q), prev_set
                    end
                  else sub_explore equality_constructor_checked_IK q_id
                else sub_explore equality_constructor_checked_IK q_id
          in
          sub_explore csys.equality_constructor_checked_IK csys.equality_constructor_to_checked_IK

  let equality_constructor_IK (f_continuation: 'a Set.t -> (unit -> unit) -> unit) (csys_set:'a Set.t) (f_next:unit -> unit) =

    let rec internal checked_csys to_check_csys f_next = match exploration_equality_constructor_IK checked_csys to_check_csys with
      | None, checked_csys_1 -> f_continuation checked_csys_1 f_next
      | Some (mgs_csys,l_vars,id_ik,recipe,symb,csys,to_check_csys_1), checked_csys_1 ->
          if Subst.is_identity mgs_csys
          then
            begin
              Config.debug (fun () ->
                if l_vars <> []
                then Config.internal_error "[Constraint_system.ml >> internal_equality] An identity substitution should imply an empty list of created variables"
              );
              let fact = IK.get csys.ik id_ik in
              let head = Fact.create_equality_fact (Fact.get_recipe fact) recipe in
              let csys' = { csys with uf = UF.add_equality_fact csys.uf head } in

              let exists_unsolved = ref false in
              let all_exists = ref true in

              let positive_checked_list =
                List.fold_left (fun set csys ->
                  try
                    let form = create_eq_constructor_formula_IK csys id_ik recipe symb in

                    if Fact.is_fact form
                    then { csys with uf = UF.add_equality_fact csys.uf head } :: set
                    else
                      begin
                        exists_unsolved := true;
                        { csys with uf = UF.add_equality_formula csys.uf form } :: set
                      end
                  with Fact.Bot ->
                    all_exists := false;
                    csys::set
                ) [csys'] checked_csys_1
              in
              let positive_all_csys_list =
                List.fold_left (fun set csys ->
                  try
                    let form = create_eq_constructor_formula_IK csys id_ik recipe symb in

                    if Fact.is_fact form
                    then { csys with uf = UF.add_equality_fact csys.uf head } :: set
                    else
                      begin
                        exists_unsolved := true;
                        { csys with uf = UF.add_equality_formula csys.uf form } :: set
                      end
                  with Fact.Bot ->
                    all_exists := false;
                    csys::set
                ) positive_checked_list to_check_csys_1
              in

              let final_apply csys_set f_next =
                let csys_set_1 =
                  List.rev_map (fun csys ->
                    { csys with
                      equality_constructor_to_checked_IK = remove_id_from_list id_ik csys.equality_constructor_to_checked_IK;
                      ik = IK.remove id_ik csys.ik;
                      uf = UF.remove_equality_fact csys.uf
                    }
                  ) csys_set
                in
                internal [] csys_set_1 f_next
              in

              if !exists_unsolved
              then sat_equality_formula (normalisation_split_equality final_apply (internal [])) positive_all_csys_list f_next
              else
                if !all_exists
                then final_apply positive_all_csys_list f_next
                else normalisation_split_equality final_apply (internal []) positive_all_csys_list f_next
            end
          else
            begin
              let new_eqsnd = Eq.apply Recipe csys.eqsnd mgs_csys in
              let new_i_subst_snd = Subst.compose_restricted_generic csys.i_subst_snd mgs_csys (fun x -> Variable.quantifier_of x = Free) in
              let data_shared =
                {
                  share_sdf = (Array.make (K.cardinal csys.sdf) dummy_recipe);
                  share_eqsnd = new_eqsnd;
                  share_ded = ref [];
                  share_eq = ref None;
                  share_i_subst_snd = new_i_subst_snd
                }
              in
              let csys' = apply_mgs_and_gather csys data_shared (mgs_csys,l_vars) in
              let fact = IK.get csys'.ik id_ik in
              let head = Fact.create_equality_fact (Fact.get_recipe fact) recipe in
              let csys'' = { csys' with uf = UF.add_equality_fact csys'.uf head } in

              let exists_unsolved = ref false in
              let all_exists = ref true in

              let positive_to_check_csys_list =
                List.fold_left (fun set csys ->
                  try
                    let csys_1 = apply_mgs_from_gathering csys data_shared (mgs_csys,l_vars) in

                    begin try
                      let form_1 = create_eq_constructor_formula_IK csys_1 id_ik recipe symb in

                      if Fact.is_fact form_1
                      then { csys with uf = UF.add_equality_fact csys.uf head } :: set
                      else
                        begin
                          exists_unsolved := true;
                          { csys with uf = UF.add_equality_formula csys.uf form_1 } :: set
                        end
                    with Fact.Bot ->
                      all_exists := false;
                      csys_1::set
                    end
                  with Bot -> set
                  ) [csys''] to_check_csys_1
              in
              let positive_all_csys_list =
                List.fold_left (fun set csys ->
                  try
                    let csys_1 = apply_mgs_from_gathering csys data_shared (mgs_csys,l_vars) in

                    begin try
                      let form_1 = create_eq_constructor_formula_IK csys_1 id_ik recipe symb in

                      if Fact.is_fact form_1
                      then { csys with uf = UF.add_equality_fact csys.uf head } :: set
                      else
                        begin
                          exists_unsolved := true;
                          { csys with uf = UF.add_equality_formula csys.uf form_1 } :: set
                        end
                    with Fact.Bot ->
                      all_exists := false;
                      csys_1::set
                    end
                  with Bot -> set
                  ) positive_to_check_csys_list checked_csys_1
              in

              let diseq = Diseq.of_substitution_recipe mgs_csys l_vars in
              let new_eqsnd = Eq.wedge csys.eqsnd diseq in

              let negative_checked_list = List.rev_map (fun csys -> { csys with eqsnd = new_eqsnd }) checked_csys_1 in
              let negative_to_check_list = List.rev_map (fun csys -> { csys with eqsnd = new_eqsnd }) (csys::to_check_csys_1) in

              let final_apply csys_set f_next =
                let csys_set_1 =
                  List.rev_map (fun csys ->
                    { csys with
                      equality_constructor_to_checked_IK = remove_id_from_list id_ik csys.equality_constructor_to_checked_IK;
                      ik = IK.remove id_ik csys.ik;
                      uf = UF.remove_equality_fact csys.uf
                    }
                  ) csys_set
                in
                internal [] csys_set_1 f_next
              in

              let next_negative_function () = internal negative_checked_list negative_to_check_list f_next in

              if !exists_unsolved
              then sat_equality_formula (normalisation_split_equality final_apply (internal [])) positive_all_csys_list next_negative_function
              else
                if !all_exists
                then final_apply positive_all_csys_list next_negative_function
                else normalisation_split_equality final_apply (internal []) positive_all_csys_list next_negative_function
            end
    in

    internal [] csys_set f_next

  let initialise_equality_constructor_IK (f_continuation: 'a Set.t -> (unit -> unit) -> unit) (csys_set:'a Set.t) (f_next:unit -> unit) =
    if csys_set = []
    then f_continuation csys_set f_next
    else
      let one_csys = List.hd csys_set in
      let all_id = IK.all_id one_csys.ik in

      let csys_set' =
        List.rev_map (fun csys ->
          Config.debug (fun () ->
            if csys.equality_constructor_to_checked_IK <> []
            then Config.internal_error "[constraint_system.ml >> initialise_equality_constructor_IK] The list equality constructor to check IK";

            if csys.equality_constructor_checked_IK <> []
            then Config.internal_error "[constraint_system.ml >> initialise_equality_constructor_IK] The list equality constructor checked IK";
          );
          { csys with equality_constructor_to_checked_IK = all_id }
        ) csys_set
      in

      f_continuation csys_set' f_next

  let transfer_IK_into_K (f_continuation: 'a Set.t -> (unit -> unit) -> unit) (csys_set:'a Set.t) (f_next:unit -> unit) =
    if csys_set = []
    then f_continuation csys_set f_next
    else
      let one_csys = List.hd csys_set in
      let all_id = IK.all_id one_csys.ik in

      if all_id = []
      then f_continuation csys_set f_next
      else
        let last_id = K.cardinal one_csys.sdf in

        let rec generate_assoc_list n = function
          | [] -> []
          | id_ik::q_id -> (id_ik,n)::(generate_assoc_list (n+1) q_id)
        in

        let assoc_list = generate_assoc_list (last_id + 1) all_id in

        let csys_set' =
          List.rev_map (fun csys ->
            let skeletons_checked =
              List.fold_left (fun acc (id,id_skel) ->
                let id' = List.assoc id assoc_list in
                (id',id_skel)::acc
              ) csys.skeletons_checked csys.skeletons_checked_IK
            in
            let equality_constructor_checked =
              List.fold_left (fun acc id ->
                (List.assoc id assoc_list)::acc
              ) csys.equality_constructor_checked csys.equality_constructor_checked_IK
            in
            let sdf' =
              IK.fold_right (fun acc_sdf fact ->
                K.add acc_sdf csys.size_frame fact
              ) csys.sdf csys.ik
            in

            { csys with
              skeletons_checked = skeletons_checked;
              equality_constructor_checked = equality_constructor_checked;
              skeletons_checked_IK = [];
              equality_constructor_checked_IK = [];
              ik = IK.empty;
              sdf = sdf'
            }
          ) csys_set
        in

        f_continuation csys_set' f_next

  let complete_equality_constructor_IK (f_continuation: 'a Set.t -> (unit -> unit) -> unit) =
    initialise_equality_constructor_IK (equality_constructor_IK (transfer_IK_into_K f_continuation))

  (**** The main rule after an input ****)

  let apply_rules_after_input exists_private (f_continuation: 'a Set.t -> (unit -> unit) -> unit) =
    if exists_private
    then sat (sat_private (sat_disequation f_continuation))
    else sat (sat_disequation f_continuation)

  let apply_rules_after_output exists_private (f_continuation: 'a Set.t -> (unit -> unit) -> unit) =
    if exists_private
    then
      sat (sat_private (sat_disequation (normalisation_split_deduction_axiom (
        normalisation_deduction_consequence (rewrite (equality_constructor (complete_equality_constructor_IK f_continuation)))
      ))))
    else
      sat (sat_disequation (normalisation_split_deduction_axiom (
        normalisation_deduction_consequence (rewrite (equality_constructor (complete_equality_constructor_IK f_continuation)))
      )))
end
