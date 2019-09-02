open Types
open Term
open Extensions

(***********************
***       Facts      ***
************************)

type basic_fact =
  {
    bf_var : recipe_variable;
    bf_term : term
  }

type deduction_fact =
  {
    df_recipe : recipe;
    df_term : term;
  }

type equality_fact =
  {
    ef_recipe1 : recipe;
    ef_recipe2 : recipe;
  }

type deduction_formula =
  {
    df_head : deduction_fact;
    df_equations : (variable * term) list
  }

type equality_formula =
  {
    ef_head : equality_fact;
    ef_equations : (variable * term) list
  }

(*********************************
***       Deduction facts      ***
**********************************)

module DF = struct

  module Var_Comp = struct
    type t = recipe_variable
    let compare = Recipe_Variable.order
  end

  module VarMap = Map.Make(Var_Comp)

  type t = term VarMap.t

  (******* Generation *******)

  let empty : term VarMap.t = VarMap.empty

  let add (df:t) b_fct =
    Config.debug (fun () ->
      try
        let _ = VarMap.find b_fct.bf_var df in
        Config.internal_error "[data_structure.ml >> DF.add] A basic deduction fact with the same second-order variable already exists."
      with
        | Not_found-> ()
    );

    VarMap.add b_fct.bf_var b_fct.bf_term df

  let add_multiple (df:t) bfact_l = List.fold_left add df bfact_l

  let add_multiple_max_type = add_multiple

  let remove (df:t) x_snd =
    Config.debug (fun () ->
      try
        let _ = VarMap.find x_snd df in
        ()
      with
        | Not_found -> Config.internal_error "[data_structure.ml >> DF.remove] No basic deduction fact has the variable given in argument."
    );

    VarMap.remove x_snd df

  let get_term (df:t) (x:recipe_variable) = VarMap.find x df

  (******* Function for MGS *********)

  type mgs_applicability =
    | Solved
    | UnifyVariables of t
    | UnsolvedFact of basic_fact * t * bool (* [true] when there were also unification of variables *)

  exception Found of basic_fact

  let compute_mgs_applicability df =
    let linked_vars = ref [] in
    let vars_to_remove = ref [] in

    let rec explore v t = match t with
      | Var ({ link = NoLink ; _ } as x) ->
          x.link <- XLink v;
          linked_vars := x :: !linked_vars
      | Var { link = XLink v'; _ } ->
          (* We link v to v' *)
          Recipe_Variable.link_recipe v (RVar v');
          vars_to_remove := v :: !vars_to_remove
      | Var { link = TLink t ; _ } -> explore v t
      | Var _ -> Config.internal_error "[data_structure.ml >> DF.compute_mgs_applicability] Unexpected link."
      | _ -> raise (Found { bf_var = v ; bf_term = t })
    in

    try
      VarMap.iter explore df;
      List.iter (fun v -> v.link <- NoLink) !linked_vars;
      if !vars_to_remove = []
      then Solved
      else UnifyVariables(List.fold_left remove df !vars_to_remove)
    with Found bfact ->
      List.iter (fun v -> v.link <- NoLink) !linked_vars;
      if !vars_to_remove = []
      then UnsolvedFact(bfact,remove df bfact.bf_var,false)
      else
        let new_df = List.fold_left remove df (bfact.bf_var :: !vars_to_remove) in
        UnsolvedFact(bfact,new_df,true)
end

module DF2 = struct

  type t = (int * basic_fact list) list

  (******* Generation *******)

  let empty : t = []

  let add (df:t) bfact =
    let type_r = bfact.bf_var.type_r in
    let rec explore = function
      | [] -> [type_r, [bfact]]
      | ((i,_) as head)::q when i < type_r -> head :: (explore q)
      | (i,bfact_list)::q when i = type_r -> (i,bfact::bfact_list)::q
      | _ -> (type_r, [bfact])::df
    in
    explore df

  let add_mutliple (df:t) bfact_list =
    if bfact_list = []
    then df
    else
      let type_r = (List.hd bfact_list).bf_var.type_r in
      let rec explore = function
        | [] -> [type_r,bfact_list]
        | ((i,_) as head)::q when i < type_r -> head :: (explore q)
        | (i,bfact_list')::q when i = type_r -> (i,List.rev_append bfact_list bfact_list')::q
        | _ -> (type_r, bfact_list)::df
      in
      explore df

  let add_multiple_max_type (df:t) bfact_list =
    if bfact_list = []
    then df
    else
      let type_r = (List.hd bfact_list).bf_var.type_r in
      let rec explore = function
        | [] -> [type_r,bfact_list]
        | [(i,bfact_list')] when i = type_r -> [(i,List.rev_append bfact_list bfact_list')]
        | [head] -> [head;(type_r,bfact_list)]
        | head::q -> head :: (explore q)
      in
      explore df

  let remove (df:t) x_snd =
    let type_r = x_snd.type_r in

    let rec remove_bfact = function
      | [] -> Config.internal_error "[data_structure.ml >> DF.remove] No basic deduction fact has the variable given in argument (1)."
      | bfact'::q' when bfact'.bf_var == x_snd -> q'
      | bfact'::q' -> bfact'::(remove_bfact q')
    in

    let rec explore = function
      | ((i,_) as head)::q when i < type_r -> head :: (explore q)
      | (i,bfact_list)::q when i = type_r ->
          let bfact_list' = remove_bfact bfact_list in
          if bfact_list' = []
          then q
          else (i,bfact_list')::q
      | _ -> Config.internal_error "[data_structure.ml >> DF.remove] No basic deduction fact has the variable given in argument (2)."
    in

    explore df

  let get_term (df:t) (x:recipe_variable) =
    let type_r = x.type_r in

    let rec find_bfact = function
      | [] -> raise Not_found
      | bfact::_ when bfact.bf_var == x -> bfact.bf_term
      | _::q -> find_bfact q
    in

    let rec explore = function
      | (i,_)::q when i < type_r -> explore q
      | (i,bfact_list)::_ when i = type_r -> find_bfact bfact_list
      | _ -> raise Not_found
    in

    explore df

  (******* Function for MGS *********)

  type mgs_applicability =
    | Solved
    | UnifyVariables of t
    | UnsolvedFact of basic_fact * t * bool (* [true] when there were also unification of variables *)

  exception Found of basic_fact

  let compute_mgs_applicability df =
    let linked_vars = ref [] in
    let vars_removed = ref false in

    let rec explore_term v t = match t with
      | Var ({ link = NoLink ; _ } as x) ->
          x.link <- XLink v;
          linked_vars := x :: !linked_vars;
          false, None
      | Var { link = XLink v'; _ } ->
          (* We link v to v' *)
          Recipe_Variable.link_recipe v (RVar v');
          vars_removed := true;
          true, None
      | Var { link = TLink t ; _ } -> explore_term v t
      | Var _ -> Config.internal_error "[data_structure.ml >> DF.compute_mgs_applicability] Unexpected link."
      | _ -> true, Some { bf_var = v ; bf_term = t }
    in

    let rec explore_bfact_list = function
      | [] -> [], None
      | bfact::q ->
          match explore_term bfact.bf_var bfact.bf_term with
            | false, None ->
                let (q',res) = explore_bfact_list q in
                (bfact::q',res)
            | true, None -> explore_bfact_list q
            | _, res -> (q,res)
    in

    let rec explore = function
      | [] -> [], None
      | (i,bfact_list)::q ->
          match explore_bfact_list bfact_list with
            | [], None -> explore q
            | [], res -> q,res
            | bfact_list', None ->
                let (q',res) = explore q in
                (i,bfact_list')::q', res
            | bfact_list', res -> (i,bfact_list')::q, res
    in

    match explore df with
      | df', None ->
          List.iter (fun v -> v.link <- NoLink) !linked_vars;
          if !vars_removed
          then UnifyVariables df'
          else Solved
      | df', Some bfact ->
          List.iter (fun v -> v.link <- NoLink) !linked_vars;
          UnsolvedFact(bfact,df',!vars_removed)
end

(*********************************
***       Knowledge base       ***
**********************************)

module K = struct

  type entry =
    {
      type_r : int;
      recipe : recipe;
      term : term
    }

  type t =
    {
      size : int;
      data : entry Array.t
    }

  let dummy_entry = { type_r = 0; recipe = Axiom 0; term = Name { label_n = ""; index_n = 0; link_n = NNoLink; deducible_n = None} }

  let empty = { size = 0; data = Array.make 0 dummy_entry }

  let find_unifier_with_recipe kb t type_r f_continuation (f_next:unit->unit) =

    let rec explore = function
      | i when i = kb.size -> f_next ()
      | i ->
          if kb.data.(i).type_r > type_r
          then f_next ()
          else
            begin
              let tmp = !Variable.currently_linked in
              Variable.currently_linked := [];

              let is_unifiable =
                try
                  Term.unify kb.data.(i).term t;
                  true
                with Term.Not_unifiable -> false
              in
              if is_unifiable
              then
                if !Variable.currently_linked = []
                then
                  (* Identity substitution *)
                  f_continuation true (fun () ->
                    Variable.currently_linked := tmp;
                    f_next ()
                  )
                else
                  f_continuation false (fun () ->
                    List.iter (fun v -> v.link <- NoLink) !Variable.currently_linked;
                    Variable.currently_linked := tmp;
                    explore (i+1)
                  )
              else
                begin
                  List.iter (fun v -> v.link <- NoLink) !Variable.currently_linked;
                  Variable.currently_linked := tmp;
                  explore(i+1)
                end
            end
    in
    explore 0
end

(* Incremented knowledge base *)
module IK = struct

  (* We do not need to know about the type of the recipe as they are always
     of maximum type (i.e. type of the last axiom) *)
  type entry =
    {
      recipe : recipe;
      term : term
    }

  type t = entry list (* To be always kept ordered *)

  let empty = []
end

(************************
***         UF        ***
*************************)

module UF = struct

  type state_ded_form =
    | DedSolved of deduction_fact list
    | DedUnsolved of deduction_formula list
    | DedNone

  type state_eq_form =
    | EqSolved of equality_fact
    | EqUnsolved of equality_formula
    | EqNone

  type t =
    {
      ded_formula : state_ded_form;
      eq_formula : state_eq_form
    }

  (******** Generation ********)

  let empty =
    {
      ded_formula = DedNone;
      eq_formula = EqNone
    }

  let add_equality_fact uf fact =
    Config.debug (fun () ->
      if uf.eq_formula <> EqNone
      then Config.internal_error "[Data_structure.ml >> add_equality_fact] There is already an equality formula or fact in UF."
    );

    { uf with eq_formula = EqSolved fact }

  let add_equality_formula uf form =
    Config.debug (fun () ->
      if uf.eq_formula <> EqNone
      then Config.internal_error "[Data_structure.ml >> add_equality_formula] There is already an equality formula in UF.";

      if form.ef_equations = []
      then Config.internal_error "[Data_structure.ml >> add_equality_formula] The formula should not be solved."
    );

    { uf with eq_formula = EqUnsolved form }

  let add_deduction_fact uf fact =
    Config.debug (fun () ->
      if uf.ded_formula <> DedNone
      then Config.internal_error "[Data_structure.ml >> add_deduction_fact] There is already a deduction formula or fact in UF."
      );

    { uf with ded_formula = DedSolved [fact] }

  let add_deduction_formulas uf form_list =
    Config.debug (fun () ->
      if uf.ded_formula <> DedNone
      then Config.internal_error "[Data_structure.ml >> UF.add_deduction_formulas] There is already a deduction formula in UF.";

      if form_list = []
      then Config.internal_error "[Data_structure.ml >> UF.add_deduction_formulas] The list of deduction formulas given as argument should not be empty.";

      if List.exists (fun df -> df.df_equations = []) form_list
      then Config.internal_error "[Data_structure.ml >> UF.add_deduction_formulas] The list should only contain unsolved deduction formulas."
      );

    { uf with ded_formula = DedUnsolved form_list }

  let replace_deduction_facts uf fact_list =
    Config.debug (fun () ->
      match uf.ded_formula, uf.eq_formula with
        | DedSolved [_], EqNone -> ()
        | _ -> Config.internal_error "[Data_structure.ml >> UF.replace_deduction_facts] There should be only one deduction fact and no equality fact."
    );
    { ded_formula = DedSolved fact_list; eq_formula = EqNone}

  let remove_one_deduction_fact uf = match uf.ded_formula with
    | DedSolved [_] -> { uf with ded_formula = DedNone }
    | DedSolved (_::q) -> { uf with ded_formula = DedSolved q }
    | _ -> Config.internal_error "[data_structure.ml >> UF.remove_one_deduction_facts] There should be at least one deduction fact."

  let remove_equality_fact uf =
    Config.debug (fun () ->
      match uf.eq_formula with
        | EqSolved _ -> ()
        | _ -> Config.internal_error "[data_structure.ml >> UF.remove_equality_fact] There should be an equality fact."
    );
    { uf with eq_formula = EqNone }

  let remove_one_unsolved_equality_formula uf =
    Config.debug (fun () ->
      match uf.eq_formula with
        | EqUnsolved _ -> ()
        | _ -> Config.internal_error "[data_structure.ml >> UF.remove_usolved] UF should contain an unsolved equality formula."
    );
    { uf with eq_formula = EqNone }

  let remove_one_unsolved_deduction_formula uf = match uf.ded_formula with
    | DedUnsolved (_::q) -> { uf with ded_formula = DedUnsolved q }
    | _ -> Config.internal_error "[data_structure.ml >> UF.remove_usolved] UF should contain an unsolved deduction formula."

  let filter_unsolved uf f = match uf.ded_formula with
    | DedUnsolved form_list ->
        let result = List.filter_unordered f form_list in
        if result = []
        then { uf with ded_formula = DedNone }
        else { uf with ded_formula = DedUnsolved result }
    | _ -> Config.internal_error "[data_structure.ml >> UF.filter_unsolved] There should be unsolved formula."

  (******** Testing ********)

  let exists_equality_fact uf = match uf.eq_formula with
    | EqSolved _ -> true
    | _ -> false

  let exists_deduction_fact uf = match uf.ded_formula with
    | DedSolved _ -> true
    | _ -> false

  let exists_unsolved_equality_formula uf = match uf.eq_formula with
    | EqUnsolved _ -> true
    | _ -> false

  (******** Access ********)

  let pop_deduction_fact uf = match uf.ded_formula with
    | DedSolved (t::_) -> t
    | _ -> Config.internal_error "[data_structure.ml >> UF.pop_deduction_fact] There should be at least one deduction fact."

  let pop_deduction_fact_option uf = match uf.ded_formula with
    | DedSolved (t::_) -> Some t
    | _ -> None

  let pop_equality_fact_option uf = match uf.eq_formula with
    | EqSolved t -> Some t
    | _ -> None

  let pop_deduction_formula_option uf = match uf.ded_formula with
    | DedUnsolved (t::_) -> Some t
    | _ -> None

  let pop_equality_formula_option uf = match uf.eq_formula with
    | EqUnsolved t -> Some t
    | _ -> None

  let number_of_deduction_facts uf = match uf.ded_formula with
    | DedSolved l -> List.length l
    | _ -> 0
end
