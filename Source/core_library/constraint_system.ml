(**************************************************************************)
(*                                                                        *)
(*                               DeepSec                                  *)
(*                                                                        *)
(*               Vincent Cheval, project PESTO, INRIA Nancy               *)
(*                Steve Kremer, project PESTO, INRIA Nancy                *)
(*            Itsaka Rakotonirina, project PESTO, INRIA Nancy             *)
(*                                                                        *)
(*   Copyright (C) INRIA 2017-2020                                        *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU General Public License version 3.0 as described in the       *)
(*   file LICENSE                                                         *)
(*                                                                        *)
(**************************************************************************)

open Types
open Term
open Formula
open Data_structure
open Extensions
open Display

(*************************************
***       Constraint systems       ***
**************************************)

type history_skeleton =
  {
    destructor : symbol;
    fst_vars : variable list;
    snd_vars : recipe_variable list;
    diseq : Formula.M.t
  }

type rule_data =
  {
    history_skeleton : history_skeleton list;
    skeletons_K : (int * int) list * (int * int) list; (* First argument are checked, second to check *)
    skeletons_IK : (int * int) list * (int * int) list;  (* First argument are checked, second to check *)

    equality_constructor_K : int list * int list; (* First argument are checked, second to check *)
    equality_constructor_IK : int list * int list; (* First argument are checked, second to check *)

    normalisation_deduction_checked : bool (* To be set to false every time we apply a substitution on the constraint system. *)
  }

type 'a t =
  {
    additional_data : 'a;

    size_frame : int;

    (* Deduction requirement *)

    deduction_facts : DF.t;
    non_deducible_terms : term list; (* List of terms that should not be deducible. *)

    (* Knowledge base *)

    knowledge : K.t;
    incremented_knowledge : IK.t;

    unsolved_facts : UF.t;

    (* The formulae *)

    eq_term : Formula.T.t;
    eq_uniformity : Formula.T.t;

    (* Original variables and names *)

    original_substitution : (variable * term) list;

    (* Data for rules *)
    rule_data : rule_data
  }

type 'a set =
  {
    eq_recipe : Formula.R.t;
    knowledge_recipe : KR.t;
    set : 'a t list
  }

exception Bot

(********* Generators *********)

let generate_history f =
  let rec generate_vars fst_vars snd_vars = function
    | 0 -> fst_vars, snd_vars
    | n ->
        let x_fst = Variable.fresh Existential in
        let x_snd = Recipe_Variable.fresh Existential Recipe_Variable.infinite_type in
        generate_vars (x_fst::fst_vars) (x_snd::snd_vars) (n-1)
  in

  let (fst_vars, snd_vars) = generate_vars [] [] (Symbol.get_arity f) in

  {
    destructor = f;
    fst_vars = fst_vars;
    snd_vars = snd_vars;
    diseq = Formula.M.Top
  }

let empty data =
  {
    additional_data = data;
    size_frame = 0;
    deduction_facts = DF.empty;
    non_deducible_terms = [];
    knowledge = K.empty;
    incremented_knowledge = IK.empty;
    unsolved_facts = UF.empty;
    eq_term = Formula.T.Top;
    eq_uniformity = Formula.T.Top;
    original_substitution = [];

    rule_data =
      {
        history_skeleton = List.fold_left (fun acc f -> if f.public then (generate_history f)::acc else acc) [] !Symbol.all_destructors;
        skeletons_K = ([],[]);
        skeletons_IK = ([],[]);
        equality_constructor_K = ([],[]);
        equality_constructor_IK = ([],[]);
        normalisation_deduction_checked = false
      }
  }

let add_basic_facts csys bfact_list =
  { csys with deduction_facts = DF.add_multiple_max_type csys.deduction_facts bfact_list }

let add_axiom csys ax t =
  Config.debug (fun () ->
    if csys.size_frame + 1 <> ax
    then Config.internal_error "[constraint_system.ml >> add_axiom] The axiom given as argument should have an index equal to the size of the frame + 1";
  );

  { csys with
    unsolved_facts = UF.add_deduction_fact csys.unsolved_facts { df_recipe = Axiom ax; df_term = t};
    size_frame = csys.size_frame + 1
  }

let add_disequations csys diseq_list =
  { csys with eq_term = Formula.T.wedge_conjunction diseq_list csys.eq_term }

let add_non_deducible_terms csys l =
  Config.debug (fun () ->
    if csys.non_deducible_terms <> []
    then Config.internal_error "[constraint_system.ml >> add_non_deducible_terms] The current list should be empty."
  );
  { csys with non_deducible_terms = l }

(*** Completion of solving procedure ***)

(* In this function, we rename all variables and names by fresh ones. Moreover, we
   instantiate the terms. Note that only the variales in the original substitution
   will not be renames (They are all free variables.
   We also transfer the incremented knowledge base inside the knowledge base.
   Skeletons are updated accordingly.
   Finally, the knowledge base being mutable, we also do a copy of it. *)

let generic_prepare_for_solving kb ikb id_assoc csys =
  let df = DF.rename_and_instantiate csys.deduction_facts in
  let non_deducible_terms = List.rev_map Term.rename_and_instantiate csys.non_deducible_terms in
  let uf = UF.rename_and_instantiate csys.unsolved_facts in
  let eq_term = Formula.T.rename_and_instantiate csys.eq_term in
  let eq_uni = Formula.T.rename_and_instantiate csys.eq_uniformity in
  let orig_subst =
    List.map_q (fun ((v,t) as sub) ->
      let t' = Term.rename_and_instantiate t in
      if t == t'
      then sub
      else (v, t')
    ) csys.original_substitution
  in

  let history_skeleton =
    List.map_q (fun hist ->
      let diseq' = Formula.M.rename_and_instantiate hist.fst_vars hist.diseq in
      if diseq' == hist.diseq
      then hist
      else { hist with  diseq = diseq' }
    ) csys.rule_data.history_skeleton
  in

  let skeletons_checked_K = match csys.rule_data.skeletons_K, csys.rule_data.skeletons_IK with
    | (checked_K,[]), (checked_IK,[]) ->
        List.fold_left (fun acc (index_ikb,index_skel) ->
          Config.debug (fun () ->
            if List.assoc_opt index_ikb id_assoc = None
            then Config.internal_error "[constraint_system.ml >> prepare_for_solving_procedure] Index not found."
          );
          (List.assoc index_ikb id_assoc,index_skel)::acc
        ) checked_K checked_IK
    | _ -> Config.internal_error "[constraint_system.ml >> prepare_for_solving_procedure] All skeletons should have been checked."
  in

  let equality_constructor_checked_K = match csys.rule_data.equality_constructor_K, csys.rule_data.equality_constructor_IK with
    | (checked_K,[]), (checked_IK,[]) ->
        List.fold_left (fun acc index_ikb ->
          Config.debug (fun () ->
            if List.assoc_opt index_ikb id_assoc = None
            then Config.internal_error "[constraint_system.ml >> prepare_for_solving_procedure] Index not found (2)."
          );
          (List.assoc index_ikb id_assoc)::acc
        ) checked_K checked_IK
    | _ -> Config.internal_error "[constraint_system.ml >> prepare_for_solving_procedure] All constructor skeletons should have been checked."
  in

  let rule_data =
    {
      history_skeleton = history_skeleton;
      skeletons_K = (skeletons_checked_K,[]);
      skeletons_IK = ([],[]);
      equality_constructor_K = (equality_constructor_checked_K,[]);
      equality_constructor_IK = ([],[]);
      normalisation_deduction_checked = csys.rule_data.normalisation_deduction_checked
    }
  in

  { csys with
    deduction_facts = df;
    non_deducible_terms = non_deducible_terms;
    knowledge = kb;
    incremented_knowledge = ikb;
    unsolved_facts = uf;
    eq_term = eq_term;
    eq_uniformity = eq_uni;
    original_substitution = orig_subst;
    rule_data = rule_data
  }

let prepare_for_solving_procedure_first after_output kbr csys =
  Variable.auto_cleanup_with_reset_notail (fun () ->
    let (kbr',kb,ikb,id_assoc) = IK.transfer_incremented_knowledge_into_knowledge after_output kbr csys.knowledge csys.incremented_knowledge in
    let csys' = generic_prepare_for_solving kb ikb id_assoc csys in
    csys', kbr',ikb,id_assoc
  )

let prepare_for_solving_procedure_others ikb id_assoc csys =
  Variable.auto_cleanup_with_reset_notail (fun () ->
    let kb = IK.transfer_incremented_knowledge_into_knowledge_only_kb csys.knowledge csys.incremented_knowledge in
    generic_prepare_for_solving kb ikb id_assoc csys
  )

let generic_prepare_for_solving_ground kb ikb id_assoc csys =
  let skeletons_checked_K = match csys.rule_data.skeletons_K, csys.rule_data.skeletons_IK with
    | (checked_K,[]), (checked_IK,[]) ->
        List.fold_left (fun acc (index_ikb,index_skel) ->
          Config.debug (fun () ->
            if List.assoc_opt index_ikb id_assoc = None
            then Config.internal_error "[constraint_system.ml >> prepare_for_solving_procedure] Index not found."
          );
          (List.assoc index_ikb id_assoc,index_skel)::acc
        ) checked_K checked_IK
    | _ -> Config.internal_error "[constraint_system.ml >> prepare_for_solving_procedure] All skeletons should have been checked."
  in

  let equality_constructor_checked_K = match csys.rule_data.equality_constructor_K, csys.rule_data.equality_constructor_IK with
    | (checked_K,[]), (checked_IK,[]) ->
        List.fold_left (fun acc index_ikb ->
          Config.debug (fun () ->
            if List.assoc_opt index_ikb id_assoc = None
            then Config.internal_error "[constraint_system.ml >> prepare_for_solving_procedure] Index not found (2)."
          );
          (List.assoc index_ikb id_assoc)::acc
        ) checked_K checked_IK
    | _ -> Config.internal_error "[constraint_system.ml >> prepare_for_solving_procedure] All constructor skeletons should have been checked."
  in

  let rule_data =
    { csys.rule_data with
      skeletons_K = (skeletons_checked_K,[]);
      skeletons_IK = ([],[]);
      equality_constructor_K = (equality_constructor_checked_K,[]);
      equality_constructor_IK = ([],[])
    }
  in

  { csys with
    knowledge = kb;
    incremented_knowledge = ikb;
    rule_data = rule_data
  }

let prepare_for_solving_procedure_first_ground kbr csys =
  Variable.auto_cleanup_with_reset_notail (fun () ->
    let (kbr',kb,ikb,id_assoc) = IK.transfer_incremented_knowledge_into_knowledge_no_rename kbr csys.knowledge csys.incremented_knowledge in
    let csys' = generic_prepare_for_solving_ground kb ikb id_assoc csys in
    csys', kbr', ikb, id_assoc
  )

let prepare_for_solving_procedure_others_ground ikb id_assoc csys =
  Variable.auto_cleanup_with_reset_notail (fun () ->
    let kb = IK.transfer_incremented_knowledge_into_knowledge_only_kb_no_rename csys.knowledge csys.incremented_knowledge in
    generic_prepare_for_solving_ground kb ikb id_assoc csys
  )

(* This function should only be applied on solved constraint system. *)
let instantiate csys =
  Config.debug (fun () ->
    DF.iter (fun bfact ->
      if not (Term.is_variable bfact.bf_term)
      then Config.internal_error "[constraint_system.ml >> instantiate] All term in the deduction facts should be variables."
    ) csys.deduction_facts;

    if csys.non_deducible_terms <> []
    then Config.internal_error "[constraint_system.ml >> instantiate] There should not be any non deducible terms.";

    if csys.unsolved_facts <> UF.empty
    then Config.internal_error "[constraint_system.ml >> instantiate] All unsolved facts should have been resolved."
  );

  let orig_subst =
    List.map_q (fun ((v,t) as sub) ->
      let t' = Term.instantiate t in
      if t == t'
      then sub
      else (v, t')
    ) csys.original_substitution
  in
  let df' = DF.instantiate csys.deduction_facts in
  let k' = K.instantiate csys.knowledge in
  let ik' = IK.instantiate csys.incremented_knowledge in

  if df' == csys.deduction_facts && k' == csys.knowledge && ik' == csys.incremented_knowledge && orig_subst == csys.original_substitution
  then csys
  else
    { csys with
      deduction_facts = DF.instantiate csys.deduction_facts;
      knowledge = K.instantiate csys.knowledge;
      incremented_knowledge = IK.instantiate csys.incremented_knowledge;
      original_substitution = orig_subst
    }

let rec link_top_level_names = function
  | Var { link = TLink t; _ } -> link_top_level_names t;
  | Name n ->
      Config.debug (fun () ->
        if n.link_n <> NNoLink
        then Config.internal_error "[constraint_system.ml >> link_top_level_names] Names should not be link at that point."
      );
      Name.link_search n
  | _ -> ()

let link_deducible_name csys = K.iter_term link_top_level_names csys.knowledge


let display_couple_list f (l1,l2) =
  Printf.sprintf "(%s,%s)"
    (display_list f "," l1)
    (display_list f "," l2)

let display_history_skeleton tab hist =
  let str = Printf.sprintf "Symb = %s / Fst vars = %s / Snd vars = %s / Mixed diseq = %s"
    (Symbol.display Terminal hist.destructor)
    (display_list (Variable.display Terminal) "," hist.fst_vars)
    (display_list (Recipe_Variable.display ~display_type:true ~label:"X" Terminal) "," hist.snd_vars)
    (Formula.M.display Terminal hist.diseq)
  in

  display_with_tab tab str

let display_rule_data tab data =
  display_object tab None [
    "skeletons_K", (display_couple_list (fun (x1,x2) -> Printf.sprintf "(%d,%d)" x1 x2) data.skeletons_K);
    "skeletons_IK", (display_couple_list (fun (x1,x2) -> Printf.sprintf "(%d,%d)" x1 x2) data.skeletons_IK);
    "equality_cons_K", (display_couple_list string_of_int data.equality_constructor_K);
    "equality_cons_IK", (display_couple_list string_of_int data.equality_constructor_IK);
    "normalisation_checked", string_of_bool data.normalisation_deduction_checked;
    "history_skeleton", ("\n"^(display_list (display_history_skeleton (tab+1)) "" data.history_skeleton))
  ]

let display_constraint_system tab kbr csys =
  display_object tab None [
    "Size frame", string_of_int csys.size_frame;
    "DF", DF.display csys.deduction_facts;
    "K_IK", IK.display (tab+1) kbr csys.knowledge csys.incremented_knowledge;
    "UF", UF.display (tab+1) csys.unsolved_facts;
    "Eq_term", Formula.T.display Display.Terminal csys.eq_term;
    "Orig_subst", (Display.display_list (fun (x,t) ->
        Printf.sprintf "%s -> %s" (Variable.display Display.Terminal x) (Term.display Display.Terminal t)
      ) "; " csys.original_substitution);
    "rule_data", display_rule_data (tab+1) csys.rule_data
  ]

let debug_check_origination msg csys =
  try
    Variable.auto_cleanup_with_exception (fun () ->
      DF.debug_link_with_SLink csys.deduction_facts;
      K.debug_check_link_with_SLink csys.knowledge;
      IK.debug_check_link_with_SLink csys.incremented_knowledge;
      UF.debug_check_link_with_SLink csys.unsolved_facts;
      List.iter (fun (_,t) -> Term.debug_check_link_with_SLink t) csys.original_substitution
    )
  with Not_found -> Config.internal_error (msg^" Origination incorrect")

let debug_on_constraint_system msg ?(solved=true) csys =
  DF.debug msg csys.deduction_facts;
  if solved && not (DF.is_solved csys.deduction_facts)
  then Config.internal_error (msg^" The constraint system should be solved.");
  debug_check_origination msg csys;
  if not (Formula.T.debug_no_linked_variables csys.eq_term)
  then Config.internal_error (msg^" Variables in eq_term should not be linked.");
  if not (Formula.T.debug_no_linked_variables csys.eq_uniformity)
  then Config.internal_error (msg^" Variables in eq_uniformity should not be linked.")

(****************************************
***       Most general solutions      ***
*****************************************)

module MGS = struct

  type simplified_constraint_system =
    {
      simp_deduction_facts : DF.t;

      simp_knowledge_recipe : KR.t;
      simp_knowledge : K.t;
      simp_incremented_knowledge : IK.t;

      simp_eq_term : Formula.T.t;
      simp_eq_recipe : Formula.R.t;
      simp_eq_uniformity : Formula.T.t;
      simp_eq_skeleton : Formula.M.t
    }

  (***** Generators ******)

  let simple_of csys kbr eq_recipe =
    {
      simp_deduction_facts = csys.deduction_facts;
      simp_knowledge_recipe = kbr;
      simp_knowledge = csys.knowledge;
      simp_incremented_knowledge = csys.incremented_knowledge;
      simp_eq_term = csys.eq_term;
      simp_eq_recipe = eq_recipe;
      simp_eq_uniformity = csys.eq_uniformity;
      simp_eq_skeleton = Formula.M.Top
    }

  let simple_of_disequation csys kbr eq_recipe diseq =
    let subst = Diseq.T.substitution_of diseq in
    List.iter (fun (v,t) -> Variable.link_term v t) subst;

    let eq_term = Formula.T.instantiate_and_normalise csys.eq_term in
    if Formula.T.Bot = eq_term
    then None
    else
      let eq_uni = Formula.T.instantiate_and_normalise csys.eq_uniformity in
      if Formula.T.Bot = eq_uni
      then None
      else
        Some {
          simp_deduction_facts = csys.deduction_facts;
          simp_knowledge_recipe = kbr;
          simp_knowledge = csys.knowledge;
          simp_incremented_knowledge = csys.incremented_knowledge;
          simp_eq_term = eq_term;
          simp_eq_recipe = eq_recipe;
          simp_eq_uniformity = eq_uni;
          simp_eq_skeleton = Formula.M.Top
        }

  let simple_of_non_deducible_term csys kbr eq_recipe t =
    let x = Recipe_Variable.fresh Existential Recipe_Variable.infinite_type in
    let bfact = { bf_var = x ; bf_term = t } in
    {
      simp_deduction_facts = DF.add csys.deduction_facts bfact;
      simp_knowledge_recipe = kbr;
      simp_knowledge = csys.knowledge;
      simp_incremented_knowledge = csys.incremented_knowledge;
      simp_eq_term = csys.eq_term;
      simp_eq_recipe = eq_recipe;
      simp_eq_uniformity = csys.eq_uniformity;
      simp_eq_skeleton = Formula.M.Top
    }, x

  type result_simple_of_formula =
    | SFNone
    | SFSolved
    | SFSome of (variable * term) list * simplified_constraint_system

  let simple_of_equality_formula ?(universal=true) csys kbr eq_recipe form =
    let tmp = !Variable.currently_linked in
    Variable.currently_linked := [];
    try
      List.iter (fun (v,t) -> Term.unify (Var v) t) form;

      if universal
      then List.iter (fun v -> Term.replace_universal_to_existential (Var v)) !Variable.currently_linked;

      let result =
        if List.for_all (fun v -> v.quantifier = Universal) !Variable.currently_linked
        then SFSolved
        else
          let eq_term = Formula.T.instantiate_and_normalise csys.eq_term in
          if Formula.T.Bot = eq_term
          then SFNone
          else
            let eq_uni = Formula.T.instantiate_and_normalise csys.eq_uniformity in
            if Formula.T.Bot = eq_uni
            then SFNone
            else
              let subst =
                List.rev_map (fun v -> match v.link with
                  | TLink t -> v,t
                  | _ -> Config.internal_error "[constraint_system.ml >> simple_of_equality_formula] Unexpected link."
                ) !Variable.currently_linked
              in
              SFSome (subst,{
                simp_deduction_facts = csys.deduction_facts;
                simp_knowledge_recipe = kbr;
                simp_knowledge = csys.knowledge;
                simp_incremented_knowledge = csys.incremented_knowledge;
                simp_eq_term = eq_term;
                simp_eq_recipe = eq_recipe;
                simp_eq_uniformity = eq_uni;
                simp_eq_skeleton = Formula.M.Top
              })
      in
      List.iter (fun v -> v.link <- NoLink) !Variable.currently_linked;
      Variable.currently_linked := tmp;
      result
    with Term.Not_unifiable ->
      List.iter (fun v -> v.link <- NoLink) !Variable.currently_linked;
      Variable.currently_linked := tmp;
      SFNone

  let simple_of_deduction_formula csys kbr eq_recipe form =
    let tmp = !Variable.currently_linked in
    Variable.currently_linked := [];

    let result =
      try
        List.iter (fun (v,t) -> Term.unify (Var v) t) form.df_equations;

        List.iter (fun v -> Term.replace_universal_to_existential (Var v)) !Variable.currently_linked;

        let eq_term = Formula.T.instantiate_and_normalise csys.eq_term in
        if Formula.T.Bot = eq_term
        then None
        else
          let eq_uni = Formula.T.instantiate_and_normalise csys.eq_uniformity in
          if Formula.T.Bot = eq_uni
          then None
          else
            Some {
              simp_deduction_facts = csys.deduction_facts;
              simp_knowledge_recipe = kbr;
              simp_knowledge = csys.knowledge;
              simp_incremented_knowledge = csys.incremented_knowledge;
              simp_eq_term = eq_term;
              simp_eq_recipe = eq_recipe;
              simp_eq_uniformity = eq_uni;
              simp_eq_skeleton = Formula.M.Top
            }
      with Term.Not_unifiable -> None
    in
    if result = None
    then
      begin
        List.iter (fun v -> v.link <- NoLink) !Variable.currently_linked;
        Variable.currently_linked := tmp;
        None
      end
    else result

  type result_simple_of_skeleton =
    | RSSNone
    | RSSNo_IK_solution
    | RSSSimple of recipe * simplified_constraint_system * basic_fact list * recipe_variable list

  let rec term_cannot_be_deduced_by_incremented_knowledge size_kb ikb = function
    | Var { link = TLink t; _ } -> term_cannot_be_deduced_by_incremented_knowledge size_kb ikb t
    | Var _ -> false
    | (Name _) as t ->
        IK.for_all_term (fun t' ->
          Variable.auto_cleanup_with_reset_notail (fun () ->
            try
              Term.unify t t';
              false
            with Term.Not_unifiable -> true
          )
        ) ikb
    | Func(f,[]) when f.public -> true
    | Func(_,args) as t ->
        if
          IK.for_all_term (fun t' ->
            Variable.auto_cleanup_with_reset_notail (fun () ->
              try
                Term.unify t t';
                false
              with Term.Not_unifiable -> true
            )
          ) ikb
        then List.for_all (term_cannot_be_deduced_by_incremented_knowledge size_kb ikb) args
        else false

  let simple_of_skeleton csys kbr eq_recipe index_kb index_skel =
    let (recipe,term) = IK.get kbr csys.knowledge csys.incremented_knowledge index_kb in
    let skel = Rewrite_rules.get_skeleton index_skel in
    let symb = Recipe.root skel.Rewrite_rules.recipe in
    try
      Term.unify term skel.Rewrite_rules.pos_term;

      let eq_term = Formula.T.instantiate_and_normalise csys.eq_term in
      if Formula.T.Bot = eq_term
      then RSSNone
      else
        let eq_uni = Formula.T.instantiate_and_normalise csys.eq_uniformity in
        if Formula.T.Bot = eq_uni
        then RSSNone
        else
          begin
            Recipe_Variable.link_recipe skel.Rewrite_rules.pos_vars (CRFunc(index_kb,recipe));

            let hist = List.find (fun hist -> hist.destructor == symb) csys.rule_data.history_skeleton in
            List.iter2 (fun x t -> Variable.link_term x t) hist.fst_vars skel.Rewrite_rules.lhs;
            List.iter2 (fun x r -> Recipe_Variable.link_recipe x r) hist.snd_vars (Recipe.get_args skel.Rewrite_rules.recipe);
            let eq_skeleton = Formula.M.instantiate_and_normalise_full hist.diseq in

            if Formula.M.Bot = eq_skeleton
            then RSSNone
            else
              let size = KR.size kbr in
              if index_kb < size && List.for_all (fun bfact -> term_cannot_be_deduced_by_incremented_knowledge size csys.incremented_knowledge bfact.bf_term) skel.Rewrite_rules.basic_deduction_facts
              then RSSNo_IK_solution
              else
                let simple_csys =
                  {
                    simp_deduction_facts = csys.deduction_facts;
                    simp_eq_term = eq_term;
                    simp_eq_uniformity = eq_uni;
                    simp_eq_recipe = eq_recipe;
                    simp_knowledge_recipe = kbr;
                    simp_knowledge = csys.knowledge;
                    simp_incremented_knowledge = csys.incremented_knowledge;
                    simp_eq_skeleton = eq_skeleton
                  }
                in
                RSSSimple(Recipe.instantiate_preserve_context skel.Rewrite_rules.recipe,simple_csys,skel.Rewrite_rules.basic_deduction_facts,skel.Rewrite_rules.snd_vars)
          end
    with Term.Not_unifiable -> RSSNone

  let simple_of_equality_constructor csys kbr eq_recipe index_kb symb args skeleton_cons =

    let new_formula =
      if Formula.M.Top = skeleton_cons.Rewrite_rules.formula
      then Formula.M.Top
      else
        Variable.auto_cleanup_with_reset_notail (fun () ->
          List.iter2 (fun x t -> Variable.link_term x t) skeleton_cons.Rewrite_rules.term_vars args;
          Formula.M.instantiate_and_normalise_full skeleton_cons.Rewrite_rules.formula
        )
    in

    if Formula.M.Bot = new_formula
    then RSSNone
    else
      let size = KR.size kbr in
      if index_kb < size && List.for_all (term_cannot_be_deduced_by_incremented_knowledge size csys.incremented_knowledge) args
      then RSSNo_IK_solution
      else
        let additional_basic_facts = List.map2 (fun x t -> { bf_var = x; bf_term = t}) skeleton_cons.Rewrite_rules.recipe_vars args in

        let simple_csys =
          {
            simp_deduction_facts = csys.deduction_facts;
            simp_eq_term = csys.eq_term;
            simp_eq_uniformity = csys.eq_uniformity;
            simp_knowledge_recipe = kbr;
            simp_eq_recipe = eq_recipe;
            simp_knowledge = csys.knowledge;
            simp_incremented_knowledge = csys.incremented_knowledge;
            simp_eq_skeleton = new_formula
          }
        in
        RSSSimple(RFunc(symb,List.map (fun x -> RVar x) skeleton_cons.Rewrite_rules.recipe_vars), simple_csys,additional_basic_facts,skeleton_cons.Rewrite_rules.recipe_vars)

  (***** Compute MGS *****)

  type mgs_data =
    {
      mgs_deduction_facts : DF.t;
      mgs_eq_term : Formula.T.t;
      mgs_eq_recipe : Formula.R.t;
      mgs_eq_uniformity : Formula.T.t;
      mgs_eq_skeleton : Formula.M.t;
      mgs_fresh_existential_vars : recipe_variable list
    }

  let compute_all csys f_found_mgs f_next =
    Config.debug (fun () -> DF.debug "[compute_all]" csys.simp_deduction_facts);
    let rec apply_rules df eq_term eq_rec eq_uni exist_vars f_next_0 =
      Config.debug (fun () -> DF.debug "[compute_all >> apply_rules]" df);
      Recipe_Variable.auto_cleanup_with_reset (fun f_next_1 ->
        match DF.compute_mgs_applicability df with
          | DF.Solved ->
              let exist_vars' =
                List.fold_left (fun acc v -> match v.link_r with
                  | RNoLink -> v::acc
                  | _ -> acc
                ) [] exist_vars
              in
              f_found_mgs { mgs_deduction_facts = df; mgs_eq_term = eq_term; mgs_eq_recipe = eq_rec; mgs_eq_uniformity =  eq_uni; mgs_eq_skeleton = Formula.M.Top; mgs_fresh_existential_vars = exist_vars' } f_next_1
          | DF.UnifyVariables df' ->
              Config.debug (fun () -> DF.debug "[compute_all >> apply_rules >> UnifyVariables]" df');
              let eq_rec' = Formula.R.instantiate_and_normalise eq_rec in
              if eq_rec' = Formula.R.Bot
              then f_next_1 ()
              else
                let exist_vars' =
                  List.fold_left (fun acc v -> match v.link_r with
                    | RNoLink -> v::acc
                    | _ -> acc
                  ) [] exist_vars
                in
                f_found_mgs { mgs_deduction_facts = df'; mgs_eq_term = eq_term; mgs_eq_recipe = eq_rec'; mgs_eq_uniformity =  eq_uni; mgs_eq_skeleton = Formula.M.Top; mgs_fresh_existential_vars = exist_vars' } f_next_1
          | DF.UnsolvedFact(bfact,df',unif) ->
              let x = bfact.bf_var
              and t = bfact.bf_term in
              Config.debug (fun () -> DF.debug "[compute_all >> apply_rules >> UnsolvedFact]" df');
              Config.debug (fun () ->
                if x.type_r = Recipe_Variable.infinite_type
                then Config.internal_error "[constraint_system.ml >> MGS.compute_all] There should not be variable with infinite type when computing all mgs."
              );

              match t with
                | Func(f,[]) when f.public ->
                    let r = RFunc(f,[]) in
                    Recipe_Variable.link_recipe x r;
                    let eq_rec' =
                      if unif
                      then Formula.R.instantiate_and_normalise eq_rec
                      else Formula.R.instantiate_and_normalise_one_variable_constructor x r eq_rec
                    in
                    if eq_rec' = Formula.R.Bot
                    then f_next_1 ()
                    else apply_rules df' eq_term eq_rec' eq_uni exist_vars f_next_1
                | Name _ ->
                    K.find_unifier_with_recipe csys.simp_knowledge_recipe csys.simp_knowledge t x.type_r (fun is_identity r f_next_2 ->
                      Config.debug (fun () ->
                        if not is_identity
                        then Config.internal_error "[Constraint_system.ml >> MGS.compute_all] Finding a unifier with a name implies identity."
                      );

                      (* We do not need to auto_clean the recipe variable cause this is the last
                      case that will be applied. Hence, the cleanup will be handled by f_next_2 which
                      will call f_next_1. *)
                      Recipe_Variable.link_recipe x r;
                      let eq_rec' =
                        if unif
                        then Formula.R.instantiate_and_normalise eq_rec
                        else Formula.R.instantiate_and_normalise_one_variable x r eq_rec
                      in
                      if eq_rec' = Formula.R.Bot
                      then f_next_2 ()
                      else apply_rules df' eq_term eq_rec' eq_uni exist_vars f_next_2
                    ) f_next_1
                | Func(f,args) ->
                    (* Compute_all is only used for the rule [sat],
                       in which case incremented knowledge is empty. *)
                    let acc_eq_uni = ref eq_uni in
                    let found_identity = ref false in


                    K.find_unifier_with_recipe csys.simp_knowledge_recipe csys.simp_knowledge t x.type_r (fun is_identity r f_next_2 ->
                      if is_identity
                      then
                        begin
                          found_identity := true;
                          (* We do not need to auto_clean the recipe variable cause this is the last
                          case that will be applied. Hence, the cleanup will be handled by f_next_2 which
                          will call f_next_1. *)
                          Recipe_Variable.link_recipe x r;
                          let eq_rec' =
                            if unif
                            then Formula.R.instantiate_and_normalise eq_rec
                            else Formula.R.instantiate_and_normalise_one_variable x r eq_rec
                          in
                          if eq_rec' = Formula.R.Bot
                          then f_next_2 ()
                          else apply_rules df' eq_term eq_rec' eq_uni exist_vars f_next_2
                        end
                      else
                        let eq_term' = Formula.T.instantiate_and_normalise eq_term in
                        if eq_term' = Formula.T.Bot
                        then f_next_2 ()
                        else
                          let eq_uni' = Formula.T.instantiate_and_normalise eq_uni in
                          if eq_uni' = Formula.T.Bot
                          then f_next_2 ()
                          else
                            begin
                              let diseq = Diseq.T.of_linked_variables !Variable.currently_linked in
                              acc_eq_uni := Formula.T.wedge diseq !acc_eq_uni;

                              Recipe_Variable.auto_cleanup_with_reset (fun f_next_3 ->
                                Recipe_Variable.link_recipe x r;
                                let eq_rec' =
                                  if unif
                                  then Formula.R.instantiate_and_normalise eq_rec
                                  else Formula.R.instantiate_and_normalise_one_variable x r eq_rec
                                in
                                Config.debug (fun () -> if x.link_r = RNoLink then Config.internal_error "[MGS.compute_all] Variable should be linked.");
                                if eq_rec' = Formula.R.Bot
                                then f_next_3 ()
                                else apply_rules df' eq_term' eq_rec' eq_uni' exist_vars f_next_3
                              ) f_next_2
                            end
                    ) (fun () ->
                      if !found_identity || not f.public
                      then f_next_1 ()
                      else
                        begin
                          let fresh_vars = Recipe_Variable.fresh_list Existential x.type_r f.arity in
                          let exists_vars' = List.rev_append fresh_vars exist_vars in
                          let r = RFunc(f,List.map (fun y -> RVar y) fresh_vars) in

                          (* No need to auto cleanup the recipe variables as it will be done by f_next_1 *)
                          Recipe_Variable.link_recipe x r;

                          let eq_rec' =
                            if unif
                            then Formula.R.instantiate_and_normalise eq_rec
                            else Formula.R.instantiate_and_normalise_one_variable_constructor x r eq_rec
                          in
                          if eq_rec' = Formula.R.Bot
                          then f_next_1 ()
                          else
                            begin
                              let ded_fact_list = List.map2 (fun x' t' -> { bf_var = x'; bf_term = t' }) fresh_vars args in
                              let df'' = DF.add_multiple df' ded_fact_list in
                              apply_rules df'' eq_term eq_rec' !acc_eq_uni exists_vars' f_next_1
                            end
                        end
                    )
                | _ -> Config.internal_error "[constraint_system.ml >> MGS.compute_all] Cannot be a variable."
      ) f_next_0
    in

    apply_rules csys.simp_deduction_facts csys.simp_eq_term csys.simp_eq_recipe csys.simp_eq_uniformity [] f_next

  type one_mgs_data =
    {
      one_mgs_std_subst : (recipe_variable * recipe) list;
      one_mgs_infinite_subst : (recipe_variable * recipe) list;
      one_mgs_fresh_existential_vars : recipe_variable list;
      one_mgs_fresh_existential_infinite_vars : recipe_variable list;
      one_mgs_eq_recipe : Formula.R.t
    }

  type deduction_facts_vars =
    {
      std_vars : recipe_variable list option ref;
      infinite_vars : recipe_variable list
    }

  let compute_one csys df_vars =
    let mgs_found = ref false in
    let result_mgs = ref None in

    let std_vars = match !(df_vars.std_vars) with
      | None ->
          let vars = DF.get_standard_recipe_variables csys.simp_deduction_facts in
          df_vars.std_vars := Some vars;
          vars
      | Some vlist -> vlist
    in

    let generate_result eq_recipe exist_vars =
      let subst_std = List.fold_left (fun acc v -> match v.link_r with RLink r -> (v,Recipe.instantiate_preserve_context r)::acc | _ -> acc) [] std_vars in
      let subst_infinite = List.fold_left (fun acc v -> match v.link_r with RLink r -> (v,Recipe.instantiate_preserve_context r)::acc | _ -> acc) [] df_vars.infinite_vars in
      let (exists_vars_std, exists_vars_infinite) =
        List.fold_left (fun (acc_std,acc_infinite) v -> match v.link_r with
          | RNoLink ->
              if v.type_r = Recipe_Variable.infinite_type
              then (acc_std, v::acc_infinite)
              else (v::acc_std,acc_infinite)
          | _ -> (acc_std,acc_infinite)
        ) ([],[]) exist_vars
      in
      mgs_found := true;
      result_mgs :=
        Some
          {
            one_mgs_std_subst = subst_std;
            one_mgs_infinite_subst = subst_infinite;
            one_mgs_fresh_existential_vars = exists_vars_std;
            one_mgs_fresh_existential_infinite_vars = exists_vars_infinite;
            one_mgs_eq_recipe = eq_recipe
          }
    in

    let rec apply_rules df eq_term eq_rec eq_uni exist_vars f_next_0 =
      Recipe_Variable.auto_cleanup_with_reset (fun f_next_1 ->
        match DF.compute_mgs_applicability df with
          | DF.Solved ->
              generate_result eq_rec exist_vars;
              f_next_1 ()
          | DF.UnifyVariables _ ->
              let eq_rec' = Formula.R.instantiate_and_normalise eq_rec in
              if eq_rec' = Formula.R.Bot
              then f_next_1 ()
              else
                begin
                  generate_result eq_rec' exist_vars;
                  f_next_1 ()
                end
          | DF.UnsolvedFact(bfact,df',unif) ->
              let x = bfact.bf_var
              and t = bfact.bf_term in

              match t with
                | Func(f,[]) when f.public ->
                    let r = RFunc(f,[]) in
                    Recipe_Variable.link_recipe x r;
                    let eq_rec' =
                      if unif
                      then Formula.R.instantiate_and_normalise eq_rec
                      else Formula.R.instantiate_and_normalise_one_variable_constructor x r eq_rec
                    in
                    if eq_rec' = Formula.R.Bot
                    then f_next_1 ()
                    else apply_rules df' eq_term eq_rec' eq_uni exist_vars f_next_1
                | Name _ ->
                    K.find_unifier_with_recipe_with_stop csys.simp_knowledge_recipe csys.simp_knowledge t x.type_r mgs_found (fun is_identity r f_next_2 ->
                      Config.debug (fun () ->
                        if not is_identity
                        then Config.internal_error "[Constraint_system.ml >> MGS.compute_one] Finding a unifier with a name implies identity."
                      );

                      (* We do not need to auto_clean the recipe variable cause this is the last
                      case that will be applied. Hence, the cleanup will be handled by f_next_2 which
                      will call f_next_1. *)
                      Recipe_Variable.link_recipe x r;
                      let eq_rec' =
                        if unif
                        then Formula.R.instantiate_and_normalise eq_rec
                        else Formula.R.instantiate_and_normalise_one_variable x r eq_rec
                      in
                      if eq_rec' = Formula.R.Bot
                      then f_next_2 ()
                      else apply_rules df' eq_term eq_rec' eq_uni exist_vars f_next_2
                    ) f_next_1
                | Func(f,args) ->
                    (* Compute_all is only used for the rule [sat],
                       in which case incremented knowledge is empty. *)
                    let acc_eq_uni = ref eq_uni in
                    let found_identity = ref false in

                    K.find_unifier_with_recipe_with_stop csys.simp_knowledge_recipe csys.simp_knowledge t x.type_r mgs_found (fun is_identity r f_next_2 ->
                      if is_identity
                      then
                        begin
                          found_identity := true;
                          (* We do not need to auto_clean the recipe variable cause this is the last
                          case that will be applied. Hence, the cleanup will be handled by f_next_2 which
                          will call f_next_1. *)
                          Recipe_Variable.link_recipe x r;
                          let eq_rec' =
                            if unif
                            then Formula.R.instantiate_and_normalise eq_rec
                            else Formula.R.instantiate_and_normalise_one_variable x r eq_rec
                          in
                          if eq_rec' = Formula.R.Bot
                          then f_next_2 ()
                          else apply_rules df' eq_term eq_rec' eq_uni exist_vars f_next_2
                        end
                      else
                        let eq_term' = Formula.T.instantiate_and_normalise eq_term in
                        if eq_term' = Formula.T.Bot
                        then f_next_2 ()
                        else
                          let eq_uni' = Formula.T.instantiate_and_normalise eq_uni in
                          if eq_uni' = Formula.T.Bot
                          then f_next_2 ()
                          else
                            begin
                              let diseq = Diseq.T.of_linked_variables !Variable.currently_linked in
                              acc_eq_uni := Formula.T.wedge diseq !acc_eq_uni;
                              Recipe_Variable.auto_cleanup_with_reset (fun f_next_3 ->
                                Recipe_Variable.link_recipe x r;
                                let eq_rec' =
                                  if unif
                                  then Formula.R.instantiate_and_normalise eq_rec
                                  else Formula.R.instantiate_and_normalise_one_variable x r eq_rec
                                in
                                if eq_rec' = Formula.R.Bot
                                then f_next_3 ()
                                else apply_rules df' eq_term' eq_rec' eq_uni' exist_vars f_next_3
                              ) f_next_2
                            end
                    ) (fun () ->
                      if !mgs_found || !found_identity || not f.public
                      then f_next_1 ()
                      else
                        begin
                          let fresh_vars = Recipe_Variable.fresh_list Existential x.type_r f.arity in
                          let exists_vars' = List.rev_append fresh_vars exist_vars in
                          let r = RFunc(f,List.map (fun y -> RVar y) fresh_vars) in

                          (* No need to auto cleanup the recipe variables as it will be done by f_next_1 *)
                          Recipe_Variable.link_recipe x r;
                          let eq_rec' =
                            if unif
                            then Formula.R.instantiate_and_normalise eq_rec
                            else Formula.R.instantiate_and_normalise_one_variable_constructor x r eq_rec
                          in
                          if eq_rec' = Formula.R.Bot
                          then f_next_1 ()
                          else
                            let ded_fact_list = List.map2 (fun x' t' -> { bf_var = x'; bf_term = t' }) fresh_vars args in
                            let df'' = DF.add_multiple df' ded_fact_list in
                            apply_rules df'' eq_term eq_rec' !acc_eq_uni exists_vars' f_next_1
                        end
                    )
                | _ -> Config.internal_error "[constraint_system.ml >> MGS.compute_one] Cannot be a variable."
      ) f_next_0
    in

    apply_rules csys.simp_deduction_facts csys.simp_eq_term csys.simp_eq_recipe csys.simp_eq_uniformity [] (fun () -> ());

    !result_mgs

  (* Invariant : Variables with the same type as the last axiom does not occur
     in sim_eq_recipe. *)
  let compute_one_with_IK csys infinite_basic_facts df_vars =
    let mgs_found = ref false in
    let result_mgs = ref None in

    let std_vars = match !(df_vars.std_vars) with
      | None ->
          let vars = DF.get_standard_recipe_variables csys.simp_deduction_facts in
          df_vars.std_vars := Some vars;
          vars
      | Some vlist -> vlist
    in

    let df = DF.add_multiple_max_type csys.simp_deduction_facts infinite_basic_facts in

    Config.debug (fun () ->
      if List.exists (fun bfact -> bfact.bf_var.link_r <> RNoLink) infinite_basic_facts
      then Config.internal_error "[constraint_system.ml >> MGS.compute_one_with_IK] Variables in infinite basic facts should not be linked.";

      DF.debug "[constraint_system.ml >> MGS.compute_one_with_IK]" df;
    );

    let generate_result eq_recipe exist_vars =
      let subst_std = List.fold_left (fun acc v -> match v.link_r with RLink r -> (v,Recipe.instantiate_preserve_context r)::acc | _ -> acc) [] std_vars in
      let subst_infinite = List.fold_left (fun acc v -> match v.link_r with RLink r -> (v,Recipe.instantiate_preserve_context r)::acc | _ -> acc) [] df_vars.infinite_vars in
      let (exists_vars_std, exists_vars_infinite) =
        List.fold_left (fun (acc_std,acc_infinite) v -> match v.link_r with
          | RNoLink ->
              if v.type_r = Recipe_Variable.infinite_type
              then (acc_std, v::acc_infinite)
              else (v::acc_std,acc_infinite)
          | _ -> (acc_std,acc_infinite)
        ) ([],[]) exist_vars
      in
      mgs_found := true;
      result_mgs :=
        Some
          {
            one_mgs_std_subst = subst_std;
            one_mgs_infinite_subst = subst_infinite;
            one_mgs_fresh_existential_vars = exists_vars_std;
            one_mgs_fresh_existential_infinite_vars = exists_vars_infinite;
            one_mgs_eq_recipe = eq_recipe
          }
    in

    let size_kb = KR.size csys.simp_knowledge_recipe in

    let rec apply_rules df eq_term eq_rec eq_uni eq_skel exist_vars f_next_0 =
      Config.debug (fun () -> DF.debug "[constraint_system.ml >> MGS.compute_one_with_IK]" df);
      Recipe_Variable.auto_cleanup_with_reset (fun f_next_1 ->
        match DF.compute_mgs_applicability df with
          | DF.Solved ->
              generate_result eq_rec exist_vars;
              f_next_1 ()
          | DF.UnifyVariables _ ->
              let eq_rec' = Formula.R.instantiate_and_normalise eq_rec in
              if eq_rec' = Formula.R.Bot
              then f_next_1 ()
              else
                let eq_skel' = Formula.M.instantiate_and_normalise eq_skel in
                if eq_skel' = Formula.M.Bot
                then f_next_1 ()
                else
                  begin
                    generate_result eq_rec' exist_vars;
                    f_next_1 ()
                  end
          | DF.UnsolvedFact(bfact,df',unif) ->
              let x = bfact.bf_var
              and t = bfact.bf_term in

              Config.debug (fun () ->
                if x.link_r <> RNoLink
                then Config.internal_error "[constraint_system.ml >> compute_one_with_IK] Variable should not be linked."
              );

              match t with
                | Func(f,[]) when f.public ->
                    let r = RFunc(f,[]) in
                    Recipe_Variable.link_recipe x r;
                    let eq_rec' =
                      if unif
                      then Formula.R.instantiate_and_normalise eq_rec
                      else
                        if x.type_r = Recipe_Variable.infinite_type
                        then eq_rec
                        else Formula.R.instantiate_and_normalise_one_variable_constructor x r eq_rec
                    in
                    if eq_rec' = Formula.R.Bot
                    then f_next_1 ()
                    else
                      let eq_skel' =
                        if unif
                        then Formula.M.instantiate_and_normalise eq_skel
                        else Formula.M.instantiate_and_normalise_one_variable_constructor x r eq_skel
                      in
                      if eq_skel' = Formula.M.Bot
                      then f_next_1 ()
                      else apply_rules df' eq_term eq_rec' eq_uni eq_skel' exist_vars f_next_1
                | Name _ ->
                    IK.find_unifier_with_recipe_with_stop csys.simp_knowledge_recipe csys.simp_knowledge csys.simp_incremented_knowledge t x.type_r mgs_found (fun is_identity r f_next_2 ->
                      Config.debug (fun () ->
                        if not is_identity
                        then Config.internal_error "[Constraint_system.ml >> MGS.compute_one_with_IK] Finding a unifier with a name implies identity."
                      );

                      (* We do not need to auto_clean the recipe variable cause this is the last
                      case that will be applied. Hence, the cleanup will be handled by f_next_2 which
                      will call f_next_1. *)
                      Recipe_Variable.link_recipe x r;
                      let eq_rec' =
                        if unif
                        then Formula.R.instantiate_and_normalise eq_rec
                        else
                          if x.type_r = Recipe_Variable.infinite_type
                          then eq_rec
                          else Formula.R.instantiate_and_normalise_one_variable x r eq_rec
                      in
                      if eq_rec' = Formula.R.Bot
                      then f_next_2 ()
                      else
                        let eq_skel' =
                          if unif
                          then Formula.M.instantiate_and_normalise eq_skel
                          else Formula.M.instantiate_and_normalise_one_variable x r eq_skel
                        in
                        if eq_skel' = Formula.M.Bot
                        then f_next_2 ()
                        else apply_rules df' eq_term eq_rec' eq_uni eq_skel' exist_vars f_next_2
                    ) f_next_1
                | Func(f,args) ->
                    (* Compute_all is only used for the rule [sat],
                       in which case incremented knowledge is empty. *)
                    let acc_eq_uni = ref eq_uni in
                    let found_identity = ref false in

                    IK.find_unifier_with_recipe_with_stop csys.simp_knowledge_recipe csys.simp_knowledge csys.simp_incremented_knowledge t x.type_r mgs_found (fun is_identity r f_next_2 ->
                      if is_identity
                      then
                        begin
                          found_identity := true;
                          (* We do not need to auto_clean the recipe variable cause this is the last
                          case that will be applied. Hence, the cleanup will be handled by f_next_2 which
                          will call f_next_1. *)
                          Recipe_Variable.link_recipe x r;
                          let eq_rec' =
                            if unif
                            then Formula.R.instantiate_and_normalise eq_rec
                            else
                              if x.type_r = Recipe_Variable.infinite_type
                              then eq_rec
                              else Formula.R.instantiate_and_normalise_one_variable x r eq_rec
                          in
                          if eq_rec' = Formula.R.Bot
                          then f_next_2 ()
                          else
                            let eq_skel' =
                              if unif
                              then Formula.M.instantiate_and_normalise eq_skel
                              else Formula.M.instantiate_and_normalise_one_variable x r eq_skel
                            in
                            if eq_skel' = Formula.M.Bot
                            then f_next_2 ()
                            else apply_rules df' eq_term eq_rec' eq_uni eq_skel' exist_vars f_next_2
                        end
                      else
                        let eq_term' = Formula.T.instantiate_and_normalise eq_term in
                        if eq_term' = Formula.T.Bot
                        then f_next_2 ()
                        else
                          let eq_uni' = Formula.T.instantiate_and_normalise eq_uni in
                          if eq_uni' = Formula.T.Bot
                          then f_next_2 ()
                          else
                            begin
                              begin match r with
                                | CRFunc(i,_) when i < size_kb ->
                                    let diseq = Diseq.T.of_linked_variables !Variable.currently_linked in
                                    acc_eq_uni := Formula.T.wedge diseq !acc_eq_uni;
                                | _ -> ()
                              end;

                              Recipe_Variable.auto_cleanup_with_reset (fun f_next_3 ->
                                Recipe_Variable.link_recipe x r;
                                let eq_rec' =
                                  if unif
                                  then Formula.R.instantiate_and_normalise eq_rec
                                  else
                                    if x.type_r = Recipe_Variable.infinite_type
                                    then eq_rec
                                    else Formula.R.instantiate_and_normalise_one_variable x r eq_rec
                                in
                                if eq_rec' = Formula.R.Bot
                                then f_next_3 ()
                                else
                                  let eq_skel' =
                                    if unif
                                    then Formula.M.instantiate_and_normalise eq_skel
                                    else Formula.M.instantiate_and_normalise_one_variable x r eq_skel
                                  in
                                  if eq_skel' = Formula.M.Bot
                                  then f_next_3 ()
                                  else apply_rules df' eq_term' eq_rec' eq_uni' eq_skel' exist_vars f_next_3
                              ) f_next_2
                            end
                    ) (fun () ->
                      if !mgs_found || !found_identity || not f.public
                      then f_next_1 ()
                      else
                        begin
                          let fresh_vars = Recipe_Variable.fresh_list Existential x.type_r f.arity in
                          let exists_vars' = List.rev_append fresh_vars exist_vars in
                          let r = RFunc(f,List.map (fun y -> RVar y) fresh_vars) in

                          (* No need to auto cleanup the recipe variables as it will be done by f_next_1 *)
                          Recipe_Variable.link_recipe x r;
                          let eq_rec' =
                            if unif
                            then Formula.R.instantiate_and_normalise eq_rec
                            else
                              if x.type_r = Recipe_Variable.infinite_type
                              then eq_rec
                              else Formula.R.instantiate_and_normalise_one_variable_constructor x r eq_rec
                          in
                          if eq_rec' = Formula.R.Bot
                          then f_next_1 ()
                          else
                            let eq_skel' =
                              if unif
                              then Formula.M.instantiate_and_normalise eq_skel
                              else Formula.M.instantiate_and_normalise_one_variable_constructor x r eq_skel
                            in
                            if eq_skel' = Formula.M.Bot
                            then f_next_1 ()
                            else
                              let ded_fact_list = List.map2 (fun x' t' -> { bf_var = x'; bf_term = t' }) fresh_vars args in
                              let df'' = DF.add_multiple df' ded_fact_list in
                              apply_rules df'' eq_term eq_rec' !acc_eq_uni eq_skel' exists_vars' f_next_1
                        end
                    )
                | _ -> Config.internal_error "[constraint_system.ml >> MGS.compute_one_with_IK] Cannot be a variable."
      ) f_next_0
    in

    apply_rules df csys.simp_eq_term csys.simp_eq_recipe csys.simp_eq_uniformity csys.simp_eq_skeleton [] (fun () -> ());

    !result_mgs
  (**** Application of MGS ****)

  let apply_mgs_on_same_csys csys mgs_data =
    { csys with
      deduction_facts = mgs_data.mgs_deduction_facts;
      eq_term = mgs_data.mgs_eq_term;
      eq_uniformity = mgs_data.mgs_eq_uniformity;
      rule_data = { csys.rule_data with normalisation_deduction_checked = false }
    }

  let apply_mgs_on_different_csys csys kbr mgs_fresh_vars =
    Config.debug (fun () ->
      if List.exists (function { link_r = l; _} when l <> RNoLink -> true | _ -> false) mgs_fresh_vars
      then Config.internal_error "[constraint_system.ml >> MGS.apply_mgs_on_different_csys] Variables should not be linked."
    );

    let (new_df_1,removed_bfacts,remain_rec_vars) = DF.remove_linked_variables csys.deduction_facts in

    let remain_rec_vars_ref = ref remain_rec_vars in
    let var_and_term_fresh = ref [] in

    (* Linking the new variables *)
    List.iter (fun x ->
      let t = Var(Variable.fresh Existential) in
      x.link_r <- RXLink t;
      remain_rec_vars_ref := x :: !remain_rec_vars_ref;
      var_and_term_fresh := (x,t)::!var_and_term_fresh;
    ) mgs_fresh_vars;

    let equation_op =
      try
        Some (List.fold_left (fun (acc_eq,eq_uni) bfact -> match bfact.bf_var.link_r with
          | RLink r ->
              let (eq_uni',t,_) = K.consequence_uniform_recipe kbr csys.knowledge eq_uni r in
              (bfact.bf_term,t)::acc_eq , eq_uni'
          | _ -> Config.internal_error "[constraint_system.ml >> MGS.apply_mgs_on_different_csys] The variables should be linked with a recipe."
        ) ([],csys.eq_uniformity) removed_bfacts)
      with K.Uniformity_falsified -> None
    in

    List.iter (fun v -> v.link_r <- RNoLink) !remain_rec_vars_ref;

    match equation_op with
      | None -> None
      | Some(equations,new_eq_uniformity_1) ->

          let is_unifiable =
            try
              List.iter (fun (t1,t2) -> Term.unify t1 t2) equations;
              true
            with Term.Not_unifiable -> false
          in
          if is_unifiable
          then
            let new_eq_term_1 = Formula.T.instantiate_and_normalise_full csys.eq_term in
            if new_eq_term_1 = Formula.T.Bot
            then None
            else
              let new_eq_uniformity_2 = Formula.T.instantiate_and_normalise_full new_eq_uniformity_1 in
              if new_eq_uniformity_2 = Formula.T.Bot
              then None
              else
                let new_df_2 =
                  List.fold_left (fun df (x,t) ->
                    let bfact = { bf_var = x; bf_term = t } in
                    DF.add df bfact
                  ) new_df_1 !var_and_term_fresh
                in

                let new_csys =
                  { csys with
                    deduction_facts = new_df_2;
                    eq_term = new_eq_term_1;
                    eq_uniformity = new_eq_uniformity_2;
                    rule_data = { csys.rule_data with normalisation_deduction_checked = false }
                  }
                in
                Some new_csys
          else None

  let rec get_linked_variable = function
    | Var { link = TLink t; _} -> get_linked_variable t
    | Var x -> x
    | _ -> Config.internal_error "[constraint_system.ml >> MGS.get_linked_variable] The term should be a variable."

  let apply_mgs_on_different_solved_csys csys kbr mgs_fresh_vars =
    Config.debug (fun () ->
      if List.exists (function { link_r = l; _} when l <> RNoLink -> true | _ -> false) mgs_fresh_vars
      then Config.internal_error "[constraint_system.ml >> MGS.apply_mgs_on_different_solved_csys] Variables should not be linked."
    );

    let (new_df_1,removed_bfacts,remain_rec_vars) = DF.remove_linked_variables csys.deduction_facts in

    let remain_rec_vars_ref = ref remain_rec_vars in
    let var_and_term_fresh = ref [] in

    (* Linking the new variables *)
    List.iter (fun x ->
      let t = Var(Variable.fresh Existential) in
      x.link_r <- RXLink t;
      remain_rec_vars_ref := x :: !remain_rec_vars_ref;
      var_and_term_fresh := (x,t)::!var_and_term_fresh;
    ) mgs_fresh_vars;

    let equation_op =
      try
        Some (List.fold_left (fun (acc_eq,eq_uni) bfact -> match bfact.bf_var.link_r with
          | RLink r ->
              let (eq_uni',t,_) = K.consequence_uniform_recipe kbr csys.knowledge eq_uni r in
              let x_bfact = get_linked_variable bfact.bf_term in
              (x_bfact,t)::acc_eq , eq_uni'
          | _ -> Config.internal_error "[constraint_system.ml >> MGS.apply_mgs_on_different_solved_csys] The variables should be linked with a recipe."
        ) ([],csys.eq_uniformity) removed_bfacts)
      with K.Uniformity_falsified -> None
    in

    List.iter (fun v -> v.link_r <- RNoLink) !remain_rec_vars_ref;

    match equation_op with
      | None -> None
      | Some(equations,new_eq_uniformity_1) ->
          List.iter (fun (x,t) -> Variable.link_term x t) equations;

          let new_eq_term_1 = Formula.T.instantiate_and_normalise_full csys.eq_term in
          if new_eq_term_1 = Formula.T.Bot
          then None
          else
            let new_eq_uniformity_2 = Formula.T.instantiate_and_normalise_full new_eq_uniformity_1 in
            if new_eq_uniformity_2 = Formula.T.Bot
            then None
            else
              let new_df_2 =
                List.fold_left (fun df (x,t) ->
                  let bfact = { bf_var = x; bf_term = t } in
                  DF.add df bfact
                ) new_df_1 !var_and_term_fresh
              in
              let new_csys =
                { csys with
                  deduction_facts = new_df_2;
                  eq_term = new_eq_term_1;
                  eq_uniformity = new_eq_uniformity_2;
                  rule_data = { csys.rule_data with normalisation_deduction_checked = false }
                }
              in
              Some new_csys
end

(****************************************
***               Set                 ***
*****************************************)

module Set = struct

  (** The type of set of constraint systems. *)

  let empty = { eq_recipe = Formula.R.Top; set = []; knowledge_recipe = KR.empty }

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
    explore csys_set.set

  let debug_check_structure str set =
    if List.exists (fun csys -> K.size csys.knowledge <> KR.size set.knowledge_recipe) set.set
    then Config.internal_error (str^" KBR structure incorrect");

    List.iter (fun csys1 ->
      List.iter (fun csys2 ->
        DF.debug_same_structure str csys1.deduction_facts csys2.deduction_facts
      ) set.set
    ) set.set
end

(****************************************
***              Rules                ***
*****************************************)

module Rule = struct

  (*** Record function ***)

  let record =
    if Config.record_time
    then
      (fun stat (f_continuation:('a set -> (unit -> unit) -> unit)) (set:'a set) -> Statistic.record_tail stat (f_continuation set))
    else (fun _ f_continuation -> f_continuation)

  (**** The rule Sat ****)

  let rec exploration_sat prev_set = function
    | [] -> None, prev_set
    | csys::q when DF.is_solved csys.deduction_facts -> exploration_sat (csys::prev_set) q
    | csys::q -> Some (csys,q), prev_set

  let debug_sat_index = ref 0

  let sat f_continuation csys_set f_next =
    Config.debug (fun () ->
      incr debug_sat_index;
      Config.log_in_debug Config.Constraint_solving (Printf.sprintf "[constraint_system.ml >> Rule] Rule Sat (%d): Nb csys = %d" !debug_sat_index (List.length csys_set.set));
      Set.debug_check_structure "[Sat]" csys_set;
      List.iter (fun csys ->
        debug_on_constraint_system "[Rule Sat]" ~solved:false csys;
        if not (Formula.T.debug_no_linked_variables csys.eq_term)
        then Config.internal_error "[constraint_system.ml >> sat] Variables in eq_term should not be linked.";
        if not (Formula.T.debug_no_linked_variables csys.eq_uniformity)
        then Config.internal_error "[constraint_system.ml >> sat] Variables in eq_uniformity should not be linked.";
        Config.log_in_debug Config.Constraint_systems ("Eq recipe = "^(Formula.R.display Terminal csys_set.eq_recipe));
        Config.log_in_debug Config.Constraint_systems (display_constraint_system 1 csys_set.knowledge_recipe csys)
      ) csys_set.set
    );

    let rec internal checked_csys to_check_csys eq_rec vars_df_op f_next_1 = match exploration_sat checked_csys to_check_csys with
      | None, checked_csys_1 -> f_continuation { csys_set with set = checked_csys_1; eq_recipe = eq_rec } f_next_1
      | Some(csys,to_check_csys_1), checked_csys_1 ->
          let simple_csys = MGS.simple_of csys csys_set.knowledge_recipe eq_rec in

          let accu_neg_eq_recipe = ref [] in
          let vars_df = match vars_df_op with
            | None -> DF.get_recipe_variables csys.deduction_facts
            | Some vlist -> vlist
          in

          Config.debug (fun () ->
            debug_on_constraint_system "[Rule Sat >> internal >> Found unsolved csys]" ~solved:false csys;
            List.iter (fun csys' -> debug_on_constraint_system "[Rule Sat >> internal >> Found unsolved csys]" ~solved:false csys') checked_csys_1;
            List.iter (fun csys' -> debug_on_constraint_system "[Rule Sat >> internal >> Found unsolved csys]" ~solved:false csys') to_check_csys_1;
          );

          MGS.compute_all simple_csys (fun mgs_data f_next_2 ->
            Variable.auto_cleanup_with_reset (fun f_next_3 ->
              let diseq_rec = Diseq.R.of_maybe_linked_variables vars_df mgs_data.MGS.mgs_fresh_existential_vars in
              accu_neg_eq_recipe := diseq_rec :: !accu_neg_eq_recipe;

              let new_csys = MGS.apply_mgs_on_same_csys csys mgs_data in

              let new_checked_csys =
                List.fold_left (fun set csys -> match MGS.apply_mgs_on_different_solved_csys csys csys_set.knowledge_recipe mgs_data.MGS.mgs_fresh_existential_vars with
                  | None -> set
                  | Some csys' -> csys' :: set
                ) [new_csys] checked_csys_1
              in
              let new_to_check_csys =
                List.fold_left (fun set csys -> match MGS.apply_mgs_on_different_csys csys csys_set.knowledge_recipe mgs_data.MGS.mgs_fresh_existential_vars with
                  | None -> set
                  | Some csys' -> csys' :: set
                ) [] to_check_csys_1
              in

              internal new_checked_csys new_to_check_csys mgs_data.MGS.mgs_eq_recipe None f_next_3
            ) f_next_2
          ) (fun () ->
            Config.debug (fun () ->
              List.iter (fun csys' -> debug_on_constraint_system "[Rule Sat >> internal >> After compute all >> Negation Checked]" ~solved:false csys') checked_csys_1;
              List.iter (fun csys' -> debug_on_constraint_system "[Rule Sat >> internal >> After compute all >> Negation To Check]" ~solved:false csys') to_check_csys_1
            );
            if !accu_neg_eq_recipe = []
            then internal checked_csys_1 to_check_csys_1 eq_rec (Some vars_df) f_next_1 (* Implies that no MGS was found. *)
            else
              let eq_rec' = Formula.R.wedge_conjunction !accu_neg_eq_recipe eq_rec in
              internal checked_csys_1 to_check_csys_1 eq_rec' (Some vars_df) f_next_1
          )
    in

    internal [] csys_set.set csys_set.eq_recipe None f_next

  (**** The rule Sat for disequation ****)

  let rec exploration_sat_disequation prev_set = function
    | [] -> None, prev_set
    | csys::q when Formula.T.Top = csys.eq_term -> exploration_sat_disequation (csys::prev_set) q
    | csys::q ->
        let (diseq, eq_term) = Formula.T.extract_one_diseq csys.eq_term in
        let new_csys = { csys with eq_term = eq_term } in
        Some(new_csys,diseq,q), prev_set

  let sat_disequation f_continuation csys_set f_next =
    Config.debug (fun () ->
      Config.log_in_debug Config.Constraint_solving (Printf.sprintf "[constraint_system.ml >> Rule] Rule Sat disequation (%d): Nb csys = %d" !debug_sat_index (List.length csys_set.set));
      Set.debug_check_structure "[Sat disequation]" csys_set;
      List.iter (debug_on_constraint_system ~solved:true "[sat_disequation]") csys_set.set;
      List.iter (fun csys ->
        if not (Formula.T.debug_no_linked_variables csys.eq_term)
        then Config.internal_error "[constraint_system.ml >> sat_disequation] Variables in eq_term should not be linked.";
        if not (Formula.T.debug_no_linked_variables csys.eq_uniformity)
        then Config.internal_error "[constraint_system.ml >> sat_disequation] Variables in eq_uniformity should not be linked."
      ) csys_set.set
    );
    let rec internal checked_csys to_check_csys eq_rec vars_df_op f_next_1 = match exploration_sat_disequation checked_csys to_check_csys with
      | None, checked_csys_1 -> f_continuation { csys_set with set = checked_csys_1; eq_recipe = eq_rec } f_next_1
      | Some(new_csys,diseq,to_check_csys_1), checked_csys_1 ->
          let accu_neg_eq_recipe = ref [] in
          let vars_df_op_ref = ref vars_df_op in

          Variable.auto_cleanup_with_reset (fun f_next_2 -> match MGS.simple_of_disequation new_csys csys_set.knowledge_recipe eq_rec diseq with
            | None -> f_next_2 ()
            | Some simple_csys ->
                MGS.compute_all simple_csys (fun mgs_data f_next_3 ->
                  Variable.auto_cleanup_with_reset (fun f_next_4 ->
                    let vars_df = match !vars_df_op_ref with
                      | None ->
                          let vlist = DF.get_recipe_variables new_csys.deduction_facts in
                          vars_df_op_ref := Some vlist;
                          vlist
                      | Some vlist -> vlist
                    in
                    let diseq_rec = Diseq.R.of_maybe_linked_variables vars_df mgs_data.MGS.mgs_fresh_existential_vars in
                    accu_neg_eq_recipe := diseq_rec :: !accu_neg_eq_recipe;

                    let new_checked_csys =
                      List.fold_left (fun set csys -> match MGS.apply_mgs_on_different_solved_csys csys csys_set.knowledge_recipe mgs_data.MGS.mgs_fresh_existential_vars with
                        | None -> set
                        | Some csys' -> csys' :: set
                      ) [] checked_csys_1
                    in
                    let new_to_check_csys =
                      List.fold_left (fun set csys -> match MGS.apply_mgs_on_different_solved_csys csys csys_set.knowledge_recipe mgs_data.MGS.mgs_fresh_existential_vars with
                        | None -> set
                        | Some csys' -> csys' :: set
                      ) [] to_check_csys_1
                    in
                    internal new_checked_csys new_to_check_csys mgs_data.MGS.mgs_eq_recipe None f_next_4
                  ) f_next_3
                ) f_next_2
          ) (fun () ->
            if !accu_neg_eq_recipe = []
            then internal checked_csys_1 (new_csys::to_check_csys_1) eq_rec !vars_df_op_ref f_next_1 (* No mgs found *)
            else
              let eq_rec' = Formula.R.wedge_conjunction !accu_neg_eq_recipe eq_rec in
              internal checked_csys_1 (new_csys::to_check_csys_1) eq_rec' !vars_df_op_ref f_next_1
          )
    in

    internal [] csys_set.set csys_set.eq_recipe None f_next

  (**** The rule Sat for private channels ****)

  let rec exploration_sat_non_deducible_terms kbr eq_recipe vars_df_ref prev_set = function
    | [] -> None, prev_set
    | ({ non_deducible_terms = []; _} as csys)::q -> exploration_sat_non_deducible_terms kbr eq_recipe vars_df_ref (csys::prev_set) q
    | ({ non_deducible_terms = t::q_t; _} as csys)::q ->
        let (simple_csys,x_infinite) = MGS.simple_of_non_deducible_term csys kbr eq_recipe t in
        let ded_fact_vars = { MGS.std_vars = vars_df_ref; MGS.infinite_vars = [x_infinite] } in
        match MGS.compute_one simple_csys ded_fact_vars with
          | None -> exploration_sat_non_deducible_terms kbr eq_recipe vars_df_ref prev_set ({ csys with non_deducible_terms = q_t }::q)
          | Some mgs_data -> Some(csys,mgs_data,q), prev_set

  let sat_non_deducible_terms f_continuation csys_set f_next =
    Config.debug (fun () ->
      Config.log_in_debug Config.Constraint_solving (Printf.sprintf "[constraint_system.ml >> Rule] Sat non deducible terms : Nb csys = %d" (List.length csys_set.set));
      Set.debug_check_structure "[Sat non_deducible_terms]" csys_set;
    );
    let rec internal checked_csys to_check_csys eq_rec vars_df_ref f_next_1 = match exploration_sat_non_deducible_terms csys_set.knowledge_recipe eq_rec vars_df_ref checked_csys to_check_csys with
      | None, checked_csys_1 -> f_continuation { csys_set with set = checked_csys_1; eq_recipe = eq_rec } f_next_1
      | Some(csys,mgs_data,to_check_csys_1), checked_csys_1 ->
          let new_eq_rec_ref = ref eq_rec in

          Recipe_Variable.auto_cleanup_with_reset (fun f_next_2 ->
            (* We link the variables of the mgs *)
            List.iter (fun (v,r) -> Recipe_Variable.link_recipe v r) mgs_data.MGS.one_mgs_std_subst;
            let vars_df = match !vars_df_ref with
              | Some vlist -> vlist
              | None -> Config.internal_error "[constraint_system.ml >> Rule.sat_non_deducible_terms] The variables of DF should have been computed during the computation of one_mgs."
            in

            new_eq_rec_ref := Formula.R.wedge (Diseq.R.of_maybe_linked_variables vars_df mgs_data.MGS.one_mgs_fresh_existential_vars) !new_eq_rec_ref;

            Variable.auto_cleanup_with_reset (fun f_next_3 ->
              let new_checked_csys =
                List.fold_left (fun set csys -> match MGS.apply_mgs_on_different_solved_csys csys csys_set.knowledge_recipe mgs_data.MGS.one_mgs_fresh_existential_vars with
                  | None -> set
                  | Some csys' -> csys' :: set
                ) [] checked_csys_1
              in
              let new_to_check_csys =
                List.fold_left (fun set csys -> match MGS.apply_mgs_on_different_solved_csys csys csys_set.knowledge_recipe mgs_data.MGS.one_mgs_fresh_existential_vars with
                  | None -> set
                  | Some csys' -> csys' :: set
                ) [] to_check_csys_1
              in
              internal new_checked_csys new_to_check_csys mgs_data.MGS.one_mgs_eq_recipe (ref None) f_next_3
            ) f_next_2
          ) (fun () -> internal checked_csys_1 (csys::to_check_csys_1) !new_eq_rec_ref vars_df_ref f_next_1)
    in

    internal [] csys_set.set csys_set.eq_recipe (ref None) f_next

  (**** The rule Sat for equality formula ****)

  type 'a csys_set_for_formula =
    {
      satf_knowledge_recipe : KR.t;
      satf_eq_recipe : Formula.R.t;
      satf_no_formula : 'a t list;
      satf_solved : 'a t list;
      satf_unsolved : 'a t list
    }

  let rec exploration_sat_equality_formula ?(universal=true) kbr eq_recipe (no_eq_csys:'a t list) (eq_fact_csys:'a t list) = function
    | [] -> None, no_eq_csys, eq_fact_csys
    | csys::q ->
        match UF.get_equality_formula_option csys.unsolved_facts with
          | None -> Config.internal_error "[constraint_system.ml >> Rule.exploration_sat_equality_formula] There should be an equality formula."
          | Some form ->
              match MGS.simple_of_equality_formula ~universal:universal csys kbr eq_recipe form with
                | MGS.SFNone ->
                    let csys' = { csys with unsolved_facts = UF.remove_unsolved_equality_formula csys.unsolved_facts } in
                    exploration_sat_equality_formula ~universal:universal kbr eq_recipe (csys'::no_eq_csys) eq_fact_csys q
                | MGS.SFSolved ->
                    let csys' = { csys with unsolved_facts = UF.remove_unsolved_equality_formula csys.unsolved_facts } in
                    exploration_sat_equality_formula ~universal:universal kbr eq_recipe no_eq_csys (csys'::eq_fact_csys) q
                | MGS.SFSome(subst,simple_csys) -> Some(csys,subst,simple_csys,q), no_eq_csys, eq_fact_csys

  let sat_equality_formula ?(universal=true) (f_continuation_pos:'a set -> (unit -> unit) -> unit) f_continuation_neg csys_set f_next =
    Config.debug (fun () ->
      Config.log_in_debug Config.Constraint_solving (Printf.sprintf "[constraint_system.ml >> Rule] Sat equality formula : Nb csys no_formula = %d, Nb csys solved = %d, Nb csys unsolved = %d"
        (List.length csys_set.satf_no_formula) (List.length csys_set.satf_solved) (List.length csys_set.satf_unsolved)
      );
      let csys_set = { set = csys_set.satf_no_formula @ csys_set.satf_solved @ csys_set.satf_unsolved; eq_recipe = csys_set.satf_eq_recipe; knowledge_recipe = csys_set.satf_knowledge_recipe } in
      List.iter (debug_on_constraint_system ~solved:true "[Sat equality_formula]") csys_set.set;
      Set.debug_check_structure "[Sat equality_formula]" csys_set
    );
    let rec internal no_eq_csys eq_fact_csys eq_form_csys eq_rec vars_df_ref f_next_1 = match exploration_sat_equality_formula ~universal:universal csys_set.satf_knowledge_recipe eq_rec no_eq_csys eq_fact_csys eq_form_csys with
      | None, no_eq_csys_1, eq_fact_csys_1 ->
          f_continuation_pos  {
            eq_recipe = eq_rec;
            set = eq_fact_csys_1;
            knowledge_recipe = csys_set.satf_knowledge_recipe
          } (fun () ->
            f_continuation_neg {
              eq_recipe = eq_rec;
              set = no_eq_csys_1;
              knowledge_recipe = csys_set.satf_knowledge_recipe
            } f_next_1
          )
      | Some(csys,subst,simple_csys,eq_form_csys_1), no_eq_csys_1, eq_fact_csys_1 ->

          let accu_neg_eq_recipe = ref [] in

          Variable.auto_cleanup_with_reset (fun f_next_2 ->
            (* Instantiate the substitution *)
            List.iter (fun (v,t) -> Variable.link_term v t) subst;

            MGS.compute_all simple_csys (fun mgs_data f_next_3 ->
              Variable.auto_cleanup_with_reset (fun f_next_4 ->
                let vars_df = match !vars_df_ref with
                  | None ->
                      let vlist = DF.get_recipe_variables simple_csys.MGS.simp_deduction_facts in
                      vars_df_ref := Some vlist;
                      vlist
                  | Some vlist -> vlist
                in
                let diseq_rec = Diseq.R.of_maybe_linked_variables vars_df mgs_data.MGS.mgs_fresh_existential_vars in
                accu_neg_eq_recipe := diseq_rec :: !accu_neg_eq_recipe;

                let new_csys_1 = MGS.apply_mgs_on_same_csys csys mgs_data in
                let new_csys_2 = { new_csys_1 with unsolved_facts = UF.remove_unsolved_equality_formula new_csys_1.unsolved_facts } in

                let f_apply =
                  List.fold_left (fun set csys -> match MGS.apply_mgs_on_different_solved_csys csys csys_set.satf_knowledge_recipe mgs_data.MGS.mgs_fresh_existential_vars with
                    | None -> set
                    | Some csys' -> csys' :: set
                  ) []
                in
                let new_no_eq_csys = f_apply no_eq_csys_1 in
                let new_eq_fact_csys = new_csys_2::(f_apply eq_fact_csys_1) in
                let new_eq_form_csys = f_apply eq_form_csys_1 in
                internal new_no_eq_csys new_eq_fact_csys new_eq_form_csys mgs_data.MGS.mgs_eq_recipe (ref None) f_next_4
              ) f_next_3
            ) f_next_2
          ) (fun () ->
            let new_csys = { csys with unsolved_facts = UF.remove_unsolved_equality_formula csys.unsolved_facts } in
            if !accu_neg_eq_recipe = []
            then internal (new_csys::no_eq_csys_1) eq_fact_csys_1 eq_form_csys_1 eq_rec vars_df_ref f_next_1
            else
              let eq_rec' = Formula.R.wedge_conjunction !accu_neg_eq_recipe eq_rec in
              internal (new_csys::no_eq_csys_1) eq_fact_csys_1 eq_form_csys_1 eq_rec' vars_df_ref f_next_1
          )
    in

    internal csys_set.satf_no_formula csys_set.satf_solved csys_set.satf_unsolved csys_set.satf_eq_recipe (ref None) f_next

  (**** The rule Sat for deduction formula ****)

  let rec exploration_sat_deduction_formula head_normalised no_ded_csys ded_fact_csys = function
    | [] -> None, no_ded_csys, ded_fact_csys
    | csys::q ->
        let new_csys_1 =
          if head_normalised
          then csys
          else { csys with unsolved_facts = UF.normalise_deductions csys.unsolved_facts }
        in
        match UF.get_deduction_formula_option new_csys_1.unsolved_facts with
          | None, true ->
              exploration_sat_deduction_formula false no_ded_csys (new_csys_1::ded_fact_csys) q
          | None, false ->
              exploration_sat_deduction_formula false (new_csys_1::no_ded_csys) ded_fact_csys q
          | Some [], _ ->  Config.internal_error "[constraint_system.ml >> Rule.exploration_sat_deduction_formula] It should not be any empty list."
          | Some (form::form_list), _ -> Some(new_csys_1,form,form_list,q), no_ded_csys, ded_fact_csys

  type data_sat_deduction_formula =
    {
      dsd_knowledge_recipe : KR.t;
      dsd_eq_rec : Formula.R.t;
      dsd_head_normalised : bool;
      dsd_vars_df_ref : recipe_variable list option ref
    }

  let sat_deduction_formula (f_continuation_pos:'a set -> (unit -> unit) -> unit) f_continuation_neg csys_set f_next =
    Config.debug (fun () ->
      Config.log_in_debug Config.Constraint_solving (Printf.sprintf "[constraint_system.ml >> Rule] Sat deduction formula : Nb csys no_formula = %d, Nb csys solved = %d, Nb csys unsolved = %d"
        (List.length csys_set.satf_no_formula) (List.length csys_set.satf_solved) (List.length csys_set.satf_unsolved));
      let csys_set = { set = csys_set.satf_no_formula @ csys_set.satf_solved @ csys_set.satf_unsolved; eq_recipe = csys_set.satf_eq_recipe; knowledge_recipe = csys_set.satf_knowledge_recipe } in
      Set.debug_check_structure "[sat_deduction_formula]" csys_set;
      List.iter (debug_on_constraint_system ~solved:true "[sat_deduction_formula]") csys_set.set;
      Config.log_in_debug Config.Constraint_systems ("Eq recipe = "^(Formula.R.display Terminal csys_set.eq_recipe));
      List.iter (fun csys ->
        Config.log_in_debug Config.Constraint_systems (display_constraint_system 1 csys_set.knowledge_recipe csys)
      ) csys_set.set
    );
    let rec internal no_ded_csys ded_fact_csys ded_form_csys data f_next_1 = match exploration_sat_deduction_formula data.dsd_head_normalised no_ded_csys ded_fact_csys ded_form_csys with
      | None, no_ded_csys_1, ded_fact_csys_1 ->
          f_continuation_pos  {
            eq_recipe = data.dsd_eq_rec;
            set = ded_fact_csys_1;
            knowledge_recipe = csys_set.satf_knowledge_recipe;
          } (fun () ->
            f_continuation_neg {
              eq_recipe = data.dsd_eq_rec;
              set = no_ded_csys_1;
              knowledge_recipe = csys_set.satf_knowledge_recipe;
            } f_next_1
          )
      | Some(csys,ded_form,ded_form_list,ded_form_csys_1), no_ded_csys_1, ded_fact_csys_1 ->

          let accu_neg_eq_recipe = ref [] in

          Variable.auto_cleanup_with_reset (fun f_next_2 -> match MGS.simple_of_deduction_formula csys csys_set.satf_knowledge_recipe data.dsd_eq_rec ded_form with
            | None ->
                let new_csys = { csys with unsolved_facts = UF.set_no_deduction csys.unsolved_facts } in
                internal (new_csys::no_ded_csys_1) ded_fact_csys_1 ded_form_csys_1 { data with dsd_head_normalised = false } f_next_2
            | Some simple_csys ->
                MGS.compute_all simple_csys (fun mgs_data f_next_3 ->
                  Variable.auto_cleanup_with_reset (fun f_next_4 ->
                    let vars_df = match !(data.dsd_vars_df_ref) with
                      | None ->
                          let vlist = DF.get_recipe_variables csys.deduction_facts in
                          data.dsd_vars_df_ref := Some vlist;
                          vlist
                      | Some vlist -> vlist
                    in

                    let diseq_rec = Diseq.R.of_maybe_linked_variables vars_df mgs_data.MGS.mgs_fresh_existential_vars in
                    accu_neg_eq_recipe := diseq_rec :: !accu_neg_eq_recipe;

                    let f_apply =
                      List.fold_left (fun set csys -> match MGS.apply_mgs_on_different_solved_csys csys csys_set.satf_knowledge_recipe mgs_data.MGS.mgs_fresh_existential_vars with
                        | None -> set
                        | Some csys' -> csys' :: set
                      ) []
                    in

                    let new_csys_1 = MGS.apply_mgs_on_same_csys csys mgs_data in
                    let new_csys_2 = { new_csys_1 with unsolved_facts = UF.normalise_deduction_formula_to_fact new_csys_1.unsolved_facts ded_form } in

                    let new_no_ded_csys = f_apply no_ded_csys_1 in
                    let new_ded_fact_csys = new_csys_2::(f_apply ded_fact_csys_1) in
                    let new_ded_form_csys = f_apply ded_form_csys_1 in

                    internal new_no_ded_csys new_ded_fact_csys new_ded_form_csys { dsd_eq_rec = mgs_data.MGS.mgs_eq_recipe; dsd_vars_df_ref = ref None; dsd_head_normalised = false; dsd_knowledge_recipe = csys_set.satf_knowledge_recipe } f_next_4
                  ) f_next_3
                ) f_next_2
          ) (fun () ->
            let eq_rec' =
              if !accu_neg_eq_recipe = []
              then data.dsd_eq_rec
              else Formula.R.wedge_conjunction !accu_neg_eq_recipe data.dsd_eq_rec
            in

            if ded_form_list = []
            then
              let new_csys = { csys with unsolved_facts = UF.set_no_deduction csys.unsolved_facts } in
              internal (new_csys::no_ded_csys_1) ded_fact_csys_1 ded_form_csys_1 { data with dsd_eq_rec = eq_rec'; dsd_head_normalised = false } f_next_1
            else
              let new_csys = { csys with unsolved_facts = UF.replace_deduction_formula csys.unsolved_facts ded_form_list } in
              internal no_ded_csys_1 ded_fact_csys_1 (new_csys::ded_form_csys_1) { data with dsd_eq_rec = eq_rec'; dsd_head_normalised = true } f_next_1
          )
    in

    internal csys_set.satf_no_formula csys_set.satf_solved csys_set.satf_unsolved { dsd_eq_rec = csys_set.satf_eq_recipe; dsd_head_normalised = false; dsd_vars_df_ref = ref None; dsd_knowledge_recipe = csys_set.satf_knowledge_recipe } f_next

  (**** The normalisation rule for data constructor *)

  type pattern =
    | PVar of recipe_variable
    | PTuple of symbol
    | PTerm

  let extract_pattern_of_deduction_fact df dfact =

    let rec explore = function
      | Func(f,_) when f.cat = Tuple -> PTuple f
      | Var { link = TLink t; _ } -> explore t
      | Var v ->
          Config.debug (fun () ->
            try ignore (DF.find_term df (Var v)) with Not_found ->
              Config.log_in_debug Config.Always (Printf.sprintf "Error:\nDF = %s\ndfact term = %s\nVariable = %s\n" (DF.display df) (Term.display Display.Terminal dfact.df_term) (Term.display Display.Terminal (Var v)));
              Config.internal_error "[constraint_system >> Rule.extract_pattern_of_deduction_fact] Should be the recipe"
          );
          let x = DF.find_term df (Var v) in
          PVar x
      | _ -> PTerm
    in

    explore dfact.df_term

  let is_equal_pattern pat1 pat2 = match pat1,pat2 with
    | PTuple f1, PTuple f2 when f1 == f2 -> true
    | PTerm, PTerm -> true
    | _ -> false

  exception Found

  type 'a application_data_constructor =
    | ADC_Variable of recipe_variable
    | ADC_Split of 'a t list * 'a t list

  let find_application_data_constructor csys dfact q_csys = match extract_pattern_of_deduction_fact csys.deduction_facts dfact with
      | PVar x -> ADC_Variable x
      | pat ->
          let found_variable = ref None in
          let acc_same_pattern = ref [{ csys with unsolved_facts = UF.validate_head_deduction_facts_for_pattern csys.unsolved_facts }] in
          let acc_diff_pattern = ref [] in

          begin
            try
              List.iter (fun csys' ->
                let dfact_to_check = match UF.pop_deduction_fact_to_check_for_pattern csys'.unsolved_facts with
                  | Some df -> df
                  | _ -> Config.internal_error "[constraint_system.ml >> find_application_data_constructor] The should be a deduction fact to check for pattern."
                in
                match extract_pattern_of_deduction_fact csys'.deduction_facts dfact_to_check with
                  | PVar x -> found_variable := Some x; raise Found
                  | pat' ->
                      if is_equal_pattern pat pat'
                      then acc_same_pattern := { csys' with unsolved_facts = UF.validate_head_deduction_facts_for_pattern csys'.unsolved_facts } :: !acc_same_pattern
                      else acc_diff_pattern := csys' :: !acc_diff_pattern
              ) q_csys;
              ADC_Split(!acc_same_pattern,!acc_diff_pattern)
            with Found ->
              match !found_variable with
                | Some x -> ADC_Variable x
                | _ -> Config.internal_error "[constraint_system.ml >> find_application_data_constructor] Unexpected case."
          end

  let rec split_data_constructor f_continuation csys_set f_next =
    Config.debug (fun () ->
      Config.log_in_debug Config.Constraint_solving (Printf.sprintf "[constraint_system.ml >> Rule] Rule split data constructor : Nb csys = %d" (List.length csys_set.set));
      Set.debug_check_structure "[Split data constructor]" csys_set;
      List.iter (debug_on_constraint_system ~solved:true "[split_data_constructor]") csys_set.set;
      List.iter (fun csys -> Config.log_in_debug Config.Constraint_systems (display_constraint_system 1 csys_set.knowledge_recipe csys)) csys_set.set
    );
    match csys_set.set with
    | [] -> f_next ()
    | csys::q_csys ->

        match UF.pop_deduction_fact_to_check_for_pattern csys.unsolved_facts with
          | None -> f_continuation csys_set f_next
          | Some dfact ->
              match find_application_data_constructor csys dfact q_csys with
                | ADC_Variable x ->
                    let acc_no_formula = ref [] in
                    let acc_solved = ref [] in
                    let acc_unsolved = ref [] in

                    List.iter (fun csys' ->
                      match UF.pop_deduction_fact_to_check_for_pattern csys'.unsolved_facts with
                        | None -> Config.internal_error "[constraint_system.ml >> split_data_constructor] There should be a dedduction fact to check for pattern."
                        | Some dfact' ->
                            let tmp = !Variable.currently_linked in
                            Variable.currently_linked := [];

                            let t_bfact = DF.get_term csys'.deduction_facts x in
                            try
                              Term.unify t_bfact dfact'.df_term;

                              begin
                                if !Variable.currently_linked = []
                                then acc_solved := csys' :: !acc_solved
                                else
                                  let eq_form =
                                    List.rev_map (fun v -> match v.link with
                                      | TLink t -> (v,t)
                                      | _ -> Config.internal_error "[constraint_system.ml >> split_data_constructor] All variables should be linked."
                                    ) !Variable.currently_linked
                                  in
                                  let csys'' = { csys' with unsolved_facts = UF.add_equality_formula csys'.unsolved_facts eq_form } in
                                  acc_unsolved := csys'' :: !acc_unsolved
                              end;

                              List.iter (fun v -> v.link <- NoLink) !Variable.currently_linked;
                              Variable.currently_linked := tmp
                            with Term.Not_unifiable ->
                              acc_no_formula := csys' :: !acc_no_formula;
                              List.iter (fun v -> v.link <- NoLink) !Variable.currently_linked;
                              Variable.currently_linked := tmp
                    ) csys_set.set;

                    let f_continuation_pos csys_set_1 f_next_1 =
                      let csys_set_2 =
                        { csys_set_1 with set =
                            List.rev_map (fun csys ->
                              { csys with unsolved_facts = UF.remove_head_unchecked_deduction_fact_for_pattern csys.unsolved_facts }
                            ) csys_set_1.set
                        }
                      in
                      split_data_constructor f_continuation csys_set_2 f_next_1
                    in

                    let f_continuation_neg = split_data_constructor f_continuation in

                    sat_equality_formula ~universal:false f_continuation_pos f_continuation_neg { satf_eq_recipe = csys_set.eq_recipe; satf_no_formula = !acc_no_formula; satf_solved = !acc_solved; satf_unsolved = !acc_unsolved; satf_knowledge_recipe = csys_set.knowledge_recipe } f_next
                | ADC_Split(same_pattern_csys_list,diff_pattern_csys_list) ->
                    split_data_constructor f_continuation { csys_set with set = same_pattern_csys_list } (fun () ->
                      split_data_constructor f_continuation { csys_set with set = diff_pattern_csys_list } f_next
                    )

  (**** The rule Equality for element of the knowledge base. ****)

  let equality_knowledge_base f_continuation csys_set f_next =
    Config.debug (fun () ->
      Config.log_in_debug Config.Constraint_solving (Printf.sprintf "[constraint_system.ml >> Rule] Rule equality_knowledge_base : Nb csys = %d" (List.length csys_set.set));
      Set.debug_check_structure "[Equality knowledge base]" csys_set;
      Config.log_in_debug Config.Constraint_systems ("Eq recipe = "^(Formula.R.display Terminal csys_set.eq_recipe));
      List.iter (fun csys ->
        debug_on_constraint_system "[equality_knowledge_base]" csys;
        Config.log_in_debug Config.Constraint_systems (display_constraint_system 1 csys_set.knowledge_recipe csys)
      ) csys_set.set
    );
    match csys_set.set with
    | [] -> f_next ()
    | csys::_ ->
        let last_index = IK.get_last_index csys.incremented_knowledge in

        let rec internal last_term_list_ref last_index_checked csys_set_1 f_next_1 = match IK.get_previous_index_in_knowledge_base csys_set.knowledge_recipe csys.incremented_knowledge last_index_checked with
          | None ->
              let last_term_list = match !last_term_list_ref with
                | Some t_list -> t_list
                | None ->
                    let t_list = List.map_tail (fun csys -> IK.get_last_term csys.incremented_knowledge) csys_set_1.set in
                    last_term_list_ref := Some t_list;
                    t_list
              in

              let csys_list =
                List.rev_map2 (fun csys last_term ->
                  let new_skeletons = List.map (fun index_skel -> (last_index,index_skel)) (Rewrite_rules.get_possible_skeletons_for_terms last_term) in

                  let (skeletons_checked_IK,skeletons_to_check_IK) = csys.rule_data.skeletons_IK in
                  let (skeletons_checked_K,skeletons_to_check_K) = csys.rule_data.skeletons_K in

                  let new_skeletons_to_check_K = List.rev_append skeletons_to_check_K skeletons_checked_K in
                  let new_skeletons_to_check_IK = List.rev_append new_skeletons (List.rev_append skeletons_to_check_IK skeletons_checked_IK) in

                  let rule_data =
                    { csys.rule_data with
                      skeletons_K = ([],new_skeletons_to_check_K);
                      skeletons_IK = ([],new_skeletons_to_check_IK)
                    }
                  in

                  { csys with rule_data = rule_data }
                ) csys_set_1.set last_term_list
              in

              f_continuation { csys_set_1 with set = csys_list } f_next_1
          | Some index_to_check ->
              let last_term_list = match !last_term_list_ref with
                | Some t_list -> t_list
                | None ->
                    let t_list = List.map_tail (fun csys -> IK.get_last_term csys.incremented_knowledge) csys_set_1.set in
                    last_term_list_ref := Some t_list;
                    t_list
              in

              let eq_solved_csys = ref [] in
              let eq_form_csys = ref [] in
              let no_eq_csys = ref [] in

              List.iter2 (fun csys last_term ->
                Variable.auto_cleanup_with_reset_notail (fun () ->
                  try
                    Term.unify last_term (IK.get_term csys.knowledge csys.incremented_knowledge index_to_check);

                    if !Variable.currently_linked = []
                    then eq_solved_csys := csys :: !eq_solved_csys
                    else
                      let ef_form =
                        List.rev_map (fun v -> match v.link with
                          | TLink t -> v,t
                          | _ -> Config.internal_error "[constraint_system.ml >> equality_knowledge_base] Unexpected link."
                        ) !Variable.currently_linked
                      in
                      eq_form_csys := { csys with unsolved_facts = UF.add_equality_formula csys.unsolved_facts ef_form } :: !eq_form_csys
                  with Term.Not_unifiable -> no_eq_csys := csys :: !no_eq_csys
                )
              ) csys_set_1.set last_term_list;

              if !eq_form_csys = [] && !no_eq_csys = []
              then
                (* All equal *)
                f_continuation { csys_set_1 with set = List.rev_map (fun csys -> { csys with incremented_knowledge = IK.remove_last_entry csys.incremented_knowledge }) !eq_solved_csys } f_next_1
              else if !eq_form_csys = [] && !eq_solved_csys = []
              then
                (* None equal *)
                internal last_term_list_ref index_to_check csys_set_1 f_next_1
              else
                (* Other *)
                let f_continuation_pos csys_set_2 f_next_2 =
                  let csys_set_3 =
                    { csys_set_2 with
                      set = List.rev_map (fun csys -> { csys with incremented_knowledge = IK.remove_last_entry csys.incremented_knowledge }) csys_set_2.set
                    }
                  in
                  f_continuation csys_set_3 f_next_2
                in
                let f_continuation_neg csys_set_2 f_next_2 =
                  internal (ref None) index_to_check csys_set_2 f_next_2
                in

                sat_equality_formula ~universal:false f_continuation_pos f_continuation_neg { satf_eq_recipe = csys_set_1.eq_recipe; satf_no_formula = !no_eq_csys; satf_solved = !eq_solved_csys; satf_unsolved = !eq_form_csys; satf_knowledge_recipe = csys_set.knowledge_recipe } f_next_1
        in

        internal (ref None) last_index csys_set f_next

  (**** The rule for adding element in the knowledge base ****)

  type 'a result_exploration_normalisation_deduction_consequence =
    | Add of 'a t list
    | Remove
    | Consequence of recipe * 'a t * 'a t list * 'a t list

  let rec exploration_normalisation_deduction_consequence kbr only_pure prev_csys = function
    | [] ->
        if only_pure
        then Remove
        else Add prev_csys
    | csys::q ->
        let t = (UF.pop_deduction_fact csys.unsolved_facts).df_term in
        match t with
          | Name { pure_fresh_n = true; _ } ->
              exploration_normalisation_deduction_consequence kbr only_pure (csys::prev_csys) q
          | _ ->
              if csys.rule_data.normalisation_deduction_checked
              then exploration_normalisation_deduction_consequence kbr false (csys::prev_csys) q
              else
                match IK.consequence_term kbr csys.knowledge csys.incremented_knowledge csys.deduction_facts t with
                  | None ->
                      let csys' = { csys with rule_data = { csys.rule_data with normalisation_deduction_checked = true } } in
                      exploration_normalisation_deduction_consequence kbr false (csys'::prev_csys) q
                  | Some r -> Consequence(r,csys,q, prev_csys)

  (** Purpose : Check whether a deduction fact is consequence or not of the knowledge base and incremented knowledge base.
     Input : Only deductions facts (no formula nor equality) and same amount. (Can we have several ?)
     Output :
      - When no consequence -> Adding in SDF and followed by equality_SDF and then back to [normalisation_deduction_consequence]
      - When there are consequence -> add an equality formula and check it.
      *)
  let rec normalisation_deduction_consequence f_continuation csys_set f_next =
    Config.debug (fun () ->
      Config.log_in_debug Config.Constraint_solving (Printf.sprintf "[constraint_system.ml >> Rule] Rule normalisation_deduction_consequence : Nb csys = %d" (List.length csys_set.set));
      Set.debug_check_structure "[Normalisation deduction consequence]" csys_set;
      List.iter (debug_on_constraint_system ~solved:true "[normalisation_deduction_consequence]") csys_set.set;
      Config.log_in_debug Config.Constraint_systems ("Eq recipe = "^(Formula.R.display Terminal csys_set.eq_recipe));
      List.iter (fun csys ->
        Config.log_in_debug Config.Constraint_systems (display_constraint_system 1 csys_set.knowledge_recipe csys)
      ) csys_set.set
    );
    if csys_set.set = []
    then f_next ()
    else
      let csys = List.hd csys_set.set in
      if UF.exists_deduction_fact csys.unsolved_facts
      then
        begin match exploration_normalisation_deduction_consequence csys_set.knowledge_recipe true [] csys_set.set with
          | Remove ->
              (* We detected that the terms of the deduction facts are only pure fresh names
                 so we can remove them. *)
              let new_csys_list =
                List.rev_map (fun csys' ->
                  { csys' with unsolved_facts = UF.remove_head_deduction_fact csys'.unsolved_facts}
                ) csys_set.set
              in
              normalisation_deduction_consequence f_continuation { csys_set with set = new_csys_list } f_next
          | Add checked_csys ->
              (* We add in the incremented knowledge base *)
              let new_csys_list =
                List.rev_map (fun csys ->
                  let (dfact,uf) = UF.pop_and_remove_deduction_fact csys.unsolved_facts in
                  { csys with
                    unsolved_facts = uf;
                    incremented_knowledge = IK.add csys.incremented_knowledge dfact;
                    rule_data = { csys.rule_data with normalisation_deduction_checked = false }
                  }
                ) checked_csys
              in

              equality_knowledge_base (normalisation_deduction_consequence f_continuation) { csys_set with set = new_csys_list } f_next
          | Consequence(recipe,csys,to_check_csys,checked_csys) ->
              let no_eq_form_csys = ref [] in
              let solved_eq_csys = ref [csys] in
              let eq_form_csys = ref [] in

              let explore_csys_list =
                List.iter (fun csys' ->
                  let t = (UF.pop_deduction_fact csys'.unsolved_facts).df_term in
                  let t_conseq = IK.consequence_recipe csys'.knowledge csys'.incremented_knowledge csys'.deduction_facts recipe in

                  Variable.auto_cleanup_with_reset_notail (fun () ->
                    try
                      Term.unify t t_conseq;

                      if !Variable.currently_linked = []
                      then solved_eq_csys := csys' :: !solved_eq_csys
                      else
                        let form =
                          List.rev_map (fun v -> match v.link with
                            | TLink t' -> (v,t')
                            | _ -> Config.internal_error "[constraint_system.ml >> normalisation_deduction_consequence] Unexpected link."
                          ) !Variable.currently_linked
                        in
                        let csys'' = { csys' with unsolved_facts = UF.add_equality_formula csys'.unsolved_facts form } in
                        eq_form_csys := csys'' :: !eq_form_csys
                    with Term.Not_unifiable -> no_eq_form_csys := csys' :: !no_eq_form_csys
                  )
                )
              in

              explore_csys_list to_check_csys;
              explore_csys_list checked_csys;

              let f_continuation_pos csys_set_1 f_next_1 =
                let csys_set_2 =
                  { csys_set_1 with
                    set =
                      List.rev_map (fun csys' ->
                        { csys' with
                          unsolved_facts = UF.remove_head_deduction_fact csys'.unsolved_facts;
                          rule_data = { csys'.rule_data with normalisation_deduction_checked = false }
                        }
                      ) csys_set_1.set
                  }
                in
                normalisation_deduction_consequence f_continuation csys_set_2 f_next_1
              in

              sat_equality_formula f_continuation_pos (normalisation_deduction_consequence f_continuation) { satf_solved = !solved_eq_csys; satf_unsolved = !eq_form_csys; satf_no_formula = !no_eq_form_csys; satf_eq_recipe = csys_set.eq_recipe; satf_knowledge_recipe = csys_set.knowledge_recipe } f_next
        end
      else f_continuation csys_set f_next

  (**** The rule Rewrite ****)

  let nb_RSSNone_rewrite = ref 0
  let nb_RSSNo_IK_solution_rewrite = ref 0
  let nb_RSSSimple_pos_rewrite = ref 0
  let nb_RSSSimple_neg_rewrite = ref 0

  exception NFound of deduction_fact

  type deduction_formula_generated =
    | NoFormula
    | FoundFact of deduction_fact
    | Unsolved of deduction_formula list

  let create_generic_skeleton_formula csys index_skel recipe =
    let lhs_recipe = Recipe.get_args recipe in
    let lhs_term = List.map (IK.consequence_recipe csys.knowledge csys.incremented_knowledge csys.deduction_facts) lhs_recipe in

    try
      let unsolved_deduction =
        List.fold_left (fun acc (lhs,rhs) ->
          (* All variables in lhs and rhs are universal *)
          let tmp = !Variable.currently_linked in
          Variable.currently_linked := [];

          try
            List.iter2 (fun t1 t2 -> Term.unify t1 t2) lhs_term lhs;

            let equations =
              List.fold_left (fun acc v -> match v.link with
                | TLink t when v.quantifier <> Universal -> (v,Term.instantiate t)::acc
                | _ -> acc
              ) [] !Variable.currently_linked
            in

            if equations = []
            then
              begin
                let dfact = { df_recipe = recipe; df_term = Term.instantiate rhs } in
                List.iter (fun v -> v.link <- NoLink) !Variable.currently_linked;
                Variable.currently_linked := tmp;
                raise (NFound dfact)
              end
            else
              begin
                let form = { df_head = { df_recipe = recipe; df_term = Term.instantiate rhs }; df_equations = equations } in
                List.iter (fun v -> v.link <- NoLink) !Variable.currently_linked;
                Variable.currently_linked := tmp;
                form::acc
              end
          with Term.Not_unifiable ->
            List.iter (fun v -> v.link <- NoLink) !Variable.currently_linked;
            Variable.currently_linked := tmp;
            acc
        ) [] (Rewrite_rules.get_compatible_rewrite_rules index_skel)
      in

      if unsolved_deduction = []
      then NoFormula
      else Unsolved unsolved_deduction
    with NFound fact -> FoundFact fact

  let update_skeleton_history csys =
    let dfact = UF.get_unique_unchecked_deduction_fact csys.unsolved_facts in

    let f = Recipe.root dfact.df_recipe in

    let rec replace_history = function
      | [] -> Config.internal_error "[constraint_system.ml >> Rule.update_skeleton] Unexpected case"
      | hist::q when hist.destructor == f ->
          let diseq = Rewrite_rules.generate_mixed_formulas_for_skeletons csys.knowledge csys.incremented_knowledge csys.deduction_facts hist.fst_vars hist.snd_vars dfact.df_recipe in
          { hist with diseq = Formula.M.wedge diseq hist.diseq }::q
      | hist::q -> hist::(replace_history q)
    in

    replace_history csys.rule_data.history_skeleton

  let remove_skeletons ((id_kb,id_skel):int*int) skel_list =
    let rec explore f_next = function
      | [] -> f_next []
      | (id_kb',id_skel')::q when id_kb' = id_kb && id_skel' = id_skel -> f_next q
      | e::q -> explore (fun q' -> e::q') q
    in
    explore (fun x -> x) skel_list

  let rec remove_all_skeletons id_kb = function
    | [] -> []
    | (id_kb',_)::q when id_kb = id_kb' -> remove_all_skeletons id_kb q
    | t::q -> t::(remove_all_skeletons id_kb q)

  let rec instantiate_infinite_variables is_for_ground_rule = function
    | RVar { link_r = RLink r; _ } -> instantiate_infinite_variables is_for_ground_rule r
    | RVar v when v.type_r = Recipe_Variable.infinite_type ->
        let f =
          if is_for_ground_rule
          then Symbol.fresh_attacker_name_ground ()
          else Symbol.fresh_attacker_name ()
        in
        Recipe_Variable.link_recipe v (RFunc(f,[]));
        RFunc(f,[])
    | RFunc(f,args) -> RFunc(f,List.map (instantiate_infinite_variables is_for_ground_rule) args)
    | r -> r

  let rec exploration_rewrite ?(ground=false) kbr eq_recipe vars_df_ref prev_set = function
    | [] -> None, prev_set
    | csys::q ->
        let rule_data_ref = ref csys.rule_data in

        let rec explore check_on_K skeletons_checked = function
          | [] ->
              if check_on_K
              then
                begin
                  rule_data_ref :=  { !rule_data_ref with skeletons_K = (skeletons_checked,[]) };
                  let (checked_IK,to_check_IK) = (!rule_data_ref).skeletons_IK in
                  explore false checked_IK to_check_IK
                end
              else
                let rule_data = { !rule_data_ref with skeletons_IK = (skeletons_checked,[]) } in
                exploration_rewrite ~ground:ground kbr eq_recipe vars_df_ref ({ csys with rule_data = rule_data }::prev_set) q
          | ((index_kb,index_skel)::q_skel) as all_skel ->
              let found_simple = ref false in
              let result =
                Variable.auto_cleanup_with_reset_notail (fun () ->
                  Recipe_Variable.auto_cleanup_with_reset_notail (fun () ->
                    match MGS.simple_of_skeleton csys kbr eq_recipe index_kb index_skel with
                      | MGS.RSSNone ->
                          Config.debug (fun () -> incr nb_RSSNone_rewrite);
                          None
                      | MGS.RSSNo_IK_solution ->
                          Config.debug (fun () -> incr nb_RSSNo_IK_solution_rewrite);
                          found_simple := true;
                          None
                      | MGS.RSSSimple(recipe,simple_csys,infinite_basic_facts,infinite_vars) ->
                          let df_vars = { MGS.std_vars = vars_df_ref; MGS.infinite_vars = infinite_vars } in
                          match MGS.compute_one_with_IK simple_csys infinite_basic_facts df_vars with
                            | None ->
                                Config.debug (fun () -> incr nb_RSSSimple_neg_rewrite);
                                found_simple := true;
                                None
                            | Some mgs_data ->
                                Config.debug (fun () -> incr nb_RSSSimple_pos_rewrite);
                                Some(recipe,mgs_data)
                  )
                )
              in
              match result with
                | None ->
                    if !found_simple
                    then explore check_on_K ((index_kb,index_skel)::skeletons_checked) q_skel
                    else explore check_on_K skeletons_checked q_skel
                | Some(recipe,mgs_data) ->
                    let new_recipe =
                      Recipe_Variable.auto_cleanup_with_reset_notail (fun () ->
                        List.iter (fun (v,r) -> Recipe_Variable.link_recipe v r) mgs_data.MGS.one_mgs_infinite_subst;
                        instantiate_infinite_variables ground recipe
                      )
                    in
                    let rule_data =
                      if check_on_K
                      then { !rule_data_ref with skeletons_K = (skeletons_checked,all_skel) }
                      else { !rule_data_ref with skeletons_IK = (skeletons_checked,all_skel) }
                    in
                    Some(index_kb,index_skel,mgs_data,new_recipe,{ csys with rule_data = rule_data },q), prev_set
        in

        match csys.rule_data.skeletons_K, csys.rule_data.skeletons_IK with
          | (_,[]),(_,[]) -> exploration_rewrite ~ground:ground kbr eq_recipe vars_df_ref (csys::prev_set) q
          | (_,[]),(skeletons_checked_IK,skeletons_to_check_IK) ->
              (* All skeletons in K are checked *)
              explore false skeletons_checked_IK skeletons_to_check_IK
          | (skeletons_checked_K,skeletons_to_check_K), _ ->
              explore true skeletons_checked_K skeletons_to_check_K

  let rewrite f_continuation csys_set f_next =
    Config.debug (fun () ->
      Config.log_in_debug Config.Constraint_solving (Printf.sprintf "[constraint_system.ml >> Rule] Rule Rewrite : Nb csys = %d" (List.length csys_set.set));
      Config.log_in_debug Config.Constraint_systems ("Eq recipe = "^(Formula.R.display Terminal csys_set.eq_recipe));
      List.iter (fun csys ->
        Config.log_in_debug Config.Constraint_systems (display_constraint_system 1 csys_set.knowledge_recipe csys)
      ) csys_set.set;
      Set.debug_check_structure "[Rewrite]" csys_set;
      List.iter (debug_on_constraint_system ~solved:true "[Rewrite]") csys_set.set
    );
    let rec internal eq_recipe vars_df_ref checked_csys to_check_csys f_next_0 =
      Symbol.auto_cleanup_attacker_name (fun f_next_1 ->
        match exploration_rewrite csys_set.knowledge_recipe eq_recipe vars_df_ref checked_csys to_check_csys with
          | None, checked_csys_1 -> f_continuation { csys_set with set = checked_csys_1; eq_recipe = eq_recipe } f_next_1
          | Some(index_kb,index_skel,mgs_data,recipe,csys,to_check_csys_1),checked_csys_1 ->
          if mgs_data.MGS.one_mgs_std_subst = []
          then
            begin
              (* Implies that no substitution was applied to apply the rewrite rule *)

              let no_ded_form_csys = ref [] in
              let ded_solved_csys = ref [] in
              let ded_form_csys = ref [] in

              let f_apply csys' = match create_generic_skeleton_formula csys' index_skel recipe with
                | FoundFact fact -> ded_solved_csys := { csys' with unsolved_facts = UF.add_deduction_fact csys'.unsolved_facts fact} :: !ded_solved_csys
                | NoFormula -> no_ded_form_csys := csys' :: !no_ded_form_csys
                | Unsolved form_l -> ded_form_csys := { csys' with unsolved_facts = UF.add_deduction_formulas csys'.unsolved_facts form_l} :: !ded_form_csys
              in

              List.iter f_apply (csys::checked_csys_1);
              List.iter f_apply to_check_csys_1;

              let size_K = KR.size csys_set.knowledge_recipe in
              let application_on_IK = index_kb >= size_K in
              let removal_allowed = application_on_IK && (Rewrite_rules.get_skeleton index_skel).Rewrite_rules.removal_allowed in
              let no_history = (Rewrite_rules.get_skeleton index_skel).Rewrite_rules.no_history in

              sat_deduction_formula (fun csys_set_2 f_next_2 ->
                (* All the deduction facts are in solved form. *)
                let csys_list =
                  List.rev_map (fun csys ->
                    let new_ik =
                      if removal_allowed
                      then IK.remove csys.incremented_knowledge index_kb
                      else csys.incremented_knowledge
                    in

                    let rule_data =
                      if no_history
                      then
                        if application_on_IK
                        then
                          let (skels_checked,skels_to_check) = csys.rule_data.skeletons_IK in
                          if removal_allowed
                          then
                            let (skels_checked',skels_to_check') = (remove_all_skeletons index_kb skels_checked,remove_all_skeletons index_kb skels_to_check ) in
                            { csys.rule_data with skeletons_IK = (skels_checked',skels_to_check') }
                          else { csys.rule_data with skeletons_IK = (skels_checked,remove_skeletons (index_kb,index_skel) skels_to_check) }
                        else
                          let (skels_checked,skels_to_check) = csys.rule_data.skeletons_K in
                          { csys.rule_data with skeletons_K = (skels_checked,remove_skeletons (index_kb,index_skel) skels_to_check) }
                      else
                        if removal_allowed
                        then
                          begin
                            let (skels_checked,skels_to_check) = csys.rule_data.skeletons_IK in
                            let (skels_checked',skels_to_check') = (remove_all_skeletons index_kb skels_checked,remove_all_skeletons index_kb skels_to_check ) in
                            { csys.rule_data with history_skeleton =  update_skeleton_history csys; skeletons_IK = (skels_checked',skels_to_check') }
                          end
                        else { csys.rule_data with history_skeleton =  update_skeleton_history csys }
                    in
                    { csys with incremented_knowledge = new_ik; rule_data = rule_data }
                  ) csys_set_2.set
                in
                split_data_constructor (
                  normalisation_deduction_consequence (fun csys_set_4 f_next_4 ->
                    internal csys_set_4.eq_recipe (ref None) [] csys_set_4.set f_next_4
                  )
                ) { csys_set_2 with set = csys_list }  f_next_2
              ) (fun csys_set_2 f_next_2 ->
                internal csys_set_2.eq_recipe (ref None) [] csys_set_2.set f_next_2
              ) { satf_solved = !ded_solved_csys; satf_unsolved = !ded_form_csys; satf_no_formula = !no_ded_form_csys; satf_eq_recipe = eq_recipe; satf_knowledge_recipe = csys_set.knowledge_recipe } f_next_1
            end
          else
            begin
              let new_eq_rec_ref = ref eq_recipe in

              Recipe_Variable.auto_cleanup_with_reset (fun f_next_2 ->
                (* Applying the mgs *)

                (* We link the variables of the mgs *)
                List.iter (fun (v,r) -> Recipe_Variable.link_recipe v r) mgs_data.MGS.one_mgs_std_subst;

                let vars_df = match !vars_df_ref with
                  | Some vlist -> vlist
                  | None -> Config.internal_error "[constraint_system.ml >> Rule.rewrite] The variables of DF should have been computed during the computation of one_mgs."
                in

                new_eq_rec_ref := Formula.R.wedge (Diseq.R.of_maybe_linked_variables vars_df mgs_data.MGS.one_mgs_fresh_existential_vars) !new_eq_rec_ref;

                Variable.auto_cleanup_with_reset (fun f_next_3 ->
                  let no_ded_form_csys = ref [] in
                  let ded_solved_csys = ref [] in
                  let ded_form_csys = ref [] in

                  let f_apply csys = match MGS.apply_mgs_on_different_solved_csys csys csys_set.knowledge_recipe mgs_data.MGS.one_mgs_fresh_existential_vars with
                    | None -> ()
                    | Some csys' ->
                        match create_generic_skeleton_formula csys' index_skel recipe with
                          | FoundFact fact -> ded_solved_csys := { csys' with unsolved_facts = UF.add_deduction_fact csys'.unsolved_facts fact} :: ! ded_solved_csys
                          | NoFormula -> no_ded_form_csys := csys' :: !no_ded_form_csys
                          | Unsolved form_l -> ded_form_csys := { csys' with unsolved_facts = UF.add_deduction_formulas csys'.unsolved_facts form_l} :: !ded_form_csys
                  in

                  List.iter f_apply (csys::checked_csys_1);
                  List.iter f_apply to_check_csys_1;

                  let size_K = KR.size csys_set.knowledge_recipe in
                  let application_on_IK = index_kb >= size_K in
                  let removal_allowed = application_on_IK && (Rewrite_rules.get_skeleton index_skel).Rewrite_rules.removal_allowed in
                  let no_history = (Rewrite_rules.get_skeleton index_skel).Rewrite_rules.no_history in

                  sat_deduction_formula (fun csys_set_4 f_next_4 ->
                    (* All the deduction facts are in solved form. *)
                    let csys_list =
                      List.rev_map (fun csys ->
                        let new_ik =
                          if removal_allowed
                          then IK.remove csys.incremented_knowledge index_kb
                          else csys.incremented_knowledge
                        in

                        let rule_data =
                          if no_history
                          then
                            if application_on_IK
                            then
                              let (skels_checked,skels_to_check) = csys.rule_data.skeletons_IK in
                              if removal_allowed
                              then
                                let (skels_checked',skels_to_check') = (remove_all_skeletons index_kb skels_checked,remove_all_skeletons index_kb skels_to_check ) in
                                { csys.rule_data with skeletons_IK = (skels_checked',skels_to_check') }
                              else { csys.rule_data with skeletons_IK = (skels_checked,remove_skeletons (index_kb,index_skel) skels_to_check) }
                            else
                              let (skels_checked,skels_to_check) = csys.rule_data.skeletons_K in
                              { csys.rule_data with skeletons_K = (skels_checked,remove_skeletons (index_kb,index_skel) skels_to_check) }
                          else
                            if removal_allowed
                            then
                              let (skels_checked,skels_to_check) = csys.rule_data.skeletons_IK in
                              let (skels_checked',skels_to_check') = (remove_all_skeletons index_kb skels_checked,remove_all_skeletons index_kb skels_to_check ) in
                              { csys.rule_data with history_skeleton =  update_skeleton_history csys; skeletons_IK = (skels_checked',skels_to_check') }
                            else { csys.rule_data with history_skeleton =  update_skeleton_history csys }
                        in
                        { csys with incremented_knowledge = new_ik; rule_data = rule_data }
                      ) csys_set_4.set
                    in
                    split_data_constructor (
                      normalisation_deduction_consequence (fun csys_set_6 f_next_6 ->
                        internal csys_set_6.eq_recipe (ref None) [] csys_set_6.set f_next_6
                      )
                    ) { csys_set_4 with set = csys_list }  f_next_4
                  ) (fun csys_set_4 f_next_4 ->
                    internal csys_set_4.eq_recipe (ref None) [] csys_set_4.set f_next_4
                  ) { satf_solved = !ded_solved_csys; satf_unsolved = !ded_form_csys; satf_no_formula = !no_ded_form_csys; satf_eq_recipe = eq_recipe; satf_knowledge_recipe = csys_set.knowledge_recipe } f_next_3
                ) f_next_2
              ) (fun () ->
                (* Negation of the mgs *)
                internal !new_eq_rec_ref vars_df_ref checked_csys_1 (csys::to_check_csys_1) f_next_1
              )
            end
      ) f_next_0
    in

    internal csys_set.eq_recipe (ref None) [] csys_set.set f_next

  (*** The rule consequence ***)

  let nb_RSSNone_constructor = ref 0
  let nb_RSSNo_IK_solution_constructor = ref 0
  let nb_RSSSimple_pos_constructor = ref 0
  let nb_RSSSimple_neg_constructor = ref 0

  type equality_formula_generated =
    | NoEq
    | SolvedEq
    | UnsolvedEq of equality_formula

  let remove_skeletons_cons (id_kb:int) =
    let rec explore f_next = function
      | [] -> f_next []
      | id_kb'::q when id_kb' = id_kb -> f_next q
      | e::q -> explore (fun q' -> e::q') q
    in
    explore (fun x -> x)

  let remove_all_skeletons (id_kb:int) skel_list =
    let rec explore acc = function
      | [] -> acc
      | (id_kb',_)::q when id_kb' = id_kb -> explore acc q
      | e::q -> explore (e::acc) q
    in
    explore [] skel_list

  let create_eq_constructor_formula csys index_kb recipe =
    let f = Recipe.root recipe in

    match IK.get_term csys.knowledge csys.incremented_knowledge index_kb with
      | (Func(f',_)) as t_kb when f == f' ->
          let t = IK.consequence_recipe csys.knowledge csys.incremented_knowledge csys.deduction_facts recipe in
          Variable.auto_cleanup_with_reset_notail (fun () ->
            try
              Term.unify t t_kb;

              if !Variable.currently_linked = []
              then SolvedEq
              else UnsolvedEq(List.rev_map (fun x -> (x,Term.instantiate (Var x))) !Variable.currently_linked)
            with Term.Not_unifiable -> NoEq
          )
      | _ -> NoEq

  let rec exploration_equality_constructor ?(ground=false) kbr eq_recipe vars_df_ref checked_csys = function
    | [] -> None, checked_csys
    | csys::q ->
        let rule_data_ref = ref csys.rule_data in

        let rec sub_explore check_on_K equality_constructor_checked = function
          | [] ->
              if check_on_K
              then
                begin
                  rule_data_ref :=  { !rule_data_ref with equality_constructor_K = (equality_constructor_checked,[]) };
                  let (checked_IK,to_check_IK) = (!rule_data_ref).equality_constructor_IK in
                  sub_explore false checked_IK to_check_IK
                end
              else
                let rule_data = { !rule_data_ref with equality_constructor_IK = (equality_constructor_checked,[]) } in
                exploration_equality_constructor ~ground:ground kbr eq_recipe vars_df_ref ({csys with rule_data = rule_data}::checked_csys) q
          | index_kb::q_id ->
              match IK.get_term csys.knowledge csys.incremented_knowledge index_kb with
                | Func(f,args) when f.public ->
                    let skeleton_cons = Rewrite_rules.get_skeleton_constructor f in
                    if Formula.M.Bot = skeleton_cons.Rewrite_rules.formula
                    then sub_explore check_on_K equality_constructor_checked q_id
                    else
                      begin match MGS.simple_of_equality_constructor csys kbr eq_recipe index_kb f args skeleton_cons with
                        | MGS.RSSNone ->
                            Config.debug (fun () -> incr nb_RSSNone_constructor);
                            sub_explore check_on_K equality_constructor_checked q_id
                        | MGS.RSSNo_IK_solution ->
                            Config.debug (fun () -> incr nb_RSSNo_IK_solution_constructor);
                            sub_explore check_on_K (index_kb::equality_constructor_checked) q_id
                        | MGS.RSSSimple(recipe,simple_csys,infinite_bfacts,infinite_vars) ->
                            Config.debug (fun () ->
                              if List.exists (fun bfact -> bfact.bf_var.link_r <> RNoLink) infinite_bfacts
                              then Config.internal_error "[constraint_system.ml >> exploration_equality_constructor] Variables in infinite basic facts should not be linked.";

                              DF.debug "[constraint_system.ml >> exploration_equality_constructor]" simple_csys.MGS.simp_deduction_facts
                            );
                            let df_vars = { MGS.std_vars = vars_df_ref; MGS.infinite_vars = infinite_vars } in
                            match MGS.compute_one_with_IK simple_csys infinite_bfacts df_vars with
                              | None ->
                                  Config.debug (fun () -> incr nb_RSSSimple_neg_constructor);
                                  sub_explore check_on_K (index_kb::equality_constructor_checked) q_id
                              | Some mgs_data ->
                                  Config.debug (fun () -> incr nb_RSSSimple_pos_constructor);
                                  let new_recipe =
                                    Recipe_Variable.auto_cleanup_with_reset_notail (fun () ->
                                      List.iter (fun (v,r) -> Recipe_Variable.link_recipe v r) mgs_data.MGS.one_mgs_infinite_subst;
                                      instantiate_infinite_variables ground recipe
                                    )
                                  in
                                  let rule_data =
                                    if check_on_K
                                    then { !rule_data_ref with equality_constructor_K = (equality_constructor_checked,index_kb::q_id) }
                                    else { !rule_data_ref with equality_constructor_IK = (equality_constructor_checked,index_kb::q_id) }
                                  in
                                  Some(new_recipe,mgs_data,index_kb,{ csys with rule_data = rule_data },q), checked_csys
                      end
                | _ -> sub_explore check_on_K equality_constructor_checked q_id
        in

        match csys.rule_data.equality_constructor_K, csys.rule_data.equality_constructor_IK with
          | (_,[]),(_,[]) -> exploration_equality_constructor ~ground:ground kbr eq_recipe vars_df_ref (csys::checked_csys) q
          | (_,[]),(equality_constructor_checked_IK,equality_constructor_to_check_IK) ->
              (* All skeletons in K are checked *)
              sub_explore false equality_constructor_checked_IK equality_constructor_to_check_IK
          | (equality_constructor_checked_K,equality_constructor_to_check_K), _ ->
              sub_explore true equality_constructor_checked_K equality_constructor_to_check_K

  let internal_equality_constructor f_continuation csys_set f_next =
    Config.debug (fun () ->
      Config.log_in_debug Config.Constraint_solving (Printf.sprintf "[constraint_system.ml >> Rule] Rule internal equality constructor : Nb csys = %d" (List.length csys_set.set));
      Config.log_in_debug Config.Constraint_systems ("Eq recipe = "^(Formula.R.display Terminal csys_set.eq_recipe));
      List.iter (fun csys ->
        Config.log_in_debug Config.Constraint_systems (display_constraint_system 1 csys_set.knowledge_recipe csys)
      ) csys_set.set;
      Set.debug_check_structure "[Internal equality constructor]" csys_set;
      List.iter (debug_on_constraint_system ~solved:true "[Internal equality constructor]") csys_set.set
    );
    let rec internal eq_recipe vars_df_ref checked_csys to_check_csys f_next_0 =
      Symbol.auto_cleanup_attacker_name (fun f_next_1 ->
        match exploration_equality_constructor csys_set.knowledge_recipe eq_recipe vars_df_ref checked_csys to_check_csys with
          | None, checked_csys_1 -> f_continuation { set = checked_csys_1; eq_recipe = eq_recipe; knowledge_recipe = csys_set.knowledge_recipe } f_next_1
          | Some(recipe,mgs_data,index_kb,csys,to_check_csys_1), checked_csys_1 ->
              if mgs_data.MGS.one_mgs_std_subst = []
              then
                begin
                  (* Implies that no substitution was applied on the standard recipe variables. *)
                  let no_eq_form_csys = ref []
                  and solved_eq_form_csys = ref []
                  and eq_form_csys = ref [] in

                  let f_apply csys' = match create_eq_constructor_formula csys' index_kb recipe with
                    | NoEq -> no_eq_form_csys := csys' :: !no_eq_form_csys
                    | SolvedEq -> solved_eq_form_csys := csys' :: !solved_eq_form_csys
                    | UnsolvedEq form -> eq_form_csys := { csys' with unsolved_facts = UF.add_equality_formula csys'.unsolved_facts form } :: !eq_form_csys
                  in

                  List.iter f_apply checked_csys_1;
                  List.iter f_apply (csys::to_check_csys_1);

                  let application_on_IK = index_kb >= KR.size csys_set.knowledge_recipe in

                  let f_continuation_pos csys_set_2 f_next_2 =
                    let csys_list =
                      List.rev_map (fun csys' ->
                        let ikb =
                          if application_on_IK
                          then IK.remove csys'.incremented_knowledge index_kb
                          else csys'.incremented_knowledge
                        in
                        let rule_data =
                          if application_on_IK
                          then
                            begin
                              let (skel_checked_IK,skel_to_check_IK) = csys'.rule_data.skeletons_IK in
                              Config.debug (fun () -> if skel_to_check_IK <> [] then Config.internal_error "[constraint_system.ml >> equality_constructor] The skeletons should all be checked.");
                              let (equality_constructor_checked_IK,equality_constructor_to_check_IK) = csys'.rule_data.equality_constructor_IK in
                              { csys'.rule_data with
                                skeletons_IK = (remove_all_skeletons index_kb skel_checked_IK,[]);
                                equality_constructor_IK = (equality_constructor_checked_IK,remove_skeletons_cons index_kb equality_constructor_to_check_IK)
                              }
                            end
                          else
                            let (equality_constructor_checked_K,equality_constructor_to_check_K) = csys'.rule_data.equality_constructor_K in
                            { csys'.rule_data with equality_constructor_K = (equality_constructor_checked_K,remove_skeletons_cons index_kb equality_constructor_to_check_K) }
                        in
                        { csys' with rule_data = rule_data; incremented_knowledge = ikb }
                      ) csys_set_2.set
                    in
                    internal csys_set_2.eq_recipe (ref None) [] csys_list f_next_2
                  in

                  let f_continuation_neg csys_set_2 f_next_2 = internal csys_set_2.eq_recipe (ref None) [] csys_set_2.set f_next_2 in

                  sat_equality_formula f_continuation_pos f_continuation_neg { satf_solved = !solved_eq_form_csys; satf_unsolved = !eq_form_csys; satf_no_formula = !no_eq_form_csys; satf_eq_recipe = eq_recipe; satf_knowledge_recipe = csys_set.knowledge_recipe } f_next_1
                end
              else
                begin
                  let new_eq_rec_ref = ref eq_recipe in
                  Recipe_Variable.auto_cleanup_with_reset (fun f_next_2 ->
                    (* We link the variables of the mgs *)
                    List.iter (fun (v,r) -> Recipe_Variable.link_recipe v r) mgs_data.MGS.one_mgs_std_subst;

                    let vars_df = match !vars_df_ref with
                      | Some vlist -> vlist
                      | None -> Config.internal_error "[constraint_system.ml >> Rule.equality_constructor] The variables of DF should have been computed during the computation of one_mgs."
                    in

                    new_eq_rec_ref := Formula.R.wedge (Diseq.R.of_maybe_linked_variables vars_df mgs_data.MGS.one_mgs_fresh_existential_vars) !new_eq_rec_ref;

                    Variable.auto_cleanup_with_reset (fun f_next_3 ->
                      let no_eq_form_csys = ref []
                      and solved_eq_form_csys = ref []
                      and eq_form_csys = ref [] in

                      let f_apply csys = match MGS.apply_mgs_on_different_solved_csys csys csys_set.knowledge_recipe mgs_data.MGS.one_mgs_fresh_existential_vars with
                        | None -> ()
                        | Some csys' ->
                            match create_eq_constructor_formula csys' index_kb recipe with
                              | NoEq -> no_eq_form_csys := csys' :: !no_eq_form_csys
                              | SolvedEq -> solved_eq_form_csys := csys' :: !solved_eq_form_csys
                              | UnsolvedEq form -> eq_form_csys := { csys' with unsolved_facts = UF.add_equality_formula csys'.unsolved_facts form } :: !eq_form_csys
                      in

                      List.iter f_apply checked_csys_1;
                      List.iter f_apply (csys::to_check_csys_1);

                      let application_on_IK = index_kb >= KR.size csys_set.knowledge_recipe in

                      let f_continuation_pos csys_set_4 f_next_4 =
                        let csys_list =
                          List.rev_map (fun csys' ->
                            let ikb =
                              if application_on_IK
                              then IK.remove csys'.incremented_knowledge index_kb
                              else csys'.incremented_knowledge
                            in
                            let rule_data =
                              if application_on_IK
                              then
                                begin
                                  let (skel_checked_IK,skel_to_check_IK) = csys'.rule_data.skeletons_IK in
                                  Config.debug (fun () -> if skel_to_check_IK <> [] then Config.internal_error "[constraint_system.ml >> equality_constructor] The skeletons should all be checked (2).");
                                  let (equality_constructor_checked_IK,equality_constructor_to_check_IK) = csys'.rule_data.equality_constructor_IK in
                                  { csys'.rule_data with
                                    skeletons_IK = (remove_all_skeletons index_kb skel_checked_IK,[]);
                                    equality_constructor_IK = (equality_constructor_checked_IK,remove_skeletons_cons index_kb equality_constructor_to_check_IK)
                                  }
                                end
                              else
                                let (equality_constructor_checked_K,equality_constructor_to_check_K) = csys'.rule_data.equality_constructor_K in
                                { csys'.rule_data with equality_constructor_K = (equality_constructor_checked_K,remove_skeletons_cons index_kb equality_constructor_to_check_K) }
                            in
                            { csys' with rule_data = rule_data; incremented_knowledge = ikb }
                          ) csys_set_4.set
                        in
                        internal csys_set_4.eq_recipe (ref None) [] csys_list f_next_4
                      in

                      let f_continuation_neg csys_set_4 f_next_4 = internal csys_set_4.eq_recipe (ref None) [] csys_set_4.set f_next_4 in

                      sat_equality_formula f_continuation_pos f_continuation_neg { satf_solved = !solved_eq_form_csys; satf_unsolved = !eq_form_csys; satf_no_formula = !no_eq_form_csys; satf_eq_recipe = eq_recipe; satf_knowledge_recipe = csys_set.knowledge_recipe } f_next_3
                    ) f_next_2
                  ) (fun () ->
                    (* Negation of the mgs *)
                    internal !new_eq_rec_ref vars_df_ref checked_csys_1 (csys::to_check_csys_1) f_next_1
                  )
                end
      ) f_next_0
    in

    internal csys_set.eq_recipe (ref None) [] csys_set.set f_next

  let equality_constructor f_continuation csys_set (f_next:unit -> unit) =
    if csys_set.set = []
    then f_next ()
    else
      let one_csys = List.hd csys_set.set in
      let all_id = IK.get_all_index one_csys.incremented_knowledge in
      if all_id = []
      then f_continuation csys_set f_next
      else
        let csys_list =
          List.rev_map (fun csys ->
            Config.debug (fun () ->
              if csys.rule_data.equality_constructor_IK <> ([],[])
              then Config.internal_error "[constraint_system.ml >> initialise_equality_constructor] The equality constructor skeletons for IK should be empty.";
            );
            match csys.rule_data.equality_constructor_K with
              | (checked_K,[]) -> { csys with rule_data = { csys.rule_data with equality_constructor_IK = ([],all_id); equality_constructor_K = ([],checked_K) } }
              | _ -> Config.internal_error "[constraint_system.ml >> initialise_equality_constructor] The equality constructor skeletons for K should be empty.";
          ) csys_set.set
        in

        internal_equality_constructor f_continuation { csys_set with set = csys_list } f_next

  (*** Main functions ***)

  let apply_rules_after_input exists_private f_continuation =
    if exists_private
    then sat (sat_non_deducible_terms (sat_disequation f_continuation))
    else sat (sat_disequation f_continuation)

  let apply_rules_after_output exists_private f_continuation =
    if exists_private
    then sat (sat_non_deducible_terms (sat_disequation (split_data_constructor (normalisation_deduction_consequence (rewrite (equality_constructor f_continuation))))))
    else sat (sat_disequation (split_data_constructor (normalisation_deduction_consequence (rewrite (equality_constructor f_continuation)))))

  let apply_rules_after_input =
    if Config.record_time
    then
      (fun exists_private f_continuation ->
        if exists_private
        then
          record Statistic.time_sat (sat (
            record Statistic.time_non_deducible_term (sat_non_deducible_terms (
              record Statistic.time_sat_disequation (sat_disequation (
                record Statistic.time_other f_continuation
              ))
            ))
          ))
        else
          record Statistic.time_sat (sat (
            record Statistic.time_sat_disequation (sat_disequation (
              record Statistic.time_other f_continuation
            ))
          ))
      )
    else apply_rules_after_input

  let apply_rules_after_output =
    if Config.record_time
    then
      (fun exists_private f_continuation ->
        if exists_private
        then
          record Statistic.time_sat (sat (
            record Statistic.time_non_deducible_term (sat_non_deducible_terms (
              record Statistic.time_sat_disequation (sat_disequation (
                record Statistic.time_split_data_constructor (split_data_constructor (
                  record Statistic.time_normalisation_deduction_consequence (normalisation_deduction_consequence (
                    record Statistic.time_rewrite (rewrite (
                      record Statistic.time_equality_constructor (equality_constructor (
                        record Statistic.time_other f_continuation
                      ))
                    ))
                  ))
                ))
              ))
            ))
          ))
        else
          record Statistic.time_sat (sat (
            record Statistic.time_sat_disequation (sat_disequation (
              record Statistic.time_split_data_constructor (split_data_constructor (
                record Statistic.time_normalisation_deduction_consequence (normalisation_deduction_consequence (
                  record Statistic.time_rewrite (rewrite (
                    record Statistic.time_equality_constructor (equality_constructor (
                      record Statistic.time_other f_continuation
                    ))
                  ))
                ))
              ))
            ))
          ))
      )
    else apply_rules_after_output

  (*** Additional function ***)

  let rec mark_variables = function
    | Var v ->
        begin
          match v.link with
          | TLink t -> mark_variables t
          | NoLink -> v.link <- SLink; Variable.currently_linked := v :: !Variable.currently_linked
          | SLink -> ()
          | _ -> Config.internal_error "[constraint_system.ml >> mark_variables] Unexpected link."
        end
    | Func(_,args) -> List.iter mark_variables args
    | _ -> ()

  let rec record_marked_variables f_next = function
    | Var { link = NoLink; _ } -> f_next ()
    | Var { link = SLink; _ } -> ()
    | Var { link = TLink t; _ } -> record_marked_variables f_next t
    | Var _ -> Config.internal_error "[constraint_system.ml >> record_marked_variables] Unexpected link."
    | _ -> Config.internal_error "[constraint_system.ml >> record_marked_variables] Unexpected term."

  let rec instantiate_useless_deduction_facts_list rec_vars = function
    | [] -> rec_vars
    | csys::q ->
        let rec_vars' =
          Variable.auto_cleanup_with_reset_notail (fun () ->
            K.iter_term mark_variables csys.knowledge;
            IK.iter_term mark_variables csys.incremented_knowledge;
            List.iter (fun (_,t) -> mark_variables t) csys.original_substitution;
            let rec_vars1 = ref [] in
            DF.iter (fun bfact ->
              record_marked_variables (fun () ->
                if List.memq bfact.bf_var rec_vars
                then rec_vars1 := bfact.bf_var :: !rec_vars1
              ) bfact.bf_term
            ) csys.deduction_facts;
            !rec_vars1
          )
        in
        if rec_vars' = []
        then []
        else instantiate_useless_deduction_facts_list rec_vars' q

  let instantiate_useless_deduction_facts f_continuation csys_set f_next =
    Config.debug (fun () ->
      Config.log_in_debug Config.Constraint_solving (Printf.sprintf "[constraint_system.ml >> Rule] instantiate_useless_deduction_facts : Nb csys = %d" (List.length csys_set.set));

      Set.debug_check_structure "[generic_equivalence >> apply_one_transition_and_rules_private]" csys_set;
      Config.log_in_debug Config.Constraint_systems ("Eq recipe = "^(Formula.R.display Terminal csys_set.eq_recipe));
      List.iter (fun csys ->
        Config.log_in_debug Config.Constraint_systems (display_constraint_system 1 csys_set.knowledge_recipe csys)
      ) csys_set.set
    );

    if csys_set.set = []
    then f_continuation csys_set f_next
    else
      let csys = List.hd csys_set.set in
      if DF.is_empty csys.deduction_facts
      then f_continuation csys_set f_next
      else
        let first_rec_vars =
          Variable.auto_cleanup_with_reset_notail (fun () ->
            K.iter_term mark_variables csys.knowledge;
            IK.iter_term mark_variables csys.incremented_knowledge;
            List.iter (fun (_,t) -> mark_variables t) csys.original_substitution;
            let rec_vars = ref [] in
            DF.iter (fun bfact ->
              record_marked_variables (fun () -> rec_vars := bfact.bf_var :: !rec_vars) bfact.bf_term
            ) csys.deduction_facts;
            !rec_vars
          )
        in
        if first_rec_vars = []
        then f_continuation csys_set f_next
        else
          let final_rec_vars = instantiate_useless_deduction_facts_list first_rec_vars (List.tl csys_set.set) in
          Recipe_Variable.auto_cleanup_with_reset (fun f_next1 ->
            Symbol.auto_cleanup_attacker_name (fun f_next2 ->
              List.iter (fun x ->
                let f = Symbol.fresh_attacker_name () in
                Recipe_Variable.link_recipe x (RFunc(f,[]))
              ) final_rec_vars;

              let eq_recipe = Formula.R.instantiate_and_normalise csys_set.eq_recipe in

              Config.debug (fun () ->
                if eq_recipe = Formula.R.Bot
                then Config.internal_error "[constraint_system.ml >> instantiate_useless_deduction_facts] Should not be bot."
              );

              let csys_list =
                List.rev_map (fun csys ->
                  { csys with deduction_facts = DF.remove_all_linked_variables csys.deduction_facts }
                ) csys_set.set
              in

              f_continuation { eq_recipe = eq_recipe; set = csys_list; knowledge_recipe = csys_set.knowledge_recipe } f_next2
            ) f_next1
          ) f_next
end

(***********************************************
***    Rules for ground constraint system    ***
************************************************)

module Rule_ground = struct

  exception WitnessMessage of recipe
  exception WitnessEquality of recipe * recipe

  let find_witness = ref false

  (**** The normalisation rule for data constructor *)

  let rec find_pattern = function
    | Var { link = TLink t; _ } -> find_pattern t
    | Var _ -> Config.internal_error "[constraint_system.ml >> Rule_ground.find_pattern] The term should be ground."
    | Func(f,_) when f.cat = Tuple -> Some f
    | _ -> None

  (* When [witness = true], the list [csys_list] only contains one element. *)
  let rec split_data_constructor (f_continuation: 'a t -> 'b t list -> 'c) kbr target_csys csys_list =
    Config.debug (fun () ->
      Config.log_in_debug Config.Constraint_solving (Printf.sprintf "[constraint_system.ml >> Rule] Rule split data constructor : Nb csys = %d" (List.length csys_list));
      Config.log_in_debug Config.Constraint_systems (Printf.sprintf "Target constraint system:%s" (display_constraint_system 1 kbr target_csys));
      Config.log_in_debug Config.Constraint_systems "Other constraint systems:";
      List.iter (fun csys -> Config.log_in_debug Config.Constraint_systems (display_constraint_system 1 kbr csys)) csys_list
    );
    match UF.pop_deduction_fact_to_check_for_pattern target_csys.unsolved_facts with
      | None -> f_continuation target_csys csys_list
      | Some dfact ->
          let target_csys_1 = { target_csys with unsolved_facts = UF.validate_head_deduction_facts_for_pattern target_csys.unsolved_facts } in
          let pattern = find_pattern dfact.df_term in
          let csys_list_ref = ref [] in
          List.iter (fun csys ->
            let dfact_to_check = match UF.pop_deduction_fact_to_check_for_pattern csys.unsolved_facts with
              | Some df -> df
              | _ -> Config.internal_error "[constraint_system.ml >> Rule_ground.split_data_constructor] The should be a deduction fact to check for pattern."
            in
            let pattern' = find_pattern dfact_to_check.df_term in
            match pattern,pattern' with
              | None, None -> csys_list_ref := { csys with unsolved_facts = UF.validate_head_deduction_facts_for_pattern csys.unsolved_facts } :: !csys_list_ref
              | Some f, Some f' when f == f' -> csys_list_ref := { csys with unsolved_facts = UF.validate_head_deduction_facts_for_pattern csys.unsolved_facts } :: !csys_list_ref
              | Some f, _ | _, Some f ->
                  if !find_witness
                  then
                    begin
                      if f.arity = 0
                      then raise (WitnessEquality (RFunc(f,[]),dfact.df_recipe))
                      else
                        let proj = List.hd (Symbol.get_projections f) in
                        raise (WitnessMessage (RFunc(proj,[dfact.df_recipe])))
                    end
          ) csys_list;
          split_data_constructor f_continuation kbr target_csys_1 !csys_list_ref

  (**** The rule for adding element in the knowledge base ****)

  (* Return true when it needs to be added. False when it needs to be removed. *)
  let exploration_normalisation_deduction_consequence kbr target_csys csys_list =

    let rec explore_no_consequence only_pure prev_csys = function
      | [] -> not only_pure, prev_csys
      | csys::q_csys ->
          let t = (UF.pop_deduction_fact csys.unsolved_facts).df_term in
          match t with
            | Name { pure_fresh_n = true; _ } -> explore_no_consequence only_pure (csys::prev_csys) q_csys
            | _ ->
                match IK.consequence_term kbr csys.knowledge csys.incremented_knowledge csys.deduction_facts t with
                  | None -> explore_no_consequence false (csys::prev_csys) q_csys
                  | Some r ->
                      if !find_witness
                      then raise (WitnessEquality(r,(UF.pop_deduction_fact csys.unsolved_facts).df_recipe));

                      explore_no_consequence only_pure prev_csys q_csys
    in

    let rec explore_consequence recipe prev_csys = function
      | [] -> prev_csys
      | csys::q_csys ->
          let t = (UF.pop_deduction_fact csys.unsolved_facts).df_term in
          let t' = IK.consequence_recipe csys.knowledge csys.incremented_knowledge csys.deduction_facts recipe in
          if Term.is_equal t t'
          then explore_consequence recipe (csys::prev_csys) q_csys
          else
            begin
              if !find_witness
              then raise (WitnessEquality(recipe,(UF.pop_deduction_fact csys.unsolved_facts).df_recipe));

              explore_consequence recipe prev_csys q_csys
            end
    in

    let t_target = (UF.pop_deduction_fact target_csys.unsolved_facts).df_term in
    match t_target with
      | Name { pure_fresh_n = true; _ } -> explore_no_consequence true [] csys_list
      | _ ->
          match IK.consequence_term kbr target_csys.knowledge target_csys.incremented_knowledge target_csys.deduction_facts t_target with
            | None -> explore_no_consequence false [] csys_list
            | Some r -> false, explore_consequence r [] csys_list

  let add_skeletons_in_rule_data csys new_term index_new_elt =
    let new_skeletons = List.map (fun index_skel -> (index_new_elt,index_skel)) (Rewrite_rules.get_possible_skeletons_for_terms new_term) in
    let (skeletons_checked_IK,skeletons_to_check_IK) = csys.rule_data.skeletons_IK in
    let (skeletons_checked_K,skeletons_to_check_K) = csys.rule_data.skeletons_K in
    let new_skeletons_to_check_K = List.rev_append skeletons_to_check_K skeletons_checked_K in
    let new_skeletons_to_check_IK = List.rev_append new_skeletons (List.rev_append skeletons_to_check_IK skeletons_checked_IK) in

    { csys.rule_data with
      skeletons_K = ([],new_skeletons_to_check_K);
      skeletons_IK = ([],new_skeletons_to_check_IK)
    }

  (** Purpose : Check whether a deduction fact is consequence or not of the knowledge base and incremented knowledge base.
     Input : Only deductions facts (no formula nor equality) and same amount. (Can we have several ?)
     Output :
      - When no consequence -> Adding in SDF and followed by equality_SDF and then back to [normalisation_deduction_consequence]
      - When there are consequence -> add an equality formula and check it.
      *)
  let rec normalisation_deduction_consequence f_continuation kbr (target_csys:'a t) (csys_list:'b t list) =
    Config.debug (fun () ->
      Config.log_in_debug Config.Constraint_solving (Printf.sprintf "[constraint_system.ml >> Rule] Rule normalisation_deduction_consequence : Nb csys = %d" (List.length csys_list));
      Config.log_in_debug Config.Constraint_systems (Printf.sprintf "Target constraint system:%s" (display_constraint_system 1 kbr target_csys));
      Config.log_in_debug Config.Constraint_systems "Other constraint systems:";
      List.iter (fun csys -> Config.log_in_debug Config.Constraint_systems (display_constraint_system 1 kbr csys)) csys_list
    );
    if UF.exists_deduction_fact target_csys.unsolved_facts
    then
      let (to_add,csys_list1) = exploration_normalisation_deduction_consequence kbr target_csys csys_list in

      if to_add
      then
        begin
          let index_new_elt = IK.get_next_index target_csys.incremented_knowledge in
          let target_csys1 =
            let (dfact,uf) = UF.pop_and_remove_deduction_fact target_csys.unsolved_facts in
            { target_csys with
              unsolved_facts = uf;
              incremented_knowledge = IK.add target_csys.incremented_knowledge dfact;
              rule_data = add_skeletons_in_rule_data target_csys dfact.df_term index_new_elt
            }
          in
          let csys_list2 =
            List.rev_map (fun csys ->
              let (dfact,uf) = UF.pop_and_remove_deduction_fact csys.unsolved_facts in
              { csys with
                unsolved_facts = uf;
                incremented_knowledge = IK.add csys.incremented_knowledge dfact;
                rule_data = add_skeletons_in_rule_data csys dfact.df_term index_new_elt
              }
            ) csys_list1
          in
          normalisation_deduction_consequence f_continuation kbr target_csys1 csys_list2
        end
      else
        begin
          let csys_list2 =
            List.rev_map (fun csys' ->
              { csys' with unsolved_facts = UF.remove_head_deduction_fact csys'.unsolved_facts}
            ) csys_list1
          in
          let target_csys1 = { target_csys with unsolved_facts = UF.remove_head_deduction_fact target_csys.unsolved_facts} in
          normalisation_deduction_consequence f_continuation kbr target_csys1 csys_list2
        end
    else f_continuation target_csys csys_list

  (*** The rule rewrite ***)


  let update_skeleton_history dfact csys =

    let f = Recipe.root dfact.df_recipe in

    let rec replace_history = function
      | [] -> Config.internal_error "[constraint_system.ml >> Rule.update_skeleton] Unexpected case"
      | hist::q when hist.destructor == f ->
          let diseq = Rewrite_rules.generate_mixed_formulas_for_skeletons csys.knowledge csys.incremented_knowledge csys.deduction_facts hist.fst_vars hist.snd_vars dfact.df_recipe in
          { hist with diseq = Formula.M.wedge diseq hist.diseq }::q
      | hist::q -> hist::(replace_history q)
    in

    replace_history csys.rule_data.history_skeleton

  let rewrite (f_continuation:'a t -> 'b t list -> 'c) kbr (target_csys:'a t) (csys_list:'b t list) =
    Config.debug (fun () ->
      Config.log_in_debug Config.Constraint_solving (Printf.sprintf "[constraint_system.ml >> Rule] Rule rewrite : Nb csys = %d" (List.length csys_list));
      Config.log_in_debug Config.Constraint_systems (Printf.sprintf "Target constraint system:%s" (display_constraint_system 1 kbr target_csys));
      Config.log_in_debug Config.Constraint_systems "Other constraint systems:";
      List.iter (fun csys -> Config.log_in_debug Config.Constraint_systems (display_constraint_system 1 kbr csys)) csys_list;
    );

    let rec internal target_csys checked_csys to_check_csys = match Rule.exploration_rewrite ~ground:true kbr Formula.R.Top (ref None) checked_csys to_check_csys with
      | None, checked_csys_1 -> f_continuation target_csys checked_csys_1
      | Some(_,_,_,recipe,_,to_check_csys_1), checked_csys_1 ->
          (* We found an application of a destructor that is not applicable to the target csys. *)
          if !find_witness
          then raise (WitnessMessage recipe);

          internal target_csys checked_csys_1 to_check_csys_1
    in

    let rec internal_target target_csys csys_list = match Rule.exploration_rewrite ~ground:true kbr Formula.R.Top (ref None) [] [target_csys] with
      | None, [target_csys1] -> internal target_csys1 [] csys_list
      | Some(index_kb,index_skel,mgs_data,recipe,target_csys1,[]),[] ->
          Config.debug (fun () ->
            if mgs_data.MGS.one_mgs_std_subst <> []
            then Config.internal_error "[constraint_system.ml >> Rune_ground.rewrite] The mgs should be ground."
          );

          let size_K = KR.size kbr in
          let application_on_IK = index_kb >= size_K in
          let removal_allowed = application_on_IK && (Rewrite_rules.get_skeleton index_skel).Rewrite_rules.removal_allowed in
          let no_history = (Rewrite_rules.get_skeleton index_skel).Rewrite_rules.no_history in

          let update_constraint_system csys fact =
            let new_ik =
              if removal_allowed
              then IK.remove csys.incremented_knowledge index_kb
              else csys.incremented_knowledge
            in
            let rule_data =
              if no_history
              then
                if application_on_IK
                then
                  let (skels_checked,skels_to_check) = csys.rule_data.skeletons_IK in
                  { csys.rule_data with skeletons_IK = (skels_checked,Rule.remove_skeletons (index_kb,index_skel) skels_to_check) }
                else
                  let (skels_checked,skels_to_check) = csys.rule_data.skeletons_K in
                  { csys.rule_data with skeletons_K = (skels_checked,Rule.remove_skeletons (index_kb,index_skel) skels_to_check) }
              else { csys.rule_data with history_skeleton = update_skeleton_history fact csys }
            in
            { csys with
              incremented_knowledge = new_ik;
              rule_data = rule_data;
              unsolved_facts = UF.add_deduction_fact csys.unsolved_facts fact
            }
          in

          let target_csys2 = match Rule.create_generic_skeleton_formula target_csys1 index_skel recipe with
            | Rule.FoundFact fact -> update_constraint_system target_csys1 fact
            | _ -> Config.internal_error "[constraint_system.ml >> Rule_ground.rewrite] We should have found a fact"
          in

          let csys_list_ref = ref [] in
          List.iter (fun csys -> match Rule.create_generic_skeleton_formula csys index_skel recipe with
            | Rule.FoundFact fact ->
                let csys' = update_constraint_system csys fact in
                csys_list_ref := csys' :: !csys_list_ref
            | Rule.NoFormula ->
                if !find_witness
                then raise (WitnessMessage recipe)
            | Rule.Unsolved _ -> Config.internal_error "[constraint_system.ml >> Rule_ground.rewrite] Since the frame is ground, there should not be unsolved formula."
          ) csys_list;

          split_data_constructor (normalisation_deduction_consequence internal_target kbr) kbr target_csys2 !csys_list_ref
      | _ -> Config.internal_error "[constraint_system.ml >> Rule_ground.rewrite] Unexpected number of constraint system returned by exploration."
    in

    internal_target target_csys csys_list

  (*** The rule consequence ***)

  let internal_equality_constructor f_continuation kbr (target_csys:'a t) (csys_list:'b t list) =
    Config.debug (fun () ->
      Config.log_in_debug Config.Constraint_solving (Printf.sprintf "[constraint_system.ml >> Rule] Rule equality_constructor : Nb csys = %d" (List.length csys_list));
      Config.log_in_debug Config.Constraint_systems (Printf.sprintf "Target constraint system:%s\n" (display_constraint_system 1 kbr target_csys));
      Config.log_in_debug Config.Constraint_systems "Other constraint systems:\n";
      List.iter (fun csys -> Config.log_in_debug Config.Constraint_systems (display_constraint_system 1 kbr csys)) csys_list
    );

    let rec internal target_csys checked_csys to_check_csys =
      match Rule.exploration_equality_constructor ~ground:true kbr Formula.R.Top (ref None) checked_csys to_check_csys with
      | None, checked_csys_1 -> f_continuation target_csys checked_csys_1
      | Some(recipe,_,index_kb,csys,to_check_csys_1), checked_csys_1 ->
          (* We found an application of a destructor that is not applicable to the target csys. *)
          if !find_witness
          then raise (WitnessEquality(recipe,IK.get_recipe kbr csys.incremented_knowledge index_kb));

          internal target_csys checked_csys_1 to_check_csys_1
    in

    let rec internal_target target_csys csys_list  = match Rule.exploration_equality_constructor ~ground:true kbr Formula.R.Top (ref None) [] [target_csys] with
      | None, [target_csys1] -> internal target_csys1 [] csys_list
      | Some(recipe,mgs_data,index_kb,target_csys_1,[]), [] ->
          Config.debug (fun () ->
            if mgs_data.MGS.one_mgs_std_subst <> []
            then Config.internal_error "[constraint_system.ml >> Rune_ground.internal_equality_constructor] The mgs should be ground."
          );

          let application_on_IK = index_kb >= KR.size kbr in

          let csys_list_ref = ref [] in

          List.iter (fun csys -> match Rule.create_eq_constructor_formula csys index_kb recipe with
            | Rule.NoEq ->
                if !find_witness
                then raise (WitnessEquality(recipe,IK.get_recipe kbr csys.incremented_knowledge index_kb))
            | Rule.SolvedEq ->
                let ikb =
                  if application_on_IK
                  then IK.remove csys.incremented_knowledge index_kb
                  else csys.incremented_knowledge
                in
                let rule_data =
                  if application_on_IK
                  then
                    begin
                      let (skel_checked_IK,skel_to_check_IK) = csys.rule_data.skeletons_IK in
                      Config.debug (fun () -> if skel_to_check_IK <> [] then Config.internal_error "[constraint_system.ml >> equality_constructor] The skeletons should all be checked.");
                      let (equality_constructor_checked_IK,equality_constructor_to_check_IK) = csys.rule_data.equality_constructor_IK in
                      { csys.rule_data with
                        skeletons_IK = (Rule.remove_all_skeletons index_kb skel_checked_IK,[]);
                        equality_constructor_IK = (equality_constructor_checked_IK,Rule.remove_skeletons_cons index_kb equality_constructor_to_check_IK)
                      }
                    end
                  else
                    let (equality_constructor_checked_K,equality_constructor_to_check_K) = csys.rule_data.equality_constructor_K in
                    { csys.rule_data with equality_constructor_K = (equality_constructor_checked_K,Rule.remove_skeletons_cons index_kb equality_constructor_to_check_K) }
                in
                csys_list_ref := { csys with rule_data = rule_data; incremented_knowledge = ikb } :: !csys_list_ref
            | _ -> Config.internal_error "[constraint_system.ml >> Rule_ground.internal_equality_constructor] Unexpected case with ground constraint system."
          ) csys_list;

          internal_target target_csys_1 !csys_list_ref
      | _ -> Config.internal_error "[constraint_system.ml >> Rule_ground.internal_equality_constructor] Unexpected number of constraint system returned by exploration."
    in

    internal_target target_csys csys_list

  let initialise_equality_constructor f_continuation (target_csys:'a t) (csys_list:'b t list) =

    let all_id = IK.get_all_index target_csys.incremented_knowledge in

    let target_csys1 =
      Config.debug (fun () ->
        if target_csys.rule_data.equality_constructor_IK <> ([],[])
        then Config.internal_error "[constraint_system.ml >> Rule_ground.initialise_equality_constructor] The equality constructor skeletons for IK should be empty.";
      );
      match target_csys.rule_data.equality_constructor_K with
        | (checked_K,[]) -> { target_csys with rule_data = { target_csys.rule_data with equality_constructor_IK = ([],all_id); equality_constructor_K = ([],checked_K) } }
        | _ -> Config.internal_error "[constraint_system.ml >> Rule_ground.initialise_equality_constructor] The equality constructor skeletons for K should be empty."
    in

    let csys_list1 =
      List.rev_map (fun csys ->
        Config.debug (fun () ->
          if csys.rule_data.equality_constructor_IK <> ([],[])
          then Config.internal_error "[constraint_system.ml >> Rule_ground.initialise_equality_constructor] The equality constructor skeletons for IK should be empty (2).";
        );
        match csys.rule_data.equality_constructor_K with
          | (checked_K,[]) -> { csys with rule_data = { csys.rule_data with equality_constructor_IK = ([],all_id); equality_constructor_K = ([],checked_K) } }
          | _ -> Config.internal_error "[constraint_system.ml >> Rule_ground.initialise_equality_constructor] The equality constructor skeletons for K should be empty (2).";
      ) csys_list
    in

    f_continuation target_csys1 csys_list1

  let equality_constructor f_continuation kbr = initialise_equality_constructor (internal_equality_constructor f_continuation kbr)

  (*** Main function ***)

  let apply_rules f_continuation kbr  =
    split_data_constructor (normalisation_deduction_consequence (rewrite (equality_constructor f_continuation kbr) kbr) kbr) kbr

  type 'a result_static_equivalence =
    | Static_equivalent of KR.t * 'a t * 'a t
    | Witness_message of recipe
    | Witness_equality of recipe * recipe

  let apply_rules_for_static_equivalence kbr csys_1 csys_2 =
    let f_continuation csys_1' csys_list = match csys_list with
      | [ csys_2' ] ->
          let (csys_1'',kbr',ikb,assoc_id) = prepare_for_solving_procedure_first_ground kbr csys_1' in
          let csys_2'' = prepare_for_solving_procedure_others_ground ikb assoc_id csys_2' in
          find_witness := false;
          Static_equivalent (kbr', csys_1'',csys_2'')
      | _ -> Config.internal_error "[constraint_system.ml >> Rule_ground.apply_rules_for_static_equivalence] Unexpected number of constraint system."
    in

    find_witness := true;
    try
      split_data_constructor (normalisation_deduction_consequence (rewrite (equality_constructor f_continuation kbr) kbr) kbr) kbr csys_1 [csys_2]
    with
      | WitnessMessage r ->
          find_witness := false;
          Witness_message (Recipe.instantiate r)
      | WitnessEquality (r1,r2) ->
          find_witness := false;
          Witness_equality (Recipe.instantiate r1,Recipe.instantiate r2)

  let is_term_deducible kbr csys t = match t with
    | Func(f,[]) when f.public -> true
    | _ -> (IK.consequence_term kbr csys.knowledge csys.incremented_knowledge csys.deduction_facts t) <> None

  let recipe_of_deducible_term kbr csys t = match t with
    | Func(f,[]) when f.public -> Some (RFunc(f,[]))
    | _ ->
        match IK.consequence_term kbr csys.knowledge csys.incremented_knowledge csys.deduction_facts t with
          | None -> None
          | Some r -> Some (Recipe.instantiate r)

  let solve kbr csys =
    let data = ref (kbr,csys) in
    apply_rules (fun csys' _ ->
      let (csys',kbr',_,_) = prepare_for_solving_procedure_first_ground kbr csys' in
      data := kbr',csys'
    ) kbr csys [];
    !data
 end
