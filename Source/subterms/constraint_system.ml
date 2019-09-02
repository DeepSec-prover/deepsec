open Types
open Term
open Formula
open Data_structure
open Extensions

(*************************************
***       Constraint systems       ***
**************************************)

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

    eq_term : Formula.Term.t;
    eq_recipe : Formula.Recipe.t;

    eq_uniformity : Formula.Term.t;

    (* Original variables and names *)

    original_variables : variable list;
    original_names : name list
  }

exception Bot

(********* Access  ********)

let get_additional_data csys = csys.additional_data

(********* Generators *********)

let empty data =
  {
    additional_data = data;
    size_frame = 0;
    deduction_facts = DF.empty;
    non_deducible_terms = [];
    knowledge = K.empty;
    incremented_knowledge = IK.empty;
    unsolved_facts = UF.empty;
    eq_term = Formula.Term.Top;
    eq_recipe = Formula.Recipe.Top;
    eq_uniformity = Formula.Term.Top;
    original_variables = [];
    original_names = []
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
  { csys with eq_term = Formula.Term.wedge_conjunction diseq_list csys.eq_term }

let add_non_deducible_terms csys l =
  Config.debug (fun () ->
    if csys.non_deducible_terms <> []
    then Config.internal_error "[constraint_system.ml >> add_non_deducible_terms] The current list should be empty."
  );
  { csys with non_deducible_terms = l }

let replace_additional_data csys data =
  { csys with additional_data = data }

(****************************************
***       Most general solutions      ***
*****************************************)

module MGS = struct

  type simplified_constraint_system =
    {
      simp_deduction_facts : DF.t;

      simp_knowledge : K.t;
      simp_incremented_knowledge : IK.t;

      simp_eq_term : Formula.Term.t;
      simp_eq_recipe : Formula.Recipe.t;
      simp_eq_uniformity : Formula.Term.t;
      simp_eq_skeleton : Formula.Mixed.t
    }

  (***** Generators ******)

  let simple_of csys =
    {
      simp_deduction_facts = csys.deduction_facts;
      simp_knowledge = csys.knowledge;
      simp_incremented_knowledge = csys.incremented_knowledge;
      simp_eq_term = csys.eq_term;
      simp_eq_recipe = csys.eq_recipe;
      simp_eq_uniformity = csys.eq_uniformity;
      simp_eq_skeleton = Formula.Mixed.Top
    }

  (***** Compute MGS *****)

  type mgs_data =
    {
      mgs_deduction_facts : DF.t;
      mgs_eq_term : Formula.Term.t;
      mgs_eq_recipe : Formula.Recipe.t;
      mgs_eq_uniformity : Formula.Term.t;
      mgs_eq_skeleton : Formula.Mixed.t
    }

  let compute_all csys f_found_mgs f_next =
    let found_mgs = ref false in

    let rec apply_rules df eq_term eq_rec eq_uni f_next_0 =
      Recipe_Variable.auto_cleanup (fun f_next_1 ->
        match DF.compute_mgs_applicability df with
          | DF.Solved ->
              found_mgs := true;
              f_found_mgs { mgs_deduction_facts = df; mgs_eq_term = eq_term; mgs_eq_recipe = eq_rec; mgs_eq_uniformity =  eq_uni; mgs_eq_skeleton = Formula.Mixed.Top } f_next_1
          | DF.UnifyVariables df ->
              let eq_rec' = Formula.Recipe.instantiate_and_normalise eq_rec in
              if eq_rec' = Formula.Recipe.Bot
              then f_next_1 ()
              else f_found_mgs { mgs_deduction_facts = df; mgs_eq_term = eq_term; mgs_eq_recipe = eq_rec'; mgs_eq_uniformity =  eq_uni; mgs_eq_skeleton = Formula.Mixed.Top } f_next_1
          | DF.UnsolvedFact(bfact,df',unif) ->
              let x = bfact.bf_var
              and t = bfact.bf_term in

              Config.debug (fun () ->
                if x.type_r = Recipe_Variable.infinite_type
                then Config.internal_error "[constraint_system.ml >> MGS.compute_all] There should not be variable with infinite type when computing all mgs."
              );

              match t with
                | Func(f,[]) when f.public ->
                    let r = RFunc(f,[]) in
                    if unif
                    then
                      begin
                        Recipe_Variable.link_recipe x r;
                        let eq_rec' = Formula.Recipe.instantiate_and_normalise eq_rec in
                        if eq_rec' = Formula.Recipe.Bot
                        then f_next_1 ()
                        else apply_rules df' eq_term eq_rec' eq_uni f_next_1
                      end
                    else
                      let eq_rec' = Formula.Recipe.instantiate_and_normalise_constructor x r eq_rec in
                      if eq_rec' = Formula.Recipe.Bot
                      then f_next_1 ()
                      else
                        begin
                          Recipe_Variable.link_recipe x r;
                          apply_rules df' eq_term eq_rec' eq_uni f_next_1
                        end
                | Name { deducible_n = None ; _ } ->
                    (* It indicates that the name is not deducible *)
                    f_next_1 ()
                | Name { deducible_n = Some r; _ } ->
                    (* It indicates that the name occurs directly in the knowledge base or
                       the incremented knowledge base. *)
                    if unif
                    then
                      begin
                        Recipe_Variable.link_recipe x r;
                        let eq_rec' = Formula.Recipe.instantiate_and_normalise eq_rec in
                        if eq_rec' = Formula.Recipe.Bot
                        then f_next_1 ()
                        else apply_rules df' eq_term eq_rec' eq_uni f_next_1
                      end
                    else
                      let eq_rec' = Formula.Recipe.instantiate_and_normalise_constructor x r eq_rec in
                      if eq_rec' = Formula.Recipe.Bot
                      then f_next_1 ()
                      else
                        begin
                          Recipe_Variable.link_recipe x r;
                          apply_rules df' eq_term eq_rec' eq_uni f_next_1
                        end
                | _ ->
                    (* Compute_all is only used for the rule [sat],
                       in which case incremented knowledge is empty. *)
                    K.find_unifier_with_recipe csys.knowledge t x.type_r (fun r f_next_2 ->
                      
                    ) (fun () ->

                    )

      ) f_next_0

    in

    ()
end
