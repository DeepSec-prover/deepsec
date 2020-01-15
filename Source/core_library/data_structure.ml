open Types
open Term
open Formula
open Extensions
open Display

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

type deduction_formula =
  {
    df_head : deduction_fact;
    df_equations : (variable * term) list
  }

type equality_formula = (variable * term) list

let display_deduction_fact ded_fact =
  Printf.sprintf "%s |- %s" (Recipe.display Display.Terminal ded_fact.df_recipe) (Term.display Display.Terminal ded_fact.df_term)

let display_equations eq =
  Display.display_list (fun (x,t) -> (Variable.display Display.Terminal x)^" = "^(Term.display Display.Terminal t)) (" "^(Display.wedge Display.Terminal)^" ") eq

let display_deduction_formula ded_form =
  Printf.sprintf "%s <= %s" (display_deduction_fact ded_form.df_head) (display_equations ded_form.df_equations)

let display_equality_formula eq =
  Printf.sprintf "[%s] <= %s" (Display.eqf Display.Terminal) (display_equations eq)

(************************)

let instantiate_deduction_formula_to_fact form =
  let tmp = !Variable.currently_linked in
  Variable.currently_linked := [];

  List.iter (fun (x,t) -> Term.unify (Var x) t) form.df_equations;

  let fact = { df_recipe = form.df_head.df_recipe; df_term = Term.instantiate form.df_head.df_term } in

  List.iter (fun v -> v.link <- NoLink) !Variable.currently_linked;
  Variable.currently_linked := tmp;

  fact

(*********************************
***       Deduction facts      ***
**********************************)

module DF = struct

  type t = (int * basic_fact list) list

  (******* Generation *******)

  let empty : t = []

  let display df =
    let acc = ref "" in

    List.iter (fun (_,bfact_l) ->
      List.iter (fun bfact ->
        acc := !acc ^ (Printf.sprintf "%s |- %s, " (Recipe_Variable.display Display.Terminal ~display_type:true bfact.bf_var) (Term.display Display.Terminal bfact.bf_term))
      ) bfact_l
    ) df;

    !acc

  let add (df:t) bfact =
    let type_r = bfact.bf_var.type_r in
    let rec explore = function
      | [] -> [type_r, [bfact]]
      | ((i,_) as head)::q when i < type_r -> head :: (explore q)
      | (i,bfact_list)::q when i = type_r -> (i,bfact::bfact_list)::q
      | df' -> (type_r, [bfact])::df'
    in
    explore df

  let add_multiple (df:t) bfact_list =
    if bfact_list = []
    then df
    else
      let type_r = (List.hd bfact_list).bf_var.type_r in
      let rec explore = function
        | [] -> [type_r,bfact_list]
        | ((i,_) as head)::q when i < type_r -> head :: (explore q)
        | (i,bfact_list')::q when i = type_r -> (i,List.rev_append bfact_list bfact_list')::q
        | df' -> (type_r, bfact_list)::df'
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

    (explore df:t)

  let remove_all_linked_variables (df:t) =

    let rec explore_bfact_list bfact_list = match bfact_list with
      | [] -> bfact_list
      | bfact::q when bfact.bf_var.link_r = RNoLink ->
          let q' = explore_bfact_list q in
          if q == q'
          then bfact_list
          else bfact::q'
      | _::q -> explore_bfact_list q
    in

    let rec explore df = match df with
      | [] -> df
      | ((i,bfact_list) as head)::q ->
          let bfact_list' = explore_bfact_list bfact_list in
          if bfact_list == bfact_list'
          then
            let q' = explore q in
            if q == q'
            then df
            else head :: q'
          else
            if bfact_list' = []
            then explore q
            else (i,bfact_list')::(explore q)
    in

    explore df

  (******* Access *******)

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

  let get_recipe_variables (df:t) =
    List.fold_left (fun acc (_,bfact_list) ->
      List.fold_left (fun acc' bfact ->
        bfact.bf_var :: acc'
      ) acc bfact_list
    ) [] df

  let get_standard_recipe_variables (df:t) =

    let rec explore acc = function
      | [] -> acc
      | [(i,_)] when i = Recipe_Variable.infinite_type -> acc
      | (_,bfact_list)::q ->
          explore (
            List.fold_left (fun acc' bfact ->
              bfact.bf_var :: acc'
            ) acc bfact_list
          ) q
    in
    explore [] df

  exception Found of recipe_variable

  let find_term df t =

    let rec find_bfact = function
      | [] -> ()
      | { bf_var = x; bf_term = t'}::_ when Term.is_equal t t' -> raise (Found x)
      | _::q -> find_bfact q
    in

    let rec find_all = function
      | [] -> ()
      | (_,bfact_list)::q ->
          find_bfact bfact_list;
          find_all q
    in

    try
      find_all df;
      raise Not_found
    with Found x -> x

  let iter f df =
    List.iter (fun (_,bfact_l) -> List.iter f bfact_l) df

  (******* Testing *******)

  let is_solved (df:t) =
    let linked_vars = ref [] in

    let rec explore_term t = match t with
      | Var ({ link = NoLink ; _ } as x) ->
          x.link <- SLink;
          linked_vars := x :: !linked_vars;
          true
      | Var { link = SLink; _ } -> false
      | Var { link = TLink t ; _ } -> explore_term t
      | Var _ -> Config.internal_error "[data_structure.ml >> DF.compute_mgs_applicability] Unexpected link."
      | _ -> false
    in

    let rec explore_bfact_list = function
      | [] -> true
      | bfact::q -> explore_term bfact.bf_term && explore_bfact_list q
    in

    let rec explore = function
      | [] -> true
      | (_,bfact_list)::q -> explore_bfact_list bfact_list && explore q
    in

    let result = explore df in
    List.iter (fun v -> v.link <- NoLink) !linked_vars;
    result

  let is_empty (df:t) = df = []

  (******* Function for MGS *********)

  type mgs_applicability =
    | Solved
    | UnifyVariables of t
    | UnsolvedFact of basic_fact * t * bool (* [true] when there were also unification of variables *)

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

  let remove_linked_variables (df:t) =
    let removed_bfact = ref [] in
    let newly_linked = ref [] in

    let rec explore_bfact_list = function
      | [] -> []
      | bfact::q when bfact.bf_var.link_r = RNoLink ->
          bfact.bf_var.link_r <- RXLink bfact.bf_term;
          newly_linked := bfact.bf_var :: !newly_linked;
          bfact::(explore_bfact_list q)
      | bfact::q ->
          removed_bfact := bfact :: !removed_bfact;
          explore_bfact_list q
    in

    let rec explore = function
      | [] -> []
      | (i,bfact_list)::q ->
          let bfact_list' = explore_bfact_list bfact_list in
          if bfact_list' = []
          then explore q
          else (i,bfact_list')::(explore q)
    in

    let (result:t) = explore df in
    result, !removed_bfact, !newly_linked

  let link_term_variables linked_vars (df:t) =

    let rec explore_term v = function
      | Var { link = TLink t; _ } -> explore_term v t
      | Var ({ link = NoLink ; _ } as x) ->
          x.link <- XLink v;
          linked_vars := x :: !linked_vars
      | _ -> Config.internal_error "[data_structure.ml >> DF.link_term_variables] The deduction facts should be solved hence distinct variables"
    in

    let rec explore_bfact_list = function
      | [] -> ()
      | bfact::q ->
          explore_term bfact.bf_var bfact.bf_term;
          explore_bfact_list q
    in

    let rec explore = function
      | [] -> ()
      | (_,bfact_list)::q ->
          explore_bfact_list bfact_list;
          explore q
    in

    explore df

  let link_recipe_variables linked_vars (df:t) =

    let rec explore_bfact_list = function
      | [] -> ()
      | bfact::q ->
          Config.debug (fun () ->
            if bfact.bf_var.link_r <> RNoLink
            then Config.internal_error "[data_structure.ml >> DF.link_recipe_variables] The variables of deduction facts DF should not be linked."
          );
          bfact.bf_var.link_r <- RXLink bfact.bf_term;
          linked_vars := bfact.bf_var :: !linked_vars;
          explore_bfact_list q
    in

    let rec explore = function
      | [] -> ()
      | (_,bfact_list)::q ->
          explore_bfact_list bfact_list;
          explore q
    in

    explore df

  (******* Function for preparing the solving procedure *******)

  (* We do not try to  guarantee physical equality. This function is only applied after
     generation of transitions. Thus they originally were deduction facts with variables as right
     hand term, i.e. they would always need to be instantiate. *)
  let rename_and_instantiate (df:t) =
    List.map (fun (i,bfact_list) ->
      (i,List.map (fun bfact -> { bfact with bf_term = Term.rename_and_instantiate bfact.bf_term }) bfact_list)
    ) df

  let instantiate (df:t) =
    List.map (fun (i,bfact_list) ->
      (i,List.map (fun bfact -> { bfact with bf_term = Term.instantiate bfact.bf_term }) bfact_list)
    ) df

  (******* Function for debuging ******)

  let debug str (df:t) =
    List.iter (fun (i,bfact_l) ->
      List.iter (fun bfact ->
        if bfact.bf_var.type_r <> i
        then Config.internal_error (str^" The type of variable in the basic fact does not correspond to its placement.");

        if bfact.bf_var.link_r <> RNoLink
        then Config.internal_error (str^" The second order variables in the basic fact should not be linked.");

      ) bfact_l
    ) df

  let debug_same_structure str (df1:t) (df2:t) =

    let explore_bfact_list bf_l1 bf_l2 =
      List.iter (fun bfact1 ->
        if not (List.exists (fun bfact2 -> bfact1.bf_var == bfact2.bf_var) bf_l2)
        then Config.internal_error (str^" One deduction fact is missing from the other deduction facts.");
      ) bf_l1;

      List.iter (fun bfact2 ->
        if not (List.exists (fun bfact1 -> bfact1.bf_var == bfact2.bf_var) bf_l1)
        then Config.internal_error (str^" One deduction fact is missing from the other deduction facts.");
      ) bf_l2
    in

    let rec explore df1 df2 = match df1, df2 with
      | [], [] -> ()
      | [], _
      | _, [] -> Config.internal_error (str^" The deduction facts do not have the basic facts of same type.")
      | (i,_)::_ , (j,_)::_ when i <> j -> Config.internal_error (str^" The deduction facts do not have the basic facts of same type (2).")
      | (_,bf_l1)::q1, (_,bf_l2)::q2 ->
          explore_bfact_list bf_l1 bf_l2;
          explore q1 q2
    in
    explore df1 df2

  let debug_link_with_SLink (df:t) =
    List.iter (fun (_,bfactl) ->
      List.iter (fun bfact ->
        Term.debug_link_with_SLink bfact.bf_term
      ) bfactl
    ) df
end

(*********************************
***       Knowledge base       ***
**********************************)

module KR = struct

  type entry =
    {
      type_rec : int;
      recipe : recipe;
    }

  type t =
    {
      max_type_r : int;
      size : int;
      data : entry array
    }

  let dummy_entry = { type_rec = 0; recipe = Axiom 0 }

  let empty = { max_type_r = 0; size = 0; data = Array.make 0 dummy_entry }

  let size kbr = kbr.size

  let instantiate kbr =
    let data' =
      Array.map_q (fun elt ->
        let r' = Recipe.instantiate elt.recipe in
        if elt.recipe == r'
        then elt
        else { elt with recipe = r'}
      ) kbr.data
    in
    if data' == kbr.data
    then kbr
    else { kbr with data = data' }
end

module K = struct

  type t = term array

  let dummy_entry = Name { label_n = ""; index_n = 0; pure_fresh_n = false; link_n = NNoLink }

  let empty = Array.make 0 dummy_entry

  let instantiate (kb:t) =
    let kb' = Array.map_q Term.instantiate kb in
    if kb == kb' then kb else kb'

  let size kb = Array.length kb

  (* Iteration on the knowledge base *)

  let find_unifier_with_recipe_with_type kbr (kb:t) t type_r f_continuation (f_next:unit->unit) =

    let rec explore = function
      | i when i = kbr.KR.size -> f_next ()
      | i ->
          if kbr.KR.data.(i).KR.type_rec > type_r
          then f_next ()
          else
            begin
              let tmp = !Variable.currently_linked in
              Variable.currently_linked := [];

              let is_unifiable =
                try
                  Term.unify kb.(i) t;
                  true
                with Term.Not_unifiable -> false
              in
              if is_unifiable
              then
                if !Variable.currently_linked = []
                then
                  (* Identity substitution *)
                  f_continuation true (CRFunc(i,kbr.KR.data.(i).KR.recipe)) (fun () ->
                    Variable.currently_linked := tmp;
                    f_next ()
                  )
                else
                  f_continuation false (CRFunc(i,kbr.KR.data.(i).KR.recipe)) (fun () ->
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

  let find_unifier_with_recipe_no_type kbr (kb:t) t f_continuation (f_next:unit->unit) =

    let rec explore = function
      | i when i = kbr.KR.size -> f_next ()
      | i ->
          let tmp = !Variable.currently_linked in
          Variable.currently_linked := [];

          let is_unifiable =
            try
              Term.unify kb.(i) t;
              true
            with Term.Not_unifiable -> false
          in
          if is_unifiable
          then
            if !Variable.currently_linked = []
            then
              (* Identity substitution *)
              f_continuation true (CRFunc(i,kbr.KR.data.(i).KR.recipe)) (fun () ->
                Variable.currently_linked := tmp;
                f_next ()
              )
            else
              f_continuation false (CRFunc(i,kbr.KR.data.(i).KR.recipe)) (fun () ->
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
    in
    explore 0

  let find_unifier_with_recipe kbr (kb:t) t type_r f_continuation f_next =
    if type_r >= kbr.KR.max_type_r
    then find_unifier_with_recipe_no_type kbr kb t f_continuation f_next
    else find_unifier_with_recipe_with_type kbr kb t type_r f_continuation f_next

  let find_unifier_with_recipe_with_stop_with_type kbr (kb:t) t type_r stop_ref f_continuation (f_next:unit->unit) =

    let rec explore = function
      | i when i = kbr.KR.size -> f_next ()
      | i ->
          if kbr.KR.data.(i).KR.type_rec > type_r
          then f_next ()
          else
            begin
              let tmp = !Variable.currently_linked in
              Variable.currently_linked := [];

              let is_unifiable =
                try
                  Term.unify kb.(i) t;
                  true
                with Term.Not_unifiable -> false
              in
              if is_unifiable
              then
                if !Variable.currently_linked = []
                then
                  (* Identity substitution *)
                  f_continuation true (CRFunc(i,kbr.KR.data.(i).KR.recipe)) (fun () ->
                    Variable.currently_linked := tmp;
                    f_next ()
                  )
                else
                  f_continuation false (CRFunc(i,kbr.KR.data.(i).KR.recipe)) (fun () ->
                    List.iter (fun v -> v.link <- NoLink) !Variable.currently_linked;
                    Variable.currently_linked := tmp;
                    if !stop_ref then f_next () else explore (i+1)
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

  let find_unifier_with_recipe_with_stop_no_type kbr (kb:t) t stop_ref f_continuation (f_next:unit->unit) =

    let rec explore = function
      | i when i = kbr.KR.size -> f_next ()
      | i ->
          let tmp = !Variable.currently_linked in
          Variable.currently_linked := [];

          let is_unifiable =
            try
              Term.unify kb.(i) t;
              true
            with Term.Not_unifiable -> false
          in
          if is_unifiable
          then
            if !Variable.currently_linked = []
            then
              (* Identity substitution *)
              f_continuation true (CRFunc(i,kbr.KR.data.(i).KR.recipe)) (fun () ->
                Variable.currently_linked := tmp;
                f_next ()
              )
            else
              f_continuation false (CRFunc(i,kbr.KR.data.(i).KR.recipe)) (fun () ->
                List.iter (fun v -> v.link <- NoLink) !Variable.currently_linked;
                Variable.currently_linked := tmp;
                if !stop_ref then f_next () else explore (i+1)
              )
          else
            begin
              List.iter (fun v -> v.link <- NoLink) !Variable.currently_linked;
              Variable.currently_linked := tmp;
              explore(i+1)
            end
    in
    explore 0

  let find_unifier_with_recipe_with_stop kbr (kb:t) t type_r stop_ref f_continuation (f_next:unit->unit) =
    if type_r >= kbr.KR.max_type_r
    then find_unifier_with_recipe_with_stop_no_type kbr kb t stop_ref f_continuation f_next
    else find_unifier_with_recipe_with_stop_with_type kbr kb t type_r stop_ref f_continuation f_next

  let iteri f kbr kb =
    for i = 0 to kbr.KR.size - 1 do
      f i kbr.KR.data.(i).KR.recipe kb.(i)
    done

  let iter_term f kb =
    for i = 0 to Array.length kb - 1 do
      f kb.(i)
    done

  (* Consequence *)

  exception Uniformity_falsified

  let consequence_uniform_recipe kbr kb eq_uni r =

    let rec consequence eq_uni = function
      | RVar { link_r = RLink r; _ } -> consequence eq_uni r
      | CRFunc(i,_) -> eq_uni, kb.(i), kbr.KR.data.(i).KR.type_rec
      | RFunc(f,args_r) ->
          Config.debug (fun () ->
            if not (Symbol.is_constructor f)
            then Config.internal_error "[data_structure.ml >> K.consequence_uniform_recipe] The symbol should be constructor"
          );
          if f.arity = 0
          then eq_uni, Func(f,[]), 0
          else
            begin
              let (eq_uni_1, args_t, type_r) = consequence_list eq_uni args_r in
              let t = Func(f,args_t) in
              let acc_eq_uni_ref = ref eq_uni_1 in
              let result = ref None in
              find_unifier_with_recipe kbr kb t type_r (fun is_identity _ f_next ->
                if is_identity
                then acc_eq_uni_ref := Formula.T.Bot
                else acc_eq_uni_ref := Formula.T.wedge (Diseq.T.of_linked_variables !Variable.currently_linked) !acc_eq_uni_ref;
                f_next ()
              ) (fun () ->
                if !acc_eq_uni_ref <> Formula.T.Bot
                then result := Some !acc_eq_uni_ref
              );
              match !result with
                | None -> raise Uniformity_falsified
                | Some eq_uni_2 -> eq_uni_2, t, type_r
            end
      | RVar ({ link_r = RXLink t; _ } as x) -> eq_uni, t, x.type_r
      | RVar _ -> Config.internal_error "[data_structure.ml >> K.consequence_uniform_recipe] Unexpected variable."
      | _ -> Config.internal_error "[data_structure.ml >> K.consequence_uniform_recipe] Axioms should have been captured with context."

    and consequence_list eq_uni = function
      | [] -> eq_uni, [], 0
      | r::q_r ->
          let (eq_uni_1, t,type_r) = consequence eq_uni r in
          let (eq_uni_2, q_t,type_r') = consequence_list eq_uni_1 q_r in
          (eq_uni_2,t::q_t, max type_r type_r')
    in

    consequence eq_uni r

  (* Debug *)

  let debug_check_link_with_SLink kb =
    for i = 0 to Array.length kb - 1 do
      Term.debug_check_link_with_SLink kb.(i)
    done
end

(* Incremented knowledge base *)
module IK = struct

  type entry =
    {
      id : int;
      recipe : recipe;
      term : term
    }

  type t =
    {
      index_counter : int;
      type_rec : int;
      data : entry list (* To be always kept ordered. The first element is the last added. *)
    }

  let display tab kbr kb ikb =
    let accK = ref "" in

    for i = 0 to kbr.KR.size - 1 do
      accK := !accK ^ (Printf.sprintf "%s,%d |-%d %s, " (Recipe.display Display.Terminal kbr.KR.data.(i).KR.recipe) kbr.KR.data.(i).KR.type_rec i (Term.display Display.Terminal kb.(i)))
    done;

    let accIK = ref "" in

    List.iter (fun elt ->
      accIK := !accIK ^ (Printf.sprintf "%s,%d |-%d %s, " (Recipe.display Display.Terminal elt.recipe) ikb.type_rec elt.id (Term.display Display.Terminal elt.term))
    ) ikb.data;

    display_object tab None [ "K", !accK ; "IK", !accIK]

  let empty = { index_counter = 0; type_rec = 0; data = [] }

  let transfer_incremented_knowledge_into_knowledge after_output kbr kb ikb =

    let size_ikb = List.length ikb.data in
    let size_kbr = kbr.KR.size in

    if size_ikb = 0
    then
      begin
        Config.debug (fun () ->
          if ikb.index_counter <> kbr.KR.size
          then Config.internal_error "[data_structure.ml >> IK.transfer_incremented_knowledge_into_knowledge] Incorrect index counter";
        );
        (* Nothing to be added in Kb *)
        let kb' = Array.map_q Term.rename_and_instantiate kb in

        let ikb' =
          if after_output
          then { ikb with type_rec = ikb.type_rec + 1 }
          else ikb
        in
        kbr, kb',ikb',[]
      end
    else
      begin
        let new_size = size_ikb + kbr.KR.size in
        let kb' = Array.make new_size K.dummy_entry in
        let data_kbr' = Array.make new_size KR.dummy_entry in

        (* Copy data of K *)
        for i = 0 to size_kbr - 1 do
          kb'.(i) <- Term.rename_and_instantiate kb.(i)
        done;

        (* Copy data of KR *)
        for i = 0 to size_kbr - 1 do
          data_kbr'.(i) <- kbr.KR.data.(i)
        done;

        (* Copy data of IK *)
        let rec copy index acc = function
          | [] -> acc
          | elt::q ->
              kb'.(index) <- Term.rename_and_instantiate elt.term;
              data_kbr'.(index) <- { KR.type_rec = ikb.type_rec; KR.recipe = elt.recipe };
              copy (index-1) ((elt.id,index)::acc) q
        in

        let id_assoc = copy (new_size-1) [] ikb.data in

        let kbr' =
          {
            KR.max_type_r = ikb.type_rec;
            KR.size = new_size;
            KR.data = data_kbr'
          }
        in

        let ikb' =
          {
            index_counter = new_size;
            type_rec = if after_output then ikb.type_rec + 1 else ikb.type_rec;
            data = []
          }
        in
        kbr',kb',ikb',id_assoc
      end

  let transfer_incremented_knowledge_into_knowledge_only_kb kb ikb =

    let size_ikb = List.length ikb.data in
    let size_kb = Array.length kb in

    if size_ikb = 0
    then
      begin
        Config.debug (fun () ->
          if ikb.index_counter <> size_kb
          then Config.internal_error "[data_structure.ml >> IK.transfer_incremented_knowledge_into_knowledge] Incorrect index counter";
        );
        (* Nothing to be added in Kb *)
        Array.map_q Term.rename_and_instantiate kb
      end
    else
      begin
        let new_size = size_ikb + size_kb in
        let kb' = Array.make new_size K.dummy_entry in

        (* Copy data of K *)
        for i = 0 to  size_kb - 1 do
          kb'.(i) <- Term.rename_and_instantiate kb.(i)
        done;

        (* Copy data of IK *)
        let rec copy index = function
          | [] -> ()
          | elt::q ->
              kb'.(index) <- Term.rename_and_instantiate elt.term;
              copy (index-1) q
        in

        copy (new_size-1) ikb.data;

        kb'
      end

  (* his function should only be applied after and output. *)
  let transfer_incremented_knowledge_into_knowledge_no_rename kbr kb ikb =

    let size_ikb = List.length ikb.data in
    let size_kbr = kbr.KR.size in

    if size_ikb = 0
    then
      begin
        Config.debug (fun () ->
          if ikb.index_counter <> kbr.KR.size
          then Config.internal_error "[data_structure.ml >> IK.transfer_incremented_knowledge_into_knowledge] Incorrect index counter";
        );

        let ikb' = { ikb with type_rec = ikb.type_rec + 1 } in
        kbr, kb,ikb',[]
      end
    else
      begin
        let new_size = size_ikb + kbr.KR.size in
        let kb' = Array.make new_size K.dummy_entry in
        let data_kbr' = Array.make new_size KR.dummy_entry in

        (* Copy data of K *)
        for i = 0 to size_kbr - 1 do
          kb'.(i) <- kb.(i)
        done;

        (* Copy data of KR *)
        for i = 0 to size_kbr - 1 do
          data_kbr'.(i) <- kbr.KR.data.(i)
        done;

        (* Copy data of IK *)
        let rec copy index acc = function
          | [] -> acc
          | elt::q ->
              kb'.(index) <- Term.instantiate elt.term;
              data_kbr'.(index) <- { KR.type_rec = ikb.type_rec; KR.recipe = Recipe.instantiate elt.recipe };
              copy (index-1) ((elt.id,index)::acc) q
        in

        let id_assoc = copy (new_size-1) [] ikb.data in

        let kbr' =
          {
            KR.max_type_r = ikb.type_rec;
            KR.size = new_size;
            KR.data = data_kbr'
          }
        in

        let ikb' =
          {
            index_counter = new_size;
            type_rec = ikb.type_rec + 1;
            data = []
          }
        in
        kbr',kb',ikb',id_assoc
      end

  let transfer_incremented_knowledge_into_knowledge_only_kb_no_rename kb ikb =

    let size_ikb = List.length ikb.data in
    let size_kb = Array.length kb in

    if size_ikb = 0
    then
      begin
        Config.debug (fun () ->
          if ikb.index_counter <> size_kb
          then Config.internal_error "[data_structure.ml >> IK.transfer_incremented_knowledge_into_knowledge] Incorrect index counter";
        );
        (* Nothing to be added in Kb *)
        kb
      end
    else
      begin
        let new_size = size_ikb + size_kb in
        let kb' = Array.make new_size K.dummy_entry in

        (* Copy data of K *)
        for i = 0 to size_kb - 1 do
          kb'.(i) <- kb.(i)
        done;

        (* Copy data of IK *)
        let rec copy index = function
          | [] -> ()
          | elt::q ->
              kb'.(index) <- Term.instantiate elt.term;
              copy (index-1)  q
        in

        copy (new_size-1) ikb.data;

        kb'
      end

  let add ikb dfact =
    let index = ikb.index_counter in
    { ikb with
      index_counter = ikb.index_counter + 1;
      data = { id = index; recipe = dfact.df_recipe; term = dfact.df_term } :: ikb.data
    }

  let remove ikb index =
    let rec explore = function
      | [] -> Config.internal_error "[data_structure.ml >> IK.remove] Invalid index."
      | elt::q when elt.id = index -> q
      | elt::q -> elt::(explore q)
    in

    { ikb with data = explore ikb.data }

  let remove_last_entry ikb = { ikb with data = List.tl ikb.data }

  let get_next_index ikb = ikb.index_counter

  let get_last_term ikb = (List.hd ikb.data).term

  let get_last_index ikb = (List.hd ikb.data).id

  let get_all_index ikb = List.map (fun elt -> elt.id) ikb.data

  let get_previous_index_in_knowledge_base kbr ikb index =
    if index = 0
    then None
    else
      if index < kbr.KR.size
      then Some(index - 1)
      else
        let rec explore = function
          | [] -> Config.internal_error "[data_structure.ml >> get_previous_index_in_knowledge_base] The index should be part of IK at that point."
          | [elt] ->
              Config.debug (fun () ->
                if elt.id <> index
                then Config.internal_error "[data_structure.ml >> get_previous_index_in_knowledge_base] The index should be part of IK at that point (2)."
              );
              if kbr.KR.size = 0 then None else Some (kbr.KR.size - 1)
          | elt1::elt2::_ when elt1.id = index -> Some(elt2.id)
          | _::q -> explore q
        in
        explore ikb.data

  let get_term kb ikb index =
    if index < Array.length kb
    then kb.(index)
    else
      let rec explore = function
        | [] -> Config.internal_error "[data_structure.ml >> IK.get_term] Invalid index."
        | elt::_ when elt.id = index -> elt.term
        | _::q -> explore q
      in
      explore ikb.data

  let get_recipe kbr ikb index =
    if index < kbr.KR.size
    then kbr.KR.data.(index).KR.recipe
    else
      let rec explore = function
        | [] -> Config.internal_error "[data_structure.ml >> IK.get_recipe] Invalid index."
        | elt::_ when elt.id = index -> elt.recipe
        | _::q -> explore q
      in
      explore ikb.data

  let get kbr kb ikb index =
    if index < kbr.KR.size
    then kbr.KR.data.(index).KR.recipe, kb.(index)
    else
      let rec explore = function
        | [] -> Config.internal_error "[data_structure.ml >> IK.get] Invalid index."
        | elt::_ when elt.id = index -> elt.recipe, elt.term
        | _::q -> explore q
      in
      explore ikb.data

  let get_max_type_recipe kbr ikb =
    if ikb.data = []
    then kbr.KR.max_type_r
    else ikb.type_rec

  let find_unifier_with_recipe_with_stop kbr kb ikb t type_r stop_ref f_continuation (f_next:unit->unit) = match compare type_r kbr.KR.max_type_r with
    | -1 -> K.find_unifier_with_recipe_with_stop_with_type kbr kb t type_r stop_ref f_continuation f_next
    | 0 -> K.find_unifier_with_recipe_with_stop_no_type kbr kb t stop_ref f_continuation f_next
    | _ ->
        let rec explore = function
          | [] -> f_next ()
          | entry :: q ->
              let tmp = !Variable.currently_linked in
              Variable.currently_linked := [];

              let is_unifiable =
                try
                  Term.unify entry.term t;
                  true
                with Term.Not_unifiable -> false
              in
              if is_unifiable
              then
                if !Variable.currently_linked = []
                then
                  (* Identity substitution *)
                  f_continuation true (CRFunc(entry.id,entry.recipe)) (fun () ->
                    Variable.currently_linked := tmp;
                    f_next ()
                  )
                else
                  f_continuation false (CRFunc(entry.id,entry.recipe)) (fun () ->
                    List.iter (fun v -> v.link <- NoLink) !Variable.currently_linked;
                    Variable.currently_linked := tmp;
                    if !stop_ref then f_next () else explore q
                  )
              else
                begin
                  List.iter (fun v -> v.link <- NoLink) !Variable.currently_linked;
                  Variable.currently_linked := tmp;
                  explore q
                end
        in

        K.find_unifier_with_recipe_with_stop_no_type kbr kb t stop_ref f_continuation (fun () ->
          if !stop_ref || type_r < ikb.type_rec
          then f_next ()
          else explore ikb.data
        )

  let iteri f ikb =
    List.iter (fun elt ->
      f elt.id elt.recipe elt.term
    ) ikb.data

  let iter_term f ikb =
    List.iter (fun elt ->
      f elt.term
    ) ikb.data

  let instantiate_entry elt =
    let t = Term.instantiate elt.term in
    if elt.term == t
    then
      let r = Recipe.instantiate elt.recipe in
      if elt.recipe == r
      then elt
      else { elt with recipe = r }
    else { elt with recipe = Recipe.instantiate elt.recipe; term = t }

  let instantiate ikb =
    let data = List.map_q instantiate_entry ikb.data in
    if data == ikb.data
    then ikb
    else { ikb with data = data }


  (* Testing *)

  let for_all_term f_test ikb = List.for_all (fun e -> f_test e.term) ikb.data

  (* Consequence *)

  let find f_cont kbr kb ikb =

    let rec explore_ikb = function
      | [] -> raise Not_found
      | entry::q ->
          try
            f_cont (CRFunc(entry.id,entry.recipe)) entry.term
          with Not_found -> explore_ikb q
    in

    let rec explore_k = function
      | i when i = kbr.KR.size -> raise Not_found
      | i ->
          try
            f_cont (CRFunc(i,kbr.KR.data.(i).KR.recipe)) kb.(i)
          with Not_found -> explore_k (i+1)
    in

    try
      explore_k 0
    with Not_found ->
      explore_ikb ikb.data

  let consequence_term kbr kb kbi df term =

    let accu_variables = ref [] in

    let rec explore f_next = function
      | Var v ->
          begin match v.link with
            | TLink t -> explore f_next t
            | XLink r -> f_next (RVar r)
            | NoLink ->
                DF.link_term_variables accu_variables df;
                explore f_next (Var v)
            | _ -> Config.internal_error "[data_structure.ml >> IK.consequence_term] Unexpected link."
          end
      | (Name _) as t ->
          find (fun recipe term ->
            if Term.is_equal t term
            then f_next recipe
            else raise Not_found
          ) kbr kb kbi
      | Func(f,_) when f.arity = 0 && f.public -> f_next (RFunc(f,[]))
      | (Func(f,_)) as t when not f.public ->
          find (fun recipe term ->
            if Term.is_equal t term
            then f_next recipe
            else raise Not_found
          ) kbr kb kbi
      | (Func(f,args_t)) as t ->
          try
            explore_list (fun args_r ->
              f_next (RFunc(f,args_r))
            ) args_t
          with Not_found ->
            find (fun recipe term ->
              if Term.is_equal t term
              then f_next recipe
              else raise Not_found
            ) kbr kb kbi

    and explore_list f_next = function
      | [] -> f_next []
      | t::q ->
          explore (fun r ->
            explore_list (fun q_r ->
              f_next (r::q_r)
            ) q
          ) t
    in

    try
      explore (fun r ->
        List.iter (fun v -> v.link <- NoLink) !accu_variables;
        Some r
      ) term
    with Not_found ->
        List.iter (fun v -> v.link <- NoLink) !accu_variables;
        None

  let consequence_recipe kb ikb df recipe =
    let accu_variables = ref [] in

    let rec explore = function
      | (RVar v) as r ->
          begin match v.link_r with
            | RLink r' -> explore r'
            | RXLink t -> t
            | RNoLink ->
                DF.link_recipe_variables accu_variables df;
                explore r
            | _ -> Config.internal_error "[data_structure.ml >> IK.consequence_recipe] Unexpected link."
          end
      | RFunc(f,args) ->
          Config.debug (fun () ->
            if not (Symbol.is_constructor f)
            then Config.internal_error "[data_structure.ml >> IK.consequence_recipe] Consequence should only be applied on context."
          );
          Func(f,List.map explore args)
      | CRFunc(i,_) -> get_term kb ikb i
      | Axiom _ -> Config.internal_error "[data_structure.ml >> IK.consequence_recipe] The recipe given as input should be a context."

    in

    let t = explore recipe in

    List.iter (fun v -> v.link_r <- RNoLink) !accu_variables;

    t

  (* Debug *)

  let debug_check_link_with_SLink ikb =
    List.iter (fun entry -> Term.debug_check_link_with_SLink entry.term) ikb.data
end

(************************
***         UF        ***
*************************)

module UF = struct

  type state_ded_form =
    | DedPattern of deduction_fact list * deduction_fact list
    | DedSolved of deduction_fact list
    | DedUnsolved of deduction_formula list
    | DedNone

  type state_eq_form =
    | EqUnsolved of equality_formula
    | EqNone

  type t =
    {
      ded_formula : state_ded_form;
      eq_formula : state_eq_form
    }

  (**** Display functions ****)

  let display_state_eq_formula = function
    | EqNone -> Display.emptyset Display.Terminal
    | EqUnsolved eq -> display_equality_formula eq

  let display_state_ded_form = function
    | DedPattern (dfactl1, dfactl2) ->
        Printf.sprintf "Pattern: 1-- %s 2-- %s" (Display.display_list display_deduction_fact "; " dfactl1) (Display.display_list display_deduction_fact "; " dfactl2)
    | DedSolved dfactl ->
        Printf.sprintf "Solved: %s" (Display.display_list display_deduction_fact "; " dfactl)
    | DedUnsolved dforml ->
        Printf.sprintf "Unsolved: %s" (Display.display_list display_deduction_formula "; " dforml)
    | DedNone -> Display.emptyset Display.Terminal

  let display tab uf =
    display_object tab None [
      "Ded", display_state_ded_form uf.ded_formula;
      "Eq", display_state_eq_formula uf.eq_formula
    ]

  (******** Generation ********)

  let empty =
    {
      ded_formula = DedNone;
      eq_formula = EqNone
    }

  let add_equality_formula uf form =
    Config.debug (fun () ->
      if uf.eq_formula <> EqNone
      then Config.internal_error "[Data_structure.ml >> add_equality_formula] There is already an equality formula in UF.";
    );

    { uf with eq_formula = EqUnsolved form }

  let add_deduction_formulas uf form_list =
    Config.debug (fun () ->
      if uf.eq_formula <> EqNone
      then Config.internal_error "[Data_structure.ml >> add_deduction_formulas] There is already a deduction formula or fact in UF.";

      if form_list = []
      then Config.internal_error "[Data_structure.ml >> add_deduction_formulas] The list should not be empty.";
    );

    { uf with ded_formula = DedUnsolved form_list }

  let add_deduction_fact uf fact =
    Config.debug (fun () ->
      if uf.ded_formula <> DedNone
      then Config.internal_error "[Data_structure.ml >> add_deduction_fact] There is already a deduction formula or fact in UF."
      );

    { uf with ded_formula = DedPattern ([],[fact]) }

  let replace_deduction_formula uf form_list =
    Config.debug (fun () ->
      if form_list = []
      then Config.internal_error "[data_structure.ml >> UF.replace_deduction_formula] The list given as argument should not be empty.";

      match uf.ded_formula, uf.eq_formula with
        | DedUnsolved _, EqNone -> ()
        | _ -> Config.internal_error "[Data_structure.ml >> UF.replace_deduction_formula] There should be deduction formula and no equality."
    );
    { ded_formula = DedUnsolved form_list; eq_formula = EqNone }

  let set_no_deduction uf =
    Config.debug (fun () ->
      match uf.ded_formula, uf.eq_formula with
        | DedUnsolved _, EqNone -> ()
        | _ -> Config.internal_error "[Data_structure.ml >> UF.set_no_deduction] There should be deduction formula."
    );
    { ded_formula = DedNone; eq_formula = EqNone }

  let remove_unsolved_equality_formula uf =
    Config.debug (fun () ->
      match uf.eq_formula with
        | EqUnsolved _ -> ()
        | _ -> Config.internal_error "[data_structure.ml >> UF.remove_usolved] UF should contain an unsolved equality formula."
    );
    { uf with eq_formula = EqNone }

  let remove_head_deduction_fact uf = match uf.ded_formula with
    | DedSolved [_] -> { uf with ded_formula = DedNone }
    | DedSolved (_::q) -> { uf with ded_formula = DedSolved q }
    | _ -> Config.internal_error "[data_structure.ml >> remove_head_deduction_fact] Unexpected case."

  let validate_head_deduction_facts_for_pattern uf = match uf.ded_formula with
    | DedPattern(checked,dfact::q_dfact) ->
        let rec generate_dfact_list = function
          | Var { link = TLink t; _ } -> generate_dfact_list t
          | Func(f,args) when f.cat = Tuple && f.arity <> 0 ->
              let projections = Symbol.get_projections f in
              { uf with ded_formula = DedPattern(checked,List.fold_left2 (fun acc f_proj t -> { df_recipe = RFunc(f_proj,[dfact.df_recipe]); df_term = t}::acc) q_dfact projections args) }
          | _ ->
              { uf with ded_formula = if q_dfact = [] then DedSolved(dfact::checked) else DedPattern(dfact::checked,q_dfact) }
        in
        generate_dfact_list dfact.df_term
    | _ -> Config.internal_error "[data_structure.ml >> UF.validate_head_deduction_facts_for_pattern] There should be at least one deduction fact to check for pattern."

  let remove_head_unchecked_deduction_fact_for_pattern uf = match uf.ded_formula with
    | DedPattern([],[_]) -> { uf with ded_formula = DedNone }
    | DedPattern(checked,[_]) -> { uf with ded_formula = DedSolved checked }
    | DedPattern(checked,_::q) -> { uf with ded_formula = DedPattern(checked,q) }
    | _ -> Config.internal_error "[data_structure.ml >> UF.remove_head_unchecked_deduction_fact_for_pattern] Unexpected case."


  (******** Access ********)

  let get_deduction_formula_option uf = match uf.ded_formula with
    | DedUnsolved l -> Some l, false
    | DedPattern _ -> None, true
    | DedNone -> None, false
    | _ -> Config.internal_error "[data_structure.ml >> UF.get_deduction_formula_option] The solved fact should be in the pattern to be checked"

  let get_unique_unchecked_deduction_fact uf = match uf.ded_formula with
    | DedPattern([],[dfact]) -> dfact
    | _ -> Config.internal_error "[data_structure.ml >> UF.get_unique_unchecked_deduction_fact] There should be only one fact in the pattern to be checked"

  let get_equality_formula_option uf = match uf.eq_formula with
    | EqUnsolved t -> Some t
    | _ -> None

  let pop_deduction_fact_to_check_for_pattern uf = match uf.ded_formula with
    | DedPattern(_,dfact::_) -> Some dfact
    | _ -> None

  let pop_and_remove_deduction_fact uf = match uf.ded_formula with
    | DedSolved [dfact] -> dfact, { uf with ded_formula = DedNone }
    | DedSolved (dfact::q) -> dfact, { uf with ded_formula = DedSolved q }
    | _ -> Config.internal_error "[data_structure.ml >> pop_and_remove_deduction_fact] Unexpected case."

  let pop_deduction_fact uf = match uf.ded_formula with
    | DedSolved (dfact::_) -> dfact
    | DedSolved [] -> Config.internal_error "[data_structure.ml >> pop_deduction_fact] Incorrect structure."
    | DedPattern _ -> Config.internal_error "[data_structure.ml >> pop_deduction_fact] The deduction facts should have been checked for pattern already."
    | DedNone -> Config.internal_error "[data_structure.ml >> pop_deduction_fact] The deduction facts should not be empty."
    | _ -> Config.internal_error "[data_structure.ml >> pop_deduction_fact] There should be at least one deduction fact."

  (****** Testing ******)

  let exists_deduction_fact uf = match uf.ded_formula with
    | DedSolved _ -> true
    | _ -> false

  (******* Instantiation *******)

  exception NFound of deduction_fact

  let normalise_deduction_formula_to_fact uf form =
    let tmp = !Variable.currently_linked in
    Variable.currently_linked := [];

    List.iter (fun (v,t) -> Term.unify (Var v) t) form.df_equations;

    let dfact = { form.df_head with df_term = Term.instantiate form.df_head.df_term } in

    List.iter (fun v -> v.link <- NoLink) !Variable.currently_linked;
    Variable.currently_linked := tmp;

    { uf with ded_formula = DedPattern ([],[dfact]) }

  let normalise_deductions uf = match uf.ded_formula with
    | DedUnsolved form_list ->
        begin
          try
            let form_list' =
              List.fold_left (fun acc form ->
                let tmp = !Variable.currently_linked in
                Variable.currently_linked := [];

                try
                  List.iter (fun (v,t) -> Term.unify (Var v) t) form.df_equations;

                  let new_equations =
                    List.fold_left (fun acc v -> match v.link with
                      | TLink t when v.quantifier <> Universal -> (v,Term.instantiate t)::acc
                      | _ -> acc
                    ) [] !Variable.currently_linked
                  in
                  if new_equations = []
                  then
                    begin
                      let dfact = { form.df_head with df_term = Term.instantiate form.df_head.df_term } in
                      List.iter (fun v -> v.link <- NoLink) !Variable.currently_linked;
                      Variable.currently_linked := tmp;
                      raise (NFound dfact)
                    end
                  else
                    begin
                      let head = { form.df_head with df_term = Term.instantiate form.df_head.df_term } in
                      List.iter (fun v -> v.link <- NoLink) !Variable.currently_linked;
                      Variable.currently_linked := tmp;
                      { df_head = head; df_equations = new_equations } :: acc
                    end
                with Term.Not_unifiable ->
                  List.iter (fun v -> v.link <- NoLink) !Variable.currently_linked;
                  Variable.currently_linked := tmp;
                  acc
              ) [] form_list
            in
            if form_list' = []
            then { uf with ded_formula = DedNone }
            else { uf with ded_formula = DedUnsolved form_list' }
          with NFound dfact -> { uf with ded_formula = DedPattern([],[dfact]) }
        end
    | _ -> uf

  let rename_and_instantiate uf =
    Config.debug (fun () ->
      if uf.eq_formula <> EqNone
      then Config.internal_error "[data_structure.ml >> UF.rename_and_instantiate] Should not be any equality formula.";
    );

    match uf.ded_formula with
      | DedPattern([],[dfact]) ->
          let t' = Term.rename_and_instantiate dfact.df_term in
          if dfact.df_term == t'
          then uf
          else
            {
              eq_formula = EqNone;
              ded_formula = DedPattern([],[{ dfact with df_term = Term.rename_and_instantiate dfact.df_term}])
            }
      | DedNone -> uf
      | _ -> Config.internal_error "[data_structure.ml >> UF.rename_and_instantiate] Unexpected case."

  (* Debug *)

  let debug_check_link_with_SLink uf =
    begin match uf.ded_formula with
      | DedPattern(dfact1,dfact2) ->
          List.iter (fun dfact -> Term.debug_check_link_with_SLink dfact.df_term) dfact1;
          List.iter (fun dfact -> Term.debug_check_link_with_SLink dfact.df_term) dfact2
      | DedSolved dfactl ->
          List.iter (fun dfact -> Term.debug_check_link_with_SLink dfact.df_term) dfactl
      | _ -> ()
    end
end
