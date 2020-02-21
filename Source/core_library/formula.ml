open Types
open Term
open Display
open Extensions

(***********************************
***          Disequations        ***
************************************)

module Diseq = struct

  module T = struct

    type t =
      | Top
      | Bot
      | Disj of (variable * term) list

    (* Generation *)

    (* All variables of [v_list] should be linked. *)
    let of_linked_variables v_list =
      if v_list = []
      then Bot
      else
        Disj (List.rev_map (fun v -> match v.link with
          | TLink t -> v, Term.instantiate t
          | _ -> Config.internal_error "[formula.ml >> Diseq.T.of_linked_variables] There should only be variables linked with TLink."
        ) v_list)

    let rec rename_universal_to_existential = function
      | Var { link = VLink v; _ } -> Var v
      | Var v when v.quantifier = Universal ->
          let v' = Variable.fresh Existential in
          Variable.link v v';
          Var v'
      | Func(f,args) -> Func(f,List.map rename_universal_to_existential args)
      | t -> t

    (** The disequation should not contained linked variables. *)
    let substitution_of = function
      | Top | Bot -> Config.internal_error "[term.ml >> Diseq.substitution_of] The disequation should not be bot or top"
      | Disj disj_list ->
          let tmp = !Variable.currently_linked in
          Variable.currently_linked := [];

          let subst = List.rev_map (fun (x,t) -> (x,rename_universal_to_existential t)) disj_list in

          List.iter (fun v -> v.link <- NoLink) !Variable.currently_linked;
          Variable.currently_linked := tmp;
          subst

    (* Instantiation *)

    let instantiate_and_normalise = function
      | Bot -> Bot
      | Top -> Top
      | Disj diseq_list ->
          let tmp = !Variable.currently_linked in
          Variable.currently_linked := [];

          try
            List.iter (fun (t1,t2) ->
              Term.unify (Var t1) t2
            ) diseq_list;

            let diseq_list' =
              List.fold_left (fun acc var ->
                if var.quantifier = Universal
                then acc
                else (var,Term.instantiate (Var var))::acc
              ) [] !Variable.currently_linked
            in

            List.iter (fun v -> v.link <- NoLink) !Variable.currently_linked;
            Variable.currently_linked := tmp;

            if diseq_list' = []
            then Bot
            else Disj diseq_list'
          with Term.Not_unifiable ->
            List.iter (fun v -> v.link <- NoLink) !Variable.currently_linked;
            Variable.currently_linked := tmp;
            Top

    (* [Variable.currently_linked] should be equal to [x] linked with [t] *)
    let instantiate_and_normalise_one_variable x t = function
      | Top -> Top
      | Bot -> Bot
      | Disj diseq_list ->
          Config.debug (fun () ->
            if x.link = NoLink
            then Config.internal_error "[formula.ml >> Diseq.T.instantiate_and_normalise_one_variable] The variable x should be linked to the term.";
          );

          (* We link the variables of the disequality *)
          x.link <- NoLink;
          List.iter (fun (y,r') -> y.link <- TLink r') diseq_list;
          Variable.currently_linked := [];

          (* We unify [x] with [r] *)
          let result =
            try
              Term.unify (Var x) t;
              let diseq_list_1 =
                List.fold_left (fun acc var ->
                  if var.quantifier = Universal || var == x
                  then acc
                  else (var,Term.instantiate (Var var))::acc
                ) [] !Variable.currently_linked
              in
              let diseq_list_2 =
                List.fold_left (fun acc (y,r') ->
                  (* We know that [y] is not universal. *)
                  if y == x
                  then acc
                  else (y,Term.instantiate r')::acc
                ) diseq_list_1 diseq_list
              in

              if diseq_list_2 = []
              then Bot
              else Disj diseq_list_2
            with Term.Not_unifiable -> Top
          in

          List.iter (fun v -> v.link <- NoLink) !Variable.currently_linked;
          List.iter (fun (v,_) -> v.link <- NoLink) diseq_list;
          x.link <- TLink t;
          Variable.currently_linked := [x];
          result

    (* Does not rename universal variables. *)
    let rename_and_instantiate form = match form with
      | Top | Bot -> form
      | Disj disj ->
          Config.debug (fun () ->
            if List.exists (fun (v,_) -> v.quantifier = Universal) disj
            then Config.internal_error "[formula.ml >> Diseq.T.rename_and_instantiate] The formula should be normalised before renaming.";

            if disj = []
            then Config.internal_error "[formula.ml >> Diseq.T.rename_and_instantiate] The list should not be empty.";
          );
          Disj(List.map (fun (v,t) -> Variable.rename v, Term.rename_and_instantiate_exclude_universal t) disj)

    (* Display *)

    let display ?(follow_link=true) out = function
      | Top -> top out
      | Bot -> bot out
      | Disj diseq_list ->
          let univ_vars = ref [] in

          let rec find_univ_var = function
            | Var v ->
                if v.quantifier = Universal && not (List.memq v !univ_vars)
                then univ_vars := v :: !univ_vars
            | Func(_,args) -> List.iter find_univ_var args
            | Name _ -> ()
          in

          let display_single (v,t) = Printf.sprintf "%s %s %s" (Variable.display out v) (neqs out) (Term.display ~follow_link:follow_link out t) in

          List.iter (fun (_,t2) -> find_univ_var t2) diseq_list;

          if !univ_vars = []
          then Printf.sprintf "%s" (display_list display_single (Printf.sprintf " %s " (vee out)) diseq_list)
          else Printf.sprintf "%s %s.%s" (forall out) (display_list (Variable.display out) "," !univ_vars) (display_list display_single (Printf.sprintf " %s " (vee out)) diseq_list)

    (* Debug function *)

    let rec debug_no_linked_variables_term = function
      | Var v ->
          begin match v.link with
            | NoLink -> true
            | TLink _ -> Config.log_in_debug Config.Always "[debug_no_linked_variables_term] TLink in term"; false
            | VLink _ -> Config.log_in_debug Config.Always "[debug_no_linked_variables_term] VLink in term"; false
            | SLink -> Config.log_in_debug Config.Always "[debug_no_linked_variables_term] SLink in term"; false
            | XLink _ -> Config.log_in_debug Config.Always "[debug_no_linked_variables_term] XLink in term"; false
          end
      | Func(_,args) -> List.for_all debug_no_linked_variables_term args
      | _ -> true

    let debug_no_linked_variables = function
      | Top
      | Bot -> true
      | Disj vlist -> List.for_all (fun (v,t) ->
          begin match v.link with
            | NoLink ->  debug_no_linked_variables_term t
            | TLink _ -> Config.log_in_debug Config.Always "[debug_no_linked_variables_term] TLink in variable"; false
            | VLink _ -> Config.log_in_debug Config.Always "[debug_no_linked_variables_term] VLink in variable"; false
            | SLink -> Config.log_in_debug Config.Always "[debug_no_linked_variables_term] SLink in variable"; false
            | XLink _ -> Config.log_in_debug Config.Always "[debug_no_linked_variables_term] XLink in variable"; false
          end
          ) vlist

  end

  module R = struct

    type t =
      | Top
      | Bot
      | Disj of (recipe_variable * int) list * (recipe_variable * recipe) list
          (* Type of the variable is almost equal or bigger than the type of the recipe *)

    (* [of_maybe_linked_variables v_list to_be_univ_vars] returns the disequalities corresponding to
       the negation represented by the links in [v_list]. The variables in [to_be_univ_vars]
       should be transformed as universal variables.
       All variables in [v_list] can be linked and should not be in [to_be_univ_vars].
       Variables in [to_be_univ_vars] should not be linked. Only the unlinked variables are transformed
       in universal variables. *)
    let of_maybe_linked_variables v_list to_be_univ_vars =
      if v_list = []
      then Bot
      else if to_be_univ_vars = []
      then
        let diseq =
          List.fold_left (fun acc v -> match v.link_r with
            | RLink r -> (v, Recipe.instantiate r)::acc
            | _ -> acc
          ) [] v_list
        in
        if diseq = []
        then Bot
        else Disj ([],diseq)
      else
        begin
          let renamed_vars = ref [] in

          Config.debug (fun () ->
            if List.exists (function { link_r = l; _} when l <> RNoLink -> true | _ -> false) to_be_univ_vars
            then Config.internal_error "[formula.ml >> Diseq.of_maybe_linked_variables] Variables should not be linked."
          );

          List.iter (fun v ->
            let v' = Recipe_Variable.fresh Universal v.type_r in
            v.link_r <- RLink (RVar v');
            renamed_vars := v :: !renamed_vars
          ) to_be_univ_vars;

          let original_link = ref [] in
          let changed_vars = ref [] in

          List.iter (fun v ->
            let rec explore = function
              | RVar { link_r = RLink r; _ } -> explore r
              | RVar v' when v'.quantifier_r = Universal && v'.type_r = v.type_r ->
                  original_link := (v,v.link_r) :: !original_link;
                  changed_vars := v' :: !changed_vars;
                  v'.link_r <- RLink (RVar v);
                  v.link_r <- RNoLink
              | _ -> ()
            in
            match v.link_r with
              | RLink r -> explore r
              | _ -> ()
          ) v_list;

          let diseq =
            List.fold_left (fun acc v -> match v.link_r with
              | RLink r -> (v,Recipe.instantiate r)::acc
              | _ -> acc
            ) [] v_list
          in

          List.iter (fun (v,link) -> v.link_r <- link) !original_link;
          List.iter (fun v -> v.link_r <- RNoLink) !renamed_vars;
          List.iter (fun v -> v.link_r <- RNoLink) !changed_vars;

          if diseq = []
          then Bot
          else Disj ([],diseq)
        end

    let restricted_vars = ref []

    let rec restrict_recipe k = function
      | Axiom i ->
          if i <= k
          then raise Recipe.Not_unifiable
      | CRFunc(_,r) -> restrict_recipe k r
      | RFunc(_,args) -> List.iter (restrict_recipe k) args
      | RVar x ->
          match x.link_r with
            | RLink r -> restrict_recipe k r
            | RNoLink ->
                if x.type_r > k
                then
                  begin
                    restricted_vars := x :: !restricted_vars;
                    x.link_r <- RRLink k
                  end
            | RRLink k' -> x.link_r <- RRLink (min k k')
            | _ -> Config.internal_error "[formula.ml >> Diseq.R.restrict_recipe] Unexpected link"

    (* We assume that [r] is of the form [f(x_1,...,x_n)] with x_1,...,x_n fresh
       or [r] is ground.
       Moreover no variables in the disequality should be linked.*)
    let instantiate_and_normalise_one_variable_constructor x r = function
      | Top -> Top
      | Bot -> Bot
      | Disj(restriction_list,diseq_list) ->
          Config.debug (fun () ->
            if x.link_r = RNoLink
            then Config.internal_error "[formula.ml >> Diseq.R.instantiate_and_normalise_one_variable_constructor] The variable x should be linked to the term.";
          );

          if !restricted_vars <> []
          then Config.internal_error "[formula.ml >> Diseq.R.instantiate_and_normalise_one_variable_constructor] Restriction vars list should be empty.";

          (* We link the variables of the disequality *)
          x.link_r <- RNoLink;
          List.iter (fun (y,r') -> y.link_r <- RLink r') diseq_list;

          (* We unify [x] with [r] *)
          begin match x.link_r with
            | RNoLink ->
                (* In such a case, we can directly instantiate the variables without
                   applying [Recipe.unify] since [x_1,...,x_n] are fresh or [r] is ground *)
                x.link_r <- RLink r;
                let diseq_list' = List.rev_map (fun (y,r') -> y, Recipe.instantiate r') diseq_list in
                let restriction_list' = match List.extract_opt (fun (v,_) -> v == x) restriction_list with
                  | None -> restriction_list
                  | Some((_,k),restr_list) ->
                      match r with
                        | RFunc(_,args) ->
                            List.fold_left (fun acc r' -> match r' with
                              | RVar x' -> (x',k)::acc
                              | _ -> Config.internal_error "[formula.ml >> Diseq.R.instantiate_and_normalise_one_variable_constructor] Unexpected recipe (1)"
                            ) restr_list args
                        | _ -> Config.internal_error "[formula.ml >> Diseq.R.instantiate_and_normalise_one_variable_constructor] Unexpected recipe (2)"
                in
                List.iter (fun (y,_) -> y.link_r <- RNoLink) diseq_list;
                Disj(restriction_list',diseq_list')
            | RLink r' ->
                let tmp = !Recipe_Variable.currently_linked in
                Recipe_Variable.currently_linked := [];
                let result =
                  try
                    Recipe.unify r r';

                    let diseq_list_1 =
                      List.fold_left (fun acc var ->
                        if var.quantifier_r = Universal
                        then
                          begin
                            restrict_recipe var.type_r (RVar var);
                            acc
                          end
                        else (var,Recipe.instantiate (RVar var))::acc
                      ) [] !Recipe_Variable.currently_linked
                    in
                    let diseq_list_2 =
                      List.fold_left (fun acc (y,r') ->
                        (* We know that [y] is not universal. *)
                        if y == x
                        then acc
                        else (y,Recipe.instantiate r')::acc
                      ) diseq_list_1 diseq_list
                    in

                    (* We check the old variable restrictions *)
                    List.iter (fun (v,k) -> restrict_recipe k (RVar v)) restriction_list;

                    let restriction_list' =
                      List.rev_map (fun var -> match var.link_r with
                        | RRLink k -> (var,k)
                        | _ -> Config.internal_error "[formula.ml >> Diseq.R.instantiate_and_normalise_one_variable_constructor] The should be a restricted link."
                      ) !restricted_vars
                    in

                    if diseq_list_2 = [] && restriction_list' = []
                    then Bot
                    else Disj(restriction_list',diseq_list_2)
                  with Recipe.Not_unifiable -> Top
                in
                List.iter (fun v -> v.link_r <- RNoLink) !restricted_vars;
                List.iter (fun v -> v.link_r <- RNoLink) !Recipe_Variable.currently_linked;
                List.iter (fun (v,_) -> v.link_r <- RNoLink) diseq_list;
                x.link_r <- RLink r;
                Recipe_Variable.currently_linked := tmp;
                restricted_vars := [];

                result
            | _ -> Config.internal_error "[formula.ml >> Diseq.R.instantiate_and_normalise_constructor] Unexpected link."
          end

    let instantiate_and_normalise_one_variable x r = function
      | Top -> Top
      | Bot -> Bot
      | Disj(restriction_list,diseq_list) ->
          Config.debug (fun () ->
            if x.link_r = RNoLink
            then Config.internal_error "[formula.ml >> Diseq.R.instantiate_and_normalise_one_variable_constructor] The variable x should not be linked to the term.";
          );

          if !restricted_vars <> []
          then Config.internal_error "[formula.ml >> Diseq.R.instantiate_and_normalise_one_variable] Restriction vars list should be empty.";

          (* We link the variables of the disequality *)
          x.link_r <- RNoLink;
          List.iter (fun (y,r') -> y.link_r <- RLink r') diseq_list;
          Recipe_Variable.currently_linked := [];

          (* We unify [x] with [r] *)

          let result =
            try
              Recipe.unify (RVar x) r;
              let diseq_list_1 =
                List.fold_left (fun acc var ->
                  if var.quantifier_r = Universal || var == x
                  then
                    begin
                      restrict_recipe var.type_r (RVar var);
                      acc
                    end
                  else (var,Recipe.instantiate (RVar var))::acc
                ) [] !Recipe_Variable.currently_linked
              in
              let diseq_list_2 =
                List.fold_left (fun acc (y,r') ->
                  (* We know that [y] is not universal. *)
                  if y == x
                  then acc
                  else (y,Recipe.instantiate r')::acc
                ) diseq_list_1 diseq_list
              in

              (* We check the old variable restrictions *)
              List.iter (fun (v,k) -> restrict_recipe k (RVar v)) restriction_list;

              let restriction_list' =
                List.rev_map (fun var -> match var.link_r with
                  | RRLink k -> (var,k)
                  | _ -> Config.internal_error "[formula.ml >> Diseq.R.instantiate_and_normalise_one_variable] The should be a restricted link."
                ) !restricted_vars
              in

              if diseq_list_2 = []  && restriction_list' = []
              then Bot
              else Disj(restriction_list',diseq_list_2)
            with Recipe.Not_unifiable -> Top
          in
          List.iter (fun v -> v.link_r <- RNoLink) !restricted_vars;
          List.iter (fun v -> v.link_r <- RNoLink) !Recipe_Variable.currently_linked;
          List.iter (fun (v,_) -> v.link_r <- RNoLink) diseq_list;
          x.link_r <- RLink r;
          Recipe_Variable.currently_linked := [x];
          restricted_vars := [];

          result

    let instantiate_and_normalise = function
      | Bot -> Bot
      | Top -> Top
      | Disj(restriction_list, diseq_list) ->
          let tmp = !Recipe_Variable.currently_linked in
          Recipe_Variable.currently_linked := [];

          if !restricted_vars <> []
          then Config.internal_error "[formula.ml >> Diseq.R.instantiate_and_normalise] Restriction vars list should be empty.";

          try
            (* First we unify the disequalities *)
            List.iter (fun (t1,t2) ->
              Recipe.unify (RVar t1) t2
            ) diseq_list;

            let diseq_list' =
              List.fold_left (fun acc var ->
                if var.quantifier_r = Universal
                then
                  begin
                    restrict_recipe var.type_r (RVar var);
                    acc
                  end
                else (var,Recipe.instantiate (RVar var))::acc
              ) [] !Recipe_Variable.currently_linked
            in

            (* We check the old variable restrictions *)
            List.iter (fun (v,k) -> restrict_recipe k (RVar v)) restriction_list;

            let restriction_list' =
              List.rev_map (fun var -> match var.link_r with
                | RRLink k -> (var,k)
                | _ -> Config.internal_error "[formula.ml >> Diseq.R.instantiate_and_normalise] The should be a restricted link."
              ) !restricted_vars
            in

            (* We cleanup *)
            List.iter (fun v -> v.link_r <- RNoLink) !restricted_vars;
            List.iter (fun v -> v.link_r <- RNoLink) !Recipe_Variable.currently_linked;
            Recipe_Variable.currently_linked := tmp;
            restricted_vars := [];

            if diseq_list' = [] && restriction_list' = []
            then Bot
            else Disj(restriction_list',diseq_list')
          with Recipe.Not_unifiable ->
            List.iter (fun v -> v.link_r <- RNoLink) !restricted_vars;
            List.iter (fun v -> v.link_r <- RNoLink) !Recipe_Variable.currently_linked;
            Recipe_Variable.currently_linked := tmp;
            restricted_vars := [];
            Top

    (* Display *)

    let display ?(follow_link=true) out = function
      | Top -> top out
      | Bot -> bot out
      | Disj(restriction_list,diseq_list) ->
          let univ_vars = ref [] in

          let rec find_univ_var = function
            | RVar v ->
                begin match v.link_r with
                  | RSLink -> ()
                  | RNoLink when v.quantifier_r = Universal ->
                      v.link_r <- RSLink;
                      univ_vars := v :: !univ_vars
                  | RNoLink -> ()
                  | _ -> Config.internal_error "[formula.ml >> Diseq.R.display] The variables in the disequality should not be linked."
                end
            | RFunc(_,args) -> List.iter find_univ_var args
            | CRFunc(_,r) -> find_univ_var r
            | Axiom _ -> ()
          in

          let display_single (v,t) = Printf.sprintf "%s %s %s" (Recipe_Variable.display out v) (neqs out) (Recipe.display ~follow_link:follow_link out t) in
          let display_restriction (v,k) = Printf.sprintf "%s > %d" (Recipe_Variable.display out v) k in

          List.iter (fun (_,t2) -> find_univ_var t2) diseq_list;

          let display_disj = match restriction_list,diseq_list with
            | [], [] -> Config.internal_error "[formula.ml >> Formula.R.display] Unexpected case"
            | [], _ -> display_list display_single (Printf.sprintf " %s " (vee out)) diseq_list
            | _, [] -> display_list display_restriction (Printf.sprintf " %s " (vee out)) restriction_list
            | _ -> (display_list display_restriction (Printf.sprintf " %s " (vee out)) restriction_list) ^ " " ^ (vee out) ^ (display_list display_single (Printf.sprintf " %s " (vee out)) diseq_list)
          in

          if !univ_vars = []
          then display_disj
          else
            begin
              List.iter (fun v -> v.link_r <- RNoLink) !univ_vars;
              Printf.sprintf "%s %s.%s" (forall out) (display_list (fun v -> Recipe_Variable.display out v) "," !univ_vars) display_disj
            end
  end

  module M = struct

    type t =
      | Top
      | Bot
      | Disj of (variable * term) list * (recipe_variable * int) list * (recipe_variable * recipe) list

    let instantiate_and_normalise_only_recipe f_norm diseq = match diseq with
      | Top
      | Bot
      | Disj(_,[],[]) -> diseq
      | Disj(disj_t,restr_r,disj_r) ->
          match f_norm (R.Disj(restr_r,disj_r)) with
            | R.Top -> Top
            | R.Bot -> if disj_t = [] then Bot else Disj(disj_t,[],[])
            | R.Disj(restr_r',disj_r') -> Disj(disj_t,restr_r',disj_r')

    let instantiate_and_normalise f_norm_term f_norm_rec diseq = match diseq with
      | Top
      | Bot -> diseq
      | Disj([],restr_r,disj_r) ->
          begin match f_norm_rec (R.Disj(restr_r,disj_r)) with
            | R.Top -> Top
            | R.Bot -> Bot
            | R.Disj(restr_r',disj_r') -> Disj([],restr_r',disj_r')
          end
      | Disj(disj_t,[],[]) ->
          begin match f_norm_term (T.Disj disj_t) with
            | T.Top -> Top
            | T.Bot -> Bot
            | T.Disj disj_t' -> Disj(disj_t',[],[])
          end
      | Disj(disj_t,restr_r,disj_r) ->
          begin match f_norm_term (T.Disj disj_t) with
            | T.Top -> Top
            | T.Bot ->
                begin match f_norm_rec (R.Disj (restr_r,disj_r)) with
                  | R.Top -> Top
                  | R.Bot -> Bot
                  | R.Disj(restr_r',disj_r') -> Disj([],restr_r',disj_r')
                end
            | T.Disj disj_t' ->
                begin match f_norm_rec (R.Disj (restr_r,disj_r)) with
                  | R.Top -> Top
                  | R.Bot -> Disj(disj_t',[],[])
                  | R.Disj(restr_r',disj_r') -> Disj(disj_t',restr_r',disj_r')
                end
          end

    let rename_and_instantiate_exclude_universal_slink mixed = match mixed with
      | Top | Bot -> mixed
      | Disj(disj_t,restr_r,disj_r) ->
          if disj_t = []
          then mixed
          else
            begin
              Config.debug (fun () ->
                if List.exists (fun (v,_) -> v.quantifier = Universal) disj_t
                then Config.internal_error "[formula.ml >> Diseq.M.rename_and_instantiate] The formula should be normalised before renaming.";
              );

              Disj(List.map (fun (v,t) -> Variable.rename v, Term.rename_and_instantiate_exclude_universal_slink t) disj_t, restr_r,disj_r)
            end
  end
end

module Formula = struct

  module T = struct

    type t =
      | Top
      | Bot
      | Conj of Diseq.T.t list

    (* We assume that [diseq] is neither top or bot. *)
    let wedge diseq = function
      | Top -> Conj [diseq]
      | Bot -> Bot
      | Conj diseq_l -> Conj (diseq::diseq_l)

    let wedge_formula form1 form2 = match form1, form2 with
      | Top, form'
      | form', Top -> form'
      | Bot, _
      | _, Bot -> Bot
      | Conj conj1, Conj conj2 -> Conj (List.rev_append conj1 conj2)

    let wedge_conjunction diseq_list = function
      | Top -> Conj diseq_list
      | Bot -> Bot
      | Conj diseq_l -> Conj (List.rev_append diseq_list diseq_l)

    let extract_one_diseq = function
      | Conj [diseq] -> diseq, Top
      | Conj (diseq::q) -> diseq, Conj q
      | _ -> Config.internal_error "[formula.ml >> Formula.Term..extract_one_diseq] There should be at least one disequation."

    exception Is_Bot

    (* The variables of [Variable.currently_linked] should included the linked variables
       of the disequation. We also assume that there are some linked variables.
       We assume that [Variable.currently_linked] is not empty. *)
    let instantiate_and_normalise form = match form with
      | Top | Bot -> form
      | Conj diseq_l ->
          if !Variable.currently_linked = []
          then form
          else
            let f_norm = match !Variable.currently_linked with
              | [{ link = TLink t; _} as x] -> Diseq.T.instantiate_and_normalise_one_variable x t
              | _ -> Diseq.T.instantiate_and_normalise
            in

            try
              let diseq_l_1 =
                List.fold_left (fun acc diseq ->
                  let diseq_1 = f_norm diseq in
                  match diseq_1 with
                    | Diseq.T.Top -> acc
                    | Diseq.T.Bot -> raise Is_Bot
                    | _ -> diseq_1 :: acc
                ) [] diseq_l
              in

              if diseq_l_1 = []
              then Top
              else Conj diseq_l_1
            with Is_Bot -> Bot

    let instantiate_and_normalise_full form = match form with
      | Top | Bot -> form
      | Conj diseq_l ->
          try
            let diseq_l_1 =
              List.fold_left (fun acc diseq ->
                let diseq_1 = Diseq.T.instantiate_and_normalise diseq in
                match diseq_1 with
                  | Diseq.T.Top -> acc
                  | Diseq.T.Bot -> raise Is_Bot
                  | _ -> diseq_1 :: acc
              ) [] diseq_l
            in

            if diseq_l_1 = []
            then Top
            else Conj diseq_l_1
          with Is_Bot -> Bot

    let rename_and_instantiate form = match form with
      | Top | Bot -> form
      | Conj conj ->
          Config.debug (fun () ->
            if List.exists (fun dis -> dis = Diseq.T.Top || dis = Diseq.T.Bot) conj
            then Config.internal_error "[formula.ml >> Formula.T.rename_and_instantiate] The formula should be normalised before applying renaming."
          );
          Conj (List.map Diseq.T.rename_and_instantiate conj)

    let debug_no_linked_variables = function
      | Top
      | Bot -> true
      | Conj conj -> List.for_all Diseq.T.debug_no_linked_variables conj

    let display ?(follow_link=true) out = function
      | Top -> top out
      | Bot -> bot out
      | Conj conj ->
          display_list (Diseq.T.display ~follow_link:follow_link out) (Display.wedge out) conj

  end


  module R = struct

    type t =
      | Top
      | Bot
      | Conj of Diseq.R.t list

    exception Is_Bot

    let wedge_conjunction diseq_list = function
      | Top -> Conj diseq_list
      | Bot -> Bot
      | Conj diseq_l -> Conj (List.rev_append diseq_list diseq_l)

    let wedge diseq = function
      | Top -> Conj [diseq]
      | Bot -> Bot
      | Conj diseq_l -> Conj (diseq::diseq_l)

    let intern_instantiate_and_normalise f_norm = function
      | Top -> Top
      | Bot -> Bot
      | Conj diseq_l ->
          try
            let diseq_l_1 =
              List.fold_left (fun acc diseq ->
                let diseq_1 = f_norm diseq in
                match diseq_1 with
                  | Diseq.R.Top -> acc
                  | Diseq.R.Bot -> raise Is_Bot
                  | _ -> diseq_1 :: acc
              ) [] diseq_l
            in

            if diseq_l_1 = []
            then Top
            else Conj diseq_l_1
          with Is_Bot -> Bot

    let instantiate_and_normalise = intern_instantiate_and_normalise Diseq.R.instantiate_and_normalise

    (* The list currently_linked should only contain one element x *)
    let instantiate_and_normalise_one_variable_constructor x r =
      Config.debug (fun () -> match !Recipe_Variable.currently_linked with
        | [x'] when x == x' -> ()
        | _ -> Config.internal_error "[formula.ml >> Formula.R.instantiate_and_normalise_one_variable_constructor] The list Recipe_Variable.currently_linked should only contain the element [x]"
      );
      intern_instantiate_and_normalise (Diseq.R.instantiate_and_normalise_one_variable_constructor x r)

    let instantiate_and_normalise_one_variable x r =
      Config.debug (fun () -> match !Recipe_Variable.currently_linked with
        | [x'] when x == x' -> ()
        | _ -> Config.internal_error "[formula.ml >> Formula.R.instantiate_and_normalise_one_variable] The list Recipe_Variable.currently_linked should only contain the element [x]"
      );
      intern_instantiate_and_normalise (Diseq.R.instantiate_and_normalise_one_variable x r)

    let display ?(follow_link=true) out = function
      | Top -> top out
      | Bot -> bot out
      | Conj conj ->
          display_list (Diseq.R.display ~follow_link:follow_link out) (Display.wedge out) conj
  end

  module M = struct

    type t =
      | Top
      | Bot
      | Conj of Diseq.M.t list

    exception Is_Bot

    let intern_instantiate_and_normalise f_norm_rec form =
      Config.debug (fun () ->
        if !Recipe_Variable.currently_linked = []
        then Config.internal_error "[formula.ml >> Formula.M.instantiate_and_normalise] There should be an instantiation of recipe variable."
      );

      match form with
      | Top -> Top
      | Bot -> Bot
      | Conj diseq_l ->
          let f_norm_mix = match !Variable.currently_linked with
            | [] -> Diseq.M.instantiate_and_normalise_only_recipe f_norm_rec
            | [{ link = TLink t; _} as x] -> Diseq.M.instantiate_and_normalise (Diseq.T.instantiate_and_normalise_one_variable x t) f_norm_rec
            | _ -> Diseq.M.instantiate_and_normalise Diseq.T.instantiate_and_normalise f_norm_rec
          in

          try
            let diseq_l' =
              List.fold_left (fun acc diseq ->
                let diseq' = f_norm_mix diseq in
                match diseq' with
                  | Diseq.M.Top -> acc
                  | Diseq.M.Bot -> raise Is_Bot
                  | _ -> diseq'::acc
              ) [] diseq_l
            in
            if diseq_l' = []
            then Top
            else Conj diseq_l'
          with Is_Bot -> Bot

    let instantiate_and_normalise_one_variable_constructor x r =
      intern_instantiate_and_normalise (Diseq.R.instantiate_and_normalise_one_variable_constructor x r)

    let instantiate_and_normalise_one_variable x r =
      intern_instantiate_and_normalise (Diseq.R.instantiate_and_normalise_one_variable x r)

    let instantiate_and_normalise = intern_instantiate_and_normalise Diseq.R.instantiate_and_normalise

    let instantiate_and_normalise_full form = match form with
      | Top | Bot -> form
      | Conj diseq_l ->
          try
            let diseq_l' =
              List.fold_left (fun acc diseq ->
                let diseq' = Diseq.M.instantiate_and_normalise Diseq.T.instantiate_and_normalise Diseq.R.instantiate_and_normalise diseq in
                match diseq' with
                  | Diseq.M.Top -> acc
                  | Diseq.M.Bot -> raise Is_Bot
                  | _ -> diseq'::acc
              ) [] diseq_l
            in
            if diseq_l' = []
            then Top
            else Conj diseq_l'
          with Is_Bot -> Bot

    let wedge diseq = function
      | Top -> Conj [diseq]
      | Bot -> Bot
      | Conj diseq_l -> Conj (diseq::diseq_l)

    let rename_and_instantiate vars form = match form with
      | Top | Bot -> form
      | Conj conj ->
          Variable.auto_cleanup_with_reset_notail (fun () ->
            List.iter (fun v -> Variable.link_search v) vars;
            let conj' = List.map_q Diseq.M.rename_and_instantiate_exclude_universal_slink conj in
            if conj == conj'
            then form
            else Conj conj'
          )


  end
end
