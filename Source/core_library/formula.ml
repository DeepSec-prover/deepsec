open Types
open Term
open Display

(***********************************
***          Disequations        ***
************************************)

module Diseq = struct

  module Term = struct

    type t =
      | Top
      | Bot
      | Disj of (variable * term) list

    (* Generation *)

    let of_linked_variables v_list =
      if v_list = []
      then Bot
      else
        Disj (List.rev_map (fun v -> match v.link with
          | TLink t -> v, Term.instantiate t
          | _ -> Config.internal_error "[formula.ml >> Diseq.Term.of_linked_variables] There should only be variables linked with TLink."
        ) v_list)

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

    (* Display *)

    let display out = function
      | Top -> top out
      | Bot -> bot out
      | Disj diseq_list ->
          let univ_vars = ref [] in

          let rec find_univ_var = function
            | Var v when v.link = SLink -> ()
            | Var v when v.quantifier = Universal && v.link = NoLink ->
                v.link <- SLink;
                univ_vars := v :: !univ_vars
            | Func(_,args) -> List.iter find_univ_var args
            | _ -> Config.internal_error "[formula.ml >> Diseq.Term.display] The variables in the disequality should not be linked."
          in

          let display_single (v,t) = Printf.sprintf "%s %s %s" (Variable.display out v) (neqs out) (Term.display out t) in

          List.iter (fun (_,t2) -> find_univ_var t2) diseq_list;

          if !univ_vars = []
          then Printf.sprintf "%s" (display_list display_single (Printf.sprintf " %s " (vee out)) diseq_list)
          else
            begin
              List.iter (fun v -> v.link <- NoLink) !univ_vars;
              Printf.sprintf "%s %s.%s" (forall out) (display_list (Variable.display out) "," !univ_vars) (display_list display_single (Printf.sprintf " %s " (vee out)) diseq_list)
            end
  end

  module Recipe = struct

    type t =
      | Top
      | Bot
      | Disj of (recipe_variable * recipe) list
          (* Type of the variable is almost equal or bigger than the type of the recipe *)

    (* [of_linked_variables v_list to_be_univ_vars] returns the disequalities corresponding to
       the negation represented by the links in [v_list]. The variables in [to_be_univ_vars]
       should be transformed as universal variables.
       All variables in [v_list] should be linked and should not be in [to_be_univ_vars].
       Variables in [to_be_univ_vars] can be linked. Only the unlinked variables are transformed
       in universal variables. *)
    let of_linked_variables v_list to_be_univ_vars =
      if v_list = []
      then Bot
      else if to_be_univ_vars = []
      then
        Disj (List.rev_map (fun v -> match v.link_r with
          | CRLink r -> v, Recipe.instantiate_context r
          | _ -> Config.internal_error "[formula.ml >> Diseq.Recipe.of_linked_variables] There should only be variables linked with CRLink (generated from mgs)."
        ) v_list)
      else
        begin
          let renamed_vars = ref [] in

          List.iter (fun v -> match v.link_r with
            | RNoLink ->
                let v' = Recipe_Variable.fresh Universal v.type_r in
                v.link_r <- RLink (RVar v');
                renamed_vars := v :: !renamed_vars
            | _ ->  ()
          ) to_be_univ_vars;

          let diseq =
            List.fold_left (fun acc v -> match v.link_r with
              | CRLink r -> (v, Recipe.instantiate_context r)::acc
              | _ -> Config.internal_error "[formula.ml >> Diseq.Recipe.of_linked_variables] There should only be variables linked with CRLink (generated from mgs) (2)."
            ) [] v_list
          in

          List.iter (fun v -> v.link_r <- RNoLink) !renamed_vars;

          Disj diseq
        end

    (* We assume here that [x] is not already linked with [r].
       We assume that [r] is of the form [f(x_1,...,x_n)] with x_1,...,x_n fresh.
       Moreover no variables in the disequality should be linked. *)
    let instantiate_and_normalise_constructor x r = function
      | Top -> Top
      | Bot -> Bot
      | Disj diseq_list ->
          (* We link the variables of the disequality *)

          List.iter (fun (y,r') -> y.link_r <- RLink r') diseq_list;

          (* We unify [x] with [r] *)
          begin match x.link_r with
            | RNoLink ->
                (* In such a case, we can directly instantiate the variables without
                   applying [Recipe.unify] since [x_1,...,x_n] are fresh.*)
                x.link_r <- RLink r;
                let r = Disj (List.rev_map (fun (y,r') -> y, Recipe.instantiate r') diseq_list) in
                x.link_r <- RNoLink;
                r
            | RLink r' ->
                let tmp = !Recipe_Variable.currently_linked in
                Recipe_Variable.currently_linked := [];

                let result =
                  try
                    Recipe.unify r r';

                    let diseq_list_1 =
                      List.fold_left (fun acc var ->
                        if var.quantifier_r = Universal
                        then acc
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
                    Disj diseq_list_2
                  with Recipe.Not_unifiable -> Top
                in

                List.iter (fun v -> v.link_r <- RNoLink) !Recipe_Variable.currently_linked;
                List.iter (fun (v,_) -> v.link_r <- RNoLink) diseq_list;
                Recipe_Variable.currently_linked := tmp;
                result
            | _ -> Config.internal_error "[formula.ml >> Diseq.Recipe.instantiate_and_normalise_constructor] Unexpected link."
          end
  end

  module Mixed = struct

    type t =
      | Top
      | Bot
      | Disj of (term * term) list * (recipe * recipe) list
  end
end


module Formula = struct

  module Term = struct

    type t =
      | Top
      | Bot
      | Conj of Diseq.Term.t list

    (* We assume that [diseq] is neither top or bot. *)
    let wedge diseq = function
      | Top -> Conj [diseq]
      | Bot -> Bot
      | Conj diseq_l -> Conj (diseq::diseq_l)

    let extract_one_diseq = function
      | Conj [diseq] -> diseq, Top
      | Conj (diseq::q) -> diseq, Conj q
      | _ -> Config.internal_error "[formula.ml >> Formula.Term..extract_one_diseq] There should be at least one disequation."

    exception Is_Bot

    let instantiate_and_normalise = function
      | Top -> Top
      | Bot -> Bot
      | Conj diseq_l ->
          try
            let diseq_l_1 =
              List.fold_left (fun acc diseq ->
                let diseq_1 = Diseq.Term.instantiate_and_normalise diseq in
                match diseq_1 with
                  | Diseq.Term.Top -> acc
                  | Diseq.Term.Bot -> raise Is_Bot
                  | _ -> diseq_1 :: acc
              ) [] diseq_l
            in

            if diseq_l_1 = []
            then Top
            else Conj diseq_l_1
          with Is_Bot -> Bot
  end


  module Recipe = struct

    type t =
      | Top
      | Bot
      | Conj of Diseq.Recipe.t list

  end

  module Mixed = struct

    type t =
      | Top
      | Bot
      | Conj of Diseq.Mixed.t list

  end
end
