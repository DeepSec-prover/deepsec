(* Process manipulation for equivalence by session *)
open Extensions
open Types
open Term
open Formula

module Label = struct

  type t =
    {
      prefix : int list;
      last_index : int
    }

  type complete =
    | LStd of t
    | LComm of t * t * name * bool
        (** In [LComm(lbl1,lbl2,d,prio)]:
            - [lbl1] should smaller than [lbl2]
            - [d] is the private channel on which the communication occur
            - [prio] indicate if the communication was done with priority. *)

  let initial = { prefix = []; last_index = 0 }

  let add_position (lbl:t) pos = { prefix = lbl.prefix @ [lbl.last_index]; last_index = pos }

  let add_position_from_prefix prefix pos = { prefix = prefix; last_index = pos }

  (*** Order relation ***)

  let rec independent_prefix (prefix1:int list) (prefix2:int list) = match prefix1, prefix2 with
    | [], _
    | _, [] -> 0
    | pos1::q1, pos2::q2 ->
        match compare pos1 pos2 with
          | 0 -> independent_prefix q1 q2
          | i -> i

  let independent lbl1 lbl2 =
    let rec independent_prefix (prefix1:int list) prefix2 = match prefix1, prefix2 with
      | [], [] -> compare lbl1.last_index lbl2.last_index
      | [], _
      | _, [] -> 0
      | pos1::q1, pos2::q2 ->
          match compare pos1 pos2 with
            | 0 -> independent_prefix q1 q2
            | i -> i
    in
    independent_prefix lbl1.prefix lbl2.prefix


  (* We assume that the second and third argument are sorted *)
  let all_independant lbl1 lbl2_1 lbl2_2 = match independent lbl1 lbl2_1 with
    | -1 -> true
    | 0 -> false
    | _ -> independent lbl1 lbl2_2 <> 0

  (** Does take into account the priority status of private communication.
      When there is a LComm with priority, it always returs one unless
      the other label is also a LComm with priority on same channel. In
      that case, a normal check of independence is done. *)
  let independent_complete clbl1 clbl2 = match clbl1, clbl2 with
    | LComm(lbl1_1,lbl1_2,c1,prio1), LComm(lbl2_1,lbl2_2,c2,prio2) ->
        if (prio1 && prio2 && c1 == c2) || not (prio1 || prio2)
        then
          begin match independent lbl1_1 lbl2_1 with
            | 0 -> 0
            | -1 -> if all_independant lbl1_2 lbl2_1 lbl2_2 then -1 else 0
            | _ -> if all_independant lbl2_2  lbl1_1 lbl1_2 then 1 else 0
          end
        else 1
    | LComm(_,_,_,true), _ | _, LComm(_,_,_,true) -> 1
    | LStd lbl1, LStd lbl2 -> independent lbl1 lbl2
    | LStd lbl1, LComm(lbl2_1,lbl2_2,_,_) ->
        begin match independent lbl1 lbl2_1 with
          | 1 -> if independent lbl1 lbl2_2 = 0 then 0 else 1
          | i -> i
        end
    | LComm(lbl1_1,lbl1_2,_,_), LStd lbl2 ->
        begin match independent lbl1_1 lbl2 with
          | -1 -> if independent lbl1_2 lbl2 = 0 then 0 else -1
          | i -> i
        end

  (*** Creation of complete ***)

  let create_complete_comm lbl1 lbl2 ch prio =
    Config.debug (fun () ->
      if independent lbl1 lbl2 = 0
      then Config.internal_error "[session_process.ml >> Label.create_complete_comm] Labels should be independent."
    );
    if independent lbl1 lbl2 = -1
    then LComm(lbl1,lbl2,ch,prio)
    else LComm(lbl2,lbl1,ch,prio)
end

module Block = struct

  (** Contrary to previous previous version of the session. We split the notion of
      block in two;
        - One part only contain labels and improper status.
        - The second part contains the recipes, axioms and max var.

      Considering that all traces within a symbolic set have the same block sequence
      except for the labels and improper status, we can compute once the second part
      of the block for all traces in the set.
  *)

  type recipe_block =
    {
      variables : recipe_variable list;
      used_axioms : int list; (* Ordered from the smallest to the biggest axiom *)
      bound_axioms : (int * int) option;
      maximal_var : int
    }

  type local_blocks =
    {
      local_proper_blocks : Label.complete list;
      local_improper_blocks : Label.complete list;
    }

  type general_blocks =
    {
      recipe_blocks : recipe_block list; (* Ordered from the most recent to the oldest *)
      current_recipe_block : recipe_block option; (* = None only when we are on improper phase *)

      number_blocks : int; (* Kept as List.length recipe_block *)
      ground_index : int; (* Inverse index of recipe_block such that all recipe
        block with this index or below are ground.
        Inverse index of a list [ t1,...,t_n ] are n-1, ..., 0 *)

      current_block_sure_proper : bool;
      last_added_axiom : int (* Last axiom that was added *)
    }

  (*** Creation ***)

  let empty_recipe_block =
    {
      variables = [];
      used_axioms = [];
      bound_axioms = None;
      maximal_var = 0
    }

  let empty_general =
    {
      recipe_blocks = [];
      current_recipe_block = Some empty_recipe_block ;
      number_blocks = 0;
      ground_index = -1;
      current_block_sure_proper = false;
      last_added_axiom = 0
    }

  (*** Update ***)

  (** [check_and_update_axiom csys gen_recipe] will update [gen_recipe] by first
    retrieving the maximal recipe type from the constraint system [csys] and
    second compare it with the [gen_recipe.last_added_axiom]:
      - If they are the same then it means no usefull axiom have been added (even
        if it is after an output.)
      - If they are not the same then the current block will be updated.
    This function should only be applied after constraints resolution. *)
  let add_axiom_after_constraint_solving max_type gen_block =
    if gen_block.last_added_axiom = max_type
    then
      (* Axiom was not added in the knowledge base *)
      Some gen_block
    else
      (* Axiom was added in the knowledge base *)
      match gen_block.current_recipe_block with
        | None -> None
        | Some r_block ->
            let current_recipe_block' = match r_block.bound_axioms with
              | None -> { r_block with bound_axioms = Some (max_type,max_type) }
              | Some(ax1,_) -> { r_block with bound_axioms = Some(ax1,max_type) }
            in
            Some { gen_block with last_added_axiom = max_type; current_recipe_block = Some current_recipe_block'; current_block_sure_proper = true }

  let add_input_variable x gen_block = match gen_block.current_recipe_block with
    | None -> Config.internal_error "[session_process.ml >> add_input_variable] Should contain at least a current block."
    | Some c_block ->
        let c_block' = { c_block with variables = x::c_block.variables; maximal_var = max x.type_r c_block.maximal_var } in

        { gen_block with current_recipe_block = Some c_block' }

  let close_current_recipe_block gen_block = match gen_block.current_recipe_block with
    | None -> Config.internal_error "[session_process.ml >> Block.add_new_current_recipe_block] Should not be used in improper phase."
    | Some c_block ->
        if gen_block.current_block_sure_proper
        then
          { gen_block with
            recipe_blocks = c_block::gen_block.recipe_blocks;
            current_recipe_block = Some empty_recipe_block;
            number_blocks = gen_block.number_blocks + 1;
            current_block_sure_proper = false
          }
        else
          { gen_block with
            current_recipe_block = None;
            current_block_sure_proper = false
          }

  let is_improper_phase gen_block = gen_block.current_recipe_block = None

  let rec add_axiom_in_sorted_list (i:int) axiom_list = match axiom_list with
    | [] -> [i]
    | j::q when j < i -> j::(add_axiom_in_sorted_list i q)
    | j::_ when j = i -> axiom_list
    | _ -> i::axiom_list

  let update_recipe block =
    let used_axioms_ref = ref block.used_axioms in
    let max_var = ref 0 in
    let used_vars = ref [] in

    let rec explore_recipe = function
      | RVar { link_r = RLink r; _ }
      | CRFunc(_,r) -> explore_recipe r
      | RVar x ->
          max_var := max !max_var x.type_r;
          if not (List.memq x !used_vars)
          then used_vars := x :: !used_vars
      | RFunc(_,args) -> List.iter explore_recipe args
      | Axiom i -> used_axioms_ref := add_axiom_in_sorted_list i !used_axioms_ref
    in

    List.iter (fun x -> explore_recipe (RVar x)) block.variables;

    let block' = { block with variables = !used_vars; used_axioms = !used_axioms_ref; maximal_var = !max_var } in
    if !used_vars = []
    then (block',true)
    else (block',false)

  (** [update_recipes_in_general_block gen_block] update all the blocks in [gen_block]
      by instantiating the variables and gathering the remaning variables and axioms.
      This function should only be applied after constraints resolution. *)
  let update_recipes_in_general_block gen_block =
    let ground_index = ref gen_block.ground_index in

    let rec explore_blocks index blocks =
      if index = !ground_index
      then (blocks,true)
      else
        match blocks with
          | [] -> ([],true)
          | block::q_b ->
              let (q_b',all_ground) = explore_blocks (index-1) q_b in
              if block.variables = []
              then
                begin
                  ground_index := index;
                  (block::q_b',true)
                end
              else
                begin
                  let (block',is_ground) = update_recipe block in
                  let all_ground' = is_ground && all_ground in
                  if all_ground' then ground_index := index;
                  (block'::q_b',all_ground')
                end
    in

    let (recipe_blocks',_) = explore_blocks (gen_block.number_blocks-1) gen_block.recipe_blocks in
    let current_recipe_block' = match gen_block.current_recipe_block with
      | None -> None
      | Some c_block -> Some (fst (update_recipe c_block))
    in

    { gen_block with
      recipe_blocks = recipe_blocks';
      current_recipe_block = current_recipe_block';
      ground_index = !ground_index
    }

  let tansition_proper_to_improper_phase local_blocks = match local_blocks.local_proper_blocks with
    | [] -> Config.internal_error "[session_process.ml >> Block.transition_proper_to_improper_phase] The local block should contain at least the initial label."
    | lbl :: q ->
        match lbl with
          | Label.LComm(_,_,_,true) -> { local_proper_blocks = q; local_improper_blocks = [] }
          | _ -> { local_proper_blocks = q; local_improper_blocks = [lbl] }

  (*** Test for partial reduction ***)

  let rec all_axiom_excluded (min_ax:int) max_ax = function
    | [] -> true
    | ax :: q -> (ax > max_ax) || (ax < min_ax && all_axiom_excluded min_ax min_ax q)

  let rec is_faulty lbl_block r_block lbl_block_l r_block_l = match lbl_block_l, r_block_l with
    | [],[] -> false
    | [], _ | _, [] -> Config.internal_error "[session_process.ml >> Block.is_faulty] The size of the lists should be equal."
    | lbl_b_i::q_lbl, r_b_i::q_r ->
        match Label.independent_complete lbl_block lbl_b_i with
          | -1 ->
              begin match r_b_i.bound_axioms with
                | None -> true
                | Some(min_ax,max_ax) -> r_block.maximal_var < min_ax && all_axiom_excluded min_ax max_ax r_block.used_axioms
              end
          | 1 -> is_faulty lbl_block r_block q_lbl q_r
          | _ -> false

  let is_authorised previous_ground_index gen_block local_block =
    let full_r_block_l = match gen_block.current_recipe_block with
      | None -> gen_block.recipe_blocks
      | Some r_block -> r_block :: gen_block.recipe_blocks
    in

    let rec explore_block index lbl_block_l r_block_l =
      if index = previous_ground_index
      then true
      else
        match lbl_block_l, r_block_l with
          | [], _ | [_], _ -> true
          | _, [] -> Config.internal_error "[session_process.ml >> Block.is_authorised] Lists shouls have the same size."
          | lbl_block::q_lbl, r_block::q_r ->
              if is_faulty lbl_block r_block q_lbl q_r
              then false
              else explore_block (index-1) q_lbl q_r
    in

    explore_block gen_block.number_blocks local_block.local_proper_blocks full_r_block_l
end

module Channel = struct

  type t =
    | CPublic of symbol
    | CPrivate of name * bool
        (* Indicates whether the internal communication on this channel can
           never have a conflict in the future.*)

  let compare ch1 ch2 = match ch1,ch2 with
    | CPublic f1, CPublic f2 -> compare f1.index_s f2.index_s
    | CPrivate(n1,prio1), CPrivate(n2,prio2) ->
        begin match compare prio1 prio2 with
          | 0 -> compare n1.index_n n2.index_n
          | i -> - i
        end
    | CPrivate _, _ -> -1
    | _ -> 1

  let of_term no_conflict_names = function
    | Func(f,_) ->
        if not f.public || f.arity <> 0
        then Config.internal_error "[session_process.ml >> Channel.of_term] The symbol should be of arity 0 and public.";
        CPublic f
    | Name n -> CPrivate(n,(List.memq n no_conflict_names))
    | _ -> Config.internal_error "[session_process.ml >> Channel.of_term] The channel should not be a variable."

  let recipe_of = function
    | CPublic f -> RFunc(f,[])
    | _ -> Config.internal_error "[session_process.ml >> Channel.recipe_of] Only public channels can be transformed into a recipe."

  let is_public = function
    | CPublic _ -> true
    | _ -> false

  let is_private = function
    | CPrivate _ -> true
    | _ -> false

  let is_equal ch1 ch2 = match ch1, ch2 with
    | CPublic f1, CPublic f2 -> f1 == f2
    | CPrivate(n1,_), CPrivate(n2,_) -> n1 == n2
    | _ -> false
end

module NameList = List.Ordered(struct type t = name let compare n1 n2 = compare n1.index_n n2.index_n end)

module Labelled_process = struct

  type channel_set = name list (* Always kept ordered. *)

  type equations = (variable * term) list

  type used_data =
    {
      variables : variable list;
      names : variable list
    }

  type t =
    | PStart of t
    | PNil
    | POutput of Channel.t * term * t * Label.t option * position * used_data * channel_set
    | PInput of Channel.t * variable * t * Label.t option * position * used_data * channel_set
    | PCondition of equations list * Formula.T.t * variable list (* fresh variables *) * t * t * used_data
    | PNew of variable * name * t * used_data
    | PPar of t list
    | PBangStrong of t list (* Broken *) * t list (* Standard *)
    | PBangPartial of t list

  (*** Find cells ***)

  let find_cells proc =
    let cells = ref [] in

    let rec explore = function
      | Nil -> []
      | Output(Func _,_,p,_)
      | Input(Func _,_,p,_) -> explore p
      | Output(Name n,_,p,_) ->
          let out_ch = explore p in

          if n.link_n <> NNoLink
          then out_ch (* Already detected as not a cell *)
          else
            if List.memq n out_ch
            then
              begin
                List.iter Name.link_search out_ch;
                List.filter (fun n' -> n != n') out_ch
              end
            else n::out_ch
      | Input(Name n,_,p,_) ->
          let out_ch = explore p in

          if n.link_n <> NNoLink
          then out_ch (* Already detected as not a cell *)
          else List.filter (fun n' -> n != n') out_ch
      | Output _ | Input _ -> Config.internal_error "[session_process.ml >> find_cells] Wrong format of channels"
      | IfThenElse(_,_,p1,p2,_)
      | Let (_,_,p1,p2,_) ->
          let out_ch1 = explore p1 in
          let out_ch2 = explore p2 in

          List.fold_left (fun acc n ->
            if n.link_n = NNoLink
            then
              if List.memq n out_ch2
              then acc
              else n::acc
            else acc
          ) out_ch2 out_ch1
      | New(n,p,_) ->
          let out_ch = explore p in
          if n.link_n = NNoLink
          then cells := n :: !cells;
          List.filter (fun n' -> n != n') out_ch
      | Par p_list -> explore_list p_list
      | Bang ([],_) -> Config.internal_error "[session_process.ml >> find_cells] Bang should contain at least 2 processes."
      | Bang (p::_,_) ->
          let out_ch = explore p in
          List.iter Name.link_search out_ch;
          []
      | Choice _ -> Config.internal_error "[session_process.ml >> find_cells] Processes should not contain any choice."

    and explore_list = function
      | [] -> []
      | p::q ->
          let out_ch = explore p in
          let out_ch_q = explore_list q in

          List.iter (fun n ->
            if List.memq n out_ch
            then Name.link_search n
          ) out_ch_q;

          let l1 = List.fold_left (fun acc n -> if n.link_n = NNoLink then n::acc else acc) [] out_ch in
          List.fold_left (fun acc n -> if n.link_n = NNoLink then n::acc else acc) l1 out_ch_q
    in

    Name.auto_cleanup_with_reset_notail (fun () ->
      let l = explore proc in
      if l <> []
      then Config.internal_error "[session_process.ml >> find_cells] Explore proc should always return an empty list.";
      !cells
    )

  (*** Transformation from a process to labelled process ***)

  let link_used_data data =
    List.iter (fun v -> match v.link with
      | NoLink -> v.link <- SLink; Variable.currently_linked := v :: !Variable.currently_linked
      | _ -> ()
    ) data.variables;
    List.iter (fun n -> match n.link with
      | NoLink -> n.link <- SLink; Variable.currently_linked := n :: !Variable.currently_linked
      | _ -> ()
    ) data.names

  let rec link_names n = function
    | [] -> Config.internal_error "[session_process.ml >> link_names] Unexpected case"
    | (n',x)::_ when n == n' ->
        begin match x.link with
          | NoLink ->
              x.link <- SLink;
              Variable.currently_linked := x :: !Variable.currently_linked
          | SLink -> ()
          | _ -> Config.internal_error "[session_process.ml >> link_names] Unexpected link."
        end
    | _::q -> link_names n q

  let rec link_used_data_term assoc = function
    | Var ({ link = NoLink; _} as v) ->
        v.link <- SLink;
        Variable.currently_linked := v :: !Variable.currently_linked
    | Name n -> link_names n assoc
    | Func(_,args) -> List.iter (link_used_data_term assoc) args
    | _ -> ()

  let rec link_used_data_pattern assoc = function
    | PatEquality t -> link_used_data_term assoc t
    | PatTuple(_,args) -> List.iter (link_used_data_pattern assoc) args
    | _ -> ()

  (* We assume that the variables are not linked. *)
  let rec link_used_data_process = function
    | PStart p -> link_used_data_process p
    | PNil -> ()
    | POutput(_,_,_,_,_,data,_)
    | PInput(_,_,_,_,_,data,_)
    | PCondition(_,_,_,_,_,data)
    | PNew(_,_,_,data) -> link_used_data data
    | PPar p_list
    | PBangPartial p_list -> List.iter link_used_data_process p_list
    | PBangStrong(p_list1,p_list2) ->
        List.iter link_used_data_process p_list1;
        List.iter link_used_data_process p_list2

  let auto_cleanup_all f =
    Variable.auto_cleanup_with_reset_notail f

  let of_process proc =

    let rec replace_name_by_variables assoc t = match t with
      | Name n -> Var(List.assq n assoc)
      | Func(f,args) -> Func(f,List.map (replace_name_by_variables assoc) args)
      | _ ->
          Config.debug (fun () ->
            match t with
              | Var v when v.link <> NoLink -> Config.internal_error "[generic_process.ml >> generic_process_of_process] Variables should not be linked."
              | _ -> ()
          );
          t
    in

    let replace_name_by_variables_formula assoc = function
      | Formula.T.Bot -> Formula.T.Bot
      | Formula.T.Top -> Formula.T.Top
      | Formula.T.Conj conj_l ->
          Formula.T.Conj (
            List.map (function
              | Diseq.T.Bot | Diseq.T.Top -> Config.internal_error "[generic_process.ml >> generic_process_of_process] Unexpected case"
              | Diseq.T.Disj disj_l ->
                  Diseq.T.Disj (
                    List.map (fun (v,t) ->
                      Config.debug (fun () ->
                        if v.link <> NoLink
                        then Config.internal_error "[generics_process.ml >> generic_process_of_process] Variables should not be linked (2)."
                      );
                      (v,replace_name_by_variables assoc t)
                    ) disj_l
                  )
            ) conj_l
          )
    in

    let replace_name_by_variables_equations assoc =
        List.map (fun (v,t) ->
          Config.debug (fun () ->
            if v.link <> NoLink
            then Config.internal_error "[generic_process.ml >> generic_process_of_process] Variables should not be linked (3)."
          );
          (v,replace_name_by_variables assoc t)
        ) in

    let replace_fresh_vars_by_universal fresh_vars disequations =
      Variable.auto_cleanup_with_reset_notail (fun () ->
        List.iter (fun x ->
          let x' = Variable.fresh Universal in
          Variable.link_term x (Var x')
        ) fresh_vars ;

        Formula.T.instantiate_and_normalise_full disequations
      )
    in

    let filter_used_data prev_data =
      let vars =
        List.fold_left (fun acc v -> match v.link with
          | SLink -> v::acc
          | _ -> acc
        ) [] prev_data.variables
      in
      let names =
        List.fold_left (fun acc n -> match n.link with
          | SLink -> n::acc
          | _ -> acc
        ) [] prev_data.names
      in
      { variables = vars; names = names }
    in

    let rec get_pattern_vars vars = function
      | PatVar x -> vars := x :: !vars
      | PatTuple(_,args) -> List.iter (get_pattern_vars vars) args
      | _ -> ()
    in

    let rec term_of_pattern = function
      | PatVar x -> Var x
      | PatTuple(f,args) -> Func(f,List.map term_of_pattern args)
      | PatEquality t -> t
    in

    let cells = find_cells proc in

    let rec explore assoc prev_data = function
      | Nil -> PNil, []
      | Output(ch,t,p,pos) ->
          let (p',under_ch_set) = explore assoc prev_data p in

          let used_data =
            auto_cleanup_all (fun () ->
              link_used_data_process p';
              link_used_data_term assoc t;
              filter_used_data prev_data
            )
          in
          let ch' = Channel.of_term cells ch in
          let (ch_set,under_ch_set') = match ch' with
            | Channel.CPrivate(n,false) -> NameList.add n under_ch_set, NameList.remove n under_ch_set
            | _ -> under_ch_set, under_ch_set
          in
          POutput(ch',replace_name_by_variables assoc t,p',None,pos,used_data,under_ch_set'), ch_set
      | Input(ch,PatVar v,p,pos) ->
          Config.debug (fun () ->
            if v.link <> NoLink
            then Config.internal_error "[session_process.ml >> of_process] Variables should not be linked (4)."
          );

          let (p',under_ch_set) = explore assoc { prev_data with variables = v::prev_data.variables } p in

          let used_data =
            auto_cleanup_all (fun () ->
              link_used_data_process p';
              filter_used_data prev_data
            )
          in
          let ch' = Channel.of_term cells ch in
          let (ch_set,under_ch_set') = match ch' with
            | Channel.CPrivate(n,false) -> NameList.add n under_ch_set, NameList.remove n under_ch_set
            | _ -> under_ch_set, under_ch_set
          in
          PInput(ch',v,p',None,pos,used_data,under_ch_set'), ch_set
      | Input _ -> Config.internal_error "[session_process.ml >> of_process] Input should only have variable as pattern at this stage."
      | IfThenElse(t1,t2,pthen,pelse,_) ->
          Config.debug (fun () ->
            if !Variable.currently_linked <> [] || !Name.currently_linked <> []
            then Config.internal_error "[generic_process.ml >> generic_process_of_process] No variables or names should be linked."
          );

          let (pthen',ch_set_then) = explore assoc prev_data pthen in
          let (pelse',ch_set_else) = explore assoc prev_data pelse in

          let used_data =
            auto_cleanup_all (fun () ->
              link_used_data_process pthen';
              link_used_data_process pelse';
              link_used_data_term assoc t1;
              link_used_data_term assoc t2;
              filter_used_data prev_data
            )
          in
          let ch_set = NameList.union ch_set_then ch_set_else in
          let (equations_1,disequations_1) = Rewrite_rules.compute_equality_modulo_and_rewrite [(t1,t2)] in
          let equations_2 = List.map (replace_name_by_variables_equations assoc) equations_1 in
          let disequations_2 = replace_name_by_variables_formula assoc disequations_1 in
          PCondition(equations_2,disequations_2,[],pthen',pelse',used_data), ch_set
      | Let(pat,t,pthen,pelse,_) ->
          Config.debug (fun () ->
            if !Variable.currently_linked <> []
            then Config.internal_error "[determinate_process.ml >> generic_process_of_intermediate_process] No variables should be linked."
          );
          let fresh_vars = ref [] in
          get_pattern_vars fresh_vars pat;

          let (pthen',ch_set_then) = explore assoc { prev_data with variables = !fresh_vars @ prev_data.variables } pthen in
          let (pelse',ch_set_else) = explore assoc prev_data pelse in

          let used_data =
            auto_cleanup_all (fun () ->
              link_used_data_process pthen';
              link_used_data_process pelse';
              link_used_data_term assoc t;
              link_used_data_pattern assoc pat;
              filter_used_data prev_data
            )
          in

          let ch_set = NameList.union ch_set_then ch_set_else in
          let (equations_1,disequations_1) = Rewrite_rules.compute_equality_modulo_and_rewrite [(t,term_of_pattern pat)] in
          let disequations_2 = replace_fresh_vars_by_universal !fresh_vars disequations_1 in
          let disequations_3 = replace_name_by_variables_formula assoc disequations_2 in
          let equations_2 = List.map (replace_name_by_variables_equations assoc) equations_1 in
          PCondition(equations_2,disequations_3,!fresh_vars,pthen',pelse',used_data) ,ch_set
      | New(n,p,_) ->
          let x = Variable.fresh Free in
          let (p',ch_set) = explore ((n,x)::assoc) { prev_data with names = x::prev_data.names } p in
          let used_data =
            auto_cleanup_all (fun () ->
              link_used_data_process p';
              filter_used_data prev_data
            )
          in
          PNew(x,n,p',used_data), ch_set
      | Par p_list ->
          let (p_list',ch_set) =
            List.fold_right (fun p (acc_p,acc_ch_set) ->
              let (p',ch_set') = explore assoc prev_data p in
              let acc_ch_set' = NameList.union ch_set' acc_ch_set in
              (p'::acc_p,acc_ch_set')
            ) p_list ([],[])
          in
          PPar p_list' , ch_set
      | Bang(p_list,_) ->
          let (p_list',ch_set) =
            List.fold_right (fun p (acc_p,acc_ch_set) ->
              let (p',ch_set') = explore assoc prev_data p in
              let acc_ch_set' = NameList.union ch_set' acc_ch_set in
              (p'::acc_p,acc_ch_set')
            ) p_list ([],[])
          in
          PBangStrong([],p_list'), ch_set
      | Choice _ -> Config.internal_error "[session_process.ml >> Labelled_process.of_process] Should not contain choice operator."
    in

    let (p,_) = explore [] { variables = []; names = [] } proc in
    PStart p

  (*** Skeletons gathering ***)

  (* Each component (ch,mult,l) indicates [mult] action on the channel [ch], on labels of last positions in [l].
    The Internal list are ordered in decreasing order. *)
  type gathering_skeletons =
    {
      input_skel : (Channel.t * int * int list) list; (* Sorted by Channel.compare. *)
      output_skel : (Channel.t * int * int list) list; (* Sorted by Channel.compare. *)
      private_input_skel : int * int list;
      private_output_skel : int * int list;

      private_channels : (Channel.t * int * int) list; (* [c,nb_out,nb_int] indicates that there are [nb_out] outputs on [c]
        and [nb_in] inputs on [c].
        The list is sorted by Channel.compare. *)

      label_prefix : int list;
      par_created : bool
    }

  let rec add_private_channel is_output ch priv_list = match priv_list with
    | [] -> if is_output then [ ch, 1, 0 ] else [ ch, 0, 1 ]
    | ((ch',nb_out,nb_in) as t)::q ->
        match Channel.compare ch' ch with
          | -1 -> t :: (add_private_channel is_output ch q)
          | 0 -> if is_output then (ch',nb_out+1,nb_in)::q else (ch',nb_out,nb_in+1)::q
          | _ -> if is_output then (ch, 1, 0)::priv_list else (ch, 0, 1)::priv_list

  let rec add_channel_occurrence ch pos occ_list = match occ_list with
    | [] -> [(ch,1,[pos])]
    | ((ch',n,inter_list) as t)::q ->
        match Channel.compare ch' ch with
          | -1 -> t :: (add_channel_occurrence ch pos q)
          | 0 -> (ch',n+1,pos::inter_list)::q
          | _ -> (ch,1,[pos]) :: occ_list

  let add_output_in_skeleton ch pos skeletons = match ch with
    | Channel.CPublic _ -> { skeletons with output_skel = add_channel_occurrence ch pos skeletons.output_skel }
    | _ ->
        let (occ,inter_list) = skeletons.private_output_skel in
        { skeletons with
          private_output_skel = occ+1,pos::inter_list;
          private_channels = add_private_channel true ch skeletons.private_channels
        }

  let add_input_in_skeleton ch pos skeletons = match ch with
    | Channel.CPublic _ -> { skeletons with input_skel = add_channel_occurrence ch pos skeletons.input_skel }
    | _ ->
        let (occ,inter_list) = skeletons.private_input_skel in
        { skeletons with
          private_input_skel = occ+1,pos::inter_list;
          private_channels = add_private_channel false ch skeletons.private_channels
        }

  let rec is_equal_input_output (l1:(Channel.t * int * int list) list) l2 = match l1, l2 with
    | [], [] -> true
    | [],_ | _, [] -> false
    | (ch1,i1,_)::q1, (ch2,i2,_)::q2 ->
        i1 = i2 && Channel.is_equal ch1 ch2 && (is_equal_input_output q1 q2)

  let is_equal_skeletons skel1 skel2 =
    skel1.private_input_skel = skel2.private_input_skel &&
    skel1.private_output_skel = skel2.private_output_skel &&
    is_equal_input_output skel1.input_skel skel2.input_skel &&
    is_equal_input_output skel1.output_skel skel2.output_skel


  (*** Next transition ***)

  type proper_status =
    | Proper
    | ImproperNegPhase
    | ImproperPosFocusPhase

  type gathering_normalise =
    {
      original_subst : (variable * term) list;
      original_names : (variable * name) list;
      disequations : Formula.T.t
    }

  let normalise proper_status label gather_norm proc f_continuation f_next =
    let prefix_label = label.Label.prefix @ [ label.Label.last_index ] in
    let gather_skel =
      {
        input_skel = [];
        output_skel = [];
        private_input_skel = (0,[]);
        private_output_skel = (0,[]);
        private_channels = [];
        label_prefix = prefix_label;
        par_created = true

      }
    in

    let rec normalise_process current_index gather_norm gather_skel proc f_continuation f_next = match proc with
      | PStart _ -> Config.internal_error "[session_process.ml >> Labelled_process.normalise] A start process should not be normalised."
      | PNil -> f_continuation current_index gather_norm gather_skel proc f_next
      | POutput(ch,t,p,None,pos,used_data,ch_set) ->
          let apply () =
            let gather_skel_1 = add_output_in_skeleton ch current_index gather_skel in
            let proc1 = POutput(ch,t,p,Some (Label.add_position_from_prefix prefix_label current_index),pos,used_data,ch_set) in
            f_continuation (current_index+1) gather_norm gather_skel_1 proc1 f_next
          in
          begin match proper_status with
            | Proper -> apply ()
            | ImproperNegPhase -> if Channel.is_private ch then f_next () else apply ()
            | _ -> if Channel.is_private ch || gather_skel.input_skel <> [] then f_next () else apply ()
          end
      | PInput(ch,x,p,None,pos,used_data,ch_set) ->
          let apply () =
            let gather_skel_1 = add_input_in_skeleton ch current_index gather_skel in
            let proc1 = PInput(ch,x,p,Some (Label.add_position_from_prefix prefix_label current_index),pos,used_data,ch_set) in
            f_continuation (current_index+1) gather_norm gather_skel_1 proc1 f_next
          in
          begin match proper_status with
            | Proper -> apply ()
            | ImproperNegPhase -> f_next ()
            | ImproperPosFocusPhase -> if Channel.is_private ch || gather_skel.input_skel <> [] then f_next () else apply ()
          end
      | PCondition(equation_list,diseq_form,fresh_vars,pthen,pelse,_) ->
          let rec apply_positive f_next_1 = function
            | [] -> f_next_1 ()
            | equation::q ->
                Variable.auto_cleanup_with_reset (fun f_next_2 ->
                  let orig_subst_1 =
                    List.fold_left (fun acc v ->
                      let v' = Variable.fresh Existential in
                      Variable.link_term v (Var v');
                      (v,Var v') :: acc
                    ) gather_norm.original_subst fresh_vars
                  in

                  let is_unifiable =
                    try
                      List.iter (fun (v,t) -> Term.unify (Var v) t) equation;
                      true
                    with Term.Not_unifiable -> false
                  in

                  if is_unifiable
                  then
                    let disequations_1 = Formula.T.instantiate_and_normalise gather_norm.disequations in
                    if Formula.T.Bot = disequations_1
                    then f_next_2 ()
                    else normalise_process current_index { gather_norm with original_subst = orig_subst_1; disequations = disequations_1 } gather_skel pthen f_continuation f_next_2
                  else f_next_2 ()
                ) (fun () -> apply_positive f_next_1 q)
          in

          let apply_negative f_next_1 =
            let diseq_form_1 = Formula.T.instantiate_and_normalise_full diseq_form in
            if Formula.T.Bot = diseq_form_1
            then f_next_1 ()
            else
              let disequations_1 = Formula.T.wedge_formula diseq_form_1 gather_norm.disequations in
              normalise_process current_index { gather_norm with disequations = disequations_1 } gather_skel pelse f_continuation f_next_1
          in

          apply_positive (fun () ->
            apply_negative f_next
          ) equation_list
      | PNew(x,n,p,_) ->
          Variable.auto_cleanup_with_reset (fun f_next_1 ->
            Variable.link_term x (Name n);
            normalise_process current_index { gather_norm with original_names = ((x,n)::gather_norm.original_names) } gather_skel p f_continuation f_next_1
          ) f_next
      | PPar p_list ->
          normalise_process_list ~split_par:true current_index gather_norm gather_skel p_list (fun current_index_1 gather_norm_1 gather_skel_1 p_list_1 f_next_1 ->
            match p_list_1 with
              | [] -> f_continuation current_index_1 gather_norm_1 gather_skel_1 PNil f_next_1
              | [p] -> f_continuation current_index_1 gather_norm_1 gather_skel_1 p f_next_1
              | _ -> f_continuation current_index_1 gather_norm_1 gather_skel_1 (PPar p_list_1) f_next_1
          ) f_next
      | PBangStrong([],plist) ->
          normalise_process_list current_index gather_norm gather_skel plist (fun current_index_1 gather_norm_1 gather_skel_1 plist_1 f_next_1 ->
            match plist_1 with
              | [] -> f_continuation current_index_1 gather_norm_1 gather_skel_1 PNil f_next_1
              | [p] -> f_continuation current_index_1 gather_norm_1 gather_skel_1 p f_next_1
              | _ -> f_continuation current_index_1 gather_norm_1 gather_skel_1 (PBangStrong([],plist_1)) f_next_1
          ) f_next
      | PBangStrong _ -> Config.internal_error "[session_process.ml >> normalise_process] Normalisation should only be done on processes without broken symmetry"
      | PBangPartial plist ->
          normalise_process_list current_index gather_norm gather_skel plist (fun current_index_1 gather_norm_1 gather_skel_1 plist_1 f_next_1 ->
            match plist_1 with
              | [] -> f_continuation current_index_1 gather_norm_1 gather_skel_1 PNil f_next_1
              | [p] -> f_continuation current_index_1 gather_norm_1 gather_skel_1 p f_next_1
              | _ -> f_continuation current_index_1 gather_norm_1 gather_skel_1 (PBangPartial plist_1) f_next_1
          ) f_next
      | POutput _ | PInput _ -> Config.internal_error "[session_process.ml >> normalise_process] The inputs and outputs should not be already labeled."

    and normalise_process_list ?(split_par=false) current_index gather_norm gather_skel p_list f_continuation f_next = match p_list with
      | [] -> f_continuation current_index gather_norm gather_skel [] f_next
      | p::q ->
          normalise_process current_index gather_norm gather_skel p (fun current_index_1 gather_norm_1 gather_skel_1 p_1 f_next_1 ->
            normalise_process_list ~split_par:split_par current_index_1 gather_norm_1 gather_skel_1 q (fun current_index_2 gather_norm_2 gather_skel_2 q_2 f_next_2 ->
              match p_1 with
                | PNil -> f_continuation current_index_2 gather_norm_2 gather_skel_2 q_2 f_next_2
                | PPar plist_1 when split_par -> f_continuation current_index_2 gather_norm_2 gather_skel_2  (List.rev_append plist_1 q_2) f_next_2
                | _ -> f_continuation current_index_2 gather_norm_2 gather_skel_2  (p_1::q_2) f_next_2
            ) f_next_1
          ) f_next
    in

    normalise_process 1 gather_norm gather_skel proc (fun _ gather_norm_1 gather_skel_1 proc_1 f_next_1 ->
      match proc_1 with
        | POutput(ch,t,p,_,pos,used_data,ch_set) ->
            let gather_skel_2 =
              if fst gather_skel_1.private_output_skel = 1
              then { gather_skel_1 with private_output_skel = (1,[label.Label.last_index]); label_prefix = label.Label.prefix; par_created = false }
              else
                match gather_skel_1.output_skel with
                  | [f,1,_] -> { gather_skel_1 with output_skel = [f,1,[label.Label.last_index]]; label_prefix = label.Label.prefix; par_created = false }
                  | _ -> Config.internal_error "[session_process.ml >> normalise] There should be only one output."
            in
            let proc_2 = POutput(ch,t,p,Some label,pos,used_data,ch_set) in
            f_continuation gather_norm_1 gather_skel_2 proc_2 f_next_1
        | PInput(ch,x,p,_,pos,used_data,ch_set) ->
            let gather_skel_2 =
              if fst gather_skel_1.private_input_skel = 1
              then { gather_skel_1 with private_input_skel = (1,[label.Label.last_index]); label_prefix = label.Label.prefix }
              else
                match gather_skel_1.input_skel with
                  | [f,1,_] -> { gather_skel_1 with input_skel = [f,1,[label.Label.last_index]]; label_prefix = label.Label.prefix }
                  | _ -> Config.internal_error "[session_process.ml >> normalise] There should be only one output."
            in
            let proc_2 = PInput(ch,x,p,Some label,pos,used_data,ch_set) in
            f_continuation gather_norm_1 gather_skel_2 proc_2 f_next_1
        | _ -> f_continuation gather_norm_1 gather_skel_1 proc_1 f_next_1
    ) f_next

  (*** Testing ***)

  let rec exists_toplevel_public_output = function
    | PNil
    | PInput _ -> false
    | POutput(c,_,_,_,_,_,_) ->  Channel.is_public c
    | PPar plist
    | PBangPartial plist
    | PBangStrong(plist,[]) -> List.exists exists_toplevel_public_output plist
    | PBangStrong(plist,p::_) -> List.exists exists_toplevel_public_output plist || exists_toplevel_public_output p
    | _ -> Config.internal_error "[session_process.ml >> Labelled_process.exists_toplevel_public_output] Should only be applied on a normalised process."

  let count_toplevel_public_output plist =

    let rec explore_process n = function
      | [] -> n
      | PInput _ ::q
      | PNil :: q -> explore_process n q
      | POutput(c,_,_,_,_,_,_)::q when Channel.is_public c ->
          if Channel.is_public c
          then if n = 1 then 2 else explore_process 1 q
          else n
      | PPar p_list :: q
      | PBangPartial p_list :: q ->
          let n_1 = explore_process n p_list in
          if n_1 = 2 then 2 else explore_process n_1 q
      | PBangStrong(brok_plist,plist) :: q ->
          let n_1 = explore_process n brok_plist in
          if n_1 = 2
          then 2
          else
            let n_2 = explore_process n_1 plist in
            if n_2 = 2 then n_2 else explore_process n_2 q
      | _ -> Config.internal_error "[session_process.ml >> Labelled_process.count_toplevel_public_output] Should only be applied on a normalised process"
    in

    explore_process 0 plist

end

module Configuration = struct

  type matching_status =
    | ForAll
    | Exists
    | Both

  type t =
    {
      (* Processes *)
      input_and_private_proc : Labelled_process.t list;
      output_proc : Labelled_process.t list;
      focused_proc : Labelled_process.t option;
      pure_improper_proc : Labelled_process.t list;

      (* Blocks *)
      blocks : Block.local_blocks;

      (* Private channel *)
      private_channels : (Channel.t * int (* out *) * int (* in *)) list; (* Ordered by Channel.compare *)
    }

  type output_transition =
    {
      out_label : Label.t;
      out_term : term;
      out_position : position;
      out_matching_status : matching_status;
      out_gathering_normalise : Labelled_process.gathering_normalise;
      out_gathering_skeleton : Labelled_process.gathering_skeletons
    }

  (* Invariant:
    In the set of configuration, the skeletons of the processes are all the same.
    Thus we keep a list indicating the number of public channel.
      public_output_channels : (Channel.t * int) list (* Ordered by Channel.compare *)
  *)

  (** Link of used data **)

  let link_used_data f_next conf =
    Labelled_process.auto_cleanup_all (fun () ->
      List.iter Labelled_process.link_used_data_process conf.input_and_private_proc;
      List.iter Labelled_process.link_used_data_process conf.output_proc;
      begin match conf.focused_proc with
        | None -> ()
        | Some p -> Labelled_process.link_used_data_process p
      end;
      f_next ()
    )

  (*** Public output utilities ***)

  let rec remove_ch_from_public_output_channels ch = function
    | [] -> Config.internal_error "[session_process.ml >> Configuration.remove_ch_from_public_output_channels] The channel should be in the list"
    | (ch',i)::q when Channel.is_equal ch ch' -> if i = 1 then q else (ch',i-1)::q
    | t::q -> t::(remove_ch_from_public_output_channels ch q)

  let rec merge_public_output_channels_from_two_skel (skel1:(Channel.t * int * int list) list) skel2 = match skel1,skel2 with
    | [], skel | skel, [] -> List.map (fun (ch,i,_) -> (ch,i)) skel
    | (ch1,i1,_)::q1, (ch2,i2,_)::q2 ->
        match Channel.compare ch1 ch2 with
          | 0 -> (ch1,i1+i2)::(merge_public_output_channels_from_two_skel q1 q2)
          | 1 -> (ch2,i2)::(merge_public_output_channels_from_two_skel skel1 q2)
          | _ -> (ch1,i1)::(merge_public_output_channels_from_two_skel q1 skel2)

  let rec merge_public_output_channels chlist1 chlist2 = match chlist1,chlist2 with
    | [], chlist | chlist, [] -> chlist
    | (ch1,i1)::q1, (ch2,i2)::q2 ->
        match Channel.compare ch1 ch2 with
          | 0 -> (ch1,i1+i2)::(merge_public_output_channels q1 q2)
          | 1 -> (ch2,i2)::(merge_public_output_channels chlist1 q2)
          | _ -> (ch1,i1)::(merge_public_output_channels q1 chlist2)

  let rec merge_public_output_channels_from_one_skel (skel:(Channel.t * int * int list) list) chlist = match skel,chlist with
    | [], chlist -> chlist
    | skel, [] -> List.map (fun (ch,i,_) -> (ch,i)) skel
    | (ch1,i1,_)::q1, (ch2,i2)::q2 ->
        match Channel.compare ch1 ch2 with
          | 0 -> (ch1,i1+i2)::(merge_public_output_channels_from_one_skel q1 q2)
          | 1 -> (ch2,i2)::(merge_public_output_channels_from_one_skel skel q2)
          | _ -> (ch1,i1)::(merge_public_output_channels_from_one_skel q1 chlist)

  (*** Private channels utilities ***)

  let rec remove_ch_from_private_channels ch = function
    | [] -> Config.internal_error "[session_process.ml >> Configuration.remove_ch_from_private_channels] The channel should be in the list"
    | (ch',i_out,i_in)::q when Channel.is_equal ch ch' ->
        if i_out = 1 && i_in = 1 then q else (ch',i_out-1,i_in-1)::q
    | t::q -> t::(remove_ch_from_private_channels ch q)

  let rec merge_private_channels chlist1 chlist2 = match chlist1,chlist2 with
    | [], chlist | chlist, [] -> chlist
    | (ch1,out1,in1)::q1, (ch2,out2,in2)::q2 ->
        match Channel.compare ch1 ch2 with
          | 0 -> (ch1,out1+out2,in1+in2)::(merge_private_channels q1 q2)
          | 1 -> (ch2,out2,in2)::(merge_private_channels chlist1 q2)
          | _ -> (ch1,out1,in1)::(merge_private_channels q1 chlist2)

  (*** Output transition ***)

  let update_public_output_channel_from_output_transition ch out_chlist skel =
    let out_chlist_1 = remove_ch_from_public_output_channels ch out_chlist in
    merge_public_output_channels_from_one_skel skel.Labelled_process.output_skel out_chlist_1

  let update_private_channels_from_output_transition conf trans =
    merge_private_channels conf.private_channels trans.out_gathering_skeleton.Labelled_process.private_channels

  let main_next_public_output proper_status matching_status target_channel original_subst original_names conf (f_continuation : output_transition -> t -> unit)=
    Config.debug (fun () ->
      if conf.focused_proc <> None
      then Config.internal_error "[session_process.ml >> Configuration.next_public_output] An output transition should not be computed when there are still a focused process."
    );

    let already_assigned_forall = ref false in
    let only_forall = matching_status = ForAll in

    let rec explore_process proc f_cont f_next = match proc with
      | Labelled_process.POutput(c,t,p,Some label,pos,_,_) ->
          if not (Channel.is_equal target_channel c) || (only_forall && !already_assigned_forall)
          then f_next ()
          else
            let apply_normalisation matching_status_1 f_next_1 =
              let gather_norm =
                {
                  Labelled_process.original_subst = original_subst;
                  Labelled_process.original_names = original_names;
                  Labelled_process.disequations = Formula.T.Top
                }
              in
              Labelled_process.normalise proper_status label gather_norm p (fun gather_norm_1 gather_skel_1 p_1 f_next_2 ->
                let transition =
                  {
                    out_label = label;
                    out_term = t;
                    out_position = pos;
                    out_matching_status = matching_status_1;
                    out_gathering_normalise = gather_norm_1;
                    out_gathering_skeleton = gather_skel_1
                  }
                in
                f_cont transition p_1 f_next_2
              ) f_next_1
            in

            if !already_assigned_forall
            then apply_normalisation Exists f_next
            else apply_normalisation matching_status (fun () -> already_assigned_forall := true; f_next ())
      | Labelled_process.PPar plist ->
          explore_process_list ~split_par:true [] plist (fun transition plist_1 f_next_1 -> match plist_1 with
            | [] -> f_cont transition Labelled_process.PNil f_next_1
            | [p] -> f_cont transition p f_next_1
            | _ -> f_cont transition (Labelled_process.PPar plist_1) f_next_1
          ) f_next
      | Labelled_process.PBangStrong(brok_plist,plist) ->
          let nb_output = Labelled_process.count_toplevel_public_output [proc] in

          if nb_output = 0
          then f_next ()
          else
            (* Since the replication is strong, we need to tag one of [brok_plist] or one of [plist] as forall
               and do all brok_plist and one of plist as an Exists transition. *)
            explore_process_list [] brok_plist (fun transition brok_plist_1 f_next_1 ->
              if brok_plist_1 = [] && plist = []
              then f_cont transition Labelled_process.PNil f_next_1
              else
                if nb_output = 1 && transition.out_gathering_skeleton.Labelled_process.output_skel = []
                then
                  begin
                    Config.debug (fun () ->
                      if plist <> []
                      then Config.internal_error "[session_process.ml >> Configuration.next_public_output] When there is no more output then plist should be empty."
                    );
                    f_cont transition (Labelled_process.PBangPartial brok_plist_1) f_next_1
                  end
                else f_cont transition (Labelled_process.PBangStrong(brok_plist_1,plist)) f_next_1
            ) (fun () -> match plist with
              | [] -> f_next ()
              | p::q_list ->
                  explore_process p (fun transition p_1 f_next_1 ->
                    if p_1 = Labelled_process.PNil && q_list = [] && brok_plist = []
                    then f_cont transition Labelled_process.PNil f_next_1
                    else
                      if nb_output = 1 && transition.out_gathering_skeleton.Labelled_process.output_skel = []
                      then
                        begin
                          Config.debug (fun () ->
                            if q_list <> []
                            then Config.internal_error "[session_process.ml >> Configuration.next_public_output] When there is no more output then q_list should be empty."
                          );
                          f_cont transition (Labelled_process.PBangPartial(p_1::brok_plist)) f_next_1
                        end
                      else f_cont transition (Labelled_process.PBangStrong(p_1::brok_plist,q_list)) f_next_1
                  ) f_next
            )
      | Labelled_process.PBangPartial plist ->
          (* Since the replication is partial, we need to tag one of [plist] as forall
             and all plist as an Exists transition. *)
          explore_process_list [] plist (fun transition plist_1 f_next_1 -> match plist_1 with
            | [] -> f_cont transition Labelled_process.PNil f_next_1
            | [p] -> f_cont transition p f_next_1
            | _ -> f_cont transition (Labelled_process.PBangPartial plist_1) f_next_1
          ) f_next
      | Labelled_process.PInput(_,_,_,Some _,_,_,_) -> f_next ()
      | _ -> Config.internal_error "[session_process.ml >> Configuration.next_public_output] Should only find Input (with label), Output (with label), Par or Bang."

    and explore_process_list ?(split_par=false) prev_plist plist f_cont f_next = match plist with
      | [] -> f_next ()
      | p::q ->
          explore_process p (fun transition p_1 f_next_1 -> match p_1 with
            | Labelled_process.PNil -> f_cont transition (List.rev_append prev_plist q) f_next_1
            | Labelled_process.PPar plist' when split_par -> f_cont transition (List.rev_append prev_plist (plist'@q)) f_next_1
            | _ -> f_cont transition (List.rev_append prev_plist (p_1::q)) f_next_1
          ) (fun () ->
            if only_forall && !already_assigned_forall
            then f_next ()
            else explore_process_list ~split_par:split_par (p::prev_plist) q f_cont f_next
          )
    in

    let rec explore_output_processes prev_out_plist out_plist in_priv_plist f_cont f_next = match out_plist with
      | [] -> f_next ()
      | p::q ->
          explore_process p (fun transition p_1 f_next_1 -> match p_1 with
            | Labelled_process.PPar plist' ->
                let (out_p,in_p) =
                  List.fold_right (fun p' (acc_out,acc_in) ->
                    if Labelled_process.exists_toplevel_public_output p'
                    then (p'::acc_out,acc_in)
                    else (acc_out,p'::acc_in)
                  ) plist' (q,in_priv_plist)
                in
                f_cont transition (List.rev_append prev_out_plist out_p) in_p f_next_1
            | Labelled_process.PNil -> f_cont transition (List.rev_append prev_out_plist q) in_priv_plist f_next_1
            | _ ->
                if transition.out_gathering_skeleton.Labelled_process.output_skel = [] && not (Labelled_process.exists_toplevel_public_output p_1)
                then f_cont transition (List.rev_append prev_out_plist q) (p_1::in_priv_plist) f_next_1
                else f_cont transition (List.rev_append prev_out_plist (p_1::q)) in_priv_plist f_next_1
          ) (fun () ->
            if only_forall && !already_assigned_forall
            then f_next ()
            else explore_output_processes (p::prev_out_plist) q in_priv_plist f_cont f_next
          )
    in

    explore_output_processes [] conf.output_proc conf.input_and_private_proc (fun transition out_proc in_priv_proc f_next_1 ->
      let private_channels = update_private_channels_from_output_transition conf transition in
      let conf' =
        { conf with
          input_and_private_proc = in_priv_proc;
          output_proc = out_proc;
          private_channels = private_channels
        }
      in
      f_continuation transition conf';
      f_next_1 ()
    ) (fun () -> ())

  let next_public_output = main_next_public_output Labelled_process.Proper

  let next_public_output_improper_phase = main_next_public_output Labelled_process.ImproperNegPhase

  (*** Input and private communication transition ***)

  type input_data =
    {
      in_data_label : Label.t;
      in_data_channel : Channel.t;
      in_data_var : variable;
      in_data_position : position;
      in_data_process : Labelled_process.t;
      in_data_matching_status : matching_status
    }

  type output_data =
    {
      out_data_label : Label.t;
      out_data_term : term;
      out_data_position : position;
      out_data_process : Labelled_process.t;
      out_data_matching_status : matching_status
    }

  type channel_priority =
    | ChNone (* Must do input and private channel *)
    | ChOnlyPrivate (* Must do only the private channel. Typically only used with an Exists matching status *)
    | ChPriority of Channel.t * bool
        (* With [ChPriority(ch,b)], we must do [ch] in priority for the ForAll. Moreover, if [b = true] then
           we only do the private channels for Exists else we do everything for Exists.
           Cannot be used with matching statys = Exists *)

  let next_input matching_status is_applicable proc f_continuation (f_next:unit -> unit) =
    let only_forall = matching_status = ForAll in

    let rec explore_process m_status proc f_cont f_next = match proc with
      | Labelled_process.PNil
      | Labelled_process.POutput _ -> f_next ()
      | Labelled_process.PInput(ch,x,p,Some label,pos,_,_) ->
          begin match is_applicable m_status ch label with
            | None -> f_next ()
            | Some m_status' ->
                let input_data =
                  { in_data_label = label;
                    in_data_channel = ch;
                    in_data_var = x;
                    in_data_position = pos;
                    in_data_process = p;
                    in_data_matching_status = m_status'
                  }
                in
                f_continuation input_data Labelled_process.PNil f_next
          end
      | Labelled_process.PPar plist ->
          explore_process_list m_status [] plist (fun input_data rest_plist f_next_1 -> match rest_plist with
            | [] -> f_continuation input_data Labelled_process.PNil f_next_1
            | [p] -> f_continuation input_data p f_next_1
            | _ -> f_continuation input_data (Labelled_process.PPar rest_plist) f_next_1
          ) f_next
      | Labelled_process.PBangStrong([],[p])
      | Labelled_process.PBangPartial [p] -> explore_process m_status p f_cont f_next
      | Labelled_process.PBangStrong([],[p1;p2]) ->
          explore_process m_status p1 (fun input_data p' f_next_1 -> match p' with
            | Labelled_process.PNil -> f_cont input_data p2 f_next_1
            | Labelled_process.PPar plist' -> f_cont input_data (Labelled_process.PPar(p2::plist')) f_next_1
            | _ -> f_cont input_data (Labelled_process.PPar [p';p2]) f_next_1
          ) f_next
      | Labelled_process.PBangStrong([],p::plist) ->
          explore_process m_status p (fun input_data p' f_next_1 -> match p' with
            | Labelled_process.PNil -> f_cont input_data (Labelled_process.PBangStrong([],plist)) f_next_1
            | Labelled_process.PPar plist' -> f_cont input_data (Labelled_process.PPar(Labelled_process.PBangStrong([],plist)::plist')) f_next_1
            | _ -> f_cont input_data (Labelled_process.PPar [p';Labelled_process.PBangStrong([],plist)]) f_next_1
          ) f_next
      | Labelled_process.PBangPartial [p1;p2] ->
          explore_process m_status p1 (fun input_data p1' f_next_1 -> match p1' with
            | Labelled_process.PNil -> f_cont input_data p2 f_next_1
            | Labelled_process.PPar plist1' -> f_cont input_data (Labelled_process.PPar(p2::plist1')) f_next_1
            | _ -> f_cont input_data (Labelled_process.PPar [p1;p2]) f_next_1
          ) (fun () ->
            explore_process Exists p2 (fun input_data p2' f_next_1 -> match p2' with
              | Labelled_process.PNil -> f_cont input_data p1 f_next_1
              | Labelled_process.PPar plist_2' -> f_cont input_data (Labelled_process.PPar(p1::plist_2')) f_next_1
              | _ -> f_cont input_data (Labelled_process.PPar[p2';p1]) f_next_1
            ) f_next
          )
      | Labelled_process.PBangPartial (p::plist) ->
          explore_process m_status p (fun input_data p' f_next_1 -> match p' with
            | Labelled_process.PNil -> f_cont input_data (Labelled_process.PBangPartial plist) f_next_1
            | Labelled_process.PPar plist' -> f_cont input_data (Labelled_process.PPar((Labelled_process.PBangPartial plist)::plist')) f_next_1
            | _ -> f_cont input_data (Labelled_process.PPar [p';Labelled_process.PBangPartial plist]) f_next_1
          ) (fun () ->
            if only_forall
            then f_next ()
            else explore_bang_partial [p] plist f_cont f_next
          )
      | _ -> Config.internal_error "[session_process.ml >> Configuration.next_input] Unexpected process."

    and explore_bang_partial prev_plist plist f_cont f_next = match plist with
      | [] -> f_next ()
      | p::q ->
          explore_process Exists p (fun input_data p' f_next_1 ->
            let bang_partial = Labelled_process.PBangPartial (List.rev_append prev_plist q) in
            match p' with
              | Labelled_process.PNil -> f_cont input_data bang_partial f_next_1
              | Labelled_process.PPar plist' -> f_cont input_data (Labelled_process.PPar (bang_partial::plist')) f_next_1
              | _ -> f_cont input_data (Labelled_process.PPar [p';bang_partial]) f_next_1
          ) (fun () -> explore_bang_partial (p::prev_plist) q f_cont f_next)

    and explore_process_list m_status prev_plist plist f_cont f_next = match plist with
      | [] -> f_next ()
      | p::q ->
          explore_process m_status p (fun input_data p' f_next_1 -> match p' with
            | Labelled_process.PNil -> f_cont input_data (List.rev_append prev_plist q) f_next_1
            | Labelled_process.PPar plist' -> f_cont input_data (List.rev_append prev_plist (plist'@q)) f_next_1
            | _ -> f_cont input_data (List.rev_append prev_plist (p'::q)) f_next_1
          ) (fun () -> explore_process_list m_status (p::prev_plist) q f_cont f_next)
    in

    explore_process matching_status proc f_continuation f_next

  let next_output matching_status is_applicable target_channel proc f_continuation f_next =
    let only_forall = matching_status = ForAll in

    let rec explore_process m_status proc f_cont f_next = match proc with
      | Labelled_process.PNil
      | Labelled_process.PInput _ -> f_next ()
      | Labelled_process.POutput(ch,t,p,Some label,pos,_,_) ->
          if Channel.is_equal ch target_channel && is_applicable label
          then
            let output_data =
              { out_data_label = label;
                out_data_term = t;
                out_data_position = pos;
                out_data_process = p;
                out_data_matching_status = m_status
              }
            in
            f_continuation output_data Labelled_process.PNil f_next
          else f_next ()
      | Labelled_process.PPar plist ->
          explore_process_list m_status [] plist (fun output_data rest_plist f_next_1 -> match rest_plist with
            | [] -> f_continuation output_data Labelled_process.PNil f_next_1
            | [p] -> f_continuation output_data p f_next_1
            | _ -> f_continuation output_data (Labelled_process.PPar rest_plist) f_next_1
          ) f_next
      | Labelled_process.PBangStrong([],[p])
      | Labelled_process.PBangPartial [p] -> explore_process m_status p f_cont f_next
      | Labelled_process.PBangStrong([],[p1;p2]) ->
          explore_process m_status p1 (fun output_data p' f_next_1 -> match p' with
            | Labelled_process.PNil -> f_cont output_data p2 f_next_1
            | Labelled_process.PPar plist' -> f_cont output_data (Labelled_process.PPar(p2::plist')) f_next_1
            | _ -> f_cont output_data (Labelled_process.PPar [p';p2]) f_next_1
          ) f_next
      | Labelled_process.PBangStrong([],p::plist) ->
          explore_process m_status p (fun output_data p' f_next_1 -> match p' with
            | Labelled_process.PNil -> f_cont output_data (Labelled_process.PBangStrong([],plist)) f_next_1
            | Labelled_process.PPar plist' -> f_cont output_data (Labelled_process.PPar(Labelled_process.PBangStrong([],plist)::plist')) f_next_1
            | _ -> f_cont output_data (Labelled_process.PPar [p';Labelled_process.PBangStrong([],plist)]) f_next_1
          ) f_next
      | Labelled_process.PBangPartial [p1;p2] ->
          explore_process m_status p1 (fun output_data p1' f_next_1 -> match p1' with
            | Labelled_process.PNil -> f_cont output_data p2 f_next_1
            | Labelled_process.PPar plist1' -> f_cont output_data (Labelled_process.PPar(p2::plist1')) f_next_1
            | _ -> f_cont output_data (Labelled_process.PPar [p1;p2]) f_next_1
          ) (fun () ->
            explore_process Exists p2 (fun output_data p2' f_next_1 -> match p2' with
              | Labelled_process.PNil -> f_cont output_data p1 f_next_1
              | Labelled_process.PPar plist_2' -> f_cont output_data (Labelled_process.PPar(p1::plist_2')) f_next_1
              | _ -> f_cont output_data (Labelled_process.PPar[p2';p1]) f_next_1
            ) f_next
          )
      | Labelled_process.PBangPartial (p::plist) ->
          explore_process m_status p (fun output_data p' f_next_1 -> match p' with
            | Labelled_process.PNil -> f_cont output_data (Labelled_process.PBangPartial plist) f_next_1
            | Labelled_process.PPar plist' -> f_cont output_data (Labelled_process.PPar((Labelled_process.PBangPartial plist)::plist')) f_next_1
            | _ -> f_cont output_data (Labelled_process.PPar [p';Labelled_process.PBangPartial plist]) f_next_1
          ) (fun () ->
            if only_forall
            then f_next ()
            else explore_bang_partial [p] plist f_cont f_next
          )
      | _ -> Config.internal_error "[session_process.ml >> Configuration.next_input] Unexpected process."

    and explore_bang_partial prev_plist plist f_cont f_next = match plist with
      | [] -> f_next ()
      | p::q ->
          explore_process Exists p (fun output_data p' f_next_1 ->
            let bang_partial = Labelled_process.PBangPartial (List.rev_append prev_plist q) in
            match p' with
              | Labelled_process.PNil -> f_cont output_data bang_partial f_next_1
              | Labelled_process.PPar plist' -> f_cont output_data (Labelled_process.PPar (bang_partial::plist')) f_next_1
              | _ -> f_cont output_data (Labelled_process.PPar [p';bang_partial]) f_next_1
          ) (fun () -> explore_bang_partial (p::prev_plist) q f_cont f_next)

    and explore_process_list m_status prev_plist plist f_cont f_next = match plist with
      | [] -> f_next ()
      | p::q ->
          explore_process m_status p (fun output_data p' f_next_1 -> match p' with
            | Labelled_process.PNil -> f_cont output_data (List.rev_append prev_plist q) f_next_1
            | Labelled_process.PPar plist' -> f_cont output_data (List.rev_append prev_plist (plist'@q)) f_next_1
            | _ -> f_cont output_data (List.rev_append prev_plist (p'::q)) f_next_1
          ) (fun () -> explore_process_list m_status (p::prev_plist) q f_cont f_next)
    in

    explore_process matching_status proc f_continuation f_next

  type input_transition =
    {
      in_complete_label : Label.complete;
      in_channel : recipe;
      in_term : term;
      in_position : position;
      in_skeletons : Labelled_process.gathering_skeletons
    }

  type comm_transition =
    {
      comm_complete_label : Label.complete;
      comm_in_position : position;
      comm_out_position : position;
      comm_in_label : Label.t;
      comm_out_label : Label.t;
      comm_in_skeletons : Labelled_process.gathering_skeletons;
      comm_out_skeletons : Labelled_process.gathering_skeletons
    }

  type type_transition =
    | TInput of input_transition
    | TComm of comm_transition

  type input_and_comm_transition =
    {
      in_comm_type : type_transition;
      in_comm_matching_status : matching_status;
      in_comm_gathering_normalise : Labelled_process.gathering_normalise
    }

  (* Channel priority *)

  let determine_channel_priority conf =

    let rec filter_private_names_list main_ch_list = function
      | [] -> main_ch_list
      | p::q ->
          let main_ch_list_1 = filter_private_name main_ch_list p in
          if main_ch_list_1 = []
          then []
          else filter_private_names_list main_ch_list_1 q

    and filter_private_name main_ch_list = function
      | Labelled_process.PInput(_,_,_,_,_,_,ch_list)
      | Labelled_process.POutput(_,_,_,_,_,_,ch_list) -> NameList.diff main_ch_list ch_list
      | Labelled_process.PBangStrong([],p::_) -> filter_private_name main_ch_list p
      | Labelled_process.PBangPartial plist
      | Labelled_process.PPar plist -> filter_private_names_list main_ch_list plist
      | _ -> Config.internal_error "[session_process.ml >> determine_channel_priority] Unexpected case."
    in

    let rec explore_private_channels = function
      | [] -> None
      | ((Channel.CPrivate(_,true)) as ch,i,j)::_ when i >= 1 && j >= 1 -> Some ch
      | (Channel.CPrivate(_,true),_,_)::q -> explore_private_channels q
      | ch_list ->
          let channel_names =
            List.map (fun (ch,_,_) -> match ch with
              | Channel.CPrivate(n,false) -> n
              | _ -> Config.internal_error "[session_process.ml >> determine_channel_priority] The rest of the list should only contain private name."
            ) ch_list
          in
          if channel_names = []
          then None
          else
            let channel_names' = filter_private_names_list channel_names conf.input_and_private_proc in
            if channel_names' = []
            then None
            else Some (Channel.CPrivate(List.hd channel_names',false))
    in

    explore_private_channels conf.private_channels

  (* Handling of processes *)

  let process_list_of_par = function
    | Labelled_process.PNil -> []
    | Labelled_process.PPar plist' -> plist'
    | p -> [p]

  let make_par_processes plist = function
    | Labelled_process.PNil -> plist
    | Labelled_process.PPar plist' -> plist' @ plist
    | p -> p::plist

  let rec make_par_processes_list plist = function
    | [] -> []
    | p :: q -> make_par_processes_list (make_par_processes plist p) q

  (* Updating private channels and output_channel collector *)

  let update_private_channels_from_in_comm_transition conf trans = match trans.in_comm_type with
    | TInput in_trans ->
        merge_private_channels conf.private_channels in_trans.in_skeletons.Labelled_process.private_channels
    | TComm comm_trans ->
        let ch = match comm_trans.comm_complete_label with
          | Label.LComm(_,_,n,_) -> Channel.CPrivate(n,false) (* The false value does not matter as we only use this for equality *)
          | _ -> Config.internal_error "[session_process.ml >> Configuration.update_private_channels_from_in_comm_transition] We should have found a private channel."
        in
        let priv_ch_list = remove_ch_from_private_channels ch conf.private_channels in
        let sub_priv_ch_list = merge_private_channels comm_trans.comm_in_skeletons.Labelled_process.private_channels comm_trans.comm_out_skeletons.Labelled_process.private_channels in
        merge_private_channels priv_ch_list sub_priv_ch_list

  let rec generate_in_out_list in_plist out_plist skel_list plist = match skel_list, plist with
    | [],[] -> in_plist, out_plist
    | skel::q_skel, p::q ->
        if skel.Labelled_process.output_skel = []
        then generate_in_out_list (make_par_processes in_plist p) out_plist q_skel q
        else
          begin match p with
            | Labelled_process.PPar plist' ->
                let (in_plist_1,out_plist_1) =
                  List.fold_left (fun (acc_in,acc_out) p' ->
                    if Labelled_process.exists_toplevel_public_output p'
                    then (acc_in,p'::acc_out)
                    else (p'::acc_in,acc_out)
                  ) (in_plist,out_plist) plist'
                in
                generate_in_out_list in_plist_1 out_plist_1 q_skel q
            | _ -> generate_in_out_list in_plist (p::out_plist) q_skel q
          end
    | _ -> Config.internal_error "[session_process.ml >> Configuration.generate_in_out_list] The skeleton and process lists should be of same size."

  let main_next_input_and_private_comm proper_status channel_priority matching_status original_subst original_names conf (f_continuation:input_and_comm_transition -> t -> unit) =

    let is_input_applicable = match matching_status with
      | ForAll ->
          begin match channel_priority with
            | ChNone ->
                begin match proper_status, conf.blocks.Block.local_improper_blocks with
                  | Labelled_process.Proper, _
                  | _, [] -> fun _ _ _ -> Some ForAll
                  | _, Label.LComm(lbl,_,_,_) :: _
                  | _, Label.LStd lbl :: _ -> (fun _ _ lbl' -> if Label.independent lbl' lbl > 0 then Some ForAll else None)
                end
            | ChPriority(target_ch,_) ->
                fun _ ch _ ->
                  if Channel.is_equal ch target_ch
                  then Some ForAll
                  else None
            | _ -> Config.internal_error "[session_process.ml >> Configuration.next_input] ChOnlyPrivate should only be applied with an initial matching_status = Exists."
          end
      | Exists ->
          begin match channel_priority with
            | ChNone ->
                begin match proper_status, conf.blocks.Block.local_improper_blocks with
                  | Labelled_process.Proper, _
                  | _, [] -> fun _ _ _ -> Some Exists
                  | _, Label.LComm(lbl,_,_,_) :: _
                  | _, Label.LStd lbl :: _ -> (fun _ _ lbl' -> if Label.independent lbl' lbl > 0 then Some Exists else None)
                end
            | ChOnlyPrivate -> fun _ ch _ -> if Channel.is_public ch then None else Some Exists
            | _ -> Config.internal_error "[session_process.ml >> Configuration.next_input] ChPriority should not be applied with an initial matching_status = Exists."
          end
      | Both ->
          begin match channel_priority with
            | ChNone ->
                begin match proper_status, conf.blocks.Block.local_improper_blocks with
                  | Labelled_process.Proper, _
                  | _, [] -> fun m_status _ _ -> Some m_status
                  | _, Label.LComm(lbl,_,_,_) :: _
                  | _, Label.LStd lbl :: _ -> (fun m_status _ lbl' -> if Label.independent lbl' lbl > 0 then Some m_status else None)
                end
            | ChPriority(target_ch,false) ->
                fun m_status ch _ -> if Channel.is_equal target_ch ch then Some m_status else Some Exists
            | ChPriority(Channel.CPrivate(n_target_ch,_),true) ->
                begin fun m_status ch _ -> match ch with
                  | Channel.CPublic _ -> None
                  | Channel.CPrivate(n,_) -> if n == n_target_ch then Some m_status else Some Exists
                end
            | ChPriority _ -> Config.internal_error "[session_process.ml >> Configuration.next_input] A private channel is expected in ChPriority."
            | _ -> Config.internal_error "[session_process.ml >> Configuration.next_input] ChOnlyPrivate should only be applied with an initial matching_status = Exists."
          end
    in

    let is_output_applicable = match proper_status, conf.blocks.Block.local_improper_blocks with
      | Labelled_process.Proper, _
      | _, [] -> (fun _ -> true)
      | _, Label.LComm(lbl,_,_,_)::_
      | _, Label.LStd lbl :: _ -> (fun lbl' -> Label.independent lbl' lbl > 0)
    in

    let rec explore_input_processes prev_in_plist in_plist f_cont f_next = match in_plist with
      | [] -> f_next ()
      | p::q ->
          next_input matching_status is_input_applicable p (fun in_data p_rest f_next_1 ->
            if Channel.is_public in_data.in_data_channel
            then
              Variable.auto_cleanup_with_reset (fun f_next_2 ->
                (* Corresponds to an input transition on a public channel. We thus need to normalise. *)
                let x_fresh = Var (Variable.fresh Existential) in
                Variable.link_term in_data.in_data_var x_fresh;
                let gather_norm =
                  {
                    Labelled_process.original_subst = (in_data.in_data_var,x_fresh) :: original_subst;
                    Labelled_process.original_names = original_names;
                    Labelled_process.disequations = Formula.T.Top
                  }
                in
                Labelled_process.normalise proper_status in_data.in_data_label gather_norm in_data.in_data_process (fun gather_norm_1 gather_skel_1 p_in f_next_3 ->
                  let type_transition = TInput
                    {
                      in_complete_label = Label.LStd in_data.in_data_label;
                      in_term = x_fresh;
                      in_position = in_data.in_data_position;
                      in_skeletons = gather_skel_1
                    }
                  in
                  let transition =
                    {
                      in_comm_type = type_transition;
                      in_comm_matching_status = in_data.in_data_matching_status;
                      in_comm_gathering_normalise = gather_norm_1
                    }
                  in
                  match p_in with
                    | Labelled_process.PInput(ch,_,_,_,_,_,_) when Channel.is_public ch -> (* We focus the process *)
                        f_cont transition (make_par_processes (List.rev_append prev_in_plist q) p_rest) [] (Some p_in) f_next_3
                    | _ -> (* We release the process *)
                      let (in_plist_1,out_plist_1) = generate_in_out_list (make_par_processes (List.rev_append prev_in_plist q) p_rest) [] [gather_skel_1] [p_in] in
                      f_cont transition in_plist_1 out_plist_1 None f_next_3
                ) f_next_2
              ) f_next_1
            else
              (* Corresponds to an private communication. Thus we need to search for an ouput *)
              let proc_for_output = Labelled_process.PPar (make_par_processes (List.rev_append prev_in_plist q) p_rest) in
              next_output in_data.in_data_matching_status is_output_applicable in_data.in_data_channel proc_for_output (fun out_data p_rest_out f_next_2 ->
                let n = match in_data.in_data_channel with
                  | Channel.CPrivate(n,_) -> n
                  | _ -> Config.internal_error "[session_process.ml >> next_input_and_private_comm] Should be a private channel."
                in

                let complete_label = match out_data.out_data_matching_status, channel_priority with
                  | (ForAll | Both), ChPriority _ -> Label.create_complete_comm in_data.in_data_label out_data.out_data_label n true
                  | _ -> Label.create_complete_comm in_data.in_data_label out_data.out_data_label n false
                in

                Variable.auto_cleanup_with_reset (fun f_next_3 ->
                  Variable.link_term in_data.in_data_var out_data.out_data_term;
                  let gather_norm =
                    {
                      Labelled_process.original_subst = (in_data.in_data_var,out_data.out_data_term) :: original_subst;
                      Labelled_process.original_names = original_names;
                      Labelled_process.disequations = Formula.T.Top
                    }
                  in
                  Labelled_process.normalise proper_status in_data.in_data_label gather_norm in_data.in_data_process (fun gather_norm_1 in_gather_skel p_in f_next_4 ->
                    Labelled_process.normalise proper_status out_data.out_data_label gather_norm_1 out_data.out_data_process (fun gather_norm_2 out_gather_skel p_out f_next_5 ->
                      let type_transition = TComm
                        {
                          comm_complete_label = complete_label;
                          comm_in_position = in_data.in_data_position;
                          comm_out_position = out_data.out_data_position;
                          comm_in_label = in_data.in_data_label;
                          comm_out_label = out_data.out_data_label;
                          comm_in_skeletons = in_gather_skel;
                          comm_out_skeletons = out_gather_skel
                        }
                      in
                      let transition =
                        {
                          in_comm_type = type_transition;
                          in_comm_matching_status = out_data.out_data_matching_status;
                          in_comm_gathering_normalise = gather_norm_2
                        }
                      in
                      let (in_plist_1,out_plist_1) = generate_in_out_list (process_list_of_par p_rest_out) [] [in_gather_skel;out_gather_skel] [p_in;p_out] in
                      f_cont transition in_plist_1 out_plist_1 None f_next_5
                    ) f_next_4
                  ) f_next_3
                ) f_next_2
              ) f_next_1
          ) (fun () -> explore_input_processes (p::prev_in_plist) q f_cont f_next)
    in

    explore_input_processes [] conf.input_and_private_proc (fun transition in_plist out_plist focus f_next_1 ->
      let private_channels = update_private_channels_from_in_comm_transition conf transition in
      let conf' =
        { conf with
          input_and_private_proc = in_plist;
          output_proc = out_plist;
          focused_proc = focus;
          private_channels = private_channels
        }
      in
      f_continuation transition conf';
      f_next_1 ()
    ) (fun () -> ())

  let next_input_and_private_comm = main_next_input_and_private_comm Labelled_process.Proper

  let next_input_and_private_comm_improper_phase = main_next_input_and_private_comm Labelled_process.ImproperPosFocusPhase ChNone

  let main_next_pos_input proper_status matching_status original_subst original_names conf f_continuation = match conf.focused_proc with
    | Some Labelled_process.PInput(_,x,p,Some label,pos,_,_) ->
        Variable.auto_cleanup_with_reset (fun f_next_1 ->
          (* Corresponds to an input transition on a public channel. We thus need to normalise. *)
          let x_fresh = Var (Variable.fresh Existential) in
          Variable.link_term x x_fresh;
          let gather_norm =
            {
              Labelled_process.original_subst = (x,x_fresh) :: original_subst;
              Labelled_process.original_names = original_names;
              Labelled_process.disequations = Formula.T.Top
            }
          in
          Labelled_process.normalise proper_status label gather_norm p (fun gather_norm_1 gather_skel_1 p_in f_next_2 ->
            let type_transition = TInput
              {
                in_complete_label = Label.LStd label;
                in_term = x_fresh;
                in_position = pos;
                in_skeletons = gather_skel_1
              }
            in
            let transition =
              {
                in_comm_type = type_transition;
                in_comm_matching_status = matching_status;
                in_comm_gathering_normalise = gather_norm_1
              }
            in
            match p_in with
              | Labelled_process.PInput(ch,_,_,_,_,_,_) when Channel.is_public ch -> (* We keep the process focused *)
                  f_continuation transition { conf with focused_proc = Some p_in } f_next_2
              | _ -> (* We release the process *)
                  let (in_plist,out_plist) = generate_in_out_list conf.input_and_private_proc [] [gather_skel_1] [p_in] in
                  let private_channels = update_private_channels_from_in_comm_transition conf transition in
                  let conf' =
                    { conf with
                      input_and_private_proc = in_plist;
                      output_proc = out_plist;
                      focused_proc = None;
                      private_channels = private_channels
                    }
                  in
                  f_continuation transition conf' f_next_2
          ) f_next_1
        ) (fun () -> ())
    | _ -> Config.internal_error "[session_process.ml >> Configuration.next_focused_input] The configuration should be focused with a labeled public input."

  let next_pos_input = main_next_pos_input Labelled_process.Proper

  let next_pos_input_improper_phase = main_next_pos_input Labelled_process.ImproperPosFocusPhase
end
