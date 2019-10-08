open Term
open Display
open Extensions

(************************
***       SDF      ***
*************************)

type id_recipe_equivalent = int

let accumulator_id_recipe_equivalent = ref 0

let fresh_id_recipe_equivalent () =
  accumulator_id_recipe_equivalent := !accumulator_id_recipe_equivalent + 1;
  !accumulator_id_recipe_equivalent

module Int_Comp =
struct
  type t = int
  let compare = compare
end

module IntMap = Map.Make(Int_Comp)

module IK = struct

  type t =
    {
      all_id : int list;
      counter_id : int;
      map : Fact.deduction IntMap.t
    }

  (******* Access ********)

  let last_entry ik =
    let (_,fact) = IntMap.max_binding ik.map in
    fact

  let last_entry_with_id ik = IntMap.max_binding ik.map

  let last_entry_id ik = ik.counter_id

  let all_id ik = ik.all_id

  let get ik id = IntMap.find id ik.map

  (******* Iterator ********)

  let iter ik f = IntMap.iter (fun _ fact -> f fact) ik.map

  let tail_iter ik f f_next = IntMap.tail_iter f ik.map f_next

  let fold_right f acc ik = IntMap.fold_right f acc ik.map

  (******* Modification ********)

  let apply ik subst_snd subst_fst =
    if Subst.is_identity subst_snd
    then
      if Subst.is_identity subst_fst
      then ik
      else { ik with map = Subst.apply subst_fst ik.map (fun m f -> IntMap.map (Fact.apply_fst_function_on_deduction_fact f) m) }
    else
      if Subst.is_identity subst_fst
      then { ik with map = Subst.apply subst_snd ik.map (fun m f -> IntMap.map (Fact.apply_snd_function_on_deduction_fact f) m) }
      else { ik with map = Subst.apply_both subst_fst subst_snd ik.map (fun m f_fst f_snd -> IntMap.map (Fact.apply_both_functions_on_deduction_fact f_fst f_snd) m) }

  let apply_recipe ik subst_snd =
    if Subst.is_identity subst_snd
    then ik
    else { ik with map = Subst.apply subst_snd ik.map (fun m f -> IntMap.map (Fact.apply_snd_function_on_deduction_fact f) m) }

  let apply_protocol ik subst_fst =
    if Subst.is_identity subst_fst
    then ik
    else { ik with map = Subst.apply subst_fst ik.map (fun m f -> IntMap.map (Fact.apply_fst_function_on_deduction_fact f) m) }

  (******* Basic operations *********)

  let empty = { all_id = [];  counter_id = 0; map = IntMap.empty }

  let add ik fact =
    let counter' = ik.counter_id + 1 in
    {
      all_id = counter' :: ik.all_id;
      counter_id = counter';
      map = IntMap.add counter' fact ik.map
    }

  let remove_last ik =
    let t = List.hd ik.all_id in
    let rest = List.tl ik.all_id in
    if rest = []
    then empty
    else
      { ik with
        all_id = rest;
        map = IntMap.remove t ik.map
      }

  let rec remove_in_list (i:int) = function
    | [] -> Config.internal_error "[data_structure.ml >> IK.remove_in_list] The id should be in the list"
    | t::q when i = t -> q
    | t::q -> t::(remove_in_list i q)

  let remove n ik =
    let rest = remove_in_list n ik.all_id in
    if rest = []
    then empty
    else
      { ik with
        all_id = rest;
        map = IntMap.remove n ik.map
      }

  (******* Testing *********)

  let find_recipe ik r =
    let fact = IntMap.search (fun fact -> is_equal Recipe (Fact.get_recipe fact) r) ik.map in
    Fact.get_protocol_term fact

  let find_protocol_opt ik t =
    match IntMap.search_opt (fun fact -> is_equal Protocol (Fact.get_protocol_term fact) t) ik.map with
      | None -> None
      | Some fact -> Some (Fact.get_recipe fact)

  let find_unifier_with_recipe ik t f_continuation (f_next:unit -> unit) =
    IntMap.tail_iter (fun fact f_next_1 ->
      let t' = Fact.get_protocol_term fact in

      let result_unification =
        try
          Some (Subst.unify_protocol [t,t'])
        with Subst.Not_unifiable -> None
      in

      match result_unification with
        | None -> f_next_1 ()
        | Some subst -> f_continuation (Fact.get_recipe fact) subst f_next_1
    ) ik.map f_next

  let display _ ?(rho = None) ?(per_line = 8) ik =
    let size = IntMap.cardinal ik.map in
    if IntMap.is_empty ik.map
    then emptyset Latex
    else
      begin
        let str = ref "\\left\\{ \\begin{array}{l} " in
        let current_number = ref 1 in
        IntMap.iter (fun _ fact ->
          if !current_number >= size
          then str := Printf.sprintf "%s%s \\end{array}\\right\\}" !str (Fact.display_deduction_fact Latex ~rho:rho fact)
          else if (!current_number / per_line)*per_line = !current_number
          then str := Printf.sprintf "%s%s,\\\\" !str (Fact.display_deduction_fact Latex ~rho:rho fact)
          else str := Printf.sprintf "%s%s, " !str (Fact.display_deduction_fact Latex ~rho:rho fact);

          incr current_number
        ) ik.map;
        !str
      end
end

module K = struct

  type cell =
    {
      var_type : int;
      fact : Fact.deduction;
      recipe_ground : bool;
      protocol_ground : bool
    }

  type cell_ground =
    {
      g_var_type : int;
      g_fact : Fact.deduction
    }

  type t =
    {
      max_var_type : int;
      all_id : int list;
      size : int;
      map : cell IntMap.t;
      map_ground : cell_ground IntMap.t
    }

  (******* Access ********)

  let cardinal sdf = sdf.size

  let all_id sdf = sdf.all_id

  let get sdf id =
    try
      let cell = IntMap.find id sdf.map_ground in
      cell.g_fact
    with
      | Not_found ->
        begin
          try
            let cell = IntMap.find id sdf.map in
            cell.fact
          with
          | Not_found -> Config.internal_error "[Data_structure.ml >> get] There is no deduction fact in SDF with this recipe equivalent id."
        end

  let iter_variables_and_terms (f_var:fst_ord_variable -> unit) (f_term:protocol_term -> unit) sdf =
    IntMap.iter (fun _ cell -> Fact.iter_variables_and_terms_deduction f_var f_term cell.fact) sdf.map;
    IntMap.iter (fun _ cell -> Fact.iter_variables_and_terms_deduction f_var f_term cell.g_fact) sdf.map_ground

  let map_variables_and_terms (f_var:fst_ord_variable -> fst_ord_variable) (f_term:protocol_term -> protocol_term) sdf =
    { sdf with
      map = IntMap.map (fun cell -> { cell with fact = Fact.map_variables_and_terms_deduction f_var f_term cell.fact }) sdf.map;
      map_ground = IntMap.map (fun cell -> { cell with g_fact = Fact.map_variables_and_terms_deduction f_var f_term cell.g_fact }) sdf.map_ground
    }

  (******* Iterators ********)

  exception Out_of_type

  let iter sdf f =
    IntMap.iter (fun _ cell -> f cell.g_fact) sdf.map_ground;
    IntMap.iter (fun _ cell -> f cell.fact) sdf.map

  let iter_terms2 f sdf1 sdf2 =
    let term_ground_list1 = ref [] in
    let term_list1 = ref [] in
    let term_ground_list2 = ref [] in
    let term_list2 = ref [] in
    IntMap.iter (fun i cell ->
      term_list1 := (i,Fact.get_protocol_term cell.fact) :: !term_list1;
    ) sdf1.map;
    IntMap.iter (fun i cell ->
      term_ground_list1 := (i,Fact.get_protocol_term cell.g_fact) :: !term_ground_list1;
    ) sdf1.map_ground;
    IntMap.iter (fun i cell ->
      term_list2 := (i,Fact.get_protocol_term cell.fact) :: !term_list2;
    ) sdf2.map;
    IntMap.iter (fun i cell ->
      term_ground_list2 := (i,Fact.get_protocol_term cell.g_fact) :: !term_ground_list2;
    ) sdf2.map_ground;

    let rec iter2 l1 lg1 l2 lg2 = match l1, lg1, l2, lg2 with
      | [],[],[],[] -> ()
      | (i1,t1)::q1,_,(i2,t2)::q2,_ when i1 = i2 ->
          f t1 t2;
          iter2 q1 lg1 q2 lg2
      | _, (i1,t1)::q1,(i2,t2)::q2,_ when i1 = i2 ->
          f t1 t2;
          iter2 l1 q1 q2 lg2
      | (i1,t1)::q1,_,_,(i2,t2)::q2 when i1 = i2 ->
          f t1 t2;
          iter2 q1 lg1 l2 q2
      | _,(i1,t1)::q1,_,(i2,t2)::q2 when i1 = i2 ->
          f t1 t2;
          iter2 l1 q1 l2 q2
      | _ -> Config.internal_error "[data_structure.ml >> K.iter2] The two set K should have the same indexes."
  in
  iter2 !term_list1 !term_ground_list1 !term_list2 !term_ground_list2

  let iter_within_var_type k sdf f =
    begin try
      IntMap.iter (fun _ cell ->
        if cell.g_var_type > k
        then raise Out_of_type
        else f cell.g_fact
        ) sdf.map_ground;
    with
    | Out_of_type -> ()
    end;
    try
      IntMap.iter (fun _ cell ->
        if cell.var_type > k
        then raise Out_of_type
        else f cell.fact
        ) sdf.map;
    with
    | Out_of_type -> ()

  let tail_iter_within_var_type k sdf f f_next =
    IntMap.tail_iter_until (fun cell f_next_1 -> f cell.g_fact f_next_1) (fun cell -> cell.g_var_type > k) sdf.map_ground
      (fun () -> IntMap.tail_iter_until (fun cell f_next_1 -> f cell.fact f_next_1) (fun cell -> cell.var_type > k) sdf.map f_next)

  let tail_iter sdf f f_next =
    IntMap.tail_iter (fun cell f_next_1 -> f cell.g_fact f_next_1) sdf.map_ground
      (fun () -> IntMap.tail_iter (fun cell f_next_1 -> f cell.fact f_next_1) sdf.map f_next)

  (* Application of a substitution *)

  let map_protocol_term (sdf:t) (f:protocol_term -> protocol_term) =
    let (map_ground, map) =
      IntMap.fold (fun i cell (acc_map_ground, acc_map) ->
        if cell.protocol_ground
        then (acc_map_ground, IntMap.add i cell acc_map)
        else
          let t = f (Fact.get_protocol_term cell.fact) in
          if is_ground t
          then
            if cell.recipe_ground
            then (IntMap.add i { g_var_type = cell.var_type; g_fact = Fact.create_deduction_fact (Fact.get_recipe cell.fact) t } acc_map_ground, acc_map)
            else (acc_map_ground, IntMap.add i { cell with protocol_ground = true; fact = Fact.create_deduction_fact (Fact.get_recipe cell.fact) t } acc_map)
          else (acc_map_ground, IntMap.add i { cell with fact = Fact.create_deduction_fact (Fact.get_recipe cell.fact) t } acc_map)
      ) sdf.map (sdf.map_ground, IntMap.empty)
    in
    { sdf with map_ground = map_ground; map = map }

  let map_recipe (sdf:t) (f:recipe -> recipe) =
    let (map_ground, map) =
      IntMap.fold (fun i cell (acc_map_ground, acc_map) ->
        if cell.recipe_ground
        then (acc_map_ground, IntMap.add i cell acc_map)
        else
          let t = f (Fact.get_recipe cell.fact) in
          if is_ground t
          then
            if cell.protocol_ground
            then (IntMap.add i { g_var_type = cell.var_type; g_fact = Fact.create_deduction_fact t (Fact.get_protocol_term cell.fact) } acc_map_ground, acc_map)
            else (acc_map_ground, IntMap.add i { cell with recipe_ground = true; fact = Fact.create_deduction_fact  t (Fact.get_protocol_term cell.fact) } acc_map)
          else (acc_map_ground, IntMap.add i { cell with fact = Fact.create_deduction_fact t (Fact.get_protocol_term cell.fact) } acc_map)
      ) sdf.map (sdf.map_ground, IntMap.empty)
    in
    { sdf with map_ground = map_ground; map = map }

  let map_both (sdf:t) (f_fst:protocol_term -> protocol_term) (f_snd:recipe -> recipe) =
    let (map_ground, map) =
      IntMap.fold (fun i cell (acc_map_ground, acc_map) ->
        let r =
          if cell.recipe_ground
          then Fact.get_recipe cell.fact
          else f_snd (Fact.get_recipe cell.fact)
        in
        let t =
          if cell.protocol_ground
          then Fact.get_protocol_term cell.fact
          else f_fst (Fact.get_protocol_term cell.fact)
        in

        let g_r = is_ground r
        and g_t = is_ground t in

        if g_r && g_t
        then (IntMap.add i { g_var_type = cell.var_type; g_fact = Fact.create_deduction_fact r t } acc_map_ground, acc_map)
        else (acc_map_ground, IntMap.add i { cell with recipe_ground = g_r; protocol_ground = g_t; fact = Fact.create_deduction_fact r t } acc_map)
      ) sdf.map (sdf.map_ground, IntMap.empty)
    in
    { sdf with map_ground = map_ground; map = map }

  let apply sdf subst_snd subst_fst = Subst.apply_both subst_fst subst_snd sdf map_both

  let apply_protocol sdf subst_fst = Subst.apply subst_fst sdf map_protocol_term

  let apply_recipe sdf subst_snd = Subst.apply subst_snd sdf map_recipe

  let apply_recipe_and_gather (sdf:t) (subst_snd:(snd_ord,axiom) Subst.t) (array_recipe:recipe array) =
    let map_recipe (sdf:t)  (f:recipe -> recipe) =
      let (map_ground, map) =
        IntMap.fold (fun i cell (acc_map_ground, acc_map) ->
          if cell.recipe_ground
          then (acc_map_ground, IntMap.add i cell acc_map)
          else
            begin
              let t = f (Fact.get_recipe cell.fact) in
              array_recipe.(i-1) <- t;
              if is_ground t
              then
                if cell.protocol_ground
                then (IntMap.add i { g_var_type = cell.var_type; g_fact = Fact.create_deduction_fact t (Fact.get_protocol_term cell.fact) } acc_map_ground, acc_map)
                else (acc_map_ground, IntMap.add i { cell with recipe_ground = true; fact = Fact.create_deduction_fact  t (Fact.get_protocol_term cell.fact) } acc_map)
              else (acc_map_ground, IntMap.add i { cell with fact = Fact.create_deduction_fact t (Fact.get_protocol_term cell.fact) } acc_map)
            end
        ) sdf.map (sdf.map_ground, IntMap.empty)
      in
      { sdf with map_ground = map_ground; map = map }
    in

    Subst.apply subst_snd sdf map_recipe

  let apply_recipe_from_gathering (sdf:t) (array_recipe:recipe array) =
    let (map_ground, map) =
      IntMap.fold (fun i cell (acc_map_ground, acc_map) ->
        if cell.recipe_ground
        then (acc_map_ground, IntMap.add i cell acc_map)
        else
          begin
            let t = array_recipe.(i-1) in
            if is_ground t
            then
              if cell.protocol_ground
              then (IntMap.add i { g_var_type = cell.var_type; g_fact = Fact.create_deduction_fact t (Fact.get_protocol_term cell.fact) } acc_map_ground, acc_map)
              else (acc_map_ground, IntMap.add i { cell with recipe_ground = true; fact = Fact.create_deduction_fact  t (Fact.get_protocol_term cell.fact) } acc_map)
            else (acc_map_ground, IntMap.add i { cell with fact = Fact.create_deduction_fact t (Fact.get_protocol_term cell.fact) } acc_map)
          end
      ) sdf.map (sdf.map_ground, IntMap.empty)
    in
    { sdf with map_ground = map_ground; map = map }

  (******* Testing ********)

  let mem_fst_ord_variable v k =
    IntMap.exists (fun _ cell ->
      var_occurs v (Fact.get_protocol_term cell.fact)
    ) k.map

  let find_protocol_opt k t = match IntMap.search_opt (fun cell -> is_equal Protocol (Fact.get_protocol_term cell.fact) t) k.map with
    | None ->
        begin match IntMap.search_opt (fun cell -> is_equal Protocol (Fact.get_protocol_term cell.g_fact) t) k.map_ground with
          | None -> None
          | Some cell -> Some (Fact.get_recipe cell.g_fact)
        end
    | Some cell -> Some (Fact.get_recipe cell.fact)

  let find_recipe k r = match IntMap.search_opt (fun cell -> is_equal Recipe (Fact.get_recipe cell.fact) r) k.map with
    | None ->
        let cell = IntMap.search (fun cell -> is_equal Recipe (Fact.get_recipe cell.g_fact) r) k.map_ground in
        Fact.get_protocol_term cell.g_fact
    | Some cell -> Fact.get_protocol_term cell.fact

  let find_recipe_opt k r = match IntMap.search_opt (fun cell -> is_equal Recipe (Fact.get_recipe cell.fact) r) k.map with
    | None ->
        begin match IntMap.search_opt (fun cell -> is_equal Recipe (Fact.get_recipe cell.g_fact) r) k.map_ground with
          | None -> None
          | Some cell -> Some (Fact.get_protocol_term cell.g_fact)
        end
    | Some cell -> Some (Fact.get_protocol_term cell.fact)

  let find_recipe_with_var_type k r = match IntMap.search_opt (fun cell -> is_equal Recipe (Fact.get_recipe cell.fact) r) k.map with
    | None ->
        let cell = IntMap.search (fun cell -> is_equal Recipe (Fact.get_recipe cell.g_fact) r) k.map_ground in
        Fact.get_protocol_term cell.g_fact, cell.g_var_type
    | Some cell -> Fact.get_protocol_term cell.fact, cell.var_type

  let find_recipe_with_var_type_opt k r = match IntMap.search_opt (fun cell -> is_equal Recipe (Fact.get_recipe cell.fact) r) k.map with
    | None ->
        begin match IntMap.search_opt (fun cell -> is_equal Recipe (Fact.get_recipe cell.g_fact) r) k.map_ground with
          | None -> None
          | Some cell -> Some (Fact.get_protocol_term cell.g_fact, cell.g_var_type)
        end
    | Some cell -> Some (Fact.get_protocol_term cell.fact, cell.var_type)

  let find_unifier k t i f_continuation f_next =
    Config.debug (fun () ->
      if i = max_int
      then Config.internal_error "[data_structure.ml >> find_unifier] The var type should not be unbounded."
    );

    if i = k.max_var_type
    then
      IntMap.tail_iter (fun cell f_next_1 ->
        match Subst.unify_protocol_opt [t,Fact.get_protocol_term cell.g_fact] with
          | None -> f_next_1 ()
          | Some subst -> f_continuation subst f_next_1
      ) k.map_ground (fun () ->
        IntMap.tail_iter (fun cell f_next_1 ->
          match Subst.unify_protocol_opt [t,Fact.get_protocol_term cell.fact] with
          | None -> f_next_1 ()
          | Some subst -> f_continuation subst f_next_1
        ) k.map f_next
      )
    else
      IntMap.tail_iter_until (fun cell f_next_1 ->
        match Subst.unify_protocol_opt [t,Fact.get_protocol_term cell.g_fact] with
          | None -> f_next_1 ()
          | Some subst -> f_continuation subst f_next_1
      ) (fun cell -> cell.g_var_type > i) k.map_ground (fun () ->
        IntMap.tail_iter_until (fun cell f_next_1 ->
          match Subst.unify_protocol_opt [t,Fact.get_protocol_term cell.fact] with
          | None -> f_next_1 ()
          | Some subst -> f_continuation subst f_next_1
        ) (fun cell -> cell.var_type > i) k.map f_next
      )

  let find_unifier_with_recipe k t i f_continuation f_next =
    if i = k.max_var_type || i = max_int
    then
      IntMap.tail_iter (fun cell f_next_1 ->
        match Subst.unify_protocol_opt [t,Fact.get_protocol_term cell.g_fact] with
          | None -> f_next_1 ()
          | Some subst -> f_continuation (Fact.get_recipe cell.g_fact) subst f_next_1
      ) k.map_ground (fun () ->
        IntMap.tail_iter (fun cell f_next_1 ->
          match Subst.unify_protocol_opt [t,Fact.get_protocol_term cell.fact] with
          | None -> f_next_1 ()
          | Some subst -> f_continuation (Fact.get_recipe cell.fact) subst f_next_1
        ) k.map f_next
      )
    else
      IntMap.tail_iter_until (fun cell f_next_1 ->
        match Subst.unify_protocol_opt [t,Fact.get_protocol_term cell.g_fact] with
          | None -> f_next_1 ()
          | Some subst -> f_continuation (Fact.get_recipe cell.g_fact) subst f_next_1
      ) (fun cell -> cell.g_var_type > i) k.map_ground (fun () ->
        IntMap.tail_iter_until (fun cell f_next_1 ->
          match Subst.unify_protocol_opt [t,Fact.get_protocol_term cell.fact] with
          | None -> f_next_1 ()
          | Some subst -> f_continuation (Fact.get_recipe cell.fact) subst f_next_1
        ) (fun cell -> cell.var_type > i) k.map f_next
      )

  (******* Basic operations *********)

  let empty = { max_var_type = 0; size = 0 ; map = IntMap.empty; all_id = []; map_ground = IntMap.empty }

  let add sdf var_type fct =
    Config.debug (fun () ->
      let recipe = Fact.get_recipe fct in
      let k = get_type recipe in
      if k <> var_type
      then Config.internal_error "[Data_structure.ml >> add] An element added to SDF should always have the same var type as the size of the frame.";

      let vars_snd = get_vars Recipe recipe in

      if List.exists (fun v -> k = Variable.type_of v) vars_snd
      then Config.internal_error "[data_structure.ml >> SDF.add] The added deduction fact have a second-order variable with the same type as the recipe itself";

      try
        let var_type =
          let (_,cell_max_g) = IntMap.max_binding sdf.map_ground in
          let (_,cell_max) = IntMap.max_binding sdf.map in
          max cell_max.var_type cell_max_g.g_var_type
        in
        if var_type > k
        then Config.internal_error "[data_structure.ml >> SDF.add] The added deduction fact have stricly smaller variable type than some deduction fact of SDF.";
      with
        | Not_found -> ()
    );
    let r = Fact.get_recipe fct
    and t = Fact.get_protocol_term fct in

    let recipe_ground = is_ground r
    and protocol_ground = is_ground t in
    let new_size = sdf.size + 1 in
    if recipe_ground && protocol_ground
    then
      { sdf with
        max_var_type = var_type;
        size = new_size;
        map_ground = IntMap.add new_size ({ g_var_type = var_type; g_fact = fct }) sdf.map_ground;
        all_id = new_size::sdf.all_id
      }
    else
      {
        sdf with
        max_var_type = var_type;
        size = new_size;
        map = IntMap.add new_size ({ var_type = var_type; fact = fct ; protocol_ground = protocol_ground; recipe_ground = recipe_ground }) sdf.map;
        all_id = new_size::sdf.all_id
      }

  let display out ?(rho = None) ?(per_line = 8) ?(tab = 0) sdf = match out with
    | Testing ->
        if sdf.size = 0
        then emptyset Testing
        else
          begin
            let current_number = ref 1 in
            let str = ref "{ " in
            IntMap.iter (fun _ cell ->
              if !current_number < sdf.size
              then str := Printf.sprintf "%s%s, " !str (Fact.display_deduction_fact Testing ~rho:rho cell.fact)
              else str := Printf.sprintf "%s%s }" !str (Fact.display_deduction_fact Testing ~rho:rho cell.fact);

              incr current_number
            ) sdf.map;
            IntMap.iter (fun _ cell ->
              if !current_number < sdf.size
              then str := Printf.sprintf "%s%s, " !str (Fact.display_deduction_fact Testing ~rho:rho cell.g_fact)
              else str := Printf.sprintf "%s%s }" !str (Fact.display_deduction_fact Testing ~rho:rho cell.g_fact);

              incr current_number
            ) sdf.map_ground;
            !str
          end
    | Latex ->
        if sdf.size = 0
        then emptyset Latex
        else
          begin
            let str = ref "" in
            IntMap.iter (fun _ cell ->
              str := Printf.sprintf "%s%s, " !str (Fact.display_deduction_fact Latex ~rho:rho cell.fact)
            ) sdf.map;
            IntMap.iter (fun _ cell ->
              str := Printf.sprintf "%s%s, " !str (Fact.display_deduction_fact Latex ~rho:rho cell.g_fact)
            ) sdf.map_ground;
            !str
          end
    | HTML ->
        if sdf.size = 0
        then emptyset HTML
        else
          begin
            let str = ref "<table class=\"sdf\"><tr><td>" in
            let current_number = ref 1 in
            IntMap.iter (fun _ cell ->
              if !current_number >= sdf.size
              then str := Printf.sprintf "%s%s</td></tr></table>" !str (Fact.display_deduction_fact HTML ~rho:rho cell.fact)
              else if (!current_number / per_line)*per_line = !current_number
              then str := Printf.sprintf "%s%s,</td></tr><tr><td>" !str (Fact.display_deduction_fact HTML ~rho:rho cell.fact)
              else str := Printf.sprintf "%s%s, " !str (Fact.display_deduction_fact HTML ~rho:rho cell.fact);

              incr current_number
            ) sdf.map;
            IntMap.iter (fun _ cell ->
              if !current_number >= sdf.size
              then str := Printf.sprintf "%s%s</td></tr></table>" !str (Fact.display_deduction_fact HTML ~rho:rho cell.g_fact)
              else if (!current_number / per_line)*per_line = !current_number
              then str := Printf.sprintf "%s%s,</td></tr><tr><td>" !str (Fact.display_deduction_fact HTML ~rho:rho cell.g_fact)
              else str := Printf.sprintf "%s%s, " !str (Fact.display_deduction_fact HTML ~rho:rho cell.g_fact);

              incr current_number
            ) sdf.map_ground;
            !str
          end
    | _ ->
        let tab_str = create_tab tab in
        begin match sdf.size with
          | 0 -> "{}"
          | s when s <= per_line ->
              let str = ref "{ " in
              let current_number = ref 1 in
              IntMap.iter (fun _ cell ->
                if !current_number < sdf.size
                then str := Printf.sprintf "%s%s; " !str (Fact.display_deduction_fact out ~rho:rho cell.fact)
                else str := Printf.sprintf "%s%s }" !str (Fact.display_deduction_fact out ~rho:rho cell.fact);

                incr current_number
              ) sdf.map;
              IntMap.iter (fun _ cell ->
                if !current_number < sdf.size
                then str := Printf.sprintf "%s%s; " !str (Fact.display_deduction_fact out ~rho:rho cell.g_fact)
                else str := Printf.sprintf "%s%s }" !str (Fact.display_deduction_fact out ~rho:rho cell.g_fact);

                incr current_number
              ) sdf.map_ground;
              !str
          | _ ->
              let tab_str_inside = create_tab (tab+1) in
              let str = ref (Printf.sprintf "\n%s{\n%s" tab_str tab_str_inside) in
              let current_number = ref 1 in
              IntMap.iter (fun _ cell ->
                if !current_number >= sdf.size
                then str := Printf.sprintf "%s%s\n%s}\n" !str (Fact.display_deduction_fact out ~rho:rho cell.fact) tab_str
                else if (!current_number / per_line)*per_line = !current_number
                then str := Printf.sprintf "%s%s,\n%s" !str (Fact.display_deduction_fact out cell.fact) tab_str_inside
                else str := Printf.sprintf "%s%s, "!str (Fact.display_deduction_fact out ~rho:rho cell.fact);

                incr current_number
              ) sdf.map;
              IntMap.iter (fun _ cell ->
                if !current_number >= sdf.size
                then str := Printf.sprintf "%s%s\n%s}\n" !str (Fact.display_deduction_fact out ~rho:rho cell.g_fact) tab_str
                else if (!current_number / per_line)*per_line = !current_number
                then str := Printf.sprintf "%s%s,\n%s" !str (Fact.display_deduction_fact out cell.g_fact) tab_str_inside
                else str := Printf.sprintf "%s%s, "!str (Fact.display_deduction_fact out ~rho:rho cell.g_fact);

                incr current_number
              ) sdf.map_ground;
              !str
        end
end

(************************
***         DF        ***
*************************)

module DF = struct

  module Var_Comp =
  struct
    type t = snd_ord_variable
    let compare = Variable.order Recipe
  end

  module VarMap = Map.Make(Var_Comp)

  type t = protocol_term VarMap.t

  (******* Generation *******)

  let empty = VarMap.empty

  let add df b_fct =
    Config.debug (fun () ->
      try
        let _ = VarMap.find (BasicFact.get_snd_ord_variable b_fct) df in
        Config.internal_error "[data_structure.ml >> DF.add] A basic deduction fact with the same second-order variable already exists."
      with
        | Not_found-> ()
    );

    VarMap.add (BasicFact.get_snd_ord_variable b_fct) (BasicFact.get_protocol_term b_fct) df

  let remove df x_snd =
    Config.debug (fun () ->
      try
        let _ = VarMap.find x_snd df in
        ()
      with
        | Not_found -> Config.internal_error "[data_structure.ml >> DF.remove] No basic deduction fact has the variable given in argument."
    );

    VarMap.remove x_snd df

  let apply df (subst: (fst_ord, name) Subst.t) =

    let map_term df (f:protocol_term -> protocol_term) =
      VarMap.map (fun t -> f t) df
    in
    Subst.apply subst df map_term

  let get_protocol_term df x = VarMap.find x df

  (********* Testing ********)

  let find_protocol_opt df (t:protocol_term) = match VarMap.search_key_opt (is_equal Protocol t) df with
    | None -> None
    | Some v -> Some (of_variable v)

  let find_recipe df (v:snd_ord_variable) = VarMap.find v df

  (********* Iterators ********)

  let fold f a df = VarMap.fold (fun x t c -> f c x t) df a

  let iter df f = VarMap.iter (fun x t -> f x t) df

  let iter_variables_and_terms (_:fst_ord_variable -> unit) (f_term:protocol_term -> unit) df =
    VarMap.iter (fun _ t -> f_term t) df

  let map_variables_and_terms (_:fst_ord_variable -> fst_ord_variable) (f_term:protocol_term -> protocol_term) df =
    VarMap.map (fun t -> f_term t) df

  let iter2 = VarMap.iter2

  let display out ?(rho = None) ?(per_line = 8) ?(tab = 0) df = match out with
    | Testing ->
        if VarMap.is_empty df
        then emptyset Testing
        else
          begin
            let s = VarMap.cardinal df in
            let current_number = ref 1 in
            let str = ref "{ " in
            VarMap.iter (fun x t ->
              if !current_number < s
              then str := Printf.sprintf "%s%s, " !str (BasicFact.display Testing ~rho:rho (BasicFact.create x t))
              else str := Printf.sprintf "%s%s }" !str (BasicFact.display Testing ~rho:rho (BasicFact.create x t));

              incr current_number
            ) df;
            !str
          end
    | Latex ->
        if VarMap.is_empty df
        then emptyset Latex
        else
          begin
            let s = VarMap.cardinal df in
            let str = ref "\\left\\{ \\begin{array}{l} " in
            let current_number = ref 1 in
            VarMap.iter (fun x t ->
              if !current_number >= s
              then str := Printf.sprintf "%s%s \\end{array}\\right\\}" !str (BasicFact.display Latex ~rho:rho (BasicFact.create x t))
              else if (!current_number / per_line)*per_line = !current_number
              then str := Printf.sprintf "%s%s,\\\\" !str (BasicFact.display Latex ~rho:rho (BasicFact.create x t))
              else str := Printf.sprintf "%s%s, " !str (BasicFact.display Latex ~rho:rho (BasicFact.create x t));

              incr current_number
            ) df;
            !str
          end
    | HTML ->
        if VarMap.is_empty df
        then emptyset HTML
        else
          begin
            let s = VarMap.cardinal df in
            let str = ref "<table class=\"df\"><tr><td>" in
            let current_number = ref 1 in
            VarMap.iter (fun x t ->
              if !current_number >= s
              then str := Printf.sprintf "%s%s</td></tr></table>" !str (BasicFact.display HTML ~rho:rho (BasicFact.create x t))
              else if (!current_number / per_line)*per_line = !current_number
              then str := Printf.sprintf "%s%s,</td></tr><tr><td>" !str (BasicFact.display HTML ~rho:rho (BasicFact.create x t))
              else str := Printf.sprintf "%s%s, " !str (BasicFact.display HTML ~rho:rho (BasicFact.create x t));

              incr current_number
            ) df;
            !str
          end
    | _ ->
        let tab_str = create_tab tab in
        begin match VarMap.cardinal df with
          | 0 -> "{}"
          | s when s <= per_line ->
              let str = ref "{ " in
              let current_number = ref 1 in
              VarMap.iter (fun x t ->
                if !current_number < s
                then str := Printf.sprintf "%s%s; " !str (BasicFact.display out ~rho:rho (BasicFact.create x t))
                else str := Printf.sprintf "%s%s }" !str (BasicFact.display out ~rho:rho (BasicFact.create x t));

                incr current_number
              ) df;
              !str
          | s ->
              let tab_str_inside = create_tab (tab+1) in
              let str = ref (Printf.sprintf "\n%s{\n%s" tab_str tab_str_inside) in
              let current_number = ref 1 in
              VarMap.iter (fun x t ->
                if !current_number >= s
                then str := Printf.sprintf "%s%s\n%s}\n" !str (BasicFact.display out ~rho:rho (BasicFact.create x t)) tab_str
                else if (!current_number / per_line)*per_line = !current_number
                then str := Printf.sprintf "%s%s,\n%s" !str (BasicFact.display out (BasicFact.create x t)) tab_str_inside
                else str := Printf.sprintf "%s%s, "!str (BasicFact.display out ~rho:rho (BasicFact.create x t));

                incr current_number
              ) df;
              !str
        end
end


(************************
***         UF        ***
*************************)

module UF = struct

  type state_ded_form =
    | DedSolved of Fact.deduction list
    | DedUnsolved of Fact.deduction_formula list
    | DedNone

  type state_eq_form =
    | EqSolved of Fact.equality
    | EqUnsolved of Fact.equality_formula
    | EqNone

  type t =
    {
      ded_formula : state_ded_form;
      eq_formula : state_eq_form
    }

  (******** Testing *********)

  let match_variables_and_names uf1 uf2 =
    Config.debug (fun () ->
      if uf1.eq_formula <> EqNone || uf2.eq_formula <> EqNone
      then Config.internal_error "[data_structure.ml >> UF.match_variables_and_names] This function should only be applied on intial constraint systems."
    );

    match uf1.ded_formula, uf2.ded_formula with
      | DedNone, DedNone -> ()
      | DedSolved [fact1], DedSolved [fact2] ->
          Term.match_variables_and_names_in_terms (Fact.get_protocol_term fact1) (Fact.get_protocol_term fact2)
      | _ -> Config.internal_error "[data_structure.ml >> UF.match_variables_and_names] This function should only be applied on intial constraint systems (2)."

  let iter_variables_and_terms (f_var:fst_ord_variable -> unit) (f_term:protocol_term -> unit) uf =
    begin match uf.eq_formula with
      | EqUnsolved form -> Fact.iter_variables_and_terms_formula Fact.Equality f_var f_term form
      | _ -> ()
    end;
    begin match uf.ded_formula with
      | DedSolved ded_list -> List.iter (Fact.iter_variables_and_terms_deduction f_var f_term) ded_list
      | DedUnsolved form_list -> List.iter (Fact.iter_variables_and_terms_formula Fact.Deduction f_var f_term) form_list
      | _ -> ()
    end

  let map_variables_and_terms (f_var:fst_ord_variable -> fst_ord_variable) (f_term:protocol_term -> protocol_term) uf =
    let eq_form = match uf.eq_formula with
      | EqUnsolved form -> EqUnsolved (Fact.map_variables_and_terms_formula Fact.Equality f_var f_term form)
      | eq -> eq
    in
    let ded_form = match uf.ded_formula with
      | DedSolved ded_list -> DedSolved(List.map (Fact.map_variables_and_terms_deduction f_var f_term) ded_list)
      | DedUnsolved form_list -> DedUnsolved (List.map (Fact.map_variables_and_terms_formula Fact.Deduction f_var f_term) form_list)
      | ded -> ded
    in
    { ded_formula = ded_form ; eq_formula = eq_form }
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

      if Fact.is_fact form
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

      if List.exists Fact.is_fact form_list
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

  let exists_equality_fact uf = match uf.eq_formula with
    | EqSolved _ -> true
    | _ -> false

  let exists_deduction_fact uf = match uf.ded_formula with
    | DedSolved _ -> true
    | _ -> false

  let exists_unsolved_equality_formula uf = match uf.eq_formula with
    | EqUnsolved _ -> true
    | _ -> false

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

  exception Solved_ded of Fact.deduction

  let apply uf subst =

    if (uf.ded_formula = DedNone && uf.eq_formula = EqNone) || Subst.is_identity subst
    then uf
    else
      let new_ded_formula = match uf.ded_formula with
        | DedNone -> DedNone
        | DedSolved fact_list -> DedSolved (List.map (Fact.apply_fst_on_deduction_fact subst) fact_list)
        | DedUnsolved form_list ->
            begin try
              let form_list' =
                List.fold_left (fun acc form ->
                  try
                    let form_1 = Fact.apply_fst_on_formula Fact.Deduction subst form in
                    if Fact.is_fact form_1
                    then raise (Solved_ded (Fact.get_head form_1))
                    else form_1 :: acc
                  with Fact.Bot -> acc
                ) [] form_list
              in

              if form_list' = []
              then DedNone
              else DedUnsolved form_list'
            with Solved_ded fact -> DedSolved [fact]
            end
      in

      let new_eq_formula = match uf.eq_formula with
        | EqUnsolved form ->
            begin try
              let form_1 = Fact.apply_fst_on_formula Fact.Equality subst form in
              if Fact.is_fact form_1
              then EqSolved (Fact.get_head form_1)
              else EqUnsolved form_1
            with
              | Fact.Bot -> EqNone
            end
        | _ -> uf.eq_formula
      in

      { ded_formula = new_ded_formula ; eq_formula = new_eq_formula }

  let apply_with_gathering uf subst_snd subst_fst ded_ref eq_ref =
    if (uf.ded_formula = DedNone && uf.eq_formula = EqNone)
    then uf
    else
      match Subst.is_identity subst_fst, Subst.is_identity subst_snd with
        | true,true -> uf
        | true,false ->
            let new_ded_formula = match uf.ded_formula with
              | DedNone -> DedNone
              | DedSolved fact_list ->
                  if !ded_ref = []
                  then
                    begin
                      let fact_list' = List.map (Fact.apply_snd_on_fact Fact.Deduction subst_snd) fact_list in
                      let recipe_list = List.map (fun fact -> Fact.get_recipe fact) fact_list' in
                      ded_ref := recipe_list;
                      DedSolved fact_list'
                    end
                  else DedSolved (List.map2 Fact.replace_recipe_in_deduction_fact !ded_ref fact_list)
              | DedUnsolved form_list ->
                  if !ded_ref = []
                  then
                    begin
                      let form = List.hd form_list in
                      let form' = Fact.apply_snd_on_formula Fact.Deduction subst_snd form in
                      let recipe = Fact.get_recipe (Fact.get_head form') in
                      let q_form = List.rev_map (Fact.replace_recipe_in_deduction_formula recipe) (List.tl form_list) in
                      ded_ref := [recipe];
                      DedUnsolved (form'::q_form)
                    end
                  else DedUnsolved (List.rev_map (Fact.replace_recipe_in_deduction_formula (List.hd !ded_ref)) form_list)
            in

            let new_eq_formula = match uf.eq_formula with
              | EqNone -> EqNone
              | EqSolved fact ->
                  begin match !eq_ref with
                    | None ->
                        let fact' = Fact.apply_snd_on_fact Fact.Equality subst_snd fact in
                        eq_ref := Some fact';
                        EqSolved fact'
                    | Some eq_fact -> EqSolved eq_fact
                  end
              | EqUnsolved form ->
                  begin match !eq_ref with
                    | None ->
                        let form' = Fact.apply_snd_on_formula Fact.Equality subst_snd form in
                        eq_ref := Some (Fact.get_head form');
                        EqUnsolved form'
                    | Some eq_fact -> EqUnsolved (Fact.replace_head_in_equality_formula eq_fact form)
                  end
            in

            { ded_formula = new_ded_formula ; eq_formula = new_eq_formula }
        | false,true ->
            let new_ded_formula = match uf.ded_formula with
              | DedNone -> DedNone
              | DedSolved fact_list -> DedSolved (List.map (Fact.apply_fst_on_deduction_fact subst_fst) fact_list)
              | DedUnsolved form_list ->
                  begin try
                    let form_list' =
                      List.fold_left (fun acc form ->
                        try
                          let form_1 = Fact.apply_fst_on_formula Fact.Deduction subst_fst form in
                          if Fact.is_fact form_1
                          then raise (Solved_ded (Fact.get_head form_1))
                          else form_1 :: acc
                        with Fact.Bot -> acc
                      ) [] form_list
                    in

                    if form_list' = []
                    then DedNone
                    else DedUnsolved form_list'
                  with Solved_ded fact -> DedSolved [fact]
                  end
            in

            let new_eq_formula = match uf.eq_formula with
              | EqUnsolved form ->
                  begin try
                    let form_1 = Fact.apply_fst_on_formula Fact.Equality subst_fst form in
                    if Fact.is_fact form_1
                    then EqSolved (Fact.get_head form_1)
                    else EqUnsolved form_1
                  with
                    | Fact.Bot -> EqNone
                  end
              | _ -> uf.eq_formula
            in

            { ded_formula = new_ded_formula ; eq_formula = new_eq_formula }
        | false,false ->
            let new_ded_formula = match uf.ded_formula with
              | DedNone -> DedNone
              | DedSolved fact_list ->
                  if !ded_ref = []
                  then
                    begin
                      let fact_list' = List.map (Fact.apply_on_deduction_fact subst_snd subst_fst) fact_list in
                      let recipe_list = List.map (fun fact -> Fact.get_recipe fact) fact_list' in
                      ded_ref := recipe_list;
                      DedSolved fact_list'
                    end
                  else
                    let fact_list' = List.map (Fact.apply_fst_on_deduction_fact subst_fst) fact_list in
                    DedSolved (List.map2 Fact.replace_recipe_in_deduction_fact !ded_ref fact_list')
              | DedUnsolved form_list ->
                  begin try
                    let form_list' =
                      List.fold_left (fun acc form ->
                        try
                          let form_1 = Fact.apply_fst_on_formula Fact.Deduction subst_fst form in
                          if Fact.is_fact form_1
                          then raise (Solved_ded (Fact.get_head form_1))
                          else form_1 :: acc
                        with Fact.Bot -> acc
                      ) [] form_list
                    in

                    if form_list' = []
                    then DedNone
                    else
                      if !ded_ref = []
                      then
                        begin
                          let form = Fact.apply_snd_on_formula Fact.Deduction subst_snd (List.hd form_list') in
                          let recipe = Fact.get_recipe (Fact.get_head form) in
                          ded_ref := [recipe];
                          DedUnsolved (form::(List.rev_map (Fact.replace_recipe_in_deduction_formula recipe) (List.tl form_list')))
                        end
                      else DedUnsolved (List.rev_map (Fact.replace_recipe_in_deduction_formula (List.hd !ded_ref)) form_list')
                  with Solved_ded fact -> DedSolved [Fact.replace_recipe_in_deduction_fact (List.hd !ded_ref) fact]
                  end
            in

            let new_eq_formula = match uf.eq_formula with
              | EqNone -> EqNone
              | EqSolved fact ->
                  begin match !eq_ref with
                    | None ->
                        let fact' = Fact.apply_snd_on_fact Fact.Equality subst_snd fact in
                        eq_ref := Some fact';
                        EqSolved fact'
                    | Some fact' -> EqSolved fact'
                  end
              | EqUnsolved form ->
                  begin try
                    let form_1 = Fact.apply_fst_on_formula Fact.Equality subst_fst form in
                    match !eq_ref with
                      | None ->
                          let form_2 = Fact.apply_snd_on_formula Fact.Equality subst_snd form_1 in
                          let head = Fact.get_head form_2 in
                          eq_ref := Some head;
                          if Fact.is_fact form_2
                          then EqSolved head
                          else EqUnsolved form_2
                      | Some eq_fact ->
                          if Fact.is_fact form_1
                          then EqSolved eq_fact
                          else EqUnsolved (Fact.replace_head_in_equality_formula eq_fact form_1)
                  with Fact.Bot -> EqNone
                  end
            in

            { ded_formula = new_ded_formula ; eq_formula = new_eq_formula }

  (**** Display functions ****)

  let gather_deduction_formula uf = match uf.ded_formula with
    | DedNone -> []
    | DedSolved fact_list -> List.map (fun fact -> Fact.create Fact.Deduction fact []) fact_list
    | DedUnsolved form_list -> form_list

  let gather_equality_formula uf = match uf.eq_formula with
    | EqNone -> []
    | EqSolved fact -> [Fact.create Fact.Equality fact []]
    | EqUnsolved form -> [form]

  let display out ?(rho = None) uf = match out with
    | Testing -> Printf.sprintf "{{%s}{%s}}"
        (display_list (fun form -> Printf.sprintf "(%s)" (Fact.display_formula Testing ~rho:rho Fact.Deduction form)) "" (gather_deduction_formula uf))
        (display_list (fun form -> Printf.sprintf "(%s)" (Fact.display_formula Testing ~rho:rho Fact.Equality form)) "" (gather_equality_formula uf))
    | _ ->
        begin match gather_deduction_formula uf, gather_equality_formula uf with
          | [], [] -> emptyset out
          | [], form_list ->
              Printf.sprintf "%s %s %s"
                (lcurlybracket out)
                (display_list (fun form -> Printf.sprintf "%s" (Fact.display_formula out ~rho:rho Fact.Equality form)) ", " form_list)
                (rcurlybracket out)
          | form_list, [] ->
              Printf.sprintf "%s %s %s"
                (lcurlybracket out)
                (display_list (fun form -> Printf.sprintf "%s" (Fact.display_formula out ~rho:rho Fact.Deduction form)) ", " form_list)
                (rcurlybracket out)
          | ded_form_list, eq_form_list ->
              Printf.sprintf "%s %s, %s %s"
                (lcurlybracket out)
                (display_list (fun form -> Printf.sprintf "%s" (Fact.display_formula out ~rho:rho Fact.Deduction form)) ", " ded_form_list)
                (display_list (fun form -> Printf.sprintf "%s" (Fact.display_formula out ~rho:rho Fact.Equality form)) ", " eq_form_list)
                (rcurlybracket out)
        end
end

(************************
***         Eq        ***
*************************)

module Eq = struct

  type ('a, 'b) t =
    | Top
    | Bot
    | Conj of ('a, 'b) Diseq.t list

  (* Tested function *)

  let test_implies_Protocol : ((fst_ord, name) t -> (fst_ord, name) term -> (fst_ord, name) term -> bool -> unit) ref = ref (fun _ _ _ _ -> ())

  let test_implies_Recipe : ((snd_ord, axiom) t -> (snd_ord, axiom) term -> (snd_ord, axiom) term -> bool -> unit) ref = ref (fun _ _ _ _ -> ())

  (*let test_implies (type a) (type b) (at:(a,b) atom) (form: (a,b) t) (term1:(a,b) term) (term2:(a,b) term) (res:bool) = match at with
    | Protocol -> !test_implies_Protocol form term1 term2 res
    | Recipe -> !test_implies_Recipe form term1 term2 res*)

  let update_test_implies (type a) (type b) (at:(a,b) atom) (f: (a, b) t -> (a, b) term -> (a, b) term -> bool -> unit) = match at with
    | Protocol -> test_implies_Protocol := f
    | Recipe -> test_implies_Recipe := f

  (* Generation *)

  let top = Top

  let bot = Bot

  let is_bot = function
    | Bot -> true
    | _ -> false

  let is_top = function
    | Top -> true
    | _ -> false

  let wedge form diseq = match form with
    | Top -> Conj [diseq]
    | Bot -> Bot
    | Conj diseq_l -> Conj (diseq::diseq_l)

  (***** Access *****)

  let get_names_with_list at form l = match form with
    | Bot | Top -> l
    | Conj diseq_l ->
        List.fold_left (fun acc diseq -> Diseq.get_names_with_list at diseq acc) l diseq_l

  let get_vars_with_list at form l = match form with
    | Bot | Top -> l
    | Conj diseq_l ->
        List.fold_left (fun acc diseq -> Diseq.get_vars_with_list at diseq acc) l diseq_l

  let get_axioms_with_list form l = match form with
    | Bot | Top -> l
    | Conj diseq_l ->
        List.fold_left (fun acc diseq -> Diseq.get_axioms_with_list diseq acc) l diseq_l

  let iter_variables_and_terms (f_var:fst_ord_variable -> unit) (f_term:protocol_term -> unit) = function
    | Conj l -> List.iter (Diseq.iter_variables_and_terms f_var f_term) l
    | _ -> ()

  let map_variables_and_terms (f_var:fst_ord_variable -> fst_ord_variable) (f_term:protocol_term -> protocol_term) = function
    | Conj l -> Conj (List.map (Diseq.map_variables_and_terms f_var f_term) l)
    | eq -> eq

  exception Is_Bot

  let apply at form subst = match form with
    | Top -> Top
    | Bot -> Bot
    | Conj diseq_l ->
        try
          let diseq_l_1 = List.fold_left (fun l diseq ->
            let diseq_1 = Diseq.apply_and_normalise at subst diseq in
            if Diseq.is_bot diseq_1
            then raise Is_Bot
            else if Diseq.is_top diseq_1
            then l
            else diseq_1::l
            ) [] diseq_l
          in

          if diseq_l_1 = []
          then Top
          else Conj diseq_l_1
        with
        | Is_Bot -> Bot

  let extract = function
    | Conj [diseq] -> diseq, Top
    | Conj (diseq::q) -> diseq, Conj q
    | _ -> Config.internal_error "[data_structure.ml >> DF.extract] There should be at least one disequation."

  let display out ?(rho=None) at = function
    | Top -> Display.top out
    | Bot -> Display.bot out
    | Conj diseq_list -> Display.display_list (Diseq.display out ~rho:rho at) (Printf.sprintf " %s " (Display.wedge out)) diseq_list

  let match_variables_and_names f_next eq1 eq2 = match eq1, eq2 with
    | Top, Top | Bot, Bot -> f_next ()
    | Conj diseq_l1, Conj diseq_l2 ->
        if List.length diseq_l1 <> List.length diseq_l2
        then raise No_Match;

        match_variables_and_names_elt_list f_next Diseq.match_variables_and_names diseq_l1 diseq_l2
    | _ -> raise No_Match

  let occurs (v:fst_ord_variable) = function
    | Conj diseq -> List.exists (Diseq.occurs v) diseq
    | _ -> false

  module Mixed = struct

    type t =
      | MTop
      | MBot
      | MConj of Diseq.Mixed.t list

    let top = MTop

    let bot = MBot

    let wedge form diseq = match form with
      | MTop -> MConj [diseq]
      | MBot -> MBot
      | MConj diseq_l -> MConj (diseq::diseq_l)

    let map_variables_and_terms (f_var:fst_ord_variable -> fst_ord_variable) (f_term:protocol_term -> protocol_term) = function
      | MConj l -> MConj (List.map (Diseq.Mixed.map_variables_and_terms f_var f_term) l)
      | eq -> eq

    let apply form fst_subst snd_subst = match form with
      | MTop -> MTop
      | MBot -> MBot
      | MConj diseq_l ->
          try
            let diseq_l' =
              List.fold_left (fun acc diseq ->
                let diseq' = Diseq.Mixed.apply_and_normalise fst_subst snd_subst diseq in
                if Diseq.Mixed.is_bot diseq'
                then raise Is_Bot
                else if Diseq.Mixed.is_top diseq'
                then acc
                else diseq'::acc
              ) [] diseq_l
            in
            if diseq_l' = []
            then MTop
            else MConj diseq_l'
          with Is_Bot -> MBot

    let is_top = function
      | MTop -> true
      | _ -> false

    let is_bot = function
      | MBot -> true
      | _ -> false
  end
end

(*****************************************
***                Tools               ***
******************************************)

module Tools = Tools_Subterm(K)(IK)(DF)(Eq.Mixed)(Eq)
