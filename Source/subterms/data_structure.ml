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

module SDF = struct

  module Int_Comp =
  struct
    type t = int
    let compare = compare
  end

  module SDF_Map = Map.Make(Int_Comp)

  type cell =
    {
      var_type : int;
      fact : Fact.deduction;
      recipe_ground : bool;
      protocol_ground : bool;
      marked_uniset : bool
    }

  type cell_ground =
    {
      g_var_type : int;
      g_fact : Fact.deduction;
      g_marked_uniset : bool
    }

  type t =
    {
      all_id : int list;
      last_entry_ground : bool;
      size : int;
      map : cell SDF_Map.t;
      map_ground : cell_ground SDF_Map.t
    }

  (******* Access ********)

  let cardinal sdf = sdf.size

  let last_entry sdf =
    try
      if sdf.last_entry_ground
      then
        let _, cell = SDF_Map.max_binding sdf.map_ground in
        cell.g_fact
      else
        let _, cell = SDF_Map.max_binding sdf.map in
        cell.fact
    with
      | Not_found -> Config.internal_error "[Data_structure.ml >> last_entry] Should not apply last entry on an empty SDF."

  let last_entry_with_id sdf =
    try
      if sdf.last_entry_ground
      then
        let id,cell = SDF_Map.max_binding sdf.map_ground in
        cell.g_fact, id
      else
        let id,cell = SDF_Map.max_binding sdf.map in
        cell.fact, id
    with
      | Not_found -> Config.internal_error "[Data_structure.ml >> last_entry_with_id] Should not apply last entry on an empty SDF."

  let last_entry_id sdf = sdf.size

  let all_id sdf = sdf.all_id

  let get sdf id =
    try
      let cell = SDF_Map.find id sdf.map_ground in
      cell.g_fact
    with
      | Not_found ->
        begin
          try
            let cell = SDF_Map.find id sdf.map in
            cell.fact
          with
          | Not_found -> Config.internal_error "[Data_structure.ml >> get] There is no deduction fact in SDF with this recipe equivalent id."
        end

  (******* Iterators ********)

  exception Out_of_type

  let iter sdf f =
    SDF_Map.iter (fun _ cell -> f cell.g_fact) sdf.map_ground;
    SDF_Map.iter (fun _ cell -> f cell.fact) sdf.map

  let iter_id sdf f =
    SDF_Map.iter (fun id cell -> f id cell.g_fact) sdf.map_ground;
    SDF_Map.iter (fun id cell -> f id cell.fact) sdf.map

  let iter_unmarked sdf f =
    SDF_Map.iter (fun id cell -> if not cell.g_marked_uniset then f id cell.g_fact) sdf.map_ground;
    SDF_Map.iter (fun id cell -> if not cell.marked_uniset then f id cell.fact) sdf.map

  let iter_within_var_type k sdf f =
    begin try
      SDF_Map.iter (fun _ cell ->
        if cell.g_var_type > k
        then raise Out_of_type
        else f cell.g_fact
        ) sdf.map_ground;
    with
    | Out_of_type -> ()
    end;
    try
      SDF_Map.iter (fun _ cell ->
        if cell.var_type > k
        then raise Out_of_type
        else f cell.fact
        ) sdf.map;
    with
    | Out_of_type -> ()

  let tail_iter_within_var_type k sdf f f_next =
    SDF_Map.tail_iter_until (fun cell f_next_1 -> f cell.g_fact f_next_1) (fun cell -> cell.g_var_type > k) sdf.map_ground
      (fun () -> SDF_Map.tail_iter_until (fun cell f_next_1 -> f cell.fact f_next_1) (fun cell -> cell.var_type > k) sdf.map f_next)

  let tail_iter sdf f f_next =
    SDF_Map.tail_iter (fun cell f_next_1 -> f cell.g_fact f_next_1) sdf.map_ground
      (fun () -> SDF_Map.tail_iter (fun cell f_next_1 -> f cell.fact f_next_1) sdf.map f_next)

  let map_protocol_term sdf f =
    if sdf.last_entry_ground
    then
      let (map_ground, map) =
        SDF_Map.fold (fun i cell (acc_map_ground, acc_map) ->
          if cell.protocol_ground
          then (acc_map_ground, SDF_Map.add i cell acc_map)
          else
            let t = f (Fact.get_protocol_term cell.fact) in
            if is_ground t
            then
              if cell.recipe_ground
              then (SDF_Map.add i { g_var_type = cell.var_type; g_fact = Fact.create_deduction_fact (Fact.get_recipe cell.fact) t ; g_marked_uniset = cell.marked_uniset } acc_map_ground, acc_map)
              else (acc_map_ground, SDF_Map.add i { cell with protocol_ground = true; fact = Fact.create_deduction_fact (Fact.get_recipe cell.fact) t } acc_map)
            else (acc_map_ground, SDF_Map.add i { cell with fact = Fact.create_deduction_fact (Fact.get_recipe cell.fact) t } acc_map)
        ) sdf.map (sdf.map_ground, SDF_Map.empty)
      in
      { sdf with map_ground = map_ground; map = map }
    else
      let (map_ground, map, last_entry_ground) =
        SDF_Map.fold (fun i cell (acc_map_ground, acc_map, acc_last_entry_ground) ->
          if cell.protocol_ground
          then (acc_map_ground, SDF_Map.add i cell acc_map, acc_last_entry_ground)
          else
            let t = f (Fact.get_protocol_term cell.fact) in
            if is_ground t
            then
              if cell.recipe_ground
              then (SDF_Map.add i { g_var_type = cell.var_type; g_fact = Fact.create_deduction_fact (Fact.get_recipe cell.fact) t ; g_marked_uniset = cell.marked_uniset } acc_map_ground, acc_map, acc_last_entry_ground || i = sdf.size)
              else (acc_map_ground, SDF_Map.add i { cell with protocol_ground = true; fact = Fact.create_deduction_fact (Fact.get_recipe cell.fact) t } acc_map, acc_last_entry_ground)
            else (acc_map_ground, SDF_Map.add i { cell with fact = Fact.create_deduction_fact (Fact.get_recipe cell.fact) t } acc_map, acc_last_entry_ground)
        ) sdf.map (sdf.map_ground, SDF_Map.empty, false)
      in
      { sdf with map_ground = map_ground; map = map; last_entry_ground = last_entry_ground }

  let map_recipe sdf f =
    if sdf.last_entry_ground
    then
      let (map_ground, map) =
        SDF_Map.fold (fun i cell (acc_map_ground, acc_map) ->
          if cell.recipe_ground
          then (acc_map_ground, SDF_Map.add i cell acc_map)
          else
            let t = f (Fact.get_recipe cell.fact) in
            if is_ground t
            then
              if cell.protocol_ground
              then (SDF_Map.add i { g_var_type = cell.var_type; g_fact = Fact.create_deduction_fact t (Fact.get_protocol_term cell.fact) ; g_marked_uniset = cell.marked_uniset } acc_map_ground, acc_map)
              else (acc_map_ground, SDF_Map.add i { cell with recipe_ground = true; fact = Fact.create_deduction_fact  t (Fact.get_protocol_term cell.fact) } acc_map)
            else (acc_map_ground, SDF_Map.add i { cell with fact = Fact.create_deduction_fact t (Fact.get_protocol_term cell.fact) } acc_map)
        ) sdf.map (sdf.map_ground, SDF_Map.empty)
      in
      { sdf with map_ground = map_ground; map = map }
    else
      let (map_ground, map, last_entry_ground) =
        SDF_Map.fold (fun i cell (acc_map_ground, acc_map, acc_last_entry_ground) ->
          if cell.recipe_ground
          then (acc_map_ground, SDF_Map.add i cell acc_map, acc_last_entry_ground)
          else
            let t = f (Fact.get_recipe cell.fact) in
            if is_ground t
            then
              if cell.protocol_ground
              then (SDF_Map.add i { g_var_type = cell.var_type; g_fact = Fact.create_deduction_fact t (Fact.get_protocol_term cell.fact) ; g_marked_uniset = cell.marked_uniset } acc_map_ground, acc_map, acc_last_entry_ground || i = sdf.size)
              else (acc_map_ground, SDF_Map.add i { cell with recipe_ground = true; fact = Fact.create_deduction_fact t (Fact.get_protocol_term cell.fact) } acc_map, acc_last_entry_ground)
            else (acc_map_ground, SDF_Map.add i { cell with fact = Fact.create_deduction_fact t (Fact.get_protocol_term cell.fact) } acc_map, acc_last_entry_ground)
        ) sdf.map (sdf.map_ground, SDF_Map.empty, false)
      in
      { sdf with map_ground = map_ground; map = map; last_entry_ground = last_entry_ground }

  let apply sdf subst_snd subst_fst =
    if Subst.is_identity subst_snd
    then
      if Subst.is_identity subst_fst
      then sdf
      else Subst.apply subst_fst sdf map_protocol_term
    else
      if Subst.is_identity subst_fst
      then Subst.apply subst_snd sdf map_recipe
      else
        let sdf_1 = Subst.apply subst_snd sdf map_recipe in
        Subst.apply subst_fst sdf_1 map_protocol_term

  let apply_snd_and_gather sdf subst array_recipe =
    let map_recipe_gather sdf f =
      if sdf.last_entry_ground
      then
        let (map_ground, map) =
          SDF_Map.fold (fun i cell (acc_map_ground, acc_map) ->
            if cell.recipe_ground
            then (acc_map_ground, SDF_Map.add i cell acc_map)
            else
              let t = f (Fact.get_recipe cell.fact) in
              if is_ground t
              then
                begin
                  array_recipe.(i-1) <- (t,true);
                  if cell.protocol_ground
                  then (SDF_Map.add i { g_var_type = cell.var_type; g_fact = Fact.create_deduction_fact t (Fact.get_protocol_term cell.fact) ; g_marked_uniset = cell.marked_uniset } acc_map_ground, acc_map)
                  else (acc_map_ground, SDF_Map.add i { cell with recipe_ground = true; fact = Fact.create_deduction_fact  t (Fact.get_protocol_term cell.fact) } acc_map)
                end
              else
                begin
                  array_recipe.(i-1) <- (t,false);
                  (acc_map_ground, SDF_Map.add i { cell with fact = Fact.create_deduction_fact t (Fact.get_protocol_term cell.fact) } acc_map)
                end
          ) sdf.map (sdf.map_ground, SDF_Map.empty)
        in
        { sdf with map_ground = map_ground; map = map }
      else
        let (map_ground, map, last_entry_ground) =
          SDF_Map.fold (fun i cell (acc_map_ground, acc_map, acc_last_entry_ground) ->
            if cell.recipe_ground
            then (acc_map_ground, SDF_Map.add i cell acc_map, acc_last_entry_ground)
            else
              let t = f (Fact.get_recipe cell.fact) in
              if is_ground t
              then
                begin
                  array_recipe.(i-1) <- (t,true);
                  if cell.protocol_ground
                  then (SDF_Map.add i { g_var_type = cell.var_type; g_fact = Fact.create_deduction_fact t (Fact.get_protocol_term cell.fact) ; g_marked_uniset = cell.marked_uniset } acc_map_ground, acc_map, acc_last_entry_ground || i = sdf.size)
                  else (acc_map_ground, SDF_Map.add i { cell with recipe_ground = true; fact = Fact.create_deduction_fact t (Fact.get_protocol_term cell.fact) } acc_map, acc_last_entry_ground)
                end
              else
                begin
                  array_recipe.(i-1) <- (t,false);
                  (acc_map_ground, SDF_Map.add i { cell with fact = Fact.create_deduction_fact t (Fact.get_protocol_term cell.fact) } acc_map, acc_last_entry_ground)
                end
          ) sdf.map (sdf.map_ground, SDF_Map.empty, false)
        in
        { sdf with map_ground = map_ground; map = map; last_entry_ground = last_entry_ground }
    in

    Subst.apply subst sdf map_recipe_gather

  let apply_snd_from_gathering sdf array_recipe =
    if sdf.last_entry_ground
    then
      let (map_ground, map) =
        SDF_Map.fold (fun i cell (acc_map_ground, acc_map) ->
          if cell.recipe_ground
          then (acc_map_ground, SDF_Map.add i cell acc_map)
          else
            let (t,is_ground) = array_recipe.(i-1) in
            if is_ground
            then
              if cell.protocol_ground
              then (SDF_Map.add i { g_var_type = cell.var_type; g_fact = Fact.create_deduction_fact t (Fact.get_protocol_term cell.fact) ; g_marked_uniset = cell.marked_uniset } acc_map_ground, acc_map)
              else (acc_map_ground, SDF_Map.add i { cell with recipe_ground = true; fact = Fact.create_deduction_fact  t (Fact.get_protocol_term cell.fact) } acc_map)
            else (acc_map_ground, SDF_Map.add i { cell with fact = Fact.create_deduction_fact t (Fact.get_protocol_term cell.fact) } acc_map)
        ) sdf.map (sdf.map_ground, SDF_Map.empty)
      in
      { sdf with map_ground = map_ground; map = map }
    else
      let (map_ground, map, last_entry_ground) =
        SDF_Map.fold (fun i cell (acc_map_ground, acc_map, acc_last_entry_ground) ->
          if cell.recipe_ground
          then (acc_map_ground, SDF_Map.add i cell acc_map, acc_last_entry_ground)
          else
            let (t,is_ground) = array_recipe.(i-1) in
            if is_ground
            then
              if cell.protocol_ground
              then (SDF_Map.add i { g_var_type = cell.var_type; g_fact = Fact.create_deduction_fact t (Fact.get_protocol_term cell.fact) ; g_marked_uniset = cell.marked_uniset } acc_map_ground, acc_map, acc_last_entry_ground || i = sdf.size)
              else (acc_map_ground, SDF_Map.add i { cell with recipe_ground = true; fact = Fact.create_deduction_fact t (Fact.get_protocol_term cell.fact) } acc_map, acc_last_entry_ground)
            else (acc_map_ground, SDF_Map.add i { cell with fact = Fact.create_deduction_fact t (Fact.get_protocol_term cell.fact) } acc_map, acc_last_entry_ground)
        ) sdf.map (sdf.map_ground, SDF_Map.empty, false)
      in
      { sdf with map_ground = map_ground; map = map; last_entry_ground = last_entry_ground }

  (******* Testing ********)

  exception Found

  let exists sdf f =
    SDF_Map.exists (fun _ cell -> f cell.g_fact) sdf.map_ground || SDF_Map.exists (fun _ cell -> f cell.fact) sdf.map

  let exists_within_var_type k sdf f =
    let test_ground =
      try
        SDF_Map.iter (fun _ cell ->
          if cell.g_var_type > k
          then raise Out_of_type
          else
            if  f cell.g_fact
            then raise Found
            else ()
          ) sdf.map_ground;
        false
      with
      | Found -> true
      | Out_of_type -> false
    in
    if test_ground
    then true
    else
      try
        SDF_Map.iter (fun _ cell ->
          if cell.var_type > k
          then raise Out_of_type
          else
            if  f cell.fact
            then raise Found
            else ()
          ) sdf.map;
        false
      with
      | Found -> true
      | Out_of_type -> false

  let find sdf f =
    let result = ref None in

    try
      SDF_Map.iter (fun _ cell -> match f cell.fact with
        | None -> ()
        | Some a -> result := Some a; raise Found
      ) sdf.map;

      SDF_Map.iter (fun _ cell -> match f cell.g_fact with
        | None -> ()
        | Some a -> result := Some a; raise Found
      ) sdf.map_ground;

      !result
    with
    | Found -> !result

  type marked_result =
    | Not_in_SDF
    | Marked of protocol_term
    | Unmarked of protocol_term * t

  let find_term_and_mark sdf recipe =
    match SDF_Map.find_and_replace (fun _ cell -> is_equal Recipe recipe (Fact.get_recipe cell.fact)) (fun cell -> { cell with marked_uniset = true }) sdf.map with
      | None ->
          begin match SDF_Map.find_and_replace (fun _ g_cell -> is_equal Recipe recipe (Fact.get_recipe g_cell.g_fact)) (fun g_cell -> { g_cell with g_marked_uniset = true }) sdf.map_ground with
            | None -> Not_in_SDF
            | Some (g_cell,_) when g_cell.g_marked_uniset -> Marked (Fact.get_protocol_term g_cell.g_fact)
            | Some (g_cell,sdf_g_map) -> Unmarked (Fact.get_protocol_term g_cell.g_fact, { sdf with map_ground = sdf_g_map })
          end
      | Some (cell,_) when cell.marked_uniset -> Marked (Fact.get_protocol_term cell.fact)
      | Some (cell,sdf_map) -> Unmarked (Fact.get_protocol_term cell.fact, { sdf with map = sdf_map })

  (******* Basic operations *********)

  let empty = { size = 0 ; map = SDF_Map.empty; all_id = []; last_entry_ground = false; map_ground = SDF_Map.empty }

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
          if sdf.last_entry_ground
          then
            let (_,cell_max) = SDF_Map.max_binding sdf.map_ground in
            cell_max.g_var_type
          else
            let (_,cell_max) = SDF_Map.max_binding sdf.map in
            cell_max.var_type
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
        size = new_size;
        map_ground = SDF_Map.add new_size ({ g_var_type = var_type; g_fact = fct; g_marked_uniset = false }) sdf.map_ground;
        all_id = new_size::sdf.all_id;
        last_entry_ground = true;
      }
    else
      {
        sdf with
        size = new_size;
        map = SDF_Map.add new_size ({ var_type = var_type; fact = fct ; protocol_ground = protocol_ground; recipe_ground = recipe_ground; marked_uniset = false}) sdf.map;
        all_id = new_size::sdf.all_id;
        last_entry_ground = false
      }

  let display out ?(rho = None) ?(per_line = 8) ?(tab = 0) sdf = match out with
    | Testing ->
        if sdf.size = 0
        then emptyset Testing
        else
          begin
            let current_number = ref 1 in
            let str = ref "{ " in
            SDF_Map.iter (fun _ cell ->
              if !current_number < sdf.size
              then str := Printf.sprintf "%s%s, " !str (Fact.display_deduction_fact Testing ~rho:rho cell.fact)
              else str := Printf.sprintf "%s%s }" !str (Fact.display_deduction_fact Testing ~rho:rho cell.fact);

              incr current_number
            ) sdf.map;
            SDF_Map.iter (fun _ cell ->
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
            let str = ref "\\left\\{ \\begin{array}{l} " in
            let current_number = ref 1 in
            SDF_Map.iter (fun _ cell ->
              if !current_number >= sdf.size
              then str := Printf.sprintf "%s%s \\end{array}\\right\\}" !str (Fact.display_deduction_fact Latex ~rho:rho cell.fact)
              else if (!current_number / per_line)*per_line = !current_number
              then str := Printf.sprintf "%s%s,\\\\" !str (Fact.display_deduction_fact Latex ~rho:rho cell.fact)
              else str := Printf.sprintf "%s%s, " !str (Fact.display_deduction_fact Latex ~rho:rho cell.fact);

              incr current_number
            ) sdf.map;
            SDF_Map.iter (fun _ cell ->
              if !current_number >= sdf.size
              then str := Printf.sprintf "%s%s \\end{array}\\right\\}" !str (Fact.display_deduction_fact Latex ~rho:rho cell.g_fact)
              else if (!current_number / per_line)*per_line = !current_number
              then str := Printf.sprintf "%s%s,\\\\" !str (Fact.display_deduction_fact Latex ~rho:rho cell.g_fact)
              else str := Printf.sprintf "%s%s, " !str (Fact.display_deduction_fact Latex ~rho:rho cell.g_fact);

              incr current_number
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
            SDF_Map.iter (fun _ cell ->
              if !current_number >= sdf.size
              then str := Printf.sprintf "%s%s</td></tr></table>" !str (Fact.display_deduction_fact HTML ~rho:rho cell.fact)
              else if (!current_number / per_line)*per_line = !current_number
              then str := Printf.sprintf "%s%s,</td></tr><tr><td>" !str (Fact.display_deduction_fact HTML ~rho:rho cell.fact)
              else str := Printf.sprintf "%s%s, " !str (Fact.display_deduction_fact HTML ~rho:rho cell.fact);

              incr current_number
            ) sdf.map;
            SDF_Map.iter (fun _ cell ->
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
              SDF_Map.iter (fun _ cell ->
                if !current_number < sdf.size
                then str := Printf.sprintf "%s%s; " !str (Fact.display_deduction_fact out ~rho:rho cell.fact)
                else str := Printf.sprintf "%s%s }" !str (Fact.display_deduction_fact out ~rho:rho cell.fact);

                incr current_number
              ) sdf.map;
              SDF_Map.iter (fun _ cell ->
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
              SDF_Map.iter (fun _ cell ->
                if !current_number >= sdf.size
                then str := Printf.sprintf "%s%s\n%s}\n" !str (Fact.display_deduction_fact out ~rho:rho cell.fact) tab_str
                else if (!current_number / per_line)*per_line = !current_number
                then str := Printf.sprintf "%s%s,\n%s" !str (Fact.display_deduction_fact out cell.fact) tab_str_inside
                else str := Printf.sprintf "%s%s, "!str (Fact.display_deduction_fact out ~rho:rho cell.fact);

                incr current_number
              ) sdf.map;
              SDF_Map.iter (fun _ cell ->
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

  module DF_Map = Map.Make(Var_Comp)

  type t = (BasicFact.t) DF_Map.t

  (******* Generation *******)

  let empty = DF_Map.empty

  let add df b_fct =
    Config.debug (fun () ->
      try
        let _ = DF_Map.find (BasicFact.get_snd_ord_variable b_fct) df in
        Config.internal_error "[data_structure.ml >> DF.add] A basic deduction fact with the same second-order variable already exists."
      with
        | Not_found-> ()
    );

    DF_Map.add (BasicFact.get_snd_ord_variable b_fct) b_fct df

  let remove df x_snd =
    Config.debug (fun () ->
      try
        let _ = DF_Map.find x_snd df in
        ()
      with
        | Not_found -> Config.internal_error "[data_structure.ml >> DF.remove] No basic deduction fact has the variable given in argument."
    );

    DF_Map.remove x_snd df

  let apply df subst =

    let map_term df f =
      DF_Map.map (fun b_fct -> BasicFact.create (BasicFact.get_snd_ord_variable b_fct) (f (BasicFact.get_protocol_term b_fct))) df
    in
    Subst.apply subst df map_term

  let get df x =
    try
      Some(DF_Map.find x df)
    with
    | Not_found -> None

  (********* Testing ********)

  exception Out_of_type
  exception Found

  let exists_within_var_type k df f =
    try
      DF_Map.iter (fun x b_fct ->
        if Variable.type_of x <= k
        then
          if f b_fct
          then raise Found
          else ()
        else raise Out_of_type
        ) df;
      false
    with
      | Found -> true
      | Out_of_type -> false

  let find df f =
    let result = ref None in

    try
      DF_Map.iter (fun _ b_fct ->
        match f b_fct with
        | None -> ()
        | Some a -> (result := Some a; raise Found)
        ) df;
      !result
    with
      | Found -> !result

  let find_term df x_snd = match DF_Map.find_opt x_snd df with
    | None -> None
    | Some bfact -> Some(BasicFact.get_protocol_term bfact)

  let find_within_var_type k df f =
    let result = ref None in

    try
      DF_Map.iter (fun x b_fct ->
        if Variable.type_of x <= k
        then
          match f b_fct with
          | None -> ()
          | Some a -> result := Some a; raise Found
        else raise Out_of_type
        ) df;
      !result
    with
      | Found -> !result
      | Out_of_type -> None

  (********* Iterators ********)

  let fold f a df = DF_Map.fold (fun _ b_fct c -> f c b_fct) df a

  let iter df f = DF_Map.iter (fun _ b_fct -> f b_fct) df

  let display out ?(rho = None) ?(per_line = 8) ?(tab = 0) df = match out with
    | Testing ->
        if DF_Map.is_empty df
        then emptyset Testing
        else
          begin
            let s = DF_Map.cardinal df in
            let current_number = ref 1 in
            let str = ref "{ " in
            DF_Map.iter (fun _ bfct ->
              if !current_number < s
              then str := Printf.sprintf "%s%s, " !str (BasicFact.display Testing ~rho:rho bfct)
              else str := Printf.sprintf "%s%s }" !str (BasicFact.display Testing ~rho:rho bfct);

              incr current_number
            ) df;
            !str
          end
    | Latex ->
        if DF_Map.is_empty df
        then emptyset Latex
        else
          begin
            let s = DF_Map.cardinal df in
            let str = ref "\\left\\{ \\begin{array}{l} " in
            let current_number = ref 1 in
            DF_Map.iter (fun _ bfct ->
              if !current_number >= s
              then str := Printf.sprintf "%s%s \\end{array}\\right\\}" !str (BasicFact.display Latex ~rho:rho bfct)
              else if (!current_number / per_line)*per_line = !current_number
              then str := Printf.sprintf "%s%s,\\\\" !str (BasicFact.display Latex ~rho:rho bfct)
              else str := Printf.sprintf "%s%s, " !str (BasicFact.display Latex ~rho:rho bfct);

              incr current_number
            ) df;
            !str
          end
    | HTML ->
        if DF_Map.is_empty df
        then emptyset HTML
        else
          begin
            let s = DF_Map.cardinal df in
            let str = ref "<table class=\"df\"><tr><td>" in
            let current_number = ref 1 in
            DF_Map.iter (fun _ bfct ->
              if !current_number >= s
              then str := Printf.sprintf "%s%s</td></tr></table>" !str (BasicFact.display HTML ~rho:rho bfct)
              else if (!current_number / per_line)*per_line = !current_number
              then str := Printf.sprintf "%s%s,</td></tr><tr><td>" !str (BasicFact.display HTML ~rho:rho bfct)
              else str := Printf.sprintf "%s%s, " !str (BasicFact.display HTML ~rho:rho bfct);

              incr current_number
            ) df;
            !str
          end
    | _ ->
        let tab_str = create_tab tab in
        begin match DF_Map.cardinal df with
          | 0 -> "{}"
          | s when s <= per_line ->
              let str = ref "{ " in
              let current_number = ref 1 in
              DF_Map.iter (fun _ bfct ->
                if !current_number < s
                then str := Printf.sprintf "%s%s; " !str (BasicFact.display out ~rho:rho bfct)
                else str := Printf.sprintf "%s%s }" !str (BasicFact.display out ~rho:rho bfct);

                incr current_number
              ) df;
              !str
          | s ->
              let tab_str_inside = create_tab (tab+1) in
              let str = ref (Printf.sprintf "\n%s{\n%s" tab_str tab_str_inside) in
              let current_number = ref 1 in
              DF_Map.iter (fun _ bfct ->
                if !current_number >= s
                then str := Printf.sprintf "%s%s\n%s}\n" !str (BasicFact.display out ~rho:rho bfct) tab_str
                else if (!current_number / per_line)*per_line = !current_number
                then str := Printf.sprintf "%s%s,\n%s" !str (BasicFact.display out bfct) tab_str_inside
                else str := Printf.sprintf "%s%s, "!str (BasicFact.display out ~rho:rho bfct);

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
***         Subterm_consequence        ***
******************************************)

module Uniformity_Set = struct

  module Term_Comp =
  struct
    type t = protocol_term
    let compare = order Protocol
  end

  module Recipe_Comp =
  struct
    type t = recipe
    let compare = order Recipe
  end

  module Recipe_Set = Set.Make(Recipe_Comp)

  module Subterm = Map.Make(Term_Comp)

  type t =
    {
      gterm_grecipe : recipe Subterm.t;
      gterm_recipe : recipe Subterm.t;
      term_grecipe : recipe Subterm.t;
      term_recipe : recipe Subterm.t;
      multiple : Recipe_Set.t Subterm.t
    }

  (******* Display *******)

  let display out ?(rho = None) ?(per_line = 8) ?(tab = 0) uniset = match out with
    | Testing ->
        if
          Subterm.is_empty uniset.gterm_grecipe &&
          Subterm.is_empty uniset.gterm_recipe &&
          Subterm.is_empty uniset.term_grecipe &&
          Subterm.is_empty uniset.term_recipe &&
          Subterm.is_empty uniset.multiple
        then emptyset Testing
        else
          begin
            let elements = ref [] in
            Subterm.iter (fun term recipe_set ->
              Recipe_Set.iter (fun recipe ->
                elements := (recipe,term) :: !elements
              ) recipe_set
            ) uniset.multiple;
            Subterm.iter (fun term recipe -> (recipe,term) :: !elements) uniset.gterm_grecipe;
            Subterm.iter (fun term recipe -> (recipe,term) :: !elements) uniset.gterm_recipe;
            Subterm.iter (fun term recipe -> (recipe,term) :: !elements) uniset.term_recipe;
            Subterm.iter (fun term recipe -> (recipe,term) :: !elements) uniset.term_grecipe;
            let sorted_elements = List.sort (fun (r1,_) (r2,_) -> order Recipe r1 r2) !elements in

            let s = List.length sorted_elements in
            let current_number = ref 1 in
            let str = ref "{ " in
            List.iter (fun (recipe,term) ->
              if !current_number < s
              then str := Printf.sprintf "%s(%s,%s), " !str (display Testing ~rho:rho Recipe recipe) (display Testing ~rho:rho Protocol term)
              else str := Printf.sprintf "%s(%s,%s) }" !str (display Testing ~rho:rho Recipe recipe) (display Testing ~rho:rho Protocol term);

              incr current_number
            ) sorted_elements;
            !str
          end
    | Latex ->
        if
          Subterm.is_empty uniset.gterm_grecipe &&
          Subterm.is_empty uniset.gterm_recipe &&
          Subterm.is_empty uniset.term_grecipe &&
          Subterm.is_empty uniset.term_recipe &&
          Subterm.is_empty uniset.multiple
        then emptyset Latex
        else
          begin
            let s = Subterm.fold (fun _ recipe_set acc -> (Recipe_Set.cardinal recipe_set) + acc) uniset.multiple ((Subterm.cardinal uniset.gterm_grecipe) + (Subterm.cardinal uniset.gterm_recipe) + (Subterm.cardinal uniset.term_grecipe) + (Subterm.cardinal uniset.term_recipe)) in
            let str = ref "\\left\\{ \\begin{array}{l} " in
            let current_number = ref 1 in

            let f_display term recipe =
              if !current_number >= s
              then str := Printf.sprintf "%s(%s,%s) \\end{array}\\right\\}" !str (display Latex ~rho:rho Recipe recipe) (display Latex ~rho:rho Protocol term)
              else if (!current_number / per_line)*per_line = !current_number
              then str := Printf.sprintf "%s(%s,%s),\\\\" !str (display Latex ~rho:rho Recipe recipe) (display Latex ~rho:rho Protocol term)
              else str := Printf.sprintf "%s(%s,%s), " !str(display Latex ~rho:rho Recipe recipe) (display Latex ~rho:rho Protocol term);

              incr current_number
            in

            Subterm.iter (fun term recipe_set ->
              Recipe_Set.iter (fun recipe -> f_display term recipe) recipe_set
            ) uniset.multiple;
            Subterm.iter f_display uniset.gterm_grecipe;
            Subterm.iter f_display uniset.gterm_recipe;
            Subterm.iter f_display uniset.term_grecipe;
            Subterm.iter f_display uniset.term_recipe;

            !str
          end
    | HTML ->
        if
          Subterm.is_empty uniset.gterm_grecipe &&
          Subterm.is_empty uniset.gterm_recipe &&
          Subterm.is_empty uniset.term_grecipe &&
          Subterm.is_empty uniset.term_recipe &&
          Subterm.is_empty uniset.multiple
        then emptyset HTML
        else
          begin
            let s = Subterm.fold (fun _ recipe_set acc -> (Recipe_Set.cardinal recipe_set) + acc) uniset.multiple ((Subterm.cardinal uniset.gterm_grecipe) + (Subterm.cardinal uniset.gterm_recipe) + (Subterm.cardinal uniset.term_grecipe) + (Subterm.cardinal uniset.term_recipe)) in
            let str = ref "<table class=\"uniformset\"><tr><td>" in
            let current_number = ref 1 in

            let f_display term recipe =
              if !current_number >= s
              then str := Printf.sprintf "%s(%s,%s)</td></tr></table>" !str (display HTML ~rho:rho Recipe recipe) (display HTML ~rho:rho Protocol term)
              else if (!current_number / per_line)*per_line = !current_number
              then str := Printf.sprintf "%s(%s,%s),</td></tr><tr><td>" !str (display HTML ~rho:rho Recipe recipe) (display HTML ~rho:rho Protocol term)
              else str := Printf.sprintf "%s(%s,%s), " !str (display HTML ~rho:rho Recipe recipe) (display HTML ~rho:rho Protocol term);

              incr current_number
            in

            Subterm.iter (fun term recipe_set ->
              Recipe_Set.iter (fun recipe -> f_display term recipe) recipe_set
            ) uniset.multiple;
            Subterm.iter f_display uniset.gterm_grecipe;
            Subterm.iter f_display uniset.gterm_recipe;
            Subterm.iter f_display uniset.term_grecipe;
            Subterm.iter f_display uniset.term_recipe;
            !str
          end
    | _ ->
        let tab_str = create_tab tab in
        begin match Subterm.fold (fun _ recipe_set acc -> (Recipe_Set.cardinal recipe_set) + acc) uniset.multiple ((Subterm.cardinal uniset.gterm_grecipe) + (Subterm.cardinal uniset.gterm_recipe) + (Subterm.cardinal uniset.term_grecipe) + (Subterm.cardinal uniset.term_recipe)) with
          | 0 -> "{}"
          | s when s <= per_line ->
              let str = ref "{ " in
              let current_number = ref 1 in

              let f_display term recipe =
                if !current_number < s
                then str := Printf.sprintf "%s(%s,%s); " !str (display out ~rho:rho Recipe recipe) (display out ~rho:rho Protocol term)
                else str := Printf.sprintf "%s(%s,%s) }" !str (display out ~rho:rho Recipe recipe) (display out ~rho:rho Protocol term);

                incr current_number
              in

              Subterm.iter (fun term recipe_set ->
                Recipe_Set.iter (fun recipe -> f_display term recipe) recipe_set
              ) uniset.multiple;
              Subterm.iter f_display uniset.gterm_grecipe;
              Subterm.iter f_display uniset.gterm_recipe;
              Subterm.iter f_display uniset.term_grecipe;
              Subterm.iter f_display uniset.term_recipe;
              !str
          | s ->
              let tab_str_inside = create_tab (tab+1) in
              let str = ref (Printf.sprintf "\n%s{\n%s" tab_str tab_str_inside) in
              let current_number = ref 1 in

              let f_display term recipe =
                if !current_number >= s
                then str := Printf.sprintf "%s(%s,%s)\n%s}\n" !str (display out ~rho:rho Recipe recipe) (display out ~rho:rho Protocol term) tab_str
                else if (!current_number / per_line)*per_line = !current_number
                then str := Printf.sprintf "%s(%s,%s),\n%s" !str (display out ~rho:rho Recipe recipe) (display out ~rho:rho Protocol term) tab_str_inside
                else str := Printf.sprintf "%s(%s,%s), "!str (display out ~rho:rho Recipe recipe) (display out ~rho:rho Protocol term);

                incr current_number
              in

              Subterm.iter (fun term recipe_set ->
                Recipe_Set.iter (fun recipe -> f_display term recipe) recipe_set
              ) uniset.multiple;
              Subterm.iter f_display uniset.gterm_grecipe;
              Subterm.iter f_display uniset.gterm_recipe;
              Subterm.iter f_display uniset.term_grecipe;
              Subterm.iter f_display uniset.term_recipe;
              !str
        end

  (***** Generation ******)

  let empty =
    {
      gterm_grecipe = Subterm.empty;
      gterm_recipe = Subterm.empty;
      term_grecipe = Subterm.empty;
      term_recipe = Subterm.empty;
      multiple = Subterm.empty
    }

  let add uniset recipe pterm =
    try
      { uniset with multiple = Subterm.replace pterm (fun recipe_set -> Recipe_Set.add recipe recipe_set) uniset.multiple }
    with
      | Not_found ->
          let multiple_ref = ref uniset.multiple in
          let singleton = Recipe_Set.singleton recipe in

          let f_remove_test recipe' =
            let recipe_set = Recipe_Set.add recipe' singleton in
            if Recipe_Set.is_singleton recipe_set
            then false
            else (multiple_ref := Subterm.add pterm recipe_set !multiple_ref; true)
          in

          begin match is_ground pterm, is_ground recipe with
            | true,true ->
                begin try
                  let recipe', map = Subterm.remove_exception pterm uniset.gterm_recipe in
                  multiple_ref := Subterm.add pterm (Recipe_Set.add recipe' (Recipe_Set.singleton recipe)) !multiple_ref;
                  { uniset with gterm_recipe = map ; multiple = !multiple_ref }
                with Not_found ->
                  let single = Subterm.add_or_remove pterm recipe f_remove_test uniset.gterm_grecipe in
                  { uniset with multiple = !multiple_ref; gterm_grecipe = single }
                end
            | true,false ->
                begin try
                  let recipe', map = Subterm.remove_exception pterm uniset.gterm_grecipe in
                  multiple_ref := Subterm.add pterm (Recipe_Set.add recipe' (Recipe_Set.singleton recipe)) !multiple_ref;
                  { uniset with gterm_grecipe = map ; multiple = !multiple_ref }
                with Not_found ->
                  let single = Subterm.add_or_remove pterm recipe f_remove_test uniset.gterm_recipe in
                  { uniset with multiple = !multiple_ref; gterm_recipe = single }
                end
            | false, true ->
                begin try
                  let recipe', map = Subterm.remove_exception pterm uniset.term_recipe in
                  multiple_ref := Subterm.add pterm (Recipe_Set.add recipe' (Recipe_Set.singleton recipe)) !multiple_ref;
                  { uniset with term_recipe = map ; multiple = !multiple_ref }
                with Not_found ->
                  let single = Subterm.add_or_remove pterm recipe f_remove_test uniset.term_grecipe in
                  { uniset with multiple = !multiple_ref; term_grecipe = single }
                end
            | false, false ->
                begin try
                  let recipe', map = Subterm.remove_exception pterm uniset.term_grecipe in
                  multiple_ref := Subterm.add pterm (Recipe_Set.add recipe' (Recipe_Set.singleton recipe)) !multiple_ref;
                  { uniset with term_grecipe = map ; multiple = !multiple_ref }
                with Not_found ->
                  let single = Subterm.add_or_remove pterm recipe f_remove_test uniset.term_recipe in
                  { uniset with multiple = !multiple_ref; term_recipe = single }
                end
          end

  let map_recipe uniset f =
    let gterm_grecipe_ref = ref uniset.gterm_grecipe
    and term_grecipe_ref = ref uniset.term_grecipe in

    let gterm_recipe_ref = ref
      (Subterm.map_or_remove f (fun pterm recipe ->
        if is_ground recipe
        then (gterm_grecipe_ref := Subterm.add pterm recipe !gterm_grecipe_ref; true)
        else false
      ) uniset.gterm_recipe)
    in
    let term_recipe_ref = ref
      (Subterm.map_or_remove f (fun pterm recipe ->
        if is_ground recipe
        then (term_grecipe_ref := Subterm.add pterm recipe !term_grecipe_ref; true)
        else false
      ) uniset.term_recipe)
    in

    let multiple =
      Subterm.map_or_remove (Recipe_Set.map f) (fun pterm recipe_set ->
        if Recipe_Set.is_singleton recipe_set
        then
          let recipe = Recipe_Set.choose_optimised recipe_set in
          match is_ground pterm, is_ground recipe with
            | true,true -> gterm_grecipe_ref := Subterm.add pterm recipe !gterm_grecipe_ref; true
            | true,false -> gterm_recipe_ref := Subterm.add pterm recipe !gterm_recipe_ref; true
            | false,true -> term_grecipe_ref := Subterm.add pterm recipe !term_grecipe_ref; true
            | false, false -> term_recipe_ref := Subterm.add pterm recipe !term_recipe_ref; true
        else false
      ) uniset.multiple
    in

    {
      gterm_grecipe = !gterm_grecipe_ref;
      gterm_recipe = !gterm_recipe_ref;
      term_grecipe = !term_grecipe_ref;
      term_recipe = !term_recipe_ref;
      multiple = multiple
    }

  let map_protocol uniset f =
    let gterm_grecipe = ref uniset.gterm_grecipe in
    let gterm_recipe = ref uniset.gterm_recipe in
    let term_grecipe = ref Subterm.empty in
    let term_recipe = ref Subterm.empty in
    let multiple = ref Subterm.empty in

    let try_add_in_multi pterm recipe f_next =
      try
        multiple := Subterm.replace pterm (fun recipe_set -> Recipe_Set.add recipe recipe_set) !multiple
      with
        | Not_found -> f_next ()
    in

    let check_in_opposite pterm recipe map_ref f_next =
      try
        let recipe', map = Subterm.remove_exception pterm !map_ref in
        multiple := Subterm.add pterm (Recipe_Set.add recipe' (Recipe_Set.singleton recipe)) !multiple;
        map_ref := map
      with
        | Not_found -> f_next ()
    in

    let f_remove_test pterm recipe_1 recipe_2 =
      let recipe_set = Recipe_Set.add recipe_2 (Recipe_Set.singleton recipe_1) in
      if Recipe_Set.is_singleton recipe_set
      then false
      else (multiple := Subterm.add pterm recipe_set !multiple; true)
    in

    Subterm.iter (fun pterm recipe ->
      let pterm' = f pterm in

      try_add_in_multi pterm' recipe (fun () ->
        if is_ground pterm'
        then
          check_in_opposite pterm' recipe gterm_recipe (fun () ->
            gterm_grecipe := Subterm.add_or_remove pterm' recipe (f_remove_test pterm' recipe) !gterm_grecipe
          )
        else
          check_in_opposite pterm' recipe term_recipe (fun () ->
            term_grecipe := Subterm.add_or_remove pterm' recipe (f_remove_test pterm' recipe) !term_grecipe
          )
      )
    ) uniset.term_grecipe;

    Subterm.iter (fun pterm recipe ->
      let pterm' = f pterm in

      try_add_in_multi pterm' recipe (fun () ->
        if is_ground pterm'
        then
          check_in_opposite pterm' recipe gterm_grecipe (fun () ->
            gterm_recipe := Subterm.add_or_remove pterm' recipe (f_remove_test pterm' recipe) !gterm_recipe
          )
        else
          check_in_opposite pterm' recipe term_grecipe (fun () ->
            term_recipe := Subterm.add_or_remove pterm' recipe (f_remove_test pterm' recipe) !term_recipe
          )
      )
    ) uniset.term_recipe;

    let check_map map_ref pterm recipe_set f_next =
      try
        let recipe, map = Subterm.remove_exception pterm !map_ref in
        map_ref := map;
        multiple := Subterm.add pterm (Recipe_Set.add recipe recipe_set) !multiple
      with
        | Not_found -> f_next ()
    in

    Subterm.iter (fun pterm recipe_set ->
      let pterm' = f pterm in
      if is_ground pterm'
      then
        check_map gterm_recipe pterm' recipe_set (fun () ->
          check_map gterm_grecipe pterm' recipe_set (fun () ->
            multiple := Subterm.add_or_replace pterm' recipe_set (fun recipe_set' -> Recipe_Set.union recipe_set' recipe_set) !multiple
          )
        )
      else
        check_map term_recipe pterm' recipe_set (fun () ->
          check_map term_grecipe pterm' recipe_set (fun () ->
            multiple := Subterm.add_or_replace pterm' recipe_set (fun recipe_set' -> Recipe_Set.union recipe_set' recipe_set) !multiple
          )
        )
    ) uniset.multiple;

    {
      gterm_grecipe = !gterm_grecipe;
      gterm_recipe = !gterm_recipe;
      term_grecipe = !term_grecipe;
      term_recipe = !term_recipe;
      multiple = !multiple
    }

  let map_protocol_recipe uniset f_protocol f_recipe =
    let gterm_grecipe = ref uniset.gterm_grecipe in

    let term_grecipe = ref Subterm.empty in
    let term_recipe = ref Subterm.empty in
    let multiple = ref Subterm.empty in

    let gterm_recipe = ref
      (Subterm.map_or_remove f_recipe (fun pterm recipe ->
        if is_ground recipe
        then (gterm_grecipe := Subterm.add pterm recipe !gterm_grecipe; true)
        else false
      ) uniset.gterm_recipe)
    in

    let try_add_in_multi pterm recipe f_next =
      try
        multiple := Subterm.replace pterm (fun recipe_set -> Recipe_Set.add recipe recipe_set) !multiple
      with
        | Not_found -> f_next ()
    in

    let check_in_opposite pterm recipe map_ref f_next =
      try
        let recipe', map = Subterm.remove_exception pterm !map_ref in
        multiple := Subterm.add pterm (Recipe_Set.add recipe' (Recipe_Set.singleton recipe)) !multiple;
        map_ref := map
      with
        | Not_found -> f_next ()
    in

    let f_remove_test pterm recipe_1 recipe_2 =
      let recipe_set = Recipe_Set.add recipe_2 (Recipe_Set.singleton recipe_1) in
      if Recipe_Set.is_singleton recipe_set
      then false
      else (multiple := Subterm.add pterm recipe_set !multiple; true)
    in

    Subterm.iter (fun pterm recipe ->
      let pterm' = f_protocol pterm in

      try_add_in_multi pterm' recipe (fun () ->
        if is_ground pterm'
        then
          check_in_opposite pterm' recipe gterm_recipe (fun () ->
            gterm_grecipe := Subterm.add_or_remove pterm' recipe (f_remove_test pterm' recipe) !gterm_grecipe
          )
        else
          check_in_opposite pterm' recipe term_recipe (fun () ->
            term_grecipe := Subterm.add_or_remove pterm' recipe (f_remove_test pterm' recipe) !term_grecipe
          )
      )
    ) uniset.term_grecipe;

    Subterm.iter (fun pterm recipe ->
      let pterm' = f_protocol pterm in
      let recipe' = f_recipe recipe in

      try_add_in_multi pterm' recipe' (fun () ->
        match is_ground pterm', is_ground recipe' with
          | true, true ->
              check_in_opposite pterm' recipe' gterm_recipe (fun () ->
                gterm_grecipe := Subterm.add_or_remove pterm' recipe' (f_remove_test pterm' recipe') !gterm_grecipe
              )
          | true, false ->
              check_in_opposite pterm' recipe' gterm_grecipe (fun () ->
                gterm_recipe := Subterm.add_or_remove pterm' recipe' (f_remove_test pterm' recipe') !gterm_recipe
              )
          | false, true ->
              check_in_opposite pterm' recipe' term_recipe (fun () ->
                term_grecipe := Subterm.add_or_remove pterm' recipe' (f_remove_test pterm' recipe') !term_grecipe
              )
          | false, false ->
              check_in_opposite pterm' recipe' term_grecipe (fun () ->
                term_recipe := Subterm.add_or_remove pterm' recipe' (f_remove_test pterm' recipe') !term_recipe
              )
      )
    ) uniset.term_recipe;

    let check_map map_ref pterm recipe_set f_next =
      try
        let recipe, map = Subterm.remove_exception pterm !map_ref in
        map_ref := map;
        multiple := Subterm.add pterm (Recipe_Set.add recipe recipe_set) !multiple
      with
      | Not_found -> f_next ()
    in

    Subterm.iter (fun pterm recipe_set ->
      let pterm' = f_protocol pterm in
      let recipe_set' = Recipe_Set.map f_recipe recipe_set in

      if Recipe_Set.is_singleton recipe_set'
      then
        let recipe = Recipe_Set.choose_optimised recipe_set' in

        try_add_in_multi pterm' recipe (fun () ->
          match is_ground pterm' , is_ground recipe with
            | true,true ->
                check_in_opposite pterm' recipe gterm_recipe (fun () ->
                  gterm_grecipe := Subterm.add_or_remove pterm' recipe (f_remove_test pterm' recipe) !gterm_grecipe
                )
            | true, false ->
                check_in_opposite pterm' recipe gterm_grecipe (fun () ->
                  gterm_recipe := Subterm.add_or_remove pterm' recipe (f_remove_test pterm' recipe) !gterm_recipe
                )
            | false, true ->
                check_in_opposite pterm' recipe term_recipe (fun () ->
                  term_grecipe := Subterm.add_or_remove pterm' recipe (f_remove_test pterm' recipe) !term_grecipe
                )
            | false, false ->
                check_in_opposite pterm' recipe term_grecipe (fun () ->
                  term_recipe := Subterm.add_or_remove pterm' recipe (f_remove_test pterm' recipe) !term_recipe
                )
        )
      else
        if is_ground pterm'
        then
          check_map gterm_recipe pterm' recipe_set' (fun () ->
            check_map gterm_grecipe pterm' recipe_set' (fun () ->
              multiple := Subterm.add_or_replace pterm' recipe_set' (fun recipe_set'' -> Recipe_Set.union recipe_set'' recipe_set') !multiple
            )
          )
        else
          check_map term_recipe pterm' recipe_set' (fun () ->
            check_map term_grecipe pterm' recipe_set' (fun () ->
              multiple := Subterm.add_or_replace pterm' recipe_set' (fun recipe_set'' -> Recipe_Set.union recipe_set'' recipe_set') !multiple
            )
          )
    ) uniset.multiple;

    {
      gterm_grecipe = !gterm_grecipe;
      gterm_recipe = !gterm_recipe;
      term_grecipe = !term_grecipe;
      term_recipe = !term_recipe;
      multiple = !multiple
    }

  let apply uniset subst_snd subst_fst = match Subst.is_identity subst_fst, Subst.is_identity subst_snd with
    | true, true -> uniset
    | true, false -> Subst.apply subst_snd uniset map_recipe
    | false, true -> Subst.apply subst_fst uniset map_protocol
    | false, false -> Subst.apply_both subst_fst subst_snd uniset map_protocol_recipe

  (******* Iterators ********)

  let iter uniset f =
    Subterm.iter (fun term recipe_set ->
      Recipe_Set.iter (fun recipe -> f recipe term) recipe_set
    ) uniset.multiple;
    Subterm.iter (fun term recipe -> f recipe term) uniset.gterm_grecipe;
    Subterm.iter (fun term recipe -> f recipe term) uniset.gterm_recipe;
    Subterm.iter (fun term recipe -> f recipe term) uniset.term_grecipe;
    Subterm.iter (fun term recipe -> f recipe term) uniset.term_recipe

  (******* Testing ********)

  let exists_recipes_deducing_same_protocol_term uniset = Subterm.is_empty uniset.multiple

  let exists uniset recipe term =
    if is_ground term
    then
      match Subterm.find_opt term uniset.gterm_grecipe with
        | None ->
            begin match Subterm.find_opt term uniset.gterm_recipe with
              | None ->
                  begin match Subterm.find_opt term uniset.multiple with
                    | None -> false
                    | Some r_set -> Recipe_Set.exists (is_equal Recipe recipe) r_set
                  end
              | Some r -> is_equal Recipe recipe r
            end
        | Some r -> is_equal Recipe recipe r
    else
      match Subterm.find_opt term uniset.term_grecipe with
        | None ->
            begin match Subterm.find_opt term uniset.term_recipe with
              | None ->
                  begin match Subterm.find_opt term uniset.multiple with
                    | None -> false
                    | Some r_set -> Recipe_Set.exists (is_equal Recipe recipe) r_set
                  end
              | Some r -> is_equal Recipe recipe r
            end
        | Some r -> is_equal Recipe recipe r

  let find_protocol_term uniset pterm =
    if is_ground pterm
    then
      match Subterm.find_opt pterm uniset.gterm_grecipe with
        | None ->
            begin match Subterm.find_opt pterm uniset.gterm_recipe with
              | None ->
                  begin match Subterm.find_opt pterm uniset.multiple with
                    | None -> None
                    | Some set_recipe -> Some (Recipe_Set.choose_optimised set_recipe)
                  end
              | r -> r
            end
        | r -> r
    else
      match Subterm.find_opt pterm uniset.term_grecipe with
        | None ->
            begin match Subterm.find_opt pterm uniset.term_recipe with
              | None ->
                  begin match Subterm.find_opt pterm uniset.multiple with
                    | None -> None
                    | Some set_recipe -> Some (Recipe_Set.choose_optimised set_recipe)
                  end
              | r -> r
            end
        | r -> r

  type uniformity_check =
    | Not_uniform
    | Uniform
    | Substitution of (snd_ord, axiom) Subst.t * t

  let unify_recipes_deducing_same_protocol_term uniset =
    Config.debug (fun () ->
      Subterm.iter (fun _ set_recipe ->
        if Recipe_Set.is_singleton set_recipe || Recipe_Set.is_empty set_recipe
        then Config.internal_error "[data_structure.ml >> unify_multiple_opt] There should not be singletons or empty sets."
      ) uniset.multiple
    );
    if Subterm.is_empty uniset.multiple
    then Uniform
    else
      begin
        let list_of_equations = ref [] in

        Subterm.iter (fun _ set_recipe ->
          Recipe_Set.choose_and_apply (fun r1 r2 -> list_of_equations := (r1,r2) :: !list_of_equations) set_recipe
        ) uniset.multiple;

        try
          let subst = Subst.unify_recipe !list_of_equations in
          Config.debug (fun () ->
            if Subst.is_identity subst
            then Config.internal_error "[data_structure.ml >> unify_multiple_opt] The substitution can't be the identity."
          );
          let new_uniset =
            Subst.apply subst uniset (fun uni f ->
              let gterm_grecipe_ref = ref uni.gterm_grecipe
              and term_grecipe_ref = ref uni.term_grecipe
              and gterm_recipe_ref = ref (Subterm.map f uni.gterm_recipe)
              and term_recipe_ref = ref (Subterm.map f uni.term_recipe) in

              Subterm.iter (fun pterm recipe_set ->
                let recipe = f (Recipe_Set.choose recipe_set) in
                match is_ground pterm, is_ground recipe with
                  | true, true -> gterm_grecipe_ref := Subterm.add pterm recipe !gterm_grecipe_ref
                  | true, false -> gterm_recipe_ref := Subterm.add pterm recipe !gterm_recipe_ref
                  | false, true -> term_grecipe_ref := Subterm.add pterm recipe !term_grecipe_ref
                  | false, false -> term_recipe_ref := Subterm.add pterm recipe !term_recipe_ref
              ) uni.multiple;

              {
                gterm_grecipe = !gterm_grecipe_ref;
                gterm_recipe = !gterm_recipe_ref;
                term_grecipe = !term_grecipe_ref;
                term_recipe = !term_recipe_ref;
                multiple = Subterm.empty
              }
            )
          in
          Substitution (subst,new_uniset)
        with
          | Subst.Not_unifiable -> Not_uniform
      end
end

(*****************************************
***                Tools               ***
******************************************)

module Tools = Tools_Subterm(SDF)(DF)(Uniformity_Set)(Eq.Mixed)
