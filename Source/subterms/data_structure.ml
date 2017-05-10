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
        let id,cell = SDF_Map.max_binding sdf.map_ground in
        cell.g_fact, id
      else
        let id,cell = SDF_Map.max_binding sdf.map in
        cell.fact, id
    with
      | Not_found -> Config.internal_error "[Data_structure.ml >> last_entry] Should not apply last entry on an empty SDF."

  let last_entry_id sdf =
    if sdf.size = 0
    then Config.internal_error "[Data_structure.ml >> last_entry] Should not apply last_entry_id on an empty SDF."
    else sdf.size

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

  let add sdf fct =
    Config.debug (fun () ->
      let recipe = Fact.get_recipe fct in
      let k = get_type recipe in

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

    let k = get_type r in
    let recipe_ground = is_ground r
    and protocol_ground = is_ground t in
    let new_size = sdf.size + 1 in
    if recipe_ground && protocol_ground
    then
      { sdf with
        size = new_size;
        map_ground = SDF_Map.add new_size ({ g_var_type = k; g_fact = fct; g_marked_uniset = false }) sdf.map_ground;
        all_id = new_size::sdf.all_id;
        last_entry_ground = true;
      }
    else
      {
        sdf with
        size = new_size;
        map = SDF_Map.add new_size ({ var_type = k; fact = fct ; protocol_ground = protocol_ground; recipe_ground = recipe_ground; marked_uniset = false}) sdf.map;
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
    | DedSolved of Fact.deduction_formula
    | DedUnsolved of Fact.deduction_formula list
    | DedNone

  type state_eq_form =
    | EqSolved of Fact.equality_formula
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

  let add_equality uf form =
    Config.debug (fun () ->
      if uf.eq_formula <> EqNone
      then Config.internal_error "[Data_structure.ml >> add_equality] There is already an equality formula in UF."
      );

    if Fact.is_solved form
    then { uf with eq_formula = EqSolved form }
    else { uf with eq_formula = EqUnsolved form }

  let add_deduction uf form_list =
    Config.debug (fun () ->
      if uf.ded_formula <> DedNone
      then Config.internal_error "[Data_structure.ml >> add_deduction] There is already a deduction formula in UF.";

      if form_list = []
      then Config.internal_error "[Data_structure.ml >> add_deduction] The list of deduction formulas given as argument should not be empty."
      );

    try
      let solved_form = List.find Fact.is_solved form_list in
      { uf with ded_formula = DedSolved solved_form }
    with
      | Not_found -> { uf with ded_formula = DedUnsolved form_list }

  let remove_solved (type a) (fct: a Fact.t) uf = match fct with
    | Fact.Deduction ->
        { uf with ded_formula = DedNone }
    | Fact.Equality ->
        { uf with eq_formula = EqNone }

  let remove_unsolved_equality uf =
    Config.debug (fun () ->
      match uf.eq_formula with
        | EqUnsolved _ -> ()
        | _ -> Config.internal_error "[data_structure.ml >> UF.remove_usolved] UF should contain an unsolved equality formula."
    );
    { uf with eq_formula = EqNone }

  let filter (type a) (fct: a Fact.t) uf (f: a Fact.formula -> bool) = match fct with
    | Fact.Deduction ->
        begin match uf.ded_formula with
          | DedNone -> uf
          | DedSolved form when f form -> uf
          | DedSolved _ -> { uf with ded_formula = DedNone }
          | DedUnsolved form_list ->
              let result = List.filter_unordered f form_list in
              if result = []
              then { uf with ded_formula = DedNone }
              else { uf with ded_formula = DedUnsolved result }
        end
    | Fact.Equality ->
        begin match uf.eq_formula with
          | EqNone -> uf
          | EqSolved form when f form -> uf
          | EqUnsolved form  when f form -> uf
          | _ -> { uf with eq_formula = EqNone }
        end

  let solved_occurs (type a) (fct: a Fact.t) uf = match fct with
    | Fact.Deduction ->
        begin match uf.ded_formula with
          | DedSolved _ -> true
          | _ -> false
        end
    | Fact.Equality ->
        begin match uf.eq_formula with
          | EqSolved _ -> true
          | _ -> false
        end

  let unsolved_occurs (type a) (fct: a Fact.t) uf = match fct with
    | Fact.Deduction ->
        begin match uf.ded_formula with
          | DedUnsolved _ -> true
          | _ -> false
        end
    | Fact.Equality ->
        begin match uf.eq_formula with
          | EqUnsolved _ -> true
          | _ -> false
        end

  let choose_solved (type a) (fct: a Fact.t) uf = match fct with
    | Fact.Deduction ->
        begin match uf.ded_formula with
          | DedSolved form -> (form:a Fact.formula)
          | _ -> raise Not_found
        end
    | Fact.Equality ->
        begin match uf.eq_formula with
          | EqSolved form -> (form: a Fact.formula)
          | _ -> raise Not_found
        end

  let choose_solved_option (type a) (fct: a Fact.t) uf = match fct with
    | Fact.Deduction ->
        begin match uf.ded_formula with
          | DedSolved form -> ((Some form):a Fact.formula option )
          | _ -> None
        end
    | Fact.Equality ->
        begin match uf.eq_formula with
          | EqSolved form -> ((Some form): a Fact.formula option)
          | _ -> None
        end

  let choose_unsolved_option (type a) (fct: a Fact.t) uf = match fct with
    | Fact.Deduction ->
        begin match uf.ded_formula with
          | DedUnsolved [] -> Config.internal_error "[Data_structure.ml >> UF.choose_unsolved] The list should not be empty."
          | DedUnsolved form_list -> (Some (List.hd form_list): a Fact.formula option)
          | _ -> None
        end
    | Fact.Equality ->
        begin match uf.eq_formula with
          | EqUnsolved form -> ((Some form): a Fact.formula option)
          | _ -> None
        end

  let iter (type a) (fct:a Fact.t) uf (f:a Fact.formula -> unit) = match fct with
    | Fact.Deduction ->
        begin match uf.ded_formula with
          | DedNone -> ()
          | DedUnsolved [] -> Config.internal_error "[Data_structure.ml >> UF.iter] The list should not be empty."
          | DedUnsolved form_list -> List.iter f form_list
          | DedSolved form -> f form
        end
    | Fact.Equality ->
        begin match uf.eq_formula with
          | EqNone -> ()
          | EqSolved form | EqUnsolved form -> f form
        end

  exception Solved_ded of Fact.deduction_formula

  let apply uf subst_snd subst_fst =
    let fst_identity = Subst.is_identity subst_fst
    and snd_identity = Subst.is_identity subst_snd in

    if fst_identity && snd_identity
    then uf
    else
      begin
        let apply_subst_on_ded_formula, apply_subst_on_eq_formula = match fst_identity, snd_identity with
          | false, false ->
              (fun (form: Fact.deduction Fact.formula) -> Fact.apply Fact.Deduction form subst_snd subst_fst),
              (fun (form: Fact.equality Fact.formula) -> Fact.apply Fact.Equality form subst_snd subst_fst)
          | false, true ->
              (fun (form: Fact.deduction Fact.formula) -> Fact.apply_fst_ord Fact.Deduction form subst_fst),
              (fun (form: Fact.equality Fact.formula) -> Fact.apply_fst_ord Fact.Equality form subst_fst)
          | true, false ->
              (fun (form: Fact.deduction Fact.formula) -> Fact.apply_snd_ord Fact.Deduction form subst_snd),
              (fun (form: Fact.equality Fact.formula) -> Fact.apply_snd_ord Fact.Equality form subst_snd)
          | true, true -> Config.internal_error "[data_structure.ml >> apply] Impossible case"
        in

        let new_ded_formula = match uf.ded_formula with
          | DedNone -> DedNone
          | DedSolved form ->
              Config.debug (fun () ->
                try
                  let _ = apply_subst_on_ded_formula form in
                  ()
                with
                  | Fact.Bot -> Config.internal_error "[Data_structure.ml >> UF.apply] Applying a substitution on a solved formula should not result into bot."
              );

              DedSolved (apply_subst_on_ded_formula form)
          | DedUnsolved form_list ->
              begin
                let result_list = ref [] in

                try
                  List.iter (fun form ->
                    try
                      let form_1 = apply_subst_on_ded_formula form in
                      if Fact.is_solved form_1
                      then raise (Solved_ded form_1)
                      else result_list := form_1 :: !result_list
                    with
                      | Fact.Bot -> ()
                    ) form_list;

                  if !result_list = []
                  then DedNone
                  else DedUnsolved !result_list
                with
                  | Solved_ded form -> DedSolved form
              end
        in

        let new_eq_formula = match uf.eq_formula with
          | EqNone -> EqNone
          | EqSolved form ->
              Config.debug (fun () ->
                try
                  let _ = apply_subst_on_eq_formula form in
                  ()
                with
                  | Fact.Bot -> Config.internal_error "[Data_structure.ml >> UF.apply] Applying a substitution on a solved formula should not result into bot.(2)"
              );

              EqSolved(apply_subst_on_eq_formula form)
          | EqUnsolved form ->
              begin
                try
                  let form_1 = apply_subst_on_eq_formula form in
                  if Fact.is_solved form_1
                  then EqSolved form_1
                  else EqUnsolved form_1
                with
                  | Fact.Bot -> EqNone
              end
        in

        { ded_formula = new_ded_formula ; eq_formula = new_eq_formula }
      end

  let gather_deduction_formula uf = match uf.ded_formula with
    | DedNone -> []
    | DedSolved form -> [form]
    | DedUnsolved form_list -> form_list

  let gather_equality_formula uf = match uf.eq_formula with
    | EqNone -> []
    | EqSolved form | EqUnsolved form -> [form]

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

  let test_implies (type a) (type b) (at:(a,b) atom) (form: (a,b) t) (term1:(a,b) term) (term2:(a,b) term) (res:bool) = match at with
    | Protocol -> !test_implies_Protocol form term1 term2 res
    | Recipe -> !test_implies_Recipe form term1 term2 res

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

  let implies at form t1 t2 =
    try
      let subst = Subst.unify at [(t1,t2)] in

      let res = apply at form subst = Bot in
      Config.test (fun () -> test_implies at form t1 t2 res);
      res
    with
      | Subst.Not_unifiable ->
          Config.test (fun () -> test_implies at form t1 t2 true);
          true

  let extract = function
    | Top -> None, Top
    | Bot -> None, Bot
    | Conj [] -> Config.internal_error "[data_structure.ml >> DF.extract] The list should not be empty"
    | Conj [diseq] -> Some diseq, Top
    | Conj (diseq::q) -> Some diseq, Conj q

  let display out ?(rho=None) at = function
    | Top -> Display.top out
    | Bot -> Display.bot out
    | Conj diseq_list -> Display.display_list (Diseq.display out ~rho:rho at) (Printf.sprintf " %s " (Display.wedge out)) diseq_list

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
      single : recipe Subterm.t;
      multiple : Recipe_Set.t Subterm.t
    }

  (******* Display *******)

  let display out ?(rho = None) ?(per_line = 8) ?(tab = 0) uniset = match out with
    | Testing ->
        if Subterm.is_empty uniset.single && Subterm.is_empty uniset.multiple
        then emptyset Testing
        else
          begin
            let elements = ref [] in
            Subterm.iter (fun term recipe_set ->
              Recipe_Set.iter (fun recipe ->
                elements := (recipe,term) :: !elements
              ) recipe_set
            ) uniset.multiple;
            Subterm.iter (fun term recipe -> (recipe,term) :: !elements) uniset.single;
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
        if Subterm.is_empty uniset.single && Subterm.is_empty uniset.multiple
        then emptyset Latex
        else
          begin
            let s = Subterm.fold (fun _ recipe_set acc -> (Recipe_Set.cardinal recipe_set) + acc) uniset.multiple (Subterm.cardinal uniset.single) in
            let str = ref "\\left\\{ \\begin{array}{l} " in
            let current_number = ref 1 in
            Subterm.iter (fun term recipe_set ->
              Recipe_Set.iter (fun recipe ->
                if !current_number >= s
                then str := Printf.sprintf "%s(%s,%s) \\end{array}\\right\\}" !str (display Latex ~rho:rho Recipe recipe) (display Latex ~rho:rho Protocol term)
                else if (!current_number / per_line)*per_line = !current_number
                then str := Printf.sprintf "%s(%s,%s),\\\\" !str (display Latex ~rho:rho Recipe recipe) (display Latex ~rho:rho Protocol term)
                else str := Printf.sprintf "%s(%s,%s), " !str(display Latex ~rho:rho Recipe recipe) (display Latex ~rho:rho Protocol term);

                incr current_number
              ) recipe_set
            ) uniset.multiple;
            Subterm.iter (fun term recipe ->
              if !current_number >= s
              then str := Printf.sprintf "%s(%s,%s) \\end{array}\\right\\}" !str (display Latex ~rho:rho Recipe recipe) (display Latex ~rho:rho Protocol term)
              else if (!current_number / per_line)*per_line = !current_number
              then str := Printf.sprintf "%s(%s,%s),\\\\" !str (display Latex ~rho:rho Recipe recipe) (display Latex ~rho:rho Protocol term)
              else str := Printf.sprintf "%s(%s,%s), " !str(display Latex ~rho:rho Recipe recipe) (display Latex ~rho:rho Protocol term);

              incr current_number
            ) uniset.single;
            !str
          end
    | HTML ->
        if Subterm.is_empty uniset.single && Subterm.is_empty uniset.multiple
        then emptyset HTML
        else
          begin
            let s = Subterm.fold (fun _ recipe_set acc -> (Recipe_Set.cardinal recipe_set) + acc) uniset.multiple (Subterm.cardinal uniset.single) in
            let str = ref "<table class=\"uniformset\"><tr><td>" in
            let current_number = ref 1 in
            Subterm.iter (fun term recipe_set ->
              Recipe_Set.iter (fun recipe ->
                if !current_number >= s
                then str := Printf.sprintf "%s(%s,%s)</td></tr></table>" !str (display HTML ~rho:rho Recipe recipe) (display HTML ~rho:rho Protocol term)
                else if (!current_number / per_line)*per_line = !current_number
                then str := Printf.sprintf "%s(%s,%s),</td></tr><tr><td>" !str (display HTML ~rho:rho Recipe recipe) (display HTML ~rho:rho Protocol term)
                else str := Printf.sprintf "%s(%s,%s), " !str (display HTML ~rho:rho Recipe recipe) (display HTML ~rho:rho Protocol term);

                incr current_number
              ) recipe_set
            ) uniset.multiple;
            Subterm.iter (fun term recipe ->
              if !current_number >= s
              then str := Printf.sprintf "%s(%s,%s)</td></tr></table>" !str (display HTML ~rho:rho Recipe recipe) (display HTML ~rho:rho Protocol term)
              else if (!current_number / per_line)*per_line = !current_number
              then str := Printf.sprintf "%s(%s,%s),</td></tr><tr><td>" !str (display HTML ~rho:rho Recipe recipe) (display HTML ~rho:rho Protocol term)
              else str := Printf.sprintf "%s(%s,%s), " !str (display HTML ~rho:rho Recipe recipe) (display HTML ~rho:rho Protocol term);

              incr current_number
            ) uniset.single;
            !str
          end
    | _ ->
        let tab_str = create_tab tab in
        begin match Subterm.fold (fun _ recipe_set acc -> (Recipe_Set.cardinal recipe_set) + acc) uniset.multiple (Subterm.cardinal uniset.single) with
          | 0 -> "{}"
          | s when s <= per_line ->
              let str = ref "{ " in
              let current_number = ref 1 in
              Subterm.iter (fun term recipe_set ->
                Recipe_Set.iter (fun recipe ->
                  if !current_number < s
                  then str := Printf.sprintf "%s(%s,%s); " !str (display out ~rho:rho Recipe recipe) (display out ~rho:rho Protocol term)
                  else str := Printf.sprintf "%s(%s,%s) }" !str (display out ~rho:rho Recipe recipe) (display out ~rho:rho Protocol term);

                  incr current_number
                ) recipe_set
              ) uniset.multiple;
              Subterm.iter (fun term recipe ->
                if !current_number < s
                then str := Printf.sprintf "%s(%s,%s); " !str (display out ~rho:rho Recipe recipe) (display out ~rho:rho Protocol term)
                else str := Printf.sprintf "%s(%s,%s) }" !str (display out ~rho:rho Recipe recipe) (display out ~rho:rho Protocol term);

                incr current_number
              ) uniset.single;
              !str
          | s ->
              let tab_str_inside = create_tab (tab+1) in
              let str = ref (Printf.sprintf "\n%s{\n%s" tab_str tab_str_inside) in
              let current_number = ref 1 in
              Subterm.iter (fun term recipe_set ->
                Recipe_Set.iter (fun recipe ->
                  if !current_number >= s
                  then str := Printf.sprintf "%s(%s,%s)\n%s}\n" !str (display out ~rho:rho Recipe recipe) (display out ~rho:rho Protocol term) tab_str
                  else if (!current_number / per_line)*per_line = !current_number
                  then str := Printf.sprintf "%s(%s,%s),\n%s" !str (display out ~rho:rho Recipe recipe) (display out ~rho:rho Protocol term) tab_str_inside
                  else str := Printf.sprintf "%s(%s,%s), "!str (display out ~rho:rho Recipe recipe) (display out ~rho:rho Protocol term);

                  incr current_number
                ) recipe_set
              ) uniset.multiple;
              Subterm.iter (fun term recipe ->
                  if !current_number >= s
                  then str := Printf.sprintf "%s(%s,%s)\n%s}\n" !str (display out ~rho:rho Recipe recipe) (display out ~rho:rho Protocol term) tab_str
                  else if (!current_number / per_line)*per_line = !current_number
                  then str := Printf.sprintf "%s(%s,%s),\n%s" !str (display out ~rho:rho Recipe recipe) (display out ~rho:rho Protocol term) tab_str_inside
                  else str := Printf.sprintf "%s(%s,%s), "!str (display out ~rho:rho Recipe recipe) (display out ~rho:rho Protocol term);

                  incr current_number
              ) uniset.single;
              !str
        end

  (***** Generation ******)

  let empty =
    {
      single = Subterm.empty;
      multiple = Subterm.empty
    }

  let add uniset recipe pterm =
    try
      let recipe_single = Subterm.find pterm uniset.single in
      if is_equal Recipe recipe_single recipe
      then uniset
      else
        { single = Subterm.remove pterm uniset.single; multiple = Subterm.add pterm (Recipe_Set.of_list [recipe; recipe_single]) uniset.multiple }
    with
      | Not_found -> { uniset with multiple = Subterm.add_or_replace pterm (Recipe_Set.singleton recipe) (fun set_recipe -> Recipe_Set.add recipe set_recipe) uniset.multiple }

  let map_recipe uniset f =
    let single =  ref (Subterm.map (fun r -> f r) uniset.single) in
    let multiple = ref Subterm.empty in

    Subterm.iter (fun pterm set_recipe ->
      let set_recipe' =
        Recipe_Set.fold (fun r acc_set ->
          Recipe_Set.add (f r) acc_set
          ) set_recipe Recipe_Set.empty
      in
      if Recipe_Set.is_singleton set_recipe'
      then single := Subterm.add pterm (Recipe_Set.choose_optimised set_recipe') !single
      else multiple := Subterm.add pterm set_recipe' !multiple
    ) uniset.multiple;

    { single = !single; multiple = !multiple }

  let map_protocol_term uniset f =
    let single = ref Subterm.empty
    and multiple = ref Subterm.empty in

    Subterm.iter (fun pterm recipe_single ->
      let pterm' = f pterm in
      try
        let recipe_single',single' = Subterm.remove_exception pterm' !single in
        single := single';
        multiple := Subterm.add pterm' (Recipe_Set.of_list [recipe_single'; recipe_single]) !multiple
      with
        | Not_found -> single := Subterm.add pterm' recipe_single !single
    ) uniset.single;

    Subterm.iter (fun pterm recipe_set ->
      let pterm' = f pterm in
      try
        let recipe_single',single' = Subterm.remove_exception pterm' !single in
        single := single';
        multiple := Subterm.add pterm' (Recipe_Set.add recipe_single' recipe_set) !multiple
      with
        | Not_found -> multiple := Subterm.add_or_replace pterm' recipe_set (fun recipe_set' -> Recipe_Set.union recipe_set' recipe_set) !multiple
    ) uniset.multiple;

    { single = !single; multiple = !multiple }

  let apply uniset subst_snd subst_fst =
    let snd_applied =
      if Subst.is_identity subst_snd
      then uniset
      else Subst.apply subst_snd uniset map_recipe
    in

    if Subst.is_identity subst_fst
    then snd_applied
    else Subst.apply subst_fst snd_applied map_protocol_term

  (******* Iterators ********)

  let iter uniset f =
    Subterm.iter (fun term recipe_set ->
      Recipe_Set.iter (fun recipe -> f recipe term) recipe_set
    ) uniset.multiple;
    Subterm.iter (fun term recipe -> f recipe term) uniset.single

  (******* Testing ********)

  let exists uniset recipe term = match Subterm.find_opt term uniset.single with
    | None ->
        begin match Subterm.find_opt term uniset.multiple with
          | None -> false
          | Some r_set -> Recipe_Set.exists (is_equal Recipe recipe) r_set
        end
    | Some r -> is_equal Recipe recipe r

  let find_protocol_term uniset pterm =
    try
      let recipe = Subterm.find pterm uniset.single in
      Some recipe
    with
      | Not_found ->
          begin try
            let set_recipe = Subterm.find pterm uniset.multiple in
            Some (Recipe_Set.choose_optimised set_recipe)
          with
            | Not_found -> None
          end

  let find_protocol_term_within_multiple uniset pterm f =
    try
      let set_recipe = Subterm.find pterm uniset.multiple in
      Recipe_Set.find_option f set_recipe
    with
      | Not_found -> None

  let exists_pair_with_same_protocol_term uniset f =
    Subterm.exists (fun _ set_recipe ->
      Recipe_Set.exists_distinct_pair f set_recipe
      ) uniset.multiple


end

(*****************************************
***                Tools               ***
******************************************)

module Tools = Tools_Subterm(SDF)(DF)(Uniformity_Set)
