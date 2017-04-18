open Term
open Display

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
      protocol_ground : bool
    }

  type cell_ground =
    {
      g_var_type : int;
      g_fact : Fact.deduction
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

  let first_entry sdf =
    try
      let id,cell = SDF_Map.min_binding sdf.map_ground in
      cell.g_fact, id
    with
      | Not_found -> Config.internal_error "[Data_structure.ml >> first_entry] Should not apply first entry on an empty SDF."


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
              then (SDF_Map.add i { g_var_type = cell.var_type; g_fact = Fact.create_deduction_fact (Fact.get_recipe cell.fact) t } acc_map_ground, acc_map)
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
              then (SDF_Map.add i { g_var_type = cell.var_type; g_fact = Fact.create_deduction_fact (Fact.get_recipe cell.fact) t } acc_map_ground, acc_map, acc_last_entry_ground || i = sdf.size)
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
              then (SDF_Map.add i { g_var_type = cell.var_type; g_fact = Fact.create_deduction_fact t (Fact.get_protocol_term cell.fact) } acc_map_ground, acc_map)
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
              then (SDF_Map.add i { g_var_type = cell.var_type; g_fact = Fact.create_deduction_fact t (Fact.get_protocol_term cell.fact) } acc_map_ground, acc_map, acc_last_entry_ground || i = sdf.size)
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
                  then (SDF_Map.add i { g_var_type = cell.var_type; g_fact = Fact.create_deduction_fact t (Fact.get_protocol_term cell.fact) } acc_map_ground, acc_map)
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
                  then (SDF_Map.add i { g_var_type = cell.var_type; g_fact = Fact.create_deduction_fact t (Fact.get_protocol_term cell.fact) } acc_map_ground, acc_map, acc_last_entry_ground || i = sdf.size)
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
              then (SDF_Map.add i { g_var_type = cell.var_type; g_fact = Fact.create_deduction_fact t (Fact.get_protocol_term cell.fact) } acc_map_ground, acc_map)
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
              then (SDF_Map.add i { g_var_type = cell.var_type; g_fact = Fact.create_deduction_fact t (Fact.get_protocol_term cell.fact) } acc_map_ground, acc_map, acc_last_entry_ground || i = sdf.size)
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
        map_ground = SDF_Map.add new_size ({ g_var_type = k; g_fact = fct }) sdf.map_ground;
        all_id = new_size::sdf.all_id;
        last_entry_ground = true
      }
    else
      {
        sdf with
        size = new_size;
        map = SDF_Map.add new_size ({ var_type = k; fact = fct ; protocol_ground = protocol_ground; recipe_ground = recipe_ground}) sdf.map;
        all_id = new_size::sdf.all_id;
        last_entry_ground = false
      }

  let display out ?(rho = None) ?(per_line = 8) ?(tab = 0) sdf = match out with
    | Testing ->
        if SDF_Map.is_empty sdf.map
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
            !str
          end
    | Latex ->
        if SDF_Map.is_empty sdf.map
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
            !str
          end
    | HTML ->
        if SDF_Map.is_empty sdf.map
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
      DF_Map.iter (fun _ b_fct -> match f b_fct with
        | None -> ()
        | Some a -> result := Some a; raise Found
        ) df;
      !result
    with
      | Found -> !result

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

  module Int_Comp =
  struct
    type t = id_recipe_equivalent
    let compare = compare
  end

  module UF_Map = Map.Make(Int_Comp)

  type equality_type =
    | Constructor_SDF of id_recipe_equivalent * symbol
    | Equality_SDF of id_recipe_equivalent * id_recipe_equivalent
    | Consequence_UF of id_recipe_equivalent

  type cell_equality =
    {
      equality : Fact.equality_formula;
      eq_type : equality_type
    }

  type t =
    {
      solved_ded_formula : (id_recipe_equivalent * Fact.deduction_formula) option;
      unsolved_ded_formula : (id_recipe_equivalent * Fact.deduction_formula list) option;

      solved_eq_formula : cell_equality UF_Map.t;
      unsolved_eq_formula : cell_equality UF_Map.t
    }

  (******** Generation ********)

  let empty =
    {
      solved_ded_formula = None;
      unsolved_ded_formula = None;

      solved_eq_formula = UF_Map.empty;
      unsolved_eq_formula = UF_Map.empty
    }

  let add_equality uf form id eq_type =
    Config.debug (fun () ->
      if UF_Map.mem id uf.solved_eq_formula || UF_Map.mem id uf.unsolved_eq_formula
      then Config.internal_error "[Data_structure.ml >> add_equality] The id recipe equivalent is already in the set UF"
      );

    if Fact.is_solved form
    then { uf with solved_eq_formula = UF_Map.add id { equality = form ; eq_type = eq_type } uf.solved_eq_formula }
    else { uf with unsolved_eq_formula = UF_Map.add id { equality = form ; eq_type = eq_type } uf.unsolved_eq_formula }

  let add_deduction uf form_list id =
    Config.debug (fun () ->
      if uf.solved_ded_formula <> None || uf.unsolved_ded_formula <> None
      then Config.internal_error "[Data_structure.ml >> add_deduction] Some deduction formula is already in UF.";

      if form_list = []
      then Config.internal_error "[Data_structure.ml >> add_deduction] The list of deduction formulas given as argument should not be empty."
      );

    try
      let solved_form = List.find Fact.is_solved form_list in
      { uf with solved_ded_formula = Some (id, solved_form) }
    with
      | Not_found -> { uf with unsolved_ded_formula = Some (id, form_list) }

  let filter (type a) (fct: a Fact.t) uf (f: a Fact.formula -> bool) = match fct with
    | Fact.Deduction ->
        begin match uf.solved_ded_formula, uf.unsolved_ded_formula with
          | Some _, Some _ -> Config.internal_error "[Data_structure.ml >> UF.filter] There can't be deduction facts at the same time solved and unsolved."
          | Some (_,form), None when not (f form) -> { uf with solved_ded_formula = None }
          | None, Some (id,form_list) ->
              let result = List.filter f form_list in
              if result = []
              then { uf with unsolved_ded_formula = None }
              else { uf with unsolved_ded_formula = Some (id, result) }
          | _, _ -> uf
        end
    | Fact.Equality ->
        { uf with
          solved_eq_formula = UF_Map.filter (fun _ cell -> f cell.equality) uf.solved_eq_formula;
          unsolved_eq_formula = UF_Map.filter (fun _ cell -> f cell.equality) uf.unsolved_eq_formula
        }

  let exists_solved (type a) (fct: a Fact.t) uf (f: a Fact.formula -> bool) = match fct with
    | Fact.Deduction ->
        begin match uf.solved_ded_formula with
          | Some (_,form) -> f form
          | None -> false
        end
    | Fact.Equality -> UF_Map.exists (fun _ cell -> f cell.equality) uf.solved_eq_formula

  let choose_solved (type a) (fct: a Fact.t) uf = match fct with
    | Fact.Deduction ->
        begin match uf.solved_ded_formula with
          | Some (id,form) -> ((id,form): id_recipe_equivalent * a Fact.formula)
          | None -> raise Not_found
        end
    | Fact.Equality ->
        let (id,cell) = UF_Map.choose uf.solved_eq_formula in
        ((id,cell.equality): id_recipe_equivalent * a Fact.formula)

  let choose_unsolved (type a) (fct: a Fact.t) uf = match fct with
    | Fact.Deduction ->
        begin match uf.unsolved_ded_formula with
          | Some (_, []) -> Config.internal_error "[Data_structure.ml >> UF.choose_unsolved] The list should not be empty."
          | Some (id,form_list) -> ((id,List.hd form_list): id_recipe_equivalent * a Fact.formula)
          | None -> raise Not_found
        end
    | Fact.Equality ->
        let (id,cell) = UF_Map.choose uf.unsolved_eq_formula in
        ((id,cell.equality): id_recipe_equivalent * a Fact.formula)

  let get_eq_type_solved uf id =
    let cell = UF_Map.find id uf.solved_eq_formula in
    cell.eq_type

  let remove_solved_id (type a) (fct: a Fact.t) uf id = match fct with
    | Fact.Deduction ->
        begin match uf.solved_ded_formula with
          | None -> raise Not_found
          | Some(id', _) when id = id' ->  { uf with solved_ded_formula = None }
          | _ -> Config.internal_error "[Data_structure.ml >> remove_solved_id] There is already a solved deduction formula in UF with a recipe equivalent id than the one given as argument"
        end
    | Fact.Equality ->
        if UF_Map.mem id uf.solved_eq_formula
        then { uf with solved_eq_formula = UF_Map.remove id uf.solved_eq_formula }
        else raise Not_found

  let iter_solved_deduction_id  uf f = match uf.solved_ded_formula with
    | None -> ()
    | Some(id,form) -> f id form

  let iter_solved_equality_id uf f =
    UF_Map.iter (fun id cell -> f id cell.equality cell.eq_type) uf.solved_eq_formula

  let iter (type a) (fct:a Fact.t) uf (f:a Fact.formula -> unit) = match fct with
    | Fact.Deduction ->
        begin match uf.solved_ded_formula, uf.unsolved_ded_formula with
          | None, None -> ()
          | Some(_,form),None -> f form
          | None, Some(_,form_l) -> List.iter f form_l
          | Some(_,form), Some(_,form_l) -> f form; List.iter f form_l
        end
    | Fact.Equality ->
        UF_Map.iter (fun _ cell -> f cell.equality) uf.solved_eq_formula;
        UF_Map.iter (fun _ cell -> f cell.equality) uf.unsolved_eq_formula

  let is_unsolved (type a) (fct: a Fact.t) uf id = match fct with
    | Fact.Deduction ->
        begin match uf.unsolved_ded_formula with
          | None -> false
          | Some(_,[]) -> Config.internal_error "[Data_structure.ml >> is_unsolved_id] The list should not be empty"
          | Some(id',_) when id = id' -> true
          | _ -> Config.internal_error "[Data_structure.ml >> is_unsolved_id] There is already an unsolved deduction formula in UF with a recipe equivalent id than the one given as argument"
        end
    | Fact.Equality -> UF_Map.exists (fun id' _ -> id = id') uf.unsolved_eq_formula

  let is_solved (type a) (fct: a Fact.t) uf id = match fct with
    | Fact.Deduction ->
        begin match uf.solved_ded_formula with
          | None -> false
          | Some(id',_) when id = id' -> true
          | _ -> Config.internal_error "[Data_structure.ml >> is_solved_id] There is already a solved deduction formula in UF with a recipe equivalent id than the one given as argument"
        end
    | Fact.Equality -> UF_Map.exists (fun id' _ -> id = id') uf.solved_eq_formula

  exception Solved_ded of Fact.deduction_formula
  exception Solved_eq of Fact.equality_formula

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

        let new_solved_ded_formula, new_unsolved_ded_formula = match uf.solved_ded_formula, uf.unsolved_ded_formula with
          | None, None -> None, None
          | Some _, Some _ -> Config.internal_error "[Data_structure.ml >> UF.apply] There can't be deduction facts at the same time solved and unsolved."
          | Some (id,form), None ->
              Config.debug (fun () ->
                try
                  let _ = apply_subst_on_ded_formula form in
                  ()
                with
                  | Fact.Bot -> Config.internal_error "[Data_structure.ml >> UF.apply] Applying a substitution on a solved formula should not result into bot."
              );

              Some (id, apply_subst_on_ded_formula form), None
          | None, Some(id, form_list) ->
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
                  then None, None
                  else None, Some (id,!result_list)
                with
                  | Solved_ded form -> Some (id, form), None
              end
        in

        let filter_function = ref (fun _ -> false) in
        let additional_solved_eq_formula = ref UF_Map.empty in

        let new_unsolved_eq_formula =
          UF_Map.mapi (fun id cell ->
            try
              let form_1 = apply_subst_on_eq_formula cell.equality in
              if Fact.is_solved form_1
              then raise (Solved_eq form_1)
              else { cell with equality = form_1 }
            with
              | Fact.Bot -> filter_function := (fun x -> id = x || !filter_function x); cell
              | Solved_eq form ->
                  filter_function := (fun x -> id = x || !filter_function x);
                  additional_solved_eq_formula := UF_Map.add id { cell with equality = form} !additional_solved_eq_formula;
                  { cell with equality = form }
            ) uf.unsolved_eq_formula
        in

        let new_unsolved_eq_formula_1 = UF_Map.filter (fun x _ -> not (!filter_function x)) new_unsolved_eq_formula in

        let new_solved_eq_formula =
          UF_Map.merge (fun _ old_solved new_solved -> match old_solved,new_solved with
            | Some _, Some _ -> Config.internal_error "[Data_structure.ml >> UF.apply] The two maps should have disjoints keys.(2)"
            | None, Some cell -> Some cell
            | Some cell, None ->
                Config.debug (fun () ->
                  try
                    let _ = apply_subst_on_eq_formula cell.equality in
                    ()
                  with
                    | Fact.Bot -> Config.internal_error "[Data_structure.ml >> UF.apply] Applying a substitution on a solved formula should not result into bot.(2)"
                );

                Some ({cell with equality = apply_subst_on_eq_formula cell.equality })
            | None, None -> None
            ) uf.solved_eq_formula !additional_solved_eq_formula
        in

        Config.debug(fun () ->
          if UF_Map.cardinal uf.solved_eq_formula + UF_Map.cardinal !additional_solved_eq_formula <> UF_Map.cardinal new_solved_eq_formula
          then Config.internal_error "[Data_structure.ml >> UF.apply] The sum of the two sets is not a real sum."
        );

        {
          solved_ded_formula = new_solved_ded_formula;
          solved_eq_formula = new_solved_eq_formula;
          unsolved_ded_formula = new_unsolved_ded_formula;
          unsolved_eq_formula = new_unsolved_eq_formula_1
        }
      end

  let display_equality_type = function
    | Constructor_SDF (id,f) -> Printf.sprintf "_Const(%d,%s)" id (Symbol.display Testing f)
    | Equality_SDF(id1,id2) -> Printf.sprintf "_Equa(%d,%d)" id1 id2
    | Consequence_UF(id) -> Printf.sprintf "_Conseq(%d)" id

  let display_cell_equality rho (id,cell) =
    Printf.sprintf "(%d,%s,%s)"
      id
      (Fact.display_formula Testing ~rho:rho Fact.Equality cell.equality)
      (display_equality_type cell.eq_type)

  let display_deduction_formula rho (id,ded_for_list) =
    Printf.sprintf "(%d,[%s])" id (display_list (fun form -> Printf.sprintf "(%s)" (Fact.display_formula Testing ~rho:rho Fact.Deduction form)) ";" ded_for_list)

  let gather_deduction_formula uf = match uf.solved_ded_formula, uf.unsolved_ded_formula with
    | None, None -> []
    | Some(id,form), None -> [(id,[form])]
    | None, Some(id,form_l) -> [(id,form_l)]
    | Some(id,form), Some(id',form_l) -> [(id,[form]); (id',form_l)]

  let pretty_gather_deduction_formula uf = match uf.solved_ded_formula, uf.unsolved_ded_formula with
    | None, None -> []
    | Some(_,form), None -> [form]
    | None, Some(_,form_l) -> form_l
    | Some(_,form), Some(_,form_l) -> form::form_l

  let gather_equality_formula uf =
    (UF_Map.bindings uf.solved_eq_formula)@(UF_Map.bindings uf.unsolved_eq_formula)

  let display out ?(rho = None) ?(per_line = 3) ?(tab = 0) uf = match out with
    | Testing -> Printf.sprintf "{{%s}{%s}}"
        (display_list (display_deduction_formula rho) "" (gather_deduction_formula uf))
        (display_list (display_cell_equality rho) "" (gather_equality_formula uf))
    | Latex ->
        let ded_formula_list = pretty_gather_deduction_formula uf
        and eq_formula_list = gather_equality_formula uf in
        let s = (List.length ded_formula_list) + (List.length eq_formula_list) in
        if s = 0
        then emptyset Latex
        else
          begin
            let str = ref "\\left\\{ \\begin{array}{l} " in
            let current_number = ref 1 in
            List.iter (fun form ->
              if !current_number >= s
              then str := Printf.sprintf "%s%s \\end{array}\\right\\}" !str (Fact.display_formula Latex ~rho:rho Fact.Deduction form)
              else if (!current_number / per_line)*per_line = !current_number
              then str := Printf.sprintf "%s%s,\\\\" !str (Fact.display_formula Latex ~rho:rho Fact.Deduction form)
              else str := Printf.sprintf "%s%s,  " !str (Fact.display_formula Latex ~rho:rho Fact.Deduction form);

              incr current_number
            ) ded_formula_list;
            List.iter (fun (_,cell) ->
              if !current_number >= s
              then str := Printf.sprintf "%s%s \\end{array}\\right\\}" !str (Fact.display_formula Latex ~rho:rho Fact.Equality cell.equality)
              else if (!current_number / per_line)*per_line = !current_number
              then str := Printf.sprintf "%s%s,\\\\" !str (Fact.display_formula Latex ~rho:rho Fact.Equality cell.equality)
              else str := Printf.sprintf "%s%s,  " !str (Fact.display_formula Latex ~rho:rho Fact.Equality cell.equality);

              incr current_number
            ) eq_formula_list;
            !str
          end
    | HTML ->
        let ded_formula_list = pretty_gather_deduction_formula uf
        and eq_formula_list = gather_equality_formula uf in
        let s = (List.length ded_formula_list) + (List.length eq_formula_list) in
        if s = 0
        then emptyset HTML
        else
          begin
            let str = ref "<table class=\"uf\"><tr><td>" in
            let current_number = ref 1 in
            List.iter (fun form ->
              if !current_number >= s
              then str := Printf.sprintf "%s%s</td></tr></table>" !str (Fact.display_formula HTML ~rho:rho Fact.Deduction form)
              else if (!current_number / per_line)*per_line = !current_number
              then str := Printf.sprintf "%s%s,</td></tr><tr><td>" !str (Fact.display_formula HTML ~rho:rho Fact.Deduction form)
              else str := Printf.sprintf "%s%s, " !str (Fact.display_formula HTML ~rho:rho Fact.Deduction form);

              incr current_number
            ) ded_formula_list;
            List.iter (fun (_,cell) ->
              if !current_number >= s
              then str := Printf.sprintf "%s%s</td></tr></table>" !str (Fact.display_formula HTML ~rho:rho Fact.Equality cell.equality)
              else if (!current_number / per_line)*per_line = !current_number
              then str := Printf.sprintf "%s%s,</td></tr><tr><td>" !str (Fact.display_formula HTML ~rho:rho Fact.Equality cell.equality)
              else str := Printf.sprintf "%s%s, " !str (Fact.display_formula HTML ~rho:rho Fact.Equality cell.equality);

              incr current_number
            ) eq_formula_list;
            !str
          end
    | _ ->
        let ded_formula_list = pretty_gather_deduction_formula uf
        and eq_formula_list = gather_equality_formula uf in
        let tab_str = create_tab tab in
        begin match (List.length ded_formula_list) + (List.length eq_formula_list) with
          | 0 -> "{}"
          | s when s <= per_line ->
              let str = ref "{ " in
              let current_number = ref 1 in
              List.iter (fun form ->
                if !current_number < s
                then str := Printf.sprintf "%s%s; " !str (Fact.display_formula out ~rho:rho Fact.Deduction form)
                else str := Printf.sprintf "%s%s }" !str (Fact.display_formula out ~rho:rho Fact.Deduction form);

                incr current_number
              ) ded_formula_list;
              List.iter (fun (_,cell) ->
                if !current_number < s
                then str := Printf.sprintf "%s%s; " !str (Fact.display_formula out ~rho:rho Fact.Equality cell.equality)
                else str := Printf.sprintf "%s%s }" !str (Fact.display_formula out ~rho:rho Fact.Equality cell.equality);

                incr current_number
              ) eq_formula_list;
              !str
          | s ->
              let tab_str_inside = create_tab (tab+1) in
              let str = ref (Printf.sprintf "\n%s{\n%s" tab_str tab_str_inside) in
              let current_number = ref 1 in
              List.iter (fun form ->
                if !current_number >= s
                then str := Printf.sprintf "%s%s\n%s}\n" !str (Fact.display_formula out ~rho:rho Fact.Deduction form) tab_str
                else if (!current_number / per_line)*per_line = !current_number
                then str := Printf.sprintf "%s%s,\n%s" !str (Fact.display_formula out ~rho:rho Fact.Deduction form) tab_str_inside
                else str := Printf.sprintf "%s%s, "!str (Fact.display_formula out ~rho:rho Fact.Deduction form);

                incr current_number
              ) ded_formula_list;
              List.iter (fun (_,cell) ->
                if !current_number >= s
                then str := Printf.sprintf "%s%s\n%s}\n" !str (Fact.display_formula out ~rho:rho Fact.Equality cell.equality) tab_str
                else if (!current_number / per_line)*per_line = !current_number
                then str := Printf.sprintf "%s%s,\n%s" !str (Fact.display_formula out ~rho:rho Fact.Equality cell.equality) tab_str_inside
                else str := Printf.sprintf "%s%s, "!str (Fact.display_formula out ~rho:rho Fact.Equality cell.equality);

                incr current_number
              ) eq_formula_list;
              !str
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

  type t = Recipe_Set.t Subterm.t

  (***** Generation ******)

  let empty = Subterm.empty

  let add subc recipe pterm =
    try
      let set_recipe = Subterm.find pterm subc in
      let set_recipe' = Recipe_Set.add recipe set_recipe in
      Subterm.add pterm set_recipe' subc
    with
      | Not_found -> Subterm.add pterm (Recipe_Set.singleton recipe) subc

  let map_recipe subc f =
    Subterm.map (fun set_recipe ->
      Recipe_Set.fold (fun r acc_set ->
        Recipe_Set.add (f r) acc_set
        ) set_recipe Recipe_Set.empty
      ) subc

  let map_protocol_term subc f =
    Subterm.fold (fun pterm set_recipe acc_map ->
      let pterm' = f pterm in
      try
        let set_recipe_acc = Subterm.find pterm' acc_map in
        let set_recipe_acc' = Recipe_Set.union set_recipe_acc set_recipe in
        Subterm.add pterm' set_recipe_acc' acc_map
      with
        | Not_found -> Subterm.add pterm' set_recipe acc_map
      ) subc Subterm.empty

  let apply subc subst_snd subst_fst =
    let snd_applied =
      if Subst.is_identity subst_snd
      then subc
      else Subst.apply subst_snd subc map_recipe
    in

    if Subst.is_identity subst_fst
    then snd_applied
    else Subst.apply subst_fst snd_applied map_protocol_term

  (******* Iterators ********)

  let iter uniset f =
    Subterm.iter (fun term recipe_set ->
      Recipe_Set.iter (fun recipe -> f recipe term) recipe_set
    ) uniset

  (******* Testing ********)

  exception Found

  let find_protocol_term subc pterm f =
    try
      let set_recipe = Subterm.find pterm subc in

      let result = ref None in
      begin try
        Recipe_Set.iter (fun recipe ->
          if f recipe
          then
            begin
              result := Some recipe;
              raise Found
            end
          ) set_recipe;
        None
      with
        | Found -> !result
      end
    with
      | Not_found -> None

  let exists_pair_with_same_protocol_term subc f =
    Subterm.exists (fun _ set_recipe ->
      Recipe_Set.exists (fun r1 ->
        let bigger = ref false in
        try
          Recipe_Set.iter (fun r2 ->
            if !bigger
            then
              if f r1 r2 then raise Found else ()
            else
              if order Recipe r1 r2 < 0
              then
                begin
                  bigger := true;
                  if f r1 r2 then raise Found
                end
              else ()
            ) set_recipe;
          false
        with
          | Found -> true
        ) set_recipe
      ) subc

  (******* Display *******)

  let display out ?(rho = None) ?(per_line = 8) ?(tab = 0) uniset = match out with
    | Testing ->
        if Subterm.is_empty uniset
        then emptyset Testing
        else
          begin
            let elements = ref [] in
            Subterm.iter (fun term recipe_set ->
              Recipe_Set.iter (fun recipe ->
                elements := (recipe,term) :: !elements
              ) recipe_set
            ) uniset;
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
        if Subterm.is_empty uniset
        then emptyset Latex
        else
          begin
            let s = Subterm.fold (fun _ recipe_set acc -> (Recipe_Set.cardinal recipe_set) + acc) uniset 0 in
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
            ) uniset;
            !str
          end
    | HTML ->
        if Subterm.is_empty uniset
        then emptyset HTML
        else
          begin
            let s = Subterm.fold (fun _ recipe_set acc -> (Recipe_Set.cardinal recipe_set) + acc) uniset 0 in
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
            ) uniset;
            !str
          end
    | _ ->
        let tab_str = create_tab tab in
        begin match Subterm.fold (fun _ recipe_set acc -> (Recipe_Set.cardinal recipe_set) + acc) uniset 0 with
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
              ) uniset;
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
              ) uniset;
              !str
        end
end

(*****************************************
***                Tools               ***
******************************************)

module Tools = Tools_Subterm(SDF)(DF)(Uniformity_Set)
