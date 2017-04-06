open Term

(************************
***       SDF      ***
*************************)

type id_recipe_equivalent = int

let accumulator_id_recipe_equivalent = ref 0

let fresh_id_recipe_equivalent () =
  accumulator_id_recipe_equivalent := !accumulator_id_recipe_equivalent + 1;
  !accumulator_id_recipe_equivalent

let is_equal_id_recipe_equivalent id1 id2 = id1 = id2

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
      fact : Fact.deduction
    }

  type t =
    {
      size : int;
      map : cell SDF_Map.t
    }

  (******* Access ********)

  let cardinal sdf = sdf.size

  let last_entry sdf =
    try
      let id,cell = SDF_Map.max_binding sdf.map in
      cell.fact, id
    with
      | Not_found -> Config.internal_error "[Data_structure.ml >> last_entry] Should not apply last entry on an empty SDF."

  let last_entry_id sdf =
    if sdf.size = 0
    then Config.internal_error "[Data_structure.ml >> last_entry] Should not apply last_entry_id on an empty SDF."
    else sdf.size

  let all_id sdf =
    let rec make_list = function
      | 0 -> []
      | n -> n::(make_list (n-1))
    in
    make_list sdf.size

  let get sdf id =
    try
      let cell = SDF_Map.find id sdf.map in
      cell.fact
    with
      | Not_found -> Config.internal_error "[Data_structure.ml >> get] There is no deduction fact in SDF with this recipe equivalent id."

  (******* Iterators ********)

  exception Out_of_type

  let iter sdf f =
    SDF_Map.iter (fun _ cell -> f cell.fact) sdf.map

  let iter_id sdf f =
    SDF_Map.iter (fun id cell -> f id cell.fact) sdf.map

  let iter_within_var_type k sdf f =
    try
      SDF_Map.iter (fun _ cell ->
        if cell.var_type > k
        then raise Out_of_type
        else f cell.fact
        ) sdf.map;
    with
    | Out_of_type -> ()

  let map_protocol_term sdf_map f =
    SDF_Map.map (fun cell ->
      {cell with fact = Fact.create_deduction_fact (Fact.get_recipe cell.fact) (f (Fact.get_protocol_term cell.fact)) }
    ) sdf_map

  let map_recipe sdf_map f =
    SDF_Map.map (fun cell ->
      {cell with fact = Fact.create_deduction_fact (f (Fact.get_recipe cell.fact)) (Fact.get_protocol_term cell.fact) }
    ) sdf_map

  let apply sdf subst_snd subst_fst =
    let sdf_1 = Subst.apply subst_snd sdf.map map_recipe in
    { sdf with map = Subst.apply subst_fst sdf_1 map_protocol_term }

  (******* Testing ********)

  exception Found

  let exists sdf f =
    SDF_Map.exists (fun _ cell -> f cell.fact) sdf.map

  let exists_within_var_type k sdf f =
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

      !result
    with
    | Found -> !result

  (******* Basic operations *********)

  let empty = { size = 0 ; map = SDF_Map.empty }

  let add sdf fct =
    Config.debug (fun () ->
      let recipe = Fact.get_recipe fct in
      let k = get_type recipe in

      let vars_snd = get_vars Recipe recipe in

      if List.exists (fun v -> k = Variable.type_of v) vars_snd
      then Config.internal_error "[data_structure.ml >> SDF.add] The added deduction fact have a second-order variable with the same type as the recipe itself";

      try
        let (_,cell_max) = SDF_Map.max_binding sdf.map in
        if cell_max.var_type > k
        then Config.internal_error "[data_structure.ml >> SDF.add] The added deduction fact have stricly smaller variable type than some deduction fact of SDF.";
      with
        | Not_found -> ()
    );

    let k = get_type (Fact.get_recipe fct) in
    { size = sdf.size + 1 ; map = SDF_Map.add (sdf.size + 1) ({ var_type = k; fact = fct }) sdf.map }

  let display ?(per_line = 5) out sdf =
    (* Will need to do something special about HTML and LaTeX but will do it latex *)

    let current_number = ref 1 in

    match sdf.size with
      | 0 -> "[ ]"
      | s when s <= per_line ->
          let str = ref "[ " in
          SDF_Map.iter (fun _ cell ->
            if !current_number < s
            then str := !str ^ (Fact.display_deduction_fact out cell.fact) ^ "; "
            else str := !str ^ (Fact.display_deduction_fact out cell.fact) ^ " ]";

            current_number := !current_number + 1
          ) sdf.map;
          !str
      | s ->
          let str = ref "\n[\n     " in
          SDF_Map.iter (fun _ cell ->
            if !current_number >= s
            then str:= !str ^ (Fact.display_deduction_fact out  cell.fact) ^ "\n]"
            else if (!current_number / per_line)*per_line = !current_number
            then str := !str ^ (Fact.display_deduction_fact out cell.fact) ^ ";\n     "
            else str := !str ^ (Fact.display_deduction_fact out cell.fact) ^ "; ";

            current_number := !current_number + 1
          ) sdf.map;
          !str
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

  let display ?(per_line = 5) out df =
    (* Will need to do something special about HTML and LaTeX but will do it latex *)

    let current_number = ref 1 in

    match DF_Map.cardinal df with
      | 0 -> "[ ]"
      | s when s <= per_line ->
          let str = ref "[ " in
          DF_Map.iter (fun _ b_fct ->
            if !current_number < s
            then str := !str ^ (BasicFact.display out b_fct) ^ "; "
            else str := !str ^ (BasicFact.display out b_fct) ^ " ]";

            current_number := !current_number + 1
          ) df;
          !str
      | s ->
          let str = ref "\n[\n     " in
          DF_Map.iter (fun _ b_fct ->
            if !current_number >= s
            then str:= !str ^ (BasicFact.display out b_fct) ^ "\n]"
            else if (!current_number / per_line)*per_line = !current_number
            then str := !str ^ (BasicFact.display out b_fct) ^ ";\n     "
            else str := !str ^ (BasicFact.display out b_fct) ^ "; ";

            current_number := !current_number + 1
          ) df;
          !str
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

    let new_solved_ded_formula, new_unsolved_ded_formula = match uf.solved_ded_formula, uf.unsolved_ded_formula with
      | None, None -> None, None
      | Some _, Some _ -> Config.internal_error "[Data_structure.ml >> UF.apply] There can't be deduction facts at the same time solved and unsolved."
      | Some (id,form), None ->
          Config.debug (fun () ->
            try
              let _ = Fact.apply Fact.Deduction form subst_snd subst_fst in
              ()
            with
              | Fact.Bot -> Config.internal_error "[Data_structure.ml >> UF.apply] Applying a substitution on a solved formula should not result into bot."
          );

          Some (id, Fact.apply Fact.Deduction form subst_snd subst_fst), None
      | None, Some(id, form_list) ->
          begin
            let result_list = ref [] in

            try
              List.iter (fun form ->
                try
                  let form_1 = Fact.apply Fact.Deduction form subst_snd subst_fst in
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
          let form_1 = Fact.apply Fact.Equality cell.equality subst_snd subst_fst in
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
                let _ = Fact.apply Fact.Equality cell.equality subst_snd subst_fst in
                ()
              with
                | Fact.Bot -> Config.internal_error "[Data_structure.ml >> UF.apply] Applying a substitution on a solved formula should not result into bot.(2)"
            );

            Some ({cell with equality = Fact.apply Fact.Equality cell.equality subst_snd subst_fst })
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

  let display ?(per_line = 5) ?(recipe_equivalent_id = false) ?(equality_type = false) ?(split_solved = false) out uf =
    (* Will need to do something special about HTML and LaTeX but will do it latex *)

    let current_number = ref 1 in
    let s_max = ref 0 in
    let str = ref "" in

    let display_ded id ded =
      if recipe_equivalent_id
      then Printf.sprintf "%s %s with id = %d %s" (Display.lbrace out) (Fact.display_formula out Fact.Deduction  ded) id (Display.rbrace out)
      else Fact.display_formula out Fact.Deduction ded
    in

    let display_eq_type = function
      | Constructor_SDF (id,f) -> Printf.sprintf "Constructor(%d,%s)" id (Symbol.display out f)
      | Equality_SDF(id1,id2) -> Printf.sprintf "Equality(%d,%d)" id1 id2
      | Consequence_UF(id) -> Printf.sprintf "Consequence(%d)" id
    in

    let display_eq id cell = match recipe_equivalent_id, equality_type with
      | false, false -> Fact.display_formula out Fact.Equality  cell.equality
      | true, false -> Printf.sprintf "%s %s with id = %d %s" (Display.lbrace out) (Fact.display_formula out Fact.Equality cell.equality) id (Display.rbrace out)
      | true, true -> Printf.sprintf "%s %s with id = %d and type = %s %s" (Display.lbrace out) (Fact.display_formula out Fact.Equality cell.equality) id (display_eq_type cell.eq_type) (Display.rbrace out)
      | _, _ -> Printf.sprintf "%s %s with type = %s %s" (Display.lbrace out) (Fact.display_formula out Fact.Equality cell.equality) (display_eq_type cell.eq_type) (Display.rbrace out)
    in

    let display_below dis =
      if !current_number < !s_max
      then str := !str ^ dis ^ "; "
      else str := !str ^ dis ^ " " ^ (Display.rcurlybracket out);

      current_number := !current_number + 1
    in

    let display_above dis =
      if !current_number >= !s_max
      then str:= !str ^ dis ^ "\n" ^ (Display.rcurlybracket out)
      else if (!current_number / per_line)*per_line = !current_number
      then str := !str ^ dis ^ ";\n     "
      else str := !str ^ dis ^ "; ";

      current_number := !current_number + 1
    in

    if split_solved
    then
      begin
      (* Solved *)
      s_max := UF_Map.cardinal uf.solved_eq_formula + (if uf.solved_ded_formula = None then 0 else 1);

      let str_solved =
        if !s_max = 0
        then Printf.sprintf "Solved = %s %s" (Display.lcurlybracket out) (Display.rcurlybracket out)
        else if !s_max <= per_line
        then
          let _ = str := (Printf.sprintf "Solved = %s " (Display.lcurlybracket out)) in

          let _ = match uf.solved_ded_formula with
            | None -> ()
            | Some(id,ded) -> display_below (display_ded id ded)
          in
          let _ = UF_Map.iter (fun id cell -> display_below (display_eq id cell)) uf.solved_eq_formula in

          !str
        else
          let _ = str := (Printf.sprintf "\n%s\n     " (Display.lcurlybracket out)) in

          let _ = match uf.solved_ded_formula with
            | None -> ()
            | Some(id,ded) -> display_above (display_ded id ded)
          in
          let _ = UF_Map.iter (fun id cell -> display_above (display_eq id cell)) uf.solved_eq_formula in

          !str
      in

      (* UnSolved *)
      s_max := UF_Map.cardinal uf.unsolved_eq_formula + (match uf.unsolved_ded_formula with None -> 0 | Some(_,l) -> List.length l);
      current_number := 1;

      let str_unsolved =
        if !s_max = 0
        then Printf.sprintf "Unsolved = %s %s" (Display.lcurlybracket out) (Display.rcurlybracket out)
        else if !s_max <= per_line
        then
          let _ = str := (Printf.sprintf "Unsolved = %s " (Display.lcurlybracket out)) in

          let _ = match uf.unsolved_ded_formula with
            | None -> ()
            | Some(id,ded_list) -> List.iter (fun ded -> display_below (display_ded id ded)) ded_list
          in
          let _ = UF_Map.iter (fun id cell -> display_below (display_eq id cell)) uf.unsolved_eq_formula in

          !str
        else
          let _ =  str := (Printf.sprintf "\n%s\n     " (Display.lcurlybracket out)) in

          let _ = match uf.unsolved_ded_formula with
            | None -> ()
            | Some(id,ded_list) -> List.iter (fun ded -> display_above (display_ded id ded)) ded_list
          in
          let _ = UF_Map.iter (fun id cell -> display_above (display_eq id cell)) uf.unsolved_eq_formula in

          !str
      in

      str_solved ^ "\n" ^ str_unsolved ^ "\n"
      end
    else
      begin
      (* Solved *)
      s_max := UF_Map.cardinal uf.solved_eq_formula + UF_Map.cardinal uf.unsolved_eq_formula + (if uf.solved_ded_formula = None then 0 else 1) + (match uf.unsolved_ded_formula with None -> 0 | Some(_,l) -> List.length l);

      if !s_max = 0
      then Printf.sprintf "%s %s" (Display.lcurlybracket out) (Display.rcurlybracket out)
      else if !s_max <= per_line
      then
        let _ =  str := (Printf.sprintf "%s " (Display.lcurlybracket out)) in

        let _ = match uf.solved_ded_formula with
          | None -> ()
          | Some(id,ded) -> display_below (display_ded id ded)
        in

        let _ = match uf.unsolved_ded_formula with
          | None -> ()
          | Some(id,ded_list) -> List.iter (fun ded -> display_below (display_ded id ded)) ded_list
        in

        let _ = UF_Map.iter (fun id cell -> display_below (display_eq id cell)) uf.solved_eq_formula in
        let _ = UF_Map.iter (fun id cell -> display_below (display_eq id cell)) uf.unsolved_eq_formula in

        !str
      else
        let _ = str := (Printf.sprintf "\n%s\n     " (Display.lcurlybracket out)) in

        let _ = match uf.solved_ded_formula with
          | None -> ()
          | Some(id,ded) -> display_above (display_ded id ded)
        in

        let _ = match uf.unsolved_ded_formula with
          | None -> ()
          | Some(id,ded_list) -> List.iter (fun ded -> display_above (display_ded id ded)) ded_list
        in

        let _ = UF_Map.iter (fun id cell -> display_above (display_eq id cell)) uf.solved_eq_formula in
        let _ = UF_Map.iter (fun id cell -> display_above(display_eq id cell)) uf.unsolved_eq_formula in

        !str

      end
end

(************************
***         Eq        ***
*************************)

module Eq = struct

  type ('a, 'b) formula =
    | Top
    | Bot
    | Conj of ('a, 'b) Diseq.t list

  let top = Top

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

      apply at form subst = Bot
    with
      | Subst.Not_unifiable -> true

  let extract = function
    | Top -> None, Top
    | Bot -> None, Bot
    | Conj [] -> Config.internal_error "[data_structure.ml >> DF.extract] The list should not be empty"
    | Conj [diseq] -> Some diseq, Top
    | Conj (diseq::q) -> Some diseq, Conj q

  let display out at = function
    | Top -> Display.top out
    | Bot -> Display.bot out
    | Conj diseq_list -> Display.display_list (Diseq.display out at) (Printf.sprintf " %s " (Display.wedge out)) diseq_list

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

  let display ?(per_line = 5) out uni =

    let current_number = ref 1 in
    let s_max = ref 0 in

    Subterm.iter (fun _ set ->
      s_max := !s_max + Recipe_Set.cardinal set
    ) uni;

    if !s_max = 0
    then Printf.sprintf "%s %s" (Display.lcurlybracket out) (Display.rcurlybracket out)
    else if !s_max <= per_line
    then
      begin
        let str = ref (Printf.sprintf "%s " (Display.lcurlybracket out)) in
        Subterm.iter (fun pterm recipe_set ->
          Recipe_Set.iter (fun recipe ->
            if !current_number < !s_max
            then str := !str ^ (Printf.sprintf "(%s,%s)" (display out Recipe recipe) (display out Protocol pterm)) ^ "; "
            else str := !str ^ (Printf.sprintf "(%s,%s)" (display out Recipe recipe) (display out Protocol pterm)) ^ " " ^ (Display.rcurlybracket out);

            current_number := !current_number + 1
          ) recipe_set
        ) uni;

        !str
      end
    else
      begin
        let str = ref (Printf.sprintf "\n%s\n     " (Display.lcurlybracket out)) in
        Subterm.iter (fun pterm recipe_set ->
          Recipe_Set.iter (fun recipe ->
            if !current_number >= !s_max
            then str:= !str ^ (Printf.sprintf "(%s,%s)" (display out Recipe recipe) (display out Protocol pterm)) ^ "\n" ^ (Display.rcurlybracket out)
            else if (!current_number / per_line) * per_line = !current_number
            then str := !str ^ (Printf.sprintf "(%s,%s)" (display out Recipe recipe) (display out Protocol pterm)) ^ ";\n     "
            else str := !str ^ (Printf.sprintf "(%s,%s)" (display out Recipe recipe) (display out Protocol pterm)) ^ "; ";

            current_number := !current_number + 1
          ) recipe_set
        ) uni;
        !str
      end

end
