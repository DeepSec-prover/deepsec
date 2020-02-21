open Types
open Display
open Extensions

module HashSymb = struct
  type t = symbol

  let equal : symbol -> symbol -> bool = (==)

  let hash : symbol -> int = Hashtbl.hash
end

module HashtblSymb = Hashtbl.Make(HashSymb)

(************************************
***            Variables          ***
*************************************)

module Variable = struct

  let accumulator = ref 0

  let set_up_counter n = accumulator := n

  let get_counter () = !accumulator

  (******* Generation *******)

  let fresh_with_label q s =
    let var = { label = s; index = !accumulator; link = NoLink; quantifier = q } in
    incr accumulator ;
    var

  let fresh q = fresh_with_label q "x"

  let fresh_from var =
    let var = { label = var.label; index = !accumulator; link = NoLink; quantifier = var.quantifier } in
    accumulator := !accumulator + 1;
    var

  let fresh_list q n =
    let rec tail_fresh acc = function
      | 0 -> acc
      | n -> tail_fresh ((fresh q)::acc) (n-1)
    in
    tail_fresh [] n

  let fresh_term_list q n =
    let rec tail_fresh acc = function
      | 0 -> acc
      | ar -> tail_fresh ((Var(fresh q))::acc) (ar-1)
    in
    tail_fresh [] n

  (******* Access *******)

  let quantifier_of v = v.quantifier

  (******* Display *******)

  let display out v = match out with
    | Terminal ->
        if v.index = 0
        then display_identifier out v.label
        else Printf.sprintf "%s_%d" v.label v.index
    | HTML ->
        if v.index = 0
        then display_identifier out v.label
        else Printf.sprintf "%s<sub>%d</sub>" v.label v.index
    | Latex ->
        if v.index = 0
        then display_identifier out v.label
        else Printf.sprintf "%s_{%d}" v.label v.index

  (******* Links *******)

  let currently_linked : variable list ref = ref []

  (** [link v v'] links the variable [v'] to the variable [v]. *)
  let link v v' =
    Config.debug (fun () ->
      if v.link <> NoLink
      then Config.internal_error "[term.ml >> Variable.link] The first variable should not be already linked."
    );

    v.link <- VLink v';
    currently_linked := v :: !currently_linked

  let link_term v t =
    Config.debug (fun () ->
      if v.link <> NoLink
      then Config.internal_error "[term.ml >> Variable.link_term] The variable should not be already linked."
    );

    v.link <- TLink t;
    currently_linked := v :: !currently_linked

  let link_search v =
    Config.debug (fun () ->
      if v.link <> NoLink
      then Config.internal_error "[term.ml >> Variable.link_search] The first variable should not be already linked."
    );

    v.link <- SLink;
    currently_linked := v :: !currently_linked

  let auto_cleanup_with_reset (f_cont:(unit -> unit) -> unit) (f_next:unit -> unit) =
    let tmp = !currently_linked in
    currently_linked := [];

    f_cont (fun () ->
      List.iter (fun v -> v.link <- NoLink) !currently_linked;
      currently_linked := tmp;
      f_next ()
    )

  let auto_cleanup_with_reset_notail (f_cont:unit -> 'a) =
    let tmp = !currently_linked in
    currently_linked := [];

    let r = f_cont () in

    List.iter (fun v -> v.link <- NoLink) !currently_linked;
    currently_linked := tmp;

    r

  let auto_cleanup_with_exception (f_cont:unit -> 'a) =
    let tmp = !currently_linked in
    currently_linked := [];

    try
      let r = f_cont () in
      List.iter (fun v -> v.link <- NoLink) !currently_linked;
      currently_linked := tmp;
      r
    with e ->
      List.iter (fun v -> v.link <- NoLink) !currently_linked;
      currently_linked := tmp;
      raise e

  let cleanup () =
    List.iter (fun v -> v.link <- NoLink) !currently_linked;
    currently_linked := []

  (******* Renaming *******)

  let rename v = match v.link with
    | VLink v' -> v'
    | NoLink ->
        let v' = fresh_with_label v.quantifier v.label in
        link v v';
        v'
    | SLink -> v
    | _ -> Config.internal_error "[term.ml >> Variable.rename] Unexpected link"

  (** [rename_term q t] renames the variables in [t] by fresh variables with quantifier [q].
      We assume that the variables can only be linked with VLink. *)
  let rec rename_term q t = match t with
    | Var v ->
        begin match v.link with
          | VLink v' -> Var v'
          | NoLink ->
              let v' = fresh_with_label q v.label in
              link v v';
              Var v'
          | TLink _ -> Config.internal_error "[term.ml >> Variable.rename_term] Unexpected TLink"
          | XLink _ -> Config.internal_error "[term.ml >> Variable.rename_term] Unexpected XLink"
          | SLink -> Config.internal_error "[term.ml >> Variable.rename_term] Unexpected Slink"
        end
    | Func(f,args) -> Func(f, List.map (rename_term q) args)
    | _ -> t
end

(************************************-
***         Recipe variable       ***
*************************************)

module Recipe_Variable = struct

  let accumulator = ref 0

  let set_up_counter n = accumulator := n

  let get_counter () = !accumulator

  let infinite_type = max_int

  (******* Generation *******)

  let fresh q ty =
    let var = { index_r = !accumulator; link_r = RNoLink; quantifier_r = q; type_r = ty } in
    incr accumulator;
    var

  let fresh_from var =
    let var = { index_r = !accumulator; link_r = RNoLink; quantifier_r = var.quantifier_r; type_r = var.type_r } in
    accumulator := !accumulator + 1;
    var

  let fresh_list q ty n =
    let rec tail_fresh acc = function
      | 0 -> acc
      | n -> tail_fresh ((fresh q ty)::acc) (n-1)
    in
    tail_fresh [] n

  (******* Access *******)

  let quantifier_of v = v.quantifier_r

  let type_of v = v.type_r

  (******* Testing *******)

  let order v1 v2 = match compare v1.type_r v2.type_r with
    | 0 -> compare v1.index_r v2.index_r
    | n -> n

  (******* Display *******)

  let display out ?(display_type=false) ?(label="X") v =
    let index_label =
      if v.index_r = 0
      then label
      else
        match out with
          | Terminal -> Printf.sprintf "%s_%d" label v.index_r
          | HTML -> Printf.sprintf "%s<sub>%d</sub>" label v.index_r
          | Latex -> Printf.sprintf "%s_{%d}" label v.index_r
    in

    if display_type
    then
      match out with
        | Terminal | HTML -> Printf.sprintf "%s:%d" index_label v.type_r
        | Latex -> Printf.sprintf "%s\\text{:}%d" index_label v.type_r
    else index_label

  (******* Links *******)

  let currently_linked : recipe_variable list ref = ref []

  (** [link v v'] links the variable [v'] to the variable [v]. *)
  let link v v' =
    Config.debug (fun () ->
      if v.link_r <> RNoLink
      then Config.internal_error "[term.ml >> Recipe_Variable.link] The first variable should not be already linked."
    );

    v.link_r <- RVLink v';
    currently_linked := v :: !currently_linked

  let link_recipe v r =
    Config.debug (fun () ->
      if v.link_r <> RNoLink
      then Config.internal_error "[term.ml >> Recipe_Variable.link_recipe] The first variable should not be already linked."
    );

    v.link_r <- RLink r;
    currently_linked := v :: !currently_linked

  let auto_cleanup_with_reset (f_cont:(unit -> unit) -> unit) (f_next:unit -> unit) =
    let tmp = !currently_linked in
    currently_linked := [];

    f_cont (fun () ->
      List.iter (fun v -> v.link_r <- RNoLink) !currently_linked;
      currently_linked := tmp;
      f_next ()
    )

  let auto_cleanup_with_reset_notail (f_cont:unit -> 'a) =
    let tmp = !currently_linked in
    currently_linked := [];

    let r = f_cont () in

    List.iter (fun v -> v.link_r <- RNoLink) !currently_linked;
    currently_linked := tmp;

    r

  let auto_cleanup_with_exception (f_cont:unit -> 'a) =
    let tmp = !currently_linked in
    currently_linked := [];
    try
      let r = f_cont () in
      List.iter (fun v -> v.link_r <- RNoLink) !currently_linked;
      currently_linked := tmp;
      r
    with e ->
      List.iter (fun v -> v.link_r <- RNoLink) !currently_linked;
      currently_linked := tmp;
      raise e

  let cleanup () =
    List.iter (fun v -> v.link_r <- RNoLink) !currently_linked;
    currently_linked := []

  (******* Renaming *******)

  (** [rename_term q r] renames the variables in [t] by fresh variables with quantifier [q].
      We assume that the variables can only be linked with RLink. *)
  let rec rename_recipe q r = match r with
    | RVar v ->
        begin match v.link_r with
          | RVLink v' -> RVar v'
          | RNoLink ->
              let v' = fresh q v.type_r in
              link v v';
              RVar v'
          | _ -> Config.internal_error "[term.ml >> Recipe_Variable.rename_recipe] Unexpected link"
        end
    | RFunc(f,args) -> RFunc(f, List.map (rename_recipe q) args)
    | _ -> r
end

(*************************************
***             Names              ***
**************************************)

module Name = struct

  let accumulator = ref 0

  let set_up_counter n = accumulator := n

  let get_counter () = !accumulator

  (******* Generation *******)

  let fresh_with_label ?(pure=false) n =
    let name = { label_n = n; index_n = !accumulator; pure_fresh_n = pure; link_n = NNoLink } in
    accumulator := !accumulator + 1;
    name

  let fresh () = fresh_with_label "n"

  let fresh_from name = fresh_with_label ~pure:name.pure_fresh_n name.label_n

  let pure_fresh_from name =
    let name' = { label_n = name.label_n; index_n = !accumulator; pure_fresh_n = true; link_n = NNoLink } in
    accumulator := !accumulator + 1;
    name'

  (******* Testing *******)

  let order n1 n2 = compare n1.index_n n2.index_n

  (******* Display *******)

  let display out n = match out with
    | Terminal ->
        if n.index_n = 0
        then display_identifier out n.label_n
        else Printf.sprintf "%s_%d%s" n.label_n n.index_n (if n.pure_fresh_n then "[p]" else "")
    | HTML ->
        if n.index_n = 0
        then display_identifier out n.label_n
        else Printf.sprintf "%s<sub>%d</sub>" n.label_n n.index_n
    | Latex ->
        if n.index_n = 0
        then display_identifier out n.label_n
        else Printf.sprintf "%s_{%d}" n.label_n n.index_n

  (******* Link *******)

  let currently_linked : name list ref = ref []

  (** [link n n'] links the name [n'] to the variable [n]. *)
  let link n n' =
    Config.debug (fun () ->
      if n.link_n <> NNoLink
      then Config.internal_error "[term.ml >> Name.link] The first name should not be already linked."
    );

    n.link_n <- NLink n';
    currently_linked := n :: !currently_linked

  let link_search n =
    Config.debug (fun () ->
      if n.link_n <> NNoLink
      then Config.internal_error "[term.ml >> Name.link_search] The first name should not be already linked."
    );

    n.link_n <- NSLink;
    currently_linked := n :: !currently_linked

  let auto_cleanup_with_reset_notail (f_cont:unit -> 'a) =
    let tmp = !currently_linked in
    currently_linked := [];

    let r = f_cont () in

    List.iter (fun n -> n.link_n <- NNoLink) !currently_linked;
    currently_linked := tmp;

    r

  let auto_cleanup_with_exception (f_cont:unit -> 'a) =
    let tmp = !currently_linked in
    currently_linked := [];

    try
      let r = f_cont () in
      List.iter (fun n -> n.link_n <- NNoLink) !currently_linked;
      currently_linked := tmp;
      r
    with e ->
      List.iter (fun n -> n.link_n <- NNoLink) !currently_linked;
      currently_linked := tmp;
      raise e

    let cleanup () =
      List.iter (fun n -> n.link_n <- NNoLink) !currently_linked;
      currently_linked := []
end

(*************************************
***            Axioms              ***
**************************************)

module Axiom = struct

  let order (ax1:int) (ax2:int) = compare ax1 ax2

  let display out ax = match out with
    | Terminal -> Printf.sprintf "ax_%d" ax
    | HTML -> Printf.sprintf "ax<sub>%d</sub>" ax
    | Latex -> Printf.sprintf "\\mathsf{ax}_{%d}" ax
end


(*********************************
***           Symbol           ***
**********************************)

module Symbol = struct

  (********* Set of function symbols *********)

  let accumulator_nb_symb = ref 0

  let all_constructors = ref ([]:symbol list)

  let all_destructors = ref ([]:symbol list)

  let all_tuple = ref ([]:symbol list)

  let number_of_constructors = ref 0

  let number_of_destructors = ref 0

  let number_of_attacker_name = ref 0

  let all_projection : symbol list HashtblSymb.t = HashtblSymb.create 7

  let special_constructor : (int,symbol) Hashtbl.t = Hashtbl.create 7

  let attacker_names : (string,symbol) Hashtbl.t = Hashtbl.create 7

  let get_number_of_attacker_name () = !number_of_attacker_name

  let empty_signature () =
    all_constructors := [];
    all_destructors := [];
    all_tuple := [];
    number_of_constructors := 0;
    number_of_destructors := 0;
    number_of_attacker_name := 0;
    HashtblSymb.reset all_projection;
    Hashtbl.reset special_constructor;
    Hashtbl.reset attacker_names

  type setting =
    {
      all_t : symbol list ;
      all_p : (symbol * symbol list) list ;
      all_c : symbol list ;
      all_d : symbol list ;
      nb_c : int ;
      nb_d : int ;
      nb_symb : int;
      nb_a : int
    }

  let set_up_signature setting =
    accumulator_nb_symb := setting.nb_symb;
    all_constructors := setting.all_c;
    all_destructors := setting.all_d;
    all_tuple := setting.all_t;
    number_of_constructors := setting.nb_c;
    number_of_destructors := setting.nb_d;
    HashtblSymb.reset all_projection;
    Hashtbl.reset special_constructor;
    List.iter (fun (f,list_proj) ->
      HashtblSymb.add all_projection f list_proj
    ) setting.all_p;
    number_of_attacker_name := setting.nb_a

  let get_settings () =
    {
      all_t = !all_tuple;
      all_p = HashtblSymb.fold (fun f list_proj acc -> (f,list_proj)::acc) all_projection [];
      all_c = !all_constructors;
      all_d = !all_destructors;
      nb_c = !number_of_constructors;
      nb_d = !number_of_destructors;
      nb_symb = !accumulator_nb_symb;
      nb_a = !number_of_attacker_name
    }

  (********* Testing *********)

  let is_destructor sym = match sym.cat with
    | Destructor _ -> true
    | _ -> false

  let is_constructor sym = match sym.cat with
    | Constructor | Tuple -> true
    | _ -> false

  let is_attacker_name sym = match sym.represents with
    | AttackerPublicName _ -> true
    | _ -> false

  let get_arity sym = sym.arity

  let order sym_1 sym_2 = compare sym_1.index_s sym_2.index_s

  (********* Tuple ************)

  let get_projections symb_tuple = match symb_tuple.cat with
    | Tuple -> HashtblSymb.find all_projection symb_tuple
    | _ -> Config.internal_error "[term.ml >> Symbol.get_projections] The function symbol should be a tuple"

  (********* Addition ************)

  let new_constructor ar public is_name s =
    let symb = { label_s = s; arity = ar; cat = Constructor; index_s = !accumulator_nb_symb; public = public; represents = (if is_name then UserName else UserDefined) } in
    incr accumulator_nb_symb;
    all_constructors := symb :: !all_constructors;
    incr number_of_constructors;
    symb

  let new_destructor ar public s rw_rules =
    let symb = { label_s = s; arity = ar; cat = Destructor rw_rules; index_s = !accumulator_nb_symb; public = public; represents = UserDefined } in
    incr accumulator_nb_symb;
    all_destructors := symb :: !all_destructors;
    number_of_destructors := !number_of_destructors + 1;
    symb

  let rec new_projection acc tuple_symb i = match i with
    | 0 -> acc
    | i ->
        let args = Variable.fresh_term_list Existential tuple_symb.arity in
        let x = List.nth args (i-1) in
        let symb =
          {
            label_s = (Printf.sprintf "proj_{%d,%d}" i tuple_symb.arity);
            arity = 1;
            cat = Destructor([([Func(tuple_symb,args)],x)]);
            index_s = !accumulator_nb_symb;
            public = true;
            represents = UserDefined
          }
        in
        incr accumulator_nb_symb;
        new_projection (symb::acc) tuple_symb (i-1)

  let get_tuple ar =
    try
      List.find (fun symb -> symb.arity = ar) !all_tuple
    with Not_found ->
      begin
        let symb = { label_s = (Printf.sprintf "tuple%d" ar); arity = ar; cat = Tuple; index_s = !accumulator_nb_symb; public = true; represents = UserDefined } in
        incr accumulator_nb_symb;
        all_constructors := symb::!all_constructors;
        all_tuple := symb::!all_tuple;
        number_of_constructors := !number_of_constructors + 1;

        let list_proj = new_projection [] symb ar in
        HashtblSymb.add all_projection symb list_proj;

        symb
      end

  (* Used to instantiate the variables of a solved constraint system. *)

  let auto_cleanup_attacker_name (f_cont:(unit -> unit) -> unit) (f_next:unit -> unit) =
    let tmp = !number_of_attacker_name in

    f_cont (fun () ->
      number_of_attacker_name := tmp;
      f_next ()
    )

  (* Only be used in the constraint solving *)
  let fresh_attacker_name () =
    let symb = { label_s = "#n"; arity = 0; cat = Constructor; index_s = !accumulator_nb_symb; public = true; represents = AttackerPublicName !number_of_attacker_name } in
    incr number_of_attacker_name;
    incr accumulator_nb_symb;
    symb

  (* Only be used in the simulator *)
  let get_attacker_name str =
    try
      Hashtbl.find attacker_names str
    with Not_found ->
      let c = { label_s = str; arity = 0; cat = Constructor; index_s = !accumulator_nb_symb; public = true; represents = AttackerPublicName (-1) } in
      Hashtbl.add attacker_names str c;
      incr accumulator_nb_symb;
      c

  (* Only be used in the simulator *)
  let rec fresh_attacker_name_ground () =
    let str = "#n_"^(string_of_int !number_of_attacker_name) in
    if Hashtbl.mem attacker_names str
    then
      begin
        incr number_of_attacker_name;
        fresh_attacker_name_ground ()
      end
    else
      begin
        let symb = { label_s = str; arity = 0; cat = Constructor; index_s = !accumulator_nb_symb; public = true; represents = AttackerPublicName (-1) } in
        incr number_of_attacker_name;
        incr accumulator_nb_symb;
        Hashtbl.add attacker_names str symb;
        symb
      end

  (******** Display function *******)

  let display _ f = match f.represents with
    | AttackerPublicName i when i >= 0 -> "#n_"^(string_of_int i)
    | _ -> f.label_s

  let display_with_arity out f =
    if f.public
    then Printf.sprintf "%s/%d" (display out f) f.arity
    else Printf.sprintf "%s/%d [private]" (display out f) f.arity

  let reg_proj = Str.regexp "proj_{"

  let display_signature out constructor =
    if constructor
    then
      let without_tuple = List.filter (fun f -> f.cat <> Tuple && f.represents = UserDefined) !all_constructors in
      if without_tuple = []
      then emptyset out
      else Printf.sprintf "%s %s %s" (lcurlybracket out) (display_list (display_with_arity out) ", " without_tuple) (rcurlybracket out)
    else
      let without_projection = List.filter (fun f -> not (Str.string_match reg_proj f.label_s 0)) !all_destructors in
      if without_projection = []
      then emptyset out
      else Printf.sprintf "%s %s %s" (lcurlybracket out) (display_list (display_with_arity out) ", " without_projection) (rcurlybracket out)

  let display_names out public =
    let names = List.filter (fun f -> f.represents = UserName && f.public = public) !all_constructors in
    if names = []
    then emptyset out
    else Printf.sprintf "%s %s %s" (lcurlybracket out) (display_list (display out) ", " names) (rcurlybracket out)
end

(*************************************
***              Terms             ***
**************************************)

module Term = struct

  (********** Display **********)

  let rec display ?(follow_link=true) out = function
    | Var { link = TLink t; _ } when follow_link -> display out t
    | Var v -> Variable.display out v
    | Name n -> Name.display out n
    | Func(f_symb,_) when f_symb.arity = 0 ->
        Printf.sprintf "%s" (Symbol.display out f_symb)
    | Func(f_symb,args) when f_symb.cat = Tuple ->
        Printf.sprintf "(%s)" (display_list (display ~follow_link:follow_link out) "," args)
    | Func(f_symb,args) ->
        Printf.sprintf "%s(%s)" (Symbol.display out f_symb) (display_list (display ~follow_link:follow_link out) "," args)

  let rec display_pattern ?(follow_link=true) out = function
    | PatVar { link = TLink t; _} when follow_link -> display ~follow_link:follow_link out t
    | PatVar v -> Variable.display out v
    | PatEquality t -> display ~follow_link:follow_link out t
    | PatTuple(_,args) -> Printf.sprintf "%s%s%s" (langle out) (display_list (display_pattern ~follow_link:follow_link out) "," args) (rangle out)


  (********* Access *********)

  let variable_of = function
    | Var v -> v
    | _ -> Config.internal_error "[term.ml >> Term.variable_of] The term should be a variable"

  let name_of = function
    | Name n -> n
    | _ -> Config.internal_error "[term.ml >> Term.name_of] The term should be a name"

  let root = function
    | Func(s,_) -> s
    | _ -> Config.internal_error "[term.ml >> Term.root] The term is not a function application."

  let get_args = function
    | Func(s,_) when s.arity = 0 -> Config.internal_error "[term.ml >> Term.get_args] The term should not be a constant."
    | Func(_,l) -> l
    | _ -> Config.internal_error "[term.ml >> Term.get_args] The term is not a function application."

  (** We assume that the variables are not linked. *)
  let get_vars_not_in term var_list =

    List.iter (fun v -> v.link <- SLink) var_list;

    let rec explore_term = function
      | Func (_,args) -> List.iter explore_term args
      | Var({link = SLink; _}) -> ()
      | Var v ->
          v.link <- SLink;
          Variable.currently_linked := v :: !Variable.currently_linked
      | Name _ -> ()
    in

    explore_term term;
    let result = !Variable.currently_linked in
    List.iter (fun v -> v.link <- NoLink) !Variable.currently_linked;
    List.iter (fun v -> v.link <- NoLink) var_list;
    result

  (********* Testing *********)

  let rec does_not_contain_name = function
    | Var _ -> true
    | Name _ -> false
    | Func(_,tlist) -> List.for_all does_not_contain_name tlist

  (* We follow the links TLink. *)
  let rec var_occurs v = function
    | Var v' when v == v' -> true
    | Var {link = TLink t; _} -> var_occurs v t
    | Func(_,args) -> List.exists (var_occurs v) args
    | _ -> false

  let rec quantified_var_occurs q = function
    | Var { quantifier = q'; _ } -> q = q'
    | Func(_,args) -> List.exists (quantified_var_occurs q) args
    | _ -> false

  (* We follow the links TLink. *)
  let rec is_equal t1 t2 = match t1, t2 with
    | Var v1, Var v2 when v1 == v2 -> true
    | Var { link = TLink t; _ }, t'
    | t', Var { link = TLink t; _ } -> is_equal t t'
    | Name n1, Name n2 -> n1 == n2
    | Func(f1,args1), Func(f2,args2) -> f1 == f2 && List.for_all2 is_equal args1 args2
    | _ -> false

  (* Same as [is_equal] but we do not follow the links TLink. *)
  let is_equal_no_follow t1 t2 = match t1, t2 with
    | Var v1, Var v2 when v1 == v2 -> true
    | Name n1, Name n2 when n1 == n2 -> true
    | Func(f1,args1), Func(f2,args2) when f1 == f2 -> List.for_all2 is_equal args1 args2
    | _ -> false

  let is_variable = function
    | Var _ -> true
    | _ -> false

  let is_name = function
    | Name _ -> true
    | _ -> false

  let is_function  = function
    | Func _ -> true
    | _ -> false

  let rec is_constructor = function
    | Func({cat = Destructor _; _},_) -> false
    | Func(_,args) -> List.for_all is_constructor args
    | _ -> true

  let rec is_ground = function
    | Var { link = TLink t; _ } -> is_ground t
    | Name _ -> true
    | Var _ -> false
    | Func(_,args) -> List.for_all is_ground args

  (********* Renaming *********)

  let rec apply_renamings = function
    | Var { link = VLink v; _ } -> Var v
    | Var v -> Var v
    | Name { link_n = NLink n; _ } -> Name n
    | Name n -> Name n
    | Func(f,args) -> Func(f,List.map apply_renamings args)

  (********** Unification ***********)

  exception Not_unifiable

  let rec unify t1 t2 = match t1, t2 with
    | Var v1, Var v2 when v1 == v2 -> ()
    | Var {link = TLink t ; _}, _ -> unify t t2
    | _, Var {link = TLink t; _} -> unify t1 t
    | Var v1, Var v2 ->
        if v1.quantifier = Universal || (v1.quantifier = Existential && v2.quantifier = Free) || (v1.quantifier = v2.quantifier && v1.index < v2.index)
        then (v1.link <- TLink t2; Variable.currently_linked := v1 :: !Variable.currently_linked)
        else (v2.link <- TLink t1; Variable.currently_linked := v2 :: !Variable.currently_linked)
    | Var v1, _ when not (var_occurs v1 t2) -> v1.link <- TLink t2; Variable.currently_linked := v1 :: !Variable.currently_linked
    | _, Var v2 when not (var_occurs v2 t1) -> v2.link <- TLink t1; Variable.currently_linked := v2 :: !Variable.currently_linked
    | Name n1, Name n2 when n1 == n2 -> ()
    | Func(f1,args1), Func(f2,args2) when f1 == f2 -> List.iter2 unify args1 args2
    | _ -> raise Not_unifiable

  (******* Matching *******)

  exception No_match

  let rec matching t1 t2 = match t1,t2 with
    | _, Var { link = TLink t2'; _ } -> matching t1 t2'
    | Var {link = TLink t ; _}, _ ->
        if not (is_equal t t2)
        then raise No_match
    | Var v1,_ -> v1.link <- TLink t2; Variable.currently_linked := v1 :: !Variable.currently_linked
    | Name n1, Name n2 when n1 == n2 -> ()
    | Func(f1,args1), Func(f2,args2) when f1 == f2 -> List.iter2 matching args1 args2
    | _,_ -> raise No_match

  (********** Instantiation ***********)

  let rec instantiate term = match term with
    | Var { link = TLink t; _} -> instantiate t
    | Func(f,args) ->
        let args' = instantiate_list args in
        if args' == args
        then term
        else Func(f,args')
    | t -> t

  and instantiate_list term_list = match term_list with
    | [] -> term_list
    | t::q ->
        let t' = instantiate t in
        if t == t'
        then
          let q' = instantiate_list q in
          if q == q'
          then term_list
          else t'::q'
        else t'::(instantiate_list q)

  let rec instantiate_pattern = function
    | PatEquality t -> PatEquality (instantiate t)
    | PatTuple(f,args) -> PatTuple(f,List.map instantiate_pattern args)
    | pat -> pat

  let rec replace_universal_to_existential = function
    | Var { link = TLink t; _} -> replace_universal_to_existential t
    | Var v when v.quantifier = Universal ->
        let v' = Variable.fresh Existential in
        Variable.link_term v (Var v')
    | Func(_,args) -> List.iter replace_universal_to_existential args
    | _ -> ()

  (********** Renaming function for preparing the solving procedure *********)

  let rec rename_and_instantiate term = match term with
    | Var v ->
        begin match v.link with
          | TLink t -> rename_and_instantiate t
          | VLink v' -> Var v' (* v' is the fresh replacement of v *)
          | NoLink ->
              let v' = Variable.fresh_with_label v.quantifier v.label in
              Variable.link v v';
              Var v'
          | _ -> Config.internal_error "[term.ml >> Term.rename_and_instantiate] Unexpected link of variable."
        end
    | Func(f,args) ->
        let args' = rename_and_instantiate_list args in
        if args == args'
        then term
        else Func(f,args')
    | Name _ -> term

  and rename_and_instantiate_list term_list = match term_list with
    | [] -> term_list
    | t::q ->
        let t' = rename_and_instantiate t in
        if t == t'
        then
          let q' = rename_and_instantiate_list q in
          if q == q'
          then term_list
          else t'::q'
        else t'::(rename_and_instantiate_list q)

  let rec rename_and_instantiate_exclude_universal term = match term with
    | Var ({ quantifier = Universal; _ } as v) ->
        Config.debug (fun () ->
          if v.link <> NoLink
          then Config.internal_error "[term.ml >> rename_and_instantiate_exclude_universal] Should not rename a universal variable that contain link."
        );
        term
    | Var v ->
        begin match v.link with
          | TLink t -> rename_and_instantiate_exclude_universal t
          | VLink v' -> Var v'
          | NoLink ->
              let v' = Variable.fresh_with_label v.quantifier v.label in
              Variable.link v v';
              Var v'
          | _ -> Config.internal_error "[term.ml >> Term.rename_and_instantiate_exclude_universal] Unexpected link of variable."
        end
    | Func(f,args) ->
        let args' = rename_and_instantiate_exclude_universal_list args in
        if args == args'
        then term
        else Func(f,args')

    | Name _ -> term

  and rename_and_instantiate_exclude_universal_list term_list = match term_list with
    | [] -> term_list
    | t::q ->
        let t' = rename_and_instantiate_exclude_universal t in
        if t == t'
        then
          let q' = rename_and_instantiate_exclude_universal_list q in
          if q == q'
          then term_list
          else t'::q'
        else t'::(rename_and_instantiate_exclude_universal_list q)

  let rec rename_and_instantiate_exclude_universal_slink term = match term with
    | Var ({ quantifier = Universal; _ } as v) ->
        Config.debug (fun () ->
          if v.link <> NoLink
          then Config.internal_error "[term.ml >> rename_and_instantiate_exclude_universal_slink] Should not rename a universal variable that contain link."
        );
        term
    | Var v ->
        begin match v.link with
          | SLink -> term
          | TLink t -> rename_and_instantiate_exclude_universal_slink t
          | VLink v' -> Var v'
          | NoLink ->
              let v' = Variable.fresh_with_label v.quantifier v.label in
              Variable.link v v';
              Var v'
          | _ -> Config.internal_error "[term.ml >> Term.rename_and_instantiate_exclude_universal_slink] Unexpected link of variable."
        end
    | Func(f,args) ->
        let args' = rename_and_instantiate_exclude_universal_slink_list args in
        if args == args'
        then term
        else Func(f,args')

    | Name _ -> term

  and rename_and_instantiate_exclude_universal_slink_list term_list = match term_list with
    | [] -> term_list
    | t::q ->
        let t' = rename_and_instantiate_exclude_universal_slink t in
        if t == t'
        then
          let q' = rename_and_instantiate_exclude_universal_slink_list q in
          if q == q'
          then term_list
          else t'::q'
        else t'::(rename_and_instantiate_exclude_universal_slink_list q)

  (*********** Debug ************)

  let rec debug_link_with_SLink = function
    | Var { link = TLink t; _ } -> debug_link_with_SLink t
    | Var { link = SLink; _} -> ()
    | Var ({ link = NoLink; _ } as v) ->
        v.link <- SLink;
        Variable.currently_linked := v :: !Variable.currently_linked
    | Var _ -> Config.internal_error "[term.ml >> Term.debug_link_term_with_SLink] Should not apply the debug term with VLink or XLink"
    | Name _ -> ()
    | Func(_,args) -> List.iter debug_link_with_SLink args

  let rec debug_check_link_with_SLink = function
    | Var { link = TLink t; _ } -> debug_check_link_with_SLink t
    | Var { link = SLink; _} -> ()
    | Var { link = NoLink; _ } -> raise Not_found
    | Var _ -> Config.internal_error "[term.ml >> Term.debug_check_link_with_SLink] Should not apply the debug term with VLink or XLink"
    | Name _ -> ()
    | Func(_,args) -> List.iter debug_check_link_with_SLink args
end

(*************************************
***              Recipe            ***
**************************************)


module Recipe = struct

  (********* Access *********)

  let variable_of = function
    | RVar v -> v
    | _ -> Config.internal_error "[term.ml >> Recipe.variable_of] The recipe should be a variable"

  let axiom_of = function
    | Axiom ax -> ax
    | _ -> Config.internal_error "[term.ml >> Recipe.axiom_of] The recipe should be an axiom"

  let root = function
    | RFunc(s,_) -> s
    | _ -> Config.internal_error "[term.ml >> Recipe.root] The recipe is not a function application."

  let get_args = function
    | RFunc(s,_) when s.arity = 0 -> Config.internal_error "[terms.ml >> Recipe.get_args] The recipe should not be a constant."
    | RFunc(_,l) -> l
    | _ -> Config.internal_error "[terms.ml >> Recipe.get_args] The recipe is not a function application."

  (********* Testing *********)

  (** In the following funciton, we follow the links RLink. *)
  let rec var_occurs var = function
    | RVar v when v == var -> true
    | RVar {link_r = RLink t; _} -> var_occurs var t
    | RFunc(_,args) -> List.exists (var_occurs var) args
    | _ -> false

  (** [var_occurs_or_strictly_greater_type] {% $\quanti{X}{i}$ $\xi$ %} returns [true] iff {% $X \in \varsdeux{\xi}$ or $\xi \not\in \T(\F,\AX_i \cup \Xdeux_i)$. %}
     We follow the links RLink. *)
  let var_occurs_or_strictly_greater_type var r =
    if var.type_r = max_int
    then var_occurs var r
    else
      let rec explore_recipe = function
        | RVar v when v == var -> true
        | RVar {link_r = RLink r; _}
        | CRFunc(_,r)-> explore_recipe r
        | Axiom ax when ax > var.type_r -> true
        | RFunc(_,args) -> List.exists explore_recipe args
        | _ -> false
      in
      explore_recipe r

  (** We follow the links RLink. *)
  let rec is_equal r1 r2 = match r1, r2 with
    | RVar v1, RVar v2 when v1 == v2 -> true
    | RVar { link_r = RLink r; _ }, r'
    | r', RVar { link_r = RLink r; _ } -> is_equal r r'
    | Axiom n1, Axiom n2 -> n1 == n2
    | RFunc(f1,args1), RFunc(f2,args2) -> f1 == f2 && List.for_all2 is_equal args1 args2
    | _,_ -> false

  (********** Unification ***********)

  exception Not_unifiable

  let rec unify r1 r2 = match r1, r2 with
    | RVar v1, RVar v2 when v1 == v2 -> ()
    | (RVar {link_r = RLink r ; _} | CRFunc(_,r)), r'
    | r', (RVar {link_r = RLink r; _} | CRFunc(_,r)) -> unify r r'
    | RVar v1, RVar v2 ->
        if v1.type_r < v2.type_r
        then (v2.link_r <- RLink r1; Recipe_Variable.currently_linked := v2 :: !Recipe_Variable.currently_linked)
        else if v1.type_r > v2.type_r
        then (v1.link_r <- RLink r2; Recipe_Variable.currently_linked := v1 :: !Recipe_Variable.currently_linked)
        else if v1.quantifier_r = Universal || (v1.quantifier_r = Existential && v2.quantifier_r = Free) || (v1.quantifier_r = v2.quantifier_r &&  (v1.type_r < v2.type_r || (v1.type_r = v2.type_r && v1.index_r < v2.index_r)))
        then (v1.link_r <- RLink r2; Recipe_Variable.currently_linked := v1 :: !Recipe_Variable.currently_linked)
        else (v2.link_r <- RLink r1; Recipe_Variable.currently_linked := v2 :: !Recipe_Variable.currently_linked)
    | RVar v1, _ when not (var_occurs_or_strictly_greater_type v1 r2) -> v1.link_r <- RLink r2; Recipe_Variable.currently_linked := v1 :: !Recipe_Variable.currently_linked
    | _, RVar v2 when not (var_occurs_or_strictly_greater_type v2 r1) -> v2.link_r <- RLink r1; Recipe_Variable.currently_linked := v2 :: !Recipe_Variable.currently_linked
    | Axiom n1, Axiom n2 when n1 == n2 -> ()
    | RFunc(f1,args1), RFunc(f2,args2) when f1 == f2 -> List.iter2 unify args1 args2
    | _ -> raise Not_unifiable

  (******* Matching *******)

  exception No_match

  let rec matching r1 r2 = match r1,r2 with
    | _, RVar { link_r = RLink r2'; _ } -> matching r1 r2'
    | RVar { link_r = RLink r ; _ }, _ ->
        if not (is_equal r r2)
        then raise No_match
    | RVar v1,_ -> v1.link_r <- RLink r2; Recipe_Variable.currently_linked := v1 :: !Recipe_Variable.currently_linked
    | Axiom n1, Axiom n2 when n1 == n2 -> ()
    | RFunc(f1,args1), RFunc(f2,args2) when f1 == f2 -> List.iter2 matching args1 args2
    | _,_ -> raise No_match

  (********** Instantiation ***********)

  let rec instantiate r = match r with
    | RVar { link_r = RLink r'; _}
    | CRFunc(_,r') -> instantiate r'
    | RFunc(f,args) ->
        let args' = instantiate_list args in
        if args == args'
        then r
        else RFunc(f,args')
    | _ -> r

  and instantiate_list rlist = match rlist with
    | [] -> rlist
    | r::q ->
        let r' = instantiate r in
        if r == r'
        then
          let q' = instantiate_list q in
          if q == q'
          then rlist
          else r'::q'
        else r'::(instantiate_list q)

  let rec instantiate_preserve_context r = match r with
    | RVar { link_r = RLink r'; _} -> instantiate_preserve_context r'
    | RFunc(f,args) ->
        let args' = instantiate_preserve_context_list args in
        if args == args'
        then r
        else RFunc(f,args')
    | r -> r

  and instantiate_preserve_context_list rlist = match rlist with
    | [] -> rlist
    | r::q ->
        let r' = instantiate_preserve_context r in
        if r == r'
        then
          let q' = instantiate_preserve_context_list q in
          if q == q'
          then rlist
          else r'::q'
        else r'::(instantiate_preserve_context_list q)

  (********** Display **********)

  let rec display ?(follow_link=true) out = function
    | RVar { link_r = RLink r; _ } when follow_link -> display out r
    | CRFunc(i,r) -> Printf.sprintf "CR[%d,%s]" i (display out r)
    | RVar v -> Recipe_Variable.display out v
    | Axiom ax -> Axiom.display out ax
    | RFunc(f_symb,_) when f_symb.arity = 0 ->
        Printf.sprintf "%s" (Symbol.display out f_symb)
    | RFunc(f_symb,args) when f_symb.cat = Tuple ->
        Printf.sprintf "(%s)" (display_list (display ~follow_link:follow_link out) "," args)
    | RFunc(f_symb,args) ->
        Printf.sprintf "%s(%s)" (Symbol.display out f_symb) (display_list (display ~follow_link:follow_link out) "," args)
end
