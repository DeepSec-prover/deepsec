open Display

(************************
***       Types       ***
*************************)

type quantifier =
  | Free
  | Existential
  | Universal

type boundedness =
  | Public
  | Bound

type name =
  {
    label_n : string;
    bound : boundedness;
    index_n : int;
    mutable link_n : link_n
  }

and axiom =
  {
    id_axiom : int;
    public_name : name option;
  }

and link_n =
  | NNoLink
  | NLink of name
  | NLinkSearch

type fst_ord = NoType

type snd_ord = int

type ('a, 'b) atom =
  | Protocol : (fst_ord, name) atom
  | Recipe : (snd_ord, axiom) atom

type symbol_cat =
  | Tuple
  | Constructor
  | Destructor of ((fst_ord, name) term list *  (fst_ord, name) term) list

and symbol =
  {
    name : string;
    arity : int;
    cat : symbol_cat
  }

and ('a,'b) link =
  | NoLink
  | TLink of ('a,'b) term
  | VLink of ('a,'b) variable
  | FLink

and ('a,'b) variable =
  {
    label : string;
    index : int;
    mutable link : ('a, 'b) link;
    quantifier : quantifier;
    var_type : 'a
  }

and ('a,'b) term =
  | Func of symbol * ('a,'b) term list
  | Var of ('a,'b) variable
  | AxName of 'b

type protocol_term = (fst_ord, name) term

type recipe = (snd_ord, axiom) term

type fst_ord_variable = (fst_ord, name) variable

type snd_ord_variable = (snd_ord, axiom) variable

type display_renamings =
  {
    rho_name : (name * name) list;
    rho_fst_var : (fst_ord_variable * fst_ord_variable) list;
    rho_snd_var : (snd_ord_variable * snd_ord_variable) list
  }

let generate_display_renaming names fst_vars snd_vars =

  let rec organise_names n = function
    | [] -> [n.label_n,[n]]
    | (str,l)::q when str = n.label_n -> (str,n::l)::q
    | t::q -> t::(organise_names n q)
  in

  let rec organise_variables var = function
    | [] -> [var.label,[var]]
    | (str,l)::q when str = var.label -> (str,var::l)::q
    | t::q -> t::(organise_variables var q)
  in

  let organised_names:(string* name list) list = List.fold_left (fun acc n -> organise_names n acc) [] names in
  let organised_fst_vars = List.fold_left (fun acc v -> organise_variables v acc) [] fst_vars in
  let organised_snd_vars = List.fold_left (fun acc v -> organise_variables v acc) [] snd_vars in

  let rec create_rho_names : (string * name list) list -> (name * name) list = function
    | [] -> []
    | (str,l)::q ->
        begin match l with
          | [] -> Config.internal_error "[term.ml >> generate_display_renaming] Unexpected case 1"
          | [n] -> (n,{ label_n = str; bound = n.bound; index_n = 0; link_n = NNoLink })::(create_rho_names q)
          | _ ->
            let (new_l,_) =
              List.fold_left (fun (acc,i) n ->
                ((n,{ label_n = str; bound = n.bound; index_n = i; link_n = NNoLink })::acc,i+1)
              ) (create_rho_names q, 1) l in
            new_l
        end
  in

  let rec create_rho_variables = function
    | [] -> []
    | (str,l)::q ->
        begin match l with
          | [] -> Config.internal_error "[term.ml >> generate_display_renaming] Unexpected case 2"
          | [n] -> (n,{ label = str; var_type = n.var_type; index = 0; link = NoLink; quantifier = n.quantifier })::(create_rho_variables q)
          | _ ->
            let (new_l,_) =
              List.fold_left (fun (acc,i) n ->
                ((n,{ label = str; var_type = n.var_type; index = i; link = NoLink; quantifier = n.quantifier })::acc,i+1)
              ) (create_rho_variables q, 1) l in
            new_l
        end
  in

  {
    rho_name = create_rho_names organised_names;
    rho_fst_var = create_rho_variables organised_fst_vars;
    rho_snd_var = create_rho_variables organised_snd_vars
  }

let generate_display_renaming_for_testing names fst_vars snd_vars =
  let rec partition_vars = function
    | [] -> [],[],[]
    | x::q when x.quantifier = Free ->
        let (free,exis,univ) = partition_vars q in
        (x::free, exis, univ)
    | x::q when x.quantifier = Existential ->
        let (free,exis,univ) = partition_vars q in
        (free, x::exis, univ)
    | x::q ->
        let (free,exis,univ) = partition_vars q in
        (free, exis,x::univ)
  in

  let (free_fst_vars,exist_fst_vars,univ_fst_vars) = partition_vars fst_vars
  and (free_snd_vars,exist_snd_vars,univ_snd_vars) = partition_vars snd_vars
  and public_names, bound_names = List.partition (fun n -> n.bound = Public) names in

  let std_p_names = ["a";"b";"c"]
  and std_b_names = ["k";"l";"m"]
  and std_fst_vars_U = ["z"]
  and std_snd_vars_U = ["Z"]
  and std_fst_vars_E = ["x";"y"]
  and std_snd_vars_E = ["X";"Y"]
  and std_fst_vars_F = ["w"]
  and std_snd_vars_F = ["W"] in

  let rec generate_names full_std k std names = match std,names with
    | _,[] -> []
    | [],_ -> generate_names full_std (k+1) full_std  names
    | str::q_std,n::q -> (n,{ label_n = str; bound = n.bound; index_n = k; link_n = NNoLink })::(generate_names full_std k q_std q) in

  let rec generate_vars full_std  k std var = match std,var with
    | _,[] -> []
    | [],_ -> generate_vars full_std (k+1) full_std  var
    | str::q_std,x::q -> (x,{ label = str; quantifier = x.quantifier; index = k; link = NoLink ; var_type = x.var_type })::(generate_vars full_std  k q_std q) in

  {
    rho_name = (generate_names std_p_names 0 std_p_names public_names)@(generate_names std_b_names 0 std_b_names bound_names);
    rho_fst_var = (generate_vars std_fst_vars_F 0 std_fst_vars_F free_fst_vars)@
                  (generate_vars std_fst_vars_E 0 std_fst_vars_E exist_fst_vars)@
                  (generate_vars std_fst_vars_U 0 std_fst_vars_U univ_fst_vars);
    rho_snd_var = (generate_vars std_snd_vars_F 0 std_snd_vars_F free_snd_vars)@
                  (generate_vars std_snd_vars_E 0 std_snd_vars_E exist_snd_vars)@
                  (generate_vars std_snd_vars_U 0 std_snd_vars_U univ_snd_vars)
  }

let reg_latex_1 = Str.regexp "\\([a-zA-Z0-9_]+\\)_\\([0-9]+\\)"
let reg_latex_2 = Str.regexp "_"

let display_var_name_for_latex str index =
  if index = 0
  then
    if Str.string_match reg_latex_1 str 0
    then
      let body = Str.matched_group 1 str in
      let number = Str.matched_group 2 str in
      let body' = Str.global_replace reg_latex_2 "\\_" body in
      Printf.sprintf "%s_{%s}" body' number
    else Str.global_replace reg_latex_2 "\\_" str
  else
    let str' = Str.global_replace reg_latex_2 "\\_" str in
    Printf.sprintf "%s_{%d}" str' index

(************************************
***            Variables          ***
*************************************)

module Variable = struct

  let accumulator = ref 0

  let fst_ord_type = NoType

  let snd_ord_type n = n

  let fresh_with_label q ty s =
    let var = { label = s; index = !accumulator; link = NoLink; quantifier = q; var_type = ty } in
    accumulator := !accumulator + 1;
    var

  let fresh (type a) (type b) (at:(a,b) atom) q (ty:a) = match at with
    | Protocol -> fresh_with_label q ty "_x"
    | Recipe -> fresh_with_label q ty "_X"

  let fresh_from var =
    let var = { label = var.label; index = !accumulator; link = NoLink; quantifier = var.quantifier; var_type = var.var_type } in
    accumulator := !accumulator + 1;
    var

  let rec fresh_list at q ty = function
    | 0 -> []
    | n -> (fresh at q ty)::(fresh_list at q ty (n-1))

  let rec fresh_term_list at q ty = function
    | 0 -> []
    | ar -> (Var(fresh at q ty))::(fresh_term_list at q ty (ar-1))

  let is_equal v1 v2 = v1 == v2

  let quantifier_of v = v.quantifier

  let type_of (v:snd_ord_variable) = v.var_type

  let order (type a) (type b) (at:(a,b) atom) (v1:(a,b) variable) (v2:(a,b) variable) = match at with
    | Protocol -> compare v1.index v2.index
    | Recipe ->
        begin match compare (type_of v1) (type_of v2) with
          | 0 -> compare v1.index v2.index
          | n -> n
        end

  let search_variable_in_display_renaming (type a) (type b) (at:(a,b) atom) display_op (var:(a,b) variable) = match display_op with
    | None -> var
    | Some rho ->
        begin match at with
          | Protocol ->
              begin try
                let _,var' = List.find (fun (var',_) -> var == var') rho.rho_fst_var in
                (var':(a,b) variable)
              with
                | Not_found -> (var:(a,b) variable)
              end
          | Recipe ->
              begin try
                let _,var' = List.find (fun (var',_) -> var == var') rho.rho_snd_var in
                var'
              with
                | Not_found -> (var:(a,b) variable)
              end
        end

  let display (type a) (type b) out ?(rho=None) (at:(a,b) atom) ?(v_type=false) (var:(a,b) variable) =
    let x = search_variable_in_display_renaming at rho var in

    match out with
      | Testing ->
          begin match at,v_type with
            | Recipe, true -> Printf.sprintf "_%s_%d:%d" x.label x.index x.var_type
            | _ , _ -> Printf.sprintf "_%s_%d" x.label x.index
          end
      | Terminal | Pretty_Terminal ->
          begin match at,v_type with
            | Recipe, true ->
                if x.index = 0
                then Printf.sprintf "%s:%d" x.label x.var_type
                else Printf.sprintf "%s_%d:%d" x.label x.index x.var_type
            | _ , _ ->
                if x.index = 0
                then Printf.sprintf "%s" x.label
                else Printf.sprintf "%s_%d" x.label x.index
          end
      | HTML ->
          begin match at,v_type with
            | Recipe, true ->
                if x.index = 0
                then Printf.sprintf "%s:%d" x.label x.var_type
                else Printf.sprintf "%s<sub>%d</sub>:%d" x.label x.index x.var_type
            | _ , _ ->
                if x.index = 0
                then Printf.sprintf "%s" x.label
                else Printf.sprintf "%s<sub>%d</sub>" x.label x.index
          end
      | Latex ->
          begin match at,v_type with
            | Recipe, true -> Printf.sprintf "%s\\text{:}%d" (display_var_name_for_latex x.label x.index) x.var_type
            | _ , _ -> (display_var_name_for_latex x.label x.index)
          end

  (******* Renaming *******)

  module Renaming = struct

    type ('a, 'b) t = (('a, 'b) variable * ('a, 'b) variable) list

    type ('a, 'b) domain = ('a, 'b) variable list

    (***** Link *****)

    let linked_variables_fst = (ref []: fst_ord_variable list ref)

    let linked_variables_snd = (ref []: snd_ord_variable list ref)

    let link(type a) (type b) (at:(a,b) atom) (var:(a,b) variable) (var':(a,b) variable) = match at with
      | Protocol ->
          var.link <- (VLink var');
          linked_variables_fst := var::(!linked_variables_fst)
      | Recipe ->
          var.link <- (VLink var');
          linked_variables_snd := var::(!linked_variables_snd)

    let cleanup (type a) (type b) (at:(a,b) atom) = match at with
      | Protocol ->
          List.iter (fun var -> var.link <- NoLink) !linked_variables_fst;
          linked_variables_fst := []
      | Recipe ->
          List.iter (fun var -> var.link <- NoLink) !linked_variables_snd;
          linked_variables_snd := []

    let retrieve (type a) (type b) (at:(a,b) atom) = match at with
      | Protocol -> ((!linked_variables_fst): (a,b) variable list)
      | Recipe -> ((!linked_variables_snd): (a,b) variable list)

    (****** Generation *******)

    let variable_fresh_shortcut = fresh

    let identity = []

    let fresh at vars_list quanti =
      List.map (fun x -> (x, fresh at quanti x.var_type)) vars_list

    let compose rho v1 v2 =
      Config.debug (fun () ->
        if List.exists (fun (x,y) -> is_equal x v1 || is_equal x v2 || is_equal y v1 || is_equal y v2) rho
        then Config.internal_error "[term.ml >> Variable.compose] The variables should not be already in the renaming."
      );
      (v1,v2)::rho

    let empty = []

    let add dom v =
      if List.exists (is_equal v) dom
      then dom
      else v::dom

    (******* Testting *******)

    let is_identity rho = rho = []

    let is_equal at rho_1 rho_2 =
      List.iter (fun (v,v') -> link at v v') rho_1;

      let test_1 =
        List.for_all (fun (v,v') ->
          match v.link with
            | VLink v'' when is_equal v' v'' -> true
            | _ -> false
        ) rho_2 in

      cleanup at;

      List.iter (fun (v,v') -> link at v v') rho_2;

      let test_2 =
        List.for_all (fun (v,_) ->
          match v.link with
            | VLink _ -> true
            | _ -> false
        ) rho_1 in

      cleanup at;

      test_1 && test_2

    (******* Operators ********)

    let of_list l = l

    let restrict rho domain =
      List.iter (fun v -> v.link <- FLink) domain;

      let rho' =
        List.fold_left (fun acc (v,v') ->
          match v.link with
            | FLink -> (v,v')::acc
            | NoLink -> acc
            | _ -> Config.internal_error "[term.ml >> Variable.Renaming.restrict] Unexpected link."
        ) [] rho
      in

      List.iter (fun v -> v.link <- NoLink) domain;
      rho'

    let apply_variable v = match v.link with
      | VLink v' -> v'
      | NoLink -> v
      | _ -> Config.internal_error "[term.ml >> Variable.Renaming.apply_variable] Unexpected link"

    let rec apply_term = function
      | Var(v) ->
          begin match v.link with
            | VLink(v') -> Var(v')
            | NoLink -> Var v
            | _ -> Config.internal_error "[term.ml >> Variable.Renaming.apply_term] Unexpected link"
          end
      | Func(f,args) -> Func(f, List.map apply_term args)
      | term -> term

    let apply rho elt f_map_elt =
      Config.debug (fun () ->
        if List.exists (fun (v,_) -> v.link <> NoLink) rho
        then Config.internal_error "[term.ml >> Variable.Renaming.apply] Variables in the domain should not be linked"
      );

      (* Link the variables of the renaming *)
      List.iter (fun (v,v') -> v.link <- (VLink v')) rho;

      try
        (* Apply the renaming on the element *)
        let new_elt = f_map_elt elt apply_variable in

        (* Unlink the variables of the renaming *)
        List.iter (fun (v,_) -> v.link <- NoLink) rho;

        new_elt
      with exc ->
        (* Unlink the variables of the renaming *)
        List.iter (fun (v,_) -> v.link <- NoLink) rho;
        raise exc

    let apply_on_terms rho elt f_map_elt =
      Config.debug (fun () ->
        if List.exists (fun (v,_) -> v.link <> NoLink) rho
        then Config.internal_error "[term.ml >> Variable.Renaming.apply] Variables in the domain should not be linked"
      );

      (* Link the variables of the renaming *)
      List.iter (fun (v,v') -> v.link <- (VLink v')) rho;

      try
        (* Apply the renaming on the element *)
        let new_elt = f_map_elt elt apply_term in

        (* Unlink the variables of the renaming *)
        List.iter (fun (v,_) -> v.link <- NoLink) rho;

        new_elt
      with exc ->
        (* Unlink the variables of the renaming *)
        List.iter (fun (v,_) -> v.link <- NoLink) rho;
        raise exc

    let inverse rho = List.map (fun (x,y) -> (y,x)) rho

    let rec rename_term : 'a 'b. ('a,'b) atom -> quantifier -> 'a -> ('a,'b) term -> ('a,'b) term = fun (type a) (type b) (at:(a,b) atom) quantifier (ord_type:a) (t:(a,b) term) -> match t with
      | Var(v) ->
          begin match v.link with
            | VLink(v') -> Var(v')
            | NoLink ->
                let v' = variable_fresh_shortcut at quantifier ord_type in
                link at v v';
                Var(v')
            | _ -> Config.internal_error "[term.ml >> Subst.Renaming.rename] Unexpected link"
          end
      | Func(f,args) -> Func(f, List.map (rename_term at quantifier ord_type) args)
      | term -> term

    (******** Display *********)

    let display out ?(rho=None) at ?(v_type=false) subst =
      let display_element (x,t) =
        Printf.sprintf "%s %s %s" (display out ~rho:rho at ~v_type:v_type x) (rightarrow out) (display out ~rho:rho at ~v_type:v_type t)
      in

      if subst = []
      then emptyset out
      else Printf.sprintf "%s %s %s" (lcurlybracket out) (display_list display_element "; " subst) (rcurlybracket out)

  end
end

(*************************************
***             Names              ***
**************************************)

module Name = struct

  let accumulator = ref 0

  let fresh_with_label b n =
    let name = { label_n = n; bound = b; index_n = !accumulator; link_n = NNoLink } in
    accumulator := !accumulator + 1;
    name

  let fresh b = fresh_with_label b "n"

  let fresh_from name = fresh_with_label name.bound name.label_n

  let is_equal n1 n2 = n1 == n2

  let is_public n = n.bound = Public

  let order n1 n2 = compare n1.index_n n2.index_n

  (***** Link *****)

  let linked_names = ref []

  let link_search n =
    n.link_n <- NLinkSearch;
    linked_names := n :: !linked_names

  let cleanup_search () =
    List.iter (fun n -> n.link_n <- NNoLink) !linked_names;
    linked_names := []

  let retrieve_search () = !linked_names

  (****** Display *******)

  let search_name_in_display_renaming display_op name = match display_op with
    | None -> name
    | Some rho ->
        begin try
          let _,name' = List.find (fun (name',_) -> name == name') rho.rho_name in
          name'
        with
          | Not_found -> name
        end

  let display out ?(rho=None) name =
    let n' = search_name_in_display_renaming rho name in

    match out with
      | Testing -> Printf.sprintf "_%s_%d" n'.label_n n'.index_n
      | Terminal | Pretty_Terminal ->
          if n'.index_n = 0
          then Printf.sprintf "%s" n'.label_n
          else Printf.sprintf "%s_%d" n'.label_n n'.index_n
      | HTML ->
          if n'.index_n = 0
          then Printf.sprintf "%s" n'.label_n
          else Printf.sprintf "%s<sub>%d</sub>" n'.label_n n'.index_n
      | Latex -> (display_var_name_for_latex n'.label_n n'.index_n)

  (***** Renaming *****)

  module Renaming = struct

    type t = (name * name) list

    type domain = name list

    let linked_names = ref []

    let link n n' =
      n.link_n <- NLink n';
      linked_names := n :: !linked_names

    let cleanup () =
      List.iter (fun n -> n.link_n <- NNoLink) !linked_names;
      linked_names := []

    (**** Generation *****)

    let identity = []

    let fresh name_list bound =
      List.map (fun x -> (x, fresh bound)) name_list

    let compose rho n1 n2 =
      Config.debug (fun () ->
        if List.exists (fun (x,y) -> is_equal x n1 || is_equal x n2 || is_equal y n1 || is_equal y n2) rho
        then Config.internal_error "[term.ml >> Name.compose] The names should not be already in the renaming."
      );
      (n1,n2)::rho

    let empty = []

    let add dom n =
      if List.exists (is_equal n) dom
      then dom
      else n::dom

    (***** Testing *****)

    let is_identity rho = rho = []

    let is_equal rho_1 rho_2 =
      let length_1 = ref 0
      and length_2 = ref 0 in

      List.iter (fun (n,n') -> link n n'; length_1 := !length_1 + 1) rho_1;

      let test =
        List.for_all (fun (n,n') ->
          match n.link_n with
            | NLink n'' when is_equal n' n'' -> length_2 := !length_2 + 1; true
            | _ -> false
        ) rho_2 in

      cleanup ();

      (* Important to do the length test after the test on names *)
      test && !length_1 = !length_2

    (***** Operators *****)

    let of_list l = l

    let restrict rho domain =
      List.iter (fun n -> n.link_n <- NLinkSearch) domain;

      let rho' =
        List.fold_left (fun acc (n,n') ->
          match n.link_n with
            | NLinkSearch -> (n,n')::acc
            | NNoLink -> acc
            | _ -> Config.internal_error "[term.ml >> Name.Renaming.restrict] Unexpected link."
        ) [] rho
      in

      List.iter (fun n -> n.link_n <- NNoLink) domain;
      rho'

    let rec apply_term = function
      | AxName n ->
          begin match n.link_n with
            | NLink n' -> AxName n'
            | NNoLink -> AxName n
            | _ -> Config.internal_error "[term.ml >> Name.Renaming.apply_term] Unexpected link."
          end
      | Func(f,args) -> Func(f, List.map apply_term args)
      | term -> term

    let apply_on_terms rho elt f_map_elt =
      Config.debug (fun () ->
        if List.exists (fun (n,_) -> n.link_n <> NNoLink) rho
        then Config.internal_error "[term.ml >> Name.apply_on_terms] Names in the domain should not be linked"
      );

      (* Link the names of the renaming *)
      List.iter (fun (n,n') -> n.link_n <- (NLink n')) rho;

      try
        (* Apply the renaming on the element *)
        let new_elt = f_map_elt elt apply_term in

        (* Unlink the variables of the renaming *)
        List.iter (fun (n,_) -> n.link_n <- NNoLink) rho;

        new_elt
      with exc ->
        (* Unlink the variables of the renaming *)
        List.iter (fun (n,_) -> n.link_n <- NNoLink) rho;
        raise exc

    let display out ?(rho=None) subst =
      let display_element (x,t) =
        Printf.sprintf "%s %s %s" (display out ~rho:rho x) (rightarrow out) (display out ~rho:rho t)
      in

      if subst = []
      then emptyset out
      else Printf.sprintf "%s %s %s" (lcurlybracket out) (display_list display_element "; " subst) (rcurlybracket out)
  end
end

(*************************************
***            Axioms              ***
**************************************)

module Axiom = struct

  let create i =
    if i <= 0
    then Config.internal_error "[term.ml >> Axiom.create] An axiom should always be positive";
    {
      id_axiom = i;
      public_name = None
    }

  let of_public_name n k =
    Config.debug (fun () ->
      if k > 0
      then Config.internal_error "[term.ml >> Axiom.of_public_name] A public name should always be linked to an axiom with a negative index."
    );
    {
      id_axiom = k;
      public_name = Some n
    }

  let of_public_names_list n_list =
    let acc = ref 0 in
    List.rev_map (fun n ->
      Config.debug (fun () ->
        if n.bound = Bound
        then Config.internal_error "[term.ml >> Axiom.of_public_names] The names should not be bound."
      );

      let old_acc = !acc in
      acc := !acc - 1;
      { id_axiom = old_acc ; public_name = Some n }
    ) n_list

  let order ax1 ax2 = compare ax1.id_axiom ax2.id_axiom

  let index_of ax = ax.id_axiom

  let is_equal ax1 ax2 = ax1 = ax2

  let display out ?(rho=None) ?(both=false) ax = match ax.public_name with
    | None ->
        begin match out with
          | Testing -> Printf.sprintf "_ax_%d" ax.id_axiom
          | Terminal | Pretty_Terminal -> Printf.sprintf "ax_%d" ax.id_axiom
          | HTML -> Printf.sprintf "ax<sub>%d</sub>" ax.id_axiom
          | Latex -> Printf.sprintf "\\mathsf{ax}_{%d}" ax.id_axiom
        end
    | Some n ->
        let n' = Name.search_name_in_display_renaming rho n in
        if both
        then
          match out with
            | Testing -> Printf.sprintf "_ax_%d[%s]" ax.id_axiom (Name.display out ~rho:rho n')
            | Terminal | Pretty_Terminal ->  Printf.sprintf "ax_%d[%s]" ax.id_axiom (Name.display out ~rho:rho n')
            | HTML -> Printf.sprintf "ax<sub>%d</sub>[%s]" ax.id_axiom (Name.display out ~rho:rho n')
            | Latex -> Printf.sprintf "\\ax_{%d}[%s]" ax.id_axiom (Name.display out ~rho:rho n')
        else
          match out with
            | Testing -> Printf.sprintf "_ax_%d" ax.id_axiom
            | _ -> Name.display out ~rho:rho n'
end


(*********************************
***           Symbol           ***
**********************************)

module Symbol = struct
  (********* Set of function symbols *********)

  let all_constructors = ref []

  let all_destructors = ref []

  let all_tuple = ref []

  let number_of_constructors = ref 0

  let number_of_destructors = ref 0

  let all_projection = Hashtbl.create 7

  let empty_signature () =
    all_constructors := [];
    all_destructors := [];
    all_tuple := [];
    number_of_constructors :=0;
    number_of_destructors := 0;
    Hashtbl.reset all_projection

  (********* Symbols functions *********)

  let is_equal sym_1 sym_2 =
    sym_1 == sym_2

  let is_constructor sym =
    sym.cat = Constructor || sym.cat = Tuple

  let is_tuple sym =
    sym.cat = Tuple

  let is_destructor sym = match sym.cat with
    | Destructor _ -> true
    | _ -> false

  let reg_proj = Str.regexp "proj_{\\([0-9]+\\),\\([0-9]+\\)}"

  let is_proj sym = Str.string_match reg_proj sym.name 0

  let get_arity sym = sym.arity

  let order sym_1 sym_2 = compare sym_1.name sym_2.name

  (********* Tuple ************)

  let nth_projection symb_tuple i = match symb_tuple.cat with
    | Tuple ->
        let ar = symb_tuple.arity in
        (Hashtbl.find all_projection ar).(i-1)
    | _ -> Config.internal_error "[term.ml >> Symbol.nth_projection] The function symbol should be a tuple"

  let get_projections symb_tuple = match symb_tuple.cat with
    | Tuple -> Array.to_list (Hashtbl.find all_projection (symb_tuple.arity))
    | _ -> Config.internal_error "[term.ml >> Symbol.get_projections] The function symbol should be a tuple"

  (********* Addition ************)

  let new_constructor ar s =
    let symb = { name = s; arity = ar; cat = Constructor } in
    all_constructors := List.sort order (symb::!all_constructors);
    number_of_constructors := !number_of_constructors + 1;
    symb

  let new_destructor ar s rw_rules =
    let symb = { name = s; arity = ar; cat = Destructor rw_rules } in
    all_destructors := List.sort order (symb::!all_destructors);
    number_of_destructors := !number_of_destructors + 1;
    symb

  let new_projection tuple_symb i =
    let args = Variable.fresh_term_list Protocol Existential Variable.fst_ord_type tuple_symb.arity in
    let x = List.nth args i in
    {
      name = (Printf.sprintf "proj_{%d,%d}" (i+1) tuple_symb.arity);
      arity = 1;
      cat = Destructor([([Func(tuple_symb,args)],x)])
    }

  let get_tuple ar =
    try
      List.find (fun symb -> symb.arity = ar) !all_tuple
    with Not_found ->
      begin
        let symb = { name = "tuple"; arity = ar; cat = Tuple } in
        all_constructors := List.sort order (symb::!all_constructors);
        all_tuple := symb::!all_tuple;
        number_of_constructors := !number_of_constructors + 1;

        let array_proj = Array.init ar (new_projection symb) in
        Hashtbl.add all_projection ar array_proj;

        let rec add_proj = function
          | 0 -> all_destructors := List.sort order ((array_proj.(0))::!all_destructors)
          | n -> all_destructors := List.sort order ((array_proj.(n))::!all_destructors); add_proj (n-1)
        in

        add_proj (ar-1);
        number_of_destructors := ar + !number_of_destructors;
        symb
      end;;

  (******** Display function *******)

  let display out f =
    if Str.string_match reg_proj f.name 0
    then
      match out with
        | HTML ->
            let i1 = Str.matched_group 1 f.name in
            let i2 = Str.matched_group 2 f.name in
            Printf.sprintf "proj<sub>%s,%s</sub>" i1 i2
        | _ -> f.name
    else
      match out with
        | Latex ->
            if Str.string_match reg_latex_1 f.name 0
            then
              let body = Str.matched_group 1 f.name in
              let number = Str.matched_group 2 f.name in
              let body' = Str.global_replace reg_latex_2 "\\_" body in
              Printf.sprintf "%s_{%s}" body' number
            else Str.global_replace reg_latex_2 "\\_" f.name
        | _ -> f.name

  let display_with_arity out f =
    Printf.sprintf "%s/%d" (display out f) f.arity

  let display_tuple f = string_of_int (f.arity)

  let display_signature out = match out with
    | Testing ->
        let without_tuple = List.filter (fun f -> f.cat <> Tuple) !all_constructors in
        let str_without_tuple = Printf.sprintf "{ %s }" (display_list (display_with_arity Testing) ", " without_tuple) in
        let str_tuple = Printf.sprintf "{ %s }" (display_list display_tuple ", " !all_tuple) in
        str_without_tuple^" Tuple : "^str_tuple
    | _ ->
        let without_tuple = List.filter (fun f -> f.cat <> Tuple) !all_constructors in
        if without_tuple = []
        then emptyset out
        else Printf.sprintf "%s %s %s" (lcurlybracket out) (display_list (display_with_arity out) ", " without_tuple) (rcurlybracket out)

end

(*************************************
***              Terms             ***
**************************************)

module AxName = struct

  let is_equal axn1 axn2 = axn1 == axn2

  let order (type a) (type b) (at:(a,b) atom) (axn1:b) (axn2:b) = match at with
    | Protocol -> compare axn1.index_n axn2.index_n
    | Recipe -> compare axn1.id_axiom axn2.id_axiom

  let display (type a) (type b) out ?(rho=None) (at:(a,b) atom) (axn:b) = match at with
    | Protocol -> Name.display out ~rho:rho axn
    | Recipe -> Axiom.display out ~rho:rho  axn
end

(********* Generation of terms *********)

let of_variable var = Var(var)

let of_name name = AxName(name)

let of_axiom ax = AxName(ax)

let variable_of term = match term with
  | Var(var) -> var
  | _ -> Config.internal_error "[term.ml >> variable_of] The term should be a variable"

let name_of term = match term with
  | AxName(name) -> name
  | _ -> Config.internal_error "[term.ml >> name_of] The term should be a name"

let axiom_of term = match term with
  | AxName(name) -> name
  | _ -> Config.internal_error "[term.ml >> axiom_of] The term should be an axiom"

let apply_function symbol list_sons =
  Config.debug (fun () ->
    if (List.length list_sons) <> symbol.arity
    then Config.internal_error (Printf.sprintf "[term.ml >> apply_function] The function %s has arity %d but is given %d terms" symbol.name symbol.arity (List.length list_sons))
  );

  Func(symbol,list_sons)

(********* Access Functions *********)

let root = function
  | Func(s,_) -> s
  | _ -> Config.internal_error "[terms.ml >> root] The term is not a function application."

let nth_args t i = match t with
  | Func(s,_) when s.arity = 0 -> Config.internal_error "[terms.ml >> nth_args] The term should not be a constant."
  | Func(s,l) ->
      begin try
        List.nth l (i-1)
      with Failure _ -> Config.internal_error (Printf.sprintf "[terms.ml >> nth_args] The root %s of the term has arity %d but %d is given as second argument. The second argument should be between 1 and %d." s.name s.arity i s.arity)
      end
  | _ -> Config.internal_error "[terms.ml >> nth_args] The term is not a function application."

let get_args = function
  | Func(s,_) when s.arity = 0 -> Config.internal_error "[terms.ml >> get_args] The term should not be a constant."
  | Func(_,l) -> l
  | _ -> Config.internal_error "[terms.ml >> get_args] The term is not a function application."

let rec get_type = function
  | Func(_,args) -> List.fold_left (fun k r -> max k (get_type r)) 0 args
  | Var v -> Variable.type_of v
  | AxName ax -> Axiom.index_of ax


let rec order at t1 t2 = match t1,t2 with
  | Var v1, Var v2 -> Variable.order at v1 v2
  | AxName n1, AxName n2 -> AxName.order at n1 n2
  | Func(f1,args1), Func(f2,args2) ->
      let ord = Symbol.order f1 f2 in
      if ord <> 0
      then ord
      else order_list at args1 args2
  | Var _, _ -> -1
  | AxName _, Var _ -> 1
  | AxName _, _ -> -1
  | _ , _ -> 1

and order_list at l1 l2 = match l1, l2 with
  | [], [] -> 0
  | [],_ | _,[] -> Config.internal_error "[terms.ml >> order_list] The lists should be of equal size."
  | t1::q1, t2::q2 ->
      let ord = order at t1 t2 in
      if ord <> 0
      then ord
      else order_list at q1 q2

(********* Scanning Functions *********)

let rec is_ground = function
  | Func (_, tlist)  -> List.for_all is_ground tlist
  | Var _ -> false
  | AxName _ -> true

let rec no_axname = function
  | Var _ -> true
  | AxName _ -> false
  | Func (_,tlist) -> List.for_all no_axname tlist

(* In the function var_occurs and name_occurs, we go through the TLink when there is one. *)
let rec var_occurs var = function
  | Var(v) when Variable.is_equal v var -> true
  | Var({link = TLink t; _}) -> var_occurs var t
  | Func(_,args) -> List.exists (var_occurs var) args
  | _ -> false

(* [var_occurs_or_wrong_type] {% $\quanti{X}{i}$ $\xi$ %} returns [true] iff {% $X \in \varsdeux{\xi}$ or $\xi \not\in \T(\F,\AX_i \cup \Xdeux_i)$. %} *)
let rec var_occurs_or_out_of_world (var:snd_ord_variable) (r:recipe) = match r with
  | Var(v) when Variable.is_equal v var -> true
  | Var({link = TLink t; _}) -> var_occurs_or_out_of_world var t
  | Var(v) when v.var_type > var.var_type -> true
  | AxName(ax) when ax.id_axiom > var.var_type -> true
  | Func(_,args) -> List.exists (var_occurs_or_out_of_world var) args
  | _ -> false

let rec quantified_var_occurs quantifier = function
  | Var(v) when Variable.quantifier_of v = quantifier-> true
  | Var({link = TLink t; _}) -> quantified_var_occurs quantifier t
  | Func(_,args) -> List.exists (quantified_var_occurs quantifier) args
  | _ -> false

let rec name_occurs n = function
  | AxName(n') when Name.is_equal n n' -> true
  | Var({link = TLink t; _}) -> name_occurs n t
  | Func(_,args) -> List.exists (name_occurs n) args
  | _ -> false

let rec axiom_occurs n = function
  | AxName(n') when Axiom.is_equal n n' -> true
  | Var({link = TLink t; _}) -> axiom_occurs n t
  | Func(_,args) -> List.exists (axiom_occurs n) args
  | _ -> false

(* In the function is_equal on the other hand, we do not go through the TLink. *)
let rec is_equal t1 t2 = match t1,t2 with
  | Var(v1),Var(v2) when Variable.is_equal v1 v2 -> true
  | AxName(n1),AxName(n2) when AxName.is_equal n1 n2 -> true
  | Func(f1,args1), Func(f2,args2) when Symbol.is_equal f1 f2 -> List.for_all2 is_equal args1 args2
  | _,_ -> false

let is_variable = function
  | Var(_) -> true
  | _ -> false

let is_name = function
  | AxName(_) -> true
  | _ -> false

let is_axiom = function
  | AxName(_) -> true
  | _ -> false

let is_function = function
  | Func(_,_) -> true
  | _ -> false

let rec is_constructor = function
  | Func({cat = Destructor _; _},_) -> false
  | Func(_,args) -> List.for_all is_constructor args
  | _ -> true

(********* Iterators *********)

let fold_left_args f_acc acc = function
  | Func(_,l) -> List.fold_left f_acc acc l
  | _ -> Config.internal_error "[terms.ml >> PTerm.fold_left_args] The term is not a function application"

let fold_right_args f_acc term acc = match term with
  | Func(_,l) -> List.fold_right f_acc l acc
  | _ -> Config.internal_error "[terms.ml >> PTerm.fold_right_args] The term is not a function application"

let map_args f_map = function
  | Func(_,l) -> List.map f_map l
  | _ -> Config.internal_error "[terms.ml >> PTerm.map_args] The term is not a function application"

let fold_left_args2 f_acc acc term l = match term with
  | Func(_,l_args) ->
      List.fold_left2 f_acc acc l_args l
  | _ -> Config.internal_error "[terms.ml >> PTerm.fold_left_args2] The term is not a function application"

let fold_left_args3 f_acc acc term1 term2 = match term1,term2 with
  | Func(f1,args1),Func(f2,args2) when Symbol.is_equal f1 f2 ->
      List.fold_left2 f_acc acc args1 args2
  | Func _, Func _ -> Config.internal_error "[terms.ml >> PTerm.fold_left_args3] The terms do not have the same root symbol"
  | Func _, _ -> Config.internal_error "[terms.ml >> PTerm.fold_left_args3] The second term is not a function application"
  | _, Func _-> Config.internal_error "[terms.ml >> PTerm.fold_left_args3] The first term is not a function application"
  | _,_ -> Config.internal_error "[terms.ml >> PTerm.fold_left_args3] The terms are not a function application"


(******* Search ******)

let linked_variables_search_fst = (ref []: fst_ord_variable list ref)

let linked_variables_search_snd = (ref []: snd_ord_variable list ref)

let link_search (type a) (type b) (at:(a,b) atom) (var:(a,b) variable) = match at with
  | Protocol ->
      var.link <- FLink;
      linked_variables_search_fst := var::(!linked_variables_search_fst)
  | Recipe ->
      var.link <- FLink;
      linked_variables_search_snd := var::(!linked_variables_search_snd)

let cleanup_search (type a) (type b) (at:(a,b) atom) = match at with
  | Protocol ->
      List.iter (fun var -> var.link <- NoLink) !linked_variables_search_fst;
      linked_variables_search_fst := []
  | Recipe ->
      List.iter (fun var -> var.link <- NoLink) !linked_variables_search_snd;
      linked_variables_search_snd := []

let retrieve_search (type a) (type b) (at:(a,b) atom) = match at with
  | Protocol -> ((!linked_variables_search_fst): (a,b) variable list)
  | Recipe -> ((!linked_variables_search_snd): (a,b) variable list)

(********** More Access *******)

let get_vars at term =

  let rec explore_term = function
    | Func (_,args) -> List.iter explore_term args
    | Var({link = FLink; _}) -> ()
    | Var v -> link_search at v
    | AxName _ -> ()
  in

  explore_term term;

  let result = retrieve_search at in
  cleanup_search at;
  result

let rec get_names_recipe f_bound = function
  | Func (_,args) -> List.iter (get_names_recipe f_bound) args
  | AxName { public_name = Some ({link_n = NNoLink; bound = b; _} as n); _ } when f_bound b -> Name.link_search n
  | AxName _ | Var _ -> ()

let rec get_names_protocol f_bound = function
  | Func (_,args) -> List.iter (get_names_protocol f_bound) args
  | AxName ({ link_n = NNoLink ; bound = b; _} as n) when f_bound b -> Name.link_search n
  | AxName _ | Var _ -> ()

let get_names_with_list (type a) (type b) (at:(a,b) atom) (term:(a,b) term) f_bound (l:name list) =

  List.iter Name.link_search l;

  begin match at with
    | Recipe -> get_names_recipe f_bound term
    | Protocol -> get_names_protocol f_bound term
  end;

  let result = Name.retrieve_search () in
  Name.cleanup_search ();
  result

let rec get_vars_term at f_quanti = function
  | Func (_,args) -> List.iter (get_vars_term at f_quanti) args
  | Var({link = FLink; _}) -> ()
  | Var v when f_quanti v.quantifier -> link_search at v
  | Var _ -> ()
  | AxName _ -> ()

let get_vars_with_list (type a) (type b) (at:(a,b) atom) (term:(a,b) term) f_quantifier (l:(a,b) variable list) =

  List.iter (link_search at) l;

  get_vars_term at f_quantifier term;

  let result = retrieve_search at in
  cleanup_search at;
  result

let rec add_axiom_in_list ax ax_list = match ax_list with
  | [] -> [ax]
  | ax'::_ when ax'.id_axiom = ax.id_axiom ->
      Config.debug (fun () ->
        if ax'.id_axiom > 0 && ax'.public_name <> None
        then Config.internal_error "[term.ml >> add_axioms_in_list] An axiom with index bigger or equal to 1 should not be linked to a public name. (2)";

        match ax.public_name, ax'.public_name with
          | Some n, Some n' when not (n == n') -> Config.internal_error "[term.ml >> add_axioms_in_list] Axioms with same index should be linked to the same public name."
          | _, _ -> ()
      );
      ax_list
  | ax'::q -> ax'::(add_axiom_in_list ax q)


let rec get_axioms_with_list recipe f_id ax_list  = match recipe with
  | AxName ax when f_id ax.id_axiom ->
      if ax.id_axiom > 0 && ax.public_name <> None
      then Config.internal_error "[term.ml >> get_axioms_with_list] An axiom with index bigger or equal to 1 should not be linked to a public name. (1)";

      add_axiom_in_list ax ax_list
  | Var _ | AxName _ -> ax_list
  | Func(_,args) -> List.fold_left (fun acc r -> get_axioms_with_list r f_id acc) ax_list args

(********** Display **********)

let rec display out ?(rho=None) at = function
  | Var(v) -> Variable.display out ~rho:rho at v
  | AxName(axn) -> AxName.display out ~rho:rho at axn
  | Func(f_symb,_) when f_symb.arity = 0 ->
      Printf.sprintf "%s" f_symb.name
  | Func(f_symb,args) when f_symb.cat = Tuple ->
      Printf.sprintf "%s%s%s" (langle out) (display_list (display out ~rho:rho at) "," args) (rangle out)
  | Func(f_symb,args) ->
      Printf.sprintf "%s(%s)" f_symb.name (display_list (display out ~rho:rho at) "," args)

(*************************************
***         Protocol terms         ***
**************************************)

module Subst = struct

  type ('a, 'b) t = (('a, 'b) variable * ('a, 'b) term) list

  (******* Tested function *********)

  let test_unify_Protocol : (((fst_ord, name) term * (fst_ord, name) term) list-> (fst_ord, name) t option -> unit) ref = ref (fun _ _ -> ())

  let test_unify_Recipe : (((snd_ord, axiom) term * (snd_ord, axiom) term) list-> (snd_ord, axiom) t option -> unit) ref = ref (fun _ _ -> ())

  let test_unify (type a) (type b) (at:(a,b) atom) (subst: ((a,b) term * (a,b) term) list) (res:(a,b) t option) = match at with
    | Protocol -> !test_unify_Protocol subst res
    | Recipe -> !test_unify_Recipe subst res

  let update_test_unify (type a) (type b) (at:(a,b) atom) (f: ((a,b) term * (a,b) term) list -> (a,b) t option -> unit) = match at with
    | Protocol -> test_unify_Protocol := f
    | Recipe -> test_unify_Recipe := f

  let test_is_matchable_Protocol : ((fst_ord, name) term list -> (fst_ord, name) term list -> bool -> unit) ref = ref (fun _ _ _ -> ())

  let test_is_matchable_Recipe : ((snd_ord, axiom) term list -> (snd_ord, axiom) term list -> bool -> unit) ref = ref (fun _ _ _ -> ())

  let test_is_matchable (type a) (type b) (at:(a,b) atom) (t_list_1: (a,b) term list) (t_list_2: (a,b) term list) res = match at with
    | Protocol -> !test_is_matchable_Protocol t_list_1 t_list_2 res
    | Recipe -> !test_is_matchable_Recipe t_list_1 t_list_2 res

  let update_test_is_matchable (type a) (type b) (at:(a,b) atom) (f: (a,b) term list -> (a,b) term list -> bool -> unit) = match at with
    | Protocol -> test_is_matchable_Protocol := f
    | Recipe -> test_is_matchable_Recipe := f

  let test_is_extended_by_Protocol : ((fst_ord, name) t -> (fst_ord, name) t -> bool -> unit) ref = ref (fun _ _ _ -> ())

  let test_is_extended_by_Recipe : ((snd_ord, axiom) t -> (snd_ord, axiom) t -> bool -> unit) ref = ref (fun _ _ _ -> ())

  let test_is_extended_by (type a) (type b) (at:(a,b) atom) (subst_1: (a,b) t) (subst_2: (a,b) t) res = match at with
    | Protocol -> !test_is_extended_by_Protocol subst_1 subst_2 res
    | Recipe -> !test_is_extended_by_Recipe subst_1 subst_2 res

  let update_test_is_extended_by (type a) (type b) (at:(a,b) atom) (f: (a,b) t -> (a,b) t -> bool -> unit) = match at with
    | Protocol -> test_is_extended_by_Protocol := f
    | Recipe -> test_is_extended_by_Recipe := f

  let test_is_equal_equations_Protocol : ((fst_ord, name) t -> (fst_ord, name) t -> bool -> unit) ref = ref (fun _ _ _ -> ())

  let test_is_equal_equations_Recipe : ((snd_ord, axiom) t -> (snd_ord, axiom) t -> bool -> unit) ref = ref (fun _ _ _ -> ())

  let test_is_equal_equations (type a) (type b) (at:(a,b) atom) (subst_1: (a,b) t) (subst_2: (a,b) t) res = match at with
    | Protocol -> !test_is_equal_equations_Protocol subst_1 subst_2 res
    | Recipe -> !test_is_equal_equations_Recipe subst_1 subst_2 res

  let update_test_is_equal_equations (type a) (type b) (at:(a,b) atom) (f: (a,b) t -> (a,b) t -> bool -> unit) = match at with
    | Protocol -> test_is_equal_equations_Protocol := f
    | Recipe -> test_is_equal_equations_Recipe := f

  (******* Generation **********)

  let identity = []

  let is_identity subst = subst = []

  let create (type a) (type b) (at:(a,b) atom) (var:(a,b) variable) (term:(a,b) term) =
    Config.debug (fun () ->
      match at with
        | Protocol ->
            if var_occurs var term
            then Config.internal_error "[term.ml >> Subst.create] The substution is not acyclic"
        | Recipe ->
            if var_occurs_or_out_of_world var term
            then Config.internal_error "[term.ml >> Subst.create] The substution is not acyclic or the types do not corresponds"
    );
    [var,term]

  let is_in_domain subst x_snd = List.exists (fun (x,_) -> Variable.is_equal x x_snd) subst

  let rec check_disjoint_domain = function
    | [] -> true
    | (x,_) :: q ->
        if (List.exists (fun (y,_) -> Variable.is_equal x y) q)
        then false
        else check_disjoint_domain q

  let create_multiple (type a) (type b) (at:(a,b) atom) (l_subst:((a,b) variable * (a,b) term) list) =
    Config.debug (fun () ->
      match at with
        | Protocol ->
            if not (check_disjoint_domain l_subst)
            then Config.internal_error "[term.ml >> Subst.create_multiple] A variable appears twice in the domain";

            if List.exists (fun (x,_) -> List.exists (fun (_,t) -> var_occurs x t) l_subst) l_subst
            then Config.internal_error "[term.ml >> Subst.create_multiple] The substution is not acyclic"
        | Recipe ->
            if not (check_disjoint_domain l_subst)
            then Config.internal_error "[term.ml >> Subst.create_multiple] A variable appears twice in the domain";

            if List.exists (fun (x,_) -> List.exists (fun (_,t) -> var_occurs x t) l_subst) l_subst
            then Config.internal_error "[term.ml >> Subst.create_multiple] The substution is not acyclic";

            if List.exists (fun (x,t) -> var_occurs_or_out_of_world x t) l_subst
            then Config.internal_error "[term.ml >> Subst.create_multiple] The substitution is not unifiable (type issue)"
    );

    l_subst

  let split_domain subst f = List.partition (fun (x,_) -> f x) subst

  let of_renaming rho = List.map (fun (x,y) -> (x,Var y)) rho

  let equations_of subst = List.map (fun (x,t) -> (Var x, t)) subst

  let rec apply_on_term term = match term with
    | Func(f,args) -> Func(f, List.map apply_on_term args)
    | Var(t) ->
        begin match t.link with
          | NoLink -> term
          | TLink t' -> t'
          | _ -> Config.internal_error "[term.ml >> Subst.apply_on_term] Unexpected link"
        end
    | _ -> term

  let apply subst elt f_iter_elt =
    Config.debug (fun () ->
      if List.exists (fun (v,_) -> v.link <> NoLink) subst
      then Config.internal_error "[term.ml >> Subst.apply_substitution] Variables in the domain should not be linked"
    );

    (* Link the variables of the substitution *)
    List.iter (fun (v,t) -> v.link <- (TLink t)) subst;

    try
      (* Apply the substitution on the element *)
      let new_elt = f_iter_elt elt apply_on_term in

      (* Unlink the variables of the substitution *)
      List.iter (fun (v,_) -> v.link <- NoLink) subst;

      new_elt
    with exc ->
      (* Unlink the variables of the substitution *)
      List.iter (fun (v,_) -> v.link <- NoLink) subst;
      raise exc

  (*********** Iterators ************)

  let fold f elt subst = List.fold_left (fun e (x,t) -> f e x t) elt subst

  (*********** Access ************)

  let get_names_with_list (type a) (type b) (at:(a,b) atom) (subst:(a,b) t) f_bound (l:name list) =

    List.iter Name.link_search l;

    begin match at with
      | Recipe -> List.iter (fun (_,t) -> get_names_recipe f_bound t) subst
      | Protocol -> List.iter (fun (_,t) -> get_names_protocol f_bound t) subst
    end;

    let result = Name.retrieve_search () in
    Name.cleanup_search ();
    result

  let get_vars_with_list (type a) (type b) (at:(a,b) atom) (subst:(a,b) t) f_quantifier (l:(a,b) variable list) =

    List.iter (link_search at) l;

    List.iter (fun (x,t) -> get_vars_term at f_quantifier (Var x); get_vars_term at f_quantifier t) subst;

    let result = retrieve_search at in
    cleanup_search at;
    result

  let get_axioms_with_list subst f_id ax_list  =
    List.fold_left (fun acc (_,t) -> get_axioms_with_list t f_id acc) ax_list subst

  (*********** Composition ************)

  let compose subst_1 subst_2 =
    Config.debug (fun () ->
      if List.exists (fun (x,_) -> List.exists (fun (y,_) -> Variable.is_equal x y) subst_2) subst_1
      then Config.internal_error "[term.ml >> Subst.compose] The substutions do not have the disjoint domain"
    );

    let subst = apply subst_2 subst_1 (fun s f ->
        List.map (fun (x,t) -> (x,f t)) s) in

    Config.debug (fun () ->
      if List.exists (fun (x,_) -> List.exists (fun (_,t) -> var_occurs x t) subst) subst
      then Config.internal_error "[term.ml >> Subst.compose] The resulting substution is not acyclic"
    );

    subst @ subst_2

  let compose_restricted subst_1 subst_2 =
    Config.debug (fun () ->
      if List.exists (fun (x,_) -> List.exists (fun (y,_) -> Variable.is_equal x y) subst_2) subst_1
      then Config.internal_error "[term.ml >> Subst.compose_restricted] The substutions do not have the disjoint domain"
    );

    let subst = apply subst_2 subst_1 (fun s f ->
        List.map (fun (x,t) -> (x,f t)) s) in

    Config.debug (fun () ->
      if List.exists (fun (x,_) -> List.exists (fun (_,t) -> var_occurs x t) subst) subst
      then Config.internal_error "[term.ml >> Subst.compose_restricted] The resulting substution is not acyclic"
    );

    subst

  let compose_restricted_generic subst_1 subst_2 f =
    Config.debug (fun () ->
      if List.exists (fun (x,_) -> List.exists (fun (y,_) -> Variable.is_equal x y) subst_2) subst_1
      then Config.internal_error "[term.ml >> Subst.compose_restricted_generic] The substutions do not have the disjoint domain"
    );

    let subst = apply subst_2 subst_1 (fun s f ->
        List.map (fun (x,t) -> (x,f t)) s) in

    Config.debug (fun () ->
      if List.exists (fun (x,_) -> List.exists (fun (_,t) -> var_occurs x t) subst) subst
      then Config.internal_error "[term.ml >> Subst.compose_restricted_generic] The resulting substution is not acyclic"
    );

    subst @ (List.filter (fun (x,_) -> f x) subst_2)

  let restrict subst f =
    List.filter (fun (x,_) -> f x) subst

  let is_extended_by (type a) (type b) (at:(a,b) atom) (subst_1:(a,b) t) (subst_2:(a,b) t) =

    let subst = apply subst_2 subst_1 (fun s f ->
        List.map (fun (x,t) -> (x,f t)) s) in

    List.iter (fun (x,t) -> x.link <- TLink t) subst;

    let result =
      List.for_all (fun (x,t)->
        match x.link with
          | NoLink -> true
          | TLink t' -> is_equal t t'
          | _ -> Config.internal_error "[terml.ml >> Subst.is_extended_by] Unexpected link."
      ) subst_2 in

    List.iter (fun (x,_) -> x.link <- NoLink) subst;

    Config.test (fun () -> test_is_extended_by at subst_1 subst_2 result);

    result

  (*********** Display ************)

  let display out ?(rho=None) at subst =
    let display_element (x,t) =
      Printf.sprintf "%s %s %s" (Variable.display out ~rho:rho at x) (rightarrow out) (display out ~rho:rho at t)
    in

    if subst = []
    then emptyset out
    else Printf.sprintf "%s %s %s" (lcurlybracket out) (display_list display_element ", " subst) (rcurlybracket out)

  (*********** Unification **********)

  let linked_variables_fst = (ref []: fst_ord_variable list ref)

  let linked_variables_snd = (ref []: snd_ord_variable list ref)

  let link (type a) (type b) (at:(a,b) atom) (var:(a,b) variable) (term:(a,b) term) = match at with
    | Protocol ->
        var.link <- (TLink term);
        linked_variables_fst := var::(!linked_variables_fst)
    | Recipe ->
        var.link <- (TLink term);
        linked_variables_snd := var::(!linked_variables_snd)

  let cleanup (type a) (type b) (at:(a,b) atom) = match at with
    | Protocol ->
        List.iter (fun var -> var.link <- NoLink) !linked_variables_fst;
        linked_variables_fst := []
    | Recipe ->
        List.iter (fun var -> var.link <- NoLink) !linked_variables_snd;
        linked_variables_snd := []

  let retrieve (type a) (type b) (at:(a,b) atom) = match at with
    | Protocol -> ((!linked_variables_fst): (a,b) variable list)
    | Recipe -> ((!linked_variables_snd): (a,b) variable list)

  let rec follow_link = function
    | Func(f,args) -> Func(f,List.map follow_link args)
    | Var({link = TLink t;_}) -> follow_link t
    | term -> term

  (******* Syntactic unification *******)

  exception Not_unifiable

  let rec unify_term : 'a 'b. ('a,'b) atom -> ('a,'b) term -> ('a,'b) term -> unit = fun (type a) (type b) (at:(a, b) atom) (t1:(a, b) term) (t2:(a, b) term) -> match t1,t2 with
    | Var(v1), Var(v2) when Variable.is_equal v1 v2 -> ()
    | Var({link = TLink t ; _}), _ -> unify_term at t t2
    | _, Var({link = TLink t; _}) -> unify_term at t1 t
    | Var(v1),Var(v2) ->
        begin match at with
          | Protocol ->
              if v1.quantifier = Universal || (v1.quantifier = Existential && v2.quantifier = Free) || Variable.order at v1 v2 < 0
              then link at v1 t2
              else link at v2 t1
          | Recipe ->
              if v1.var_type < v2.var_type
              then link at v2 t1
              else if v1.var_type > v2.var_type
              then link at v1 t2
              else if v1.quantifier = Universal || (v1.quantifier = Existential && v2.quantifier = Free) || Variable.order at v1 v2 < 0
              then link at v1 t2
              else link at v2 t1
        end
    | Var(v1), _ ->
        begin match at with
          | Protocol -> if var_occurs v1 t2 then raise Not_unifiable else link at v1 t2
          | Recipe -> if var_occurs_or_out_of_world v1 t2 then raise Not_unifiable else link at v1 t2
        end
    | _, Var(v2) ->
        begin match at with
          | Protocol -> if var_occurs v2 t1  then raise Not_unifiable else link at v2 t1
          | Recipe -> if var_occurs_or_out_of_world v2 t1 then raise Not_unifiable else link at v2 t1
        end
    | AxName(n1), AxName(n2) when AxName.is_equal n1 n2 -> ()
    | Func(f1,args1), Func(f2,args2) ->
        if Symbol.is_equal f1 f2 then List.iter2 (unify_term at) args1 args2 else raise Not_unifiable
    | _,_ -> raise Not_unifiable

  let unify : 'a 'b. ('a,'b) atom -> (('a,'b) term * ('a, 'b) term) list -> ('a, 'b) t = fun (type a) (type b) (at:(a,b) atom) (eq_list:((a,b) term * (a,b) term) list) ->
    Config.debug (fun () ->
      if retrieve at <> []
      then Config.internal_error "[term.ml >> Subst.unify_generic] The list of linked variables should be empty"
    );

    try
      List.iter (fun (t1,t2) -> unify_term at t1 t2) eq_list;
      let subst = List.map (fun var -> (var,follow_link (Var var))) (retrieve at) in
      cleanup at;
      Config.test (fun () -> test_unify at eq_list (Some subst));
      subst
    with Not_unifiable ->
      cleanup at;
      Config.test (fun () -> test_unify at eq_list None);
      raise Not_unifiable

  let is_unifiable (type a) (type b) (at:(a,b) atom) (eq_list:((a, b) term * (a, b) term) list) =
    Config.debug (fun () ->
      if retrieve at <> []
      then Config.internal_error "[term.ml >> Subst.is_unifiable] The list of linked variables should be empty"
    );

    try
      List.iter (fun (t1,t2) -> unify_term at t1 t2) eq_list;
      cleanup at;
      true
    with Not_unifiable -> cleanup at; false

  (******* Syntactic match *******)

  exception Not_matchable

  let rec match_term : 'a 'b. ('a,'b) atom -> ('a,'b) term -> ('a,'b) term -> unit = fun (type a) (type b) (at:(a, b) atom) (t1:(a, b) term) (t2:(a, b) term) -> match t1,t2 with
    | Var({link = TLink t ; _}), _ ->
        if not (is_equal t t2)
        then raise Not_matchable
    | _, Var({link = TLink _; _}) -> Config.internal_error "[term.ml >> Subst.match_term] Unexpected link"
    | Var(v1),_ -> link at v1 t2
    | AxName(n1), AxName(n2) when AxName.is_equal n1 n2 -> ()
    | Func(f1,args1), Func(f2,args2) ->
        if Symbol.is_equal f1 f2 then List.iter2 (match_term at) args1 args2 else raise Not_matchable
    | _,_ -> raise Not_matchable

  let is_matchable at term_list1 term_list2 =
    Config.debug (fun () ->
      if retrieve at <> []
      then Config.internal_error "[term.ml >> Subst.is_matchable] The list of linked variables should be empty.";

      if List.length term_list1 <> List.length term_list2
      then Config.internal_error "[term.ml >> Subst.is_matchable] Both lists should have the same size.";
    );

    try
      List.iter2 (match_term at) term_list1 term_list2;
      cleanup at;
      Config.test (fun () -> test_is_matchable at term_list1 term_list2 true);
      true
    with Not_matchable ->
      cleanup at;
      Config.test (fun () -> test_is_matchable at term_list1 term_list2 false);
      false

  (********** is_equal_equations **********)

  let rec is_equal_linked_terms t1 t2 = match t1,t2 with
    | Var(v1),Var(v2) when Variable.is_equal v1 v2 -> true
    | Var({link = TLink t;_}), _ -> is_equal_linked_terms t t2
    | _, Var({link = TLink t;_}) -> is_equal_linked_terms t1 t
    | Var _ , _ | _ , Var _ -> false
    | AxName(n1),AxName(n2) when AxName.is_equal n1 n2 -> true
    | Func(f1,args1), Func(f2,args2) when Symbol.is_equal f1 f2 -> List.for_all2 is_equal_linked_terms args1 args2
    | _,_ -> false

  let is_equal_equations at subst_1 subst_2 =

    (* Link the variables of the substitution *)
    List.iter (fun (v,t) ->
      match t with
        | Var v' -> if Variable.order at v v' < 0 then link at v t else link at v' (Var v)
        | _ -> link at v t
    ) subst_1;

    let result = List.for_all (fun (v,t) -> is_equal_linked_terms (Var v) t) subst_2 in

    cleanup at;
    Config.test (fun () -> test_is_equal_equations at subst_1 subst_2 result);
    result
end

(***********************************
***          Disequations        ***
************************************)

module Diseq = struct

  type ('a,'b) t =
    | Top
    | Bot
    | Diseq of (('a, 'b) term * ('a, 'b) term) list

  let is_top = function
    | Top -> true
    | _ -> false

  let is_bot = function
    | Bot -> true
    | _ -> false

  (*** Access ***)

  let get_names_with_list (type a) (type b) (at:(a,b) atom) (diseq:(a,b) t) (l:name list) = match diseq with
    | Top | Bot -> l
    | Diseq diseq_l ->
        List.iter Name.link_search l;

        begin match at with
          | Recipe ->
              List.iter (fun (t1,t2) ->
                get_names_recipe (fun _ -> true) t1;
                get_names_recipe (fun _ -> true) t2
              ) diseq_l
          | Protocol ->
              List.iter (fun (t1,t2) ->
                get_names_protocol (fun _ -> true) t1;
                get_names_protocol (fun _ -> true) t2
              ) diseq_l
        end;

        let result = Name.retrieve_search () in
        Name.cleanup_search ();
        result

  let get_vars_with_list (type a) (type b) (at:(a,b) atom) (diseq:(a,b) t) (l:(a,b) variable list) = match diseq with
    | Top | Bot -> l
    | Diseq diseq_l ->
        List.iter (link_search at) l;

        List.iter (fun (t1,t2) ->
          get_vars_term at (fun _ -> true) t1;
          get_vars_term at (fun _ -> true) t2
        ) diseq_l;

        let result = retrieve_search at in
        cleanup_search at;
        result

  let get_axioms_with_list diseq ax_list  = match diseq with
    | Top | Bot -> ax_list
    | Diseq diseq_l ->
        List.fold_left (fun acc (t1,t2) ->
          get_axioms_with_list t2 (fun _ -> true) (get_axioms_with_list t1 (fun _ -> true) acc)
        ) ax_list diseq_l

  let of_substitution at sigma l =
    if sigma = []
    then Bot
    else
      begin
        List.iter (fun v -> link_search at v) l;
        let diseq = List.fold_left (fun acc (v,t) ->
          if v.link = NoLink
          then ((Var v),t)::acc
          else acc
          ) [] sigma
        in

        cleanup_search at;
        if diseq = []
        then Bot
        else Diseq diseq
      end

  let rec rename_universal_to_existential at = function
    | Var(v) when v.quantifier = Universal ->
        begin match v.link with
          | VLink(v') -> Var(v')
          | NoLink ->
              let v' = Variable.fresh_with_label Existential v.var_type v.label in
              Variable.Renaming.link at v v';
              Var(v')
          | _ -> Config.internal_error "[term.ml >> Subst.rename] Unexpected link"
        end
    | Func(f,args) -> Func(f, List.map (rename_universal_to_existential at) args)
    | term -> term

  let rec check_disjoint_domain = function
    | [] -> true
    | (x,_) :: q ->
        if (List.exists (fun (y,_) -> is_equal x y) q)
        then false
        else check_disjoint_domain q

  let substitution_of (type a) (type b) (at:(a,b) atom) (form:(a,b) t) = match form with
    | Top -> [],[]
    | Bot -> Config.internal_error "[term.ml >> Diseq.substitution_of] The disequation should not be bot."
    | Diseq diseq ->
        Config.debug (fun () ->
          if List.exists (fun (t,_) -> not (is_variable t) || Variable.quantifier_of (variable_of t) = Universal) diseq
          then Config.internal_error "[term.ml >> Diseq.substitution_of] The disequation should not be in normal form (1)";

          match at with
            | Protocol ->
                if not (check_disjoint_domain diseq)
                then Config.internal_error "[term.ml >> Diseq.substitution_of] The disequation should not be in normal form (2)";

                if List.exists (fun (x,_) -> List.exists (fun (_,t) -> var_occurs (variable_of x) t) diseq) diseq
                then Config.internal_error "[term.ml >> Diseq.substitution_of] The disequation should not be in normal form (3)"
            | Recipe ->
                if not (check_disjoint_domain diseq)
                then Config.internal_error "[term.ml >> Diseq.substitution_of] The disequation should not be in normal form (4)";

                if List.exists (fun (x,_) -> List.exists (fun (_,t) -> var_occurs (variable_of x) t) diseq) diseq
                then Config.internal_error "[term.ml >> Diseq.substitution_of] The disequation should not be in normal form (5)";

                if List.exists (fun (x,t) -> var_occurs_or_out_of_world (variable_of x) t) diseq
                then Config.internal_error "[term.ml >> Diseq.substitution_of] The disequation should not be in normal form (6)"
        );


        let subst = List.map (fun (t1,t2) -> variable_of t1, rename_universal_to_existential at t2) diseq in

        let renaming = List.map (fun var -> (var,Variable.Renaming.apply_variable var)) (Variable.Renaming.retrieve at) in
        Variable.Renaming.cleanup at;
        subst, renaming

  let rec elim_universal_variables = function
    | [] -> []
    | v::q when v.quantifier = Universal -> elim_universal_variables q
    | v::q -> ((Var v), Subst.follow_link (Var v))::(elim_universal_variables q)

  let apply_and_normalise at subst = function
    | Top -> Top
    | Bot -> Bot
    | Diseq diseq ->
        Config.debug (fun () ->
          if List.exists (fun (v,_) -> v.link <> NoLink) subst
          then Config.internal_error "[term.ml >> Diseq.apply_substitution_and_normalise] Variables in the domain should not be linked"
        );

        Config.debug (fun () ->
          if List.exists (fun (v,t) -> Variable.quantifier_of v = Universal || quantified_var_occurs Universal t) subst
          then Config.internal_error "[term.ml >> Diseq.apply_substitution_and_normalise] Variables in the substitutions should not be universal"
        );

        (* Link the variables of the substitution *)
        List.iter (fun (v,t) -> v.link <- (TLink t)) subst;

        try
          List.iter (fun (t1,t2) -> Subst.unify_term at t1 t2) diseq;

          let linked_variables = Subst.retrieve at in

          let result =
            if linked_variables = []
            then Bot
            else Diseq(elim_universal_variables linked_variables)
          in

          Subst.cleanup at;
          List.iter (fun (v,_) -> v.link <- NoLink) subst;
          result
        with Subst.Not_unifiable ->
          Subst.cleanup at;
          List.iter (fun (v,_) -> v.link <- NoLink) subst;
          Top

  let display out ?(rho=None) at = function
    | Top -> top out
    | Bot -> bot out
    | Diseq diseq ->
        begin match out with
          | Testing ->
              Config.debug (fun () ->
                if diseq = []
                then Config.internal_error "[term.ml >> Diseq.display] There should be some disequation (otherwise it should have been Bot)."
              );
              Printf.sprintf "(%s)" (
                display_list (fun (t1,t2) ->
                  Printf.sprintf "%s %s %s" (display Testing ~rho:rho at t1) (neqs Testing) (display Testing ~rho:rho at t2)
                ) (Printf.sprintf " %s " (vee Testing)) diseq
              )
          | _ ->
              let rec find_univ_var_term = function
                | Var v when v.link = FLink -> ()
                | Var v when v.quantifier = Universal ->
                    link_search at v;
                | Func(_,args) -> List.iter find_univ_var_term args
                | _ -> ()
              in

              let display_single (t1,t2) =
                Printf.sprintf "%s %s %s" (display out ~rho:rho at t1) (neqs out) (display out ~rho:rho at t2)
              in

              List.iter (fun (t1,t2) -> find_univ_var_term t1; find_univ_var_term t2) diseq;

              let found_vars = retrieve_search at in
              cleanup_search at;

              if found_vars = []
              then Printf.sprintf "%s" (display_list display_single (Printf.sprintf " %s " (vee out)) diseq)
              else Printf.sprintf "%s %s.%s" (forall out) (display_list (Variable.display out ~rho:rho  ~v_type:true at) "," found_vars) (display_list display_single (Printf.sprintf " %s " (vee out)) diseq)
        end

  let create_for_testing l = Diseq l

end

(***********************************
***     (Dis)equations Modulo    ***
************************************)

module Modulo = struct

  type equation = protocol_term * protocol_term

  type disequation = protocol_term * protocol_term

  (******* Tested function *********)

  type 'a result =
    | Top_raised
    | Bot_raised
    | Ok of 'a

  let test_syntactic_equations_of_equations : (equation list -> (fst_ord, name) Subst.t list result -> unit) ref = ref (fun _ _ -> ())

  let update_test_syntactic_equations_of_equations f = test_syntactic_equations_of_equations := f

  (****** Generation *******)

  let create_equation t1 t2 = t1,t2

  let create_disequation t1 t2 = t1,t2

  (****** Access *******)

  let get_vars_eq_with_list (t1,t2) f v_l = get_vars_with_list Protocol t1 f (get_vars_with_list Protocol t2 f v_l)

  let get_names_eq_with_list (t1,t2) f n_l = get_names_with_list Protocol t1 f (get_names_with_list Protocol t2 f n_l)

  let get_vars_diseq_with_list (t1,t2) f v_l = get_vars_with_list Protocol t1 f (get_vars_with_list Protocol t2 f v_l)

  let get_names_diseq_with_list (t1,t2) f n_l = get_names_with_list Protocol t1 f (get_names_with_list Protocol t2 f n_l)
  (****** Display *******)

  let display_equation out ?(rho=None) (t1,t2) =
    Printf.sprintf "%s %s %s" (display out ~rho:rho Protocol t1) (eqi out) (display out ~rho:rho Protocol t2)

  let display_disequation out ?(rho=None) (t1,t2) =
    Printf.sprintf "%s %s %s" (display out ~rho:rho Protocol t1) (neqi out) (display out ~rho:rho Protocol t2)

  let rec rewrite_term_list quantifier list_t next_f = match list_t with
    | [] -> next_f []
    | t::q ->
        rewrite_term quantifier t (fun t' ->
          rewrite_term_list quantifier q (fun q' -> next_f (t'::q'))
        )

  and rewrite_term quantifier t next_f = match t with
    | Func(f1,args) ->
        begin match f1.cat with
          | Constructor | Tuple ->
              rewrite_term_list quantifier args (fun args' -> next_f (Func(f1,args')))
          | Destructor (rw_rules) ->
              rewrite_term_list quantifier args (fun args' ->
                List.iter (fun (lhs,rhs) ->
                  (***[BEGIN DEBUG]***)
                  Config.debug (fun () ->
                    if !Variable.Renaming.linked_variables_fst <> []
                    then Config.internal_error "[term.ml >> Modulo.rewrite_term] The list of linked variables for renaming should be empty"
                  );
                  (***[END DEBUG]***)

                  let lhs' = List.map (Variable.Renaming.rename_term Protocol quantifier Variable.fst_ord_type) lhs in
                  let rhs' = Variable.Renaming.rename_term Protocol quantifier Variable.fst_ord_type rhs in

                  Variable.Renaming.cleanup Protocol;

                  let saved_linked_variables = !Subst.linked_variables_fst in
                  Subst.linked_variables_fst := [];

                  begin try
                    List.iter2 (Subst.unify_term Protocol) lhs' args';
                    let saved_linked_variables_from_unify = !Subst.linked_variables_fst in
                    Subst.linked_variables_fst := !Subst.linked_variables_fst @ saved_linked_variables;

                    begin try
                      next_f rhs';

                      Subst.linked_variables_fst := saved_linked_variables_from_unify;
                      Subst.cleanup Protocol;
                      Subst.linked_variables_fst := saved_linked_variables
                    with ex ->
                      Subst.linked_variables_fst := saved_linked_variables_from_unify;
                      Subst.cleanup Protocol;
                      Subst.linked_variables_fst := saved_linked_variables;
                      raise ex
                    end
                  with
                    | Subst.Not_unifiable ->
                        Subst.cleanup Protocol;
                        Subst.linked_variables_fst := saved_linked_variables
                  end
                ) rw_rules
              )
        end
    | _ -> next_f t

  exception Bot

  exception Top

  let syntactic_equations_of_equations list_eq =
    (* Retreive the variables *)
    List.iter (fun (t1,t2) -> get_vars_term Protocol (fun _ -> true) t1; get_vars_term Protocol (fun _ -> true) t2) list_eq;
    let variables_in_list_eq = retrieve_search Protocol in
    cleanup_search Protocol;

    (* Start the rewriting *)
    let substitutions_list = ref [] in

    let rec go_through_list list_eq' next_f = match list_eq' with
      | [] -> next_f ()
      | (t1,t2)::q ->
          rewrite_term Existential t1 (fun t1' ->
            rewrite_term Existential t2 (fun t2' ->
              go_through_list q (fun () ->
                let saved_linked_variables = !Subst.linked_variables_fst in
                Subst.linked_variables_fst := [];

                begin try
                  Subst.unify_term Protocol t1' t2';
                  let saved_linked_variables_from_unify = !Subst.linked_variables_fst in
                  Subst.linked_variables_fst := !Subst.linked_variables_fst @ saved_linked_variables;

                  begin try
                    next_f ();

                    Subst.linked_variables_fst := saved_linked_variables_from_unify;
                    Subst.cleanup Protocol;
                    Subst.linked_variables_fst := saved_linked_variables
                  with ex ->
                    Subst.linked_variables_fst := saved_linked_variables_from_unify;
                    Subst.cleanup Protocol;
                    Subst.linked_variables_fst := saved_linked_variables;
                    raise ex
                  end
                with
                  | Subst.Not_unifiable ->
                      Subst.cleanup Protocol;
                      Subst.linked_variables_fst := saved_linked_variables
                  | ex ->
                      Subst.cleanup Protocol;
                      Subst.linked_variables_fst := saved_linked_variables;
                      raise ex
                end
              )
            )
          )
    in

    go_through_list list_eq (fun () ->
      let subst = List.fold_left (fun acc var ->
          match var.link with
            | NoLink -> acc
            | TLink t -> (var,Subst.follow_link t)::acc
            | _ -> Config.internal_error "[term.ml >> Modulo.syntactic_equations_of_equations] Unexpected link"
        ) [] variables_in_list_eq in

      if subst = []
      then (Config.test (fun () -> !test_syntactic_equations_of_equations list_eq Top_raised); raise Top)
      else substitutions_list := subst::!substitutions_list
    );

    if !substitutions_list = []
    then (Config.test (fun () -> !test_syntactic_equations_of_equations list_eq Bot_raised); raise Bot)
    else (Config.test (fun () -> !test_syntactic_equations_of_equations list_eq (Ok !substitutions_list)); !substitutions_list)

  let syntactic_disequations_of_disequations (t1,t2) =
    let disequations_list = ref [] in

    rewrite_term Universal t1 (fun t1' ->
      rewrite_term Universal t2 (fun t2' ->

        let saved_linked_variables = !Subst.linked_variables_fst in
        Subst.linked_variables_fst := [];

        begin try
          Subst.unify_term Protocol t1' t2';
          let saved_linked_variables_from_unify = !Subst.linked_variables_fst in
          Subst.linked_variables_fst := !Subst.linked_variables_fst @ saved_linked_variables;

          let disequations = Diseq.elim_universal_variables !Subst.linked_variables_fst in

          if disequations = []
          then
            begin
              Subst.linked_variables_fst := saved_linked_variables_from_unify;
              Subst.cleanup Protocol;
              Subst.linked_variables_fst := saved_linked_variables;
              raise Bot
            end
          else
            begin
              disequations_list := (Diseq.Diseq disequations)::!disequations_list;

              Subst.linked_variables_fst := saved_linked_variables_from_unify;
              Subst.cleanup Protocol;
              Subst.linked_variables_fst := saved_linked_variables
            end
        with Subst.Not_unifiable ->
          Subst.cleanup Protocol;
          Subst.linked_variables_fst := saved_linked_variables
        end
      )
    );

    if !disequations_list = []
    then raise Top
    else !disequations_list
end

(***************************************************
***            Basic deduction facts             ***
****************************************************)

module BasicFact = struct

  type t =
    {
      var : snd_ord_variable;
      term : protocol_term
    }

  (********* Generation *********)

  let create x t = { var = x; term = t }

  (********* Access *********)

  let get_snd_ord_variable b_fact = b_fact.var

  let get_protocol_term b_fact = b_fact.term

  (********* Display *********)

  let display out ?(rho=None) ded =
    match out with
      | Latex -> Printf.sprintf "%s \\vdash^? %s" (Variable.display out ~rho:rho Recipe ~v_type:true ded.var) (display out ~rho:rho Protocol ded.term)
      | _ -> Printf.sprintf "%s %s %s" (Variable.display out ~rho:rho Recipe ~v_type:true ded.var) (vdash out) (display out ~rho:rho Protocol ded.term)

end

(***************************************************
***    Deduction and equality facts / formulas   ***
****************************************************)

module Fact = struct

  type deduction =
    {
      df_recipe : recipe;
      df_term : protocol_term
    }

  type equality =
    {
      ef_recipe_1 : recipe;
      ef_recipe_2 : recipe
    }

  type 'a t =
    | Deduction : deduction t
    | Equality : equality t

  type 'a formula =
    {
      head : 'a;
      ded_fact_list : BasicFact.t list;
      equation_subst : (fst_ord, name) Subst.t
    }

  exception Bot

  type deduction_formula = deduction formula

  type equality_formula = equality formula

  (********* Generation ********)

  let create_deduction_fact recipe term = { df_recipe = recipe; df_term = term }

  let create_equality_fact recipe_1 recipe_2 = { ef_recipe_1 = recipe_1; ef_recipe_2 = recipe_2 }

  let create (type a) (fct: a t) (head: a) b_fct_list equations =

    try
      List.iter (fun (t1,t2) -> Subst.unify_term Protocol t1 t2) equations;
      begin match fct with
        | Deduction ->
            let new_head = { head with df_term = Subst.follow_link head.df_term }
            and new_b_fct_list = List.map (fun b_fct -> { b_fct with BasicFact.term = Subst.follow_link b_fct.BasicFact.term}) b_fct_list
            and subst = List.fold_left (fun acc var -> if var.quantifier = Universal then acc else (var,Subst.follow_link (Var var))::acc ) [] (Subst.retrieve Protocol) in

            Subst.cleanup Protocol;
            ({ head = new_head; ded_fact_list = new_b_fct_list; equation_subst = subst }: a formula)
        | Equality ->
            let new_b_fct_list = List.map (fun b_fct -> { b_fct with BasicFact.term = Subst.follow_link b_fct.BasicFact.term}) b_fct_list
            and subst = List.map (fun var -> (var,Subst.follow_link (Var var))) (Subst.retrieve Protocol) in
            Subst.cleanup Protocol;
            ({ head = head; ded_fact_list = new_b_fct_list; equation_subst = subst }: a formula)
      end
    with Subst.Not_unifiable -> Subst.cleanup Protocol; raise Bot

  let create_for_testing head b_fct_list subst =
    {
      head = head;
      ded_fact_list = b_fct_list;
      equation_subst = subst
    }
  (********* Access ********)

  let get_recipe fct = fct.df_recipe

  let get_protocol_term fct = fct.df_term

  let get_both_recipes fct = fct.ef_recipe_1, fct.ef_recipe_2

  let get_head form = form.head

  let get_mgu_hypothesis form = form.equation_subst

  let get_basic_fact_hypothesis form = form.ded_fact_list

  let rec search_term = function
    | Var(v) when v.quantifier = Universal ->
        begin match v.link with
          | FLink -> ()
          | NoLink -> link_search Protocol v
          | _ -> Config.internal_error "[term.ml >> Fact.search_term] Unexpected link"
        end
    | Func(_,args) -> List.iter search_term args
    | _ -> ()

  let rec search_equation_subst = function
    | [] -> ()
    | (x,_)::_ when x.quantifier = Universal -> Config.internal_error "[term.ml >> Fact.search_equation_subst] The formula is not normalised. (1)"
    | (_,t)::q -> search_term t; search_equation_subst q



  let universal_variables form =

    search_equation_subst form.equation_subst;
    List.iter (fun b_fct -> link_search Recipe b_fct.BasicFact.var; search_term b_fct.BasicFact.term) form.ded_fact_list;

    let vars_fst = retrieve_search Protocol
    and vars_snd = retrieve_search Recipe in

    cleanup_search Protocol;
    cleanup_search Recipe;
    vars_fst, vars_snd

  (********* Testing *********)

  let is_fact psi =
    psi.ded_fact_list = [] && psi.equation_subst = []

  let is_solved psi =

    let rec go_through_ded_fact = function
      | [] -> cleanup_search Protocol; true
      | ded::q ->
          if is_variable ded.BasicFact.term
          then
            let v = variable_of ded.BasicFact.term in
            match v.link with
              | FLink -> cleanup_search Protocol; false
              | NoLink ->
                  if v.quantifier = Universal
                  then (link_search Protocol v; go_through_ded_fact q)
                  else (cleanup_search Protocol; false)
              | _ -> Config.internal_error "[term.ml >> Fact.is_solved] Unexpected link"
          else (cleanup_search Protocol; false)
    in

    Subst.is_identity psi.equation_subst && go_through_ded_fact psi.ded_fact_list

  let is_equation_free psi = Subst.is_identity psi.equation_subst

  let is_recipe_equivalent (type a) (fct:a t) (psi_1: a formula) (psi_2:a formula) = match fct with
    | Deduction -> is_equal psi_1.head.df_recipe psi_2.head.df_recipe
    | Equality ->
        is_equal psi_1.head.ef_recipe_1 psi_2.head.ef_recipe_1 &&
        is_equal psi_1.head.ef_recipe_2 psi_2.head.ef_recipe_2

  (********** Modification *********)

  let apply (type a) (fct: a t) (psi: a formula) subst_fst subst_snd =
    Config.debug (fun () ->
      if List.exists (fun (v,_) -> v.link <> NoLink) subst_fst
      then Config.internal_error "[term.ml >> Fact.apply] Variables in the domain should not be linked"
    );

    (* Link the variables of the substitution *)
    List.iter (fun (v,t) -> v.link <- (TLink t)) subst_fst;

    try
      List.iter (fun (x,t) -> Subst.unify_term Protocol (Var x) t) psi.equation_subst;

      begin match fct with
        | Deduction ->
            let head = { psi.head with df_term = Subst.follow_link psi.head.df_term }
            and ded_fact_list = List.map (fun b_fact -> { b_fact with BasicFact.term = Subst.follow_link b_fact.BasicFact.term }) psi.ded_fact_list
            and equation_subst = List.map (fun var -> (var,Subst.follow_link (Var var))) (Subst.retrieve Protocol) in

            let psi_1 = { head = head; ded_fact_list = ded_fact_list; equation_subst = equation_subst } in

            Subst.cleanup Protocol;

            (* Unlink the variables of the substitution *)
            List.iter (fun (v,_) -> v.link <- NoLink) subst_fst;

            (* Apply the second-order substitution *)

            ({ psi_1 with head = Subst.apply subst_snd psi_1.head (fun d_fact f -> { d_fact with df_recipe = f d_fact.df_recipe }) }: a formula)

        | Equality ->
            let ded_fact_list = List.map (fun b_fact -> { b_fact with BasicFact.term = Subst.follow_link b_fact.BasicFact.term }) psi.ded_fact_list
            and equation_subst = List.map (fun var -> (var,Subst.follow_link (Var var))) (Subst.retrieve Protocol) in

            let psi_1 = { psi with ded_fact_list = ded_fact_list; equation_subst = equation_subst } in

            Subst.cleanup Protocol;

            (* Unlink the variables of the substitution *)
            List.iter (fun (v,_) -> v.link <- NoLink) subst_fst;

            (* Apply the second-order substitution *)

            ({ psi_1 with head = Subst.apply subst_snd psi_1.head (fun d_fact f -> { ef_recipe_1 = f d_fact.ef_recipe_1; ef_recipe_2 = f d_fact.ef_recipe_2 }) }: a formula)
      end
    with Subst.Not_unifiable ->
      Subst.cleanup Protocol;
      (* Unlink the variables of the substitution *)
      List.iter (fun (v,_) -> v.link <- NoLink) subst_fst;
      raise Bot

  let apply_on_fact (type a) (fct: a t) (fact: a) subst_snd subst_fst = match fct with
    | Deduction ->
        let fact_1 =
          if Subst.is_identity subst_snd
          then fact
          else Subst.apply subst_snd fact (fun fact f -> {fact with df_recipe = f fact.df_recipe})
        in

        let fact_2 =
          if Subst.is_identity subst_fst
          then fact_1
          else Subst.apply subst_fst fact_1 (fun fact f -> {fact with df_term = f fact.df_term})
        in

        (fact_2:a)
    | Equality ->
        let fact_1 =
          if Subst.is_identity subst_snd
          then fact
          else Subst.apply subst_snd fact (fun fact f -> {ef_recipe_1 = f fact.ef_recipe_1; ef_recipe_2 = f fact.ef_recipe_2})
        in

        (fact_1:a)

  (********* Display functions *******)

  let display_fact (type a) out ?(rho=None) (fct:a t) (ded_ef:a) = match fct with
    | Deduction -> Printf.sprintf "%s %s %s" (display out ~rho:rho Recipe ded_ef.df_recipe) (vdash out) (display out ~rho:rho Protocol ded_ef.df_term)
    | Equality -> Printf.sprintf "%s %s %s" (display out ~rho:rho Recipe ded_ef.ef_recipe_1) (eqf out) (display out ~rho:rho Recipe ded_ef.ef_recipe_2)

  let display_deduction_fact out ?(rho=None) fct = display_fact out ~rho:rho Deduction fct

  let display_equality_fact out ?(rho=None) fct = display_fact out ~rho:rho Equality fct

  let rec find_univ_var at = function
    | Var v when v.link = FLink -> ()
    | Var v when v.quantifier = Universal -> link_search at v
    | Func(_,args) -> List.iter (find_univ_var at) args
    | _ -> ()

  let display_formula (type a) out ?(rho=None) (fct:a t) (psi:a formula) = match out with
    | Testing ->
        Printf.sprintf "%s %s %s %s %s"
          (display_fact out ~rho:rho fct psi.head)
          (lLeftarrow out)
          (display_list (BasicFact.display out ~rho:rho) (Printf.sprintf " %s " (wedge out)) psi.ded_fact_list)
          "; "
          (Subst.display out ~rho:rho Protocol psi.equation_subst)
    | _ ->
        begin

          begin match fct with
            | Deduction ->
                find_univ_var Recipe psi.head.df_recipe;
                find_univ_var Protocol psi.head.df_term
            | Equality ->
                find_univ_var Recipe psi.head.ef_recipe_1;
                find_univ_var Recipe psi.head.ef_recipe_2
          end;

          List.iter (fun bdf ->
            find_univ_var Recipe (Var bdf.BasicFact.var);
            find_univ_var Protocol bdf.BasicFact.term
          ) psi.ded_fact_list;

          List.iter (fun (t1,t2) ->
            find_univ_var Protocol (Var t1);
            find_univ_var Protocol t2
          ) psi.equation_subst;

          let forall_str =
            match retrieve_search Protocol, retrieve_search Recipe with
              | [],[] -> ""
              | [],lvr -> Printf.sprintf "%s %s." (forall out) (display_list (Variable.display out ~rho:rho Recipe ~v_type:true) "," lvr)
              | lvp, [] -> Printf.sprintf "%s %s." (forall out) (display_list (Variable.display out ~rho:rho Protocol ~v_type:true) "," lvp)
              | lvp,lvr -> Printf.sprintf "%s %s,%s." (forall out) (display_list (Variable.display out ~rho:rho Recipe ~v_type:true) "," lvr) (display_list (Variable.display out ~rho:rho Protocol ~v_type:true) "," lvp)
          in

          cleanup_search Protocol;
          cleanup_search Recipe;

          match psi.ded_fact_list, psi.equation_subst with
            | [],[] -> display_fact out ~rho:rho fct psi.head
            | _,[] -> Printf.sprintf "%s %s %s %s"
                forall_str
                (display_fact out ~rho:rho fct psi.head)
                (lLeftarrow out)
                (display_list (BasicFact.display out ~rho:rho) (Printf.sprintf " %s " (wedge out)) psi.ded_fact_list)
            | [],_ -> Printf.sprintf "%s %s %s %s"
                forall_str
                (display_fact out ~rho:rho fct psi.head)
                (lLeftarrow out)
                (display_list (fun (t1,t2) -> Printf.sprintf "%s %s %s" (display out ~rho:rho Protocol (Var t1)) (eqs out) (display out ~rho:rho Protocol t2)) (Printf.sprintf " %s " (wedge out)) psi.equation_subst)
            | _,_ -> Printf.sprintf "%s %s %s %s %s %s"
                forall_str
                (display_fact out ~rho:rho fct psi.head)
                (lLeftarrow out)
                (display_list (BasicFact.display out ~rho:rho) (Printf.sprintf " %s " (wedge out)) psi.ded_fact_list)
                (wedge out)
                (display_list (fun (t1,t2) -> Printf.sprintf "%s %s %s" (display out ~rho:rho Protocol (Var t1)) (eqs out) (display out ~rho:rho Protocol t2)) (Printf.sprintf " %s " (wedge out)) psi.equation_subst)
        end
end

(***************************************************
***    Rewrite rules   ***
****************************************************)

module Rewrite_rules = struct

  type skeleton =
    {
      variable_at_position : snd_ord_variable;
      recipe : recipe;
      p_term : protocol_term;
      basic_deduction_facts : BasicFact.t list;
      rewrite_rule : symbol * protocol_term list * protocol_term
    }

  (****** Tested functions ********)

  let test_normalise : (protocol_term -> protocol_term -> unit) ref = ref (fun _ _ -> ())

  let update_test_normalise f = test_normalise := f

  let test_skeletons : (protocol_term -> symbol -> int -> skeleton list -> unit) ref = ref (fun _ _ _ _ -> ())

  let update_test_skeletons f = test_skeletons := f

  let test_generic_rewrite_rules_formula : (Fact.deduction -> skeleton -> Fact.deduction_formula list -> unit) ref = ref (fun _ _ _ -> ())

  let update_test_generic_rewrite_rules_formula f = test_generic_rewrite_rules_formula := f

  (****** Access ******)

  let get_vars_with_list l =
    List.fold_left (fun acc f ->
      match f.cat with
        | Destructor rw_rules ->
            List.fold_left (fun acc_1 (arg_l,r) ->
              let var_arg_l = List.fold_left (fun acc_2 t -> get_vars_with_list Protocol t (fun _ -> true) acc_2) acc_1 arg_l in
              get_vars_with_list Protocol r (fun _ -> true) var_arg_l
            ) acc rw_rules
        | _ -> Config.internal_error "[term.ml >> get_vars_signature] all_destructors should only contain destructors."
    ) l !Symbol.all_destructors

  exception Found_normalise of protocol_term

  let rec internal_normalise t = match t with
    | Func(f1,args) ->
        begin match f1.cat with
          | Constructor | Tuple ->
              Func(f1, List.map internal_normalise args)
          | Destructor (rw_rules) ->
              let args' = List.map internal_normalise args in
              begin try
                List.iter (fun (lhs,rhs) ->
                  (***[BEGIN DEBUG]***)
                  Config.debug (fun () ->
                    if !Variable.Renaming.linked_variables_fst <> []
                    then Config.internal_error "[term.ml >> Rewrite_rules.internal_normalise] The list of linked variables for renaming should be empty";

                  );
                  (***[END DEBUG]***)

                  let lhs' = List.map (Variable.Renaming.rename_term Protocol Existential Variable.fst_ord_type) lhs in
                  let rhs' = Variable.Renaming.rename_term Protocol Existential Variable.fst_ord_type rhs in

                  Variable.Renaming.cleanup Protocol;

                  try
                    List.iter2 (Subst.match_term Protocol) lhs' args';
                    let rhs'' = Subst.follow_link rhs' in
                    Subst.cleanup Protocol;
                    raise (Found_normalise rhs'')
                  with Subst.Not_matchable ->  Subst.cleanup Protocol
                ) rw_rules;
                Func(f1, args')
              with Found_normalise t' -> t'
              end
        end
    | _ -> t

  let normalise t =
      let result = internal_normalise t in
      Config.test (fun () -> !test_normalise t result);
      result

  let rec search_variables = function
    | Var ({ link = NoLink; _ }) -> false
    | Var ({ link = FLink; _ }) -> true
    | Var _ -> Config.internal_error "[term.ml >> Rewrite_rules.search_variables] Unexpected link"
    | Func(_,args) -> List.exists search_variables args
    | _ -> Config.internal_error "[term.ml >> Rewrite_rules.search_variables] There should not be any names."

  let rec create_all_but_one_fresh snd_type k term recipe b_fcts ar = function
    | n when n = k ->
        let (l_t,l_r,l_fct) = create_all_but_one_fresh snd_type k term recipe b_fcts ar (n+1) in
        (term::l_t, recipe::l_r, l_fct)
    | n when n = ar -> ([],[],b_fcts)
    | n ->
        let (l_t,l_r,l_fct) = create_all_but_one_fresh snd_type k term recipe b_fcts ar (n+1) in

        let x_snd = Variable.fresh Recipe Universal snd_type
        and x_fst = Variable.fresh Protocol Universal Variable.fst_ord_type in

        let b_fct = BasicFact.create x_snd (Var x_fst) in

        ((Var x_fst)::l_t, (Var x_snd)::l_r, b_fct::l_fct)

  (* Type of the function f_continuation : snd_ord_variable -> recipe -> protocol_term -> BasicFact.basic_deduction_fact list -> unit *)
  let rec explore_term rw_vars u snd_type (f_continuation:snd_ord_variable -> recipe -> protocol_term -> BasicFact.t list -> unit) = function
    | Var _ -> ()
    | Func(f,args) ->
        if Subst.is_unifiable Protocol [u,Func(f,args)]
        then
          begin
            List.iter (link_search Protocol) rw_vars;
            let search = search_variables (Func(f,args)) in
            cleanup_search Protocol;

            if search
            then
              let x_snd = Variable.fresh Recipe Universal snd_type
              and x_fst = Variable.fresh Protocol Universal Variable.fst_ord_type in
              let b_fct = BasicFact.create x_snd (Var x_fst) in

              f_continuation x_snd (Var x_snd) (Var x_fst) [b_fct]
            else ()
          end;

        explore_term_list rw_vars u snd_type 0 f.arity (fun x_snd recipe_l term_l b_fct_l ->
          f_continuation x_snd (Func(f,recipe_l)) (Func(f,term_l)) b_fct_l
        ) args
    | _ -> Config.internal_error "[term.ml >> Rewrite_rules.explore_term] There should not be any names in the rewrite rules."

  and explore_term_list rw_vars u snd_type k ar f_continuation = function
    | []-> ()
    | t::q ->
        explore_term rw_vars u snd_type (fun x_snd recipe term b_fct_list ->
          let (t_list, r_list, fct_list) = create_all_but_one_fresh snd_type k term recipe b_fct_list ar 0 in

          f_continuation x_snd r_list t_list fct_list
          ) t;

        explore_term_list rw_vars u snd_type (k+1) ar f_continuation q

  let skeletons u f k = match f.cat with
    | Destructor rw_rules ->
        let accumulator = ref [] in
        let fresh_rw_rules =
          List.map (fun (lhs,rhs) ->
            Config.debug (fun () ->
              if !Variable.Renaming.linked_variables_fst <> []
              then Config.internal_error "[term.ml >> Rewrite_rules.skeletons] The list of linked variables for renaming should be empty"
            );

            let lhs' = List.map (Variable.Renaming.rename_term Protocol Existential Variable.fst_ord_type) lhs in
            let rhs' = Variable.Renaming.rename_term Protocol Existential Variable.fst_ord_type rhs in

            Variable.Renaming.cleanup Protocol;
            (lhs',rhs')
          ) rw_rules
        in

        List.iter (fun (args,r) ->
          explore_term_list (get_vars Protocol r) u (Variable.snd_ord_type k) 0 f.arity (fun x_snd recipe_l term_l b_fct_list ->
            let skel =
              {
                variable_at_position = x_snd;
                recipe = Func(f,recipe_l);
                p_term = Func(f,term_l);
                basic_deduction_facts = b_fct_list;
                rewrite_rule = f, args, r
              } in
            accumulator := skel::!accumulator
          ) args
        ) fresh_rw_rules;

        Config.test (fun () -> !test_skeletons u f k !accumulator);
        !accumulator
    | _ -> Config.internal_error "[term.ml >> Rewrite_rules.skeletons] The function symbol should be a destructor."

  let rec explore_list x_snd = function
    | [] -> Config.internal_error "[term.ml >> Rewrite_rules.explore_list] The list should not be empty"
    | bfct::q when Variable.is_equal bfct.BasicFact.var x_snd -> (bfct,q)
    | bfct::q -> let (bfct',l) = explore_list x_snd q in
        (bfct',bfct::l)

  let generic_rewrite_rules_formula fct skel =
    let (f,_,_) = skel.rewrite_rule
    and x_snd = skel.variable_at_position
    and recipe = skel.recipe
    and term = skel.p_term
    and b_fct_list = skel.basic_deduction_facts in

    match f.cat with
    | Destructor rw_rules ->
        let result =
          List.fold_left (fun acc (args,r) ->
            try
              let args' = List.map (Variable.Renaming.rename_term Protocol Universal Variable.fst_ord_type) args in
              let r' = Variable.Renaming.rename_term Protocol Universal Variable.fst_ord_type r in

              Variable.Renaming.cleanup Protocol;

              let b_fct, rest_b_fct = explore_list x_snd  b_fct_list in

              Subst.link Recipe x_snd fct.Fact.df_recipe;
              let new_recipe = Subst.apply_on_term recipe in
              Subst.cleanup Recipe;

              let head = Fact.create_deduction_fact new_recipe r' in

              (Fact.create Fact.Deduction head rest_b_fct [Func(f,args'),term; b_fct.BasicFact.term, fct.Fact.df_term])::acc
            with
            | Fact.Bot -> acc
          ) [] rw_rules
        in
        Config.test (fun () -> !test_generic_rewrite_rules_formula fct skel result);
        result
    | _ -> Config.internal_error "[term.ml >> Rewrite_rules.generic_rewrite_rules_formula] The function symbol should be a destructor."

  let specific_rewrite_rules_formula fct skel  =
    let (f,args,r) = skel.rewrite_rule
    and x_snd = skel.variable_at_position
    and recipe = skel.recipe
    and term = skel.p_term
    and b_fct_list = skel.basic_deduction_facts in

    let args' = List.map (Variable.Renaming.rename_term Protocol Universal Variable.fst_ord_type) args in
    let r' = Variable.Renaming.rename_term Protocol Universal Variable.fst_ord_type r in

    Variable.Renaming.cleanup Protocol;

    let b_fct, rest_b_fct = explore_list x_snd  b_fct_list in

    Subst.link Recipe x_snd fct.Fact.df_recipe;
    let new_recipe = Subst.apply_on_term recipe in
    Subst.cleanup Recipe;

    let head = Fact.create_deduction_fact new_recipe r' in

    (Fact.create Fact.Deduction head rest_b_fct [Func(f,args'),term; b_fct.BasicFact.term, fct.Fact.df_term])

  let display_all_rewrite_rules out rho =
    let dest_without_proj = List.filter (fun f -> not (Symbol.is_proj f)) !Symbol.all_destructors in

    match out with
      | Testing ->
          if dest_without_proj = []
          then "[]"
          else
            let display_rewrite_rules f = match f.cat with
              | Destructor rw_rules ->
                  let display_elt (arg_l,arg_r) =
                    Printf.sprintf "[%s], %s" (display_list (display Testing ~rho:rho Protocol) "; " arg_l) (display Testing ~rho:rho Protocol arg_r)
                  in

                  Printf.sprintf "%s,[%s]" (Symbol.display Testing f) (display_list display_elt ";  " rw_rules)
              | _ -> Config.internal_error "[term.ml >> display_signature] all_destructors should only contain destructors."
            in
            Printf.sprintf "[%s]" (display_list display_rewrite_rules "; " dest_without_proj)
      | _ ->
          if dest_without_proj = []
          then emptyset out
          else
            let destructor_list = List.fold_left (fun acc f -> match f.cat with
                | Destructor rw_rules ->
                    List.fold_left (fun acc_1 (arg_l,r) ->
                      (Func(f,arg_l),r)::acc_1
                    ) acc rw_rules
                | _ -> Config.internal_error "[term.ml >> display_signature] all_destructors should only contain destructors.(2)"
              ) [] dest_without_proj in

            let display_elt (l,r) = Printf.sprintf "%s %s %s" (display out ~rho:rho Protocol l) (rightarrow out) (display out ~rho:rho Protocol r) in
            Printf.sprintf "%s %s %s" (lcurlybracket out) (display_list display_elt ", " destructor_list) (rcurlybracket out)

    let display_skeleton out ?(rho=None) skel =
      let (f,args,r) = skel.rewrite_rule in

      Printf.sprintf "(%s, %s, %s, %s, %s %s %s)"
        (Variable.display out ~rho:rho Recipe skel.variable_at_position)
        (display out ~rho:rho Recipe skel.recipe)
        (display out ~rho:rho Protocol skel.p_term)
        (display_list (BasicFact.display out ~rho:rho) (Printf.sprintf " %s " (wedge out)) skel.basic_deduction_facts)
        (display out ~rho:rho Protocol (Func(f,args)))
        (rightarrow out)
        (display out ~rho:rho Protocol r)

end


(**************************
***    Consequence      ***
***************************)

module type SDF =
  sig

    type t

    val exists : t -> (Fact.deduction_formula -> bool) -> bool

    val find_first : t -> (Fact.deduction_formula -> 'a option) -> 'a option
  end

module type SDF_Sub =
  sig

    type t

    val exists : t -> (Fact.deduction -> bool) -> bool

    val find : t -> (Fact.deduction -> 'a option) -> 'a option
  end

module type DF =
  sig
    type t

    val exists_within_var_type : int -> t -> (BasicFact.t -> bool) -> bool

    val find_within_var_type : int -> t -> (BasicFact.t -> 'a option) -> 'a option

    val find : t -> (BasicFact.t -> 'a option) -> 'a option

    val iter : t -> (BasicFact.t -> unit) -> unit
  end

module type Uni =
  sig
    (** The type [set] represents sets of pairs of recipes and protocol terms. Intuitively, {% the set of subterm consequence of a constraint system
        $\C$ is the set $\\{ (\xi,u) \in \Consequence{\Solved(\C) \cup \Df(\C)} \mid \xi \in \st{\InitInput(\C)} \cup \sstdeux{\Solved(\C)}\\}$. %}*)
    type t

    (** [find_protocol] {% $\Set$~$t$%} [f] returns [Some] {% $\xi$ if $(\xi,t) \in \Set$ %} and [f] {% $\xi$ %} returns [true]. Otherwise it returns [None].*)
    val find_protocol_term : t -> protocol_term -> (recipe -> bool) -> recipe option

    (** [iter] {% $\Set$ %} [f] applies the function [f] to all pairs {% $(\xi,t) \in \Set$.
        Warning : The order in which the function [iter] goes through the pairs of $\Set$ is unspecified. %}*)
    val iter : t -> (recipe -> protocol_term -> unit) -> unit
  end

module Tools_General (SDF: SDF) (DF: DF) = struct

  (******* Consequence *******)

  exception No_match

  let rec match_term at term_df term = match term_df, term with
    | AxName n, AxName n' when AxName.is_equal n n' -> ()
    | Var(v), _ when v.quantifier = Universal ->
        begin match v.link with
          | TLink t -> if not (is_equal t term) then raise No_match
          | NoLink ->  Subst.link at v term
          | _ -> Config.internal_error "[term.ml >> SDF.match_term] Unexpected link"
        end
    | Var(v), Var(v') when Variable.is_equal v v' -> ()
    | Func(f,args), Func(f',args') when Symbol.is_equal f f' ->
        List.iter2 (match_term at) args args'
    | _,_ -> raise No_match

  let consequence k sdf df op_psi recipe protocol_term =

    let rec mem_list r_list t_list = match r_list, t_list with
      | [],[] -> true
      | [],_ | _,[] -> Config.internal_error "[term.ml >> Consequence.mem] Both list should always have the same size"
      | r::q_r, t::q_t ->
          if mem_term r t
          then mem_list q_r q_t
          else false

    and mem_term r t =
      let go_through_SDF () =
        SDF.exists sdf (fun psi ->
          if psi.Fact.ded_fact_list = []
          then is_equal psi.Fact.head.Fact.df_recipe r && is_equal psi.Fact.head.Fact.df_term t
          else
            begin try
              match_term Recipe psi.Fact.head.Fact.df_recipe r;
              match_term Protocol psi.Fact.head.Fact.df_term t;

              let new_r_list,new_t_list = List.fold_left (fun (acc_r,acc_t) ded ->
                let v = variable_of ded.BasicFact.term in

                match ded.BasicFact.var.link, v.link with
                  | TLink r', TLink t' -> (r'::acc_r,t'::acc_t)
                  | _, _ -> Config.internal_error "[term.ml >> Consequence.mem] All variables should be linked after succesful matchs"
              ) ([],[]) psi.Fact.ded_fact_list in

              Subst.cleanup Recipe;
              Subst.cleanup Protocol;

              mem_list new_r_list new_t_list
            with No_match ->
              Subst.cleanup Recipe;
              Subst.cleanup Protocol;
              false
            end
        )
      in

      let go_through_DF var =
        DF.exists_within_var_type k df (fun ded -> Variable.is_equal ded.BasicFact.var var && is_equal ded.BasicFact.term t)
      in

      let rec go_through_formula_hyp var = function
        | [] -> false
        | ded::_ when Variable.is_equal ded.BasicFact.var var && is_equal ded.BasicFact.term t -> true
        | _::q -> go_through_formula_hyp var q
      in

      match r, t with
        | Func(f,args_r), Func(f',args_t) when Symbol.is_equal f f' ->
            mem_list args_r args_t
        | Func(f,_), _ when Symbol.is_constructor f -> false
        | Func(_,_), _ | AxName _, _ -> go_through_SDF ()
        | Var(v),_ ->
            begin match op_psi with
              | None -> go_through_DF v
              | Some psi -> (go_through_DF v) || (go_through_formula_hyp v psi.Fact.ded_fact_list)
            end
    in

    mem_term recipe protocol_term

  let partial_mem_recipe k sdf df op_psi recipe =

    let rec mem_list = function
      | [] -> Config.internal_error "[term.ml >> Consequence.partial_mem_recipe] The list should not be empty"
      | [r] ->
          begin match mem_term r with
            | None -> None
            | Some t -> Some [t]
          end
      | r::q_r ->
          begin match mem_term r with
            | None -> None
            | Some t ->
              begin match mem_list q_r with
                | None -> None
                | Some (l_t) -> Some(t::l_t)
              end
          end

    and mem_term r =

      let go_through_SDF () =
        SDF.find_first sdf (fun psi ->
          if psi.Fact.ded_fact_list = []
          then
            if is_equal psi.Fact.head.Fact.df_recipe r
            then Some (psi.Fact.head.Fact.df_term)
            else None
          else
            begin try
              match_term Recipe psi.Fact.head.Fact.df_recipe r;

              let new_r_list = List.map (fun ded ->
                match ded.BasicFact.var.link with
                  | TLink r' -> r'
                  | _ -> Config.internal_error "[term.ml >> Consequence.partial_mem_recipe] All variables should be linked after succesful matchs"
              )  psi.Fact.ded_fact_list in

              Subst.cleanup Recipe;

              begin match mem_list new_r_list with
                | None -> None
                | Some l_t ->
                    List.iter2 (fun ded t ->
                      let v = variable_of ded.BasicFact.term in
                      v.link <- TLink t
                    ) psi.Fact.ded_fact_list l_t;

                    let new_t = Subst.follow_link psi.Fact.head.Fact.df_term in

                    List.iter (fun ded ->
                      let v = variable_of ded.BasicFact.term in
                      v.link <- NoLink
                    ) psi.Fact.ded_fact_list;
                    Some new_t
              end

            with No_match ->
              Subst.cleanup Recipe;
              None
            end

        )
      in

      let go_through_DF var =
        DF.find_within_var_type k df (fun ded ->
          if Variable.is_equal ded.BasicFact.var var
          then Some(ded.BasicFact.term)
          else None
        )
      in

      let rec go_through_formula_hyp var = function
        | [] -> None
        | ded::_ when Variable.is_equal ded.BasicFact.var var -> Some (ded.BasicFact.term)
        | _::q -> go_through_formula_hyp var q
      in

      match r with
        | Func(f,args_r) when Symbol.is_constructor f ->
            begin match mem_list args_r with
              | None -> None
              | Some t_l -> Some (Func(f,t_l))
            end
        | Func(_,_) | AxName _ -> go_through_SDF ()
        | Var v ->
            begin match go_through_DF v, op_psi with
              | Some t, _ -> Some t
              | None, None -> None
              | None, Some psi -> go_through_formula_hyp v psi.Fact.ded_fact_list
            end
    in

    mem_term recipe

  let partial_mem_protocol k sdf df op_psi protocol_term =

    let rec mem_list = function
      | [] -> Config.internal_error "[term.ml >> Consequence.partial_mem_protocol] The list should not be empty"
      | [t] ->
          begin match mem_term t with
            | None -> None
            | Some r -> Some [r]
          end
      | t::q_t ->
          begin match mem_term t with
            | None -> None
            | Some r ->
              begin match mem_list  q_t with
                | None -> None
                | Some (l_r) -> Some(r::l_r)
              end
          end

    and mem_term t =

      let go_through_SDF () =
        SDF.find_first sdf (fun psi ->
          if psi.Fact.ded_fact_list = []
          then
            if is_equal psi.Fact.head.Fact.df_term t
            then Some (psi.Fact.head.Fact.df_recipe)
            else None
          else
            begin try
              match_term Protocol psi.Fact.head.Fact.df_term t;

              let new_t_list = List.map (fun ded ->
                let v = variable_of ded.BasicFact.term in
                match v.link with
                  | TLink t' -> t'
                  | _ -> Config.internal_error "[term.ml >> Consequence.partial_mem_protocol] All variables should be linked after succesful matchs"
              )  psi.Fact.ded_fact_list in

              Subst.cleanup Protocol;

              begin match mem_list new_t_list with
                | None -> None
                | Some l_r ->
                    List.iter2 (fun ded r ->
                      ded.BasicFact.var.link <- TLink r
                    ) psi.Fact.ded_fact_list l_r;

                    let new_r = Subst.follow_link psi.Fact.head.Fact.df_recipe in

                    List.iter (fun ded ->
                      ded.BasicFact.var.link <- NoLink
                    ) psi.Fact.ded_fact_list;
                    Some new_r
              end

            with No_match ->
              Subst.cleanup Protocol;
              None
            end
        )
      in

      let go_through_DF () =
        DF.find_within_var_type k df (fun ded ->
          if is_equal ded.BasicFact.term t
          then Some (Var(ded.BasicFact.var))
          else None
        )
      in

      let rec go_through_formula_hyp = function
        | [] -> None
        | ded::_ when is_equal ded.BasicFact.term t -> Some (Var(ded.BasicFact.var))
        | _::q -> go_through_formula_hyp q
      in

      match t with
        | Func(f,args_t) ->
            begin match mem_list args_t with
              | None ->
                  begin match go_through_SDF () with
                    | None ->
                      begin match go_through_DF () , op_psi with
                        | Some r, _ -> Some r
                        | None, None -> None
                        | None, Some psi -> go_through_formula_hyp psi.Fact.ded_fact_list
                      end
                    | Some r -> Some r
                  end
              | Some t_r -> Some (Func(f,t_r))
            end
        | _ ->
            begin match go_through_SDF () with
              | None ->
                begin match go_through_DF () , op_psi with
                  | Some r, _ -> Some r
                  | None, None -> None
                  | None, Some psi -> go_through_formula_hyp psi.Fact.ded_fact_list
                end
              | Some r -> Some r
            end
    in

    mem_term protocol_term

  let partial_consequence (type a) (type b) (at:(a,b) atom) k sdf df op_psi (term:(a,b) term) = match at with
    | Protocol ->
        begin match partial_mem_protocol k sdf df op_psi term with
          | None -> None
          | Some r -> (Some (r,term):(recipe * protocol_term) option)
        end
    | Recipe ->
        begin match partial_mem_recipe k sdf df op_psi term with
          | None -> None
          | Some t -> (Some (term,t):(recipe * protocol_term) option)
        end

  exception Found

  let is_df_solved df =
    try
      DF.iter df (fun b_fct ->
        if not (is_variable b_fct.BasicFact.term)
        then raise Found
        else
          let v = variable_of (b_fct.BasicFact.term) in
          match v.link with
            | NoLink -> link_search Protocol v
            | FLink -> raise Found
            | _ -> Config.internal_error "[term.ml >> is_df_solved] Unexpected link"
        );
      cleanup_search Protocol;
      true
    with
      | Found -> false

end

module Tools_Subterm (SDF: SDF_Sub) (DF: DF) (Uni : Uni) = struct

  (***** Tested function *******)

  let test_partial_consequence_Protocol : (SDF.t -> DF.t -> protocol_term ->  (recipe * protocol_term) option -> unit) ref = ref (fun _ _ _ _ -> ())

  let test_partial_consequence_Recipe : (SDF.t -> DF.t -> recipe ->  (recipe * protocol_term) option -> unit) ref = ref (fun _ _ _ _ -> ())

  let update_test_partial_consequence (type a) (type b) (at:(a,b) atom) (f: SDF.t -> DF.t -> (a,b) term -> (recipe * protocol_term) option -> unit) = match at with
    | Protocol -> test_partial_consequence_Protocol := f
    | Recipe -> test_partial_consequence_Recipe := f

  let test_partial_consequence_additional_Protocol : (SDF.t -> DF.t -> BasicFact.t list -> protocol_term ->  (recipe * protocol_term) option -> unit) ref = ref (fun _ _ _ _ _ -> ())

  let test_partial_consequence_additional_Recipe : (SDF.t -> DF.t -> BasicFact.t list -> recipe ->  (recipe * protocol_term) option -> unit) ref = ref (fun _ _ _ _ _ -> ())

  let update_test_partial_consequence_additional (type a) (type b) (at:(a,b) atom) (f: SDF.t -> DF.t -> BasicFact.t list -> (a,b) term -> (recipe * protocol_term) option -> unit) = match at with
    | Protocol -> test_partial_consequence_additional_Protocol := f
    | Recipe -> test_partial_consequence_additional_Recipe := f

  let test_uniform_consequence : (SDF.t -> DF.t -> Uni.t -> protocol_term -> recipe option -> unit) ref = ref (fun _ _ _ _ _ -> ())

  let update_test_uniform_consequence f = test_uniform_consequence := f

  (***** Consequence ******)

  let rec consequence sdf df recipe term = match recipe, term with
    | Func(f,args_r), Func(f',args_t) when Symbol.is_equal f f' ->
        List.for_all2 (consequence sdf df)  args_r args_t
    | Func(f,_), _ when Symbol.is_constructor f -> false
    | Func(_,_), _ | AxName _, _ ->
        SDF.exists sdf (fun fct -> (is_equal fct.Fact.df_recipe recipe) && (is_equal fct.Fact.df_term term))
    | Var(v),_ -> DF.exists_within_var_type (Variable.type_of v) df (fun b_fct -> (Variable.is_equal b_fct.BasicFact.var v) && (is_equal b_fct.BasicFact.term term))

  let partial_mem_recipe sdf df recipe =

    let rec mem_list = function
      | [] -> Config.internal_error "[term.ml >> Consequence_Subterm.partial_mem_recipe] The list should not be empty"
      | [r] ->
          begin match mem_term r with
            | None -> None
            | Some t -> Some [t]
          end
      | r::q_r ->
          begin match mem_term r with
            | None -> None
            | Some t ->
              begin match mem_list q_r with
                | None -> None
                | Some (l_t) -> Some(t::l_t)
              end
          end

    and mem_term recipe = match recipe with
      | Func(f,args_r) when Symbol.is_constructor f ->
          begin match mem_list args_r with
            | None -> None
            | Some t_l -> Some (Func(f,t_l))
          end
      | Func(_,_) | AxName _ -> SDF.find sdf (fun fct -> if is_equal fct.Fact.df_recipe recipe then Some fct.Fact.df_term else None)
      | Var v -> DF.find_within_var_type (Variable.type_of v) df (fun b_fct -> if Variable.is_equal b_fct.BasicFact.var v then Some b_fct.BasicFact.term else None)

    in

    mem_term recipe

  let partial_mem_protocol sdf df pterm =

    let rec mem_list = function
      | [] -> Config.internal_error "[term.ml >> Consequence_Subterm.partial_mem_protocol] The list should not be empty"
      | [t] ->
          begin match mem_term t with
            | None -> None
            | Some r -> Some [r]
          end
      | t::q_t ->
          begin match mem_term t with
            | None -> None
            | Some r ->
              begin match mem_list q_t with
                | None -> None
                | Some (l_r) -> Some(r::l_r)
              end
          end

    and mem_term pterm = match pterm with
      | Func(f,args_t) ->
          begin match mem_list args_t with
            | None ->
                begin match SDF.find sdf (fun fct -> if is_equal fct.Fact.df_term pterm then Some fct.Fact.df_recipe else None) with
                  | None -> DF.find df (fun b_fct -> if is_equal b_fct.BasicFact.term pterm then Some (Var b_fct.BasicFact.var) else None)
                  | Some r -> Some r
                end
            | Some t_r -> Some (Func(f,t_r))
          end
      | _ ->
          begin match SDF.find sdf (fun fct -> if is_equal fct.Fact.df_term pterm then Some fct.Fact.df_recipe else None) with
            | None -> DF.find df (fun b_fct -> if is_equal b_fct.BasicFact.term pterm then Some (Var b_fct.BasicFact.var) else None)
            | Some r -> Some r
          end
    in

    mem_term pterm

  let partial_consequence (type a) (type b) (at:(a,b) atom) sdf df (term:(a,b) term) = match at with
    | Protocol ->
        begin match partial_mem_protocol sdf df term with
          | None ->
              Config.test (fun () -> !test_partial_consequence_Protocol sdf df term None);
              None
          | Some r ->
              Config.test (fun () -> !test_partial_consequence_Protocol sdf df term (Some (r,term)));
              (Some (r,term):(recipe * protocol_term) option)
        end
    | Recipe ->
        begin match partial_mem_recipe sdf df term with
          | None ->
              Config.test (fun () -> !test_partial_consequence_Recipe sdf df term None);
              None
          | Some t ->
              Config.test (fun () -> !test_partial_consequence_Recipe sdf df term (Some (term,t)));
              (Some (term,t):(recipe * protocol_term) option)
        end

  let partial_mem_additional_recipe sdf df b_fct_list recipe =

    let rec mem_list = function
      | [] -> Config.internal_error "[term.ml >> Consequence_Subterm.partial_mem_recipe] The list should not be empty"
      | [r] ->
          begin match mem_term r with
            | None -> None
            | Some t -> Some [t]
          end
      | r::q_r ->
          begin match mem_term r with
            | None -> None
            | Some t ->
              begin match mem_list q_r with
                | None -> None
                | Some (l_t) -> Some(t::l_t)
              end
          end

    and mem_term recipe = match recipe with
      | Func(f,args_r) when Symbol.is_constructor f ->
          begin match mem_list args_r with
            | None -> None
            | Some t_l -> Some (Func(f,t_l))
          end
      | Func(_,_) | AxName _ -> SDF.find sdf (fun fct -> if is_equal fct.Fact.df_recipe recipe then Some fct.Fact.df_term else None)
      | Var v ->
          begin try
            let b_fct = List.find (fun b_fct -> Variable.is_equal v b_fct.BasicFact.var) b_fct_list in
            Some b_fct.BasicFact.term
          with
            | Not_found -> DF.find_within_var_type (Variable.type_of v) df (fun b_fct -> if Variable.is_equal b_fct.BasicFact.var v then Some b_fct.BasicFact.term else None)
          end

    in

    mem_term recipe

  let partial_mem_additional_protocol sdf df b_fct_list pterm =

    let rec mem_list = function
      | [] -> Config.internal_error "[term.ml >> Consequence_Subterm.partial_mem_protocol] The list should not be empty"
      | [t] ->
          begin match mem_term t with
            | None -> None
            | Some r -> Some [r]
          end
      | t::q_t ->
          begin match mem_term t with
            | None -> None
            | Some r ->
              begin match mem_list q_t with
                | None -> None
                | Some (l_r) -> Some(r::l_r)
              end
          end

    and mem_term pterm = match pterm with
      | Func(f,args_t) ->
          begin match mem_list args_t with
            | None ->
                begin try
                  let b_fct = List.find (fun b_fct -> is_equal pterm b_fct.BasicFact.term) b_fct_list in
                  Some (Var b_fct.BasicFact.var)
                with
                  | Not_found ->
                      begin match SDF.find sdf (fun fct -> if is_equal fct.Fact.df_term pterm then Some fct.Fact.df_recipe else None) with
                        | None -> DF.find df (fun b_fct -> if is_equal b_fct.BasicFact.term pterm then Some (Var b_fct.BasicFact.var) else None)
                        | Some r -> Some r
                      end
                end
            | Some t_r -> Some (Func(f,t_r))
          end
      | _ ->
          begin try
            let b_fct = List.find (fun b_fct -> is_equal pterm b_fct.BasicFact.term) b_fct_list in
            Some (Var b_fct.BasicFact.var)
          with
            | Not_found ->
              begin match SDF.find sdf (fun fct -> if is_equal fct.Fact.df_term pterm then Some fct.Fact.df_recipe else None) with
                | None -> DF.find df (fun b_fct -> if is_equal b_fct.BasicFact.term pterm then Some (Var b_fct.BasicFact.var) else None)
                | Some r -> Some r
              end
          end

    in

    mem_term pterm

  let compare_variables df bfct_list =
    List.iter (fun bfct ->
      let xsnd = BasicFact.get_snd_ord_variable bfct in
      DF.iter df (fun bfct_df ->
        let xsnd' = BasicFact.get_snd_ord_variable bfct_df in
        if Variable.order Recipe xsnd xsnd' <= 0
        then Config.internal_error "[term.ml >> Tools_Subterm.compare_variables] The second-order variables in the addition list of basic deduction fact should be bigger than the variables in DF (in the sense of Variable.order)."
      )
    ) bfct_list

  let partial_consequence_additional (type a) (type b) (at:(a,b) atom) sdf df b_fct_list (term:(a,b) term) = match at with
    | Protocol ->
        Config.debug (fun () -> compare_variables df b_fct_list);
        begin match partial_mem_additional_protocol sdf df b_fct_list term with
          | None ->
              Config.test (fun () -> !test_partial_consequence_additional_Protocol sdf df b_fct_list term None);
              None
          | Some r ->
              Config.test (fun () -> !test_partial_consequence_additional_Protocol sdf df b_fct_list term (Some (r,term)));
              (Some (r,term):(recipe * protocol_term) option)
        end
    | Recipe ->
        Config.debug (fun () -> compare_variables df b_fct_list);
        begin match partial_mem_additional_recipe sdf df b_fct_list term with
          | None ->
              Config.test (fun () -> !test_partial_consequence_additional_Recipe sdf df b_fct_list term None);
              None
          | Some t ->
              Config.test (fun () -> !test_partial_consequence_additional_Recipe sdf df b_fct_list term (Some (term,t)));
              (Some (term,t):(recipe * protocol_term) option)
        end

  exception Found

  let vars_occurs_in_df (type a) (type b) (at:(a,b) atom) df (x:(a,b) variable) =
    try
      DF.iter df (fun bfct ->
        match at with
          | Recipe ->
              let xsnd = BasicFact.get_snd_ord_variable bfct in
              if x = xsnd
              then raise Found
          | Protocol ->
              let term = BasicFact.get_protocol_term bfct in
              if var_occurs x term
              then raise Found
      );
      false
    with
      | Found -> true

  let uniform_consequence sdf df uni term =
    Config.debug (fun () ->
      Uni.iter uni (fun recipe term ->
        let xsnd_l = get_vars Recipe recipe
        and xfst_l = get_vars Protocol term in
        List.iter (fun x ->
          if not (vars_occurs_in_df Recipe df x)
          then Config.internal_error "[term.ml >> Tools_Subterm.uniform_consequence] The second-order variable in the uniformity set should be in DF."
        ) xsnd_l;
        List.iter (fun x ->
          if not (vars_occurs_in_df Protocol df x)
          then Config.internal_error "[term.ml >> Tools_Subterm.uniform_consequence] The first-order variable in the uniformity set should be in DF."
        ) xfst_l;
      );
    );

    let rec mem_list = function
      | [] -> Config.internal_error "[term.ml >> Tools_Subterm.uniform_consequence] The list should not be empty"
      | [t] ->
          begin match mem_term t with
            | None -> None
            | Some r -> Some [r]
          end
      | t::q_t ->
          begin match mem_term t with
            | None -> None
            | Some r ->
              begin match mem_list q_t with
                | None -> None
                | Some (l_r) -> Some(r::l_r)
              end
          end

    and mem_term pterm =
      match Uni.find_protocol_term uni pterm (fun _ -> true) with
        | None ->
            begin match pterm with
              | Func(f,args_t) ->
                  begin match mem_list args_t with
                    | None ->
                        begin match SDF.find sdf (fun fct -> if is_equal fct.Fact.df_term pterm then Some fct.Fact.df_recipe else None) with
                          | None -> DF.find df (fun b_fct -> if is_equal b_fct.BasicFact.term pterm then Some (Var b_fct.BasicFact.var) else None)
                          | Some r -> Some r
                        end
                    | Some t_r -> Some (Func(f,t_r))
                  end
              | _ ->
                  begin match SDF.find sdf (fun fct -> if is_equal fct.Fact.df_term pterm then Some fct.Fact.df_recipe else None) with
                    | None -> DF.find df (fun b_fct -> if is_equal b_fct.BasicFact.term pterm then Some (Var b_fct.BasicFact.var) else None)
                    | Some r -> Some r
                  end
            end
        | Some recipe -> Some recipe
    in

    let result = mem_term term in
    Config.test (fun () -> !test_uniform_consequence sdf df uni term result);
    result



  let is_df_solved df =
    try
      DF.iter df (fun b_fct ->
        if not (is_variable b_fct.BasicFact.term)
        then raise Found
        else
          let v = variable_of (b_fct.BasicFact.term) in
          match v.link with
            | NoLink -> link_search Protocol v
            | FLink -> raise Found
            | _ -> Config.internal_error "[term.ml >> is_df_solved] Unexpected link"
        );
      cleanup_search Protocol;
      true
    with
      | Found -> false
end
