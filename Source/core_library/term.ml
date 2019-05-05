open Display
open Extensions

(************************
***       Types       ***
*************************)

type quantifier =
  | Free
  | Existential
  | Universal

type name =
  {
    label_n : string;
    index_n : int;
    mutable link_n : link_n
  }

and axiom = int

and link_n =
  | NNoLink
  | NLink of name
  | NLinkSearch

type fst_ord = NoType

type snd_ord = int

type ('a, 'b) atom =
  | Protocol : (fst_ord, name) atom
  | Recipe : (snd_ord, axiom) atom

type representation =
  | AttackerPublicName
  | UserName
  | UserDefined

type symbol_cat =
  | Tuple
  | Constructor
  | Destructor of ((fst_ord, name) term list *  (fst_ord, name) term) list

and symbol =
  {
    name : string;
    index_s : int;
    arity : int;
    cat : symbol_cat;
    public: bool;
    represents : representation
  }

and ('a,'b) link =
  | NoLink
  | TLink of ('a, 'b) term
  | VLink of ('a, 'b) variable
  | FLink
  | XLink of (snd_ord, axiom) variable

and ('a,'b) variable =
  {
    label : string;
    index : int;
    mutable link : ('a, 'b) link;
    quantifier : quantifier;
    var_type : 'a
  }

and ('a,'b) generic_term =
  | Func of symbol * ('a, 'b) term list
  | Var of ('a, 'b) variable
  | AxName of 'b

and ('a,'b) term =
  {
    ground : bool;
    term : ('a, 'b) generic_term
  }

type protocol_term = (fst_ord, name) term

type recipe = (snd_ord, axiom) term

type fst_ord_variable = (fst_ord, name) variable

type snd_ord_variable = (snd_ord, axiom) variable

type vars = {
  snd_ord : snd_ord_variable option;
  axiom : axiom option;
}
let get_snd_ord v =
  match v.snd_ord with
  | None -> Config.internal_error "[term.ml >> get_snd_ord] Unexpected case."
  | Some x -> x

let get_axiom v =
  match v.axiom with
  | None -> Config.internal_error "[term.ml >> get_axiom] Unexpected case."
  | Some x -> x


type display_renamings =
  {
    rho_name : (name * name) list;
    rho_fst_var : (fst_ord_variable * fst_ord_variable) list;
    rho_snd_var : (snd_ord_variable * snd_ord_variable) list
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

let display_var_name_for_HTML str index =
  if index = 0
  then
    if Str.string_match reg_latex_1 str 0
    then
      let body = Str.matched_group 1 str in
      let number = Str.matched_group 2 str in
      Printf.sprintf "%s<sub>%s</sub>" body number
    else str
  else
    Printf.sprintf "%s<sub>%d</sub>" str index

let rec is_ground_debug term = match term.term with
  | Var _ -> false
  | Func(_,args) -> List.for_all is_ground_debug args
  | _ -> true

module HashSymb = struct
  type t = symbol

  let equal = (==)

  let hash = Hashtbl.hash
end

module HashtblSymb = Hashtbl.Make(HashSymb)

(************************************
***            Variables          ***
*************************************)

module Variable = struct

  let accumulator = ref 0

  let set_up_counter n = accumulator := n

  let get_counter () = !accumulator

  let fst_ord_type = NoType

  let snd_ord_type n = n

  let infinite_snd_ord_type = max_int

  let has_infinite_type v = v.var_type = max_int

  let has_not_infinite_type v = v.var_type <> max_int

  let fresh_with_label q ty s =
    let var = { label = s; index = !accumulator; link = NoLink; quantifier = q; var_type = ty } in
    incr accumulator;
    var

  let fresh (type a) (type b) (at:(a,b) atom) q (ty:a) = match at with
    | Protocol -> fresh_with_label q ty "x"
    | Recipe -> fresh_with_label q ty "X"

  let fresh_from var =
    let var = { label = var.label; index = !accumulator; link = NoLink; quantifier = var.quantifier; var_type = var.var_type } in
    accumulator := !accumulator + 1;
    var

  let fresh_list at q ty n =
    let rec tail_fresh acc = function
      | 0 -> acc
      | n -> tail_fresh ((fresh at q ty)::acc) (n-1)
    in
    tail_fresh [] n

  let fresh_term_list at q ty ar =
    let rec tail_fresh acc = function
      | 0 -> acc
      | ar -> tail_fresh (({ term = Var(fresh at q ty) ; ground = false })::acc) (ar-1)
    in
    tail_fresh [] ar

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
            | Recipe, true -> Printf.sprintf "%s:%d" (display_var_name_for_HTML x.label x.index) x.var_type
            | _ , _ -> display_var_name_for_HTML x.label x.index
          end
      | Latex ->
          begin match at,v_type with
            | Recipe, true -> Printf.sprintf "%s\\text{:}%d" (display_var_name_for_latex x.label x.index) x.var_type
            | _ , _ -> display_var_name_for_latex x.label x.index
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

    let rec follow_link term =
      Config.debug (fun () ->
        if term.ground <> is_ground_debug term
        then Config.internal_error "[term.ml >> Variable.follow_link] Conflict with ground."
      );

      if term.ground
      then term
      else
        match term.term with
          | Func(f,args) -> { term = Func(f,List.map follow_link args) ; ground = false }
          | Var({link = VLink v;_}) -> { term = Var(v) ; ground = false }
          | Var({link = NoLink; _}) -> term
          | Var _ -> Config.internal_error "[Variable.Renaming >> follow_link] Unexpected link"
          | _ -> term

    (****** Generation *******)

    let intersect_domain rho_1 rho_2 =
      List.iter (fun (v,_) -> v.link <- FLink) rho_1;

      let domain =
        List.fold_left (fun acc (n,_) ->
          if n.link = FLink
          then n::acc
          else acc
        ) [] rho_2
      in

      List.iter (fun (v,_) -> v.link <- NoLink) rho_1;
      domain

    let variable_fresh_shortcut = fresh

    let identity = []

    let fresh at vars_list quanti =
      List.rev_map (fun x -> (x, fresh at quanti x.var_type)) vars_list

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

    let get_vars_with_list rho vlist =
      List.iter (fun x -> x.link <- FLink) vlist;

      let result = ref vlist in

      List.iter (fun (x,y) ->
        match x.link,y.link with
          | NoLink , NoLink -> x.link <- FLink; y.link <- FLink; result := x::y:: !result
          | FLink, NoLink -> y.link <- FLink ; result := y:: !result
          | NoLink, FLink -> x.link <- FLink; result := x:: !result
          | FLink, FLink -> ()
          | _,_ -> Config.internal_error "[term.ml >> Variable.Renaming.get_vars_with_list] Unexpected link"
      ) rho;

      List.iter (fun x -> x.link <- NoLink) !result;
      !result

    (******* Testing *******)

    let is_identity rho = rho = []

    let is_equal at rho_1 rho_2 =

      let rec link_and_size = function
        | [],[] -> true
        | [],_ | _,[] -> false
        | (v,v')::q_1, _::q_2 ->
            link at v v';
            link_and_size (q_1,q_2)
      in

      if link_and_size (rho_1,rho_2)
      then
        begin
          let result =
            List.for_all (fun (v,v') ->
              match v.link with
                | VLink v'' when is_equal v' v'' -> true
                | _ -> false
            ) rho_2 in

            cleanup at;
            result
        end
      else
        begin
          cleanup at;
          false
        end

    (******* Operators ********)

    let not_in_domain rho v_list =
      List.iter (fun (v,_) -> v.link <- FLink) rho;
      let result = List.filter_unordered (fun v -> v.link = NoLink) v_list in
      List.iter (fun (v,_) -> v.link <- NoLink) rho;
      result

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

    let rec apply_term term =
      Config.debug (fun () ->
        if term.ground <> is_ground_debug term
        then Config.internal_error "[term.ml >> Variable.apply_term] Conflict with ground."
      );
      if term.ground
      then term
      else
        match term.term with
          | Var(v) ->
              begin match v.link with
                | VLink(v') -> { term = Var(v') ; ground = false }
                | NoLink -> term
                | _ -> Config.internal_error "[term.ml >> Variable.Renaming.apply_term] Unexpected link"
              end
          | Func(f,args) -> { term = Func(f, List.map apply_term args) ; ground = false }
          | _ -> term

    let apply rho elt f_map_elt =
      if rho = []
      then elt
      else
        begin
          Config.debug (fun () ->
            if List.exists (fun (v,_) -> v.link <> NoLink) rho
            then Config.internal_error "[term.ml >> Variable.Renaming.apply] Variables in the domain should not be linked"
          );

          (* Link the variables of the renaming *)
          let f_cleanup =
            List.fold_left (fun f_acc (v,v') -> v.link <- (VLink v'); (fun () -> v.link <- NoLink; f_acc ())) (fun () -> ()) rho
          in

          (* Apply the renaming on the element *)
          let new_elt = f_map_elt elt apply_variable in

          (* Unlink the variables of the renaming *)
          f_cleanup ();

          new_elt
        end

    let apply_on_terms rho elt f_map_elt =
      if rho = []
      then elt
      else
        begin
          Config.debug (fun () ->
            if List.exists (fun (v,_) -> v.link <> NoLink) rho
            then Config.internal_error "[term.ml >> Variable.Renaming.apply] Variables in the domain should not be linked"
          );

          (* Link the variables of the renaming *)
          let f_cleanup =
            List.fold_left (fun f_acc (v,v') -> v.link <- (VLink v'); (fun () -> v.link <- NoLink; f_acc ())) (fun () -> ()) rho
          in

          (* Apply the renaming on the element *)
          let new_elt = f_map_elt elt apply_term in

          (* Unlink the variables of the renaming *)
          f_cleanup ();

          new_elt
        end

    let rec rename_term : 'a 'b. ('a,'b) atom -> quantifier -> 'a -> ('a,'b) term -> ('a,'b) term = fun (type a) (type b) (at:(a,b) atom) quantifier (ord_type:a) (t:(a,b) term) ->
      Config.debug (fun () ->
        if t.ground <> is_ground_debug t
        then Config.internal_error "[term.ml >> Variable.rename_term] Conflict with ground."
      );
      if t.ground
      then t
      else
        match t.term with
          | Var(v) ->
              begin match v.link with
                | VLink(v') -> { term = Var(v') ; ground = false }
                | NoLink ->
                    let v' = variable_fresh_shortcut at quantifier ord_type in
                    link at v v';
                    { term = Var(v'); ground = false }
                | _ -> Config.internal_error "[term.ml >> Subst.Renaming.rename] Unexpected link"
              end
          | Func(f,args) -> { term = Func(f, List.map (rename_term at quantifier ord_type) args) ; ground = false }
          | _ -> t

    (******** Display *********)

    let display_domain out ?(rho=None) at ?(v_type=false) domain =
      if domain = []
      then emptyset out
      else Printf.sprintf "%s %s %s" (lcurlybracket out) (display_list (display out ~rho:rho at ~v_type:v_type) ", " domain) (rcurlybracket out)

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

  let set_up_counter n = accumulator := n

  let get_counter () = !accumulator

  let fresh_with_label n =
    let name = { label_n = n; index_n = !accumulator; link_n = NNoLink } in
    accumulator := !accumulator + 1;
    name

  let fresh () = fresh_with_label "n"

  let fresh_from name = fresh_with_label name.label_n

  let is_equal n1 n2 = n1 == n2

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
      | HTML -> display_var_name_for_HTML n'.label_n n'.index_n
      | Latex -> display_var_name_for_latex n'.label_n n'.index_n

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

    let fresh name_list =
      List.fold_left (fun acc x -> (x, fresh ())::acc) [] name_list

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

    let get_names_with_list rho nlist =
      List.iter (fun x -> x.link_n <- NLinkSearch) nlist;

      let result = ref nlist in

      List.iter (fun (x,y) ->
        match x.link_n,y.link_n with
          | NNoLink , NNoLink -> x.link_n <- NLinkSearch; y.link_n <- NLinkSearch; result := x::y:: !result
          | NLinkSearch, NNoLink -> y.link_n <- NLinkSearch ; result := y:: !result
          | NNoLink, NLinkSearch -> x.link_n <- NLinkSearch; result := x:: !result
          | NLinkSearch, NLinkSearch -> ()
          | _,_ -> Config.internal_error "[term.ml >> Name.Renaming.get_names_with_list] Unexpected link"
      ) rho;

      List.iter (fun x -> x.link_n <- NNoLink) !result;
      !result

    let intersect_domain rho_1 rho_2 =
      List.iter (fun (n,_) -> n.link_n <- NLinkSearch) rho_1;

      let domain = List.fold_left (fun acc (n,_) ->
        if n.link_n = NLinkSearch
        then n::acc
        else acc
      ) [] rho_2 in

      List.iter (fun (n,_) -> n.link_n <- NNoLink) rho_1;
      domain

    (***** Testing *****)

    let is_identity rho = rho = []

    let is_equal rho_1 rho_2 =

      let rec link_and_size = function
        | [],[] -> true
        | [],_ | _,[] -> false
        | (n,n')::q_1, _::q_2 ->
            link n n';
            link_and_size (q_1,q_2)
      in

      if link_and_size (rho_1,rho_2)
      then
        begin
          let result =
            List.for_all (fun (n,n') ->
              match n.link_n with
                | NLink n'' when is_equal n' n'' -> true
                | _ -> false
            ) rho_2 in

            cleanup ();
            result
        end
      else
        begin
          cleanup ();
          false
        end

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

    let rec apply_term term = match term.term with
      | AxName n ->
          begin match n.link_n with
            | NLink n' -> { term with term = AxName n' }
            | NNoLink -> { term with term = AxName n }
            | _ -> Config.internal_error "[term.ml >> Name.Renaming.apply_term] Unexpected link."
          end
      | Func(f,args) -> { term with term = Func(f, List.map apply_term args) }
      | _ -> term

    let apply_on_terms rho elt f_map_elt =
      Config.debug (fun () ->
        if List.exists (fun (n,_) -> n.link_n <> NNoLink) rho
        then Config.internal_error "[term.ml >> Name.apply_on_terms] Names in the domain should not be linked"
      );

      (* Link the names of the renaming *)
      List.iter (fun (n,n') -> n.link_n <- (NLink n')) rho;

      (* Apply the renaming on the element *)
      let new_elt = f_map_elt elt apply_term in

      (* Unlink the variables of the renaming *)
      List.iter (fun (n,_) -> n.link_n <- NNoLink) rho;

      new_elt


    let display_domain out ?(rho=None) domain =
      if domain = []
      then emptyset out
      else Printf.sprintf "%s %s %s" (lcurlybracket out) (display_list (display out ~rho:rho) ", " domain) (rcurlybracket out)


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
    i

  let order (ax1:int) (ax2:int) = compare ax1 ax2

  let index_of ax = ax

  let is_equal (ax1:int) (ax2:int) = ax1 = ax2

  let display out ax = match out with
    | Testing -> Printf.sprintf "_ax_%d" ax
    | Terminal | Pretty_Terminal -> Printf.sprintf "ax_%d" ax
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

  let all_projection = HashtblSymb.create 7

  let special_constructor = Hashtbl.create 7

  let empty_signature () =
    all_constructors := [];
    all_destructors := [];
    all_tuple := [];
    number_of_constructors :=0;
    number_of_destructors := 0;
    HashtblSymb.reset all_projection;
    Hashtbl.reset special_constructor

  type setting =
    {
      all_t : symbol list ;
      all_p : (symbol * symbol list) list ;
      all_c : symbol list ;
      all_d : symbol list ;
      nb_c : int ;
      nb_d : int ;
      nb_symb : int
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
    ) setting.all_p

  let get_settings () =
    {
      all_t = !all_tuple;
      all_p = HashtblSymb.fold (fun f list_proj acc -> (f,list_proj)::acc) all_projection [];
      all_c = !all_constructors;
      all_d = !all_destructors;
      nb_c = !number_of_constructors;
      nb_d = !number_of_destructors;
      nb_symb = !accumulator_nb_symb
    }

  (********* Symbols functions *********)

  let is_equal (sym_1:symbol) (sym_2:symbol) =
    sym_1 == sym_2

  let is_constructor sym =
    sym.cat = Constructor || sym.cat = Tuple

  let is_tuple sym =
    sym.cat = Tuple

  let is_destructor sym = match sym.cat with
    | Destructor _ -> true
    | _ -> false

  let is_public sym = sym.public

  let represents_attacker_public_name symb = match symb.represents with
    | AttackerPublicName -> true
    | _ -> false

  let represents_name symb = match symb.represents with
    | UserName -> true
    | _ -> false

  let get_arity sym = sym.arity

  let order sym_1 sym_2 = compare sym_1.index_s sym_2.index_s

  (********* Tuple ************)

  let get_projections symb_tuple = match symb_tuple.cat with
    | Tuple -> HashtblSymb.find all_projection symb_tuple
    | _ -> Config.internal_error "[term.ml >> Symbol.get_projections] The function symbol should be a tuple"

  (********* Addition ************)

  let new_constructor ar public is_name s =
    let symb = { name = s; arity = ar; cat = Constructor; index_s = !accumulator_nb_symb; public = public; represents = (if is_name then UserName else UserDefined) } in
    incr accumulator_nb_symb;
    all_constructors := symb::!all_constructors;
    incr number_of_constructors;
    symb

  let new_destructor ar public s rw_rules =
    let symb = { name = s; arity = ar; cat = Destructor rw_rules; index_s = !accumulator_nb_symb; public = public; represents = UserDefined } in
    incr accumulator_nb_symb;
    all_destructors := symb::!all_destructors;
    number_of_destructors := !number_of_destructors + 1;
    symb

  let rec new_projection acc tuple_symb i = match i with
    | 0 -> acc
    | i ->
        let args = Variable.fresh_term_list Protocol Existential Variable.fst_ord_type tuple_symb.arity in
        let x = List.nth args (i-1) in
        let symb =
          {
            name = (Printf.sprintf "proj_{%d,%d}" i tuple_symb.arity);
            arity = 1;
            cat = Destructor([([{ term = Func(tuple_symb,args) ; ground = false } ],x)]);
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
        let symb = { name = (Printf.sprintf "tuple%d" ar); arity = ar; cat = Tuple; index_s = !accumulator_nb_symb; public = true; represents = UserDefined } in
        incr accumulator_nb_symb;
        all_constructors := symb::!all_constructors;
        all_tuple := symb::!all_tuple;
        number_of_constructors := !number_of_constructors + 1;

        let list_proj = new_projection [] symb ar in
        HashtblSymb.add all_projection symb list_proj;

        symb
      end

  let get_fresh_constant (n:int) =
    try
      Hashtbl.find special_constructor n
    with
    | Not_found ->
        let c = { name = "_c"; arity = 0; cat = Constructor; index_s = !accumulator_nb_symb; public = true; represents = AttackerPublicName } in
        Hashtbl.add special_constructor n c;
        incr accumulator_nb_symb;
        c

  let fresh_attacker_name =
    let acc = ref 0 in

    let f () =
      let c = { name = (Printf.sprintf "kI_%d" !acc); arity = 0; cat = Constructor; index_s = !accumulator_nb_symb; public = true; represents = AttackerPublicName } in
      incr acc;
      c
    in
    f

  (******** Display function *******)

  let reg_proj = Str.regexp "proj_{\\([0-9]+\\),\\([0-9]+\\)}"

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
    if f.public
    then Printf.sprintf "%s/%d" (display out f) f.arity
    else Printf.sprintf "%s/%d [\\color{red}{private}]" (display out f) f.arity

  let display_tuple f = string_of_int (f.arity)

  let reg_proj = Str.regexp "proj_{"

  let display_signature out constructor = match out with
    | Testing ->
        let without_tuple = List.filter (fun f -> f.cat <> Tuple) !all_constructors in
        let str_without_tuple = Printf.sprintf "{ %s }" (display_list (display_with_arity Testing) ", " without_tuple) in
        let str_tuple = Printf.sprintf "{ %s }" (display_list display_tuple ", " (List.sort (fun f1 f2 -> compare f1.arity f2.arity) !all_tuple)) in
        str_without_tuple^" Tuple : "^str_tuple
    | _ ->
        if constructor
        then
          let without_tuple = List.filter (fun f -> f.cat <> Tuple && f.represents = UserDefined) !all_constructors in
          if without_tuple = []
          then emptyset out
          else Printf.sprintf "%s %s %s" (lcurlybracket out) (display_list (display_with_arity out) ", " without_tuple) (rcurlybracket out)
        else
          let without_projection = List.filter (fun f -> not (Str.string_match reg_proj f.name 0)) !all_destructors in
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

module AxName = struct

  let is_equal (type a) (type b) (at: (a,b) atom) (axn1:b) (axn2:b) = match at with
    | Protocol -> Name.is_equal axn1 axn2
    | Recipe -> axn1 = axn2

  let order (type a) (type b) (at:(a,b) atom) (axn1:b) (axn2:b) = match at with
    | Protocol -> compare axn1.index_n axn2.index_n
    | Recipe -> compare axn1 axn2

  let display (type a) (type b) out ?(rho=None) (at:(a,b) atom) (axn:b) = match at with
    | Protocol -> Name.display out ~rho:rho axn
    | Recipe -> Axiom.display out axn
end

(********* Generate display renaming *********)

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

  let organised_names:(string * name list) list = List.fold_left (fun acc n -> organise_names n acc) [] names in
  let organised_fst_vars = List.fold_left (fun acc v -> organise_variables v acc) [] fst_vars in
  let organised_snd_vars = List.fold_left (fun acc v -> organise_variables v acc) [] snd_vars in

  let rec create_rho_names : (string * name list) list -> (name * name) list = function
    | [] -> []
    | (str,l)::q ->
        begin match l with
          | [] -> Config.internal_error "[term.ml >> generate_display_renaming] Unexpected case 1"
          | [n] ->
              if List.exists (fun symb -> symb.name = str) !Symbol.all_constructors
              then (n,{ label_n = str; index_n = 0; link_n = NNoLink })::(create_rho_names q)
              else (n,{ label_n = str; index_n = 1; link_n = NNoLink })::(create_rho_names q)
          | _ ->
            let (new_l,_) =
              List.fold_left (fun (acc,i) n ->
                ((n,{ label_n = str; index_n = i; link_n = NNoLink })::acc,i+1)
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
  and (free_snd_vars,exist_snd_vars,univ_snd_vars) = partition_vars snd_vars in

  let std_b_names = ["k";"l";"m"]
  and std_fst_vars_U = ["z"]
  and std_snd_vars_U = ["Z"]
  and std_fst_vars_E = ["x";"y"]
  and std_snd_vars_E = ["X";"Y"]
  and std_fst_vars_F = ["w"]
  and std_snd_vars_F = ["W"] in

  let rec generate_names full_std k std names = match std,names with
    | _,[] -> []
    | [],_ -> generate_names full_std (k+1) full_std  names
    | str::q_std,n::q -> (n,{ label_n = str; index_n = k; link_n = NNoLink })::(generate_names full_std k q_std q) in

  let rec generate_vars full_std  k std var = match std,var with
    | _,[] -> []
    | [],_ -> generate_vars full_std (k+1) full_std  var
    | str::q_std,x::q -> (x,{ label = str; quantifier = x.quantifier; index = k; link = NoLink ; var_type = x.var_type })::(generate_vars full_std  k q_std q) in

  {
    rho_name =(generate_names std_b_names 0 std_b_names names);
    rho_fst_var = (generate_vars std_fst_vars_F 0 std_fst_vars_F free_fst_vars)@
                  (generate_vars std_fst_vars_E 0 std_fst_vars_E exist_fst_vars)@
                  (generate_vars std_fst_vars_U 0 std_fst_vars_U univ_fst_vars);
    rho_snd_var = (generate_vars std_snd_vars_F 0 std_snd_vars_F free_snd_vars)@
                  (generate_vars std_snd_vars_E 0 std_snd_vars_E exist_snd_vars)@
                  (generate_vars std_snd_vars_U 0 std_snd_vars_U univ_snd_vars)
  }

(********* Generation of terms *********)

let of_variable var = { term = Var(var); ground = false }

let of_name name = { term = AxName(name); ground = true }

let of_axiom ax = { term = AxName(ax); ground = true }

let variable_of term = match term.term with
  | Var(var) -> var
  | _ -> Config.internal_error "[term.ml >> variable_of] The term should be a variable"

let name_of term = match term.term with
  | AxName(name) -> name
  | _ -> Config.internal_error "[term.ml >> name_of] The term should be a name"

let axiom_of term = match term.term with
  | AxName(name) -> name
  | _ -> Config.internal_error "[term.ml >> axiom_of] The term should be an axiom"

let apply_function symbol list_sons =
  Config.debug (fun () ->
    if (List.length list_sons) <> symbol.arity
    then Config.internal_error (Printf.sprintf "[term.ml >> apply_function] The function %s has arity %d but is given %d terms" symbol.name symbol.arity (List.length list_sons));

    List.iter (fun term ->
      if term.ground <> is_ground_debug term
      then Config.internal_error "[term.ml >> Variable.follow_link] Conflict with ground."
    ) list_sons
  );
  let ground = List.for_all (fun t -> t.ground) list_sons in
  { term = Func(symbol,list_sons); ground = ground }

(********* Access Functions *********)

let root term = match term.term with
  | Func(s,_) -> s
  | _ -> Config.internal_error "[terms.ml >> root] The term is not a function application."

let get_args term = match term.term with
  | Func(s,_) when s.arity = 0 -> Config.internal_error "[terms.ml >> get_args] The term should not be a constant."
  | Func(_,l) -> l
  | _ -> Config.internal_error "[terms.ml >> get_args] The term is not a function application."

let rec get_type term = match term.term with
  | Func(_,args) -> List.fold_left (fun k r -> max k (get_type r)) 0 args
  | Var v -> Variable.type_of v
  | AxName ax -> Axiom.index_of ax

let rec order at t1 t2 = match t1.term,t2.term with
  | Var v1, Var v2 -> Variable.order at v1 v2
  | AxName n1, AxName n2 -> AxName.order at n1 n2
  | Func(f1,args1), Func(f2,args2) ->
      let ord = Symbol.order f1 f2 in
      if ord = 0
      then order_list at args1 args2
      else ord
  | Var _, _ -> -1
  | AxName _, Var _ -> 1
  | AxName _, _ -> -1
  | _ , _ -> 1

and order_list at l1 l2 = match l1, l2 with
  | [], [] -> 0
  | [],_ | _,[] -> Config.internal_error "[terms.ml >> order_list] The lists should be of equal size."
  | t1::q1, t2::q2 ->
      let ord = order at t1 t2 in
      if ord = 0
      then order_list at q1 q2
      else ord

(********* Scanning Functions *********)

let is_ground term = term.ground

let rec no_axname term = match term.term with
  | Var _ -> true
  | AxName _ -> false
  | Func (_,tlist) -> List.for_all no_axname tlist

(* In the function var_occurs and name_occurs, we go through the TLink when there is one. *)
let rec var_occurs var term =
  Config.debug (fun () ->
    if term.ground <> is_ground_debug term
    then Config.internal_error "[term.ml >> var_occurs] Conflict with ground."
  );
  if term.ground
  then false
  else
    match term.term with
      | Var(v) when Variable.is_equal v var -> true
      | Var({link = TLink t; _}) -> var_occurs var t
      | Func(_,args) -> List.exists (var_occurs var) args
      | _ -> false

(* [var_occurs_or_wrong_type] {% $\quanti{X}{i}$ $\xi$ %} returns [true] iff {% $X \in \varsdeux{\xi}$ or $\xi \not\in \T(\F,\AX_i \cup \Xdeux_i)$. %} *)
let rec internal_var_occurs_or_out_of_world (var:snd_ord_variable) (r:recipe) =
  Config.debug (fun () ->
    if r.ground <> is_ground_debug r
    then Config.internal_error "[term.ml >> var_occurs_or_out_of_world] Conflict with ground."
  );

  if r.ground
  then false
  else
    match r.term with
      | Var(v) when Variable.is_equal v var -> true
      | Var({link = TLink t; _}) -> internal_var_occurs_or_out_of_world var t
      | Var v when v.var_type > var.var_type -> true
      | AxName ax when ax > var.var_type -> true
      | Func(_,args) -> List.exists (internal_var_occurs_or_out_of_world var) args
      | _ -> false

let var_occurs_or_out_of_world (var:snd_ord_variable) (r:recipe) =
  if var.var_type = max_int
  then var_occurs var r
  else internal_var_occurs_or_out_of_world var r

let rec quantified_var_occurs quantifier term =
  if term.ground
  then false
  else
    match term.term with
      | Var(v) when Variable.quantifier_of v = quantifier-> true
      | Var({link = TLink t; _}) -> quantified_var_occurs quantifier t
      | Func(_,args) -> List.exists (quantified_var_occurs quantifier) args
      | _ -> false

let rec name_occurs n term = match term.term with
  | AxName(n') when Name.is_equal n n' -> true
  | Var({link = TLink t; _}) -> name_occurs n t
  | Func(_,args) -> List.exists (name_occurs n) args
  | _ -> false

let rec axiom_occurs n term = match term.term with
  | AxName(n') when Axiom.is_equal n n' -> true
  | Var({link = TLink t; _}) -> axiom_occurs n t
  | Func(_,args) -> List.exists (axiom_occurs n) args
  | _ -> false

(* In the function is_equal on the other hand, we do not go through the TLink. *)
let rec is_equal at t1 t2 =
  if t1.ground = t2.ground
  then
    match t1.term,t2.term with
      | Var(v1),Var(v2) when Variable.is_equal v1 v2 -> true
      | AxName(n1),AxName(n2) when AxName.is_equal at n1 n2 -> true
      | Func(f1,args1), Func(f2,args2) when Symbol.is_equal f1 f2 -> List.for_all2 (is_equal at) args1 args2
      | _,_ -> false
  else false

let is_variable term = match term.term with
  | Var(_) -> true
  | _ -> false

let is_name term = match term.term with
  | AxName(_) -> true
  | _ -> false

let is_axiom term = match term.term with
  | AxName(_) -> true
  | _ -> false

let is_function term = match term.term with
  | Func(_,_) -> true
  | _ -> false

let rec is_constructor term = match term.term with
  | Func({cat = Destructor _; _},_) -> false
  | Func(_,args) -> List.for_all is_constructor args
  | _ -> true

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
  Config.test (fun () ->
    if retrieve_search at <> []
    then Config.internal_error "[terml.ml >> get_vars] Linked variables should be empty."
  );

  let rec explore_term term =
    if not term.ground
    then
      match term.term with
        | Func (_,args) -> List.iter explore_term args
        | Var({link = FLink; _}) -> ()
        | Var v -> link_search at v
        | AxName _ -> ()
  in

  explore_term term;

  let result = retrieve_search at in
  cleanup_search at;
  result

let get_vars_not_in at term var_list =
  Config.test (fun () ->
    if retrieve_search at <> []
    then Config.internal_error "[terml.ml >> get_vars] Linked variables should be empty."
  );

  List.iter (fun v -> v.link <- FLink) var_list;

  let rec explore_term term =
    if not term.ground
    then
      match term.term with
        | Func (_,args) -> List.iter explore_term args
        | Var({link = FLink; _}) -> ()
        | Var v -> link_search at v
        | AxName _ -> ()
  in

  explore_term term;
  let result = retrieve_search at in
  cleanup_search at;
  List.iter (fun v -> v.link <- NoLink) var_list;
  result

let rec get_names_protocol term = match term.term with
  | Func (_,args) -> List.iter get_names_protocol args
  | AxName ({ link_n = NNoLink ; _} as n) -> Name.link_search n
  | AxName _ | Var _ -> ()

let get_names_with_list (type a) (type b) (at:(a,b) atom) (term:(a,b) term) (l:name list) =
  Config.test (fun () ->
    if !Name.linked_names <> []
    then Config.internal_error "[terml.ml get_names_with_list] Linked names should be empty."
  );

  List.iter Name.link_search l;

  begin match at with
    | Recipe -> ()
    | Protocol -> get_names_protocol term
  end;

  let result = Name.retrieve_search () in
  Name.cleanup_search ();
  result

let rec get_vars_term at f_quanti term =
  if not term.ground
  then
    match term.term with
      | Func (_,args) -> List.iter (get_vars_term at f_quanti) args
      | Var({link = FLink; _}) -> ()
      | Var v when f_quanti v.quantifier -> link_search at v
      | Var _ -> ()
      | AxName _ -> ()

let get_vars_with_list (type a) (type b) (at:(a,b) atom) (term:(a,b) term) f_quantifier (l:(a,b) variable list) =
  Config.test (fun () ->
    if retrieve_search at <> []
    then Config.internal_error "[terml.ml get_vars_with_list] Linked variables should be empty."
  );

  List.iter (link_search at) l;

  get_vars_term at f_quantifier term;

  let result = retrieve_search at in
  cleanup_search at;
  result

let rec add_axiom_in_list ax ax_list = match ax_list with
  | [] -> [ax]
  | ax'::_ when ax' = ax -> ax_list
  | ax'::q -> ax'::(add_axiom_in_list ax q)

let rec get_axioms_with_list recipe f_id ax_list  = match recipe.term with
  | AxName ax when f_id ax ->
      add_axiom_in_list ax ax_list
  | Var _ | AxName _ -> ax_list
  | Func(_,args) -> List.fold_left (fun acc r -> get_axioms_with_list r f_id acc) ax_list args

let rec iter_variables_and_axioms f recipe = match recipe.term with
  | AxName ax -> f (Some ax) None
  | Var v -> f None (Some v)
  | Func(_,args) -> List.iter (iter_variables_and_axioms f) args

(********** Display **********)

let rec display out ?(rho=None) at term = match term.term with
  | Var(v) -> Variable.display out ~rho:rho ~v_type:true at v
  | AxName(axn) -> AxName.display out ~rho:rho at axn
  | Func(f_symb,_) when f_symb.arity = 0 ->
      Printf.sprintf "%s" (Symbol.display out f_symb)
  | Func(f_symb,args) when f_symb.cat = Tuple ->
      Printf.sprintf "%s%s%s" (langle out) (display_list (display out ~rho:rho at) "," args) (rangle out)
  | Func(f_symb,args) ->
      Printf.sprintf "%s(%s)" (Symbol.display out f_symb) (display_list (display out ~rho:rho at) "," args)

(*************************************
***         Protocol terms         ***
**************************************)

module Subst = struct

  type ('a, 'b) t = (('a, 'b) variable * ('a, 'b) term) list
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
            then
              ( Printf.printf "Variable = %s and term = %s\n" (Variable.display Testing Recipe ~v_type:true var) (display Testing Recipe term);
                Config.internal_error "[term.ml >> Subst.create] The substution is not acyclic or the types do not corresponds"
              )
    );
    [var,term]

  let is_in_domain subst x_snd = List.exists (fun (x,_) -> Variable.is_equal x x_snd) subst

  let rec check_disjoint_domain = function
    | [] -> true
    | (x,_) :: q ->
        if (List.exists (fun (y,_) -> Variable.is_equal x y) q)
        then false
        else check_disjoint_domain q

  (*********** Display ************)

  let display out ?(rho=None) at subst =
    let display_element (x,t) =
      Printf.sprintf "%s %s %s" (Variable.display out ~rho:rho at x) (rightarrow out) (display out ~rho:rho at t)
    in

    if subst = []
    then emptyset out
    else Printf.sprintf "%s %s %s" (lcurlybracket out) (display_list display_element ", " subst) (rcurlybracket out)

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
            then
              begin
                Printf.printf "The substitution = %s\n" (display Latex at l_subst);
                Config.internal_error "[term.ml >> Subst.create_multiple] The substitution is not unifiable (type issue)"
              end
    );

    l_subst

  let split_domain subst f = List.partition (fun (x,_) -> f x) subst

  let split_domain_on_term subst f = List.partition (fun (_,t) -> f t) subst

  let union subst1 subst2 =
    Config.debug (fun () ->
      if List.exists (fun (x,_) -> List.exists (fun (y,_) -> Variable.is_equal x y) subst2) subst1 ||
        List.exists (fun (x,_) -> List.exists (fun (y,_) -> Variable.is_equal x y) subst1) subst2
      then Config.internal_error "[term.ml >> Subst.union] Domain not disjoint."
    );
    List.rev_append subst1 subst2

  let of_renaming rho = List.fold_left (fun acc (x,y) -> (x,{ term = Var y; ground = false })::acc) [] rho

  let equations_of subst = List.fold_left (fun acc (x,t) -> ({ term = Var x; ground = false}, t)::acc) [] subst

  let rec apply_on_term term =
    if term.ground
    then term
    else
      match term.term with
        | Func(f,args) ->
            let (ground,args') =
              List.fold_right (fun t (g,t_list) ->
                let t' = apply_on_term t in
                (t'.ground && g, t'::t_list)
              ) args (true,[])
            in
            { term = Func(f, args'); ground = ground }
        | Var(t) ->
            begin match t.link with
              | NoLink -> term
              | TLink t' -> t'
              | _ -> Config.internal_error "[term.ml >> Subst.apply_on_term] Unexpected link"
            end
        | _ -> term

  let apply subst elt f_iter_elt =
    if subst = []
    then elt
    else
      begin
        Config.debug (fun () ->
          if List.exists (fun (v,_) -> v.link <> NoLink) subst
          then Config.internal_error "[term.ml >> Subst.apply_substitution] Variables in the domain should not be linked"
        );

        (* Link the variables of the substitution *)
        List.iter (fun (v,t) -> v.link <- (TLink t)) subst;

        (* Apply the substitution on the element *)
        let new_elt = f_iter_elt elt apply_on_term in

        (* Unlink the variables of the substitution *)
        List.iter (fun (v,_) -> v.link <- NoLink) subst;

        new_elt
      end

  let apply_forced subst elt f_iter_elt =
    if subst = []
    then f_iter_elt elt (fun t -> t)
    else
      begin
        Config.debug (fun () ->
          if List.exists (fun (v,_) -> v.link <> NoLink) subst
          then Config.internal_error "[term.ml >> Subst.apply_substitution] Variables in the domain should not be linked"
        );

        (* Link the variables of the substitution *)
        List.iter (fun (v,t) -> v.link <- (TLink t)) subst;

        (* Apply the substitution on the element *)
        let new_elt = f_iter_elt elt apply_on_term in

        (* Unlink the variables of the substitution *)
        List.iter (fun (v,_) -> v.link <- NoLink) subst;

        new_elt
      end

  let apply_both (subst_1:(fst_ord,name) t) (subst_2:(snd_ord,axiom) t) elt f_iter_elt =
    Config.debug (fun () ->
      if List.exists (fun (v,_) -> v.link <> NoLink) subst_1 || List.exists (fun (v,_) -> v.link <> NoLink) subst_2
      then Config.internal_error "[term.ml >> Subst.apply_substitution] Variables in the domain should not be linked"
    );

    (* Link the variables of the substitution *)
    List.iter (fun (v,t) -> v.link <- (TLink t)) subst_1;
    List.iter (fun (v,t) -> v.link <- (TLink t)) subst_2;

    (* Apply the substitution on the element *)
    let new_elt = f_iter_elt elt apply_on_term apply_on_term in

    (* Unlink the variables of the substitution *)
    List.iter (fun (v,_) -> v.link <- NoLink) subst_1;
    List.iter (fun (v,_) -> v.link <- NoLink) subst_2;

    new_elt

  (*********** Iterators ************)

  let fold f elt subst = List.fold_left (fun e (x,t) -> f e x t) elt subst

  (*********** Access ************)

  let get_names_with_list (type a) (type b) (at:(a,b) atom) (subst:(a,b) t) (l:name list) =
    Config.test (fun () ->
      if !Name.linked_names <> []
      then Config.internal_error "[terml.ml >> Subst.get_names_with_list] Linked names should be empty."
    );

    List.iter Name.link_search l;

    begin match at with
      | Recipe -> ()
      | Protocol -> List.iter (fun (_,t) -> get_names_protocol t) subst
    end;

    let result = Name.retrieve_search () in
    Name.cleanup_search ();
    result

  let get_vars_with_list (type a) (type b) (at:(a,b) atom) (subst:(a,b) t) f_quantifier (l:(a,b) variable list) =
    Config.test (fun () ->
      if retrieve_search at <> []
      then Config.internal_error "[terml.ml >> Subst.get_vars_with_list] Linked variables should be empty."
    );

    List.iter (link_search at) l;

    List.iter (fun (x,t) -> get_vars_term at f_quantifier ({ term = Var x; ground = false }); get_vars_term at f_quantifier t) subst;

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

    match subst_1 = [], subst_2 = [] with
      | true, true -> []
      | true, false -> subst_2
      | false, true -> subst_1
      | false, false ->
          let subst = apply subst_2 subst_1 (fun s f ->
              List.fold_left (fun acc (x,t) -> (x,f t)::acc) [] s) in

          Config.debug (fun () ->
            if List.exists (fun (x,_) -> List.exists (fun (_,t) -> var_occurs x t) subst) subst
            then Config.internal_error "[term.ml >> Subst.compose] The resulting substution is not acyclic"
          );

          List.fold_left (fun acc (x,t) -> (x,t)::acc) subst subst_2

  let compose_restricted subst_1 subst_2 =
    Config.debug (fun () ->
      if List.exists (fun (x,_) -> List.exists (fun (y,_) -> Variable.is_equal x y) subst_2) subst_1
      then Config.internal_error "[term.ml >> Subst.compose_restricted] The substutions do not have the disjoint domain"
    );

    if subst_1 = []
    then subst_1
    else
      begin
        let subst = apply subst_2 subst_1 (fun s f ->
            List.fold_left (fun acc (x,t) -> (x,f t)::acc) [] s) in

        Config.debug (fun () ->
          if List.exists (fun (x,_) -> List.exists (fun (_,t) -> var_occurs x t) subst) subst
          then Config.internal_error "[term.ml >> Subst.compose_restricted] The resulting substution is not acyclic"
        );

        subst
      end

  let compose_restricted_generic subst_1 subst_2 f =
    Config.debug (fun () ->
      if List.exists (fun (x,_) -> List.exists (fun (y,_) -> Variable.is_equal x y) subst_2) subst_1
      then Config.internal_error "[term.ml >> Subst.compose_restricted_generic] The substutions do not have the disjoint domain"
    );

    if subst_1 = []
    then  List.fold_left (fun acc (x,t) -> if f x then (x,t)::acc else acc) [] subst_2
    else
      begin
        let subst = apply subst_2 subst_1 (fun s f ->
            List.fold_left (fun acc (x,t) -> (x,f t)::acc) [] s) in

        Config.debug (fun () ->
          if List.exists (fun (x,_) -> List.exists (fun (_,t) -> var_occurs x t) subst) subst
          then Config.internal_error "[term.ml >> Subst.compose_restricted_generic] The resulting substution is not acyclic"
        );

        List.fold_left (fun acc (x,t) -> if f x then (x,t)::acc else acc) subst subst_2
      end

  let restrict subst f = List.filter_unordered (fun (x,_) -> f x) subst

  let restrict_list subst l =
    List.iter (link_search Protocol) l;

    let subst' =
      List.fold_left (fun acc (x,t) ->
        match x.link with
          | FLink -> (x,t)::acc
          | NoLink -> acc
          | _ -> Config.internal_error "[term.ml >> Subst.restrict_list] Unexpected link"
      ) [] subst
    in

    cleanup_search Protocol;
    subst'

  let not_in_domain (subst:(snd_ord,axiom) t) (l:(snd_ord,axiom) variable list) =
    List.iter (fun (x,_) -> link_search Recipe x) subst;

    let l' =
      List.fold_left (fun acc x ->
        match x.link with
          | FLink -> acc
          | NoLink -> x::acc
          | _ -> Config.internal_error "[term.ml >> Subst.not_in_domain] Unexpected link"
      ) [] l
    in
    cleanup_search Recipe;
    l'

  let is_extended_by (type a) (type b) (at:(a,b) atom) (subst_1:(a,b) t) (subst_2:(a,b) t) =

    let subst = apply subst_2 subst_1 (fun s f ->
        List.fold_left (fun acc (x,t) -> (x,f t)::acc) [] s) in

    List.iter (fun (x,t) -> x.link <- TLink t) subst;

    let result =
      List.for_all (fun (x,t)->
        match x.link with
          | NoLink -> true
          | TLink t' -> is_equal at t t'
          | _ -> Config.internal_error "[terml.ml >> Subst.is_extended_by] Unexpected link."
      ) subst_2 in

    List.iter (fun (x,_) -> x.link <- NoLink) subst;

    result

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

  let rec follow_link term =
    if term.ground
    then term
    else
      match term.term with
        | Func(f,args) ->
            let (ground,args') =
              List.fold_right (fun t (g,t_list) ->
                let t' = follow_link t in
                (g && t'.ground, t'::t_list)
              ) args (true,[])
            in
            { term = Func(f,args'); ground = ground }
        | Var({link = TLink t;_}) -> follow_link t
        | _ -> term

  let follow_link_var v = match v.link with
    | TLink t -> follow_link t
    | _ -> Config.internal_error "[term.ml >> Subst.follow_link_var] Unexpected link"

  (******* Syntactic unification *******)

  exception Not_unifiable

  let rec unify_term_protocol (t1:protocol_term) (t2:protocol_term) = match t1.term, t2.term with
    | Var v1, Var v2 when v1 == v2 -> ()
    | Var {link = TLink t ; _}, _ -> unify_term_protocol t t2
    | _, Var {link = TLink t; _} -> unify_term_protocol t1 t
    | Var v1, Var v2 ->
        if v1.quantifier = Universal || (v1.quantifier = Existential && v2.quantifier = Free) || (v1.quantifier = v2.quantifier && v1.index < v2.index)
        then (v1.link <- TLink t2; linked_variables_fst := v1 :: !linked_variables_fst)
        else (v2.link <- TLink t1; linked_variables_fst := v2 :: !linked_variables_fst)
    | Var v1, _ -> if var_occurs v1 t2 then raise Not_unifiable else (v1.link <- TLink t2; linked_variables_fst := v1 :: !linked_variables_fst)
    | _, Var v2 -> if var_occurs v2 t1 then raise Not_unifiable else (v2.link <- TLink t1; linked_variables_fst := v2 :: !linked_variables_fst)
    | AxName n1, AxName n2 when n1 == n2 -> ()
    | Func(f1,args1), Func(f2,args2) when f1 == f2 -> List.iter2 unify_term_protocol args1 args2
    | _ -> raise Not_unifiable

  let rec unify_term_recipe (t1:recipe) (t2:recipe) = match t1.term, t2.term with
    | Var v1, Var v2 when v1 == v2 -> ()
    | Var {link = TLink t ; _}, _ -> unify_term_recipe t t2
    | _, Var {link = TLink t; _} -> unify_term_recipe t1 t
    | Var v1, Var v2 ->
        if v1.var_type < v2.var_type
        then (v2.link <- TLink t1; linked_variables_snd := v2 :: !linked_variables_snd)
        else if v1.var_type > v2.var_type
        then (v1.link <- TLink t2; linked_variables_snd := v1 :: !linked_variables_snd)
        else if v1.quantifier = Universal || (v1.quantifier = Existential && v2.quantifier = Free) || (v1.quantifier = v2.quantifier &&  (v1.var_type < v2.var_type || (v1.var_type = v2.var_type && v1.index < v2.index)))
        then (v1.link <- TLink t2; linked_variables_snd := v1 :: !linked_variables_snd)
        else (v2.link <- TLink t1; linked_variables_snd := v2 :: !linked_variables_snd)
    | Var v1, _ -> if var_occurs_or_out_of_world v1 t2 then raise Not_unifiable else (v1.link <- TLink t2; linked_variables_snd := v1 :: !linked_variables_snd)
    | _, Var v2 -> if var_occurs_or_out_of_world v2 t1 then raise Not_unifiable else (v2.link <- TLink t1; linked_variables_snd := v2 :: !linked_variables_snd)
    | AxName n1, AxName n2 when n1 = n2 -> ()
    | Func(f1,args1), Func(f2,args2) when f1 == f2 -> List.iter2 unify_term_recipe args1 args2
    | _ -> raise Not_unifiable

  let unify_protocol (eq_list:(protocol_term * protocol_term) list) =
    try
      List.iter (fun (t1,t2) -> unify_term_protocol t1 t2) eq_list;

      let subst = List.fold_left (fun acc var -> (var,follow_link_var var)::acc) [] !linked_variables_fst in

      List.iter (fun var -> var.link <- NoLink) !linked_variables_fst;
      linked_variables_fst := [];

      subst
    with Not_unifiable ->
      List.iter (fun var -> var.link <- NoLink) !linked_variables_fst;
      linked_variables_fst := [];
      raise Not_unifiable

  let unify_protocol_opt (eq_list:(protocol_term * protocol_term) list) =
    try
      List.iter (fun (t1,t2) -> unify_term_protocol t1 t2) eq_list;

      let subst = List.fold_left (fun acc var -> (var,follow_link_var var)::acc) [] !linked_variables_fst in

      List.iter (fun var -> var.link <- NoLink) !linked_variables_fst;
      linked_variables_fst := [];

      Some subst
    with Not_unifiable ->
      List.iter (fun var -> var.link <- NoLink) !linked_variables_fst;
      linked_variables_fst := [];
      None

  let unify_recipe (eq_list:(recipe * recipe) list) =
    try
      List.iter (fun (t1,t2) -> unify_term_recipe t1 t2) eq_list;

      let subst = List.fold_left (fun acc var -> (var,follow_link_var var)::acc) [] !linked_variables_snd in

      List.iter (fun var -> var.link <- NoLink) !linked_variables_snd;
      linked_variables_snd := [];

      subst
    with Not_unifiable ->
      List.iter (fun var -> var.link <- NoLink) !linked_variables_snd;
      linked_variables_snd := [];
      raise Not_unifiable

  let is_unifiable (eq_list:(protocol_term * protocol_term) list) =
    try
      List.iter (fun (t1,t2) -> unify_term_protocol t1 t2) eq_list;

      List.iter (fun var -> var.link <- NoLink) !linked_variables_fst;
      linked_variables_fst := [];

      true
    with Not_unifiable ->
      List.iter (fun var -> var.link <- NoLink) !linked_variables_fst;
      linked_variables_fst := [];
      false

  (******* Syntactic match *******)

  exception Not_matchable

  let rec match_term : 'a 'b. ('a,'b) atom -> ('a,'b) term -> ('a,'b) term -> unit = fun (type a) (type b) (at:(a, b) atom) (t1:(a, b) term) (t2:(a, b) term) -> match t1.term,t2.term with
    | Var({link = TLink t ; _}), _ ->
        if not (is_equal at t t2)
        then raise Not_matchable
    (*| _, Var({link = TLink _; _}) -> Config.internal_error "[term.ml >> Subst.match_term] Unexpected link"*)
    | Var(v1),_ -> link at v1 t2
    | AxName(n1), AxName(n2) when AxName.is_equal at n1 n2 -> ()
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
      true
    with Not_matchable ->
      cleanup at;
      false

  let match_terms at term_list1 term_list2 =
    Config.debug (fun () ->
      if retrieve at <> []
      then Config.internal_error "[term.ml >> Subst.is_matchable] The list of linked variables should be empty.";

      if List.length term_list1 <> List.length term_list2
      then Config.internal_error "[term.ml >> Subst.is_matchable] Both lists should have the same size.";
    );

    try
      List.iter2 (match_term at) term_list1 term_list2;
      let list_vars = retrieve at in
      let subst =
        List.rev_map (fun x -> match x.link with
          | TLink t -> (x,t)
          | _ -> Config.internal_error "[term.ml >> Subst.match_terms] All variables should be linked."
        ) list_vars
      in
      cleanup at;
      Some subst
    with Not_matchable ->
      cleanup at;
      None

  (********** is_equal_equations **********)

  let rec is_equal_linked_terms at t1 t2 = match t1.term,t2.term with
    | Var(v1),Var(v2) when Variable.is_equal v1 v2 -> true
    | Var({link = TLink t;_}), _ -> is_equal_linked_terms at t t2
    | _, Var({link = TLink t;_}) -> is_equal_linked_terms at t1 t
    | Var _ , _ | _ , Var _ -> false
    | AxName(n1),AxName(n2) when AxName.is_equal at n1 n2 -> true
    | Func(f1,args1), Func(f2,args2) when Symbol.is_equal f1 f2 -> List.for_all2 (is_equal_linked_terms at) args1 args2
    | _,_ -> false

  let is_equal_equations at subst_1 subst_2 =

    (* Link the variables of the substitution *)
    List.iter (fun (v,t) ->
      match t.term with
        | Var v' -> if Variable.order at v v' < 0 then link at v t else link at v' ({term = Var v; ground = false})
        | _ -> link at v t
    ) subst_1;

    let result = List.for_all (fun (v,t) -> is_equal_linked_terms at ({ term = Var v; ground = false }) t) subst_2 in

    cleanup at;
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
          | Recipe -> ()
          | Protocol ->
              List.iter (fun (t1,t2) ->
                get_names_protocol t1;
                get_names_protocol t2
              ) diseq_l
        end;

        let result = Name.retrieve_search () in
        Name.cleanup_search ();
        result

  let get_vars_with_list (type a) (type b) (at:(a,b) atom) (diseq:(a,b) t) (l:(a,b) variable list) = match diseq with
    | Top | Bot -> l
    | Diseq diseq_l ->
        Config.test (fun () ->
          if retrieve_search at <> []
          then Config.internal_error "[terml.ml >> Diseq.get_vars_with_list] Linked variables should be empty."
        );

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

  let of_substitution_recipe (sigma:(snd_ord,axiom) Subst.t) (l:(snd_ord, axiom) variable list) =
    if sigma = []
    then Bot
    else if l = []
    then Diseq (Subst.equations_of sigma)
    else
      begin
        Config.test (fun () ->
          if retrieve_search Recipe <> [] ||  Variable.Renaming.retrieve Recipe <> []
          then Config.internal_error "[terml.ml >> of_substitution] Linked variables should be empty."
        );
        List.iter (fun v ->
          let v' = Variable.fresh Recipe Universal (Variable.snd_ord_type (Variable.type_of v)) in
          Variable.Renaming.link Recipe v v'
        ) l;
        let diseq = List.fold_left (fun acc (v,t) ->
          if v.link = NoLink
          then (({ term = Var v; ground = false }),Variable.Renaming.follow_link t)::acc
          else acc
          ) [] sigma
        in

        Variable.Renaming.cleanup Recipe;
        if diseq = []
        then Bot
        else Diseq diseq
      end

  let of_substitution_protocol (sigma:(fst_ord,name) Subst.t) =
    if sigma = []
    then Bot
    else Diseq (Subst.equations_of sigma)

  let rec rename_universal_to_existential at term =
    if term.ground
    then term
    else
      match term.term with
        | Var(v) when v.quantifier = Universal ->
            begin match v.link with
              | VLink(v') -> { term = Var(v'); ground = false }
              | NoLink ->
                  let v' = Variable.fresh_with_label Existential v.var_type v.label in
                  Variable.Renaming.link at v v';
                  { term = Var(v') ; ground = false }
              | _ -> Config.internal_error "[term.ml >> Subst.rename] Unexpected link"
            end
        | Func(f,args) -> { term = Func(f, List.map (rename_universal_to_existential at) args); ground = false }
        | _ -> term

  let rec check_disjoint_domain at = function
    | [] -> true
    | (x,_) :: q ->
        if (List.exists (fun (y,_) -> is_equal at x y) q)
        then false
        else check_disjoint_domain at q

  let substitution_of (form:(fst_ord, name) t) = match form with
    | Top -> []
    | Bot -> Config.internal_error "[term.ml >> Diseq.substitution_of] The disequation should not be bot."
    | Diseq diseq ->
        Config.debug (fun () ->
          if List.exists (fun (t,_) -> not (is_variable t) || Variable.quantifier_of (variable_of t) = Universal) diseq
          then Config.internal_error "[term.ml >> Diseq.substitution_of] The disequation should not be in normal form (1)";

          if not (check_disjoint_domain Protocol diseq)
          then Config.internal_error "[term.ml >> Diseq.substitution_of] The disequation should not be in normal form (2)";

          if List.exists (fun (x,_) -> List.exists (fun (_,t) -> var_occurs (variable_of x) t) diseq) diseq
          then Config.internal_error "[term.ml >> Diseq.substitution_of] The disequation should not be in normal form (3)"
        );


        let subst = List.fold_left (fun acc (t1,t2) -> (variable_of t1, rename_universal_to_existential Protocol t2)::acc) [] diseq in

        Variable.Renaming.cleanup Protocol;
        subst

  let elim_universal_variables var_list =

    let rec explore acc = function
      | [] -> acc
      | v::q when v.quantifier = Universal -> explore acc q
      | v::q -> explore ((({ term = Var v; ground = false}), Subst.follow_link_var v)::acc) q
    in
    explore [] var_list

  let apply_and_normalise_protocol (subst:(fst_ord,name) Subst.t) (diseq:((fst_ord,name) term * (fst_ord,name) term) list) =
    (* Link the variables of the substitution *)
    List.iter (fun (v,t) -> v.link <- (TLink t)) subst;

    try
      List.iter (fun (t1,t2) -> Subst.unify_term_protocol t1 t2) diseq;

      let diseq' = List.fold_left (fun acc var -> if var.quantifier = Universal then acc else ({ term = Var var; ground = false},Subst.follow_link_var var)::acc) [] !Subst.linked_variables_fst in

      List.iter (fun (v,_) -> v.link <- NoLink) subst;
      List.iter (fun var -> var.link <- NoLink) !Subst.linked_variables_fst;
      Subst.linked_variables_fst := [];

      if diseq' = []
      then Bot
      else Diseq diseq'
    with Subst.Not_unifiable ->
      List.iter (fun (v,_) -> v.link <- NoLink) subst;
      List.iter (fun var -> var.link <- NoLink) !Subst.linked_variables_fst;
      Subst.linked_variables_fst := [];
      Top

  let apply_and_normalise_recipe (subst:(snd_ord,axiom) Subst.t) (diseq:((snd_ord,axiom) term * (snd_ord,axiom) term) list) =
    (* Link the variables of the substitution *)
    List.iter (fun (v,t) -> v.link <- (TLink t)) subst;

    try
      List.iter (fun (t1,t2) -> Subst.unify_term_recipe t1 t2) diseq;

      let diseq' = List.fold_left (fun acc var -> if var.quantifier = Universal then acc else ({ term = Var var; ground = false},Subst.follow_link_var var)::acc) [] !Subst.linked_variables_snd in

      List.iter (fun (v,_) -> v.link <- NoLink) subst;
      List.iter (fun var -> var.link <- NoLink) !Subst.linked_variables_snd;
      Subst.linked_variables_snd := [];

      if diseq' = []
      then Bot
      else Diseq diseq'
    with Subst.Not_unifiable ->
      List.iter (fun (v,_) -> v.link <- NoLink) subst;
      List.iter (fun var -> var.link <- NoLink) !Subst.linked_variables_snd;
      Subst.linked_variables_snd := [];
      Top

  let apply_and_normalise (type a) (type b) (at:(a, b) atom) (subst:(a,b) Subst.t) (dis:(a,b) t) = match dis with
    | Top -> (Top:(a,b) t)
    | Bot -> (Bot:(a,b) t)
    | Diseq diseq ->
        match at with
          | Protocol -> ((apply_and_normalise_protocol subst diseq):(a,b) t)
          | Recipe -> ((apply_and_normalise_recipe subst diseq):(a,b) t)

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
              Config.test (fun () ->
                if retrieve_search at <> []
                then Config.internal_error "[terml.ml >> Diseq.display] Linked variables should be empty."
              );
              let rec find_univ_var_term term =
                if not term.ground
                then
                  match term.term with
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

  let create_for_testing l =
    Config.test (fun () ->
      if l = []
      then Config.internal_error "[term.ml >> Diseq.create_for_testing] Should only be used for non top and bot disequations"
    );
    Diseq l

  module Mixed = struct

    type t =
      | MTop
      | MBot
      | MDiseq of (protocol_term * protocol_term) list * (recipe * recipe) list

    let is_top = function
      | MTop -> true
      | _ -> false

    let is_bot = function
      | MBot -> true
      | _ -> false

    let apply_and_normalise (fst_subst:(fst_ord,name) Subst.t) (snd_subst:(snd_ord,axiom) Subst.t) = function
      | MTop -> MTop
      | MBot -> MBot
      | MDiseq(term_l,recipe_l) ->
          Config.debug (fun () ->
            if List.exists (fun (v,_) -> v.link <> NoLink) fst_subst || List.exists (fun (v,_) -> v.link <> NoLink) snd_subst
            then Config.internal_error "[term.ml >> Diseq.Mixed.apply_and_normalise] Variables in the domain should not be linked"
          );

          Config.debug (fun () ->
            if List.exists (fun (v,t) -> Variable.quantifier_of v = Universal || quantified_var_occurs Universal t) fst_subst ||
               List.exists (fun (v,t) -> Variable.quantifier_of v = Universal || quantified_var_occurs Universal t) snd_subst
            then Config.internal_error "[term.ml >> Diseq.apply_and_normalise] Variables in the substitutions should not be universal"
          );

          let apply_term () =
            List.iter (fun (v,t) -> v.link <- (TLink t)) fst_subst;

            List.iter (fun (t1,t2) -> Subst.unify_term_protocol t1 t2) term_l;

            let result =
              List.fold_left (fun acc v ->
                if v.quantifier = Universal
                then acc
                else ({ term = Var v; ground = false}, Subst.follow_link_var v)::acc
              ) [] (Subst.retrieve Protocol)
            in

            Subst.cleanup Protocol;
            List.iter (fun (v,_) -> v.link <- NoLink) fst_subst;

            result
          in

          let apply_recipe () =
            List.iter (fun (v,t) -> v.link <- (TLink t)) snd_subst;

            List.iter (fun (t1,t2) -> Subst.unify_term_recipe t1 t2) recipe_l;

            let result =
              List.fold_left (fun acc v ->
                if v.quantifier = Universal
                then acc
                else ({ term = Var v; ground = false}, Subst.follow_link_var v)::acc
              ) [] (Subst.retrieve Recipe)
            in

            Subst.cleanup Recipe;
            List.iter (fun (v,_) -> v.link <- NoLink) snd_subst;

            result
          in

          if term_l = [] || fst_subst = []
          then
            if recipe_l = [] || snd_subst = []
            then MDiseq(term_l,recipe_l)
            else
              begin try
                let new_recipe_l = apply_recipe () in
                if term_l = [] && new_recipe_l = []
                then MBot
                else MDiseq(term_l,new_recipe_l)
              with Subst.Not_unifiable ->
                Subst.cleanup Recipe;
                List.iter (fun (v,_) -> v.link <- NoLink) snd_subst;
                MTop
              end
          else
            if recipe_l = [] || snd_subst = []
            then
              begin try
                let new_term_l = apply_term () in
                if new_term_l = [] && recipe_l = []
                then MBot
                else MDiseq(new_term_l,recipe_l)
              with Subst.Not_unifiable ->
                Subst.cleanup Protocol;
                List.iter (fun (v,_) -> v.link <- NoLink) fst_subst;
                MTop
              end
            else
              begin try
                let new_term_l = apply_term () in

                begin try
                  let new_recipe_l = apply_recipe () in
                  if new_term_l = [] && new_recipe_l = []
                  then MBot
                  else MDiseq(new_term_l,new_recipe_l)
                with Subst.Not_unifiable ->
                  Subst.cleanup Recipe;
                  List.iter (fun (v,_) -> v.link <- NoLink) snd_subst;
                  MTop
                end
              with Subst.Not_unifiable ->
                Subst.cleanup Protocol;
                List.iter (fun (v,_) -> v.link <- NoLink) fst_subst;
                MTop
              end
  end

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

  let get_names_eq_with_list (t1,t2) n_l = get_names_with_list Protocol t1 (get_names_with_list Protocol t2 n_l)

  let get_vars_diseq_with_list (t1,t2) f v_l = get_vars_with_list Protocol t1 f (get_vars_with_list Protocol t2 f v_l)

  let get_names_diseq_with_list (t1,t2) n_l = get_names_with_list Protocol t1 (get_names_with_list Protocol t2 n_l)
  (****** Display *******)

  let display_equation out ?(rho=None) (t1,t2) =
    Printf.sprintf "%s %s %s" (display out ~rho:rho Protocol t1) (eqi out) (display out ~rho:rho Protocol t2)

  let display_disequation out ?(rho=None) (t1,t2) =
    Printf.sprintf "%s %s %s" (display out ~rho:rho Protocol t1) (neqi out) (display out ~rho:rho Protocol t2)

  let rec rewrite_term_list quantifier list_t next_f = match list_t with
    | [] -> next_f (true,[])
    | t::q ->
        rewrite_term quantifier t (fun t' ->
          rewrite_term_list quantifier q (fun (g,q') -> next_f (g&&t'.ground,t'::q'))
        )

  and rewrite_term quantifier t next_f = match t.term with
    | Func(f1,args) ->
        begin match f1.cat with
          | Constructor | Tuple ->
              rewrite_term_list quantifier args (fun (g,args') -> next_f { term = Func(f1,args'); ground = g })
          | Destructor (rw_rules) ->
              rewrite_term_list quantifier args (fun (_,args') ->
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
                    List.iter2 (Subst.unify_term_protocol) lhs' args';
                    let saved_linked_variables_from_unify = !Subst.linked_variables_fst in
                    Subst.linked_variables_fst := List.rev_append !Subst.linked_variables_fst saved_linked_variables;

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
                  Subst.unify_term_protocol t1' t2';
                  let saved_linked_variables_from_unify = !Subst.linked_variables_fst in
                  Subst.linked_variables_fst := List.rev_append !Subst.linked_variables_fst saved_linked_variables;

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
          Subst.unify_term_protocol t1' t2';
          let saved_linked_variables_from_unify = !Subst.linked_variables_fst in
          Subst.linked_variables_fst := List.rev_append !Subst.linked_variables_fst saved_linked_variables;

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
      pterm : protocol_term
    }

  (********* Generation *********)

  let create x t = { var = x; pterm = t }

  (********* Access *********)

  let get_snd_ord_variable b_fact = b_fact.var

  let get_protocol_term b_fact = b_fact.pterm

  (********* Display *********)

  let display out ?(rho=None) ded =
    match out with
      | Latex -> Printf.sprintf "%s \\vdash^? %s" (Variable.display out ~rho:rho Recipe ~v_type:true ded.var) (display out ~rho:rho Protocol ded.pterm)
      | _ -> Printf.sprintf "%s %s %s" (Variable.display out ~rho:rho Recipe ~v_type:true ded.var) (vdash out) (display out ~rho:rho Protocol ded.pterm)

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
      equation_subst : (fst_ord, name) Subst.t
    }

  exception Bot

  type deduction_formula = deduction formula

  type equality_formula = equality formula

  (********* Generation ********)

  let create_deduction_fact recipe term = { df_recipe = recipe; df_term = term }

  let create_equality_fact recipe_1 recipe_2 = { ef_recipe_1 = recipe_1; ef_recipe_2 = recipe_2 }

  let create (type a) (fct: a t) (head: a) equations =

    try
      List.iter (fun (t1,t2) -> Subst.unify_term_protocol t1 t2) equations;

      if Subst.retrieve Protocol = []
      then ({ head = head ; equation_subst = []} : a formula)
      else
        begin match fct with
          | Deduction ->
              let new_head = { head with df_term = Subst.follow_link head.df_term }
              and subst = List.fold_left (fun acc var -> if var.quantifier = Universal then acc else (var,Subst.follow_link_var var)::acc ) [] (Subst.retrieve Protocol) in
              Subst.cleanup Protocol;
              ({ head = new_head; equation_subst = subst }: a formula)
          | Equality ->
              let subst = List.fold_left (fun acc var -> (var,Subst.follow_link_var var)::acc) [] (Subst.retrieve Protocol) in
              Subst.cleanup Protocol;
              ({ head = head; equation_subst = subst }: a formula)
        end
    with Subst.Not_unifiable -> Subst.cleanup Protocol; raise Bot

  (********* Access ********)

  let get_recipe fct = fct.df_recipe

  let get_protocol_term fct = fct.df_term

  let get_both_recipes fct = fct.ef_recipe_1, fct.ef_recipe_2

  let get_head form = form.head

  let get_mgu_hypothesis form = form.equation_subst

  let get_vars_with_list (type a) (type b) (type c) (at: (a,b) atom) (fct: c t) (form: c formula) f_quanti (v_list: (a,b) variable list) = match at with
    | Protocol ->
        Config.test (fun () ->
          if retrieve_search Protocol <> []
          then Config.internal_error "[terml.ml >> Modulo.get_vars_with_list] Linked variables should be empty."
        );

        List.iter (link_search Protocol) v_list;

        List.iter (fun (x,t) ->
          begin match x.link with
            | NoLink when f_quanti x.quantifier -> link_search Protocol x
            | FLink | NoLink -> ()
            | _ -> Config.internal_error "[term.ml >> Fact.get_wars_with_list] Unexpected link"
          end;
          get_vars_term Protocol f_quanti t
        ) form.equation_subst;

        begin match fct with
          | Deduction -> get_vars_term Protocol f_quanti form.head.df_term
          | Equality -> ()
        end;

        let result = retrieve_search Protocol in
        cleanup_search Protocol;
        (result: (a,b) variable list)
    | Recipe ->
        Config.test (fun () ->
          if retrieve_search at <> []
          then Config.internal_error "[terml.ml >> Modulo.get_vars_with_list] Linked variables should be empty. (2)"
        );
        List.iter (link_search Recipe) v_list;

        begin match fct with
          | Deduction -> get_vars_term Recipe f_quanti form.head.df_recipe
          | Equality -> get_vars_term Recipe f_quanti form.head.ef_recipe_1; get_vars_term Recipe f_quanti form.head.ef_recipe_2
        end;

        let result = retrieve_search Recipe in
        cleanup_search Recipe;
        (result: (a,b) variable list)

  let get_names_with_list (type a) (fct: a t) (form: a formula) (n_list: name list) =
    List.iter Name.link_search n_list;

    List.iter (fun (_,t) -> get_names_protocol t) form.equation_subst;

    begin match fct with
      | Deduction ->
          get_names_protocol form.head.df_term
      | Equality -> ()
    end;

    let result = Name.retrieve_search () in
    Name.cleanup_search ();
    result

  let get_axioms_with_list (type a) (fct: a t) (form: a formula) f_ax ax_list = match fct with
    | Deduction -> get_axioms_with_list form.head.df_recipe f_ax ax_list
    | Equality -> get_axioms_with_list form.head.ef_recipe_1 f_ax (get_axioms_with_list form.head.ef_recipe_2 f_ax ax_list)

  let rec search_term term =
    if not term.ground
    then
      match term.term with
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
    Config.test (fun () ->
      if retrieve_search Protocol <> []
      then Config.internal_error "[terml.ml >> Fact.universal_variables] Linked variables should be empty.(1)";
      if retrieve_search Recipe <> []
      then Config.internal_error "[terml.ml >> Fact.universal_variables] Linked variables should be empty.(2)"
    );
    search_equation_subst form.equation_subst;

    let vars_fst = retrieve_search Protocol in

    cleanup_search Protocol;
    vars_fst

  (********* Modification *********)

  let apply_fst_function_on_deduction_fact f fact = { fact with df_term = f fact.df_term }

  let apply_snd_function_on_deduction_fact f fact = { fact with df_recipe = f fact.df_recipe }

  let apply_both_functions_on_deduction_fact f_fst f_snd fact = { df_term = f_fst fact.df_term; df_recipe = f_snd fact.df_recipe }

  (********* Testing *********)

  let is_fact psi = psi.equation_subst = []

  (********** Application of substitution *********)

  let apply_fst_on_deduction_fact (subst_fst: (fst_ord,name) Subst.t) fact =
    Config.debug (fun () ->
      if List.exists (fun (v,_) -> v.link <> NoLink) subst_fst
      then Config.internal_error "[term.ml >> Fact.apply_fst_on_deduction_fact] Variables in the domain should not be linked"
    );

    (* Link the variables of the substitution *)
    List.iter (fun (v,t) -> v.link <- (TLink t)) subst_fst;

    let fact' = { fact with df_term = Subst.apply_on_term fact.df_term } in

    (* Clean the variables of the substitution *)
    List.iter (fun (v,_) -> v.link <- NoLink) subst_fst;

    fact'

  let apply_snd_on_fact (type a) (fct: a t) (subst_snd: (snd_ord,axiom) Subst.t) (fact:a) =
    Config.debug (fun () ->
      if List.exists (fun (v,_) -> v.link <> NoLink) subst_snd
      then Config.internal_error "[term.ml >> Fact.apply_snd_on_fact] Variables in the domain should not be linked"
    );

    (* Link the variables of the substitution *)
    List.iter (fun (v,t) -> v.link <- (TLink t)) subst_snd;

    match fct with
      | Deduction ->
          let fact' = { fact with df_recipe = Subst.apply_on_term fact.df_recipe } in
          (* Clean the variables of the substitution *)
          List.iter (fun (v,_) -> v.link <- NoLink) subst_snd;
          (fact':a)
      | Equality ->
          let fact' = { ef_recipe_1 = Subst.apply_on_term fact.ef_recipe_1; ef_recipe_2 = Subst.apply_on_term fact.ef_recipe_2 } in
          (* Clean the variables of the substitution *)
          List.iter (fun (v,_) -> v.link <- NoLink) subst_snd;
          (fact':a)

  let apply_on_deduction_fact (subst_snd: (snd_ord,axiom) Subst.t) (subst_fst: (fst_ord,name) Subst.t) fact =
    Config.debug (fun () ->
      if List.exists (fun (v,_) -> v.link <> NoLink) subst_fst || List.exists (fun (v,_) -> v.link <> NoLink) subst_snd
      then Config.internal_error "[term.ml >> Fact.apply_fst_on_deduction_fact] Variables in the domain should not be linked"
    );

    (* Link the variables of the substitution *)
    List.iter (fun (v,t) -> v.link <- (TLink t)) subst_fst;
    List.iter (fun (v,t) -> v.link <- (TLink t)) subst_snd;

    let fact' = { df_recipe = Subst.apply_on_term fact.df_recipe; df_term = Subst.apply_on_term fact.df_term } in

    (* Clean the variables of the substitution *)
    List.iter (fun (v,_) -> v.link <- NoLink) subst_fst;
    List.iter (fun (v,_) -> v.link <- NoLink) subst_snd;

    fact'

  let apply_fst_on_formula (type a) (fct: a t) (subst_fst: (fst_ord,name) Subst.t) (psi: a formula) =
    Config.debug (fun () ->
      if List.exists (fun (v,_) -> v.link <> NoLink) subst_fst
      then Config.internal_error "[term.ml >> Fact.apply_fst_on_formula] Variables in the domain should not be linked"
    );

    (* Link the variables of the substitution *)
    List.iter (fun (v,t) -> v.link <- (TLink t)) subst_fst;

    try
      List.iter (fun (x,t) -> Subst.unify_term_protocol {term = Var x; ground = false} t) psi.equation_subst;

      begin match fct with
        | Deduction ->
            let head = { psi.head with df_term = Subst.follow_link psi.head.df_term }
            and equation_subst = List.fold_left (fun acc var -> if var.quantifier = Universal then acc else (var,Subst.follow_link_var var)::acc) [] (Subst.retrieve Protocol) in

            let psi_1 = { head = head; equation_subst = equation_subst } in

            Subst.cleanup Protocol;

            (* Unlink the variables of the substitution *)
            List.iter (fun (v,_) -> v.link <- NoLink) subst_fst;

            (* Apply the second-order substitution *)

            (psi_1: a formula)

        | Equality ->
            let equation_subst = List.fold_left (fun acc var -> if var.quantifier = Universal then acc else (var,Subst.follow_link_var var)::acc) [] (Subst.retrieve Protocol) in

            let psi_1 = { psi with equation_subst = equation_subst } in

            Subst.cleanup Protocol;

            (* Unlink the variables of the substitution *)
            List.iter (fun (v,_) -> v.link <- NoLink) subst_fst;

            (psi_1: a formula)
      end
    with Subst.Not_unifiable ->
      Subst.cleanup Protocol;
      (* Unlink the variables of the substitution *)
      List.iter (fun (v,_) -> v.link <- NoLink) subst_fst;
      raise Bot

  let apply_snd_on_formula (type a) (fct: a t) (subst_snd : (snd_ord,axiom) Subst.t) (psi: a formula) = match fct with
    | Deduction ->
        (* Link the variables of the substitution *)
        List.iter (fun (v,t) -> v.link <- TLink t) subst_snd;

        let psi' = { psi with head = { psi.head with df_recipe = Subst.apply_on_term psi.head.df_recipe } } in

        (* Unlink the variables of the substitution *)
        List.iter (fun (v,_) -> v.link <- NoLink) subst_snd;

        (psi': a formula)
    | Equality ->
        (* Link the variables of the substitution *)
        List.iter (fun (v,t) -> v.link <- TLink t) subst_snd;

        let psi' = { psi with head = { ef_recipe_1 = Subst.apply_on_term psi.head.ef_recipe_1; ef_recipe_2 = Subst.apply_on_term psi.head.ef_recipe_2 } } in

        (* Unlink the variables of the substitution *)
        List.iter (fun (v,_) -> v.link <- NoLink) subst_snd;

        (psi': a formula)

  (********** Replacement of recipes *********)

  let replace_recipe_in_deduction_fact r fact = { fact with df_recipe = r }

  let replace_recipe_in_deduction_formula r form = { form with head = { form.head with df_recipe = r} }

  let replace_head_in_equality_formula (fact:equality) (form:equality_formula) = { form with head = fact }

  (********* Display functions *******)

  let display_fact (type a) out ?(rho=None) (fct:a t) (ded_ef:a) = match fct with
    | Deduction -> Printf.sprintf "%s %s %s" (display out ~rho:rho Recipe ded_ef.df_recipe) (vdash out) (display out ~rho:rho Protocol ded_ef.df_term)
    | Equality -> Printf.sprintf "%s %s %s" (display out ~rho:rho Recipe ded_ef.ef_recipe_1) (eqf out) (display out ~rho:rho Recipe ded_ef.ef_recipe_2)

  let display_deduction_fact out ?(rho=None) fct = display_fact out ~rho:rho Deduction fct

  let display_equality_fact out ?(rho=None) fct = display_fact out ~rho:rho Equality fct

  let rec find_univ_var at term =
    if not term.ground
    then
      match term.term with
        | Var v when v.link = FLink -> ()
        | Var v when v.quantifier = Universal -> link_search at v
        | Func(_,args) -> List.iter (find_univ_var at) args
        | _ -> ()

  let display_formula (type a) out ?(rho=None) (fct:a t) (psi:a formula) = match out with
    | Testing ->
        Printf.sprintf "%s %s %s"
          (display_fact out ~rho:rho fct psi.head)
          (lLeftarrow out)
          (Subst.display out ~rho:rho Protocol psi.equation_subst)
    | _ ->
        begin
          Config.test (fun () ->
            if retrieve_search Protocol <> []
            then Config.internal_error "[terml.ml >> Fact.display] Linked variables should be empty.(1)";
            if retrieve_search Recipe <> []
            then Config.internal_error "[terml.ml >> Fact.display] Linked variables should be empty.(2)"
          );
          begin match fct with
            | Deduction ->
                find_univ_var Recipe psi.head.df_recipe;
                find_univ_var Protocol psi.head.df_term
            | Equality ->
                find_univ_var Recipe psi.head.ef_recipe_1;
                find_univ_var Recipe psi.head.ef_recipe_2
          end;

          List.iter (fun (t1,t2) ->
            find_univ_var Protocol t2;
            if t1.link <> FLink && t1.quantifier = Universal
            then link_search Protocol t1
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

          match psi.equation_subst with
            | [] -> display_fact out ~rho:rho fct psi.head
            | _ -> Printf.sprintf "%s %s %s %s"
                forall_str
                (display_fact out ~rho:rho fct psi.head)
                (lLeftarrow out)
                (display_list (fun (t1,t2) -> Printf.sprintf "%s %s %s" (display out ~rho:rho Protocol ({ term = Var t1; ground = false})) (eqs out) (display out ~rho:rho Protocol t2)) (Printf.sprintf " %s " (wedge out)) psi.equation_subst)
        end
end

(***************************************************
***                Patterns                      ***
****************************************************)

type pattern =
  | PatOther
  | PatTuple of symbol * pattern list

let rec is_equal_pattern pat1 pat2 = match pat1,pat2 with
  | PatOther, PatOther -> true
  | PatTuple(f1,args1), PatTuple(f2,args2) -> f1 == f2 && List.for_all2 is_equal_pattern args1 args2
  | _, _ -> false

let extract_pattern_of_deduction_fact fact =

  let acc_facts = ref [] in

  let rec internal recipe term = match term.term with
    | Func(f,args) when f.cat = Tuple ->
        let projections = HashtblSymb.find Symbol.all_projection f in
        let pat_args = List.map2 (fun f_proj t -> internal { term = Func(f_proj,[recipe]); ground = recipe.ground } t) projections args in
        PatTuple(f,pat_args)
    | _ ->
        acc_facts := { Fact.df_recipe = recipe; Fact.df_term = term} :: !acc_facts;
        PatOther
  in

  match internal fact.Fact.df_recipe fact.Fact.df_term with
    | PatOther -> None
    | pat -> Some (pat, !acc_facts)

(***************************************************
***    Rewrite rules   ***
****************************************************)

module Rewrite_rules = struct

  type skeleton =
    {
      pos_vars : snd_ord_variable;
      pos_term : protocol_term;
      snd_vars : snd_ord_variable list;
      recipe : recipe;
      basic_deduction_facts : BasicFact.t list;

      lhs : protocol_term list;
      rhs : protocol_term
    }

  type stored_skeleton =
    {
      skeleton : skeleton;
      compat_rewrite_rules : (protocol_term list * protocol_term) list
    }

  let dummy_skeleton =
    let dummy_var_snd = Variable.fresh Recipe Existential 0
    and dummy_var_fst = Variable.fresh Protocol Existential NoType in
    {
      pos_vars = dummy_var_snd;
      pos_term = of_variable dummy_var_fst;
      snd_vars = [];
      recipe = of_variable dummy_var_snd;
      basic_deduction_facts = [];

      lhs = [];
      rhs = of_variable dummy_var_fst;
    }

  let storage_skeletons = ref (Array.make 0 { skeleton = dummy_skeleton; compat_rewrite_rules = [] })

  let index_skeletons = ref []

  (****** Normalisation ******)

  exception Found_normalise of protocol_term

  let rec normalise t = match t.term with
    | Func(f1,args) ->
        begin match f1.cat with
          | Constructor | Tuple ->
              let (ground,args') =
                List.fold_right (fun t (g,t_list) ->
                  let t' = normalise t in
                  (g&&t'.ground,t'::t_list)
                ) args (true,[])
              in
              {term = Func(f1,args'); ground = ground}
          | Destructor (rw_rules) ->
              let (ground,args') =
                List.fold_right (fun t (g,t_list) ->
                  let t' = normalise t in
                  (g&&t'.ground,t'::t_list)
                ) args (true,[])
              in
              begin try
                List.iter (fun (lhs,rhs) ->
                  (***[BEGIN DEBUG]***)
                  Config.debug (fun () ->
                    if !Variable.Renaming.linked_variables_fst <> []
                    then Config.internal_error "[term.ml >> Rewrite_rules.normalise] The list of linked variables for renaming should be empty";

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
                { term = Func(f1, args'); ground = ground }
              with Found_normalise t' -> t'
              end
        end
    | _ -> t

  let rewrite_rule_recipe (lhs,rhs) =

    let assoc_list = ref [] in

    let rec explore_term term = match term.term with
      | Var v ->
          let v_recipe =
            try
              List.assq v !assoc_list
            with
              | Not_found ->
                  let v_r = Variable.fresh Recipe Existential max_int in
                  assoc_list := (v,v_r) :: !assoc_list;
                  v_r
          in
          { term = Var v_recipe; ground = false }
      | Func(f,args) -> { term = Func(f,List.map explore_term args); ground = term.ground }
      | _ -> Config.internal_error "[term.ml >> Rewrite_rules.rewrite_rule_recipe] A rewrite rule should not contain any name."
    in

    (List.map explore_term lhs, explore_term rhs)

  exception Found_normalise_recipe of recipe

  let rec normalise_recipe t = match t.term with
    | Func(f1,args) ->
        begin match f1.cat with
          | Constructor | Tuple ->
              let (ground,args') =
                List.fold_right (fun t (g,t_list) ->
                  let t' = normalise_recipe t in
                  (g&&t'.ground,t'::t_list)
                ) args (true,[])
              in
              {term = Func(f1,args'); ground = ground}
          | Destructor (rw_rules) ->
              let (ground,args') =
                List.fold_right (fun t (g,t_list) ->
                  let t' = normalise_recipe t in
                  (g&&t'.ground,t'::t_list)
                ) args (true,[])
              in
              begin try
                List.iter (fun (lhs,rhs) ->
                  let (lhs',rhs') = rewrite_rule_recipe (lhs,rhs) in

                  try
                    List.iter2 (Subst.match_term Recipe) lhs' args';
                    let rhs'' = Subst.follow_link rhs' in
                    Subst.cleanup Recipe;
                    raise (Found_normalise_recipe rhs'')
                  with Subst.Not_matchable ->  Subst.cleanup Recipe
                ) rw_rules;
                { term = Func(f1, args'); ground = ground }
              with Found_normalise_recipe t' -> t'
              end
        end
    | _ -> t

  (****** Initialisation of skeletons ******)

  let rec explore_skel_term (f_continuation:snd_ord_variable -> protocol_term -> recipe -> BasicFact.t list -> unit) (term:protocol_term) = match term.term with
    | Var _ -> ()
    | Func(f,_) when f.arity = 0 ->
        if not f.public
        then
          begin
            Config.test (fun () ->
              if retrieve_search Protocol <> []
              then Config.internal_error "[terml.ml >> Rewrite_rules.explore_skel_term] Linked variables should be empty (1).";
            );

            let x_snd = Variable.fresh Recipe Existential max_int in
            let b_fct = BasicFact.create x_snd term in
            f_continuation x_snd term ({ term = Var x_snd; ground = false}) [b_fct]
          end
    | Func(f,args) ->
        if f.public
        then
          explore_skel_term_list (fun x_snd x_term recipe_l b_fct_l ->
            f_continuation x_snd x_term ({ term = Func(f,recipe_l); ground = false}) b_fct_l
          ) args
        else ();

        Config.test (fun () ->
          if retrieve_search Protocol <> []
          then Config.internal_error "[terml.ml >> Rewrite_rules.explore_skel_term] Linked variables should be empty (2).";
        );

        let x_snd = Variable.fresh Recipe Existential max_int in
        let b_fct = BasicFact.create x_snd term in
        f_continuation x_snd term ({ term = Var x_snd; ground = false}) [b_fct]
    | _ -> Config.internal_error "[term.ml >> Rewrite_rules.explore_skel_term] There should not be any names in the rewrite rules."

  and explore_skel_term_list f_continuation args =
    let (r_list,fct_list) =
      List.fold_right (fun t (acc_r,acc_fct) ->
        let x_snd = Variable.fresh Recipe Existential max_int in
        let b_fct = BasicFact.create x_snd t in
        ((of_variable x_snd)::acc_r, b_fct::acc_fct)
      ) args ([],[])
    in

    let rec go_through prev_r prev_fct next_r next_fct = function
      | [] -> ()
      | t::q ->
          explore_skel_term (fun x_snd x_term recipe b_fct_list ->
            f_continuation x_snd x_term (prev_r @ (recipe :: List.tl next_r)) (prev_fct @ b_fct_list @ (List.tl next_fct))
          ) t;
          go_through (prev_r @ [List.hd next_r]) ((List.hd next_fct)::prev_fct) (List.tl next_r) (List.tl next_fct) q
    in

    go_through [] [] r_list fct_list args

  let consequence_protocol_term (b_fct_list:BasicFact.t list) (term:protocol_term) =

    let rec mem_list = function
      | [] -> Config.internal_error "[term.ml >> Rewrite_rules.consequence_protocol_term] The list should not be empty"
      | [t] ->
          begin match mem_term t with
            | None -> None
            | Some r -> Some (r.ground,[r])
          end
      | t::q_t ->
          begin match mem_term t with
            | None -> None
            | Some r ->
              begin match mem_list q_t with
                | None -> None
                | Some (g,l_r) -> Some(g&&r.ground,r::l_r)
              end
          end

    and mem_term pterm = match pterm.term with
      | Func(f,_) when f.arity = 0 && f.public -> Some ({term = Func(f,[]); ground = true})
      | Func(f,args_t) when f.public ->
          begin match mem_list args_t with
            | None ->
                begin try
                  let b_fct = List.find (fun b_fct -> is_equal Protocol pterm b_fct.BasicFact.pterm) b_fct_list in
                  Some ({term = Var b_fct.BasicFact.var; ground = false})
                with
                  | Not_found -> None
                end
            | Some (g,t_r) -> Some ({term = Func(f,t_r); ground = g})
          end
      | _ ->
          begin try
            let b_fct = List.find (fun b_fct -> is_equal Protocol pterm b_fct.BasicFact.pterm) b_fct_list in
            Some ({term = Var b_fct.BasicFact.var; ground = false})
          with
            | Not_found -> None
          end

    in

    mem_term term

  let rename_recipe_in_protocol_term (recipe:recipe) =
    let assoc_list = ref [] in

    let rec explore_term term = match term.term with
      | Var v ->
          let v_term =
            try
              List.assq v !assoc_list
            with
              | Not_found ->
                  let v_t = Variable.fresh Protocol Existential NoType in
                  assoc_list := (v,v_t) :: !assoc_list;
                  v_t
          in
          { term = Var v_term; ground = false }
      | Func(f,args) -> { term = Func(f,List.map explore_term args); ground = term.ground }
      | _ -> Config.internal_error "[term.ml >> Rewrite_rules.rename_recipe_in_protocol_term] A rewrite rule should not contain any name."
    in

    explore_term recipe

  let initialise_skeletons () =
    let accumulator = ref [] in

    let rec optimise_skeletons skel prev_fct_list = function
      | [] ->
          let r_norm = normalise_recipe skel.recipe in
          if is_equal Recipe r_norm skel.recipe
          then Some skel
          else None
      | fct :: q_fct ->
          let reduced_b_fact_list = List.rev_append q_fct prev_fct_list in
          begin match consequence_protocol_term reduced_b_fact_list fct.BasicFact.pterm with
            | Some r ->
                if Variable.is_equal fct.BasicFact.var skel.pos_vars
                then None
                else
                  begin
                    fct.BasicFact.var.link <- TLink r;
                    let new_recipe = Subst.apply_on_term skel.recipe in
                    fct.BasicFact.var.link <- NoLink;
                    let new_skel = { skel with recipe = new_recipe; basic_deduction_facts = reduced_b_fact_list } in
                    optimise_skeletons new_skel [] reduced_b_fact_list
                  end
            | None -> optimise_skeletons skel (fct::prev_fct_list) q_fct
          end
    in

    (* Generate optimised skeletons *)

    let dest_without_proj = !Symbol.all_destructors in

    List.iter (fun f ->
      if f.public
      then
      match f.cat with
      | Destructor rw_rules->
          List.iter (fun (args,r) ->
            explore_skel_term_list (fun x_snd x_term recipe_l b_fct_list ->
              let skel =
                {
                  pos_vars = x_snd;
                  pos_term = x_term;
                  snd_vars = [];
                  recipe = { term = Func(f,recipe_l); ground = false };
                  basic_deduction_facts = b_fct_list;

                  lhs = args;
                  rhs = r
                }
              in
              match optimise_skeletons skel [] b_fct_list with
                | None -> ()
                | Some skel' ->
                    let (snd_vars, bfct_list) =
                      List.fold_left (fun (acc_vars,acc_bfct) bfct ->
                        if bfct.BasicFact.var == skel'.pos_vars
                        then (acc_vars,acc_bfct)
                        else (bfct.BasicFact.var::acc_vars,bfct::acc_bfct)
                      ) ([],[]) skel'.basic_deduction_facts
                    in
                    accumulator := { skel' with snd_vars = snd_vars; basic_deduction_facts = bfct_list } :: !accumulator
            ) args
          ) rw_rules
      | _ -> Config.internal_error "[term.ml >> Tools_Subterm.initialise_skeletons] There should not be any constructor function symbols in this list."
    ) dest_without_proj;

    (* Generate the array *)

    let nb_skeletons = List.length !accumulator in

    let skeleton_storage = Array.make nb_skeletons { skeleton = dummy_skeleton; compat_rewrite_rules = [] } in

    List.iteri (fun i skel ->
      let p_term = rename_recipe_in_protocol_term skel.recipe in
      let arg_term = get_args p_term in
      let f = root p_term in
      let compa_rw_rules = match f.cat with
        | Destructor rw_rules ->
            List.fold_left (fun acc (lhs,rhs) ->
              Config.debug (fun () ->
                if !Variable.Renaming.linked_variables_fst <> []
                then Config.internal_error "[term.ml >> Rewrite_rules.initialise_skeletons] The list of linked variables for renaming should be empty";

              );
              let lhs' = List.map (Variable.Renaming.rename_term Protocol Universal Variable.fst_ord_type) lhs in
              let rhs' = Variable.Renaming.rename_term Protocol Universal Variable.fst_ord_type rhs in
              Variable.Renaming.cleanup Protocol;

              if Subst.is_unifiable (List.combine lhs' arg_term)
              then (lhs',rhs')::acc
              else acc
            ) [] rw_rules
        | _ -> Config.internal_error "[term.ml >> Rewrite_rules.initialise_skeletons] There should not be any constructor function symbolc in this list (2)."
      in
      let stored_skel = { skeleton = skel; compat_rewrite_rules = compa_rw_rules } in
      skeleton_storage.(i) <- stored_skel
    ) !accumulator;

    storage_skeletons := skeleton_storage;

    (* Generate the index *)

    let rec generate_index = function
      | 0 -> [0]
      | n -> n::(generate_index (n-1))
    in

    if nb_skeletons <> 0
    then index_skeletons := generate_index (nb_skeletons - 1)

  let retrieve_stored_skeletons () = Array.to_list !storage_skeletons

  let setup_stored_skeletons l =
    let ar = Array.of_list l in
    let n = Array.length ar in

    let rec generate_index = function
      | 0 -> [0]
      | n -> n::(generate_index (n-1))
    in

    if n <> 0
    then index_skeletons := generate_index (n - 1);
    storage_skeletons := ar



  (***** checking subterm convergence ****)
  (* the test of convergence is particularly easy in the subterm destructor
  setting, since critical pairs can only appear at the root of rewrite rules. *)

  (* for printing, normalise the indexes of the variables of a term *)
  let normalised_indexes (tl:protocol_term list) : int -> int =
    let mapping =
      []
      |> List.foldl (fun t -> get_vars_with_list Protocol t (fun _ -> true)) tl
      |> List.fast_sort (fun x y -> compare x.index y.index)
      |> List.mapi (fun i x -> (x.index,i)) in
    fun i ->
      match List.assoc_opt i mapping with
      | None -> Config.internal_error "[term.ml >> naormalised_indexes] Unexpected error"
      | Some j -> j



  (* convert a term into a string for message printing. Assumes that no name
  appear. *)
  let rec string_of_term (t:protocol_term) (norm:int->int) : string =
    string_of_generic_term t.term norm

  and string_of_generic_term (t:(fst_ord,name) generic_term) (norm:int->int) : string =
    match t with
    | AxName _ -> Config.internal_error "[term.ml >> term_to_string] rewrite rules should not contain names"
    | Var x -> Printf.sprintf "%s%d" x.label (norm x.index)
    | Func(s,[]) -> s.name
    | Func(s,t::args) ->
        s.name ^ "(" ^
        string_of_term t norm ^
        List.fold_right (fun t ac -> "," ^ string_of_term t norm ^ ac) args ")"

  (* checks whether t1 is a syntactic subterm of t2. Assumes that rewrite
  rules do not contain names. *)
  let rec is_subterm (t1:protocol_term) (t2:protocol_term) : bool =
    match t1.term, t2.term with
    | AxName _, _
    | _, AxName _ -> Config.internal_error "[term.ml >> is_subterm] rewrite rules should not contain names"
    | Var x, Var y -> Variable.is_equal x y
    | Var _, Func(_,l) -> List.exists (is_subterm t1) l
    | Func _, Var _ -> false
    | Func(f1,l1), Func(f2,l2) ->
        (Symbol.is_equal f1 f2 && List.for_all2 (is_equal Protocol) l1 l2)
        || List.exists (is_subterm t1) l2

  (* checks whether a rewrite rule satisfies the subterm property *)
  let rule_is_subterm (lhs:protocol_term list) (rhs:protocol_term) : bool =
    (rhs.ground && is_equal Protocol rhs (normalise rhs))
    || List.exists (is_subterm rhs) lhs


  (* checks whether a pair of constructor-destructor rules (with same root)
  verifies the local-convergence property (critical pair---which, if any,
  needs be at the root---joinable). Left-hand sides are represented as the
  list of direct subterms of the root.
  @raise NonConvergent + witness of non convergence (that is a term + 2 normal
  forms) when the critical pair is joinable. *)
  type witness_non_conv = protocol_term list * protocol_term * protocol_term

  let critical_pair_joinable (lhs1:protocol_term list) (rhs1:protocol_term) (lhs2:protocol_term list) (rhs2:protocol_term) : witness_non_conv option =
    match Subst.unify_protocol_opt (List.combine lhs1 lhs2) with
    | None -> None
    | Some subst ->
        match Subst.apply subst (rhs1 :: rhs2 :: lhs1) (flip List.map) with
        | rhs1' :: rhs2' :: lhs ->
            if is_equal Protocol rhs1' rhs2'
            then None
            else Some(lhs,rhs1',rhs2')
        | _ -> Config.internal_error "[term.ml >> critical_pair_joinable] unexpected case"

  (* verifies that the reduction rules of a given destructor are subterm
  convergent *)
  let is_subterm_convergent_symbol (line:int) (s:symbol) : unit =
    match s.cat with
    | Tuple
    | Constructor -> Config.internal_error "[term.ml >> subterm_convergent_symbol] only destructor symbols should be considered"

    | Destructor rw_rules ->

        let check_pair (lhs1,rhs1) (lhs2,rhs2) =
          match critical_pair_joinable lhs1 rhs1 lhs2 rhs2 with
          | None -> ()
          | Some(tl,nf1,nf2) ->
            let norm = normalised_indexes tl in
            Printf.printf "Error! The rewrite system is not convergent, e.g. %s has normal forms %s and %s.\n"
              (string_of_generic_term (Func(s,tl)) norm)
              (string_of_term nf2 norm)
              (string_of_term nf1 norm);
            exit 0 in

        let check_subterm (lhs,rhs) =
          if not(rule_is_subterm lhs rhs)
          then
          (
            let norm = normalised_indexes lhs in
            Printf.printf "Error! Line %d : the rewrite rule %s -> %s is not subterm.\n"
              line
              (string_of_generic_term (Func(s,lhs)) norm)
              (string_of_term rhs norm);
            exit 0
          ) in

        let rec check_all_pairs l =
          match l with
          | [] -> ()
          | r :: rl ->
            List.iter (check_pair r) rl;
            check_all_pairs rl in

        List.iter check_subterm rw_rules;
        check_all_pairs rw_rules




  (****** Access function ******)

  let get_skeleton i = !storage_skeletons.(i).skeleton

  let get_compatible_rewrite_rules i = !storage_skeletons.(i).compat_rewrite_rules

  let get_all_skeleton_indices () = !index_skeletons

  let get_vars_with_list l =
    List.fold_left (fun acc f ->
        match f.cat with
          | Destructor rw_rules ->
              if Str.string_match Symbol.reg_proj f.name 0
              then acc
              else
                List.fold_left (fun acc_1 (arg_l,r) ->
                  let var_arg_l = List.fold_left (fun acc_2 t -> get_vars_with_list Protocol t (fun _ -> true) acc_2) acc_1 arg_l in
                  get_vars_with_list Protocol r (fun _ -> true) var_arg_l
                ) acc rw_rules
          | _ -> Config.internal_error "[term.ml >> get_vars_signature] all_destructors should only contain destructors."
    ) l !Symbol.all_destructors

  (****** Display function ******)

  let display_all_rewrite_rules out ?(per_line = 3) ?(tab = 0) rho =
    let dest_without_proj = !Symbol.all_destructors in

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
      | Latex ->
          if dest_without_proj = []
          then emptyset out
          else
            let destructor_list = List.fold_left (fun acc f -> match f.cat with
                | Destructor rw_rules ->
                    List.fold_left (fun acc_1 (arg_l,r) ->
                      let ground = List.for_all (fun t -> t.ground) arg_l in
                      ({term = Func(f,arg_l); ground = ground},r)::acc_1
                    ) acc rw_rules
                | _ -> Config.internal_error "[term.ml >> display_signature] all_destructors should only contain destructors.(2)"
              ) [] dest_without_proj in
            let s = List.length destructor_list in
            begin
              let str = ref "\\left\\{ \\begin{array}{l} " in
              let current_number = ref 1 in
              List.iter (fun (l,r) ->
                if !current_number >= s
                then str := Printf.sprintf "%s%s %s %s \\end{array}\\right\\}" !str (display out ~rho:rho Protocol l) (rightarrow out) (display out ~rho:rho Protocol r)
                else if (!current_number / per_line)*per_line = !current_number
                then str := Printf.sprintf "%s%s %s %s,\\\\" !str (display out ~rho:rho Protocol l) (rightarrow out) (display out ~rho:rho Protocol r)
                else str := Printf.sprintf "%s%s %s %s, " !str (display out ~rho:rho Protocol l) (rightarrow out) (display out ~rho:rho Protocol r);

                incr current_number
              ) destructor_list;
              !str
            end
      | HTML ->
          if dest_without_proj = []
          then emptyset out
          else
            let destructor_list = List.fold_left (fun acc f -> match f.cat with
                | Destructor rw_rules ->
                    List.fold_left (fun acc_1 (arg_l,r) ->
                      let ground = List.for_all (fun t -> t.ground) arg_l in
                      ({term = Func(f,arg_l); ground = ground},r)::acc_1
                    ) acc rw_rules
                | _ -> Config.internal_error "[term.ml >> display_signature] all_destructors should only contain destructors.(2)"
              ) [] dest_without_proj in
            let s = List.length destructor_list in
            begin
              let str = ref "<table class=\"rewrite\"><tr><td>" in
              let current_number = ref 1 in
              List.iter (fun (l,r) ->
                if !current_number >= s
                then str := Printf.sprintf "%s%s %s %s</td></tr></table>" !str (display out ~rho:rho Protocol l) (rightarrow out) (display out ~rho:rho Protocol r)
                else if (!current_number / per_line)*per_line = !current_number
                then str := Printf.sprintf "%s%s %s %s,,</td></tr><tr><td>" !str (display out ~rho:rho Protocol l) (rightarrow out) (display out ~rho:rho Protocol r)
                else str := Printf.sprintf "%s%s %s %s, " !str (display out ~rho:rho Protocol l) (rightarrow out) (display out ~rho:rho Protocol r);

                incr current_number
              ) destructor_list;
              !str
            end
      | _ ->
          let destructor_list = List.fold_left (fun acc f -> match f.cat with
              | Destructor rw_rules ->
                  List.fold_left (fun acc_1 (arg_l,r) ->
                    let ground = List.for_all (fun t -> t.ground) arg_l in
                    ({term = Func(f,arg_l); ground = ground},r)::acc_1
                  ) acc rw_rules
              | _ -> Config.internal_error "[term.ml >> display_signature] all_destructors should only contain destructors.(2)"
            ) [] dest_without_proj in
          let s = List.length destructor_list in
          let tab_str = create_tab tab in
          begin match s with
            | 0 -> "{}"
            | s when s <= per_line ->
                let str = ref "{ " in
                let current_number = ref 1 in
                List.iter (fun (l,r) ->
                  if !current_number < s
                  then str := Printf.sprintf "%s%s %s %s; " !str  (display out ~rho:rho Protocol l) (rightarrow out) (display out ~rho:rho Protocol r)
                  else str := Printf.sprintf "%s%s %s %s }" !str  (display out ~rho:rho Protocol l) (rightarrow out) (display out ~rho:rho Protocol r);

                  incr current_number
                ) destructor_list;
                !str
            | _ ->
                let tab_str_inside = create_tab (tab+1) in
                let str = ref (Printf.sprintf "\n%s{\n%s" tab_str tab_str_inside) in
                let current_number = ref 1 in
                List.iter (fun (l,r) ->
                  if !current_number >= s
                  then str := Printf.sprintf "%s%s %s %s\n%s}\n" !str (display out ~rho:rho Protocol l) (rightarrow out) (display out ~rho:rho Protocol r) tab_str
                  else if (!current_number / per_line)*per_line = !current_number
                  then str := Printf.sprintf "%s%s %s %s,\n%s" !str  (display out ~rho:rho Protocol l) (rightarrow out) (display out ~rho:rho Protocol r) tab_str_inside
                  else str := Printf.sprintf "%s%s %s %s, "!str  (display out ~rho:rho Protocol l) (rightarrow out) (display out ~rho:rho Protocol r);

                  incr current_number
                ) destructor_list;
                !str
          end

  let display_skeleton out ?(rho=None) skel =
    let f = root skel.recipe in
    let ground = List.for_all (fun t -> t.ground) skel.lhs in
    Printf.sprintf "(%s, %s, %s, %s, %s)"
      (Variable.display out ~rho:rho Recipe skel.pos_vars)
      (display out ~rho:rho Protocol skel.pos_term)
      (display out ~rho:rho Recipe skel.recipe)
      (display_list (BasicFact.display out ~rho:rho) (Printf.sprintf " %s " (wedge out)) skel.basic_deduction_facts)
      (display out ~rho:rho Protocol ({term = Func(f,skel.lhs); ground = ground}))
end

(**************************
***    Consequence      ***
***************************)

module type K =
  sig

    type t

    val find_protocol_opt : t -> protocol_term -> recipe option

    val find_recipe : t -> recipe -> protocol_term

    val find_recipe_opt : t -> recipe -> protocol_term option

    val find_recipe_with_var_type : t -> recipe -> protocol_term * int

    val find_recipe_with_var_type_opt : t -> recipe -> (protocol_term * int) option

    val find_unifier : t -> protocol_term -> int -> ((fst_ord, name) Subst.t -> (unit -> unit) -> unit) -> (unit -> unit) -> unit
  end

module type IK =
  sig

    type t

    val find_protocol_opt : t -> protocol_term -> recipe option

    val find_recipe : t -> recipe -> protocol_term
  end

module type DF =
  sig
    type t

    val find_protocol_opt : t -> protocol_term -> recipe option

    val find_recipe : t -> snd_ord_variable -> protocol_term

    val iter : t -> (snd_ord_variable -> protocol_term -> unit) -> unit
  end

module type EqFst =
  sig
    type ('a,'b) t

    val top : ('a, 'b) t

    val bot : ('a, 'b) t

    val wedge : ('a, 'b) t -> ('a, 'b) Diseq.t -> ('a, 'b) t

    val is_bot : ('a, 'b) t -> bool

    val is_top : ('a, 'b) t -> bool
  end

module type EqMixed =
  sig
    type t

    val top : t

    val bot : t

    val wedge : t -> Diseq.Mixed.t -> t

    val is_bot : t -> bool

    val is_top : t -> bool
  end

module Tools_Subterm (K:K) (IK:IK) (DF:DF) (Eq: EqMixed) (EqFst:EqFst) = struct

  (***** Consequence Recipe ******)

  let consequence_recipe (k:K.t) (df:DF.t) (recipe:recipe) =

    let rec mem_list : recipe list -> bool * protocol_term list = function
      | [] -> (true,[])
      | r::q_r ->
          let t = mem_term r in
          let (g_l,t_l) = mem_list q_r in
          (g_l&&t.ground,t::t_l)

    and mem_term : recipe -> protocol_term = fun recipe -> match recipe.term with
      | Func(f,args_r) when Symbol.is_constructor f ->
          if f.arity = 0
          then { term = Func(f,[]); ground = true }
          else
            let (g,t_l) = mem_list args_r in
            { term = Func(f,t_l); ground = g}
      | Func _
      | AxName _ -> K.find_recipe k recipe
      | Var v -> DF.find_recipe df v
    in

    mem_term recipe

  let consequence_recipe_with_IK k ik df recipe =

    let rec mem_list : recipe list -> bool * protocol_term list = function
      | [] -> (true,[])
      | r::q_r ->
          let t = mem_term r in
          let (g_l,t_l) = mem_list q_r in
          (g_l&&t.ground,t::t_l)

    and mem_term : recipe -> protocol_term = fun recipe -> match recipe.term with
      | Func(f,args_r) when Symbol.is_constructor f ->
          if f.arity = 0
          then { term = Func(f,[]); ground = true }
          else
            let (g,t_l) = mem_list args_r in
            { term = Func(f,t_l); ground = g}
      | Func(_,_)
      | AxName _ ->
          begin match K.find_recipe_opt k recipe with
            | Some t -> t
            | None -> IK.find_recipe ik recipe
          end
      | Var v -> DF.find_recipe df v
    in

    mem_term recipe

  let consequence_uniform_recipe k df eq_fst recipe =

    let rec mem_list : (fst_ord, name) EqFst.t -> recipe list ->  (fst_ord, name) EqFst.t * bool * int * protocol_term list = fun eq_fst -> function
      | [] -> (eq_fst,true,0,[])
      | r::q_r ->
          let (eq_fst',t,v_t) = mem_term eq_fst r in
          let (eq_fst'',g_l,v_l,t_l) = mem_list eq_fst' q_r in
          (eq_fst'',g_l && t.ground, max v_t v_l, t::t_l)

    and mem_term : (fst_ord, name) EqFst.t -> recipe -> (fst_ord, name) EqFst.t * protocol_term * int = fun eq_fst recipe -> match recipe.term with
      | Func(f,args_r) when Symbol.is_constructor f ->
          if f.arity = 0
          then eq_fst, { term = Func(f,[]); ground = true }, 0
          else
            let (eq_fst',g,v,t_l) = mem_list eq_fst args_r in
            let t = { term = Func(f,t_l); ground = g } in
            let eq_fst'' =
              let acc_eq = ref eq_fst' in
              K.find_unifier k t v (fun subst f_next ->
                if subst = []
                then acc_eq := EqFst.bot
                else
                  begin
                    acc_eq := EqFst.wedge !acc_eq (Diseq.Diseq (Subst.equations_of subst));
                    f_next ()
                  end
              ) (fun () -> ());
              !acc_eq
            in
            eq_fst'', t, v
      | Func _
      | AxName _ ->
          let t,v = K.find_recipe_with_var_type k recipe in
          eq_fst, t, v
      | Var v -> eq_fst, DF.find_recipe df v, v.var_type
    in

    let (phi,t,_) = mem_term eq_fst recipe in
    t,phi

  let consequence_uniform_recipe_with_IK k ik_var_type ik df eq_fst recipe =

    let rec mem_list : (fst_ord, name) EqFst.t -> recipe list ->  (fst_ord, name) EqFst.t * bool * int * protocol_term list = fun eq_fst -> function
      | [] -> (eq_fst,true,0,[])
      | r::q_r ->
          let (eq_fst',t,v_t) = mem_term eq_fst r in
          let (eq_fst'',g_l,v_l,t_l) = mem_list eq_fst' q_r in
          (eq_fst'',g_l && t.ground, max v_t v_l, t::t_l)

    and mem_term : (fst_ord, name) EqFst.t -> recipe -> (fst_ord, name) EqFst.t * protocol_term * int = fun eq_fst recipe -> match recipe.term with
      | Func(f,args_r) when Symbol.is_constructor f ->
          if f.arity = 0
          then eq_fst, { term = Func(f,[]); ground = true }, 0
          else
            let (eq_fst',g,v,t_l) = mem_list eq_fst args_r in
            let t = { term = Func(f,t_l); ground = g } in
            let eq_fst'' =
              let acc_eq = ref eq_fst' in
              K.find_unifier k t v (fun subst f_next ->
                if subst = []
                then acc_eq := EqFst.bot
                else
                  begin
                    acc_eq := EqFst.wedge !acc_eq (Diseq.Diseq (Subst.equations_of subst));
                    f_next ()
                  end
              ) (fun () -> ());
              !acc_eq
            in
            eq_fst'', t, v
      | Func _
      | AxName _ ->
          begin match K.find_recipe_with_var_type_opt k recipe with
            | None -> eq_fst, IK.find_recipe ik recipe, ik_var_type
            | Some (t,v) -> eq_fst, t, v
          end
      | Var v -> eq_fst, DF.find_recipe df v, v.var_type
    in

    let (phi,t,_) = mem_term eq_fst recipe in
    t,phi

  let consequence_protocol k ik df t =

    let rec mem_list = function
      | [] -> Config.internal_error "[term.ml >> Consequence_Subterm.consequence_protocol] The list should not be empty"
      | [t] ->
          begin match mem_term t with
            | None -> None
            | Some r -> Some (r.ground,[r])
          end
      | t::q_t ->
          begin match mem_term t with
            | None -> None
            | Some r ->
              begin match mem_list q_t with
                | None -> None
                | Some (g,l_r) -> Some(g&&r.ground,r::l_r)
              end
          end

    and mem_term pterm = match pterm.term with
      | Func(f,_) when f.arity = 0 && f.public -> Some ({term = Func(f,[]); ground = true})
      | Func(f,args_t) when f.public ->
          begin match mem_list args_t with
            | None ->
                begin match K.find_protocol_opt k pterm with
                  | None ->
                      begin match IK.find_protocol_opt ik pterm with
                        | None -> DF.find_protocol_opt df pterm
                        | r_opt -> r_opt
                      end
                  | r_opt -> r_opt
                end
            | Some (g,r_l) -> Some ({term = Func(f,r_l); ground = g})
          end
      | _ ->
          begin match K.find_protocol_opt k pterm with
            | None ->
                begin match IK.find_protocol_opt ik pterm with
                  | None -> DF.find_protocol_opt df pterm
                  | r_opt -> r_opt
                end
            | r_opt -> r_opt
          end
    in

    mem_term t

  type unsolved_status =
    | Solved
    | UnifyVariables of (snd_ord, axiom) Subst.t
    | UnsolvedFact of BasicFact.t

  exception FoundF of BasicFact.t
  exception Found

  let unsolved_DF df =
    let subst = ref [] in
    let linked_vars = ref [] in

    try
      DF.iter df (fun v t ->
        if not (is_variable t)
        then raise (FoundF { BasicFact.var = v; BasicFact.pterm = t})
        else
          begin
            let x = variable_of t in
            match x.link with
              | NoLink -> x.link <- XLink v; linked_vars := x :: !linked_vars
              | XLink v' -> subst := (v, { ground = false; term = Var v'}) :: !subst
              | _ -> Config.internal_error "[term.ml >> Tools_Subterm.unsolved_DF] Unexpected link."
          end
      );
      List.iter (fun v -> v.link <- NoLink) !linked_vars;
      if !subst = []
      then Solved
      else UnifyVariables !subst
    with FoundF fct ->
      List.iter (fun v -> v.link <- NoLink) !linked_vars;
      UnsolvedFact fct

  let is_solved_DF df =
    let linked_vars = ref [] in

    try
      DF.iter df (fun _ t ->
        if not (is_variable t)
        then raise Found
        else
          begin
            let x = variable_of t in
            match x.link with
              | NoLink -> x.link <- FLink; linked_vars := x :: !linked_vars
              | FLink -> raise Found
              | _ -> Config.internal_error "[term.ml >> Tools_Subterm.unsolved_DF] Unexpected link."
          end
      );
      List.iter (fun v -> v.link <- NoLink) !linked_vars;
      true
    with Found ->
      List.iter (fun v -> v.link <- NoLink) !linked_vars;
      false

  (* Generation of mixed disequation from rewrite rules *)

  let mixed_diseq_for_skeletons k ik df fst_vars snd_vars recipe =

    let rec mem_list attacker = function
      | [] -> (true,[],[],attacker)
      | r::q_r ->
          let term, recipe_op = mem_term r in
          begin match recipe_op with
            | None ->
                let (is_ground,term_l,recipe_l,attacker_l) = mem_list attacker q_r in
                if attacker_l
                then
                  let y_snd = Variable.fresh Recipe Universal max_int in
                  (term.ground && is_ground, term::term_l, { term = Var y_snd; ground = false} :: recipe_l, true)
                else
                  (term.ground && is_ground, term::term_l, [], false)
            | Some r_c ->
                let (is_ground,term_l,recipe_l,_) = mem_list true q_r in
                (term.ground && is_ground, term::term_l, r_c::recipe_l, true)
          end

    and mem_term recipe = match recipe.term with
      | Func(f,args_r) when Symbol.is_constructor f ->
          if f.arity = 0
          then
            if f.represents = AttackerPublicName
            then
              let y_fst = Variable.fresh Protocol Universal NoType
              and y_snd = Variable.fresh Recipe Universal max_int in
              { term = Var y_fst; ground = false }, Some { term = Var y_snd; ground = false }
            else
              { term = Func(f,[]); ground = true}, None
          else
            let is_ground, term_l, recipe_l, attacker = mem_list false args_r in
            if attacker
            then { term = Func(f,term_l); ground = is_ground }, Some { term = Func(f,recipe_l); ground = false }
            else { term = Func(f,term_l); ground = is_ground }, None
      | Func(_,_)
      | AxName _ ->
          begin match K.find_recipe_opt k recipe with
            | None -> IK.find_recipe ik recipe, None
            | Some term -> term, None
          end
      | Var v -> DF.find_recipe df v, None
    in

    let args = get_args recipe in
    let (_,term_l,recipe_l,attacker) = mem_list false args in
    if attacker
    then
      let eq_fst = List.fold_left2 (fun acc x t -> if is_variable t && (variable_of t).quantifier = Universal then acc else (of_variable x,t)::acc) [] fst_vars term_l
      and eq_snd = List.fold_left2 (fun acc x t -> if is_variable t && (variable_of t).quantifier = Universal then acc else (of_variable x,t)::acc) [] snd_vars recipe_l in
      Diseq.Mixed.MDiseq(eq_fst,eq_snd)
    else
      Diseq.Mixed.MDiseq(List.fold_left2 (fun acc x t -> (of_variable x,t)::acc) [] fst_vars term_l, [])

  (* Generation of stored constructor *)

  type stored_constructor =
    {
      snd_vars : snd_ord_variable list;
      fst_vars : fst_ord_variable list;
      mixed_diseq : Eq.t
    }

  let storage_functions: stored_constructor HashtblSymb.t = (HashtblSymb.create 10)

  let retrieve_stored_constructors () =
    HashtblSymb.fold (fun symb stored acc -> (symb,stored)::acc) storage_functions []

  let setup_stored_constructors l =
    HashtblSymb.reset storage_functions;
    List.iter (fun (symb,stored) -> HashtblSymb.add storage_functions symb stored) l

  let initialise_constructor () =
    let list_constructor = List.filter_unordered (fun f -> (not (Symbol.is_tuple f)) && f.public && (f.arity > 0)) !Symbol.all_constructors in

    let list_single_skeletons =
      let list_storage = Array.to_list !Rewrite_rules.storage_skeletons in
      List.filter (fun stored_skel ->
        let single_rw_rule = List.length stored_skel.Rewrite_rules.compat_rewrite_rules = 1 in
        let f = root stored_skel.Rewrite_rules.skeleton.Rewrite_rules.recipe in
        let f_c = root stored_skel.Rewrite_rules.skeleton.Rewrite_rules.pos_term in
        if f.public && (not (Symbol.is_tuple f_c)) && f_c.public && f_c.arity > 0
        then
          let list_same_dest = List.filter (fun stored_skel' -> (root stored_skel'.Rewrite_rules.skeleton.Rewrite_rules.recipe) == f) list_storage in
          single_rw_rule && List.length list_same_dest = 1
        else false
      ) list_storage
    in

    let rec explore_term f_next t = match t.term with
      | Var _ ->
          let x_snd = Variable.fresh Recipe Universal max_int in
          f_next (of_variable x_snd) [BasicFact.create x_snd t]
      | Func(f,args) ->
          let x_snd = Variable.fresh Recipe Universal max_int in
          f_next (of_variable x_snd) [BasicFact.create x_snd t];
          if f.public && f.arity > 0
          then
            explore_term_list (fun recipe_list bfct_list ->
              f_next (apply_function f recipe_list) bfct_list
            ) args
      | _ -> Config.internal_error "[term.ml >> Rewrtie_rules.initialise_constructor] Rewrite rules should not contain names."

    and explore_term_list f_next = function
      | [] -> f_next [] []
      | t::q ->
          explore_term_list (fun recipe_q bfct_list_q ->
            explore_term (fun recipe bfct_list ->
              f_next (recipe::recipe_q) (List.rev_append bfct_list bfct_list_q)
            ) t
          ) q
    in

    let check_conditions skel args bfct_r bfct_list =
      let test_1 =
        List.for_all (fun bfct ->
          match Rewrite_rules.consequence_protocol_term bfct_list bfct.BasicFact.pterm with
            | None -> false
            | Some _ -> true
        ) skel.Rewrite_rules.basic_deduction_facts
      in
      if test_1
      then
        List.for_all (fun t ->
          match Rewrite_rules.consequence_protocol_term (bfct_r::skel.Rewrite_rules.basic_deduction_facts) t with
            | None -> false
            | Some _ -> true
        ) args
      else false
    in

    let list_found_symb = ref [] in

    List.iter (fun stored_skel ->
      let f_c = root stored_skel.Rewrite_rules.skeleton.Rewrite_rules.pos_term in
      let args = get_args stored_skel.Rewrite_rules.skeleton.Rewrite_rules.pos_term in
      let bfct_r = BasicFact.create (Variable.fresh Recipe Universal max_int) stored_skel.Rewrite_rules.skeleton.Rewrite_rules.rhs in
      explore_term_list (fun recipe_list bfct_list ->
        if check_conditions stored_skel.Rewrite_rules.skeleton args bfct_r bfct_list
        then
          begin
            let pterm_uni = Variable.Renaming.rename_term Protocol Universal NoType stored_skel.Rewrite_rules.skeleton.Rewrite_rules.pos_term in
            Variable.Renaming.cleanup Protocol;
            list_found_symb := (f_c,get_args pterm_uni,recipe_list) :: !list_found_symb
          end
      ) args
    ) list_single_skeletons;

    List.iter (fun f ->
      let snd_vars = Variable.fresh_list Recipe Existential max_int f.arity in
      let fst_vars = Variable.fresh_list Protocol Existential NoType f.arity in

      let diseq_form =
        List.fold_left (fun acc (f_c,term_list,recipe_list) ->
          if Eq.is_bot acc || not (f == f_c)
          then acc
          else
            begin
              List.iter2 (fun x t -> Subst.unify_term_protocol (of_variable x) t) fst_vars term_list;
              List.iter2 (fun x t -> Subst.unify_term_recipe (of_variable x) t) snd_vars recipe_list;

              let fst_diseq =
                List.fold_left (fun acc v ->
                  if v.quantifier = Universal
                  then acc
                  else ({ term = Var v; ground = false}, Subst.follow_link_var v)::acc
                ) [] (Subst.retrieve Protocol)
              in
              let snd_diseq =
                List.fold_left (fun acc v ->
                  if v.quantifier = Universal
                  then acc
                  else ({ term = Var v; ground = false}, Subst.follow_link_var v)::acc
                ) [] (Subst.retrieve Recipe)
              in
              Subst.cleanup Protocol;
              Subst.cleanup Recipe;
              if fst_diseq = [] && snd_diseq = []
              then Eq.bot
              else Eq.wedge acc (Diseq.Mixed.MDiseq (fst_diseq,snd_diseq))
            end
        ) Eq.top !list_found_symb
      in

      Config.debug (fun () ->
        if Eq.is_bot diseq_form
        then Printf.printf "Function symbol removed from Equality : %s\n" (Symbol.display Latex f);

        if not (Eq.is_bot diseq_form) && not (Eq.is_top diseq_form)
        then Printf.printf "Function symbol with special diseq : %s\n" (Symbol.display Latex f);
      );
      HashtblSymb.add storage_functions f { snd_vars = snd_vars; fst_vars = fst_vars ; mixed_diseq = diseq_form }
    ) list_constructor

  let get_stored_constructor f = HashtblSymb.find storage_functions f
end
