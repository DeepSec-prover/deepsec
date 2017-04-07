(***********************************
***            Types             ***
************************************)

type ident = string * int

type term =
  | Id of ident
  | FuncApp of ident * term list
  | Tuple of term list
  | Proj of int * int * term * int

type env_elt =
  | VarFst of Term.fst_ord_variable
  | VarSnd of Term.snd_ord_variable
  | Name of Term.name
  | Axiom of Term.axiom
  | Func of Term.symbol

type parsing_mode =
  | Load
  | Verify

type 'a top_bot =
  | Top
  | Bot
  | Other of 'a

let environment = Hashtbl.create 50

(***********************************
***         Error_message        ***
************************************)

let display_env_elt_type = function
  | VarFst _ -> "a first-order variable"
  | VarSnd _ -> "a second-order variable"
  | Name _ -> "a name"
  | Axiom _ -> "an axiom"
  | Func _ -> "a function"

let error_message line str =
  let error_message = Printf.sprintf "Error! Line %d : %s\n" line str in
  failwith error_message

(***********************************
***            Parsing           ***
************************************)

let initialise_parsing () =
  Term.Symbol.empty_signature ();
  Hashtbl.reset environment

(******** First-order variables ********)

let reg_fst_vars = Str.regexp "_\\([wxyz]\\)_[0-9]+"

let rec parse_fst_vars = function
  | [] -> ()
  | (s,line)::q ->
      if Hashtbl.mem environment s
      then error_message line (Printf.sprintf "The identifiant %s should not be already declared." s);

      if Str.string_match reg_fst_vars s 0
      then
        let body = Str.matched_group 1 s in
        match body with
          | "w" -> Hashtbl.add environment s (VarFst (Term.Variable.fresh Term.Protocol Term.Free Term.Variable.fst_ord_type))
          | "x" | "y" -> Hashtbl.add environment s (VarFst (Term.Variable.fresh Term.Protocol Term.Existential Term.Variable.fst_ord_type))
          | "z" -> Hashtbl.add environment s (VarFst (Term.Variable.fresh Term.Protocol Term.Universal Term.Variable.fst_ord_type))
          | _ -> Config.internal_error "[parser_functions >> parse_fst_vars] Unexpected case."
      else error_message line (Printf.sprintf "The identifiant %s should be a first-order variable, i.e. it should match the regex _[wxyz]_[0-9]+" s);

      parse_fst_vars q

(******** Second-order variables ********)

let reg_snd_vars = Str.regexp "_\\([WXYZ]\\)_[0-9]+"

let rec parse_snd_vars = function
  | [] -> ()
  | ((s,line),k)::q ->
      if Hashtbl.mem environment s
      then error_message line (Printf.sprintf "The identifiant %s should not be already declared." s);

      if Str.string_match reg_snd_vars s 0
      then
        let body = Str.matched_group 1 s in
        match body with
          | "W" -> Hashtbl.add environment s (VarSnd (Term.Variable.fresh Term.Recipe Term.Free (Term.Variable.snd_ord_type k)))
          | "X" | "Y" -> Hashtbl.add environment s (VarSnd (Term.Variable.fresh Term.Recipe Term.Existential (Term.Variable.snd_ord_type k)))
          | "Z" -> Hashtbl.add environment s (VarSnd (Term.Variable.fresh Term.Recipe Term.Universal (Term.Variable.snd_ord_type k)))
          | _ -> Config.internal_error "[parser_functions >> parse_snd_vars] Unexpected case."
      else error_message line (Printf.sprintf "The identifiant %s should be a snd-order variable, i.e. it should match the regex _[WXYZ]_[0-9]+" s);

      parse_snd_vars q

(******** Names ********)

let reg_names = Str.regexp "_\\([abcklm]\\)_[0-9]+"

let rec parse_names = function
  | [] -> ()
  | (s,line)::q ->
      if Hashtbl.mem environment s
      then error_message line (Printf.sprintf "The identifiant %s should not be already declared." s);

      if Str.string_match reg_names s 0
      then
        let body = Str.matched_group 1 s in
        match body with
          | "a" | "b" | "c" -> Hashtbl.add environment s (Name (Term.Name.fresh Term.Public))
          | "k" | "l" | "m" -> Hashtbl.add environment s (Name (Term.Name.fresh Term.Bound))
          | _ -> Config.internal_error "[parser_functions >> parse_names] Unexpected case."
      else error_message line (Printf.sprintf "The identifiant %s should be a name, i.e. it should match the regex _[abcklm]_[0-9]+" s);

      parse_names q

(******** Axioms ********)

let reg_axioms = Str.regexp "_ax_\\(-?[0-9]+\\)"

let rec parse_axioms = function
  | [] -> ()
  | ((s,line),p_name)::q ->
      if Hashtbl.mem environment s
      then error_message line (Printf.sprintf "The identifiant %s should not be already declared." s);

      if Str.string_match reg_axioms s 0
      then
        let k = int_of_string (Str.matched_group 1 s) in
        match p_name with
          | None -> Hashtbl.add environment s (Axiom (Term.Axiom.create k))
          | Some (s',line') ->
              begin try
                begin match Hashtbl.find environment s' with
                  | Name n -> Hashtbl.add environment s (Axiom (Term.Axiom.of_public_name n k))
                  | env_elt -> error_message line' (Printf.sprintf "The identifiant %s is declared as %s but a name is expected." s' (display_env_elt_type env_elt))
                end
              with
                | Not_found -> error_message line' (Printf.sprintf "The identifiant %s should have already been declared." s')
              end
      else error_message line (Printf.sprintf "The identifiant %s should be an axiom, i.e. it should match the regex _ax_-?[0-9]+" s);

      parse_axioms q

(******** Signature ********)

let rec parse_constructor = function
  | [] -> ()
  | ((s,line),ar)::q ->
      if Hashtbl.mem environment s
      then error_message line (Printf.sprintf "The identifiant %s should not be already declared." s);

      Hashtbl.add environment s (Func (Term.Symbol.new_constructor ar s));
      parse_constructor q

let rec parse_tuple = function
  | [] -> ()
  | ar::q ->
      let _ = Term.Symbol.get_tuple ar in
      parse_tuple q

let parse_signature (constr,tuple) =
  parse_constructor constr;
  parse_tuple tuple

(******** Terms ********)

let rec parse_term : 'a 'b. ('a,'b) Term.atom -> term -> ('a,'b) Term.term = fun (type a) (type b) (at:(a,b) Term.atom) -> function
  | Id (s,line) ->
      begin try
        match Hashtbl.find environment s with
          | VarFst v ->
              begin match at with
                | Term.Protocol -> ((Term.of_variable v):(a,b) Term.term)
                | Term.Recipe -> error_message line (Printf.sprintf "The identifier %s is a first-order variable but a recipe is supposed to be parsed." s)
              end
          | VarSnd v ->
              begin match at with
                | Term.Protocol -> error_message line (Printf.sprintf "The identifier %s is a second-order variable but a protocol term is supposed to be parsed." s)
                | Term.Recipe -> ((Term.of_variable v):(a,b) Term.term)
              end
          | Name n ->
              begin match at with
                | Term.Protocol -> ((Term.of_name n):(a,b) Term.term)
                | Term.Recipe -> error_message line (Printf.sprintf "The identifier %s is a name but a recipe is supposed to be parsed." s)
              end
          | Axiom ax ->
              begin match at with
                | Term.Protocol -> error_message line (Printf.sprintf "The identifier %s is an axiom but a protocol term is supposed to be parsed." s)
                | Term.Recipe -> ((Term.of_axiom ax):(a,b) Term.term)
              end
          | Func(f) when Term.Symbol.get_arity f = 0 -> Term.apply_function f []
          | env_elt -> error_message line (Printf.sprintf "The identifiant %s is declared as %s but a name, a variable, an axiom or a unary function symbol is expected." s (display_env_elt_type env_elt))
      with
        Not_found -> error_message line (Printf.sprintf "The identifiant %s is not declared" s)
      end
  | FuncApp((s,line),args) ->
      begin try
        match Hashtbl.find environment s with
          | Func(f) ->
              if (Term.Symbol.get_arity f) <> List.length args
              then error_message line (Printf.sprintf "The function %s is given %d arguments but is expecting %d arguments" s (List.length args) (Term.Symbol.get_arity f));

              Term.apply_function f (List.map (parse_term at) args)
          | env_elt -> error_message line (Printf.sprintf "The identifiant %s is declared as %s but a name or a function is expected." s (display_env_elt_type env_elt))
      with
        Not_found -> error_message line (Printf.sprintf "The function %s is not declared" s)
      end
  | Tuple(args) ->
      let f = Term.Symbol.get_tuple (List.length args) in
      Term.apply_function f (List.map (parse_term at) args)
  | Proj(i,n,t,line) ->
       if i > n || i < 1 || n < 0
       then error_message line "A projection is necessary of the form \"proj_{i,n}\" where n > 0, i > 0 and i <= n.";
       let symb_tuple = Term.Symbol.get_tuple n in
       let symb_proj = Term.Symbol.nth_projection symb_tuple i in
       Term.apply_function symb_proj [parse_term at t]

(******** Rewriting system ********)

let rec parse_rewriting_system = function
  | [] -> ()
  | ((s,line),rw_rules)::q ->
      if Hashtbl.mem environment s
      then error_message line (Printf.sprintf "The identifiant %s should not be already declared." s);

      if rw_rules = []
      then error_message line (Printf.sprintf "The identifiant %s cannot be declared as a destructor without rewrite rules." s);

      let (arg_l,_) = List.hd rw_rules in
      let length = List.length arg_l in

      if List.exists (fun (arg_l,_) -> List.length arg_l <> length) rw_rules
      then error_message line (Printf.sprintf "The rewrite rules declared for the identifiant %s do not have the same arity." s);

      let rules =
        List.map (fun (arg_l,arg_r) ->
          let new_arg_l = List.map (parse_term Term.Protocol) arg_l
          and new_arg_r = parse_term Term.Protocol arg_r in

          if not (Term.is_constructor new_arg_r) || not (List.for_all Term.is_constructor new_arg_l)
          then error_message line (Printf.sprintf "The rewrite rule declared for the identifiant %s should not contain destructor function symbols (other than %s itself at root symbol of the left hand side term of the rule)" s s);

          if not (Term.no_axname new_arg_r) || not (List.for_all Term.no_axname new_arg_l)
          then error_message line (Printf.sprintf "The rewrite rule declared for the identifiant %s should not contain names." s);

          (new_arg_l,new_arg_r)
        ) rw_rules
      in

      Hashtbl.add environment s (Func (Term.Symbol.new_destructor length s rules));
      parse_rewriting_system q

(******** Syntactic_equation_list ********)

let rec parse_syntactic_equation_list at = function
  | [] -> []
  | (t1,t2)::q -> (parse_term at t1,parse_term at t2)::(parse_syntactic_equation_list at q)

(******** Equation_list ********)

let rec parse_equation_list = function
  | [] -> []
  | (t1,t2)::q -> (Term.Modulo.create_equation (parse_term Term.Protocol t1) (parse_term Term.Protocol t2))::(parse_equation_list q)

(******** Term list ********)

let parse_term_list at = List.map (parse_term at)

(******** Substitution ********)

let parse_substitution : 'a 'b. ('a,'b) Term.atom -> (ident * term) list -> ('a,'b) Term.Subst.t = fun (type a) (type b) (at:(a,b) Term.atom) subst ->
  List.fold_left (fun (acc_subst:(a,b) Term.Subst.t) ((s,line),term) ->
    try
      match Hashtbl.find environment s with
        | VarFst v ->
            begin match at with
              | Term.Protocol ->
                  let new_subst = Term.Subst.create at v (parse_term at term) in
                  ((Term.Subst.compose acc_subst new_subst):(a,b) Term.Subst.t)
              | Term.Recipe -> error_message line (Printf.sprintf "The identifier %s is a first-order variable but a recipe substitution is supposed to be parsed." s)
            end
        | VarSnd v ->
            begin match at with
              | Term.Protocol -> error_message line (Printf.sprintf "The identifier %s is a second-order variable but a protocol term substitution is supposed to be parsed." s)
              | Term.Recipe ->
                  let new_subst = Term.Subst.create at v (parse_term at term) in
                  ((Term.Subst.compose acc_subst new_subst):(a,b) Term.Subst.t)
            end
        | env_elt -> error_message line (Printf.sprintf "The identifiant %s is declared as %s but a variable is expected." s (display_env_elt_type env_elt))
    with
      | Not_found -> error_message line (Printf.sprintf "The identifiant %s is not declared" s)
  ) Term.Subst.identity subst

let parse_substitution_option at = function
  | None -> None
  | Some s -> Some (parse_substitution at s)

let parse_substitution_list_result = function
  | Term.Modulo.Top_raised -> Term.Modulo.Top_raised
  | Term.Modulo.Bot_raised -> Term.Modulo.Bot_raised
  | Term.Modulo.Ok s -> Term.Modulo.Ok (List.map (parse_substitution Term.Protocol) s)

(********* Symbol function ********)

let parse_symbol (s,line) =
  try
    match Hashtbl.find environment s with
      | Func(f) -> f
      | env_elt -> error_message line (Printf.sprintf "The identifiant %s is declared as %s but a function symbol is expected." s (display_env_elt_type env_elt))
  with
    | Not_found -> error_message line (Printf.sprintf "The identifiant %s is not declared" s)

(********** Basic deduction fact *********)

let parse_basic_deduction_fact ((s,line),k, term) =
  let xsnd =
    try
      match Hashtbl.find environment s with
        | VarSnd(x) when Term.Variable.type_of x = k -> x
        | VarSnd(x) -> error_message line (Printf.sprintf "The identifiant %s is declared as a second-order variable with type %d but a second-order variable with type %d is expected." s (Term.Variable.type_of x) k)
        | env_elt -> error_message line (Printf.sprintf "The identifiant %s is declared as %s but a second-order variable is expected." s (display_env_elt_type env_elt))
    with
      | Not_found -> error_message line (Printf.sprintf "The identifiant %s is not declared" s)
  in
  Term.BasicFact.create xsnd (parse_term Term.Protocol term)

(********** Deduction fact *********)

let parse_deduction_fact (recipe,term) =
  Term.Fact.create_deduction_fact (parse_term Term.Recipe recipe) (parse_term Term.Protocol term)

(********** Deduction formula *********)

let parse_deduction_formula (head,bfct_l,subst) =
  Term.Fact.create_for_testing (parse_deduction_fact head) (List.map parse_basic_deduction_fact bfct_l) (parse_substitution Term.Protocol subst)

let parse_deduction_formula_list = List.map (parse_deduction_formula)

(********** Skeleton *********)

let parse_skeleton ((s,line),recipe,term,bfct_l,(lhs,rhs)) =
  let xsnd =
    try
      match Hashtbl.find environment s with
        | VarSnd(x) -> x
        | env_elt -> error_message line (Printf.sprintf "The identifiant %s is declared as %s but a second-order variable is expected." s (display_env_elt_type env_elt))
    with
      | Not_found -> error_message line (Printf.sprintf "The identifiant %s is not declared" s)

  and recipe' = parse_term Term.Recipe recipe
  and term' = parse_term Term.Protocol term
  and bfct_l' = List.map parse_basic_deduction_fact bfct_l
  and lhs' = parse_term Term.Protocol lhs
  and rhs' = parse_term Term.Protocol rhs in

  {
    Term.Rewrite_rules.variable_at_position = xsnd;
    Term.Rewrite_rules.recipe = recipe';
    Term.Rewrite_rules.p_term = term';
    Term.Rewrite_rules.basic_deduction_facts = bfct_l';
    Term.Rewrite_rules.rewrite_rule = (Term.root lhs', Term.get_args lhs', rhs')
  }

let parse_skeleton_list l = List.map parse_skeleton l

(*********** Eq.t *********)

let parse_Eq at form = match form with
  | Top -> Data_structure.Eq.top
  | Bot -> Data_structure.Eq.bot
  | Other diseq_conj ->
      List.fold_right (fun diseq acc ->
        let new_diseq =
          Term.Diseq.create_for_testing (
            List.map (fun (t1,t2) ->
              parse_term at t1, parse_term at t2
            ) diseq
          )
        in
        Data_structure.Eq.wedge acc new_diseq
      ) diseq_conj Data_structure.Eq.top
