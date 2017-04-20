(***********************************
***            Types             ***
************************************)

(*** Parser types ****)

type parsing_mode =
  | Load of int
  | Verify

type result_parsing =
  | RLoad of Testing_functions.html_code
  | RVerify of string

type parser = parsing_mode -> result_parsing

(*** Data types ***)

type env_elt =
  | VarFst of Term.fst_ord_variable
  | VarSnd of Term.snd_ord_variable
  | Name of Term.name
  | Axiom of Term.axiom
  | Func of Term.symbol


type ident = string * int

type term =
  | Id of ident
  | FuncApp of ident * term list
  | Tuple of term list
  | Proj of int * int * term * int

type renaming = (ident * ident) list

type expansed_process =
  | ENil
  | EOutput of term * term * expansed_process
  | EInput of term * ident * expansed_process
  | ETest of term * term * expansed_process * expansed_process
  | ELet of term * term * expansed_process * expansed_process
  | ENew of ident * expansed_process
  | EPar of (expansed_process * int) list
  | EChoice of expansed_process list

type action =
  | ANil
  | AOut of term * term * int
  | AIn of term * ident * int
  | ATest of term * term * int * int
  | ALet of term * term * int * int
  | ANew of ident * int
  | APar of (int * int) list
  | AChoice of (int * int) list

type content = int * action

type symbolic_derivation = (int * int) * renaming * renaming

type process = content list * symbolic_derivation list

type action_trace =
  | TrComm of symbolic_derivation * symbolic_derivation * process
  | TrNew of symbolic_derivation * process
  | TrChoice of symbolic_derivation * process
  | TrTest of symbolic_derivation * process
  | TrLet of symbolic_derivation * process
  | TrInput of ident * term * ident * term * symbolic_derivation * process
  | TrOutput of ident * term * ident * term * symbolic_derivation * process
  | TrEavesdrop of ident * term * ident * term * symbolic_derivation * symbolic_derivation * process

type trace = action_trace list

type 'a top_bot =
  | Top
  | Bot
  | Other of 'a

type equation = term * term

type diseq = (term * term) list

type substitution = (ident * term) list

type skeleton = ident * term * term * (ident * int * term) list * (term * term)

type basic_deduction_fact = ident * int * term

type ded_eq_fact = term * term

type formula = ded_eq_fact * basic_deduction_fact list * substitution

(* Type of UF *)

type equality_type =
  | Constructor_SDF of int * ident
  | Equality_SDF of int * int
  | Consequence_UF of int

type uf = (int * formula list) list * (int * formula * equality_type) list

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

let parse_fst_var (s,line) =
  try
    match Hashtbl.find environment s with
      | VarFst v -> v
      | env_elt -> error_message line (Printf.sprintf "The identifiant %s is declared as %s but a first-order variable is expected." s (display_env_elt_type env_elt))
  with
  | _ -> error_message line (Printf.sprintf "The identifiant %s is not declared" s)

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

let parse_snd_var (s,line) =
  try
    match Hashtbl.find environment s with
      | VarSnd v -> v
      | env_elt -> error_message line (Printf.sprintf "The identifiant %s is declared as %s but a second-order variable is expected." s (display_env_elt_type env_elt))
  with
  | _ -> error_message line (Printf.sprintf "The identifiant %s is not declared" s)

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

let parse_name (s,line) =
  try
    match Hashtbl.find environment s with
      | Name v -> v
      | env_elt -> error_message line (Printf.sprintf "The identifiant %s is declared as %s but a name is expected." s (display_env_elt_type env_elt))
  with
  | _ -> error_message line (Printf.sprintf "The identifiant %s is not declared" s)

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

let reg_pos_axioms = Str.regexp "_ax_\\([0-9]+\\)"

let lookup_axiom (s,line) =
  if Str.string_match reg_pos_axioms s 0
  then
    let k = int_of_string (Str.matched_group 1 s) in
    if k = 0
    then error_message line "All axioms associated to a public name should have been already declared."
    else
      begin
        let ax = Term.Axiom.create k in
        Hashtbl.add environment s (Axiom ax);
        ax
      end
  else error_message line (Printf.sprintf "The identifiant %s is not declared." s)

let parse_axiom (s,line) =
  try
    match Hashtbl.find environment s with
      | Axiom ax -> ax
      | env_elt -> error_message line (Printf.sprintf "The identifiant %s is declared as %s but an axiom is expected." s (display_env_elt_type env_elt))
  with
  | _ -> error_message line (Printf.sprintf "The identifiant %s is not declared" s)

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
      let f = Term.Symbol.get_tuple ar in
      let get_proj = Term.Symbol.get_projections f in
      List.iter (fun proj -> Hashtbl.add environment (Term.Symbol.display Display.Testing proj) (Func proj)) get_proj;
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
        Not_found ->
          begin
            match at with
              | Term.Protocol -> error_message line (Printf.sprintf "The identifiant %s is not declared" s)
              | Term.Recipe -> ((Term.of_axiom (lookup_axiom (s,line))):(a,b) Term.term)
            end
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

(******** Diseq *********)

let parse_diseq at diseq =
  Term.Diseq.create_for_testing (List.map (fun (t1,t2) -> (parse_term at t1, parse_term at t2)) diseq)

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

(********** Fact *********)

let parse_deduction_fact (recipe,term) =
  Term.Fact.create_deduction_fact (parse_term Term.Recipe recipe) (parse_term Term.Protocol term)

let parse_equality_fact (recipe1,recipe2) =
  Term.Fact.create_equality_fact (parse_term Term.Recipe recipe1) (parse_term Term.Recipe recipe2)

(********** Deduction formula *********)

let parse_deduction_formula (head,bfct_l,subst) =
  Term.Fact.create_for_testing (parse_deduction_fact head) (List.map parse_basic_deduction_fact bfct_l) (parse_substitution Term.Protocol subst)

let parse_deduction_formula_list = List.map (parse_deduction_formula)

let parse_formula (type a) (fct: a Term.Fact.t) (head,bfct_l,subst) = match fct with
  | Term.Fact.Deduction -> ((parse_deduction_formula (head,bfct_l,subst)): a Term.Fact.formula)
  | Term.Fact.Equality -> ((Term.Fact.create_for_testing (parse_equality_fact head) (List.map parse_basic_deduction_fact bfct_l) (parse_substitution Term.Protocol subst)): a Term.Fact.formula)

let parse_formula_option fct = function
  | None -> None
  | Some form -> Some (parse_formula fct form)

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

(*********** SDF *********)

let parse_SDF  =
  List.fold_left (fun acc ded ->
    Data_structure.SDF.add acc (parse_deduction_fact ded)
  ) Data_structure.SDF.empty

(*********** DF *********)

let parse_DF  =
  List.fold_left (fun acc bfct ->
    Data_structure.DF.add acc (parse_basic_deduction_fact bfct)
  ) Data_structure.DF.empty

(*********** UF *********)

let parse_equality_type = function
  | Constructor_SDF(n,ident) -> Data_structure.UF.Constructor_SDF(n,parse_symbol ident)
  | Equality_SDF(id1,id2) ->  Data_structure.UF.Equality_SDF(id1,id2)
  | Consequence_UF(id) -> Data_structure.UF.Consequence_UF(id)

let parse_UF (ded_list,eq_list) =
  let uf_0 = Data_structure.UF.empty in

  let uf_1 =
    List.fold_left (fun uf (id,sub_ded_list) ->
      let sub_ded_list' = List.map parse_deduction_formula sub_ded_list in
      Data_structure.UF.add_deduction uf sub_ded_list' id
    ) uf_0 ded_list
  in

  List.fold_left (fun uf (id,eq_form,eq_type) ->
    let eq_form' = parse_formula Term.Fact.Equality eq_form in
    let eq_type' = parse_equality_type eq_type in
    Data_structure.UF.add_equality uf eq_form' id eq_type'
  ) uf_1 eq_list

(*********** Uniformity_Set *********)

let parse_Uniformity_Set =
  List.fold_left (fun acc (recipe,term) ->
    Data_structure.Uniformity_Set.add acc (parse_term Term.Recipe recipe) (parse_term Term.Protocol term)
  ) Data_structure.Uniformity_Set.empty

(*********** Consequence *********)

let parse_consequence  = function
  | None -> None
  | Some(recipe,term) -> Some(parse_term Term.Recipe recipe, parse_term Term.Protocol term)

(*********** Consequence *********)

let parse_recipe_option  = function
  | None -> None
  | Some(recipe) -> Some(parse_term Term.Recipe recipe)

(*********** Expansed process **********)

let rec parse_expansed_process = function
  | ENil -> Process.Nil
  | EOutput(ch,t,proc) -> Process.Output(parse_term Term.Protocol ch, parse_term Term.Protocol t, parse_expansed_process proc)
  | EInput(ch,x,proc) -> Process.Input(parse_term Term.Protocol ch, parse_fst_var x, parse_expansed_process proc)
  | ETest(t1,t2,proc_then,proc_else) -> Process.IfThenElse(parse_term Term.Protocol t1, parse_term Term.Protocol t2, parse_expansed_process proc_then, parse_expansed_process proc_else)
  | ELet(t1,t2,proc_then,proc_else) -> Process.Let(parse_term Term.Protocol t1, parse_term Term.Protocol t2, parse_expansed_process proc_then, parse_expansed_process proc_else)
  | ENew(k,proc) -> Process.New(parse_name k, parse_expansed_process proc)
  | EPar(proc_l) -> Process.Par(List.map (fun (proc,m) -> (parse_expansed_process proc, m)) proc_l)
  | EChoice(proc_l) -> Process.Choice(List.map parse_expansed_process proc_l)

(*********** ¨Process **********)

let parse_content (id,action) = match action with
  | ANil -> Process.Testing.add_Nil id
  | AOut(ch,t,id_p) -> Process.Testing.add_Out id (parse_term Term.Protocol ch) (parse_term Term.Protocol t) id_p
  | AIn(ch,x,id_p) -> Process.Testing.add_In id (parse_term Term.Protocol ch) (parse_fst_var x) id_p
  | ATest(t1,t2,id_then,id_else) -> Process.Testing.add_Test id (parse_term Term.Protocol t1) (parse_term Term.Protocol t2) id_then id_else
  | ALet(t1,t2,id_then,id_else) -> Process.Testing.add_Let id (parse_term Term.Protocol t1) (parse_term Term.Protocol t2) id_then id_else
  | ANew(k,id_p) -> Process.Testing.add_New id (parse_name k) id_p
  | APar(proc_l) -> Process.Testing.add_Par id proc_l
  | AChoice(proc_l) -> Process.Testing.add_Choice id proc_l

let parse_vars_renaming (type a) (type b) (at:(a,b) Term.atom) v_list = match at with
  | Term.Protocol ->
      ((List.fold_right (fun (v1,v2) acc -> Term.Variable.Renaming.compose acc (parse_fst_var v1) (parse_fst_var v2)) v_list Term.Variable.Renaming.identity):(a,b) Term.Variable.Renaming.t)
  | Term.Recipe ->
      ((List.fold_right (fun (v1,v2) acc -> Term.Variable.Renaming.compose acc (parse_snd_var v1) (parse_snd_var v2)) v_list Term.Variable.Renaming.identity):(a,b) Term.Variable.Renaming.t)

let parse_names_renaming n_list =
  List.fold_right (fun (n1,n2) acc -> Term.Name.Renaming.compose acc (parse_name n1) (parse_name n2)) n_list Term.Name.Renaming.identity

let parse_symbolic_derivation (content_mult, vars_rho, names_rho) = (content_mult, parse_vars_renaming Term.Protocol vars_rho, parse_names_renaming names_rho)

let parse_process (content_list,symb_list) =
  List.iter parse_content content_list;
  Process.Testing.create_process (List.map parse_symbolic_derivation symb_list)

(*********** Transition ************)

let parse_action_process (cont,var_rho,n_rho) =
  Process.Testing.create_action_process (cont,parse_vars_renaming Term.Protocol var_rho, parse_names_renaming n_rho)

let parse_trace trace =
  List.fold_right (fun action acc_trace ->
    match action with
      | TrComm(symb_in,symb_out,proc) ->
          Process.Trace.add_comm (parse_action_process symb_in) (parse_action_process symb_out) (parse_process proc) acc_trace
      | TrNew(symb,proc) ->
          Process.Trace.add_new (parse_action_process symb) (parse_process proc) acc_trace
      | TrChoice(symb,proc) ->
          Process.Trace.add_choice (parse_action_process symb) (parse_process proc) acc_trace
      | TrTest(symb,proc) ->
          Process.Trace.add_test (parse_action_process symb) (parse_process proc) acc_trace
      | TrLet(symb,proc) ->
          Process.Trace.add_let (parse_action_process symb) (parse_process proc) acc_trace
      | TrInput(ch_X,ch,t_X,t,symb,proc) ->
          Process.Trace.add_input (parse_snd_var ch_X) (parse_term Term.Protocol ch) (parse_snd_var t_X) (parse_term Term.Protocol t) (parse_action_process symb) (parse_process proc) acc_trace
      | TrOutput(ch_X,ch,ax,t,symb,proc) ->
          Process.Trace.add_output (parse_snd_var ch_X) (parse_term Term.Protocol ch) (parse_axiom ax) (parse_term Term.Protocol t) (parse_action_process symb) (parse_process proc) acc_trace
      | TrEavesdrop(ch_X,ch,ax,t,symb_in,symb_out,proc) ->
          Process.Trace.add_eavesdrop (parse_snd_var ch_X) (parse_term Term.Protocol ch) (parse_axiom ax) (parse_term Term.Protocol t) (parse_action_process symb_in) (parse_action_process symb_out) (parse_process proc) acc_trace
  ) trace Process.Trace.empty

let parse_output_transition out_l =
  List.map (fun (proc, subst, diseq_l, channel, term, term_list, action_process, trace) ->
    let proc' = parse_process proc in
    let subst' = parse_substitution Term.Protocol subst in
    let diseq_l' =
      List.map (fun diseq ->
        Term.Diseq.create_for_testing (
          List.map (fun (t1,t2) ->
            parse_term Term.Protocol t1, parse_term Term.Protocol t2
          ) diseq
        )
      ) diseq_l in
    let channel' = parse_term Term.Protocol channel in
    let term' = parse_term Term.Protocol term in
    let term_list' = parse_term_list Term.Protocol term_list in
    let action_process' = parse_action_process action_process in
    let trace' = parse_trace trace in
    (proc', {
      Process.out_equations = subst';
      Process.out_disequations = diseq_l';
      Process.out_channel = channel';
      Process.out_term = term';
      Process.out_private_channels = term_list';
      Process.out_action = Some (action_process');
      Process.out_tau_actions = trace'
    })
  ) out_l

let parse_input_transition out_l =
  List.map (fun (proc, subst, diseq_l, channel, var, term_list,action_process, trace) ->
    let proc' = parse_process proc in
    let subst' = parse_substitution Term.Protocol subst in
    let diseq_l' =
      List.map (fun diseq ->
        Term.Diseq.create_for_testing (
          List.map (fun (t1,t2) ->
            parse_term Term.Protocol t1, parse_term Term.Protocol t2
          ) diseq
        )
      ) diseq_l in
    let channel' = parse_term Term.Protocol channel in
    let var' = parse_fst_var var in
    let term_list' = parse_term_list Term.Protocol term_list in
    let action_process' = parse_action_process action_process in
    let trace' = parse_trace trace in
    (proc', {
      Process.in_equations = subst';
      Process.in_disequations = diseq_l';
      Process.in_channel = channel';
      Process.in_variable = var';
      Process.in_private_channels = term_list';
      Process.in_action = Some (action_process');
      Process.in_tau_actions = trace'
    })
  ) out_l

(*********** Constraint_system ***********)

type mgs = ident list * substitution

type constraint_system =
  term list * basic_deduction_fact list * equation list list top_bot * equation list list top_bot * ded_eq_fact list *
  uf *
  substitution * substitution *
  (term * term) list *
  int list * int list * int list *
  (int * skeleton) list * (int * skeleton) list

type simple_constraint_system = basic_deduction_fact list * equation list list top_bot * equation list list top_bot * ded_eq_fact list * (term * term) list

let parse_constraint_system (frame,df,eq1,eq2,sdf,uf,sub1,sub2,uni,il1,il2,il3,is1,is2) =
  Constraint_system.create
    (List.length (parse_term_list Term.Protocol frame))
    (parse_DF df)
    (parse_Eq Term.Protocol eq1)
    (parse_Eq Term.Recipe eq2)
    (parse_SDF sdf)
    (parse_UF uf)
    (parse_substitution Term.Protocol sub1)
    (parse_substitution Term.Recipe sub2)
    (parse_Uniformity_Set uni)
    il1
    il2
    il3
    (List.map (fun (i,skel) -> (i,parse_skeleton skel)) is1)
    (List.map (fun (i,skel) -> (i,parse_skeleton skel)) is2)

let parse_constraint_system_set csys_l =
  List.fold_right (fun csys acc -> Constraint_system.Set.add (parse_constraint_system csys) acc) csys_l Constraint_system.Set.empty

let parse_constraint_system_option = function
  | None -> None
  | Some csys -> Some (parse_constraint_system csys)

let parse_simple_constraint_system (df,eq1,eq2,sdf,uni) =
  let df' = parse_DF df in
  let eq1' = parse_Eq Term.Protocol eq1 in
  let eq2' = parse_Eq Term.Recipe eq2 in
  let sdf' = parse_SDF sdf in
  let uni' = parse_Uniformity_Set uni in
  Constraint_system.create_simple df' eq1' eq2' sdf' uni'

let parse_mgs (v_list,subst) =
  let v_list' = List.map parse_snd_var v_list in
  let subst' = parse_substitution Term.Recipe subst in
  Constraint_system.create_mgs subst' v_list'

let parse_mgs_result (mgs,subst,simple) =
  let mgs' = parse_mgs mgs in
  let subst' = parse_substitution Term.Protocol subst in
  let simple' = parse_simple_constraint_system simple in
  (mgs',subst',simple')

let parse_mgs_result_option = function
  | None -> None
  | Some res -> Some (parse_mgs_result res)

let parse_mgs_result_list mgs_list =
  List.map parse_mgs_result mgs_list
