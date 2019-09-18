
(* Types *)

type setting =
  | Classic
  | Private
  | Eavesdrop

type ident = string * int

type term =
  | Id of ident
  | FuncApp of ident * term list
  | Tuple of term list

type functions =
  | Constructor of ident * int * bool
  | Destructor of (term * term) list * bool * int

type pattern =
  | PVar of ident
  | PTuple of pattern list
  | PTest of term

type intermediate_process =
  | INil
  | IOutput of Types.term * Types.term * intermediate_process
  | IInput of Types.term * Types.pattern * intermediate_process
  | IIfThenElse of Types.term * Types.term * intermediate_process * intermediate_process
  | ILet of Types.pattern * Types.term * intermediate_process * intermediate_process
  | INew of Types.name * intermediate_process
  | IPar of (intermediate_process * int) list
  | IChoice of intermediate_process * intermediate_process

type plain_process =
  | Nil
  | Call of ident * term list
  | Choice of plain_process * plain_process
  | Par of plain_process * plain_process
  | Bang of int * plain_process * int
  | New of ident * plain_process
  | In of term * ident * plain_process
  | Out of term * term * plain_process
  | Let of pattern * term * plain_process * plain_process
  | IfThenElse of term * term * plain_process * plain_process
  | Seq of plain_process * plain_process

type extended_process =
  | EPlain of plain_process

type query =
  | Trace_Eq of extended_process * extended_process
  | Obs_Eq of extended_process * extended_process
  | Sess_Eq of extended_process * extended_process
  | Sess_Incl of extended_process * extended_process

type declaration =
  | Setting of setting * int
  | FuncDecl of functions list
  | FreeName of (ident list * bool)
  | Query of query * int
  | ExtendedProcess of ident * ident list * extended_process

(**** Environement ****)

type env_elt =
  | Var of Types.variable
  | Name of Types.name
  | PublicName of Types.symbol
  | Func of Types.symbol
  | Proc of int * (Types.term list -> intermediate_process)
  | ArgVar of Types.term

module StringComp =
struct
  type t = string
  let compare = compare
end

module Env = Map.Make(StringComp)

let environment = ref (Env.empty:env_elt Env.t)

let display_env_elt_type = function
  | ArgVar _ -> "an argument of a process"
  | Var _ -> "a variable"
  | Name _ -> "a name"
  | PublicName _ -> "a public name"
  | Func s ->
      if Term.Symbol.is_destructor s
      then "a destructor function"
      else "a constructor function"
  | Proc _ -> "a process"

(**** Error message ****)

let error_message line str =
  Printf.printf "Error! Line %d : %s\n" line str;
  exit 0

let warning_message line str =
  Printf.printf "Warning! Line %d : %s\n" line str

(******** Parse free names *******)

let parse_free_name env pub (s,line) =
  if Env.mem s env
  then error_message line (Printf.sprintf "The identifier %s is already defined." s);

  let n = Term.Symbol.new_constructor 0 pub true s in
  Env.add s (PublicName n) env

(******** Parse terms ********)

let rec parse_term env = function
  | Id (s,line) ->
      begin try
        match Env.find s env with
          | Var(v) -> Types.Var(v)
          | Name(n) -> Types.Name(n)
          | PublicName(n) -> Types.Func(n,[])
          | Func(f) when f.Types.arity = 0 -> Types.Func(f,[])
          | ArgVar(t) -> t
          | env_elt -> error_message line (Printf.sprintf "The identifiant %s is declared as %s (expected a name, a variable or a constant)." s (display_env_elt_type env_elt))
      with
        | Not_found -> error_message line (Printf.sprintf "The identifiant %s is not declared" s)
      end
  | FuncApp((s,line),args) ->
      begin try
        match Env.find s env with
          | Func(f) ->
              if f.Types.arity <> List.length args
              then error_message line (Printf.sprintf "The function %s is given %d arguments but is expecting %d arguments" s (List.length args) (Term.Symbol.get_arity f));

              Types.Func(f,List.map (parse_term env) args)
          | env_elt -> error_message line (Printf.sprintf "The identifiant %s is declared as %s but a name or a function is expected." s (display_env_elt_type env_elt))
      with
        Not_found -> error_message line (Printf.sprintf "The function %s is not declared" s)
      end
  | Tuple(args) ->
      Config.debug (fun () ->
        if List.length args <= 1
        then Config.internal_error "[parser_functions.ml >> parse_term] The number of arguments of a tuple should be at least 2."
      );
      let f = Term.Symbol.get_tuple (List.length args) in
      Types.Func(f,(List.map (parse_term env) args))

(******** Parse pattern ********)

let rec parse_pattern env prev_env = function
  | PVar (s,line) ->
      if Env.mem s env
      then warning_message line (Printf.sprintf "The identifier %s is already defined." s);

      let v = Term.Variable.fresh_with_label Types.Free s in

      Types.PatVar(v), Env.add s (Var v) env
  | PTuple(args) ->
      let args',env' = parse_pattern_list env prev_env args in
      let f = Term.Symbol.get_tuple (List.length args) in

      Types.PatTuple(f,args'), env'
  | PTest term ->
      let term' = parse_term prev_env term in
      Types.PatEquality(term'), env

and parse_pattern_list env prev_env = function
  | [] -> [], env
  | pat::q ->
      let pat',env' = parse_pattern env prev_env pat in
      let pat_l,env'' = parse_pattern_list env' prev_env q in
      pat'::pat_l, env''

(******** Process **********)

let fresh_position =
  let acc = ref 0 in
  let f () =
    let r = !acc in
    incr acc;
    r
  in
  f

let rec parse_plain_process env = function
  | Call((s,line),term_list) ->
      begin try
        match Env.find s env with
          | Proc(n,generate_process) ->
              if n <> List.length term_list
              then error_message line (Printf.sprintf "The process %s is given %d arguments but is expecting %d arguments" s (List.length term_list) n);

              let term_list' = List.map (parse_term env) term_list in

              generate_process term_list'
          | env_elt -> error_message line (Printf.sprintf "The identifiant %s is declared as %s but a process is expected." s (display_env_elt_type env_elt))
      with
        Not_found -> error_message line (Printf.sprintf "The identifiant %s is not declared" s)
      end
  | Nil -> INil
  | Choice(p1,p2) -> IChoice(parse_plain_process env p1,parse_plain_process env p2)
  | Seq(_,_)-> error_message 0 "Sequence is not yet implemented."
  | Par(p1,p2) ->
      begin match parse_plain_process env p1, parse_plain_process env p2 with
        | IPar l_1, IPar l_2 -> IPar (l_1@l_2)
        | IPar l_1, proc2 -> IPar ((proc2,1)::l_1)
        | proc1, IPar l_2 -> IPar ((proc1,1)::l_2)
        | proc1, proc2 -> IPar [(proc1,1);(proc2,1)]
      end
  | Bang(n,proc,line) ->
      if n < 1
      then error_message line "The integer should be at least 1.";

      begin match parse_plain_process env proc with
        | IPar l -> IPar (List.map (fun (p,i) -> (p,i*n)) l)
        | proc -> IPar [(proc,n)]
      end
  | New((s,line),proc) ->
      if Env.mem s env
      then warning_message line (Printf.sprintf "The identifier %s is already defined." s);

      let n = Term.Name.fresh_with_label s in
      let env' = Env.add s (Name n) env in

      INew(n,parse_plain_process env' proc)
  | In(ch,(s,line),proc) ->
      if Env.mem s env
      then warning_message line (Printf.sprintf "The identifier %s is already defined." s);

      let ch' = parse_term env ch in
      let x = Term.Variable.fresh_with_label Types.Free s in
      let env' = Env.add s (Var x) env in

      IInput(ch',Types.PatVar(x), parse_plain_process env' proc)
  | Out(ch,t,proc) ->
      let ch' = parse_term env ch
      and t' = parse_term env t
      and proc' = parse_plain_process env proc in

      IOutput(ch',t',proc')
  | Let(pat,t,proc_then,proc_else) ->
      let t' = parse_term env t in
      let pat',env' = parse_pattern env env pat in
      let proc_then' = parse_plain_process env' proc_then in
      let proc_else' = parse_plain_process env proc_else in

      ILet(pat',t',proc_then',proc_else')
  | IfThenElse(t1,t2,proc1,proc2) ->
      let t1' = parse_term env t1
      and t2' = parse_term env t2
      and proc1' = parse_plain_process env proc1
      and proc2' = parse_plain_process env proc2 in

      IIfThenElse(t1',t2',proc1',proc2')

let rec apply_renaming = function
  | Types.Var v ->
      begin match v.Types.link with
        | Types.VLink v' -> Types.Var v'
        | _ -> Config.internal_error "[parser_functions.ml >> apply_renaming] Unexpected link"
      end
  | Types.Name n ->
      begin match n.Types.link_n with
        | Types.NLink n' -> Types.Name n'
        | _ -> Config.internal_error "[parser_functions.ml >> apply_renaming] Unexpected link (2)"
      end
  | Types.Func(f,args) -> Types.Func(f,List.map apply_renaming args)

let rec apply_renaming_pat = function
  | Types.PatVar v ->
      let v' = Term.Variable.fresh_from v in
      Term.Variable.link v v';
      Types.PatVar v'
  | Types.PatEquality t -> Types.PatEquality (apply_renaming t)
  | Types.PatTuple(f,args) -> Types.PatTuple(f,List.map apply_renaming_pat args)

let rec intermediate_process_of_process = function
  | INil -> Types.Nil
  | IOutput(t1,t2,p) -> Types.Output(apply_renaming t1, apply_renaming t2, intermediate_process_of_process p, fresh_position ())
  | IInput(ch,pat,p) ->
      let ch' = apply_renaming ch in
      Term.Variable.auto_cleanup_with_reset_notail (fun () ->
        let pat' = apply_renaming_pat pat in
        Types.Input(ch',pat',intermediate_process_of_process p,fresh_position ())
      )
  | IIfThenElse(t1,t2,p1,p2) ->
      Types.IfThenElse(apply_renaming t1,apply_renaming t2, intermediate_process_of_process p1, intermediate_process_of_process p2,fresh_position ())
  | ILet(pat,t,p1,p2) ->
      let t' = apply_renaming t in
      let p2' = intermediate_process_of_process p2 in
      Term.Variable.auto_cleanup_with_reset_notail (fun () ->
        let pat' = apply_renaming_pat pat in
        let p1' = intermediate_process_of_process p1 in
        Types.Let(pat',t',p1',p2',fresh_position ())
      )
  | INew(n,p) ->
      Term.Name.auto_cleanup_with_reset_notail (fun () ->
        let n' = Term.Name.fresh_from n in
        Term.Name.link n n';
        Types.New(n',intermediate_process_of_process p,fresh_position ())
      )
  | IPar p_list ->
      let rec transform_bang p acc = function
        | 0 -> Types.Bang(acc,fresh_position ())
        | n -> transform_bang p ((intermediate_process_of_process p)::acc) (n-1)
      in
      let rec explore = function
        | [] -> []
        | (p,1)::q -> (intermediate_process_of_process p)::(explore q)
        | (p,n)::q -> (transform_bang p [] n)::(explore q)
      in
      begin match explore p_list with
        | [] -> Config.internal_error "[parser_functions.ml >> intermediate_process_of_process] There should be parallel processes"
        | [p] -> p
        | l -> Types.Par l
      end
  | IChoice(p1,p2) -> Types.Choice(intermediate_process_of_process p1,intermediate_process_of_process p2, fresh_position ())

let parse_intermediate_process env = function
  | EPlain proc -> parse_plain_process env proc


(****** Process declaration ********)

let rec parse_list_argument proc env = function
  | [] ->
      let generate_proc = function
        | [] -> parse_intermediate_process env proc
        | _ -> Config.internal_error "[parser_functions.ml >> parse_list_argument] This case should have been caught at the call (1)."
      in
      generate_proc
  | (var_s,line)::q ->
      begin
        try
          begin match Env.find var_s env with
            | ArgVar _ -> error_message line (Printf.sprintf "The identifier %s is already defined as argument of the function" var_s);
            | _ -> ()
          end
        with Not_found -> ()
      end;

      let generate_proc = function
        | [] ->  Config.internal_error "[parser_functions.ml >> parse_list_argument] This case should have been caught at the call (2)."
        | t::q_t ->
            let env' = Env.add var_s (ArgVar t) env in
            let generate_proc' = parse_list_argument proc env' q in
            generate_proc' q_t
      in
      generate_proc

let dummy_term = Types.Name(Term.Name.fresh ())

let parse_process_declaration env (s,line) var_list proc =
  if Env.mem s env
  then error_message line (Printf.sprintf "The identifier %s is already defined." s);

  let generate_proc = parse_list_argument proc env var_list in
  let _ = generate_proc (List.map (fun _ -> dummy_term) var_list) in (* To ensure that the process is parsed even if not called *)

  Env.add s (Proc (List.length var_list,generate_proc)) env

(****** Function declaration *******)

let rec parse_rewrite_rule_term env = function
  | Id (s,line) ->
      begin try
        match Env.find s env with
          | Var(v) -> Types.Var(v), env
          | Func(f) when Term.Symbol.get_arity f = 0 && Term.Symbol.is_constructor f -> Types.Func(f,[]), env
          | env_elt -> error_message line (Printf.sprintf "The identifiant %s is declared as %s (expected a variable or a constant)." s (display_env_elt_type env_elt))
      with
        | _ ->
            let x = Term.Variable.fresh Types.Existential in
            let env' = Env.add s (Var x) env in
            Types.Var(x), env'
      end
  | FuncApp((s,line),args) ->
      begin try
        match Env.find s env with
          | Func f when Term.Symbol.is_constructor f ->
              if (Term.Symbol.get_arity f) <> List.length args
              then error_message line (Printf.sprintf "The function %s is given %d arguments but is expecting %d arguments" s (List.length args) (Term.Symbol.get_arity f));

              let args', env' = parse_rewrite_rule_term_list env args in

              Types.Func(f,args'), env'
          | env_elt -> error_message line (Printf.sprintf "The identifiant %s is declared as %s (expected a constructor function)." s (display_env_elt_type env_elt))
      with
        Not_found -> error_message line (Printf.sprintf "The function %s is not declared" s)
      end
  | Tuple(args) ->
      Config.debug (fun () ->
        if List.length args <= 1
        then Config.internal_error "[parser_functions.ml >> parse_term] The number of arguments of a tuple should be at least 2."
      );
      let f = Term.Symbol.get_tuple (List.length args) in
      let args',env' = parse_rewrite_rule_term_list env args in
      Types.Func(f,args'), env'

and parse_rewrite_rule_term_list env = function
  | [] -> ([],env)
  | t::q ->
      let (t',env') = parse_rewrite_rule_term env t in
      let (q',env'') = parse_rewrite_rule_term_list env' q in
      (t'::q',env'')

let parse_rewrite_rule line env (lhs,rhs) = match lhs with
  | Id (s,line) ->
      if Env.mem s env
      then error_message line (Printf.sprintf "The identifier %s is already defined." s);

      let rhs' = parse_term env rhs in
      if Term.Term.no_name rhs' && Term.Term.is_constructor rhs'
      then (s,[],rhs')
      else error_message line "The right-hand side of a rewrite rule should be a name-free constructor term."
  | FuncApp((s,line),args) ->
      if Env.mem s env
      then error_message line (Printf.sprintf "The identifier %s is already defined." s);

      let (args',env') = parse_rewrite_rule_term_list env args in
      let rhs' = parse_term env' rhs in
      if Term.no_axname rhs' && Term.is_constructor rhs'
      then (s,args',rhs')
      else error_message line "The right-hand side of a rewrite rule should be a name-free constructor term."
  | _ -> error_message line "The left-hand side of a rewrite rule cannot be a tuple."

let parse_functions env = function
  | Constructor((s,line),n,public) ->
      if Env.mem s env
      then error_message line (Printf.sprintf "The identifier %s is already defined." s);

      let f = Term.Symbol.new_constructor n public false s in
      Env.add s (Func f) env
  | Destructor(rw_rules,public,line) ->
      let (symb,lhs,rhs) = parse_rewrite_rule line env (List.hd rw_rules) in
      let ar = List.length lhs in

      let rw_rules' =
        List.fold_left (fun acc rw_rule ->
          let (s,args',rhs') = parse_rewrite_rule line env rw_rule in
          if s <> symb
          then error_message line "Rewrite rules declared under the same `reduc' should all have the same root for the left-hand side.";

          if List.length args' <> ar
          then error_message line "The rewrite rules should have the same arity.";

          (args',rhs')::acc
        ) [lhs,rhs] (List.tl rw_rules)
      in
      let f = Term.Symbol.new_destructor ar public symb rw_rules' in
      Term.Rewrite_rules.is_subterm_convergent_symbol line f;
      Env.add symb (Func f) env

(****** Parse setting *******)

let already_chosen_semantics = ref false

let parse_setting line sem =
  if !already_chosen_semantics
  then warning_message line "A setting for the semantics has already been chosen. This new setting erases the previous one."

  (** TODO : Update that part of the code *)

  (*match sem with
    | Classic -> Process.chosen_semantics := Process.Classic; already_chosen_semantics := true
    | Private -> Process.chosen_semantics := Process.Private; already_chosen_semantics := true
    | Eavesdrop -> Process.chosen_semantics := Process.Eavesdrop; already_chosen_semantics := true*)

(****** Parse query *******)

let query_list = ref []

let parse_query env line = function
  | Trace_Eq(proc_1,proc_2) -> query_list := (Types.Trace_Equivalence,parse_extended_process env proc_1, parse_extended_process env proc_2)::!query_list
  | Sess_Eq(proc_1,proc_2) -> query_list := (Types.Session_Equivalence,parse_extended_process env proc_1, parse_extended_process env proc_2)::!query_list
  | Sess_Incl(proc_1,proc_2) -> query_list := (Types.Session_Inclusion,parse_extended_process env proc_1, parse_extended_process env proc_2)::!query_list
  | Obs_Eq(_,_) -> error_message line "Observational equivalence not implemented yet"

(****** Parse declaration *******)

let parse_one_declaration = function
  | Setting(sem,line) -> parse_setting line sem
  | FuncDecl f_list -> List.iter (fun f -> environment := parse_functions !environment f) f_list
  | FreeName (ident_list,pub) -> List.iter (fun ident -> environment := parse_free_name !environment pub ident) ident_list
  | Query (query,line) -> parse_query !environment line query
  | ExtendedProcess(id,var_list,proc) -> environment := parse_process_declaration !environment id var_list proc

let reset_parser () =
  environment := (Env.empty:env_elt Env.t);
  query_list := [];
