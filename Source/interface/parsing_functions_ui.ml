open Extensions
open Types
open Types_ui
open Term

(*** Parsing into JSON ***)

let parse_json_from_file path =

  if not (Sys.file_exists path)
  then raise (Standard_error (File_Not_Found path));

  let channel_in = open_in path in
  let lexbuf = Lexing.from_channel channel_in in

  let json = Grammar_ui.main Lexer_ui.token lexbuf in

  close_in channel_in;
  json

let parse_json_from_string str =
  let lexbuf = Lexing.from_string str in
  Grammar_ui.main Lexer_ui.token lexbuf

(*** Basic function ***)

let member label = function
  | JObject l ->
      begin
        try List.assoc label l
        with Not_found -> Config.internal_error (Printf.sprintf "[parsing_functions_ui.ml >> member] Label %s not belonging to json object." label)
      end
  | _ -> Config.internal_error "[parsing_functions_ui.ml >> member] Expecting a json object."

let member_opt label = function
  | JObject l -> List.assoc_opt label l
  | _ -> Config.internal_error "[parsing_functions_ui.ml >> member_opt] Expecting a json object."

let member_option f label = function
  | JObject l ->
      begin match List.assoc_opt label l with
        | Some a -> Some (f a)
        | None -> None
      end
  | _ -> Config.internal_error "[parsing_functions_ui.ml >> member_opt] Expecting a json object."

let iter_member_option f label = function
  | JObject l ->
      begin match List.assoc_opt label l with
        | Some a -> f a
        | None -> ()
      end
  | _ -> Config.internal_error "[parsing_functions_ui.ml >> member_opt] Expecting a json object."

(*** Basic Convertor function ***)

let int_of = function
  | JInt i -> i
  | _ -> Config.internal_error "[parsing_functions_ui.ml >> int_of] Wrong structure."

let int_auto_of = function
  | JInt i -> Some i
  | JString "auto" -> None
  | _ -> Config.internal_error "[parsing_functions_ui.ml >> int_auto_of] Wrong structure."

let bool_of = function
  | JBool b -> b
  | _ -> Config.internal_error "[parsing_functions_ui.ml >> bool_of] Wrong structure."

let bool_auto_of = function
  | JBool i -> Some i
  | JString "auto" -> None
  | _ -> Config.internal_error "[parsing_functions_ui.ml >> bool_auto_of] Wrong structure."

let bool_option_of = function
  | None -> false
  | Some b -> bool_of b

let string_of = function
  | JString s -> s
  | _ -> Config.internal_error "[parsing_functions_ui.ml >> string_of] Wrong structure."

let list_of f_parse = function
  | JList l -> List.map f_parse l
  | _ -> Config.internal_error "[parsing_functions_ui.ml >> list_of] Wrong structure."

let rec term_of assoc json = match string_of (member "type" json) with
  | "Atomic" ->
      let id = int_of (member "id" json) in
      begin match assoc.(id) with
        | JAtomVar v -> Var v
        | JAtomName n -> Name n
        | _ -> Config.internal_error "[parsing_functions_ui.ml >> term_of] Should not be a function symbol."
      end
  | "Function" ->
      let symbol_id = int_of (member "symbol" json) in
      let args = list_of (term_of assoc) (member "args" json) in
      let symbol = match assoc.(symbol_id) with
        | JAtomSymbol f -> f
        | _ -> Config.internal_error "[parsing_functions_ui.ml >> term_of] Should be a function symbol."
      in
      Func(symbol,args)
  | "Attacker" ->
      let label = string_of (member "label" json) in
      Func(Symbol.get_attacker_name label,[])
  | _ -> Config.internal_error "[parsing_functions_ui.ml >> term_of] Wrong value for type label."

let rec pattern_of assoc json = match string_of (member "type" json) with
  | "Atomic" ->
      let id = int_of (member "id" json) in
      begin match assoc.(id) with
        | JAtomVar v -> PatVar v
        | _ -> Config.internal_error "[parsing_functions_ui.ml >> pattern_of] Should be a variable."
      end
  | "Equality" -> PatEquality (term_of assoc (member "term" json))
  | "Function" ->
      let symbol_id = int_of (member "symbol" json) in
      let args = list_of (pattern_of assoc) (member "args" json) in
      let symbol = match assoc.(symbol_id) with
        | JAtomSymbol f -> f
        | _ -> Config.internal_error "[parsing_functions_ui.ml >> pattern_of] Should be a function symbol."
      in
      PatTuple(symbol,args)
  | _ -> Config.internal_error "[parsing_functions_ui.ml >> pattern_of] Wrong value for type label."

let rec recipe_of assoc json = match string_of (member "type" json) with
  | "Axiom" ->  Axiom (int_of (member "id" json))
  | "Function" ->
      let symbol_id = int_of (member "symbol" json) in
      let args = list_of (recipe_of assoc) (member "args" json) in
      let symbol = match assoc.(symbol_id) with
        | JAtomSymbol f -> f
        | _ -> Config.internal_error "[parsing_functions_ui.ml >> recipe_of] Should be a function symbol."
      in
      RFunc(symbol,args)
  | "Attacker" ->
      let label = string_of (member "label" json) in
      RFunc(Symbol.get_attacker_name label,[])
  | _ -> Config.internal_error "[parsing_functions_ui.ml >> recipe_of] Wrong value for type label."

(*** Atomic and association data ***)

let rewrite_rule_of assoc json =
  let lhs = list_of (term_of assoc) (member "lhs" json) in
  let rhs = term_of assoc (member "rhs" json) in
  (lhs,rhs)

let representation_of json = match string_of json with
  | "UserName" -> UserName
  | "UserDefined" -> UserDefined
  | "Attacker" -> AttackerPublicName
  | _ -> Config.internal_error "[parsing_functions_ui.ml >> representation_of] Wrong value."

let tuple_constructor_of all_t all_c all_p nb_c cat json =
  let index = int_of (member "index" json) in
  let label = string_of (member "label" json) in
  let arity = int_of (member "arity" json) in
  let representation = representation_of (member "representation" json) in
  let public = bool_option_of (member_opt "is_public" json) in

  let res_search =
    List.find_opt (fun f ->
        Config.debug (fun () ->
          if f.index_s = index && (f.label_s <> label || f.arity <> arity || f.represents <> representation || f.public <> public)
          then Config.internal_error "[parsinf_functions_ui.ml >> tuple_constructor_of] Incoherent data."
        );
        f.index_s = index
    ) !all_c
  in

  match res_search with
    | Some f -> f
    | None ->
        let f = { label_s = label; index_s = index; arity = arity; cat = cat; public = public; represents = representation } in
        if cat = Tuple
        then
          begin
            all_t := f :: !all_t;
            all_p := (f,[]) :: !all_p
          end;
        all_c := f :: !all_c;
        incr nb_c;
        f

let projection_of assoc all_p id_t id_p rw_rules json =
  let f_tuple = match assoc.(id_t) with
    | JAtomSymbol f -> f
    | _ -> Config.internal_error "[parsing_functions_ui.ml >> projection_of] Should be a function symbol."
  in

  let index = int_of (member "index" json) in
  let label = string_of (member "label" json) in
  let arity = int_of (member "arity" json) in
  let representation = representation_of (member "representation" json) in
  let public = bool_option_of (member_opt "is_public" json) in

  let result_f = ref None in

  let rec explore_all_p = function
    | [] -> Config.internal_error "[parsing_functions_ui.ml >> projection_of] The tuple function symbol should occur"
    | (f,projs)::q when f == f_tuple -> (f,explore_projs projs)::q
    | h::q -> h::(explore_all_p q)

  and explore_projs = function
    | [] ->
        let rewrite_rules = list_of (rewrite_rule_of assoc) rw_rules in
        let f = { label_s = label; index_s = index; arity = arity; cat = Destructor rewrite_rules; public = public; represents = representation } in
        result_f := Some f;
        [(id_p,f)]
    | (id,f)::q when id < id_p -> (id,f)::(explore_projs q)
    | (id,f)::q when id = id_p ->
        Config.debug (fun () ->
          if f.index_s <> index || f.arity <> arity || f.label_s <> label || f.public <> public || f.represents <> representation
          then Config.internal_error "[parsing_functions_ui.ml >> projection_of] Improper match."
        );
        result_f := Some f;
        (id,f)::q
    | (id,f)::q ->
        let rewrite_rules = list_of (rewrite_rule_of assoc) rw_rules in
        let f' = { label_s = label; index_s = index; arity = arity; cat = Destructor rewrite_rules; public = public; represents = representation } in
        result_f := Some f;
        (id_p,f')::(id,f)::q
  in

  all_p := explore_all_p !all_p;
  match !result_f with
    | None -> Config.internal_error "[parsing_functions_ui.ml >> projection_of] A projection should have been defined."
    | Some f -> f

let destructor_of assoc all_d nb_d rw_rules json =
  let index = int_of (member "index" json) in
  let label = string_of (member "label" json) in
  let arity = int_of (member "arity" json) in
  let representation = representation_of (member "representation" json) in
  let public = bool_option_of (member_opt "is_public" json) in

  let res_search =
    List.find_opt (fun f ->
        Config.debug (fun () ->
          if f.index_s = index && (f.label_s <> label || f.arity <> arity || f.represents <> representation || f.public <> public)
          then Config.internal_error "[parsinf_functions_ui.ml >> destructor_of] Incoherent data."
        );
        f.index_s = index
    ) !all_d
  in

  match res_search with
    | Some f -> f
    | None ->
        let rewrite_rules = list_of (rewrite_rule_of assoc) rw_rules in
        let f = { label_s = label; index_s = index; arity = arity; cat = Destructor rewrite_rules; public = public; represents = representation } in
        incr nb_d;
        all_d := f :: !all_d;
        f

let atomic_association_of = function
  | JList value_l ->
      let size = List.length value_l in
      let assoc = Array.make size (JAtomVar{label = ""; index = 0; link = NoLink; quantifier = Existential}) in
      let all_t = ref [] in
      let all_p = ref [] in
      let all_c = ref [] in
      let all_d = ref [] in
      let nb_c = ref 0 in
      let nb_d = ref 0 in

      List.iteri (fun i json -> match string_of (member "type" json) with
        | "Variable" ->
            let label = string_of (member "label" json) in
            let index = int_of (member "index" json) in
            let free = bool_option_of (member_opt "free" json) in
            let quantifier = if free then Free else Existential in
            assoc.(i) <- JAtomVar {label = label; index = index; link = NoLink; quantifier = quantifier}
        | "Name" ->
            let label = string_of (member "label" json) in
            let index = int_of (member "index" json) in
            assoc.(i) <- JAtomName {label_n = label; index_n = index; pure_fresh_n = false; link_n = NNoLink; deducible_n = None}
        | "Symbol" ->
            let cat = member "category" json in
            begin match string_of (member "type" cat) with
              | "Tuple" -> assoc.(i) <- JAtomSymbol (tuple_constructor_of all_t all_c all_p nb_c Tuple json)
              | "Constructor" -> assoc.(i) <- JAtomSymbol (tuple_constructor_of all_t all_c all_p nb_c Constructor json)
              | "Destructor" | "Projection" -> ()
              | _ -> Config.internal_error "[parsing_functions_ui.ml >> atomic_association_of] Unexpected type for category."
            end
        | _ -> Config.internal_error "[parsing_functions_ui.ml >> atomic_association_of] Unexpected type."
      ) value_l;

      (* We now parse the destructors *)

      List.iteri (fun i json -> match string_of (member "type" json) with
        | "Variable" | "Name" -> ()
        | "Symbol" ->
            let cat = member "category" json in
            begin match string_of (member "type" cat) with
              | "Tuple" | "Constructor" -> ()
              | "Destructor" ->
                  let rw_rules = member "rewrite_rules" cat in
                  assoc.(i) <- JAtomSymbol (destructor_of assoc all_d nb_d rw_rules json)
              | "Projection" ->
                  let rw_rules = member "rewrite_rules" cat in
                  let id_t = int_of (member "tuple" cat) in
                  let id_p = int_of (member "projection_nb" cat) in
                  assoc.(i) <- JAtomSymbol (projection_of assoc all_p id_t id_p rw_rules json)
              | _ -> Config.internal_error "[parsing_functions_ui.ml >> atomic_association_of] Unexpected type for category."
            end
        | _ -> Config.internal_error "[parsing_functions_ui.ml >> atomic_association_of] Unexpected type."
      ) value_l;

      let symbol_setting =
        {
          Symbol.all_t = !all_t;
          Symbol.all_p =
            List.map (fun (f_t,projs) ->
              (f_t,List.map (fun (_,f) -> f) projs)
            ) !all_p;
          Symbol.all_c = !all_c;
          Symbol.all_d = !all_d;
          Symbol.nb_c = !nb_c;
          Symbol.nb_d = !nb_d;
          Symbol.nb_symb = 0;
          Symbol.nb_a = 0
        }
      in

      assoc, symbol_setting
  | _ -> Config.internal_error "[parsing_functions_ui.ml >> atomic_association_of] Unexpected case."

let atomic_data_of json =
  let meta_json = member "meta" json in
  let (assoc,symbol_settings) = atomic_association_of (member "data" json) in

  let symbol_settings1 =
    { symbol_settings with
      Symbol.nb_symb = int_of (member "number_symbols" meta_json);
      Symbol.nb_a = int_of (member "number_attacker_names" meta_json)
    }
  in

  let query_setting =
    {
      var_set = int_of (member "number_variables" meta_json);
      name_set = int_of (member "number_names" meta_json);
      symbol_set = symbol_settings1
    }
  in
  assoc, query_setting

(*** Traces and processes ***)

let semantics_of json = match string_of json with
  | "private" -> Private
  | "classic" -> Classic
  | "eavesdrop" -> Eavesdrop
  | _ -> Config.internal_error "[parsing_functions_ui.ml >> semantics_of] Wrong format"

let position_of json =
  let index = int_of (member "index" json) in
  let args = list_of int_of (member "args" json) in
  { js_index = index; js_args = args }

let rec process_opt_of assoc = function
  | None -> JNil
  | Some p_json -> process_of assoc p_json

and process_of assoc json =
  let type_json = member "type" json in
  if type_json = JNull
  then JNil
  else
    match string_of type_json with
      | "Output" ->
          let ch = term_of assoc (member "channel" json) in
          let t = term_of assoc (member "term" json) in
          let pos = position_of (member "position" json) in
          let p = process_opt_of assoc (member_opt "process" json) in
          JOutput(ch,t,p,pos)
      | "Input" ->
          let ch = term_of assoc (member "channel" json) in
          let pat = pattern_of assoc (member "pattern" json) in
          let pos = position_of (member "position" json) in
          let p = process_opt_of assoc (member_opt "process" json) in
          JInput(ch,pat,p,pos)
      | "IfThenElse" ->
          let t1 = term_of assoc (member "term1" json) in
          let t2 = term_of assoc (member "term2" json) in
          let pos = position_of (member "position" json) in
          let p1 = process_opt_of assoc (member_opt "process_then" json) in
          let p2 = process_opt_of assoc (member_opt "process_else" json) in
          JIfThenElse(t1,t2,p1,p2,pos)
      | "LetInElse" ->
          let pat = pattern_of assoc (member "pattern" json) in
          let t = term_of assoc (member "term" json) in
          let pos = position_of (member "position" json) in
          let p1 = process_opt_of assoc (member_opt "process_then" json) in
          let p2 = process_opt_of assoc (member_opt "process_else" json) in
          JLet(pat,t,p1,p2,pos)
      | "New" ->
          let n = match assoc.(int_of (member "name" json)) with
            | JAtomName n -> n
            | _ -> Config.internal_error "[parsinf_functions_ui.ml >> process_of] Should be a name"
          in
          let pos = position_of (member "position" json) in
          let p = process_opt_of assoc (member_opt "process" json) in
          JNew(n,p,pos)
      | "Par" -> JPar (list_of (process_of assoc) (member "process_list" json))
      | "Bang" ->
          let n = int_of (member "multiplicity" json) in
          let pos = position_of (member "position" json) in
          let p = process_opt_of assoc (member_opt "process" json) in
          JBang(n,p,pos)
      | "Choice" ->
          let pos = position_of (member "position" json) in
          let p1 = process_opt_of assoc (member_opt "process1" json) in
          let p2 = process_opt_of assoc (member_opt "process2" json) in
          JChoice(p1,p2,pos)
      | _ -> Config.internal_error "[parsing_functions_ui.ml >> process_of] Unexpected type."

let transition_of assoc json = match string_of (member "type" json) with
  | "output" ->
      let r_ch = recipe_of assoc (member "channel" json) in
      let pos = position_of (member "position" json) in
      JAOutput(r_ch,pos)
  | "input" ->
      let r_ch = recipe_of assoc (member "channel" json) in
      let r_t = recipe_of assoc (member "term" json) in
      let pos = position_of (member "position" json) in
      JAInput(r_ch,r_t,pos)
  | "comm" ->
      let pos_out = position_of (member "output_position" json) in
      let pos_in = position_of (member "input_position" json) in
      JAComm(pos_out,pos_in)
  | "eavesdrop" ->
      let r_ch = recipe_of assoc (member "channel" json) in
      let pos_out = position_of (member "output_position" json) in
      let pos_in = position_of (member "input_position" json) in
      JAEaves(r_ch,pos_out,pos_in)
  | "bang" ->
      let pos = position_of (member "position" json) in
      let n = int_of (member "nb_process_unfolded" json) in
      JABang(n,pos)
  | "tau" ->
      let pos = position_of (member "position" json) in
      JATau pos
  | "choice" ->
      let pos = position_of (member "position" json) in
      let side = bool_option_of (member_opt "choose_left" json) in
      JAChoice(pos,side)
  | _ -> Config.internal_error "[parsing_functions_ui.ml >> transition_of] Wrong format."

let attack_trace_of assoc json =
  let id_proc = int_of (member "index_process" json) in
  let transitions = list_of (transition_of assoc) (member "action_sequence" json) in
  { id_proc = id_proc; transitions = transitions }

(*** Query, run and batch result ***)

let progression_of json =
  let round = int_of (member "round" json) in
  match member_opt "verification" json with
    | Some json_verif ->
        let percent = int_of (member "percent" json_verif) in
        let jobs_remaining = int_of (member "jobs_remaining" json_verif) in
        if round = 0
        then PSingleCore (PVerif(percent,jobs_remaining))
        else PDistributed(round,PVerif(percent,jobs_remaining))
    | None ->
        let json_gen = member "generation" json in
        let minimum_jobs = int_of (member "minimum_jobs" json_gen) in
        let jobs_created = int_of (member "jobs_created" json_gen) in
        if round = 0
        then PSingleCore (PGeneration(jobs_created,minimum_jobs))
        else PDistributed(round,PGeneration(jobs_created,minimum_jobs))

let query_result_of file_name json =
  let (assoc,setting) = atomic_data_of (member "atomic_data" json) in
  let batch_file = string_of (member "batch_file" json) in
  let run_file = string_of (member "run_file" json) in
  let index = int_of (member "index" json) in
  let start_time = member_option int_of "start_time" json in
  let end_time = member_option int_of "end_time" json in
  let proc_l = list_of (process_of assoc) (member "processes" json) in
  let sem = semantics_of (member "semantics" json) in
  let status = match string_of (member "status" json) with
    | "in_progress" -> QIn_progress
    | "waiting" -> QWaiting
    | "canceled" -> QCanceled
    | "completed" ->
        let res = member_option (attack_trace_of assoc) "attack_trace" json in
        QCompleted res
    | "internal_error" ->
        let err = string_of (member "error_msg" json) in
        QInternal_error err
    | _ -> Config.internal_error "[parsing_functions_ui.ml >> query_result_of] Unexpected status."
  in
  let equiv_type = match string_of (member "type" json) with
    | "trace_equiv" -> Trace_Equivalence
    | "trace_incl" -> Trace_Inclusion
    | "session_equiv" -> Session_Equivalence
    | "session_incl" -> Session_Inclusion
    | _ -> Config.internal_error "[parsing_functions_ui.ml >> query_result_of] Unexpected equivalence type."
  in
  let association =
    let symbols = ref [] in
    let names = ref [] in
    let variables = ref [] in
    let size = Array.length assoc in

    for i = 0 to size - 1 do
      match assoc.(i) with
        | JAtomName n -> names := (n,i)::!names
        | JAtomSymbol f -> symbols := (f,i)::!symbols
        | JAtomVar v -> variables := (v,i)::!variables
    done;

    {
      size = size;
      symbols = !symbols;
      names = !names;
      variables = !variables
    }
  in

  let progression = match member_opt "progression" json with
    | None -> PNot_defined
    | Some json' -> progression_of json'
  in

  {
    name_query = file_name;
    q_index = index;
    q_status = status;
    q_batch_file = batch_file;
    q_run_file = run_file;
    q_start_time = start_time;
    q_end_time = end_time;
    query_type = equiv_type;
    association = association;
    semantics = sem;
    processes = proc_l;
    settings = setting;
    progression = progression
  },
  assoc

let run_batch_status_of json = match string_of (member "status" json) with
  | "waiting" -> RBWaiting
  | "in_progress" -> RBIn_progress
  | "canceled" -> RBCanceled
  | "completed" -> RBCompleted
  | "internal_error" ->
      let err = string_of (member "error_msg" json) in
      RBInternal_error err
  | _ -> Config.internal_error "[parsing_functions_ui.ml >> run_batch_status_of] Unexpected status."

(* We assume that we do not parse run that contain query result as json data. *)
let run_result_of file_name json =
  let batch_file = string_of (member "batch_file" json) in
  let status = run_batch_status_of json in
  let start_time = member_option int_of "start_time" json in
  let end_time = member_option int_of "end_time" json in
  let input_file = member_option string_of "input_file" json in
  let query_result_files = member_option (list_of string_of) "query_files" json in
  let warnings = list_of string_of (member "warnings" json) in
  {
    name_run = file_name;
    r_batch_file = batch_file;
    r_status = status;
    input_file = input_file;
    input_str = None;
    r_start_time = start_time;
    r_end_time = end_time;
    query_result_files = query_result_files;
    query_results = None;
    warnings = warnings
  }

let batch_options_of json =
  let options = ref [] in

  let distant_of json' =
    let host = string_of (member "host" json') in
    let path = string_of (member "path" json') in
    let nb_workers = int_auto_of (member "workers" json') in
    (host,path,nb_workers)
  in

  let check_member f str = match member_opt str json with
    | None -> ()
    | Some json' -> options := (f json') :: !options
  in

  check_member (fun json' -> Nb_jobs (int_auto_of json')) "nb_jobs";
  check_member (fun json' -> Round_timer (int_of json')) "round_timer";
  check_member (fun json' -> Default_semantics (semantics_of json')) "default_semantics";
  check_member (fun json' -> Distant_workers (list_of distant_of json')) "distant_workers";
  check_member (fun json' -> Local_workers (int_auto_of json')) "local_workers";
  check_member (fun json' -> Distributed (bool_auto_of json')) "distributed";
  check_member (fun json' -> POR (bool_of json')) "por";
  check_member (fun json' -> Title (String.escaped (string_of json'))) "title";

  !options

(* We assume that we do not parse bacth that contain run result as json data. *)
let batch_result_of file_name json =
  let ocaml_version = string_of (member "ocaml_version" json) in
  let version = string_of (member "deepsec_version" json) in
  let git_branch = string_of (member "git_branch" json) in
  let git_hash = string_of (member "git_hash" json) in
  let run_result_files = member_option (list_of string_of) "run_files" json in
  let import_date = member_option int_of "import_date" json in
  let start_time = member_option int_of "start_time" json in
  let end_time = member_option int_of "end_time" json in
  let command_options = batch_options_of (member "command_options" json) in
  let status = run_batch_status_of json in

  {
    name_batch = file_name;
    b_status = status;
    b_start_time = start_time;
    b_end_time = end_time;
    deepsec_version = version;
    git_branch = git_branch;
    git_hash = git_hash;
    run_result_files = run_result_files;
    run_results = None;
    import_date = import_date;
    command_options = command_options;
    command_options_cmp = [];
    ocaml_version = ocaml_version;
    debug = Config.debug_activated
  }

(*** Simulator ***)

let detail_of json = match string_of (member "detail" json) with
  | "standard" -> DTStandard
  | "io_only" -> DTIO_only
  | "full" -> DTFull
  | _ -> Config.internal_error "[parsing_functions_ui.ml >> detail_of] Unexpected argument."

(*** Commands ***)

let input_command_of ?(assoc=None) json = match string_of (member "command" json) with
  | "start_run" ->
      let input_files = list_of string_of (member "input_files" json) in
      let command_options = batch_options_of (member "command_options" json) in
      Start_run(input_files,command_options)
  | "cancel_run" -> Cancel_run (string_of (member "result_file" json))
  | "cancel_query" -> Cancel_query (string_of (member "result_file" json))
  | "cancel_batch" | "exit" -> Cancel_batch
  | "get_config" -> Get_config
  | "set_config" -> Set_config (string_of (member "output_dir" json))
  | "start_display_trace" -> Display_trace (string_of (member "query_file" json))
  | "die" -> Die
  | "goto_step" ->
      begin match member_opt "process_id" json with
        | None -> DTGo_to (int_of (member "id" json))
        | Some pid -> ASGo_to(int_of pid,int_of (member "id" json))
      end
  | "start_attack_simulator" -> Attack_simulator (string_of (member "query_file" json))
  | "next_step_simulated" ->
      let assoc_tbl = match assoc with
        | None -> Config.internal_error "[parsing_function.ml >> input_command_of] Expect an associtation table."
        | Some assoc_tbl ->  assoc_tbl
      in
      ASNext_step (transition_of assoc_tbl (member "selected_action" json))
  | _ -> Config.internal_error "[parsing_functions_ui.ml >> input_command_of] Unknown command."
