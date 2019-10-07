open Types

(* Configuration *)

type json_position =
  {
    js_index : int;
    js_args : int list
  }

type json_process =
  | JNil
  | JOutput of term * term * json_process * json_position
  | JInput of term * pattern * json_process * json_position
  | JIfThenElse of term * term * json_process * json_process * json_position
  | JLet of pattern * term * json_process * json_process * json_position
  | JNew of name * json_process * json_position
  | JPar of json_process list
  | JBang of int * json_process * json_position
  | JChoice of json_process * json_process * json_position

type configuration =
  {
    size_frame : int;
    frame : term list;
    process : json_process
  }

(* Traces *)

type json_transition =
  | JAOutput of recipe * json_position
  | JAInput of recipe * recipe * json_position
  | JAEaves of recipe * json_position * json_position
  | JAComm of json_position * json_position
  | JABang of int * json_position
  | JATau of json_position
  | JAChoice of json_position * bool (* True when the left process is chosen *)

type json_attack_trace =
  {
    id_proc : int;
    transitions : json_transition list
  }

(* Association table *)

type association =
  {
    size : int;
    symbols : (symbol * int) list;
    names : (name * int) list;
    variables : (variable * int) list
  }

(* JSON data *)

type json =
  | JString of string
  | JBool of bool
  | JInt of int
  | JNull
  | JObject of (string * json) list
  | JList of json list

type json_atomic =
  | JAtomVar of variable
  | JAtomName of name
  | JAtomSymbol of symbol

(* Query result *)

type query_status =
  | QCompleted of json_attack_trace option
  | QOngoing
  | QCanceled

type query_result =
  {
    name_query : string;
    q_status : query_status;
    q_batch_file : string;
    q_run_file : string;
    q_start_time : int option;
    q_end_time : int option;
    association : association;
    semantics : semantics;
    query_type : equivalence;
    processes : json_process list
  }

(* Run result *)

type run_status =
  | RUser_error of string
  | RInternal_error of string
  | RCompleted
  | RIn_progress

type run_result =
  {
    name_run : string;
    r_batch_file : string;
    r_status : run_status;
    input_file : string option;
    input_str : string option;
    r_start_time : int option;
    r_end_time : int option;
    query_result_files : string list option;
    query_results : query_result list option
  }

(* Batch result *)

type batch_options =
  | Nb_jobs of int
  | Round_timer of int
  | Default_semantics of semantics
  | Distant_workers of (string * string * int) list
  | Without_por
  | Distributed of int

type batch_result =
  {
    name_batch : string;
    deepsec_version : string;
    git_branch : string;
    git_hash : string;
    run_result_files : string list option;
    run_results : run_result list option;
    import_date : int option;
    command_options : batch_options list
  }

(* Input Command *)

type input_command =
  | Start_run of string list * batch_options list
  | Cancel_run of string
  | Cancel_query of string
  | Get_config
  | Set_config of string

type output_command =
  | Batch_started of string
  | Run_started of string
  | Query_started of string
  | Batch_ended of string
  | Run_ended of string
  | Query_ended of string
