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

type progression =
  | PVerif of int (* Percent *) * int (* Job remaining *)
  | PGeneration of int (* Job generated *) * int (* Minimum nb of jobs *)

type query_progression =
  | PDistributed of int (* Round *) * progression
  | PSingleCore of progression
  | PNot_defined

type query_status =
  | QCompleted of json_attack_trace option
  | QWaiting
  | QIn_progress
  | QCanceled
  | QInternal_error of string

type query_settings =
  {
    var_set : int; (* Indicate the largest index created for a variable *)
    name_set : int; (* Indicate the largest index created for a name *)
    symbol_set : Term.Symbol.setting
  }

(* We assume that the association contains all variables, names and symbols
   occurring in the signature, processes and traces. *)
type query_result =
  {
    name_query : string;
    q_index : int;
    q_status : query_status;
    q_batch_file : string;
    q_run_file : string;
    q_start_time : int option;
    q_end_time : int option;
    association : association;
    semantics : semantics;
    query_type : equivalence;
    processes : json_process list;
    settings : query_settings;
    progression : query_progression
  }

(* Run result *)

type run_batch_status =
  | RBInternal_error of string
  | RBWaiting
  | RBCompleted
  | RBIn_progress
  | RBCanceled

type run_result =
  {
    name_run : string;
    r_batch_file : string;
    r_status : run_batch_status;
    input_file : string option;
    input_str : string option;
    r_start_time : int option;
    r_end_time : int option;
    query_result_files : string list option;
    query_results : query_result list option;
    warnings : string list
  }

(* Batch result *)

type batch_options =
  | Nb_jobs of int option
  | Round_timer of int
  | Default_semantics of semantics
  | Distant_workers of (string * string * int option) list
  | Distributed of bool option
  | Local_workers of int option
  | Quiet
  | ShowTrace
  | POR of bool
  | Title of string

type batch_result =
  {
    name_batch : string;
    b_status : run_batch_status;
    b_start_time : int option;
    b_end_time : int option;
    deepsec_version : string;
    git_branch : string;
    git_hash : string;
    run_result_files : string list option;
    run_results : run_result list option;
    import_date : int option;
    command_options : batch_options list;
    command_options_cmp : batch_options list;
    ocaml_version : string;
    debug : bool
  }

(* Simulator types *)

type detail_trace_display =
  | DTFull
  | DTStandard
  | DTIO_only

(* Input Command *)

type input_command =
  | Start_run of string list * batch_options list
  | Cancel_run of string
  | Cancel_query of string
  | Cancel_batch
  | Get_config
  | Set_config of string
  | Die
  (* Simulator: Display of traces *)
  | Display_trace of string (* Json of query result *)
  | DTNext_step of detail_trace_display
  | DTPrev_step of detail_trace_display

type output_command =
  (* Errors *)
  | Init_internal_error of string * bool
  | Batch_internal_error of string
  | User_error of (string (* Error msg*) * string (* file *) * string list (* warnings *)) list
  | Query_internal_error of string (* Error msg*) * string (* file *)
  (* Started *)
  | Batch_started of string * (string * string list) list
  | Run_started of string * string (* Dps file *)
  | Query_started of string * int (* Index of query *)
  (* Ended *)
  | Batch_ended of string * run_batch_status
  | Run_ended of string * run_batch_status
  | Query_ended of
      string *
      query_status *
      int (* Index of query *) *
      int (* Running time *) *
      equivalence
  (* Exit *)
  | Run_canceled of string
  | Query_canceled of string
  | Batch_canceled
  | ExitUi
  (* Progression *)
  | Progression of int (* Index of query *) * int (* execution time *) * query_progression
  (* Simulator: Display_of_traces *)
  | DTNo_attacker_trace
  | DTCurrent_step of association * configuration * int
