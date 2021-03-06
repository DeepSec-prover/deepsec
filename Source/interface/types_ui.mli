(**************************************************************************)
(*                                                                        *)
(*                               DeepSec                                  *)
(*                                                                        *)
(*               Vincent Cheval, project PESTO, INRIA Nancy               *)
(*                Steve Kremer, project PESTO, INRIA Nancy                *)
(*            Itsaka Rakotonirina, project PESTO, INRIA Nancy             *)
(*                                                                        *)
(*   Copyright (C) INRIA 2017-2020                                        *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU General Public License version 3.0 as described in the       *)
(*   file LICENSE                                                         *)
(*                                                                        *)
(**************************************************************************)

open Types

(* Configuration *)

type json_position =
  {
    js_index : int;
    js_args : int list
  }

type json_pattern =
  | JPVar of variable * int
  | JPTuple of symbol * json_pattern list
  | JPEquality of term

type json_process =
  | JNil
  | JOutput of term * term * json_process * json_position
  | JInput of term * json_pattern * json_process * json_position
  | JIfThenElse of term * term * json_process * json_process * json_position
  | JLet of json_pattern * term * json_process * json_process * json_position
  | JNew of name * int * json_process * json_position
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
  | JAEaves of recipe * json_position (* out *) * json_position (* in *)
  | JAComm of json_position (* out *) * json_position (* in *)
  | JABang of int * json_position
  | JATau of json_position
  | JAChoice of json_position * bool (* True when the left process is chosen *)

type json_attack_trace =
  {
    id_proc : int;
    transitions : json_transition list
  }

type json_selected_transition =
  | JSAOutput of string option * json_position
  | JSAInput of string option * string option * json_position
  | JSAEaves of string option * json_position (* out *) * json_position (* in *)
  | JSAComm of json_position (* out *) * json_position (* in *)
  | JSABang of int * json_position
  | JSATau of json_position
  | JSAChoice of json_position * bool (* True when the left process is chosen *)

(* Association table *)

type association =
  {
    size : int;
    symbols : (symbol * int) list;
    names : (name * int) list;
    variables : (variable * int) list
  }

type replicated_association =
  {
    repl_names : (name * (int * int list)) list;
    repl_variables : (variable * (int * int list)) list
  }

type full_association =
  {
    std : association;
    repl : replicated_association
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
    progression : query_progression;
    memory : int
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
    pid : int;
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

type available_transition =
  | AVDirect of recipe * recipe option * bool (* Indicate whether the recipes are lock or not. *)
  | AVComm
  | AVEavesdrop of recipe

type available_action =
  | AV_output of json_position (* output *) * term * json_position list (* tau actions *) * available_transition list
  | AV_input of json_position (* input *) * term * json_position list (* tau actions *) * available_transition list
  | AV_bang of json_position (* bang *) * int (* max nb of unfolding *) * json_position list (* tau actions *)
  | AV_choice of json_position (* choice *) * json_position list (* tau actions *)
  | AV_tau of json_position

type status_static_equivalence =
  | Static_equivalent
  | Witness_message of recipe * term * int
  | Witness_equality of recipe * recipe * term * term * term * int

(* Input Command *)

type input_command =
  | Start_run of string list * batch_options list
  | Cancel_run of string
  | Cancel_query of string
  | Cancel_batch
  | Get_config
  (* Simulator generic command *)
  | Die
  | Goto_step of int (* id process *) * int (* id step *)
  | Next_step_user of json_selected_transition
  | Next_steps of json_transition list
  (* Simulator: Display of traces *)
  | Display_trace of string * int (* Json of query result *)
  (* Simulator: Attack_simulator *)
  | Attack_simulator of string (* Json of query result *)
  (* Simulator: Equivalence_simulator *)
  | Equivalence_simulator of string * int (* process Id *)
  | ESSelect_trace of int
  | ESFind_equivalent_trace

type output_command =
  (* Errors *)
  | Init_internal_error of string * bool
  | Batch_internal_error of string
  | User_error of
      (string (* Error msg*) * string (* file *) * string list (* warnings *)) list *
      (string (* host *) * string (* Error msg *) list) list
  | Query_internal_error of string (* Error msg*) * string (* file *)
  (* Config *)
  | Send_Configuration
  (* Started *)
  | Batch_started of string * (string * string * string list) list
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
      int (* Memory used. = 0 when not defined *) *
      equivalence
  (* Exit *)
  | Run_canceled of string
  | Query_canceled of string
  | Batch_canceled of string
  (* Progression *)
  | Progression of int (* Index of query *) * int (* execution time *) * query_progression * string (* json_file *)
  (* Simulator: Generic command *)
  | SCurrent_step_displayed of full_association * configuration * name list * int * int option (* Process id *)
  | SCurrent_step_user of full_association * configuration * name list * json_transition list (* New transitions *) * available_action list (* All *)* available_action list (* default *)* status_static_equivalence option * int (* Process id *)
  | SFound_equivalent_trace of full_association * json_transition list
  | SUser_error of string
