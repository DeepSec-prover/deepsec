open Types
open Types_ui
open Display

let string_of_string_list str_list = List.fold_right (fun str acc -> str^"\n"^acc) str_list ""

let display_with_tab i str =
  let rec create_tab = function
    | 0 -> ""
    | i -> "  "^(create_tab (i-1))
  in
  (create_tab i)^str

let display_string_list str_list =
  List.fold_right (fun (tab,str) acc -> (display_with_tab tab str)^"\n"^acc) str_list ""

let header =
  display_string_list [
    0, coloured_terminal_text Black [Bold] "DeepSec - DEciding Equivalence Properties for SECurity protocols";
    2, Printf.sprintf "Version: %s" !Config.version;
    2, Printf.sprintf "Git hash: %s" !Config.git_commit;
    2, Printf.sprintf "Git branch: %s" !Config.git_branch;
  ]

let help =
  let file = coloured_terminal_text Black [Underline] "FILE" in
  let deepsec = coloured_terminal_text Black [Bold] "deepsec" in
  let value = coloured_terminal_text Black [Underline] "VALUE" in
  let int_value = coloured_terminal_text Black [Underline] "INT" in
  let bool_value = coloured_terminal_text Black [Underline] "BOOL" in
  let host_value = coloured_terminal_text Black [Underline] "HOST" in
  let path_value = coloured_terminal_text Black [Underline] "PATH" in
  display_string_list [
    0, coloured_terminal_text Black [Bold] "Usage";
    2, Printf.sprintf "%s [OPTIONS] ... %s" deepsec file;
    0, "\n";
    0, coloured_terminal_text Black [Bold] "Description";
    2, Printf.sprintf "%s analyses each specified %s." deepsec file;
    0, "\n";
    0, coloured_terminal_text Black [Bold] "General options";
    2, Printf.sprintf "%s %s (default=private)" (coloured_terminal_text Black [Bold] "-s, --semantics") value;
    4, Printf.sprintf "Specify the default semantics of the process calculus. The value %s must be one of" value;
    4, Printf.sprintf "'private', 'classic' or 'eavesdrop'. With 'classic', %s allows internal communication" deepsec;
    4, Printf.sprintf "on public channels. With 'private', internal communications are only allowed on private";
    4, Printf.sprintf "channels. With 'eavesdrop', the attacker is allowed to eavesdrop on public channels.";
    4, Printf.sprintf "For more details, see the following paper by Babel, Cheval, Kremer:";
    5, Printf.sprintf "'On Communication Models When Verifying Equivalence Properties'";
    0, "\n";
    2, Printf.sprintf "%s %s (default=true)" (coloured_terminal_text Black [Bold] "-p, --por") bool_value;
    4, Printf.sprintf "When 'true', %s applies Partial Order Reduction (POR) techniques to verify trace" deepsec;
    4, Printf.sprintf "equivalence. POR can only be applied on action determinate processes. Thus, even";
    4, Printf.sprintf "with 'true', %s will apply the POR techniques only when it is able to prove that" deepsec;
    4, Printf.sprintf "the processes are action-determinate.";
    0, "\n";
    2, Printf.sprintf "%s" (coloured_terminal_text Black [Bold] "-q, --quiet");
    4, Printf.sprintf "Only display the result of query verification.";
    0, "\n";
    2, Printf.sprintf "%s" (coloured_terminal_text Black [Bold] "-t, --trace");
    4, Printf.sprintf "When an attack is found, display the full trace with the execution of the process.";
    4, Printf.sprintf "Incompatible with %s." (coloured_terminal_text Black [Bold] "--quiet");
    0, "\n";
    2, Printf.sprintf "%s" (coloured_terminal_text Black [Bold] "-h, -help, --help");
    4, Printf.sprintf "Show this help.";
    0, "\n";
    0, coloured_terminal_text Black [Bold] "Options for distributing computation";
    2, Printf.sprintf "%s %s (default=auto)" (coloured_terminal_text Black [Bold] "-d, --distributed") value;
    4, Printf.sprintf "Specify if the computation should be distributed. The value %s must be one of" value;
    4, Printf.sprintf "'auto', 'true' or 'false'. With 'auto', %s will activates the distributed" deepsec;
    4, Printf.sprintf "computation depending on the number of physical cores in your computer. With 'true',";
    4, Printf.sprintf "%s activates the distributed computation even if your computer only has one core." deepsec;
    0, "\n";
    2, Printf.sprintf "%s %s" (coloured_terminal_text Black [Bold] "-l, --local_workers") int_value;
    4, Printf.sprintf "Set the number of local workers to %s. Automatically set %s to 'true'." int_value (coloured_terminal_text Black [Bold] "--distributed");
    4, Printf.sprintf "%s distributes the computation amongst the local workers and distant workers." deepsec;
    0, "\n";
    2, Printf.sprintf "%s %s %s %s" (coloured_terminal_text Black [Bold] "-d, --distant_workers") host_value path_value value;
    4, Printf.sprintf "Allow the computation to be also distributed on the distant machine %s." host_value;
    4, Printf.sprintf "%s must be the path on %s to the directory that contains the %s executable." path_value host_value deepsec;
    4, Printf.sprintf "The value %s represents the number of workers used on the distant machine. %s must" value value;
    4, Printf.sprintf "be either 'auto' or an integer. With 'auto', %s will set the number of workers" deepsec;
    4, Printf.sprintf "as the number of physical cores on the distant machine. When %s is an integer," value;
    4, Printf.sprintf "the number of workers on the distant machine will be set to %s." value;
    4, Printf.sprintf "Note: It is possible to rely on multiple distant machine by using several instances";
    4, Printf.sprintf "of %s. Automatically set %s to 'true'." (coloured_terminal_text Black [Bold] "--distant_workers") (coloured_terminal_text Black [Bold] "--distributed");
    0, "\n";
    2, Printf.sprintf "%s %s" (coloured_terminal_text Black [Bold] "-j, --jobs") int_value;
    4, Printf.sprintf "Set the number of jobs to %s. Automatically set %s to 'true'." int_value (coloured_terminal_text Black [Bold] "--distributed");
    4, Printf.sprintf "%s generates at least %s jobs before distributing them amongts the workers." deepsec int_value;
    4, Printf.sprintf "The default number of jobs is computed as 100 times the total number of workers.";
    0, "\n";
    2, Printf.sprintf "%s %s (default=120)" (coloured_terminal_text Black [Bold] "-r, --round_timer") int_value;
    4, Printf.sprintf "As the computation load for each job may vary greatly, it may happen that some workers";
    4, Printf.sprintf "become ilde. When such case occurs, %s starts a countdown of %s seconds. If the" deepsec int_value;
    4, Printf.sprintf "computation did not complete before the end of the countdown, %s generates a new" deepsec;
    4, Printf.sprintf "set of jobs based on the remaining jobs and redistributes them amongst the workers.";
    4, Printf.sprintf "This redistribution of jobs signals the start of a new round of computation.";
    4, Printf.sprintf "Automatically set %s to 'true'." (coloured_terminal_text Black [Bold] "--distributed");
  ]

(* Command treatment *)

let all_options = ref []
let all_files = ref ([]:string list)

let show_help () =
  print_string header;
  print_string "\n";
  print_string help;
  exit 0

let error_with_distributed_auto op_str options =
  if List.exists (function Distributed None -> true | _ -> false) options
  then raise (Arg.Bad (
      Printf.sprintf "%s The option %s is incompatible with the option %s. Either use %s or remove the option %s"
        (coloured_terminal_text Red [Bold] "Error:")
        (coloured_terminal_text Black [Bold] op_str)
        (coloured_terminal_text Black [Bold] "--distributed auto")
        (coloured_terminal_text Black [Bold] "--distributed true")
        (coloured_terminal_text Black [Bold] "--distributed auto")
    ));
  if List.exists (function Distributed (Some false) -> true | _ -> false) options
  then raise (Arg.Bad (
      Printf.sprintf "%s The option %s is incompatible with the option %s. Either use %s or remove the option %s"
        (coloured_terminal_text Red [Bold] "Error:")
        (coloured_terminal_text Black [Bold] op_str)
        (coloured_terminal_text Black [Bold] "--distributed false")
        (coloured_terminal_text Black [Bold] "--distributed true")
        (coloured_terminal_text Black [Bold] "--distributed false")
    ))

let add_and_verify_option = function
  | Nb_jobs n ->
      error_with_distributed_auto "--jobs" !all_options;
      all_options := (Nb_jobs n):: !all_options
  | Local_workers n ->
      error_with_distributed_auto "--local_workers" !all_options;
      all_options := (Local_workers n):: !all_options
  | Round_timer n ->
      error_with_distributed_auto "--round_timer" !all_options;
      all_options := (Round_timer n):: !all_options
  | Distant_workers [dist] ->
      error_with_distributed_auto "--distant_workers" !all_options;
      let rec explore = function
        | [] -> [Distant_workers [dist]]
        | (Distant_workers dist_l)::q -> (Distant_workers (dist::dist_l))::q
        | t::q -> t::(explore q)
      in
      all_options := explore !all_options
  | Quiet ->
      if List.exists (function ShowTrace -> true | _ -> false) !all_options
      then raise (Arg.Bad (
          Printf.sprintf "%s The option %s is incompatible with the option %s."
            (coloured_terminal_text Red [Bold] "Error:")
            (coloured_terminal_text Black [Bold] "--quiet")
            (coloured_terminal_text Black [Bold] "--trace")
        ));
      all_options := Quiet :: !all_options
  | ShowTrace ->
      if List.exists (function Quiet -> true | _ -> false) !all_options
      then raise (Arg.Bad (
          Printf.sprintf "%s The option %s is incompatible with the option %s."
            (coloured_terminal_text Red [Bold] "Error:")
            (coloured_terminal_text Black [Bold] "--quiet")
            (coloured_terminal_text Black [Bold] "--trace")
        ));
      all_options := ShowTrace :: !all_options
  | Distributed None ->
      List.iter (function
        | Nb_jobs _ -> error_with_distributed_auto "--jobs" [Distributed None]
        | Local_workers _ -> error_with_distributed_auto "--local_workers" [Distributed None]
        | Round_timer _ -> error_with_distributed_auto "--round_timer" [Distributed None]
        | Distant_workers _ -> error_with_distributed_auto "--distant_workers" [Distributed None]
        | _ -> ()
      ) !all_options;
      all_options := (Distributed None) :: !all_options
  | Distributed (Some false) ->
      List.iter (function
        | Nb_jobs _ -> error_with_distributed_auto "--jobs" [Distributed (Some false)]
        | Local_workers _ -> error_with_distributed_auto "--local_workers" [Distributed (Some false)]
        | Round_timer _ -> error_with_distributed_auto "--round_timer" [Distributed (Some false)]
        | Distant_workers _ -> error_with_distributed_auto "--distant_workers" [Distributed(Some false)]
        | _ -> ()
      ) !all_options;
      all_options := (Distributed (Some false)) :: !all_options
  | op -> all_options := op :: !all_options

let complete_options () =
  if not (List.exists (function Distributed _ -> true | _ -> false) !all_options) &&  List.exists (function Nb_jobs _ | Round_timer _ | Distant_workers _ | Local_workers _ -> true | _ -> false) !all_options
  then all_options := Distributed (Some true) :: !all_options

let parse_arg_bool opt = function
  | "true" -> true
  | "false" -> false
  | str ->
      raise (Arg.Bad (Printf.sprintf "%s Wrong argument %s. The option %s expects 'true' or 'false'."
        (coloured_terminal_text Red [Bold] "Error:")
        str
        (coloured_terminal_text Black [Bold] opt)
      ))

let parse_arg_int opt str =
  try
    int_of_string str
  with Failure _ ->
      raise (Arg.Bad (Printf.sprintf "%s Wrong argument %s. The option %s expects an integer."
        (coloured_terminal_text Red [Bold] "Error:")
        str
        (coloured_terminal_text Black [Bold] opt)
      ))

let parse_por op_str str =
  let b = parse_arg_bool op_str str in
  add_and_verify_option (POR b)

let parse_sem op_str = function
  | "private" -> add_and_verify_option (Default_semantics Private)
  | "classic" -> add_and_verify_option (Default_semantics Classic)
  | "eavesdrop" -> add_and_verify_option (Default_semantics Eavesdrop)
  | str ->
      raise (Arg.Bad (Printf.sprintf "%s Wrong argument %s. The option %s expects 'private', 'classic' or 'eavesdrop'."
        (coloured_terminal_text Red [Bold] "Error:")
        str
        (coloured_terminal_text Black [Bold] op_str)
      ))

let parse_nb_jobs op_str = function
  | "auto" -> add_and_verify_option (Nb_jobs None)
  | str ->
      try
        let i = int_of_string str in
        if i <= 0 then raise (Failure "");
        add_and_verify_option (Nb_jobs (Some i))
      with Failure _ ->
          raise (Arg.Bad (Printf.sprintf "%s Wrong argument %s. The option %s expects 'auto' or an integer strictly greater than 0."
            (coloured_terminal_text Red [Bold] "Error:")
            str
            (coloured_terminal_text Black [Bold] op_str)
          ))

let parse_round_timer op_str str =
  let i = parse_arg_int op_str str in
  add_and_verify_option (Round_timer i)

let parse_local_workers op_str = function
  | "auto" -> add_and_verify_option (Local_workers None)
  | str ->
      try
        let i = int_of_string str in
        if i <= 0 then raise (Failure "");
        add_and_verify_option (Local_workers (Some i))
      with Failure _ ->
        raise (Arg.Bad (Printf.sprintf "%s Wrong argument %s. The option %s expects 'auto' or an integer strictly greater than 0."
          (coloured_terminal_text Red [Bold] "Error:")
          str
          (coloured_terminal_text Black [Bold] op_str)
        ))

let parse_distributed op_str = function
  | "auto" -> add_and_verify_option (Distributed None)
  | "true" -> add_and_verify_option (Distributed (Some true))
  | "false" -> add_and_verify_option (Distributed (Some false))
  | str ->
      raise (Arg.Bad (Printf.sprintf "%s Wrong argument %s. The option %s expects 'auto', 'true' or 'false'."
        (coloured_terminal_text Red [Bold] "Error:")
        str
        (coloured_terminal_text Black [Bold] op_str)
      ))

let parse_distant_workers op_str host path = function
  | "auto" -> add_and_verify_option (Distant_workers [host,path, None])
  | str ->
      let i =
        try
          let i' = int_of_string str in
          if i' <= 0
          then raise (Failure "");
          i'
        with Failure _ ->
          raise (Arg.Bad (Printf.sprintf "%s Wrong argument %s. The option %s expects 'auto' or an integer strictly greater than 0."
            (coloured_terminal_text Red [Bold] "Error:")
            str
            (coloured_terminal_text Black [Bold] op_str)
          ))
      in
      add_and_verify_option (Distant_workers [host,path, Some i])

(*let _ =
  Config.running_api := false;

  (* Initialisation of random generator *)
  Random.init (int_of_float (Unix.time ()));

  (* Retrieve deepsec path *)
  let exe_path = Filename.dirname Sys.executable_name in
  Config.path_deepsec := exe_path;
  let database_path = Filename.concat exe_path "database" in
  Config.path_database := database_path;

  (* Retrieve the command *)

  let dist_host = ref "" in
  let dist_path = ref "" in

  let speclist = [
    "--semantics",Arg.String(parse_sem "--semantics"), "";
    "-s",Arg.String(parse_sem "-s"), "";
    "--por", Arg.String(parse_por "--por"), "";
    "-p", Arg.String(parse_por "-p"), "";
    "--quiet", Arg.Unit(fun () -> add_and_verify_option Quiet), "";
    "-q", Arg.Unit(fun () -> add_and_verify_option Quiet), "";
    "--trace", Arg.Unit(fun () -> add_and_verify_option ShowTrace), "";
    "-t", Arg.Unit(fun () -> add_and_verify_option ShowTrace), "";

    "--distributed",Arg.String(parse_distributed "--distributed"), "";
    "-d",Arg.String(parse_distributed "-d"), "";
    "--local_workers",Arg.String(parse_local_workers "--local_workers"), "";
    "-l",Arg.String(parse_local_workers "-l"), "";
    "--distant_workers", Arg.Tuple [Arg.Set_string(dist_host); Arg.Set_string(dist_path); Arg.String(parse_distant_workers "--distant_workers" !dist_host !dist_path)], "";
    "-d", Arg.Tuple [Arg.Set_string(dist_host); Arg.Set_string(dist_path); Arg.String(parse_distant_workers "--d" !dist_host !dist_path)], "";
    "--jobs",Arg.String(parse_nb_jobs "--jobs"), "";
    "-j",Arg.String(parse_nb_jobs "-j"), "";
    "--round_timer",Arg.String(parse_round_timer "--round_timer"), "";
    "-r",Arg.String(parse_round_timer "-r"), "";

    "-h", Arg.Unit show_help, "";
    "-help", Arg.Unit show_help, "";
    "--help", Arg.Unit show_help, ""
  ]
  in

  if Array.length Sys.argv = 1
  then
    begin
      print_string header;
      print_string "\n";
      print_string help;
      exit 0
    end
  else
    begin
      (* Parse the command line *)
      Arg.parse (Arg.align speclist) (fun file -> all_files := !all_files @ [file]) (Printf.sprintf "Use %s to display help." (coloured_terminal_text Black [Bold] "deepsec --help"));

      print_string header;
      print_string "\n";

      complete_options ();
      Execution_manager.set_up_batch_options !all_options;

      Sys.set_signal Sys.sigint (Sys.Signal_handle (fun _ -> Execution_manager.cancel_batch ()));

      (* Generate database if not existent *)
      if not (Sys.file_exists !Config.path_database)
      then Unix.mkdir !Config.path_database 0o770;

      (* Batch started *)
      Execution_manager.start_batch !all_files !all_options;

      Execution_manager.catch_batch_internal_error (fun () ->
        Execution_manager.execute_batch ()
      )
    end
*)

exception User_interrupt

let compute() =
  try
    let x = ref 1 in
    while true do
      x := !x * 1 + 2
    done;
    assert false
  with
    | User_interrupt ->
	print_string "Thread interrupted!\n"
;;

let main() =
  (* Install the signal handler: *)
  print_string "Thread interrupted!\n";
  print_string "Thread interrupted!\n";
  (* Fire up the compute thread: *)
  ignore (Thread.create (fun () -> ignore (Thread.create compute ()); Printf.printf "End of sub thread\n") ());
  print_string "Press Return: 2\n";
  (* Wait for user: *)
  print_string "Press Return:\n";
  let t = read_line () in
  Printf.printf "%s\n" t;
  Printf.printf "Signal was sent\n";
  Printf.printf "Signal was sent\n";
  (* Wait until the thread terminates: *)
  Printf.printf "End of thread\n"
;;

main();;
