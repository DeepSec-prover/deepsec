
(******* Help ******)

let print_help () =
  Printf.printf "Name : DeepSec\n";
  Printf.printf "   DEciding Equivalence Properties for SECurity protocols\n\n";
  Printf.printf "Version 1.0alpha\n\n"

(******* Parsing *****)

let parse_file path =

  Printf.printf "Opening file %s\n" path;

  let channel_in = open_in path in
  let lexbuf = Lexing.from_channel channel_in in

  let _ =
    try
      while true do
        Parser_functions.parse_one_declaration (Grammar.main Lexer.token lexbuf)
      done
    with
      | Failure msg -> Printf.printf "%s\n" msg; exit 0
      | End_of_file -> () in

  close_in channel_in

(****** Main ******)

let rec excecute_queries = function
  | [] -> ()
  | (Process.Trace_Equivalence,exproc1,exproc2)::q ->
      let proc1 = Process.of_expansed_process exproc1 in
      let proc2 = Process.of_expansed_process exproc2 in

      begin match Equivalence.trace_equivalence !Process.chosen_semantics proc1 proc2 with
        | Equivalence.Equivalent -> Printf.printf "Equivalent processes\n"
        | Equivalence.Not_Equivalent _ -> Printf.printf "Processes not equivalent\n"
      end;
      excecute_queries q
  | _ -> Config.internal_error "Observational_equivalence not implemented"

let _ =
  let path = ref "" in
  let arret = ref false in
  let i = ref 1 in

  while !i < Array.length Sys.argv && not !arret do
    match (Sys.argv).(!i) with
      | str_path ->
          if !i = Array.length Sys.argv - 1
          then path := str_path
          else arret := true;
          i := !i + 1
  done;

  if Array.length Sys.argv <= 1
  then arret := true;

  if !arret || !path = ""
  then print_help ()
  else
    begin
      Testing_load_verify.load ();
      Testing_functions.update ();

      Term.Symbol.empty_signature ();

      parse_file !path;

      if Config.test_activated
      then
        begin
          try
            excecute_queries !Parser_functions.query_list;
            Testing_functions.publish ();
            Testing_load_verify.publish_index ()
          with
          | _ ->
            Testing_functions.publish ();
            Testing_load_verify.publish_index ()
        end
      else excecute_queries !Parser_functions.query_list
    end;
  exit 0
