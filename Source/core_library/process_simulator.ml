open Term
open Display

(************************
***       Types       ***
*************************)

type position = int

(* TODO : Change the syntax of the bang. It is more natural to have one process
   with an integer as argument. Moreover, I think it will more beautiful to have
   a renaming of name actually happening when we excecute the New. *)
type process =
  | Nil
  | Output of protocol_term * protocol_term * process * position
  | Input of protocol_term * fst_ord_variable * process * position
  | IfThenElse of protocol_term * protocol_term * process * process * position
  | Let of protocol_term * protocol_term * process * process * position
  | New of name * process * position
  | Choice of process * process * position
      (** We consider the binary operator choice instead of a process list due
         to the observational equivalence. *)
  | Par of process list
  | Bang of process list * position

type transition =
  | TrComm of position (* Output *) * position (* Input *)
  | TrEaves of recipe (* Channel *) * position (* Output *) * position (* Input *)
  | TrInput of recipe (* Channel *) * recipe (* Term *) * position
  | TrOutput of recipe (* Channel *) * position
  | TrChoice of position * bool (* [true] when the left process is chosen, [false] otherwise. *)
  | TrSilent of position (* Includes IfThenElse, Let and New *)

type trace = transition list (* The first element of the list is the last transition of the trace. *)

let display_term = display Terminal Protocol

let display_recipe = display Terminal Recipe

let rec display = function
  | Nil -> print_string "0\n"
  | Output(ch,t,p,pos) ->
      Printf.printf "{%d} out(%s,%s);\n" pos (display_term ch) (display_term t);
      display p
  | Input(ch,x,p,pos) ->
      Printf.printf "{%d} in(%s,%s);\n" pos (display_term ch) (display_term (of_variable x));
      display p
  | IfThenElse(t1,t2,p_then,p_else,pos) ->
      Printf.printf "{%d} if %s = %s\n" pos (display_term t1) (display_term t2);
      Printf.printf "then\n";
      display p_then;
      Printf.printf "else\n";
      display p_else
  | Let(t1,t2,p_then,p_else,pos) ->
      Printf.printf "{%d} let %s = %s in\n" pos (display_term t1) (display_term t2);
      display p_then;
      Printf.printf "else\n";
      display p_else
  | New(n,p,pos) ->
      Printf.printf "{%d} new %s;\n" pos (display_term (of_name n));
      display p
  | Par p_list ->
      Printf.printf "PAR [\n";
      List.iter (fun p -> display p; print_string "|\n") p_list;
      print_string "]\n";
  | Bang(p_list,pos) ->
      Printf.printf "{%d} Bang [\n" pos;
      List.iter (fun p -> display p; print_string "|\n") p_list;
      print_string "]\n";
  | _ -> ()

let display_trace ?(no_silent=false) trace =
  let rec explore = function
    | [] -> ()
    | (TrComm(pos_out,pos_in))::q ->
        explore q;
        Printf.printf "TrComm(%d,%d)\n" pos_out pos_in
    | (TrInput(r_ch,r_t,pos))::q ->
        explore q;
        Printf.printf "TrInput(%s,%s,%d)\n" (display_recipe r_ch) (display_recipe r_t) pos
    | (TrOutput(r_ch,pos))::q ->
        explore q;
        Printf.printf "TrOutput(%s,%d)\n" (display_recipe r_ch) pos
    | (TrSilent pos)::q ->
        explore q;
        if not no_silent then Printf.printf "TrSilent(%d)\n" pos
    | _ -> ()
  in
  explore trace
