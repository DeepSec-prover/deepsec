(* Benchmarking utilities *)
let call_stats = ref false
let recorded_funcs = ref []

type count = int ref

let record_func func_name =
  if not(List.mem_assoc func_name !recorded_funcs)
  then let nb_calls = ref 0 in
       recorded_funcs := (func_name, nb_calls) :: !recorded_funcs;
       nb_calls
  else List.assoc func_name !recorded_funcs

let add_call c = if !call_stats then incr(c)

let reset_stats () = Memo.reset_stats () ; recorded_funcs := []

let display_stats () =
  if !call_stats then begin
    Format.fprintf Format.err_formatter
      "**** Stats on numbers of calls (from Utils):\n" ;
    let l = List.sort (fun (_,x) (_,y) -> compare y x) !recorded_funcs in
    List.iter
      (fun (func_name, nb_calls) ->
         Format.fprintf Format.err_formatter
           "%9d %s\n"
           !nb_calls func_name)
      l ;
    Memo.display_stats () ;
  end

let () = at_exit(display_stats)
