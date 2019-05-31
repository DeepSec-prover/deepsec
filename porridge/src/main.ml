
open Examples

(** Command line options *)
module Arg = struct

  (** Selected test *)
  let keys = ref []

  let succ = ref false
  let self = ref true
  let equivalence = ref false
  let persistent = ref false
  let sleep = ref false
  let size = ref false
  let traces = ref (-1)
  let states = ref false
  let executions = ref false
  let bench = ref false
  let compare = ref false
  let display_proc = ref false

  let options = [
    "--succ", Arg.Set succ, "select successor states" ;
    "--no-self", Arg.Clear self, "do not select initial state" ;
    "--persistent", Arg.Set persistent,
      "select persistent LTS and compute persistent sets for selected sets" ;
    "--sleep", Arg.Set sleep, "select sleep LTS" ;
    "--equivalence", Arg.Set equivalence,
      "force selection of trace equiv. LTS when reduced systems are selected" ;
    "--size", Arg.Set size, "compute LTS size in selected LTSs" ;
    "--states", Arg.Set states, "include nb of states in LTS size" ;
    "--executions", Arg.Set executions, "include nb of executions in LTS size" ;
    "--traces", Arg.Unit (fun () -> traces := max_int),
      "show maximal traces in selected LTSs" ;
    "--traces-up-to", Arg.Int (fun i -> traces := i),
      "show traces of length <n> in selected LTSs" ;
    "--no-rm-condi", Arg.Unit (fun () -> Trace_equiv.remove_conditionals := false),
    "disable an optmizatiom that remove some conditionals (which preserves reduced sets of traces)" ;
    "--bench", Arg.Set bench,
    "compute a reduced set of symbolic traces";
    "--compare", Arg.Set compare,
    "compare reduced symbolic traces for two examples";
    "--profiling",
    Arg.Unit (fun () ->
                Memo.display_stats_flag:=true; Utils.call_stats:=true),
    "display statistics on memoization and number of calls";
    "--statistics", Arg.Set POR.persistent_stats,
    "display statistics on POR computations";
    "--proc", Arg.Set display_proc,
    "display initial state given as input"
  ]

  let usage () =
    Format.asprintf
      "Usage: test [options] <example>\n\n\
       List of available examples:\n\
       %a\n\
       List of available options:"
      (fun ch h ->
         let l = Hashtbl.fold (fun k v l -> (k,v)::l) h [] in
         let l = List.sort (fun (x,_) (y,_) -> Pervasives.compare x y) l in
           List.iter
             (fun (k,(title,_)) ->
                Format.fprintf ch "  %15s : %s\n" k title)
             l)
      h

  let run () =
    Arg.parse options (fun s -> keys := s :: !keys) (usage ()) ;
    if !traces >= 0 then size := true ;
    if !states then size := true ;
    equivalence := !equivalence || not (!sleep || !persistent) ;
    if !keys = [] then begin
      Arg.usage options (usage ()) ;
      exit 1
    end ;
      try
        List.rev_map
          (fun key -> Hashtbl.find h key)
          !keys
      with Not_found -> Format.printf "Invalid example name.@." ; exit 1

end

(** Main function *)

open Sem_utils
open Frame

module POR = POR.Make(Trace_equiv)
module Persistent = POR.Persistent
module Sleep = POR.Sleep

let main s =

  let module S = Trace_equiv in

  let persistent s =
    let t0 = Unix.gettimeofday () in
    let set = POR.persistent s in
      set,
      Unix.gettimeofday () -. t0
  in

  (* Some transitions and persistent set computations *)
  if !Arg.display_proc then Format.printf "@[<2>s =@ %a@]@.@." S.State.pp s ;
  if !Arg.succ then
  S.fold_successors s ()
    (fun a s' () ->
         Format.printf
           "@[<2>s -%a->@ s'=%a@]@."
           S.Action.pp a
           S.State.pp s' ;
         if !Arg.persistent then
           let p,d = persistent s' in
             Format.printf
               "P(s') = %a (%.2fs)@.@."
               S.ActionSet.pp p d) ;
  if !Arg.self && !Arg.persistent then
    let p,d = persistent s in
      Format.printf
        "P(s) = %a (%.2fs)@."
        S.ActionSet.pp p d ;

  (* Number of states and traces in successive transition systems *)

  Format.printf "@." ;

  if !Arg.size then begin

    if !Arg.equivalence then begin
    let module Stats = LTS.Make(Trace_equiv) in
    Format.printf "Equivalence LTS: %s%s%d traces.\n"
      (if !Arg.states then
         Printf.sprintf "%d states, "
           (Trace_equiv.StateSet.cardinal (Stats.reachable_states s))
       else "")
      (if !Arg.executions then
         Printf.sprintf "%d executions, "
           (Stats.nb_traces s)
       else "")
      (Stats.count_traces (Stats.traces s)) ;
    if !Arg.traces >=0 then begin
      Format.printf "@.Traces:@." ;
      Stats.show_traces ~bound:!Arg.traces s
    end
    end ;

    if !Arg.persistent then begin
    let module Stats = LTS.Make(Persistent) in
    Format.printf "Persistent: %s%s%d traces.\n"
      (if !Arg.states then
         Printf.sprintf "%d states, "
           (Persistent.StateSet.cardinal (Stats.reachable_states s))
       else "")
      (if !Arg.executions then
         Printf.sprintf "%d executions, "
           (Stats.nb_traces s)
       else "")
      (Stats.count_traces (Stats.traces s)) ;
    if !Arg.traces >= 0 then begin
      Format.printf "@.Traces:@." ;
      Stats.show_traces ~bound:!Arg.traces s
    end
    end ;

    if !Arg.sleep then begin
    let module Stats = LTS.Make(Sleep) in
    let s = s,S.Z.empty in
      Format.printf "Sleep: %s%s%d traces.\n"
        (if !Arg.states then
           Printf.sprintf "%d states, "
             (Sleep.StateSet.cardinal (Stats.reachable_states s))
         else "")
        (if !Arg.executions then
           Printf.sprintf "%d executions, "
             (Stats.nb_traces s)
         else "")
        (Stats.count_traces (Stats.traces s)) ;
      if !Arg.traces >= 0 then begin
        Format.printf "@.Traces:@." ;
        Stats.show_traces ~bound:!Arg.traces s
      end
    end

  end ;

  Format.printf "@."

let compare s t =
  let module R = LTS.Make(Sleep) in
  let s = R.traces (s,Trace_equiv.Z.empty) in
  let t = R.traces (t,Trace_equiv.Z.empty) in
  let rec aux trace (R.Traces s) (R.Traces t) =
    if List.map fst s = List.map fst t then
      List.iter2 (fun (a,s') (_,t') -> aux (a::trace) s' t') s t
    else
      let rec pp sep ch = function
        | [] -> ()
        | [hd] ->
            Trace_equiv.ZAction.pp ch hd
        | hd::tl ->
            pp sep ch tl ;
            Format.pp_print_char ch sep ;
            Trace_equiv.ZAction.pp ch hd
      in
        Format.printf "@[<2>Difference after %a:@ %a !=@ %a@]@."
          (pp '.') trace
          (pp '+') (List.map fst s)
          (pp '+') (List.map fst t)
  in aux [] s t

open Sys
exception Break
let break i = raise Break

let main l =
  if !Arg.compare then
    match l with
    | [_,s;_,t] -> compare (s ()) (t ())
    | _ -> Format.eprintf "Two arguments needed for compare!@." ; exit 1
  else if !Arg.bench then
    List.iter
      (fun (t,s) ->
        try begin
            let s = s () in
            Format.printf "*** %s ***@.@." t ;
            let module R = LTS.Make(Sleep) in
            if !Arg.display_proc then Format.printf "@[<2>s =@ %a@]@.@." Trace_equiv.State.pp s ;
            set_signal sigint (Signal_handle break);
            let t0 = Unix.gettimeofday () in
            ignore (R.traces (s,Trace_equiv.Z.empty)) ;
            Format.printf "%.2fs@." (Unix.gettimeofday () -. t0) ;
          end with Break -> begin
            Format.printf "User interrupted computation ....\n" ;
            Utils.display_stats () ;
            Utils.reset_stats () ;
          end) l
  else
    List.iter
      (fun (t,s) ->
        Format.printf "\n*** %s ***@.@." t ;
        main (s ()) ;
        Format.printf "\n")
      l

(** ... *)

let () = main (Arg.run ())
