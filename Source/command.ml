(* Utilitaries for shell management *)

(* Reads lines from an input channel *)
let readlines_ch_map ch f =
  let rec fold accu =
    match try Some (input_line ch) with End_of_file -> None with
    | None -> let () = close_in ch in List.rev accu
    | Some l -> if l = "" then fold accu else fold (f l :: accu) in
  fold []

let readlines_ch ch = readlines_ch_map ch (fun x -> x)

(* runs a command and returns the list of the output lines *)
let run c =
  let (i,o,e) = Unix.open_process_full c [||] in
  let output = readlines_ch i in
  let _ = Unix.close_process_full (i,o,e) in output
