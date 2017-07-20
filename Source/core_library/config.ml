exception Internal_error of string

let debug_activated = false

let internal_error msg =
  Printf.printf "Internal error : %s\nPlease report the bug to vincent.cheval@loria.fr with the input file and output\n" msg;
  raise (Internal_error msg)

let debug =
  if debug_activated
  then fun f -> f ()
  else fun _ -> ()

(**** Testing *****)

let test_activated = false

let test =
  if test_activated
  then fun f -> f ()
  else fun _ -> ()

(**** Version ****)

let version = ref "1.0alpha"
let git_commit = ref "b3bce7210f8c27f785d6da27ba964d7a2e71e206"
    
(**** Paths ****)

let path_deepsec = ref ""
let path_html_template = ref ""
let path_index = ref (Filename.current_dir_name)
let tmp_file = ref ""

(**** Trace display ****)

let display_trace = ref true

let distributed = ref false
