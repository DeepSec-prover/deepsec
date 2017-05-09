exception Internal_error of string

let debug_activated = true

let internal_error msg =
  Printf.printf "Internal error : %s\nPlease report the bug to vincent.cheval@loria.fr with the input file and output\n" msg;
  raise (Internal_error msg)

let debug =
  if debug_activated
  then fun f -> f ()
  else fun _ -> ()

let test_activated = false

let test =
  if test_activated
  then fun f -> f ()
  else fun _ -> ()

(**** Testing *****)

let path_html_template = ref "Source/html_templates/"
let path_index = ref "./"

(**** Trace display ****)

let display_trace = ref true

let distributed = ref false
