type output =
  | Testing
  | Terminal
  | Pretty_Terminal
  | HTML
  | Latex

let rec display_list display_element connector = function
  | [] -> ""
  | [t] -> display_element t
  | t::q -> Printf.sprintf "%s%s%s" (display_element  t) connector (display_list display_element connector q)

let display_list_i display_element connector = function
  | [] -> ""
  | [t] -> display_element 1 t
  | t::q ->
      let str = ref (display_element 1 t) in
      List.iteri (fun i t ->
        str := Printf.sprintf "%s%s%s" !str connector (display_element (i+2) t);
      ) q;
      !str


let rec internal_create_tab = function
  | 0 -> ""
  | k -> "  "^(internal_create_tab (k-1))

let create_tab k =
  Config.debug (fun () ->
    if k < 0
    then Config.internal_error "[display.ml >> create_tab] The number of tabs cannot be negative."
  );
  internal_create_tab k


let mkRuntime f =
  let rt = int_of_float f in
  let hours = rt / 3600 in
  let rem = rt mod 3600 in
  let mins = rem / 60 in
  let secs = rem mod 60 in

  let h = ( if hours>0 then ((string_of_int hours)^"h") else "") in
  let m = ( if mins>0 then ((string_of_int mins)^"m") else "") in
  let s = ((string_of_int secs)^"s") in
  h^(m^s)


  (* Printf.sprintf "%ih %im %is" hours mins secs *)

let mkDate t =
  let weekday d =
    match d with
    | 0 -> "Sun"
    | 1 -> "Mon"
    | 2 -> "Tue"
    | 3 -> "Wed"
    | 4 -> "Thu"
    | 5 -> "Fri"
    | 6 -> "Sat"
    | _ -> Config.internal_error "[display.ml >> mkDate] Weekday must be in [0..6]."
  in
  let month m =
    match m with
    | 0 -> "Jan"
    | 1 -> "Feb"
    | 2 -> "Mar"
    | 3 -> "Apr"
    | 4 -> "May"
    | 5 -> "Jun"
    | 6 -> "Jul"
    | 7 -> "Aug"
    | 8 -> "Sep"
    | 9 -> "Oct"
    |10 -> "Nov"
    |11 -> "Dec"
    | _ -> Config.internal_error "[display.ml >> mkDate] Month must be in [0..11]."
  in
  let d = Printf.sprintf "%s, %s %i %i at %i:%i:%i"
    (weekday t.Unix.tm_wday) (month t.Unix.tm_mon) t.Unix.tm_mday (1900 + t.Unix.tm_year)
    t.Unix.tm_hour t.Unix.tm_min t.Unix.tm_sec in
  d


(**** Special character ****)

let neqi = function
  | Terminal | Testing -> "<>_R"
  | Pretty_Terminal -> "≠𝓡"
  | HTML -> "&#8800;<sub>&#8475;</sub>"
  | Latex -> "\\neq^?_{\\mathcal{R}}"

let eqi = function
  | Terminal | Testing -> "=_R"
  | Pretty_Terminal -> "=𝓡"
  | HTML -> "&#61;<sub>&#8475;</sub>"
  | Latex -> "=^?_{\\mathcal{R}}"

let neqs = function
  | Terminal | Testing -> "<>"
  | Pretty_Terminal -> "≠"
  | HTML -> "&#8800;"
  | Latex -> "\\neq^?"

let eqs = function
  | Terminal | Testing -> "="
  | Pretty_Terminal -> "="
  | HTML -> "&#61;"
  | Latex -> "=^?"

let eqf = function
  | Terminal | Testing -> "=_f"
  | Pretty_Terminal -> "=ᵩ"
  | HTML -> "=<sub>& #936;</sub>"
  | Latex -> "\\mathrel{=_f}"

let bot = function
  | Terminal | Testing -> "bot"
  | Pretty_Terminal -> "⊥"
  | HTML -> "&#8869;"
  | Latex -> "\\bot"

let top = function
  | Terminal | Testing -> "top"
  | Pretty_Terminal -> "⊤"
  | HTML -> "&#8868;"
  | Latex -> "\\top"

let forall = function
  | Terminal | Testing -> "forall"
  | Pretty_Terminal -> "∀"
  | HTML -> "&#8704;"
  | Latex -> "\\forall"

let exists = function
  | Terminal | Testing -> "exists"
  | Pretty_Terminal -> "∃"
  | HTML -> "&#8707;"
  | Latex -> "\\exists"

let vdash = function
  | Terminal | Testing -> "|-"
  | Pretty_Terminal -> "⊢"
  | HTML -> "&#8866;"
  | Latex -> "\\vdash^?"

let vee = function
  | Terminal | Testing -> "\\/"
  | Pretty_Terminal -> "∨"
  | HTML -> "&#8744;"
  | Latex -> "\\vee"

let wedge = function
  | Terminal | Testing -> "/\\"
  | Pretty_Terminal -> "∧"
  | HTML -> "&#8743;"
  | Latex -> "\\wedge"

let lLeftarrow = function
  | Terminal | Testing -> "<="
  | Pretty_Terminal -> "<="
  | HTML -> "&#10232;"
  | Latex -> "\\Leftarrow"

let leftarrow = function
  | Terminal | Testing -> "<-"
  | Pretty_Terminal -> "<-"
  | HTML -> "&#10232;"
  | Latex -> "\\leftarrow"

let rRightarrow = function
  | Terminal | Testing -> "=>"
  | Pretty_Terminal -> "=>"
  | HTML -> "&#8658;"
  | Latex -> "\\Rightarrow"

let rightarrow = function
  | Terminal | Testing -> "->"
  | Pretty_Terminal -> "->"
  | HTML -> "&#8594;"
  | Latex -> "\\rightarrow"

let langle = function
  | Terminal | Testing -> "("
  | Pretty_Terminal -> "⟨"
  | HTML -> "&#10216;"
  | Latex -> "\\langle "

let rangle = function
  | Terminal| Testing  -> ")"
  | Pretty_Terminal -> "⟩"
  | HTML -> "&#10217;"
  | Latex -> " \\rangle"

let lcurlybracket = function
  | Terminal | Testing -> "{"
  | Pretty_Terminal -> "{"
  | HTML -> "&#123;"
  | Latex -> "\\{"

let rcurlybracket = function
  | Terminal | Testing  -> "}"
  | Pretty_Terminal -> "}"
  | HTML -> "&#125;"
  | Latex -> "\\}"

let lbrace = function
  | Terminal | Testing -> "["
  | Pretty_Terminal -> "["
  | HTML -> "["
  | Latex -> "["

let rbrace = function
  | Terminal | Testing -> "]"
  | Pretty_Terminal -> "]"
  | HTML -> "]"
  | Latex -> "]"

let emptyset = function
  | Terminal | Testing -> "{ }"
  | Pretty_Terminal -> "∅"
  | HTML -> "&#8709;"
  | Latex -> "\\emptyset"
