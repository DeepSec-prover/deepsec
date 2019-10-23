type output =
  | Terminal
  | HTML
  | Latex

type colour =
  | Black
  | Red
  | Green
  | Yellow
  | Blue
  | Magenta
  | Cyan
  | White

type decoration =
  | Bold
  | Underline

let colour_to_int = function
  | Black -> 0 | Red     -> 1 | Green -> 2 | Yellow -> 3
  | Blue  -> 4 | Magenta -> 5 | Cyan  -> 6 | White  -> 7


let coloured_terminal_text colour deco text =
  let deco_str =
    List.fold_left (fun acc decoration -> match decoration with
      | Bold -> "\027[1m"^acc
      | Underline -> "\027[4m"^acc
    ) "" deco
  in

  Printf.sprintf "%s\027[3%dm%s\027[0m" deco_str (colour_to_int colour) text

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

let reg_latex_1 = Str.regexp "\\([a-zA-Z0-9_]+\\)_\\([0-9]+\\)"
let reg_latex_2 = Str.regexp "_"

let display_identifier output str = match output with
  | Terminal -> str
  | HTML ->
      if Str.string_match reg_latex_1 str 0
      then
        let body = Str.matched_group 1 str in
        let number = Str.matched_group 2 str in
        Printf.sprintf "%s<sub>%s</sub>" body number
      else str
  | Latex ->
      if Str.string_match reg_latex_1 str 0
      then
        let body = Str.matched_group 1 str in
        let number = Str.matched_group 2 str in
        let body' = Str.global_replace reg_latex_2 "\\_" body in
        Printf.sprintf "%s_{%s}" body' number
      else Str.global_replace reg_latex_2 "\\_" str

(***** Tools *****)

let rec internal_create_tab = function
  | 0 -> ""
  | k -> "  "^(internal_create_tab (k-1))

let create_tab k =
  Config.debug (fun () ->
    if k < 0
    then Config.internal_error "[display.ml >> create_tab] The number of tabs cannot be negative."
  );
  internal_create_tab k


let mkRuntime rt =
  if rt = 0
  then "< 1s"
  else
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
  | Terminal -> "≠𝓡"
  | HTML -> "&#8800;<sup>?</sup><sub>&#8475;</sub>"
  | Latex -> "\\neq^?_{\\mathcal{R}}"

let eqi = function
  | Terminal -> "=𝓡"
  | HTML -> "&#61;<sup>?</sup><sub>&#8475;</sub>"
  | Latex -> "=^?_{\\mathcal{R}}"

let neqs = function
  | Terminal -> "≠"
  | HTML -> "&#8800;<sup>?</sup>"
  | Latex -> "\\neq^?"

let eqs = function
  | Terminal -> "="
  | HTML -> "&#61;<sup>?</sup>"
  | Latex -> "=^?"

let eqf = function
  | Terminal -> "=ᵩ"
  | HTML -> "=<sub>& #936;</sub>"
  | Latex -> "\\mathrel{=_f}"

let bot = function
  | Terminal -> "⊥"
  | HTML -> "&#8869;"
  | Latex -> "\\bot"

let top = function
  | Terminal -> "⊤"
  | HTML -> "&#8868;"
  | Latex -> "\\top"

let forall = function
  | Terminal -> "∀"
  | HTML -> "&#8704;"
  | Latex -> "\\forall"

let exists = function
  | Terminal -> "∃"
  | HTML -> "&#8707;"
  | Latex -> "\\exists"

let vdash = function
  | Terminal -> "⊢"
  | HTML -> "&#8866;<sup>?</sup>"
  | Latex -> "\\vdash^?"

let vee = function
  | Terminal -> "∨"
  | HTML -> "&#8744;"
  | Latex -> "\\vee"

let wedge = function
  | Terminal -> "∧"
  | HTML -> "&#8743;"
  | Latex -> "\\wedge"

let lLeftarrow = function
  | Terminal -> "<="
  | HTML -> "&#10232;"
  | Latex -> "\\Leftarrow"

let leftarrow = function
  | Terminal -> "<-"
  | HTML -> "&#10232;"
  | Latex -> "\\leftarrow"

let rRightarrow = function
  | Terminal -> "=>"
  | HTML -> "&#8658;"
  | Latex -> "\\Rightarrow"

let rightarrow = function
  | Terminal -> "->"
  | HTML -> "&#8594;"
  | Latex -> "\\rightarrow"

let langle = function
  | Terminal -> "⟨"
  | HTML -> "&#10216;"
  | Latex -> "\\langle "

let rangle = function
  | Terminal -> "⟩"
  | HTML -> "&#10217;"
  | Latex -> " \\rangle"

let lcurlybracket = function
  | Terminal -> "{"
  | HTML -> "&#123;"
  | Latex -> "\\{"

let rcurlybracket = function
  | Terminal -> "}"
  | HTML -> "&#125;"
  | Latex -> "\\}"

let lbrace = function
  | Terminal -> "["
  | HTML -> "["
  | Latex -> "["

let rbrace = function
  | Terminal -> "]"
  | HTML -> "]"
  | Latex -> "]"

let emptyset = function
  | Terminal -> "∅"
  | HTML -> "&#8709;"
  | Latex -> "\\emptyset"
