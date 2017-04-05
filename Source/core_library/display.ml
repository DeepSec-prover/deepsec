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
  | Latex -> "=_f"

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
  | Terminal | Testing -> "<"
  | Pretty_Terminal -> "⟨"
  | HTML -> "&#10216;"
  | Latex -> "\\langle"

let rangle = function
  | Terminal| Testing  -> ">"
  | Pretty_Terminal -> "⟩"
  | HTML -> "&#10217;"
  | Latex -> "\\rangle"

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

let llinebracket = function
  | Terminal | Testing -> "["
  | Pretty_Terminal -> "["
  | HTML -> "["
  | Latex -> "["

let rlinebracket = function
  | Terminal | Testing -> "]"
  | Pretty_Terminal -> "]"
  | HTML -> "]"
  | Latex -> "]"

let emptyset = function
  | Terminal | Testing -> "{ }"
  | Pretty_Terminal -> "∅"
  | HTML -> "&#8709;"
  | Latex -> "\\emptyset"
