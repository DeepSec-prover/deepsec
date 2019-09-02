(** Main types on terms and recipes *)

(** The type [quantifier] is associated to a variable to quantify it. {% In~\paper, the variables are quantified
    within our first order logic built over atomic formulas such as deduction facts (see~\citepaper{Section}{subsec:first_order_logic}). %}
    In particular, through all the algorithm, we have either free variables or universal variables. In our implementation,
    we will partionate this set of free variables into two sets : [Free] and [Existential]. The variables that are from
    the input processes will be considered as part of [Free] and any other added variables during the algorithm will
    be considered as part of [Existential]. *)
type quantifier =
  | Free
  | Existential
  | Universal

(** The type [name] corresponds to the set {% $\Npriv$ in~\paper. %}
    The names are always considered private. *)
type name =
  {
    label_n : string;
    index_n : int;
    mutable link_n : link_n;
    mutable deducible_n : recipe option (* Indicate whether the name is deducible *)
  }

and link_n =
  | NNoLink (* No link attached to this variable *)
  | NLink of name (* For renaming only *)
  | NSLink (* When searching on names *)

(** The type [representation] indicates how the symbol was defined. *)
and representation =
  | AttackerPublicName
  | UserName
      (** Was originally a public name that has been transform into a
        public constant. *)
  | UserDefined (** User defined in the input file *)

and symbol_cat =
  | Tuple
  | Constructor
  | Destructor of (term list *  term) list

and symbol =
  {
    label_s : string;
    index_s : int;
    arity : int;
    cat : symbol_cat;
    public: bool;
    represents : representation
  }

and link =
  | NoLink
  | TLink of term (* Used for unification and substitution *)
  | VLink of variable (* Used for renaming *)
  | SLink (* Used for searching *)
  | XLink of recipe_variable
      (* Used during constraint solving to find deducible constraints with
         the same variable of right hand term. *)

and variable =
  {
    label : string; (* Default label given in the input file *)
    index : int; (* Unique index per variable *)
    mutable link : link;
    quantifier : quantifier
  }

and term =
  | Func of symbol * term list
  | Var of variable
  | Name of name

and recipe_variable =
  {
    index_r : int;
    mutable link_r : recipe_link;
    quantifier_r : quantifier;
    type_r : int
  }

and recipe_link =
  | RNoLink
  | RLink of recipe (* Used for unification and substitution *)
  | RVLink of recipe_variable (* Used for renaming *)
  | RSLink (* Used for searching *)

and recipe =
  | CRFunc of int * recipe
  | RFunc of symbol * recipe list
  | RVar of recipe_variable
  | Axiom of int
