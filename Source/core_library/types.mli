(**************************************************************************)
(*                                                                        *)
(*                               DeepSec                                  *)
(*                                                                        *)
(*               Vincent Cheval, project PESTO, INRIA Nancy               *)
(*                Steve Kremer, project PESTO, INRIA Nancy                *)
(*            Itsaka Rakotonirina, project PESTO, INRIA Nancy             *)
(*                                                                        *)
(*   Copyright (C) INRIA 2017-2020                                        *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU General Public License version 3.0 as described in the       *)
(*   file LICENSE                                                         *)
(*                                                                        *)
(**************************************************************************)

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
    pure_fresh_n : bool;
    mutable link_n : link_n
  }

and link_n =
  | NNoLink (* No link attached to this variable *)
  | NLink of name (* For renaming only *)
  | NSLink (* When searching on names *)

(** The type [representation] indicates how the symbol was defined. *)
and representation =
  | AttackerPublicName of int
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
  | RXLink of term (* Used for applying mgs *)
  | RSLink (* Used for searching *)
  | RRLink of int (* Type restriction *)

and recipe =
  | CRFunc of int * recipe
  | RFunc of symbol * recipe list
  | RVar of recipe_variable
  | Axiom of int


(**** Processes ****)

type position = int * int list

type pattern =
  | PatVar of variable
  | PatEquality of term
  | PatTuple of symbol * pattern list

type process =
  | Nil
  | Output of term * term * process * position
  | Input of term * pattern * process * position
  | IfThenElse of term * term * process * process * position
  | Let of pattern * term * process * process * position
  | New of name * process * position
  | Par of process list
  | Bang of process list * position
  | Choice of process * process * position

type semantics =
  | Classic
  | Private
  | Eavesdrop

type equivalence =
  | Trace_Equivalence
  | Trace_Inclusion
  | Session_Equivalence
  | Session_Inclusion

type transition =
  | AOutput of recipe * position
  | AInput of recipe * recipe * position
  | AEaves of recipe * position (* out *) * position (* in *)
  | AComm of position (* out *) * position (* in *)
  | ABang of int * position
  | ATau of position
  | AChoice of position * bool (* True when the left process is chosen *)

type verification_result =
  | RTrace_Equivalence of (bool * transition list) option
  | RTrace_Inclusion of transition list option
  | RSession_Equivalence of (bool * transition list) option
  | RSession_Inclusion of transition list option
