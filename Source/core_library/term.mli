(** Operations on terms *)

(** {% This module regroups all the functions that manipulate terms. In~\paper, the terms
    are splitted into protocol terms and recipes. %}*)

(** The type [symbol] represents the type of function symbol. It corresponds to the set {% $\F$ in~\paper. %} *)
type symbol

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

(** Represents the type system for first-order variables *)
type fst_ord

(** Represents the type system second-order variables *)
type snd_ord

(** The type [axiom] corresponds to the set {% $\AX$ in~\paper. %} *)
type axiom

(** The type [boundedness] is associated to a name. It specifies whether the name was public or
    bound in the input processes. *)
type boundedness =
  | Public
  | Bound

(** The type [name] corresponds to the set {% $\Npriv$ in~\paper. %} *)
type name

(** The type [atom] represents the fact that we will consider only two kinds of terms, that as protocol terms and recipes. *)
type ('a, 'b) atom =
  | Protocol : (fst_ord, name) atom
  | Recipe : (snd_ord, axiom) atom

(** Generic type for variables *)
type ('a, 'b) variable

(** Generic type for terms *)
type ('a, 'b) term

(** A [fst_ord_variable] is always quantified. {% It corresponds to the set $\Xun$ in~\paper. %} *)
type fst_ord_variable = (fst_ord, name) variable

(** A [snd_ord_variable] is always quantified. They are parametrised by an integer represening
    their type. {% It corresponds to the set $\Xdeux$ in~\paper. %} *)
type snd_ord_variable = (snd_ord, axiom) variable

(** The type [protocol_term] corresponds to the set {% $\T(\F,\N \cup \Xun)$ in~\paper. %} *)
type protocol_term = (fst_ord, name) term

(** The type [recipe] corresponds to the set {% $\T(\F,\Xdeux \cup \Npub \cup \AX)$ in~\paper. %} *)
type recipe = (snd_ord, axiom) term

(** The type [display_renamings] corresponds to three renamings, respectively of names, first-order variables and second-order variables.
    When display renamings are given to display functions, they will display the names and variables according to these renaming. *)
type display_renamings

(** [generate_display_renaming n_l fst_l snd_l] generates display renamings so that names and variables will be displayed with consecutive indices
    starting from 0. This is very useful for pretty printing. *)
val generate_display_renaming : name list -> fst_ord_variable list -> snd_ord_variable list -> display_renamings

(** [generate_display_renaming_for_testing n_l fst_l snd_l] generates display renamings so that names and variables will be displayed with consecutive indices
    starting from 0. Moreover the display renamings satisfy the following conventions:
    {%
    \begin{itemize}
    \item Free first-order (resp. second-order variables) will be denoted by $w$ (resp. $W$)
    \item Existential first-order (resp. second-order variables) will be denoted by $x$ or $y$ (resp. $X$ or $Y$)
    \item Universal first-order (resp. second-order variables) will be denoted by $z$ (resp. $Z$)
    \item Public names will be denoted by $a$ or $b$ or $c$
    \item Bound names will be denoted by $k$ or $l$ or $m$
    \end{itemize}
    %}*)
val generate_display_renaming_for_testing : name list -> fst_ord_variable list -> snd_ord_variable list -> display_renamings

(** {2 Symbols} *)

module Symbol : sig
  (** A symbol can be a destructor or a constructor.*)

  val get_constant : unit -> symbol

  (** The list of all constructors (included the tupple function symbol) used in the algorithm.*)
  val all_constructors : symbol list ref

  (** The number of constructors used in the algorithm. *)
  val number_of_constructors : int ref

  (** The list of all destructors. Does not include the projections of tuples *)
  val all_destructors : symbol list ref

  (** The number of destructors used in the algorithm. *)
  val number_of_destructors : int ref

  (** We consider tuples as a built-in function symbols. It will allows us to do some patter matching
      on tuple that will ease the syntax of processes. *)

  (** The list contains all tuples introduced by the algorithm. *)
  val all_tuple : symbol list ref

  (** Empty the signature from all function symbols (constructor, destructor and tuple) *)
  val empty_signature : unit -> unit

  type setting = { all_t : symbol list ; all_p : (int * symbol list) list ; all_c : symbol list ; all_d : symbol list ; nb_c : int ; nb_d : int ; cst : symbol }

  val set_up_signature : setting -> unit

  val get_settings : unit -> setting

  (** {3 Addition} *)

  (** [new_symbol ar s] creates a constructor function symbol with the name [s] and the arity [ar].
      The resulting symbol is automatically added into [all_constructors].
      Moreover, [number_of_constructors] is increased by 1.
      Note that if the constructor is in fact a tuple, it is better to use [get_tuple].*)
  val new_constructor : int -> string -> symbol

  (** [new_destructor ar s l] creates a destructor function symbol with the name [s] and the arity [ar].
      Furthermore each element of [l] represents the arguments and result of a rewrite rule for the destructor.
      The resulting symbol is automatically added into [all_destructors].
      Moreover, [number_of_destructors] is increased by 1.*)
  val new_destructor : int -> string -> (protocol_term list * protocol_term) list -> symbol

  (** [get_tuple ar] get the function symbol for tuple of arity [ar].
      If such function symbol was not created yet, it creates it and
      the resulting symbol is automatically added into [all_constructors].
      Moreover, [number_of_constructors] is increased by 1.
      At last, the associated projection function symbol are automatically added into [all_projection].*)
  val get_tuple : int -> symbol

  (** [nth_projection f i] returns the projection function symbol of the [i]{^ th} element of tuple function symbol [f].
      Note that for a tuple of arity [n], the range of [i] is [1...n].

      @raise Internal_error if [f] is not a tuple.
      @raise Not_found if [f] was not previously introduced by [get_tuple].*)
  val nth_projection : symbol -> int -> symbol

  (** [get_projections f] returns the list [[f_1;...;f_n]] with [f_i] is the projection
      function symbol of the [i]{^ th} element of the tuple function symbol [f].
      It returns the same result as [[nth_projection f 1; ...; nth_projection f n]].

      @raise Internal_error if [f] is not a tuple.
      @raise Not_found if [f] was not previously introduced by [get_tuple].*)
  val get_projections : symbol -> symbol list


  (** {3 Symbol testing} *)

  (** [is_equal_symbol f1 f2] returns [true] iff [f1] and [f2] are the same function symbol.*)
  val is_equal : symbol -> symbol -> bool

  (** [is_tuple f] returns [true] iff [f] is a tuple. *)
  val is_tuple : symbol -> bool

  (** [is_constructor f] returns true iff [f] is a constructor or a tuple. Note that all tuples are constructors. *)
  val is_constructor : symbol -> bool

  (** [is_destructor f] returns true iff [f] is a destructor. *)
  val is_destructor : symbol -> bool

  (** {3 Symbol Access} *)

  (** [get_arity f] returns the arity of the function symbol [f].*)
  val get_arity : symbol -> int

  (** {3 Display} *)

  val display  : Display.output -> symbol -> string

  val display_with_arity  : Display.output -> symbol -> string

  val display_signature : Display.output -> string
end

(** {2 Variables} *)

module Variable : sig
  (** The variables created by the functions below are structuraly and physically different. In the following function, elemnts of type [('a,'b) atom], usually
      denoted [at] ensures that generated variables can only be first-order or second-order variables. *)

  (** The variables of {% $\Xun$ %} are untyped hence we consider a unique value of type [fst_ord] *)
  val fst_ord_type : fst_ord

  (** The variables of {% $\Xdeux$ %} are typed by an integer. Hence, [snd_ord_type i] corresponds to the type of variables in {% $\Xdeuxi{i}$ %} *)
  val snd_ord_type : int -> snd_ord

  (** [fresh at q ty] creates a fresh variable quantified by [q] with type [ty]. *)
  val fresh : ('a, 'b) atom -> quantifier -> 'a -> ('a, 'b) variable

  (** [fresh_with_label q ty s] creates a fresh variable quantified by [q] with the label [s] and type [ty]. *)
  val fresh_with_label : quantifier -> 'a -> string -> ('a, 'b) variable

  (** [fresh_from_var x] creates a fresh variable
      with the same display identifier and quantifier as the variable [x].*)
  val fresh_from : ('a, 'b) variable -> ('a, 'b) variable

  (** [fresh_list at q ty n] creates a list of [n] fresh variables all quantified as [q] with type [ty].*)
  val fresh_list : ('a, 'b) atom -> quantifier -> 'a -> int -> ('a, 'b) variable list

  (** [is_equal x1 x2] returns [true] iff the variable [x1] and [x2] are equal. *)
  val is_equal : ('a, 'b) variable -> ('a, 'b) variable -> bool

  (** [quantifier_of x] returns the quantification of the variable [x]. *)
  val quantifier_of : ('a, 'b) variable -> quantifier

  (** [type_of] {% $X$ returns the type in which the second-variable $X$ is defined, that is returns$i$ when $X \in \Xdeuxi{i}$. %} *)
  val type_of : snd_ord_variable -> int

  (** A total ordering function over variables. This is a three-argument function [order] such that  [order at x1 x2] is zero if
      the [x1] and [x2] are equal, [order at x1 x2] is strictly negative if [x1] is smaller than [x2], and
      strictly strictly positive if [x1] is greater than [x2]. *)
  val order : ('a, 'b) atom -> ('a, 'b) variable -> ('a, 'b) variable -> int

  (** [display out at x] returns a string displaying the variable [x] depending on the outpout mode [out]. *)
  val display : Display.output -> ?rho: display_renamings option -> ('a, 'b) atom -> ?v_type:bool ->  ('a, 'b) variable -> string

  val set_up_counter : int -> unit

  val get_counter : unit -> int

  (** {3 Renaming} *)

  module Renaming : sig

    (** Variable renaming. *)
    type ('a, 'b) t

    (** Domain of a variable renaming *)
    type ('a, 'b) domain

    (** {4 Generation} *)

    (** Returns the identify renaming. *)
    val identity : ('a, 'b) t

    (** [fresh at v_l q] generate a fresh renaming for the variable in [v_l]. The image of the renaming contains only variables with quantified as [q]. *)
    val fresh : ('a, 'b) atom -> ('a, 'b) variable list -> quantifier -> ('a, 'b) t

    (** [compose] {% $\rho_1$~$\rho_2$ returns the renaming $\rho_1\rho_2$. %} *)
    val compose : ('a, 'b) t -> ('a, 'b) variable -> ('a, 'b) variable -> ('a, 'b) t

    (** Returns the empty domain. *)
    val empty : ('a, 'b) domain

    (** [add d x] adds the variable [x] in the domain [d]. *)
    val add : ('a, 'b) domain -> ('a, 'b) variable -> ('a, 'b) domain

    (** [get_varss_with_list] {% $\rho$ %} [l] adds the variables in {% $\rho$ %} in the list [l]. The addition of a name as the union of sets, i.e. there is no dupplicate in the resulting list..*)
    val get_vars_with_list : ('a, 'b) t -> ('a, 'b) variable list -> ('a, 'b) variable list

    (** {4 Testing} *)

    (** Check whether the renaming is the identity renaming. *)
    val is_identity : ('a, 'b) t -> bool

    (** Checks whether the two renamings are the same. *)
    val is_equal : ('a, 'b) atom -> ('a, 'b) t -> ('a, 'b) t -> bool

    (** [not_in_domain] {% $\rho$~$S$ %} returns {% $S \setminus \Dom{\rho}$ %}.*)
    val not_in_domain : ('a, 'b) t -> ('a, 'b) variable list -> ('a, 'b) variable list

    (** {4 Operators} *)

    (** [intersect_domain] {% $\rho_1$~$\rho_2$ returns $\Dom{\rho_1} \cap \Dom{\rho_2}$. %}*)
    val intersect_domain : ('a, 'b) t -> ('a, 'b) t -> ('a, 'b) domain

    (** Generates a domain from a list of variables. *)
    val of_list : ('a, 'b) variable list -> ('a, 'b) domain

    (** [restict] {% $\rho$~$d$% returns the renaming $\SubRestr{\rho}{x \in \Dom{\rho} \cap d}$. %}*)
    val restrict : ('a, 'b) t -> ('a, 'b) domain -> ('a, 'b) t

    (** [apply] {% $\rho$ %} [elt map_elt] applies the renaming {% $\rho$ %} on the element [elt]. The function
        [map_elt] should map the variables contained in the element [elt] on which {% $\rho$ %} should be applied.

        WARNING: The function [map_elt] should not raise an uncaught exception.*)
    val apply : ('a, 'b) t -> 'c -> ('c -> (('a, 'b) variable -> ('a, 'b) variable) -> 'c) -> 'c

    (** [apply_on_terms] {% $\rho$ %} [elt map_elt] applies the renaming {% $\rho$ %} on the element [elt]. The function
        [map_elt] should map the terms contained in the element [elt] on which {% $\rho$ %} should be applied.

        WARNING: The function [map_elt] should not raise an uncaught exception.*)
    val apply_on_terms : ('a, 'b) t -> 'c -> ('c -> (('a, 'b) term -> ('a, 'b) term) -> 'c) -> 'c

    (** {4 Display} *)

    val display : Display.output -> ?rho:display_renamings option -> ('a, 'b) atom -> ?v_type:bool -> ('a, 'b) t -> string

    val display_domain : Display.output -> ?rho:display_renamings option -> ('a, 'b) atom -> ?v_type:bool -> ('a, 'b) domain -> string
  end

end

(** {3 Axioms} *)

module Axiom : sig
  (** [create i] creates an axiom with index [i]. It corresponds to {% $\ax_i$ in~\paper.%}*)
  val create : int -> axiom

  (** [of_public_names_list] {% $[n_0;\ldots;n_k]$ generates the list of axioms $[\ax_{-k}; \ldots; \ax_0]$ where $\ax_{-i}$ is associated to $n_i$ for all $i$. %} *)
  val of_public_names_list : name list -> axiom list

  (** [of_public_name n k] generates the {% axiom $\ax_k$ and associate it with $n$. %} *)
  val of_public_name : name -> int -> axiom

  (** A total ordering function over axioms. This is a two-argument function [order] such that  [order ax1 ax2] is zero if
      the [ax1] and [ax2] are equal, [order ax1 ax2] is strictly negative if [ax1] is smaller than [ax2], and
      strictly strictly positive if [ax1] is greater than [ax2]. *)
  val order : axiom -> axiom -> int

  (** [name_of ax] returns the public name associated to [ax].
      @raise Internal_error when [ax] is not associated to a public name.*)
  val name_of : axiom -> name

  (** [index_of_axiom ax] returns the index of the axiom [ax]. *)
  val index_of : axiom -> int

  (** [is_equal ax1 ax2] returns [true] iff the axioms [ax1] and [ax2] are equal, i.e. have the same index. *)
  val is_equal : axiom -> axiom -> bool

  (** [display out ax] returns a string displaying the axiom [ax] depending on the outpout mode [out]. *)
  val display : Display.output -> ?rho:display_renamings option -> ?both:bool -> axiom -> string
end

(** {2 Names} *)

module Name :  sig

  (** [fresh b] creates a fresh name with the boundedness [b].*)
  val fresh : boundedness ->  name

  (** [fresh_with_label b s] creates a fresh name with the boundedness [b] and label [s].*)
  val fresh_with_label : boundedness ->  string -> name

  (** [fresh_from n] creates a fresh name with the same label and same boundedness as [n].*)
  val fresh_from : name -> name

  (** A total ordering function over names. This is a two-argument function [order] such that  [order n1 n2] is zero if
      the [n1] and [n2] are equal, [order n1 n2] is strictly negative if [n1] is smaller than [n2], and
      strictly strictly positive if [n1] is greater than [n2]. *)
  val order : name -> name -> int

  (** Check whether a name is public. *)
  val is_public : name -> bool

  (** [is_equal n1 n2] returns [true] iff the name [n1] and [n2] are equal. *)
  val is_equal : name -> name -> bool

  (** [display n] does not display the boundedness of [n], only its name. *)
  val display : Display.output  -> ?rho:display_renamings option -> name -> string

  val set_up_counter : int -> unit

  val get_counter : unit -> int

  (** {3 Renaming} *)

  module Renaming : sig

    (** Name renaming. *)
    type t

    (** Domain of a name renaming *)
    type domain

    (** {4 Generation} *)

    (** Returns the identify renaming. *)
    val identity : t

    (** [fresh n_l b] generate a fresh renaming for the names in [n_l]. The image of the renaming contains only names with boundedness as [b]. *)
    val fresh : name list -> boundedness -> t

    (** [compose] {% $\rho_1$~$\rho_2$ returns the renaming $\rho_1\rho_2$. %} *)
    val compose : t -> name -> name -> t

    (** Returns the empty domain. *)
    val empty : domain

    (** [add d n] adds the name [n] in the domain [d]. *)
    val add : domain -> name -> domain

    (** [get_names_with_list] {% $\rho$ %} [l] adds the names in {% $\rho$ %} in the list [l]. The addition of a name as the union of sets, i.e. there is no dupplicate in the resulting list..*)
    val get_names_with_list : t -> name list -> name list

    (** [intersect_domain] {% $\rho_1$~$\rho_2$ returns $\Dom{\rho_1} \cap \Dom{\rho_2}$. %}*)
    val intersect_domain : t -> t -> domain

    (** {4 Testing} *)

    (** Check whether the renaming is the identity renaming. *)
    val is_identity : t -> bool

    (** Checks whether the two renamings are the same. *)
    val is_equal : t -> t -> bool

    (** {4 Operators} *)

    (** Generates a domain from a list of names. *)
    val of_list : name list -> domain

    (** [restict] {% $\rho$~$d$% returns the renaming $\SubRestr{\rho}{x \in \Dom{\rho} \cap d}$. %}*)
    val restrict : t -> domain -> t

    (** [apply_on_terms] {% $\rho$ %} [elt map_elt] applies the renaming {% $\rho$ %} on the element [elt]. The function
        [map_elt] should map the protocol terms contained in the element [elt] on which {% $\rho$ %} should be applied. *)
    val apply_on_terms : t -> 'a -> ('a -> (protocol_term -> protocol_term) -> 'a) -> 'a

    (** {4 Display} *)

    val display : Display.output -> ?rho:display_renamings option -> t -> string

    val display_domain : Display.output -> ?rho:display_renamings option -> domain -> string
  end
end

(** {2 Terms} *)

(** {3 Generation of terms} *)

(** [of_variable x] returns the variable [x] considered as a term.*)
val of_variable : ('a, 'b) variable -> ('a, 'b) term

(** [of_name n] returns the name [n] considered as a protocol term.*)
val of_name : name -> protocol_term

(** [of_axiom ax] returns the axiom [ax] considered as a recipe. *)
val of_axiom : axiom -> recipe

(** [variable_of t] returns the term [t] as a variable.
    @raise Debug.Internal_error if [t] is not a variable. *)
val variable_of : ('a, 'b) term -> ('a, 'b) variable

(** [name_of t] returns the protocol term [t] as a name.
    @raise Debug.Internal_error if [t] is not a name. *)
val name_of : protocol_term -> name

(** [axiom_of r] returns the recipe [r] as an axiom.
    @raise Internal_error if [r] is not an axiom. *)
val axiom_of : recipe -> axiom

(** [apply_function f args] applies the the function symbol [f] to the arguments [args].
    If [args] is the list of element {% $t_1,\ldots, t_n$ %} then the term obtained is {% $f(t_1,...,t_n)$ %}.

    @raise Debug.Internal_error an internal error if the number of arguments in [args] does not coincide
    with the arity of [f]. {% \highdebug %}*)
val apply_function : symbol -> ('a, 'b) term list -> ('a, 'b) term

(** {3 Access functions} *)

(** [root t] returns the symbol {% $\rootsymb{t}$ %}.
    @raise Debug.Internal_error if {% $\rootsymb{t} \not\in \F$. %} *)
val root : ('a, 'b) term -> symbol

(** [get_args t] returns the list of argument of the term [t]. For example, if [t] is the term {% $f(t_1,\ldots t_n)$ %}
    then [get_args t] returns the list of element {% $t_1,\ldots,t_n$ %}.
    @raise Debug.Internal_error if {% $\rootsymb{t} \not\in \F$ or if $t$ is a constant. %} *)
val get_args : ('a, 'b) term -> ('a, 'b) term list

(** [get_type] {% $\xi$ returns the integer $k$ such that $\xi \in \Tdeux_k \setminus \Tdeux_{k-1}$. %} *)
val get_type : recipe -> int

(** [get_vars at t] returns the list of all variables in [t]. *)
val get_vars : ('a, 'b) atom -> ('a, 'b) term -> ('a, 'b) variable list

(** [get_vars_with_list at t f_q l] adds the variables in [t] whose quantifier satisfies [f_q] in the list [l]. The addition of a variable as the union of sets, i.e. there is no dupplicate in the resulting list. *)
val get_vars_with_list : ('a, 'b) atom -> ('a, 'b) term -> (quantifier -> bool) -> ('a, 'b) variable list -> ('a, 'b) variable list

(** [get_names_with_list t f_b l] adds the names in [t] whose boundedness satisfies [f_b] in the list [l]. The addition of a name as the union of sets, i.e. there is no dupplicate in the resulting list..*)
val get_names_with_list : ('a, 'b) atom -> ('a, 'b) term -> (boundedness -> bool) -> name list -> name list

(** [get_axioms_with_list t f_i l] adds the axiom in [t] whose index satisfies [f_i] in the list [l]. The addition of an axiom as the union of sets, i.e. there is no dupplicate in the resulting list..*)
val get_axioms_with_list : recipe -> (int -> bool) -> axiom list -> axiom list

(** A total ordering function over terms. This is a three-argument function [order] such that  [order at t1 t2] is zero if
    the [t1] and [t2] are equal, [order at t1 t2] is strictly negative if [t1] is smaller than [t2], and
    strictly strictly positive if [t1] is greater than [t2]. *)
val order : ('a, 'b) atom -> ('a, 'b) term -> ('a, 'b) term -> int

(** {3 Scanning} *)

(** [is_ground t] returns [true] iff {% $\varsun{t} \cup \varsdeux{t} = \emptyset$. %} *)
val is_ground : ('a, 'b) term -> bool

(** [no_axname t] returns [true] iff {% $\names{t} = \emptyset$ %} when [t] is a protocol term and {% $\axioms{t} = \emptyset$ %} when [t] is a recipe. *)
val no_axname : ('a, 'b) term -> bool

(** [var_occurs x t] returns [true] iff the variable [x] occurs in the term [t], i.e., {% $x \in \vars{t}$. %} *)
val var_occurs : ('a, 'b) variable -> ('a, 'b) term -> bool

(** [name_occurs n t] returns [true] iff the name [n] occurs in the protocol term [t], i.e., {% $n \in \names{t}$. %}*)
val name_occurs : name -> protocol_term -> bool

(** [axiom_occurs ax r] returns [true] iff the axiom [ax] occurs in the recipe [r], i.e., {% $ax \in \axioms{r}$. %} *)
val axiom_occurs : axiom -> recipe -> bool

(** [is_equal at t1 t2] returns [true] iff the [at] terms [t1] and [t2] are equal. *)
val is_equal : ('a, 'b) atom -> ('a, 'b) term -> ('a, 'b) term -> bool

(** [is_variable t] returns [true] iff the term [t] is a variable, i.e., {% $t \in \X \setminus \AX$. %} *)
val is_variable : ('a, 'b) term -> bool

(** [is_name t] returns [true] iff the term [t] is a name, i.e., {% $t \in \Npriv$. %}*)
val is_name : protocol_term -> bool

(** [is_axiom r] returns [true] iff the recipe [r] is an axiom, i.e., {% $v \in \AX$. %}  *)
val is_axiom : recipe -> bool

(** [is_function t] returns [true] iff {% $\rootsymb{t} \in \F$. %} *)
val is_function : ('a, 'b) term -> bool

(** [is_constructor t] returns [true] iff {% $t \in \T(\Fc, \Xun \cup \Npriv)$ when $t$ is a protocol term and
    $t \in \T(\Fc, \Xdeux \cup \AX)$ when $t$ is a recipe. %} *)
val is_constructor : ('a, 'b) term -> bool

(** {3 Display} *)

val display : Display.output -> ?rho:display_renamings option -> ('a, 'b) atom -> ('a, 'b) term -> string

(** {2 Substitution} *)

module Subst : sig
  type ('a, 'b) t

  (** {3 Generation} *)

  (** [identity] corresponds to the identity substitution.*)
  val identity : ('a, 'b) t

  (** [create at x t] creates the substitution {% $\sigma = \\{x \rightarrow t\\}$. %}
      @raise Debug.Internal_error if the {% $\sigma$ is not acyclic, i.e., if $x \in \vars{t}$, or it the type is not
      satisfied, i.e., if $x \in \Xdeuxi{i}$ and $t \not\in \T(\F,\Xdeux_i \cup \AX_i)$. \highdebug %}*)
  val create : ('a, 'b) atom -> ('a, 'b) variable -> ('a, 'b) term -> ('a, 'b) t

  (** [create_multiple at] {% $\ell$ creates the substitution $\sigma = \\{x \rightarrow t \mid (x,t) \in \ell \\}$. %}
      @raise Debug.Internal_error if the {% $\sigma$ is not acyclic or it the types are not
      satisfied. \highdebug %}*)
  val create_multiple : ('a, 'b) atom -> (('a, 'b) variable * ('a, 'b) term) list -> ('a, 'b) t

  (** [of_renaming] {% $\rho$ casts the renaming $\rho$ as a substitution. %} *)
  val of_renaming : ('a, 'b) Variable.Renaming.t -> ('a, 'b) t

  (** [equations_of] {% $\sigma$ %} returns the list [ ({%$x_1$},{%$t_1$}),...,({%$x_1$},{%$t_1$})] where {% $\sigma = \\{ x_i \rightarrow t_i \\}_i^n$. %}*)
  val equations_of : ('a, 'b) t -> (('a, 'b) term * ('a, 'b) term) list

  val split_domain : ('a, 'b) t -> (('a, 'b) variable -> bool) -> ('a, 'b) t * ('a, 'b) t

  val split_domain_on_term : ('a, 'b) t -> (('a, 'b) term -> bool) -> ('a, 'b) t * ('a, 'b) t

  (** [union] {% $\sigma_1$~$\sigma_2$ returns the substitution $\sigma$ such that $\Dom{\sigma} = \Dom{\sigma_1} \cup \Dom{\sigma_2}$ and
      for all $i= 1,2$, for all $x \in \Dom{\sigma_i}$, $x\sigma = x\sigma_i$.%}
      @raise Internal_error if {% $\Dom{\sigma_1} \cap \Dom{\sigma_2} \neq \emptyset$.%} *)
  val union : ('a, 'b) t -> ('a, 'b) t -> ('a, 'b) t

  (** [compose] {% $\sigma_1$~$\sigma_2$ returns the substitution $\sigma_1\sigma_2$. %}
      @raise Debug.Internal_error if {% $\Dom{\sigma_1} \cap \Dom{\sigma_2} \neq \emptyset$ or if  the resulting substitution is not acyclic. \highdebug %} *)
  val compose : ('a, 'b) t -> ('a, 'b) t -> ('a, 'b) t

  (** [compose_restricted] {% $\sigma_1$~$\sigma_2$ returns the substitution $\SubRestr{\sigma_1\sigma_2}{\Dom{\sigma_1}}$. %}
      @raise Debug.Internal_error if {% $\Dom{\sigma_1} \cap \Dom{\sigma_2} \neq \emptyset$ or if the resulting substitution is not acyclic. \highdebug %} *)
  val compose_restricted : ('a, 'b) t -> ('a, 'b) t -> ('a, 'b) t

  (** [compose_restricted_generic] {% $\sigma_1$~$\sigma_2$ %} [f] returns the substitution {% $\SubRestr{\sigma_1\sigma_2}{D}$ where $D = \Dom{\sigma_1} \cup \\{ x \in \Dom{\sigma_2} \mid$ %} [f] {% $x =$ %} [true] {% $\\}$. %} *)
  val compose_restricted_generic : ('a, 'b) t -> ('a, 'b) t -> (('a, 'b) variable -> bool) -> ('a, 'b) t

  (** [restrict] {% $\sigma$~$\ffun$ returns the substitution $\sigma$ whose domain is
      restricted to the variables $x$ such that $\ffun$~$x$ %} = [true].*)
  val restrict : ('a, 'b) t -> (('a, 'b) variable -> bool) -> ('a, 'b) t

  (** {3 Access} *)

  (** [get_vars_with_list at s f_q l] adds the variables in [s] whose quantifier satisfies [f_q] in the list [l]. The addition of a variable as the union of sets, i.e. there is no dupplicate in the resulting list. *)
  val get_vars_with_list : ('a, 'b) atom -> ('a, 'b) t -> (quantifier -> bool) -> ('a, 'b) variable list -> ('a, 'b) variable list

  (** [get_names_with_list s f_b l] adds the names in [s] whose boundedness atisfies [f_b] in the list [l]. The addition of a name as the union of sets, i.e. there is no dupplicate in the resulting list..*)
  val get_names_with_list : ('a, 'b) atom -> ('a, 'b) t -> (boundedness -> bool) -> name list -> name list

  (** [get_axioms_with_list s f_i l] adds the axiom in [s] whose index atisfies [f_i] in the list [l]. The addition of an axiom as the union of sets, i.e. there is no dupplicate in the resulting list..*)
  val get_axioms_with_list : (snd_ord, axiom) t -> (int -> bool) -> axiom list -> axiom list

  (** {3 Testing} *)

  (** [is_equal_equations at] {% $\sigma_1$~$\sigma_2$ returns %} [true] if the formulas {% $\bigwedge_{x \in \Dom{\sigma_1}} x \eqs x\sigma_1$
      and $\bigwedge_{x \in \Dom{\sigma_2}} x \eqs x\sigma_2$ have same solutions. %}*)
  val is_equal_equations : ('a, 'b) atom -> ('a, 'b) t -> ('a, 'b) t -> bool

  (** [is_identity s] returns [true] iff [s] is the identity substitution. *)
  val is_identity : ('a, 'b) t -> bool

  (** [is_in_domain s x] returns [true] iff the variable [x] is in the domain of [s].*)
  val is_in_domain : ('a, 'b) t -> ('a, 'b) variable -> bool

  (** [apply_substitution subst elt map_elt] applies the substitution [subst] on the element [elt]. The function
      [map_elt] should map the terms contained in the element [elt] on which [subst] should be applied.

      For example, applying a substitution [subst] on a list of terms [term_list]
      could be done by applying [apply_substitution subst term_list (fun l f -> List.map f l)].

      Another example: applying a substitution [subst] on the second element of a couple of terms could be
      done by applying [apply_substitution subst term_c (fun (t1,t2) f -> (t1, f t2))].
      *)
  val apply : ('a, 'b) t -> 'c -> ('c -> (('a, 'b) term -> ('a, 'b) term) -> 'c) -> 'c

  val apply_both : (fst_ord, name) t -> (snd_ord, axiom) t -> 'a -> ('a  -> ((fst_ord, name) term -> (fst_ord, name) term) -> ((snd_ord, axiom) term -> (snd_ord, axiom) term) -> 'a) -> 'a

  val apply_generalised : ('a, 'b) t -> 'c -> ('c -> (('a, 'b) term -> ('a, 'b) term) -> 'd) -> 'd

  (* [fold f elt] {% $\sigma$ %} returns [f (... (f (f elt] {% $x_1$~$t_1$%}[)] {% $x_2$~$t_2$%}[) ...)]{% $x_n$~$t_n$ where $\sigma = \{ x_i \rightarrow t_i \}_{i=1}^n$.
    Note that the order of the variables in $\sigma$ is unspecified. %}*)
  val fold : ('c -> ('a, 'b) variable -> ('a, 'b) term -> 'c) -> 'c -> ('a, 'b) t -> 'c

  (** {3 Unification} *)

  exception Not_unifiable

  (** [unify at l] unifies the pairs of term in [l] and returns the most general substitution that unifies them, i.e., {% $\mguset{l}$. %}
      When the subtitution {% $\sigma$ %} obtained is of the form {% $\sigma = \\{ x \rightarrow y \\}\sigma'$ for some variables $x,y$ of same type
      (i.e., $x,y \in \Xun$ when the substitution is on protocol term, and $x,y \in \Xdeuxi{i}$ for some $i$ when the substitution
      is on recipe) and some substitution $\sigma'$, then the following properties hold:
      \begin{itemize}
        \item $x$ is existential implies $y$ is either existential or free
        \item $x$ is free implies $y$ is free
      \end{itemize} %}
      @raise Not_unifiable if no unification is possible. *)
  val unify : ('a, 'b) atom -> (('a, 'b) term * ('a, 'b) term) list -> ('a, 'b) t

  (** [is_unifiable at l] returns [true] iff the pairs of term in [l] are unifiable, {% $\mguset{l} \neq \bot$. %} *)
  val is_unifiable : ('a, 'b) atom -> (('a, 'b) term * ('a, 'b) term) list -> bool

  (** [is_matchable at [{% $u_1$ %};...;{% $u_n$ %}] [{% $v_1$ %};...;{% $v_n$ %}]] returns [true] iff there exists {% a substitution $\sigma$ such that
      $\forall i \in \mathbb{N}^n_1$, $u_i\sigma = v_i$. Note that we allow $\sigma$ to be cyclic and to not respect types (for second-order variables). %}
      @raise Internal_error if the two lists do not have the same length. *)
  val is_matchable : ('a, 'b) atom -> ('a, 'b) term list -> ('a, 'b) term list -> bool

  (** [is_extended_by at] {% $\sigma_1$~$\sigma_2$ %} returns [true] iff {% $\exists \sigma. \sigma_2 = \sigma_1\sigma$. %}*)
  val is_extended_by : ('a, 'b) atom -> ('a, 'b) t -> ('a, 'b) t -> bool

  (** {3 Display function} *)

  val display : Display.output -> ?rho:display_renamings option -> ('a, 'b) atom -> ('a, 'b) t -> string

  (** {3 Tested functions} *)

  val update_test_unify : ('a, 'b) atom -> ((('a, 'b) term * ('a, 'b) term) list -> ('a, 'b) t option -> unit) -> unit

  val update_test_is_matchable : ('a, 'b) atom -> (('a, 'b) term list -> ('a, 'b) term list -> bool -> unit) -> unit

  val update_test_is_extended_by : ('a, 'b) atom -> (('a, 'b) t -> ('a, 'b) t -> bool -> unit) -> unit

  val update_test_is_equal_equations: ('a, 'b) atom -> (('a, 'b) t -> ('a, 'b) t -> bool -> unit) -> unit
end

(** {% A valuation in this section corresponds to a triplet of substitutions $(\Phi,\Sigma,\sigma)$ where $\Phi : \AX \rightarrow \T(\Fc,\N)$,
    $\Sigma : \Xdeux \rightarrow \T(\F,\Npub \cup (\Xdeux \cap \Dom{\Phi}))$ and $\sigma : \Xun \rightarrow \T(\Fc,\N)$. %} *)

(** {2 Syntactic disequations} *)

module Diseq : sig

  (** The type [disequation] represents {% an element of the form $\forall x_1\ldots \forall x_m. \bigvee_{i=1}^n u_i \neqs v_i$
      where $x_1,\ldots, x_m$ are variables and $u_1,v_1,\ldots, u_n,v_n$ are terms. Note that when the terms
      are protocol terms, then $u_1,v_1,\ldots, u_n,v_n$ are constructor protocol terms. %} *)
  type ('a, 'b) t

  (** {4 Access} *)

  (** [get_names_with_list s l] adds the names in [s] in the list [l]. The addition of a name as the union of sets, i.e. there is no dupplicate in the resulting list..*)
  val get_names_with_list : ('a, 'b) atom -> ('a, 'b) t -> name list -> name list

  (** [get_vars_with_list at s l] adds the variables in [s] in the list [l]. The addition of a variable as the union of sets, i.e. there is no dupplicate in the resulting list. *)
  val get_vars_with_list : ('a, 'b) atom -> ('a, 'b) t -> ('a, 'b) variable list -> ('a, 'b) variable list

  (** [get_axioms_with_list s l] adds the axiom in [s] in the list [l]. The addition of an axiom as the union of sets, i.e. there is no dupplicate in the resulting list..*)
  val get_axioms_with_list : (snd_ord, axiom) t -> axiom list -> axiom list

  (** {4 Tesing} *)

  (** [is_top diseq] returns [true] iff the disequation is {% $\top$ %}. Note that it is a syntactic condition meaning
      that an disequation that is semantically a tautology is not necessarily {% $\top$ %}.*)
  val is_top : ('a, 'b) t -> bool

  (** [is_top diseq] returns [true] iff the disequation is {% $\bot$ %}. Note that it is a syntactic condition meaning
      that an disequation that is semantically unsatisfiable is not necessarily {% $\bot$ %}.*)
  val is_bot : ('a, 'b) t -> bool

  (** {4 Generation} *)

  (** [of_substitution] {% $\sigma$~$S$ generates the normalisation of the disequation $\forall S. \bigvee_{x \in \Dom{\sigma}} x \neqs x\sigma$. %} *)
  val of_substitution : ('a, 'b) atom -> ('a, 'b) Subst.t -> ('a, 'b) variable list -> ('a, 'b) t

  (** [substitution_of_diseq at] {% $\forall \tilde{x}. \bigvee^n_1 x_i \neqs v_i$ generates the pair $(\sigma,\rho)$ where
      $\rho$ is a fresh renaming of $\tilde{x}$ to existential variables and
      $\sigma = \\{ x_i \rightarrow v_i\rho\\}_i^n$.%}
      @raise Internal_error if the disequation is bot. *)
  val substitution_of : ('a, 'b) atom -> ('a, 'b) t -> ('a, 'b) Subst.t * ('a, 'b) Variable.Renaming.t


  (** [apply_and_normalise at] {% $\sigma$~$\phi$ applies the substitution $\sigma$ on $\phi$ and normalise
      the disequation, i.e., returns $\phi\sigma\Vnorm$. %}
      @raise Debug.Internal_error if {% $\sigma$ %} contains universal variables. {% \highdebug %} *)
  val apply_and_normalise : ('a, 'b) atom -> ('a, 'b) Subst.t -> ('a, 'b) t -> ('a, 'b) t

  (** {4 Display} *)

  val display : Display.output -> ?rho:display_renamings option -> ('a, 'b) atom -> ('a, 'b) t -> string

  (** {4 Testing} *)

  val create_for_testing : (('a, 'b) term * ('a, 'b) term) list -> ('a, 'b) t
end

(** {2 (Dis)equations modulo the rewriting system} *)

module Modulo : sig

  (** The type [equation_modulo] represents an equation of the form {% $u \eqi v$ where $u,v$ are protocol terms.
      The satisfiability relation is defined as
      \\[
      (\Phi,\Sigma,\sigma) \models u \eqi v \mbox{\quad iff \quad} u\sigma\norm = v\sigma\norm \mbox{ and }\predmsg{u\sigma} \mbox{ and } \predmsg{v\sigma}
      \\] %} *)
  type equation

  (** The type [disequation_modulo] represents the negative literal {% $\neg (u \neqi v)$, denoted $u\neqi v$.
      Since we will apply a different treatment for positive and negative literals, we consider two distint types. %} *)
  type disequation

  (** {3 Generation} *)

  (** [create_equation] {% $u$~$v$ generates the equation $u \eqi v$.%}*)
  val create_equation : protocol_term -> protocol_term -> equation

  (** [create_disequation] {% $u$~$v$ generates the disequation $u \neqi v$.%}*)
  val create_disequation : protocol_term -> protocol_term -> disequation

  (** {3 Access} *)

  (** [get_vars_eq_with_list eq f_q l] adds the variables in [eq] whose quantifier satisfies [f_q] in the list [l]. The addition of a variable as the union of sets, i.e. there is no dupplicate in the resulting list. *)
  val get_vars_eq_with_list : equation -> (quantifier -> bool) -> fst_ord_variable list -> fst_ord_variable list

  (** [get_names_eq_with_list eq f_b l] adds the names in [eq] whose boundedness atisfies [f_b] in the list [l]. The addition of a name as the union of sets, i.e. there is no dupplicate in the resulting list..*)
  val get_names_eq_with_list : equation -> (boundedness -> bool) -> name list -> name list

  (** [get_vars_diseq_with_list diseq f_q l] adds the variables in [diseq] whose quantifier satisfies [f_q] in the list [l]. The addition of a variable as the union of sets, i.e. there is no dupplicate in the resulting list. *)
  val get_vars_diseq_with_list : disequation -> (quantifier -> bool) -> fst_ord_variable list -> fst_ord_variable list

  (** [get_names_diseq_with_list diseq f_b l] adds the names in [diseq] whose boundedness atisfies [f_b] in the list [l]. The addition of a name as the union of sets, i.e. there is no dupplicate in the resulting list..*)
  val get_names_diseq_with_list : disequation -> (boundedness -> bool) -> name list -> name list

  (** {3 Display} *)

  val display_equation : Display.output -> ?rho:display_renamings option -> equation -> string

  val display_disequation : Display.output -> ?rho:display_renamings option -> disequation -> string

  (** {3 transformation} *)

  exception Top

  exception Bot

  (** [syntactic_equations_of_equations l_eq] returns {% a set of substitutions $\\{ \sigma_1,\ldots \sigma_n \\}$ such that %}
      if [l_eq] is the list of equations corresponding to {% $\bigwedge_{i=1}^m u_i \eqi v_i$ and $V = \bigcup_{i=1}^m \varsun{u_i,v_i}$ then for all $\sigma$,
      \\[
        \sigma \models \bigwedge_{i=1}^m u_i \eqi v_i \mbox{ iff } \sigma \models \bigvee_{i=1}^n \exists E_i. \bigwedge_{ x \in \Dom{\sigma_i}} x \eqs x\sigma_i
      \\]
      where for all $i \in \\{1,\ldots, n\\}$, $E_i = \varsun{\sigma_i} \setminus V$. Note that all the new variables
      in the different substitutions are all fresh, i.e., %} created with [FstVar.fresh Existential].
      @raise Top if the list of equations is a tautology.
      @raise Bot if the list of equations is unsatisfiable.
      *)
  val syntactic_equations_of_equations : equation list -> (fst_ord, name) Subst.t list

  (** [disequations_of_disequations_modulo diseq] returns a list of disequations [l] {% such that %}
      if [diseq] is the {% disequation $u \neqi v$ %} and [l] is the list corresponding to {% $\bigwedge_{i=1}^n \forall S_i. \bigvee_{j=1}^m u_{i,j} \neqs v_{i,j}$ then for all $\sigma$,
      \\[
        \sigma \models u \neqi v \mbox{ iff } \sigma \models \bigwedge_{i=1}^n \forall S_i. \bigvee_{j=1}^m u_{i,j} \neqs v_{i,j}
      \\]
      Moreover, the disequations are already normalised w.r.t. to the normalisation rules described in~\citepaper{Figure}{fig:normalisation_formula}, i.e., for all $i \in \\{1,\ldots, n\\}$,
      \\[
      (\forall S_i. \bigvee_{j=1}^m u_{i,j} \neqs v_{i,j})\Vnorm = \forall S_i. \bigvee_{j=1}^m u_{i,j} \neqs v_{i,j}
      \\]
      Note that all the new variables in the different disequations, i.e., in $S_1,\ldots S_n$, are all fresh, i.e., created %} with [FstVar.fresh Universal].
      @raise Top if the disequation is a tautology.
      @raise Bot if the disequation is unsatisfiable.
      *)
  val syntactic_disequations_of_disequations : disequation -> (fst_ord, name) Diseq.t list

  (** {3 Tested functions} *)

  type 'a result =
    | Top_raised
    | Bot_raised
    | Ok of 'a

  val update_test_syntactic_equations_of_equations : (equation list -> (fst_ord, name) Subst.t list result -> unit) -> unit

end

(** {2 Basic deduction facts} *)

module BasicFact : sig

  (** The type [basic_deduction_fact] represents basic deduction facts, {% that are deduction fact $\dedfact{\xi}{u}$ where $\xi \in \Xdeux$. %} *)
  type t

  (** {3 Generation} *)

  (** [create] {% $X$~$t$ returns the basic deduction fact $\dedfact{X}{t}$. %}*)
  val create : snd_ord_variable -> protocol_term -> t

  (** {3 Access} *)

  (** [get_snd_ord_variable fct] with [fct] being {% $\dedfact{X}{u}$ returns $X$. %} *)
  val get_snd_ord_variable : t -> snd_ord_variable

  (** [get_protocol_term fct] with [fct] being {% $\dedfact{X}{u}$ returns $u$. %} *)
  val get_protocol_term : t -> protocol_term

  (** {3 Display} *)

  val display : Display.output -> ?rho:display_renamings option -> t -> string
end

(** {2 Deduction and equality facts / formulas} *)

module Fact : sig

  (** {3 Basic types} *)

  (** The type [deduction] represents {% a deduction fact, that is an element of the form $\dedfact{\xi}{u}$ where $\xi$ is a recipe
      and $u$ is a constructor term (see~\citepaper{Section}{subsec:first_order_logic}). The satisfiability relation is defined as
      \\[
      (\Phi,\Sigma,\sigma) \models \dedfact{\xi}{u} \mbox{\quad iff \quad} \xi\Sigma\Phi\norm = u\sigma\norm \mbox{ and }\predmsg{\xi\Sigma\Phi}
      \\] %} *)
  type deduction

  (** The type [equality] represents {% an equality fact, that is an element of the form $\xi_1 \eqf \xi_2$ where $\xi_1,\xi_2$ are recipes
      (see~\citepaper{Section}{subsec:first_order_logic}). The satisfiability relation is defined as
      \\[
      (\Phi,\Sigma,\sigma) \models \xi_1 \eqf \xi_2 \mbox{\quad iff \quad} \xi_1\Sigma\Phi\norm = \xi_2\Sigma\Phi\norm \mbox{ and }\predmsg{\xi_1\Sigma\Phi} \mbox{ and }\predmsg{\xi_2\Sigma\Phi}
      \\] %} *)
  type equality

  (** The type [fact] represents the fact that we will consider only two kinds of formula, that are equality and deduction formula. *)
  type 'a t =
    | Deduction : deduction t
    | Equality : equality t

  (** Generic type for formula *)
  type 'a formula

  (** The type [deduction_formula] represents the deduction formulas defined {% in~\citepaper{Definition}{def:clause}.%} *)
  type deduction_formula = deduction formula

  (** The type [equality_formula] represents the equality formulas defined {% in~\citepaper{Definition}{def:clause}.%} *)
  type equality_formula = equality formula

  (** {3 Generation} *)

  (** [create_deduction_fact] {% $\xi$~$u$ creates the deduction fact $\dedfact{\xi}{u}$. %}*)
  val create_deduction_fact : recipe -> protocol_term -> deduction

  (** [create_equality_fact] {% $\xi$~$\zeta$ creates the deduction fact $\xi \eqf \zeta$. %}*)
  val create_equality_fact : recipe -> recipe -> equality

  exception Bot

  val create : 'a t -> 'a -> BasicFact.t list -> (protocol_term * protocol_term) list -> 'a formula

  val create_for_testing : 'a -> BasicFact.t list -> (fst_ord, name)Subst.t -> 'a formula

  (** {3 Access} *)

  (** [get_recipe fct] with [fct] being {% $\dedfact{\xi}{u}$ returns $\xi$. %} *)
  val get_recipe : deduction -> recipe

  (** [get_protocol_term fct] with [fct] being {% $\dedfact{\xi}{u}$ returns $u$. %} *)
  val get_protocol_term : deduction -> protocol_term

  (** [get_both_term fct] with [fct] being {% $\xi_1 \eqf \xi_2$ returns $(\xi_1,\xi_2)$. %} *)
  val get_both_recipes : equality -> recipe * recipe

  (** [get_ded_head] {% $\clause{S}{H}{\varphi}$ returns $H$.%} *)
  val get_head : 'a formula -> 'a

  (** [get_mgu_hypothesis] {% $\psi$ returns the substitution $\Fmgu{\psi}$. %} *)
  val get_mgu_hypothesis : 'a formula -> (fst_ord, name) Subst.t

  (** [get_basic_fact_hypothesis] {% $\psi$ returns $\Df(\psi)$. %} *)
  val get_basic_fact_hypothesis : 'a formula -> BasicFact.t list

  (** [get_vars_with_list at fct] {% $\psi$ %} [f_q l] adds the [at] variables in the [fct] formula {% $\psi$ %} whose quantifier satisfies [f_q] in the list [l]. The addition of a variable as the union of sets, i.e. there is no dupplicate in the resulting list. *)
  val get_vars_with_list : ('a, 'b) atom -> 'c t -> 'c formula -> (quantifier -> bool) -> ('a, 'b) variable list -> ('a, 'b) variable list

  (** [get_names_with_list t fct] {% $\psi$ %} [f_b l] adds the names in the [fct] formula {% $\psi$ %} whose boundedness satisfies [f_b] in the list [l]. The addition of a name as the union of sets, i.e. there is no dupplicate in the resulting list..*)
  val get_names_with_list : 'c t -> 'c formula -> (boundedness -> bool) -> name list -> name list

  (** [get_axioms_with_list t fct] {% $\psi$ %} [f_i l] adds the axiom in the [fct] formula {% $\psi$ %} whose index satisfies [f_i] in the list [l]. The addition of an axiom as the union of sets, i.e. there is no dupplicate in the resulting list..*)
  val get_axioms_with_list : 'c t -> 'c formula -> (int -> bool) -> axiom list -> axiom list

  (** [universal_variables form] returns the first-order and second-order universal variables in the formula [form] *)
  val universal_variables : 'a formula -> (fst_ord, name) variable list * (snd_ord, axiom) variable list

  (** {3 Testing} *)

  (** [is_solved] {% $\psi$ %} returns [true] iff {% $\psi$ is a solved formula (see~\citepaper{Definition}{def:clause}). %} *)
  val is_solved : 'a formula  -> bool

  (** [is_equation_free] {% $\psi$ %} returns [true] iff {% $\psi = \clause{S}{H}{\varphi}$ with $\Equn(\varphi) = \top$. %} *)
  val is_equation_free : 'a formula -> bool

  (** [is_fact] {% $\psi$ %}) returns [true] iff $\psi$ is a fact, i.e. no universal variables and equation free *)
  val is_fact : 'a formula -> bool

  (** [is_recipe_equivalent] {% $\psi$~$\psi'$ %} returns [true] iff {% $\psi \receq^\rho \psi'$ with $\rho$ being the identity. %} *)
  val is_recipe_equivalent : 'a t -> 'a formula -> 'a formula -> bool

  (** {3 Modification} *)

  (** [apply fct] {% $\psi$~$\Sigma$~$\sigma$ applies the subsitutions $\Sigma$ and $\sigma$ on $\psi$ and normalise the resulting formula
      with respect to the normalisation rules in \citepaper{Figure}{fig:normalisation_formula}, i.e. $\psi\Sigma\sigma\Vnorm$. %}
      @raise Bot if {% $\psi\Sigma\sigma\Vnorm = \bot$. %} *)
  val apply : 'a t -> 'a formula -> (snd_ord, axiom) Subst.t -> (fst_ord, name) Subst.t -> 'a formula

  val apply_fst_ord : 'a t -> 'a formula -> (fst_ord, name) Subst.t -> 'a formula

  val apply_snd_ord : 'a t -> 'a formula -> (snd_ord, axiom) Subst.t -> 'a formula

  val apply_snd_ord_on_fact : 'a t -> 'a -> (snd_ord, axiom) Subst.t -> 'a

  val apply_ded_with_gathering : deduction formula -> (snd_ord, axiom) Subst.t -> (fst_ord, name) Subst.t -> recipe option ref -> deduction formula

  val apply_eq_with_gathering : equality formula -> (snd_ord, axiom) Subst.t -> (fst_ord, name) Subst.t -> equality option ref -> equality formula

  val apply_snd_ord_ded_with_gathering : deduction formula -> (snd_ord, axiom) Subst.t -> recipe option ref -> deduction formula

  val apply_snd_ord_eq_with_gathering : equality formula -> (snd_ord, axiom) Subst.t ->  equality option ref -> equality formula

  (** {3 Display functions} *)

  val display_deduction_fact : Display.output -> ?rho:display_renamings option -> deduction -> string

  val display_equality_fact : Display.output -> ?rho:display_renamings option -> equality -> string

  val display_formula : Display.output -> ?rho:display_renamings option -> 'a t -> 'a formula -> string
end

(** {2 Rewrite rules} *)

module Rewrite_rules : sig

  (** {3 Operators} *)

  (** [normalise t] returns the protocol_term [t] in its normal form. *)
  val normalise : protocol_term -> protocol_term

  type skeleton =
    {
      variable_at_position : snd_ord_variable;
      recipe : recipe;
      p_term : protocol_term;
      basic_deduction_facts : BasicFact.t list;
      rewrite_rule : symbol * protocol_term list * protocol_term
    }

  (** [skeletons] {% $u$~$\ffun$~$k$ returns the list of skeletons $(\xi,t,D) = \Skel{\ell}{p}$ such that $\vars{\xi} \in \Xdeuxi{k}$, $\ell \rightarrow r \in \R$, $\rootsymb{\ell} = \ffun$,
      $\getpos{\ell}{p} \not\in \Xun$, $\mguset{\getpos{\ell}{p} \eqs u} \neq \bot$ and $\vars{\getpos{\ell}{p}} \cap \vars{r} \neq \emptyset$. Note that we consider that $\Skel{\ell}{p}$ is unique with fresh variable (this differs slightly
      from~\citepaper{Section}{sec:transformation rules} where it is define as a set that contains all possible renaming.%}
      @raise Internal_error when [f] is not a destructor. *)
  val skeletons : protocol_term -> symbol -> int -> skeleton list

  val rename_skeletons : skeleton -> snd_ord -> skeleton

  (** The function [skeletons] will be used for the application of the rule {% \Rew. However, we use it
      in a different but equivalent way than in~\paper. Typically, in~\paper, to apply the rule \Rew,
      we need at least a deduction fact $\dedfact{\xi_0}{u_0} \in \Solved(\C)$, a rewrite rule $\ell \rightarrow r \in \R$, a recipe $\xi$, a position $p$ and a formula $\psi_0 \in \RewF{\xi}{\ell \rightarrow r}{p}$ such that
      such that there exists $\Sigma \in \mgs{\FRestr{\C}{\FApply{\Sigma_0}{\psi_0}{\C}}{}}$ where $\Sigma_0 = \\{ \getpos{\xi}{p} \rightarrow \xi_0\\}$.
      However, it is unecessary to calculate the most general solutions for all cases. In particular, when $u_0$ is not unifiable with $\getpos{\ell}{p}$ then we directly obtain that
      $\mgs{\FRestr{\C}{\FApply{\Sigma_0}{\psi_0}{\C}}{}} = \emptyset$. Therefore by inputing $u_0$ to the function %} [skeletons], {% we already reduces considerably the
      number of times we have to calculate most general solutions. Moreover, we also require that $\getpos{\ell}{p} \not\in \Xun$ but for a different reason. In such a case, we
      we would most probably obtain some most general solutions but these cases would either lead to consequential term or they would be covered by other application of the rule \Rew.%} *)

  (** Assuming that {% $(\xi,t,D) = \Skel{\ell}{p}$ for some $\ell \rightarrow r \in \R$ and $p$ a position of $\ell$, and assuming that $\rootsymb{\ell} = \ffun$, %}
      [generic_rewrite_rules_formula] {% $\ffun$~$(\xi,t,D)$ returns the set $\RewF{\xi}{\ell \rightarrow r}{p}\Vnorm$ whete $t$ and $D$ are used for the
      protocol terms.%} *)
  val generic_rewrite_rules_formula : Fact.deduction -> skeleton -> Fact.deduction_formula list

  (** The function [specific_rewrite_rules_formula] directly applies the deduction facts on the formulas generated by the skeleton. *)
  val specific_rewrite_rules_formula : Fact.deduction -> skeleton -> Fact.deduction_formula

  (** [get_vars_with_list l] adds the variables of the rewriting system in the list [l]. The addition of a variable as the union of sets, i.e. there is no dupplicate in the resulting list. *)
  val get_vars_with_list : fst_ord_variable list -> fst_ord_variable list

  (** {3 Display functions} *)

  val display_skeleton : Display.output -> ?rho:display_renamings option -> skeleton -> string

  val display_all_rewrite_rules : Display.output -> ?per_line:int -> ?tab:int -> display_renamings option -> string

  (** {3 Tested functions} *)

  val update_test_normalise : (protocol_term -> protocol_term  -> unit) -> unit

  val update_test_skeletons : (protocol_term -> symbol -> int -> skeleton list -> unit) -> unit

  val update_test_generic_rewrite_rules_formula : (Fact.deduction -> skeleton -> Fact.deduction_formula list -> unit) -> unit
end

(** {2 Tools} *)

module type SDF =
  sig

    type t

    (** [exists] {% $\Solved$ %} [f] returns [true] iff there exists a deduction fact [psi]  of {% $\Solved$ %}
        such that [f psi] returns [true]. *)
    val exists : t -> (Fact.deduction -> bool) -> bool

    (** [find] {% $\Solved$ %} [f] returns [f psi] where [psi] is the a deductin fact of {% $\Solved$ %}
        such that [f psi] is not [None], when such [psi] exists. Otherwise, it returns [None]. *)
    val find : t -> (Fact.deduction -> 'a option) -> 'a option

    type marked_result =
      | Not_in_SDF
      | Marked of protocol_term
      | Unmarked of protocol_term * t

    val find_term_and_mark : t -> recipe -> marked_result
  end

module type DF =
  sig
    type t

    (** [exists_within_var_type] {% $k$~$\Df$ %} [f] returns [true] iff there exists a basic deduction fact [ded] of {% $\SetRestr{\Df}{k}$ %}
        such that [f ded] returns [true]. *)
    val exists_within_var_type : int -> t -> (BasicFact.t -> bool) -> bool

    (** [find_within_var_type] {% $k$~$\Df$ %} [f] returns [f ded] where [ded] is a basic deduction fact of {% $\SetRestr{\Df}{k}$ %}
        such that [f ded] is not [None], when such [ded] exists. Otherwise, it returns [None]. *)
    val find_within_var_type : int -> t -> (BasicFact.t -> 'a option) -> 'a option

    (** [find] {% $\Df$ %} [f] returns [f ded] where [ded] is a basic deduction fact of {% $\Df$ %}
        such that [f ded] is not [None], when such [ded] exists. Otherwise, it returns [None]. *)
    val find : t -> (BasicFact.t -> 'a option) -> 'a option

    val find_term : t -> snd_ord_variable -> protocol_term option

    (** [iter] {% $\Df$ %} [f] returns [f] {% $\dedfact{\xi_1}{t_1}$%}[; ... ; f] {% $\dedfact{\xi_n}{t_n}$ where $\Df = \\{ \dedfact{\xi_i}{t_i} \\}_{i=1}^n$.
        Warning : The order in which the function [iter] goes through the elements of the set $\Df$ is unspecified. %}*)
    val iter : t -> (BasicFact.t -> unit) -> unit
  end

module type Uni =
  sig
    (** The type [set] represents sets of pairs of recipes and protocol terms. Intuitively, {% the set of subterm consequence of a constraint system
        $\C$ is the set $\\{ (\xi,u) \in \Consequence{\Solved(\C) \cup \Df(\C)} \mid \xi \in \st{\InitInput(\C)} \cup \sstdeux{\Solved(\C)}\\}$. %}*)
    type t

    (** [find_protocol] {% $\Set$~$t$%} [f] returns [Some] {% $\xi$ if $(\xi,t) \in \Set$ %} and [f] {% $\xi$ %} returns [true]. Otherwise it returns [None].*)
    val find_protocol_term : t -> protocol_term -> recipe option

    (** [iter] {% $\Set$ %} [f] applies the function [f] to all pairs {% $(\xi,t) \in \Set$.
        Warning : The order in which the function [iter] goes through the pairs of $\Set$ is unspecified. %}*)
    val iter : t -> (recipe -> protocol_term -> unit) -> unit

    val add : t -> recipe -> protocol_term -> t

    val exists : t -> recipe -> protocol_term -> bool
  end

module Tools_Subterm :
  functor (SDF : SDF) (DF : DF) (Uni : Uni)->
    sig

    (** {3 Consequence} *)

    (** [consequence] {% $\Solved$~$\Df$~$\xi$~$t$ %} returns [true] iff {% $(\xi,t) \in \Consequence{\Solved \cup \Df}$.%}*)
    val consequence : SDF.t -> DF.t -> recipe -> protocol_term -> bool

    (** [partial_consequence] is related to [consequence]. When [at = Protocol] (resp. [Recipe]), [partial_consequence at] {% $\Solved$~$\Df$~$t$ (resp. $\xi$)
        \begin{itemize}
        \item %} returns [None] if {% for all $\xi$ (resp. for all $t$),%} [mem] {% $\Solved$~$\Df$~$\xi$~$t$ %} returns [false]; {% otherwise
        \item %} returns [Some(]{% $\xi$%}[)] (resp. [Some(]{% $t$%}[)]) such that [mem] {% $\Solved$~$\Df$~$\xi$~$t$ %} returns [true]. {%
        \end{itemize} %}*)
    val partial_consequence : ('a, 'b) atom -> SDF.t -> DF.t -> ('a, 'b) term -> (recipe * protocol_term) option

    (** Similar to [partial_consequence] but consider the consequence with an additional set of basic deduction fact. *)
    val partial_consequence_additional : ('a, 'b) atom -> SDF.t -> DF.t -> BasicFact.t list -> ('a, 'b) term -> (recipe * protocol_term) option

    (** [uniform_consequence] {% $\Solved$~$\Df$~$\Set$~$t$ returns %} returns [Some(]{% $\xi$%}[)] if {% $(\xi,t) \in \Set$ or if $\forall \zeta. (\zeta,t) \not\in S$ and $(\xi,t) \in \Consequence{\Solved \cup \Df}$. %}*)
    val uniform_consequence : SDF.t -> DF.t -> Uni.t -> protocol_term -> recipe option

    (** {3 Others} *)

    (** [is_df_solved DF] returns [true] if and only if all basic deduction facts in [DF] have distinct variables as right hand terms. *)
    val is_df_solved : DF.t -> bool

    val add_in_uniset : Uni.t -> SDF.t -> DF.t -> recipe -> Uni.t * SDF.t

    (** {3 Tested functions} *)

    val update_test_partial_consequence : ('a, 'b) atom -> (SDF.t -> DF.t -> ('a, 'b) term ->  (recipe * protocol_term) option -> unit) -> unit

    val update_test_partial_consequence_additional : ('a, 'b) atom -> (SDF.t -> DF.t -> BasicFact.t list -> ('a, 'b) term -> (recipe * protocol_term) option -> unit) -> unit

    val update_test_uniform_consequence : (SDF.t -> DF.t -> Uni.t -> protocol_term -> recipe option -> unit) -> unit
  end
