(** Operations on terms *)

open Types

(** {% This module regroups all the functions that manipulate terms. In~\paper, the terms
    are splitted into protocol terms and recipes. %}*)

(** {2 Symbols} *)

module Symbol : sig
  (** A symbol can be a destructor or a constructor.*)

  (** The list of all constructors (included the tuple function symbol) used in the algorithm.*)
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

  type setting =
    {
      all_t : symbol list ;
      all_p : (symbol * symbol list) list ;
      all_c : symbol list ;
      all_d : symbol list ;
      nb_c : int ;
      nb_d : int;
      nb_symb : int;
      nb_a : int
    }

  val get_number_of_attacker_name : unit -> int

  val set_up_signature : setting -> unit

  val get_settings : unit -> setting

  (** {3 Addition} *)

  (** [new_symbol ar b n s] creates a constructor function symbol with the name [s] and the arity [ar].
      The symbol is public if [b = true] else private.
      The symbol represents a name if [n = true] else is a user-defined function symbol.
      The resulting symbol is automatically added into [all_constructors].
      Moreover, [number_of_constructors] is increased by 1.
      Note that if the constructor is in fact a tuple, it is better to use [get_tuple].*)
  val new_constructor : int -> bool -> bool -> string -> symbol

  (** [new_destructor ar b s l] creates a destructor function symbol with the name [s] and the arity [ar].
      The symbol is public if [b = true] else private.
      Furthermore each element of [l] represents the arguments and result of a rewrite rule for the destructor.
      The resulting symbol is automatically added into [all_destructors].
      Moreover, [number_of_destructors] is increased by 1.*)
  val new_destructor : int -> bool -> string -> (term list * term) list -> symbol

  (** [get_tuple ar] get the function symbol for tuple of arity [ar].
      If such function symbol was not created yet, it creates it and
      the resulting symbol is automatically added into [all_constructors].
      Moreover, [number_of_constructors] is increased by 1.
      At last, the associated projection function symbol are automatically added into [all_projection].*)
  val get_tuple : int -> symbol

  (** [get_projections f] returns the list [[f_1;...;f_n]] with [f_i] is the projection
      function symbol of the [i]{^ th} element of the tuple function symbol [f].

      @raise Internal_error if [f] is not a tuple.
      @raise Not_found if [f] was not previously introduced by [get_tuple].*)
  val get_projections : symbol -> symbol list

  val auto_cleanup_attacker_name : ((unit -> unit) -> unit) -> (unit -> unit) -> unit

  val fresh_attacker_name : unit -> symbol

  val fresh_attacker_name_ground : unit -> symbol

  val get_attacker_name : string -> symbol

  (** {3 Symbol testing} *)

  (** [is_destructor f] returns true iff [f] is a destructor. *)
  val is_destructor : symbol -> bool

  (** [is_destructor f] returns true iff [f] is a constructor. *)
  val is_constructor : symbol -> bool

  (** [is_attacker_name f] returns true iff [f] is an attacker name. *)
  val is_attacker_name : symbol -> bool

  val order : symbol -> symbol -> int

  (** {3 Symbol Access} *)

  (** [get_arity f] returns the arity of the function symbol [f].*)
  val get_arity : symbol -> int

  (** {3 Display} *)

  val display  : Display.output -> symbol -> string

  val display_with_arity  : Display.output -> symbol -> string

  val display_signature : Display.output -> bool -> string

  val display_names : Display.output -> bool -> string
end

(** {2 Variables} *)

module Variable : sig

  (** [fresh q] creates a fresh variable quantified by [q] with type [ty]. *)
  val fresh : quantifier -> variable

  (** [fresh_with_label q s] creates a fresh variable quantified by [q] with the label [s]. *)
  val fresh_with_label : quantifier -> string -> variable

  (** [fresh_from_var x] creates a fresh variable
      with the same display identifier and quantifier as the variable [x].*)
  val fresh_from : variable -> variable

  (** [fresh_list q n] creates a list of [n] fresh variables all quantified as [q].*)
  val fresh_list : quantifier -> int -> variable list

  (** [quantifier_of x] returns the quantification of the variable [x]. *)
  val quantifier_of : variable -> quantifier

  (** [display out at x] returns a string displaying the variable [x] depending on the outpout mode [out]. *)
  val display : Display.output -> variable -> string

  val set_up_counter : int -> unit

  val get_counter : unit -> int

  (** [rename_term q t] renames the variables in [t] by fresh variables with quantifier [q].
      We assume that the variables can only be linked with VLink. *)
  val rename_term : quantifier -> term -> term

  val rename : variable -> variable

  (** {3 Links} *)

  val currently_linked : variable list ref

  val link_search : variable -> unit

  val link : variable -> variable -> unit

  val link_term : variable -> term -> unit

  val auto_cleanup_with_reset : ((unit -> unit) -> unit) -> (unit -> unit) -> unit

  val auto_cleanup_with_reset_notail : (unit -> 'a) -> 'a

  val auto_cleanup_with_exception : (unit -> 'a) -> 'a

  val cleanup : unit -> unit
end

(** {2 Recipe Variables} *)

module Recipe_Variable : sig

  val infinite_type : int

  (** [fresh at q ty] creates a fresh variable quantified by [q] with type [ty]. *)
  val fresh : quantifier -> int -> recipe_variable

  (** [fresh_from_var x] creates a fresh variable with the same quantifier as the variable [x].*)
  val fresh_from : recipe_variable -> recipe_variable

  (** [fresh_list q ty n] creates a list of [n] fresh variables all quantified as [q] with type [ty].*)
  val fresh_list : quantifier -> int -> int -> recipe_variable list

  (** [quantifier_of x] returns the quantification of the variable [x]. *)
  val quantifier_of : recipe_variable -> quantifier

  (** [type_of] {% $X$ returns the type in which the second-variable $X$ is defined, that is returns $i$ when $X \in \Xdeuxi{i}$. %} *)
  val type_of : recipe_variable -> int

  (** [display out at x] returns a string displaying the variable [x] depending on the outpout mode [out]. *)
  val display : Display.output -> ?display_type:bool ->  ?label:string -> recipe_variable -> string

  val set_up_counter : int -> unit

  val get_counter : unit -> int

  val rename_recipe : quantifier -> recipe -> recipe

  (** A total ordering function over variables. This is a two-argument function [order] such that  [order x1 x2] is zero if
      the [x1] and [x2] are equal, [order x1 x2] is strictly negative if [x1] is smaller than [x2], and
      strictly strictly positive if [x1] is greater than [x2]. *)
  val order : recipe_variable -> recipe_variable -> int

  (** {3 Links} *)

  val currently_linked : recipe_variable list ref

  val link : recipe_variable -> recipe_variable -> unit

  val link_recipe : recipe_variable -> recipe -> unit

  val auto_cleanup_with_reset : ((unit -> unit) -> unit) -> (unit -> unit) -> unit

  val auto_cleanup_with_reset_notail : (unit -> 'a) -> 'a

  val auto_cleanup_with_exception : (unit -> 'a) -> 'a

  val cleanup : unit -> unit
end

(** {3 Axioms} *)

module Axiom : sig

  (** A total ordering function over axioms. This is a two-argument function [order] such that  [order ax1 ax2] is zero if
      the [ax1] and [ax2] are equal, [order ax1 ax2] is strictly negative if [ax1] is smaller than [ax2], and
      strictly strictly positive if [ax1] is greater than [ax2]. *)
  val order : int -> int -> int

  (** [display out ax] returns a string displaying the axiom [ax] depending on the outpout mode [out]. *)
  val display : Display.output -> int -> string
end

(** {2 Names} *)

module Name :  sig

  (** [fresh ()] creates a fresh name.*)
  val fresh :  unit -> name

  (** [fresh_with_label s] creates a fresh name with the boundedness [b] and label [s].*)
  val fresh_with_label : ?pure:bool -> string -> name

  (** [fresh_from n] creates a fresh name with the same label and same boundedness as [n].*)
  val fresh_from : name -> name

  val pure_fresh_from : name -> name

  (** A total ordering function over names. This is a two-argument function [order] such that  [order n1 n2] is zero if
      the [n1] and [n2] are equal, [order n1 n2] is strictly negative if [n1] is smaller than [n2], and
      strictly strictly positive if [n1] is greater than [n2]. *)
  val order : name -> name -> int

  (** [display n] does not display the boundedness of [n], only its name. *)
  val display : Display.output  -> name -> string

  val set_up_counter : int -> unit

  val get_counter : unit -> int

  val currently_linked : name list ref

  val link : name -> name -> unit

  val link_search : name -> unit

  val auto_cleanup_with_reset_notail : (unit -> 'a) -> 'a

  val auto_cleanup_with_exception : (unit -> 'a) -> 'a

  val cleanup : unit -> unit
end

(** {2 Terms} *)

module Term : sig

  (** {3 Access} *)

  (** [variable_of t] returns the term [t] as a variable.
      @raise Debug.Internal_error if [t] is not a variable. *)
  val variable_of : term -> variable

  (** [name_of t] returns the protocol term [t] as a name.
      @raise Debug.Internal_error if [t] is not a name. *)
  val name_of : term -> name

  (** [root t] returns the symbol {% $\rootsymb{t}$ %}.
      @raise Debug.Internal_error if {% $\rootsymb{t} \not\in \F$. %} *)
  val root : term -> symbol

  (** [get_args t] returns the list of argument of the term [t]. For example, if [t] is the term {% $f(t_1,\ldots t_n)$ %}
      then [get_args t] returns the list of element {% $t_1,\ldots,t_n$ %}.
      @raise Debug.Internal_error if {% $\rootsymb{t} \not\in \F$ or if $t$ is a constant. %} *)
  val get_args : term -> term list

  (** [get_vars_not_in t vl] returns the variables of [t] that are not in [vl]. We assume that
      no variables are currently linked when we apply the function. *)
  val get_vars_not_in : term -> variable list -> variable list

  (** {3 Testing} *)

  (** [does_not_contain_name t] returns [true] when [t] does not contain any name.
      Warning: The function does not follow through the links. *)
  val does_not_contain_name : term -> bool

  (** [var_occurs x t] returns [true] iff the variable [x] occurs in the term [t], i.e., {% $x \in \vars{t}$. %}
      Warning: The function follow through the links [TLink]. *)
  val var_occurs : variable -> term -> bool

  (** [quantified_var_occurs q t] returns [true] iff there exists a variable in [t]
      with [q] as quantification. *)
  val quantified_var_occurs : quantifier -> term -> bool

  (** [is_equal t1 t2] returns [true] iff the terms [t1] and [t2] are equal.
      Warning: The function follow through the links [TLink]. *)
  val is_equal : term -> term -> bool

  (** [is_equal_no_follow t1 t2] returns [true] iff the terms [t1] and [t2] are equal.
      Warning: The function does not follow through the linksL. *)
  val is_equal_no_follow : term -> term -> bool

  (** [is_variable t] returns [true] iff the term [t] is a variable, i.e., {% $t \in \X \setminus \AX$. %} *)
  val is_variable : term -> bool

  (** [is_name t] returns [true] iff the term [t] is a name, i.e., {% $t \in \Npriv$. %}*)
  val is_name : term -> bool

  (** [is_function t] returns [true] iff {% $\rootsymb{t} \in \F$. %} *)
  val is_function : term -> bool

  (** [is_constructor t] returns [true] iff {% $t \in \T(\Fc, \Xun \cup \Npriv)$ when $t$ is a protocol term and
      $t \in \T(\Fc, \Xdeux \cup \AX)$ when $t$ is a recipe. %}
      Warning: The function does not follow through the links. *)
  val is_constructor : term -> bool

  (** [is_ground t] returns [true] iff [term] is a ground term, i.e. does not contain variables. *)
  val is_ground : term -> bool

  (** {3 Main functions} *)

  (** [instantiate t] returns the term [t] in which the variables linked with [TLink] are replaced
      by the value of their links. *)
  val instantiate : term -> term

  val instantiate_pattern : pattern -> pattern

  val replace_universal_to_existential : term -> unit

  exception Not_unifiable

  (** [unify t1 t2] unifies the terms [t1] and [t2]. The function likes the variables with [TLink].
      @raise Not_unifiable when [t1] and [t2] are not unifiable. *)
  val unify : term -> term -> unit

  (** [apply_renamings t] replaces the variables and names linked respectively with a VLink and NLink.
      Warning: If there are variables linked with a TLink, the function does not go through. *)
  val apply_renamings : term -> term

  val rename_and_instantiate : term -> term

  val rename_and_instantiate_exclude_universal : term -> term

  val rename_and_instantiate_exclude_universal_slink : term -> term

  exception No_match

  val matching : term -> term -> unit

  (** {3 Display} *)

  val display : ?follow_link:bool -> Display.output -> term -> string

  val display_pattern : ?follow_link:bool -> Display.output -> pattern -> string

  (** {3 Debug} *)

  val debug_link_with_SLink : term -> unit

  val debug_check_link_with_SLink : term -> unit
end

(** {2 Recipe} *)

module Recipe : sig

  (** {3 Access} *)

  (** [variable_of r] returns the recipe [r] as a variable.
      @raise Debug.Internal_error if [r] is not a variable. *)
  val variable_of : recipe -> recipe_variable

  (** [axiom_of r] returns the recipe [r] as the integer axiom.
      @raise Debug.Internal_error if [r] is not an axiom *)
  val axiom_of : recipe -> int

  (** [root r] returns the symbol {% $\rootsymb{r}$ %}.
      @raise Debug.Internal_error if {% $\rootsymb{r} \not\in \F$. %} *)
  val root : recipe -> symbol

  (** [get_args r] returns the list of argument of the recipe [r]. For example, if [r] is the term {% $f(r_1,\ldots r_n)$ %}
      then [get_args r] returns the list of element {% $r_1,\ldots,r_n$ %}.
      @raise Debug.Internal_error if {% $\rootsymb{r} \not\in \F$ or if $r$ is a constant. %} *)
  val get_args : recipe -> recipe list

  (** {3 Main functions} *)

  (** [instantiate r] returns the recipe [r] in which the variables linked with [RLink] are replaced
      by the value of their links. Note that instantiating replace the CRFunc by normal recipe. *)
  val instantiate : recipe -> recipe

  val instantiate_preserve_context : recipe -> recipe

  val is_equal : recipe -> recipe -> bool

  exception Not_unifiable

  val var_occurs_or_strictly_greater_type : recipe_variable -> recipe -> bool

  (** [unify r1 r2] unifies the recipes [r1] and [r2]. The function likes the variables with [RLink].
      @raise Not_unifiable when [r1] and [r2] are not unifiable. *)
  val unify : recipe -> recipe -> unit

  exception No_match

  val matching : recipe -> recipe -> unit

  val display : ?follow_link:bool -> Display.output -> recipe -> string
end
