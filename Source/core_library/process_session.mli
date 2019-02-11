(** Operation on processes for equivalence by session *)

open Term

(** Type for plain processes*)
type plain_process =
  | Nil (** The null process *)
  | Input of symbol * fst_ord_variable * plain_process (** [Input(c,x,p)] models an input on a channel [c], bound to variable [x], followed by the execution of the process [p]. *)
  | Output of symbol * protocol_term * plain_process (** [Output(c,u,p)] models an output of a term [u] on a channel [c], followed by the execuion of the process [p]. *)
  | OutputSure of symbol * protocol_term * plain_process (** Also models outputs, with the additional guarantee that it can be executed (w.r.t. the restriction on inputs/outputs in the constructor-destructor setting). *)
  | If of protocol_term * protocol_term * plain_process * plain_process (** [If(u,v,p1,p2)] models an equality test [u=v], followed by the execution of the corresponding process [p1] or [p2]. *)
  | Let of protocol_term * protocol_term * plain_process * plain_process (** [Let(u,v,p1,p2)], with [v] a ground term, performs a pattern matching between [u] and [v], and binds the free variables of [u] accordingly.
  Then either [p1] or [p2] is executed depending on whether the unification succeeded or not. *)
  | New of name * plain_process (** [New(n,p)] declares a private name [n] and proceeds to the execution of [p]. *)
  | Par of plain_process list (** [Par(l)] models a list [l] of processes executed concurrently. *)
  | Repl of plain_process * int (** [Repl(p,n)] models [n] copies of the process [p] executed concurrently. *)


(** {2 Labels} *)

(** A type representing labels for subprocess reference.
Serves as a basis for analysing equivalence by session and managing partial-order reductions (POR) and symmetries. *)
type label = int list

(** Test of independence for labels: returns 0 if the labels are dependent
(i.e. one is the prefix of the other), and returns -1 or 1 otherwise depending
on how they are ordered lexicographically. *)
val indep_labels : label -> label -> int

(** Prints a label, separating positions by dots *)
val print_label : label -> unit

(** The type of implementations of basic operations on pools of processes
indexed by labels, including management of partial-order reductions and
symmetries. The analysis is parametric in these basic operations which may
depend on future extensions of the semantics or of the optimisations. *)
module type OperationsOnProc = sig
  (** the type modelling pools of processes *)
  type configuration
end

(** Implements operations on pools of labelled processes for equivalence by
session;
parametric in the basic operations implemented in argument [Op]. *)
module ManageProc (Op:OperationsOnProc) : sig
  val v : int
end
