(** Management of tests *)

open Term
open Data_structure

type html_code =
  | NoScript of string
  | Script of string * string * string list

(** The type [data_IO] represents all the informations required by the test manager for each tested function.
    The first three lists represent the different tests and their status. Each test is representing by a pair of string [(str1,str2)] where
    [str1] corresponds to the actual tests with complete information (no pretty print), and where [str2] represents the HTML code that will
    used for the UI. *)
type data_IO =
  {
    scripts : bool;

    mutable validated_tests : (string * html_code) list; (** The tests that have been validated by a user *)
    mutable tests_to_check : (string * html_code) list; (** The tests that have been produced during previous testing execution but haven't been validated yet. *)
    mutable additional_tests : (string * html_code) list; (** The tests that are produced during the current execution of DeepSec. *)

    mutable is_being_tested : bool; (** When [is_being_tested] is set to [false], no test is produce for this function *)

    file : string (** Core name of the files that will be generated for this function. *)
  }

(** Preload the tests, validated or not. *)
val preload : unit -> unit

(** Publish all the tests, validated or not, i.e. it generates every html and txt files for each tested function. *)
val publish : unit -> unit

(** This function updates the testing functions. This must be executed before running running any tests otherwise the tests will not be produced *)
val update : unit -> unit

(** [validate data [i_1;...;i_k]] valides the [i_1]-th, ..., [i_k]-th tests from [data.tests_to_check]. The first element of [data.tests_to_check] is considered
    as the 1-fst test of [data.tests_to_check].*)
val validate : data_IO -> int list -> unit

(** [validate data] validates all the tests in [data.tests_to_check].*)
val validate_all_tests : data_IO -> unit

(** {2 Functions to be tested} *)

(** For each tested function, we need to associate some data of type [data_IO] as well as a function that will produce the test resulting of an application
    of the function and a function that will load the test. By convention, we use the full name of the function. For example, consider the function [A.B.C.function_test : 'a -> 'b -> 'c -> bool].
    The data I/O for testing [A.B.C.function_test] will be stored in

    [val data_A_B_C_function_test : data_IO]

    the function producing the test will be as follows:

    [val apply_A_B_C_function_test : 'a -> 'b -> 'c -> string]

    and the function loading the test will be as follows:

    [val load_A_B_C_function_test : 'a -> 'b -> 'c -> bool -> string]
*)

(** {3 Term.Subst.Unify} *)

val data_IO_Term_Subst_unify : data_IO

val apply_Term_Subst_unify : ('a, 'b) atom -> (('a, 'b) term * ('a, 'b) term) list -> string

val load_Term_Subst_unify : int -> ('a, 'b) atom -> (('a, 'b) term * ('a, 'b) term) list -> ('a, 'b) Subst.t option -> html_code

(** {3 Term.Subst.is_matchable} *)

val data_IO_Term_Subst_is_matchable : data_IO

val apply_Term_Subst_is_matchable : ('a, 'b) atom -> ('a, 'b) term list -> ('a, 'b) term list -> string

val load_Term_Subst_is_matchable : int -> ('a, 'b) atom -> ('a, 'b) term list -> ('a, 'b) term list -> bool -> html_code

(** {3 Term.Subst.is_extended_by} *)

val data_IO_Term_Subst_is_extended_by : data_IO

val apply_Term_Subst_is_extended_by : ('a, 'b) atom -> ('a, 'b) Subst.t -> ('a, 'b) Subst.t -> string

val load_Term_Subst_is_extended_by : int -> ('a, 'b) atom -> ('a, 'b) Subst.t -> ('a, 'b) Subst.t -> bool -> html_code

(** {3 Term.Subst.is_equal_equations} *)

val data_IO_Term_Subst_is_equal_equations : data_IO

val apply_Term_Subst_is_equal_equations : ('a, 'b) atom -> ('a, 'b) Subst.t -> ('a, 'b) Subst.t -> string

val load_Term_Subst_is_equal_equations : int -> ('a, 'b) atom -> ('a, 'b) Subst.t -> ('a, 'b) Subst.t -> bool -> html_code

(** {3 Term.Modulo.syntactic_equations_of_equations} *)

val data_IO_Term_Modulo_syntactic_equations_of_equations : data_IO

val apply_Term_Modulo_syntactic_equations_of_equations : Modulo.equation list -> string

val load_Term_Modulo_syntactic_equations_of_equations : int -> Modulo.equation list -> (fst_ord, name) Subst.t list Modulo.result -> html_code

(** {3 Term.Rewrite_rules.normalise} *)

val data_IO_Term_Rewrite_rules_normalise : data_IO

val apply_Term_Rewrite_rules_normalise : protocol_term -> string

val load_Term_Rewrite_rules_normalise : int -> protocol_term -> protocol_term -> html_code

(** {3 Term.Rewrite_rules.skeletons} *)

val data_IO_Term_Rewrite_rules_skeletons : data_IO

val apply_Term_Rewrite_rules_skeletons : protocol_term -> symbol -> int -> string

val load_Term_Rewrite_rules_skeletons : int -> protocol_term -> symbol -> int -> Rewrite_rules.skeleton list -> html_code

(** {3 Term.Rewrite_rules.generic_rewrite_rules_formula} *)

val data_IO_Term_Rewrite_rules_generic_rewrite_rules_formula : data_IO

val apply_Term_Rewrite_rules_generic_rewrite_rules_formula : Fact.deduction -> Rewrite_rules.skeleton -> string

val load_Term_Rewrite_rules_generic_rewrite_rules_formula : int -> Fact.deduction -> Rewrite_rules.skeleton -> Fact.deduction_formula list -> html_code

(** {3 Data_structure.Eq.implies} *)

val data_IO_Data_structure_Eq_implies : data_IO

val apply_Data_structure_Eq_implies : ('a, 'b) atom -> ('a, 'b) Eq.t -> ('a, 'b) term -> ('a, 'b) term -> string

val load_Data_structure_Eq_implies : int -> ('a, 'b) atom -> ('a, 'b) Eq.t -> ('a, 'b) term -> ('a, 'b) term -> bool -> html_code

(** {3 Data_structure.Tools.partial_consequence} *)

val data_IO_Data_structure_Tools_partial_consequence : data_IO

val apply_Data_structure_Tools_partial_consequence : ('a, 'b) atom -> SDF.t -> DF.t -> ('a, 'b) term -> string

val load_Data_structure_Tools_partial_consequence : int -> ('a, 'b) atom -> SDF.t -> DF.t -> ('a, 'b) term -> (recipe * protocol_term) option -> html_code

(** {3 Data_structure.Tools.partial_consequence_additional} *)

val data_IO_Data_structure_Tools_partial_consequence_additional : data_IO

val apply_Data_structure_Tools_partial_consequence_additional : ('a, 'b) atom -> SDF.t -> DF.t -> BasicFact.t list -> ('a, 'b) term -> string

val load_Data_structure_Tools_partial_consequence_additional : int -> ('a, 'b) atom -> SDF.t -> DF.t -> BasicFact.t list -> ('a, 'b) term -> (recipe * protocol_term) option -> html_code

(** {3 Data_structure.Tools.uniform_consequence} *)

val data_IO_Data_structure_Tools_uniform_consequence : data_IO

val apply_Data_structure_Tools_uniform_consequence : SDF.t -> DF.t -> Uniformity_Set.t -> protocol_term -> string

val load_Data_structure_Tools_uniform_consequence : int -> SDF.t -> DF.t -> Uniformity_Set.t -> protocol_term -> recipe option -> html_code

(** {3 Process.of_expansed_process} *)

val data_IO_Process_of_expansed_process : data_IO

val apply_Process_of_expansed_process : Process.expansed_process -> string

val load_Process_of_expansed_process : int -> Process.expansed_process  -> Process.process -> html_code

(** {3 Process.next_output} *)

val data_IO_Process_next_output : data_IO

val apply_Process_next_output : Process.semantics -> Process.equivalence -> Process.process -> (fst_ord, name) Subst.t -> string

val load_Process_next_output : int -> Process.semantics -> Process.equivalence -> Process.process -> (fst_ord, name) Subst.t -> (Process.process * Process.output_gathering) list -> html_code
