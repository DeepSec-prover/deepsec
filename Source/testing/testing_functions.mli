(** Management of tests *)

open Term

(** The type [data_IO] represents all the informations required by the test manager for each tested function.
    The first three lists represent the different tests and their status. Each test is representing by a pair of string [(str1,str2)] where
    [str1] corresponds to the actual tests with complete information (no pretty print), and where [str2] represents the HTML code that will
    used for the UI. *)
type data_IO =
  {
    mutable validated_tests : (string * string) list; (** The tests that have been validated by a user *)
    mutable tests_to_check : (string * string) list; (** The tests that have been produced during previous testing execution but haven't been validated yet. *)
    mutable additional_tests : (string * string) list; (** The tests that are produced during the current execution of DeepSec. *)

    mutable is_being_tested : bool; (** When [is_being_tested] is set to [false], no test is produce for this function *)

    template_html : string; (** Name of html file representing the template for generating html page. *)
    html_file : string; (** Name of the html file that will be generated. *)
    terminal_file : string; (** Name of the txt file that will be generated. *)

    folder_validated : string; (** Path of the folder that contain the validated tests for this function. *)
    folder_to_check : string (** Path of the folder that contain the tests that need to be checked. *)
  }

(** Load all the tests, validated or not. *)
val load : unit -> unit

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
    of the function. By convention, we use the full name of the function. For example, consider the function [A.B.C.function_test : 'a -> 'b -> 'c -> bool].
    The data I/O for testing [A.B.C.function_test] will be stored in

    [val data_A_B_C_function_test : data_IO]

    and the function producing the test will be the following one.

    [val apply_A_B_C_function_test : 'a -> 'b -> 'c -> string]
**)

(** {3 Term.Subst.Unify} *)

val data_IO_Term_Subst_unify : data_IO

val apply_Term_Subst_unify : ('a, 'b) atom -> (('a, 'b) term * ('a, 'b) term) list -> string

(** {3 Term.Subst.is_matchable} *)

val data_IO_Term_Subst_is_matchable : data_IO

val apply_Term_Subst_is_matchable : ('a, 'b) atom -> ('a, 'b) term list -> ('a, 'b) term list -> string

(** {3 Term.Subst.is_extended_by} *)

val data_IO_Term_Subst_is_extended_by : data_IO

val apply_Term_Subst_is_extended_by : ('a, 'b) atom -> ('a, 'b) Subst.t -> ('a, 'b) Subst.t -> string

(** {3 Term.Subst.is_equal_equations} *)

val data_IO_Term_Subst_is_equal_equations : data_IO

val apply_Term_Subst_is_equal_equations : ('a, 'b) atom -> ('a, 'b) Subst.t -> ('a, 'b) Subst.t -> string

(** {3 Term.Modulo.syntactic_equations_of_equations} *)

val data_IO_Term_Modulo_syntactic_equations_of_equations : data_IO

val apply_Term_Modulo_syntactic_equations_of_equations : Modulo.equation list -> string
