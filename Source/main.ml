open Term
open Data_structure

(** Rewriting system **)

let x_var = Variable.fresh_with_label Existential Variable.fst_ord_type "x"
let y_var = Variable.fresh_with_label Existential Variable.fst_ord_type "y"
let z_var = Variable.fresh_with_label Existential Variable.fst_ord_type "z"

let x = of_variable x_var
let y = of_variable y_var
let z = of_variable z_var

let h = Symbol.new_constructor 1 "h"
let g = Symbol.new_constructor 2 "g"
let f = Symbol.new_constructor 2 "f"

let enc = Symbol.new_constructor 2 "enc"

let dec = Symbol.new_destructor 2 "dec"
  [
    ([apply_function enc [x;y]; y], x)
  ]

let pk = Symbol.new_constructor 1 "pk"
let aenc = Symbol.new_constructor 2 "aenc"

let adec = Symbol.new_destructor 2 "adec"
  [
    ([apply_function aenc [x;apply_function pk [y]]; y], x)
  ]

let vk = Symbol.new_constructor 1 "vk"
let sign = Symbol.new_constructor 2 "sign"

let check = Symbol.new_destructor 2 "check"
  [
    ([apply_function sign [x;y]; apply_function vk [y]], x)
  ]

let blind = Symbol.new_constructor 2 "blind"

let unblind = Symbol.new_destructor 2 "unblind"
  [
    ([apply_function sign [apply_function blind [x;y];z]; y], apply_function sign [x;z])
  ]

let dest = Symbol.new_destructor 2 "dest"
  [
    ([apply_function h [x]; y], apply_function f [x; y]);
    ([apply_function g [x;y]; y], apply_function h [x])
  ]

(** Next **)

let x_var = Variable.fresh Protocol Existential Variable.fst_ord_type
let y_var = Variable.fresh Protocol Existential Variable.fst_ord_type
let z_var = Variable.fresh Protocol Existential Variable.fst_ord_type

let x = of_variable x_var
let y = of_variable y_var
let z = of_variable z_var

let a_name = Name.fresh_with_label Public "a"
let b_name = Name.fresh_with_label Public "b"

let a = of_name a_name
let b = of_name b_name

let ded_1 = Fact.create_deduction_fact (of_axiom (Axiom.create 2)) (apply_function aenc [a;y])
let ded_2 = Fact.create_deduction_fact (of_axiom (Axiom.create 2)) (apply_function aenc [a;b])
let ded_3 = Fact.create_deduction_fact (of_axiom (Axiom.create 2)) (apply_function enc [a;y])


let test_generic ded f k =
  let skel_list = Rewrite_rules.skeletons (Fact.get_protocol_term ded) f k in
  List.iter (fun skel ->
    let _ = Rewrite_rules.generic_rewrite_rules_formula ded skel in
    ()
  ) skel_list


(********** Test of consequence ***********)

let test_partial_consequence () =
  let _X_var = Variable.fresh Recipe Free (Variable.snd_ord_type 0) in
  let _Y_var = Variable.fresh Recipe Free (Variable.snd_ord_type 0) in

  let _X = of_variable _X_var in
  let _Y = of_variable _Y_var in

  let bdf_1 = BasicFact.create _Y_var y in
  let bdf_2 = BasicFact.create _X_var b in

  let ax_1 = of_axiom (Axiom.create 1) in
  let ax_2 = of_axiom (Axiom.create 2) in
  let ax_3 = of_axiom (Axiom.create 3) in
  let ax_4 = of_axiom (Axiom.create 4) in

  let ded_1 = Fact.create_deduction_fact ax_1 (apply_function h [a]) in
  let ded_2 = Fact.create_deduction_fact (apply_function dec [ax_1;_Y]) (apply_function f [a;x]) in
  let ded_3 = Fact.create_deduction_fact (apply_function dec [apply_function g [_X;_Y]; ax_1]) (apply_function f [y;a]) in

  let df_0 = DF.empty in
  let df_1 = DF.add df_0 bdf_1 in
  let df_2 = DF.add df_1 bdf_2 in

  let sdf_0 = SDF.empty in
  let sdf_1 = SDF.add sdf_0 ded_1 in
  let sdf_2 = SDF.add sdf_1 ded_2 in
  let sdf_3 = SDF.add sdf_2 ded_3 in

  let t1 = apply_function h [a] in
  let t2 = apply_function f [a;y] in
  let t3 = apply_function h [b] in
  let t4 = apply_function h [apply_function f [b;y]] in
  let t5 = apply_function h [apply_function f [a;x]] in
  let t6 = apply_function h [apply_function h [a]] in
  let t7 = apply_function h [apply_function f [apply_function h [b];apply_function f [y;a]]] in

  let _ = Tools.partial_consequence Protocol sdf_3 df_2 t1 in
  let _ = Tools.partial_consequence Protocol sdf_3 df_2 t2 in
  let _ = Tools.partial_consequence Protocol sdf_3 df_2 t3 in
  let _ = Tools.partial_consequence Protocol sdf_3 df_2 t4 in
  let _ = Tools.partial_consequence Protocol sdf_3 df_2 t5 in
  let _ = Tools.partial_consequence Protocol sdf_3 df_2 t6 in
  let _ = Tools.partial_consequence Protocol sdf_3 df_2 t7 in

  let uniset_0 = Uniformity_Set.empty in
  let uniset_1 = Uniformity_Set.add uniset_0 ax_2 (apply_function h [b]) in
  let uniset_2 = Uniformity_Set.add uniset_1 ax_3 (apply_function f [y;a]) in
  let uniset_3 = Uniformity_Set.add uniset_2 ax_4 (apply_function f [a;y]) in

  let _ = Tools.uniform_consequence sdf_3 df_2 uniset_3 t1 in
  let _ = Tools.uniform_consequence sdf_3 df_2 uniset_3 t2 in
  let _ = Tools.uniform_consequence sdf_3 df_2 uniset_3 t3 in
  let _ = Tools.uniform_consequence sdf_3 df_2 uniset_3 t4 in
  let _ = Tools.uniform_consequence sdf_3 df_2 uniset_3 t5 in
  let _ = Tools.uniform_consequence sdf_3 df_2 uniset_3 t6 in
  let _ = Tools.uniform_consequence sdf_3 df_2 uniset_3 t7 in

  let r1 = ax_1 in
  let r2 = apply_function dec [ax_1; _Y] in
  let r3 = apply_function h [_X] in
  let r4 = apply_function h [apply_function f [_X;_Y]] in
  let r5 = apply_function dec [apply_function f [_X;_Y]; ax_1] in
  let r6 = apply_function h [ax_1] in
  let r7 = apply_function dec [apply_function g [apply_function h [_X]; _Y]; _Y] in

  let _ = Tools.partial_consequence Recipe sdf_3 df_2 r1 in
  let _ = Tools.partial_consequence Recipe sdf_3 df_2 r2 in
  let _ = Tools.partial_consequence Recipe sdf_3 df_2 r3 in
  let _ = Tools.partial_consequence Recipe sdf_3 df_2 r4 in
  let _ = Tools.partial_consequence Recipe sdf_3 df_2 r5 in
  let _ = Tools.partial_consequence Recipe sdf_3 df_2 r6 in
  let _ = Tools.partial_consequence Recipe sdf_3 df_2 r7 in

  let _Z_var = Variable.fresh Recipe Free (Variable.snd_ord_type 1) in

  let _Z = of_variable _X_var in

  let bdf_3 = BasicFact.create _Z_var a in

  let _ = Tools.partial_consequence_additional Protocol sdf_3 df_2 [bdf_3] t1 in
  let _ = Tools.partial_consequence_additional Protocol sdf_3 df_2 [bdf_3] t2 in
  let _ = Tools.partial_consequence_additional Protocol sdf_3 df_2 [bdf_3] t3 in
  let _ = Tools.partial_consequence_additional Protocol sdf_3 df_2 [bdf_3] t4 in
  let _ = Tools.partial_consequence_additional Protocol sdf_3 df_2 [bdf_3] t5 in
  let _ = Tools.partial_consequence_additional Protocol sdf_3 df_2 [bdf_3] t6 in
  let _ = Tools.partial_consequence_additional Protocol sdf_3 df_2 [bdf_3] t7 in

  let _ = Tools.partial_consequence_additional Recipe sdf_3 df_2 [bdf_3] r1 in
  let _ = Tools.partial_consequence_additional Recipe sdf_3 df_2 [bdf_3] r2 in
  let _ = Tools.partial_consequence_additional Recipe sdf_3 df_2 [bdf_3] r3 in
  let _ = Tools.partial_consequence_additional Recipe sdf_3 df_2 [bdf_3] r4 in
  let _ = Tools.partial_consequence_additional Recipe sdf_3 df_2 [bdf_3] r5 in
  let _ = Tools.partial_consequence_additional Recipe sdf_3 df_2 [bdf_3] r6 in
  let _ = Tools.partial_consequence_additional Recipe sdf_3 df_2 [bdf_3] r7 in
  ()


let _ =
  Testing_load_verify.load ();
  Testing_functions.update ();

  let _ = Rewrite_rules.skeletons x dest 4 in
  let _ = Rewrite_rules.skeletons x dec 2 in
  let _ = Rewrite_rules.skeletons x adec 5 in
  let _ = Rewrite_rules.skeletons x check 7 in
  let _ = Rewrite_rules.skeletons x unblind 9 in
  let _ = Rewrite_rules.skeletons (apply_function aenc [x;y]) adec 5 in
  let _ = Rewrite_rules.skeletons (apply_function aenc [x;y]) dest 5 in

  test_generic ded_1 adec 3;
  test_generic ded_1 dec 3;
  test_generic ded_2 adec 3;
  test_generic ded_2 dec 4;
  test_generic ded_3 adec 7;
  test_generic ded_3 dec 1;

  test_partial_consequence ();

  Testing_functions.publish ();
  Testing_load_verify.publish_index ()
