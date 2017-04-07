open Term

let x_var = Variable.fresh_with_label Existential Variable.fst_ord_type "x"
let y_var = Variable.fresh_with_label Existential Variable.fst_ord_type "y"
let z_var = Variable.fresh_with_label Existential Variable.fst_ord_type "z"

let x = of_variable x_var
let y = of_variable y_var
let z = of_variable z_var

let h = Symbol.new_constructor 1 "h"
let g = Symbol.new_constructor 2 "g"
let f = Symbol.new_constructor 2 "f"

let a_name = Name.fresh_with_label Public "a"
let b_name = Name.fresh_with_label Public "b"

let a = of_name a_name
let b = of_name b_name

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

let ded_1 = Fact.create_deduction_fact (of_axiom (Axiom.create 2)) (apply_function aenc [a;y])
let ded_2 = Fact.create_deduction_fact (of_axiom (Axiom.create 2)) (apply_function aenc [a;b])
let ded_3 = Fact.create_deduction_fact (of_axiom (Axiom.create 2)) (apply_function enc [a;y])


let test_generic ded f k =
  let skel_list = Rewrite_rules.skeletons (Fact.get_protocol_term ded) f k in
  List.iter (fun skel ->
    let _ = Rewrite_rules.generic_rewrite_rules_formula ded skel in
    ()
  ) skel_list


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

  Testing_functions.publish ()
