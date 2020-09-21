Require Export SystemFR.Notations.
Require Export SystemFR.Evaluator.
Require Extraction.
Import Notations.UnTyped.


Definition capturedVariable2_example := Eval compute in
   [|
    let minus := def_rec f x y => match y with
                                 | 0 => x
                                 |s y' => match x with
                                         | 0 => 0
                                         | s x' => (f x' y') end
                                 end
    in
    let double := def_rec f x => match x with
                                | 0 => 0
                                | s x' => (s (s (f x'))) end
    in
    let x := (
         let x := 5 in
         let f := fun x => (double x) in
         let x := (f x) in
         minus x x) in
    x
    |].



Example capturedVariable2 : (eval capturedVariable2_example 1000) =  Some zero.
Proof.
  native_compute ; reflexivity. Qed.

(*
(* Extraction *)
Extraction Language Ocaml.
Set Extraction AccessOpaque.
Extraction "capturedVariable2.ml" capturedVariable2_example eval.
*)
