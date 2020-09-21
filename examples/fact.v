Require Export SystemFR.Notations.
Require Export SystemFR.Evaluator.
Require Extraction.
Import Notations.UnTyped.


Definition fact_example := Eval compute in
  [|
   let plus :=
       def_rec plus x y =>
       match x with
       | 0 => y
       | s x' => s (plus x' y) end
   in
   let mult :=
       def_rec mult x y =>
       match x with
       | 0 => 0
       | s x' => plus y (mult x' y) end
   in
   let fact :=
       def_rec fact n =>
       match n with
       | 0 => 1
       | s n' => mult n (fact n') end
   in
   fact 7
    |].

Fixpoint treeToNat (t: tree) :=
  match t with
  | zero => 0
  | succ t' => S (treeToNat t')
  | _ => 0
  end.


Example fact : (option_map treeToNat (eval fact_example 30000)) = Some 5040.
Proof.
  native_compute. reflexivity. Qed.

(*
(* Extraction *)
Extraction Language Ocaml.
Set Extraction AccessOpaque.
Extraction "fact.ml" fact_example eval.
*)
