Require Export SystemFR.Notations.
Require Export SystemFR.Evaluator.
Require Extraction.
Import Notations.UnTyped.


Fixpoint natToTreeNat (n: nat) := match n with
                                 | 0 => zero
                                 | S x => succ (natToTreeNat x) end.

Definition sumAcc_example := Eval compute in 
  [|
   let plus := (
       def_rec f x y =>
       match x with
       | 0 => y
       | s x' => s (f x' y) end) in
   let sumAcc := def_rec f acc v => match v with
                                   | left x => acc
                                   | right x => f (plus x acc) end
   in
   let sum := sumAcc 0 in
   sumAcc 0 (right 5) (right 2) (left ())
    |].


Eval compute in eval sumAcc_example 1000.


Extraction Language Ocaml.
Set Extraction AccessOpaque.
Extraction "sumAcc.ml" sumAcc_example eval. 


