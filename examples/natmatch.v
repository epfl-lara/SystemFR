Require Export SystemFR.Notations.
Require Export SystemFR.Evaluator.
Require Extraction.
Import Notations.UnTyped.


Definition natmatch_example := Eval compute in
  [|
   let pred :=
       def_rec ack m =>
       match m with
       | 0 => 0
       | s m' => m'
       end
   in
   pred 9
    |].


Example natmatch : (eval natmatch_example 1000) =  Some [| 8 |].
Proof.
  native_compute; reflexivity. Qed.

(* Extraction *)
Extraction Language Ocaml.
Set Extraction AccessOpaque.
Extraction "natmatch.ml" natmatch_example eval.
