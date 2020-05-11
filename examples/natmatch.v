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


Eval compute in eval natmatch_example 1000.


Extraction Language Ocaml.
Set Extraction AccessOpaque.
Extraction "natmatch.ml" natmatch_example eval. 
