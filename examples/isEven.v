Require Export SystemFR.Notations.
Require Export SystemFR.Evaluator.
Require Extraction.
Import Notations.UnTyped.


Definition natEq_example := Eval compute in 
  [|
   let natEq := (
         def_rec nat_eq x y =>
         match x with
         | 0 => match y with
               | 0 => t_true
               | s y' => t_false end
         | s x' =>
           match y with
           | 0 =>  t_false
           | s y' => (nat_eq x' y')
           end
         end) in
   natEq 0 (s 0) |].


Print natEq_example.


Extraction Language Ocaml.
Set Extraction AccessOpaque.

Definition result := (eval natEq_example 1000).
Extraction "isEven.ml" result. (* Fails with : Fetching opaque proofs from disk for SystemFR.Evaluator
Error: The value you are asking for (getApp) is not available in this process. If you really need this, pass the
"-async-proofs off" option to CoqIDE to disable asynchronous script processing and don't pass "-quick" to coqc *)

