Require Export SystemFR.Notations.
Require Export SystemFR.Evaluator.
Require Extraction.
Import Notations.UnTyped.


Definition natEq_example := Eval compute in 
  [|
   let natEq := (
         def_rec f x y =>
         match x with
         | 0 => (match y with
               | 0 => t_true
               | s y' => t_false end)
         | s x' =>(
           match y with
           | 0 =>  t_false
           | s y' => (f x' y')
           end)
         end) in
   natEq 0 (s 0) |].


Print natEq_example.


Extraction Language Ocaml.
Set Extraction AccessOpaque.

Definition result := (eval natEq_example 1000).
Extraction "isEven.ml" result eval. 

Definition ex1 :=[| let f := def_rec f x => (s x) in f (f (f 0)) |]. 
Eval compute in ex1.
Eval compute in eval ex1 10.
