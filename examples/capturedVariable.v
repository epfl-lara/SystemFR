Require Export SystemFR.Notations.
Require Export SystemFR.Evaluator.
Require Extraction.
Import Notations.UnTyped.


Definition capturedVariable_example := Eval compute in 
  [|    
   let lt := def_rec f x y =>
             match x with
             | 0 => t_true
             | s x' => match y with
                      | 0 => t_false
                      | s y' => (f x' y') end end in
   
   let x := 5 in
   let lessThanX := fun y => (lt y x) in
   let x := 3 in
   let y := 4 in
   ((lessThanX x), (lessThanX y))
   |].


Eval compute in eval capturedVariable_example 1000.


Extraction Language Ocaml.
Set Extraction AccessOpaque.
Extraction "capturedVariable.ml" capturedVariable_example eval. 
