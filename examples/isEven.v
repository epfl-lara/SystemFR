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
   let boolAnd := (fun a => fun b => if (a) then b else t_false) in
   let oddEven := def_rec f p x => match p with
                                 | 0 => match x with
                                       | 0 => t_true
                                       | s x' => f 1 x' end
                                 | s p' => match x with
                                          | 0 => t_false
                                          | s x' => f 0 x'
                                          end
                                 end
   in
   let oddEven1 := def_rec f x => (
                     (match x with | 0 => t_true  | s x' => ((f x')._2) end),
                     (match x with | 0 => t_false | s x' => ((f x')._1) end)
                   ) in
   let isEven := oddEven 0 in
   let isOdd := oddEven 1 in
   let isEven1 := (fun x => ((oddEven1 x)._1)) in
   let isOdd1 := (fun x => ((oddEven1 x)._2)) in

   boolAnd (isEven 0)
           (boolAnd (isEven1 0)
                    (boolAnd (isOdd 1)
                             (boolAnd (isOdd1 1)
                                      (boolAnd (isEven 2)
                                               (boolAnd (isEven1 2)
                                                        (boolAnd (isOdd 3)
                                                                 (isOdd1 3)))))))
    |].


Print natEq_example.


Extraction Language Ocaml.
Set Extraction AccessOpaque.

Definition isEven := natEq_example.
Extraction "isEven.ml" isEven eval. 
