Require Export SystemFR.Notations.
Import Notations.UnTyped.


Definition streams_example := Eval compute in 
      [|
 let eq_nat := (
         def_rec f x y =>
         match x with
         | 0 => match y with
               | 0 => t_true
               | s y' => t_false end
         | s x' =>
           match y with
           | 0 =>  t_false
           | s y' => (f x' y')
           end
         end) in
 let plus := (
       def_rec f x y =>
       match x with
       | 0 => y
       |s x' => f x' y end)
 in
        
 let nil  := left () in
 let cons := fun x => fun xs => right ((x,xs)) in
 let head := fun l => (l ())._1 in
 let tail := fun l => (l ())._2 in
 let constant := def_rec f x => (fun y => right ((x, (f x) ()))) in 
 let sum := def_rec f k stream => match k with
                                 | 0 => 0
                                 | s k' => let x := stream () in (
                                      plus x._1 (f k' x._2)) end in

 let map := def_rec f g stream => fun y => (g (head stream), f g (tail stream)) in
 let zipwith := def_rec f app s1 => fun s2 => fun y => ((app (head s1) (head s2)), (f (tail s1) (tail s2))) in
 let take := def_rec f k stream => match k with
                           | 0 => nil
                                   | s k' => cons (head stream) (f k' (tail stream)) end in 
 let fibonacci := def_rec f y => (0, fun y => (1, zipwith plus f (tail f)))
                                  in take 0 fibonacci |].
Print streams_example.


Require Export SystemFR.Evaluator.


Require Extraction.

Extraction Language OCaml.
(* Set Extraction AccessOpaque.*)

Extraction "streams_example.ml" streams_example eval.
