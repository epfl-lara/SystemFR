Require Export SystemFR.Notations.
Import Notations.UnTyped.
Require Export SystemFR.Evaluator.
Require Extraction.


Definition streams_example := Eval compute in
  fun n => [|
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
       | s x' => s (f x' y) end) in

 (* Stream: a function that returns a pair (head, stream) *)
 let constant := def_rec f x => (fun y => ((x, (f x)))) in
 let head := (fun l => ((l ())._1)) in
 let tail := (fun l => ((l ())._2)) in
 let sum :=
     def_rec f k stream =>
     match k with
     | 0 => 0
     | s k' => let x := stream () in (
                plus (x._1) (f k' (x._2))) end in
 let take := def_rec f k stream => match k with
                           | 0 => (head stream)
                           | s k' => (f k' (tail stream))  end in
 let zipwith := def_rec f app s1 => fun s2 => fun y => ((app (head s1) (head s2)), (f app (tail s1) (tail s2))) in
 let fibonacci := def_rec f y => (1, (fun y => (1, (zipwith plus f (tail f))))) in

 (take n fibonacci)  |].



Fixpoint natToTreeNat (n: nat) := match n with
                                 | 0 => zero
                                 | S x => succ (natToTreeNat x) end.

(*
Extraction Language OCaml.
Set Extraction AccessOpaque.
Extraction "streams_example.ml" streams_example eval natToTreeNat.
*)
