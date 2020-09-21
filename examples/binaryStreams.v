Require Export SystemFR.Notations.
Import Notations.UnTyped.
Require Export SystemFR.Evaluator.
Require Extraction.


Definition streams_example := Eval compute in
 [|


  let nil := (left ()) in
  let cons := fun x => fun xs => (right (x,xs)) in
  let one := cons () nil in
  let double := def_rec f l => match l with
                              | left x => nil
                              | right p => right ((), (right ((), (f (p._2))))) end
  in
  let power := def_rec f a b => match b with
                               | left x => a
                               | right p => f (double a) (p._2) end in

  let getLast := def_rec f l => match l with
                               | left x => nil
                                            |right p => f (p._2) end in

  getLast (power one (double (double (double (double one)))))|].


Eval compute in (eval streams_example 30000).


         (* Stream: a function that returns a pair (head, stream) *)

 let constant := def_rec f x => (fun y => ((x, (f x)))) in
 let head := (fun l => ((l ())._1)) in
 let tail := (fun l => ((l ())._2)) in

 let one := (fun l => (1, (constant 0)) in

 let double := def_rec f stream y => (

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
