Require Export SystemFR.Notations.
Import Notations.UnTyped.
Require Export SystemFR.Evaluator.
Require Extraction.


Definition lists := Eval compute in
 [|


  let nil := (left ()) in
  let cons := fun x => fun xs => (right (x,xs)) in
  let one := cons () nil in
  let two := cons () one in
  let three := cons () two in
  let four := cons () three in
  let five := cons () four in
  let six := cons () five in
  let seven := cons () six in
  let eight := cons () seven in
  let nine := cons () eight in
  let ten := cons () nine in
  let double := def_rec f l => match l with
                              | left x => nil
                              | right p => right ((), (right ((), (f (p._2))))) end in
  let power := def_rec f a b => match b with
                               | left x => a
                               | right p => f (double a) (p._2) end in
  let getLast := def_rec f l => match l with
                               | left x => ()
                               |right p => f (p._2) end in
  getLast (power ten ten)

|].

(* power a b = a*2^b *)


Example example1 : (eval lists 1000000) = Some (uu).
Proof.
  Set Ltac Profiling.
  native_compute.
  reflexivity.
  Show Ltac Profile.
  Qed.



Extraction Language OCaml.
Set Extraction AccessOpaque.
Extraction "list_perf.ml" lists eval.
