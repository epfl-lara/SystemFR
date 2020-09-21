Require Export SystemFR.Notations.
Import Notations.UnTyped.
Require Export SystemFR.Evaluator.
Require Extraction.


Definition streams := Eval compute in
 [|

  let head := fun stream => ((stream ())._1) in
  let tail := fun stream => ((stream ())._2) in
  let before := fun val => fun stream => fun y => (val, stream) in
  let constant := def_rec f x y => (x, (f x)) in

  let zero := (constant t_false) in
  let one := before t_true zero in
  let two := before t_true one in
  let three := before t_true two in
  let four := before t_true three in
  let five := before t_true four in
  let six := before t_true five in
  let seven := before t_true six in
  let eight := before t_true seven in
  let nine := before t_true eight in

  let double := def_rec f st y => (
                  let head := (st ()) in
                  if (head._1) then
                    (t_true,(before t_true (f (head._2))))
                  else
                    (t_false, st)
                ) in
  let power := def_rec f st1 st2 => (fun y => (
                 let head := (st2 ()) in
                 if (head._1) then
                   (f (double st1) (head._2))
                 else
                   st1 () )) in

  let count := def_rec f st => (
                 let head := (st ()) in
                 if (head._1) then s (f (head._2)) else 0) in
  let getLast := def_rec f st => (
                   let head := (st ()) in
                   if (head._1) then (f (head._2)) else ()) in
  (getLast (power seven seven))
  |].


Eval native_compute in (eval streams 20000).


Example example1 : (eval streams 100000) = Some (uu).
Proof.
  Set Ltac Profiling.
  native_compute.
  Show Ltac Profile.
  reflexivity.
  Qed.


(* Extraction *)
Extraction Language OCaml.
Set Extraction AccessOpaque.
Extraction "streams_perf.ml" streams eval.
