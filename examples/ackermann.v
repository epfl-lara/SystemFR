Require Export SystemFR.Notations.
Require Export SystemFR.Evaluator.
Require Extraction.
Import Notations.UnTyped.


Definition ackermann_example := Eval compute in
  [|
   let ackermann :=
       def_rec ack m n =>
       match m with
       | 0 => (s n)
       | s m' => match n with
                | 0 => ack m' 1
                | s n' => ack m' (ack m n') end
       end
   in
   ackermann 2 2
    |].


Eval compute in eval ackermann_example 1000.

Example ackermann : (eval ackermann_example 1000) =  Some (succ (succ (succ (succ (succ (succ (succ zero))))))). (* 7 *)
Proof.
  native_compute; reflexivity. Qed.

(* Extraction *)
Extraction Language Ocaml.
Set Extraction AccessOpaque.
Extraction "ackermann.ml" ackermann_example eval.
