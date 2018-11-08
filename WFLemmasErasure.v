Require Import Termination.Syntax.
Require Import Termination.TypeErasure.
Require Import Termination.Tactics.

(*
Lemma wf_erase:
  forall t k, wf t k -> wf (erase t) k.
Proof.
  induction t; steps.
Qed.

Hint Resolve wf_erase: bwf.
*)