Require Import Termination.Syntax.
Require Import Termination.TypeErasure.
Require Import Termination.Tactics.
Require Import Termination.Sets.
Require Import Termination.SetLemmas.
Require Import Termination.ListUtils.

Lemma fv_erase:
  forall t, subset (fv (erase t)) (fv t).
Proof.
  induction t;
    repeat step || t_listutils || rewrite <- subset_union3;
      eauto using union_right1, union_right2, subset_transitive.
Qed.

Hint Resolve fv_erase: bfv.

Lemma fv_erase2:
  forall t, fv t = nil -> fv (erase t) = nil.
Proof.
  induction t; repeat step || t_listutils || rewrite_any .
Qed.

Hint Resolve fv_erase2: bfv.
