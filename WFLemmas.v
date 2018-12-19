Require Import Coq.Strings.String.
Require Import Omega.

Require Import Termination.Syntax.
Require Import Termination.Tactics.
Require Import Termination.AssocList.
Require Import Termination.Sets.
Require Import Termination.ListUtils.

Open Scope string_scope.
Open Scope list_scope.

Lemma wf_monotone:
  forall t, forall k k', wf t k -> k <= k' -> wf t k'.
Proof.
  induction t;
    repeat match goal with
           | _ => step
           | IH: forall x, _, H: wf ?t ?k |- wf ?t ?k1 => apply IH with k
           end;
    try omega.
Qed.

Hint Resolve wf_monotone: bwf.

Lemma wf_monotone2: forall t, forall k, wf t k -> wf t (S k).
Proof.
  eauto with bwf.
Qed.

Hint Immediate wf_monotone2: bwf.

Lemma wf_monotone2_type: forall T, forall k, wf T k -> wf T (S k).
Proof.
  eauto with bwf.
Qed.

Hint Immediate wf_monotone2_type: bwf.

Lemma open_none:
  forall t k rep, wf t k -> open k t rep = t.
Proof.
  induction t;
    repeat light || tequality || step; try omega.
Qed.

Lemma wfs_lookup:
  forall gamma x T k,
    wfs gamma k ->
    lookup Nat.eq_dec gamma x = Some T ->
    wf T k.
Proof.
  induction gamma; steps; eauto.
Qed.

Hint Resolve wfs_lookup: bwf.

Lemma wfs_next: forall l k,
    wfs l k ->
    wfs l (S k).
Proof.
  induction l; steps; eauto with bwf.
Qed.

Hint Resolve wfs_next: bwf.

Lemma wfs_append:
  forall l1 l2 k,
    wfs l1 k ->
    wfs l2 k ->
    wfs (l1 ++ l2) k.
Proof.
  induction l1; steps; eauto.
Qed.

Hint Resolve wfs_append: bwf.

Lemma wf_open_rev:
  forall t rep k, wf (open k t rep) k -> wf t (S k).
Proof.
  induction t; repeat step || eapply_any.
Qed.

Hint Resolve wf_open_rev: bwf.

Lemma wf_topen_rev:
  forall t rep i k, wf (topen i t rep) k -> wf t k.
Proof.
  induction t; repeat step || eapply_any.
Qed.

Hint Resolve wf_topen_rev: bwft.

Lemma wf_open:
  forall t rep k, wf t (S k) -> wf rep k -> wf (open k t rep) k.
Proof.
  induction t; repeat step || apply_any; try omega; eauto 3 with bwf.
Qed.

Hint Resolve wf_open: bwf.

Lemma wf_topen:
  forall t rep i k, wf t k -> wf rep k -> wf (topen i t rep) k.
Proof.
  induction t; repeat step || apply_any; try omega; eauto 3 with bwf.
Qed.

Hint Resolve wf_topen: bwft.

Lemma wf_subst:
  forall t l k tag,
    wf t k ->
    wfs l k ->
    wf (psubstitute t l tag) k.
Proof.
  induction t; repeat steps; eauto 4 with bwf.
Qed.

Hint Resolve wf_subst: bwf.
