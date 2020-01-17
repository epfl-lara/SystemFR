Require Import Coq.Strings.String.
Require Import Omega.

Require Export SystemFR.Syntax.
Require Export SystemFR.Tactics.
Require Export SystemFR.AssocList.

Require Export SystemFR.ListUtils.


Open Scope string_scope.
Open Scope list_scope.

Lemma wf_monotone:
  forall t, forall k k', wf t k -> k <= k' -> wf t k'.
Proof.
  induction t; steps; eauto 2 with omega.
Qed.

Hint Resolve wf_monotone: wf.

Lemma wf_monotone2: forall t, forall k, wf t k -> wf t (S k).
Proof.
  eauto 3 with wf.
Qed.

Hint Immediate wf_monotone2: wf.

Lemma wf_monotone2_type: forall T, forall k, wf T k -> wf T (S k).
Proof.
  eauto with wf.
Qed.

Hint Immediate wf_monotone2_type: wf.

Lemma open_none:
  forall t k rep, wf t k -> open k t rep = t.
Proof.
  induction t;
    try solve [ repeat light || t_equality || step; try omega ].
Qed.

Lemma wfs_lookup:
  forall gamma x T k,
    wfs gamma k ->
    lookup Nat.eq_dec gamma x = Some T ->
    wf T k.
Proof.
  induction gamma; steps; eauto.
Qed.

Hint Resolve wfs_lookup: wf.

Lemma wfs_next: forall l k,
    wfs l k ->
    wfs l (S k).
Proof.
  induction l; steps; eauto with wf.
Qed.

Hint Resolve wfs_next: wf.

Lemma wfs_append:
  forall l1 l2 k,
    wfs l1 k ->
    wfs l2 k ->
    wfs (l1 ++ l2) k.
Proof.
  induction l1; steps; eauto.
Qed.

Hint Resolve wfs_append: wf.

Lemma wf_open_rev:
  forall t rep k, wf (open k t rep) k -> wf t (S k).
Proof.
  induction t; repeat step || eapply_any.
Qed.

Hint Resolve wf_open_rev: wf.

Lemma wf_topen_rev:
  forall t rep i k, wf (topen i t rep) k -> wf t k.
Proof.
  induction t; repeat step || eapply_any.
Qed.

Hint Resolve wf_topen_rev: wft.

Lemma wf_open:
  forall t rep k, wf t (S k) -> wf rep k -> wf (open k t rep) k.
Proof.
  induction t; repeat step || apply_any; try omega; eauto 3 with wf.
Qed.

Hint Resolve wf_open: wf.

Lemma wf_topen:
  forall t rep i k, wf t k -> wf rep k -> wf (topen i t rep) k.
Proof.
  induction t; repeat step || apply_any; try omega; eauto 3 with wf.
Qed.

Hint Resolve wf_topen: wft.

Lemma wf_subst:
  forall t l k tag,
    wf t k ->
    wfs l k ->
    wf (psubstitute t l tag) k.
Proof.
  induction t; repeat steps; eauto 4 with wf.
Qed.

Hint Resolve wf_subst: wf.

