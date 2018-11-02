Require Import Coq.Strings.String.
Require Import Omega.

Require Import Termination.Syntax.
Require Import Termination.Tactics.
Require Import Termination.AssocList.
Require Import Termination.Sets.
Require Import Termination.ListUtils.

Open Scope string_scope.
Open Scope list_scope.

Lemma twf_monotone:
  forall t, forall k k', twf t k -> k <= k' -> twf t k'.
Proof.
  induction t; repeat step; eauto with omega.
Qed.

Hint Resolve twf_monotone: btwf.

Lemma twf_monotone2: forall t, forall k, twf t k -> twf t (S k).
Proof.
  eauto with btwf.
Qed.

Hint Immediate twf_monotone2: btwf.

Lemma twf_monotone2_type: forall T, forall k, twf T k -> twf T (S k).
Proof.
  eauto with btwf.
Qed.

Hint Immediate twf_monotone2_type: btwf.

Lemma topen_none:
  forall t k rep, twf t k -> topen k t rep = t.
Proof.
  induction t;
    repeat step || f_equal; eauto with omega.
Qed.

Lemma twfs_lookup:
  forall gamma x T k,
    twfs gamma k ->
    lookup Nat.eq_dec gamma x = Some T ->
    twf T k.
Proof.
  induction gamma; steps; eauto.
Qed.

Hint Resolve twfs_lookup: btwf.

Lemma twfs_next: forall l k,
    twfs l k ->
    twfs l (S k).
Proof.
  induction l; steps; eauto with btwf.
Qed.

Hint Resolve twfs_next: btwf.

Lemma twfs_append:
  forall l1 l2 k,
    twfs l1 k ->
    twfs l2 k ->
    twfs (l1 ++ l2) k.
Proof.
  induction l1; steps; eauto.
Qed.

Hint Resolve twfs_append: btwf.

Lemma twf_topen_rev:
  forall t rep k, twf (topen k t rep) k -> twf t (S k).
Proof.
  induction t;
    try solve [ repeat step; eauto ].
Qed.

Hint Resolve twf_topen_rev: btwf.

Lemma twf_open_rev:
  forall t rep i k, twf (open i t rep) k -> twf t k.
Proof.
  induction t;
    try solve [ repeat step; eauto].
Qed.

Hint Resolve twf_open_rev: btwf2.

Lemma twf_topen:
  forall t rep k, twf t (S k) -> twf rep k -> twf (topen k t rep) k.
Proof.
  induction t; repeat step || apply_any || omega; eauto with btwf.
Qed.

Hint Resolve twf_topen: btwf.

Lemma twf_open:
  forall t rep i k, twf t k -> twf rep k -> twf (open i t rep) k.
Proof.
  induction t; repeat step || apply_any || omega; eauto with btwf.
Qed.

Hint Resolve twf_open: btwf2.

Lemma wf_subst:
  forall t l k tag,
    twf t k ->
    twfs l k ->
    twf (psubstitute t l tag) k.
Proof.
  induction t; repeat steps; eauto with btwf.
Qed.

Hint Resolve wf_subst: btwf.
