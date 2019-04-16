Require Import Coq.Strings.String.
Require Import Omega.

Require Import SystemFR.Syntax.
Require Import SystemFR.Tactics.
Require Import SystemFR.AssocList.
Require Import SystemFR.Sets.
Require Import SystemFR.ListUtils.
Require Import SystemFR.SmallStep.

Open Scope string_scope.
Open Scope list_scope.

Lemma twf_monotone:
  forall t, forall k k', twf t k -> k <= k' -> twf t k'.
Proof.
  induction t;
    repeat match goal with
           | _ => step
           | IH: forall x, _, H: twf ?t ?k |- twf ?t ?k1 => apply IH with k
           end;
    try omega.
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
    repeat step || t_equality; try omega.
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
  induction t; repeat step || eapply_any.
Qed.

Hint Resolve twf_topen_rev: btwf.

Lemma twf_open_rev:
  forall t rep i k, twf (open i t rep) k -> twf t k.
Proof.
  induction t; repeat step || eapply_any.
Qed.

Hint Resolve twf_open_rev: btwf2.

Lemma twf_topen:
  forall t rep k, twf t (S k) -> twf rep k -> twf (topen k t rep) k.
Proof.
  induction t; repeat step || apply_any; try omega; eauto with btwf.
Qed.

Hint Resolve twf_topen: btwf.

Lemma twf_open:
  forall t rep i k, twf t k -> twf rep k -> twf (open i t rep) k.
Proof.
  induction t; repeat step || apply_any || omega; eauto with btwf.
Qed.

Hint Resolve twf_open: btwf2.

Lemma twf_subst:
  forall t l k tag,
    twf t k ->
    twfs l k ->
    twf (psubstitute t l tag) k.
Proof.
  induction t; repeat steps; eauto with btwf.
Qed.

Hint Resolve twf_subst: btwf.

Ltac t_topen_none :=
  match goal with
  | H1: twf ?T ?k, H2: context[topen ?k ?T ?rep] |- _ => rewrite (topen_none T k rep H1) in H2
  | H1: twf ?T ?k |- context[topen ?k ?T ?rep] => rewrite (topen_none T k rep H1)
  | H1: is_erased_term ?T, H2: context[topen ?k ?T ?rep] |- _ =>
    rewrite (topen_none T k rep) in H2 by (steps; eauto with btwf)
  | H1: is_erased_term ?T |- context[topen ?k ?T ?rep] =>
    rewrite (topen_none T k rep) by (steps; eauto with btwf)
  | H1: is_erased_term ?T, H2: context[topen ?k (open ?k' ?T ?rep') ?rep] |- _ =>
    rewrite (topen_none (open k' T rep') k rep) in H2
      by (repeat steps || apply twf_open; eauto 2 with btwf)
  | H1: is_erased_term ?T |- context[topen ?k (open ?k' ?T ?rep') ?rep] =>
    rewrite (topen_none (open k' T rep') k rep) by (repeat steps || apply twf_open; eauto 2 with btwf)
  end.
