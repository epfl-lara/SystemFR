Require Import Coq.Strings.String.
Require Import PeanoNat.
Require Import Psatz.

Require Export SystemFR.Syntax.

Open Scope string_scope.
Open Scope list_scope.

Lemma twf_monotone:
  forall t, forall k k', twf t k -> k <= k' -> twf t k'.
Proof.
  induction t; steps;
    try solve [ eapply_any; try eassumption; try lia ];
    try lia.
Qed.

#[export]
Hint Extern 1 => solve [ eapply twf_monotone; try eassumption; try lia ]: twf.

Lemma twf_monotone2: forall t, forall k, twf t k -> twf t (S k).
Proof.
  intros; eauto 1 with twf.
Qed.

#[export]
Hint Immediate twf_monotone2: twf.

Lemma topen_none:
  forall t k rep, twf t k -> topen k t rep = t.
Proof.
  induction t;
    try solve [ repeat light || t_equality || step; try lia ].
Qed.

Lemma twfs_lookup:
  forall Γ x T k,
    twfs Γ k ->
    lookup PeanoNat.Nat.eq_dec Γ x = Some T ->
    twf T k.
Proof.
  induction Γ; steps; eauto.
Qed.

#[export]
Hint Immediate twfs_lookup: twf.

Lemma twfs_monotone:
  forall l, forall k k', twfs l k -> k <= k' -> twfs l k'.
Proof.
  induction l; steps; eauto 2 with twf.
Qed.

#[export]
Hint Extern 1 => solve [ eapply twfs_monotone; try eassumption; try lia ]: twf.

Lemma twfs_monotone2: forall l k,
    twfs l k ->
    twfs l (S k).
Proof.
  intros; eauto 1 with twf.
Qed.

#[export]
Hint Immediate twfs_monotone2: twf.

Lemma twfs_append:
  forall l1 l2 k,
    twfs l1 k ->
    twfs l2 k ->
    twfs (l1 ++ l2) k.
Proof.
  induction l1; steps; eauto.
Qed.

#[export]
Hint Resolve twfs_append: twf.

Lemma twf_topen_rev:
  forall t rep k, twf (topen k t rep) k -> twf t (S k).
Proof.
  induction t; repeat step || eapply_any.
Qed.

#[export]
Hint Immediate twf_topen_rev: twf.

Lemma twf_open_rev:
  forall t rep i k, twf (open i t rep) k -> twf t k.
Proof.
  induction t; repeat step || eapply_any.
Qed.

#[export]
Hint Immediate twf_open_rev: twf.

Lemma twf_topen:
  forall t rep k, twf t (S k) -> twf rep k -> twf (topen k t rep) k.
Proof.
  induction t; repeat step || apply_any; try lia; eauto 1 with twf.
Qed.

#[export]
Hint Resolve twf_topen: twf.

Lemma twf_open:
  forall t rep i k, twf t k -> twf rep k -> twf (open i t rep) k.
Proof.
  induction t; repeat step || apply_any; try lia; eauto 1 with twf.
Qed.

#[export]
Hint Resolve twf_open: twf.

Lemma twf_subst:
  forall t l k tag,
    twf t k ->
    twfs l k ->
    twf (psubstitute t l tag) k.
Proof.
  induction t; repeat step || apply_any; eauto with twf.
Qed.

#[export]
Hint Resolve twf_subst: twf.

Ltac topen_none :=
  match goal with
  | H1: twf ?T ?k, H2: context[topen ?k ?T ?rep] |- _ => rewrite (topen_none T k rep H1) in H2
  | H1: twf ?T ?k |- context[topen ?k ?T ?rep] => rewrite (topen_none T k rep H1)
  | H1: is_erased_term ?T, H2: context[topen ?k ?T ?rep] |- _ =>
    rewrite (topen_none T k rep) in H2 by (steps; eauto with twf)
  | H1: is_erased_term ?T |- context[topen ?k ?T ?rep] =>
    rewrite (topen_none T k rep) by (steps; eauto with twf)
  | H1: is_erased_term ?T, H2: context[topen ?k (open ?k' ?T ?rep') ?rep] |- _ =>
    rewrite (topen_none (open k' T rep') k rep) in H2
      by (repeat steps || apply twf_open; eauto 2 with twf)
  | H1: is_erased_term ?T |- context[topen ?k (open ?k' ?T ?rep') ?rep] =>
    rewrite (topen_none (open k' T rep') k rep) by (repeat steps || apply twf_open; eauto 2 with twf)
  end.
