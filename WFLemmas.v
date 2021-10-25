Require Import Coq.Strings.String.
Require Import PeanoNat.
Require Import Psatz.

Require Export SystemFR.Syntax.

Open Scope string_scope.
Open Scope list_scope.

Lemma wf_var:
  forall n k, wf (fvar n term_var) k.
Proof. steps. Qed.

#[global]
Hint Resolve wf_var: wf.

Lemma wf_monotone:
  forall t, forall k k', wf t k -> k <= k' -> wf t k'.
Proof.
  induction t; steps;
    try solve [ eapply_any; try eassumption; try lia ];
    try lia.
Qed.

#[global]
Hint Extern 1 => solve [ eapply wf_monotone; try eassumption; try lia ]: wf.

Lemma wf_monotone2: forall t k, wf t k -> wf t (S k).
Proof.
  intros; eauto 1 with wf.
Qed.

#[global]
Hint Immediate wf_monotone2: wf.

Lemma wf_monotone3: forall t k, wf t 0 -> wf t k.
Proof.
  eauto with wf.
Qed.

#[global]
Hint Resolve wf_monotone3: wf.

Lemma open_none:
  forall t k rep, wf t k -> open k t rep = t.
Proof.
  induction t;
    try solve [ repeat light || t_equality || step; try lia ].
Qed.

(* rewrite in H works, but not rewrite in `*` *)
Ltac open_none :=
  match goal with
  | H: _ |- _ => rewrite open_none in H by eauto with wf
  | H: _ |- _ => rewrite (open_none _ 1) in H by eauto with wf
  | H: _ |- _ => rewrite (open_none _ 2) in H by eauto with wf
  | H: _ |- _ => rewrite (open_none _ 3) in H by eauto with wf
  | H: _ |- _ => rewrite (open_none _ 4) in H by eauto with wf
  | _ => rewrite open_none by eauto with wf
  | _ => rewrite (open_none _ 1) by eauto with wf
  | _ => rewrite (open_none _ 2) by eauto with wf
  | _ => rewrite (open_none _ 3) by eauto with wf
  | _ => rewrite (open_none _ 4) by eauto with wf
  end.

Ltac open_none_by t :=
  match goal with
  | H: _ |- _ => rewrite open_none in H by t
  | H: _ |- _ => rewrite (open_none _ 1) in H by t
  | H: _ |- _ => rewrite (open_none _ 2) in H by t
  | H: _ |- _ => rewrite (open_none _ 3) in H by t
  | H: _ |- _ => rewrite (open_none _ 4) in H by t
  | _ => rewrite open_none by t
  | _ => rewrite (open_none _ 1) by t
  | _ => rewrite (open_none _ 2) by t
  | _ => rewrite (open_none _ 3) by t
  | _ => rewrite (open_none _ 4) by t
  end.

Lemma wfs_monotone:
  forall l, forall k k', wfs l k -> k <= k' -> wfs l k'.
Proof.
  induction l; steps; eauto 2 with wf.
Qed.

#[global]
Hint Extern 1 => solve [ eapply wfs_monotone; try eassumption; try lia ]: wf.

Lemma wfs_monotone2: forall l k,
    wfs l k ->
    wfs l (S k).
Proof.
  intros; eauto 1 with wf.
Qed.

#[global]
Hint Immediate wfs_monotone2: wf.

Lemma wfs_lookup:
  forall Γ x T k,
    wfs Γ k ->
    lookup PeanoNat.Nat.eq_dec Γ x = Some T ->
    wf T k.
Proof.
  induction Γ; steps; eauto.
Qed.

#[global]
Hint Immediate wfs_lookup: wf.

Lemma wfs_lookup2:
  forall Γ x T k,
    wfs Γ 0 ->
    lookup PeanoNat.Nat.eq_dec Γ x = Some T ->
    wf T k.
Proof.
  intros; eauto using wfs_lookup with wf.
Qed.

#[global]
Hint Immediate wfs_lookup2: wf.

Lemma wfs_append:
  forall l1 l2 k,
    wfs l1 k ->
    wfs l2 k ->
    wfs (l1 ++ l2) k.
Proof.
  induction l1; steps; eauto.
Qed.

#[global]
Hint Resolve wfs_append: wf.

Lemma wf_open_rev:
  forall t rep k, wf (open k t rep) k -> wf t (S k).
Proof.
  induction t; repeat step || eapply_any.
Qed.

#[global]
Hint Immediate wf_open_rev: wf.

Lemma wf_topen_rev:
  forall t rep i k, wf (topen i t rep) k -> wf t k.
Proof.
  induction t; repeat step || eapply_any.
Qed.

#[global]
Hint Immediate wf_topen_rev: wf.

Lemma wf_open:
  forall t rep k, wf t (S k) -> wf rep k -> wf (open k t rep) k.
Proof.
  induction t; repeat step || apply_any; try lia; eauto 1 with wf.
Qed.

#[global]
Hint Resolve wf_open: wf.

Lemma wf_topen:
  forall t rep i k, wf t k -> wf rep k -> wf (topen i t rep) k.
Proof.
  induction t; repeat step || apply_any; try lia; eauto 1 with wf.
Qed.

#[global]
Hint Resolve wf_topen: wf.

Lemma wf_subst:
  forall t l k tag,
    wf t k ->
    wfs l k ->
    wf (psubstitute t l tag) k.
Proof.
  induction t; repeat step || apply_any; eauto with wf.
Qed.

#[global]
Hint Resolve wf_subst: wf.

Lemma wf_build_nat:
  forall n k,
    wf (build_nat n) k.
Proof.
  induction n; steps.
Qed.

#[global]
Hint Resolve wf_build_nat: wf.

Lemma wf_fvar: forall x tag k, wf (fvar x tag) k.
Proof.
  repeat light.
Qed.

#[export]
Hint Resolve wf_fvar : wf.
