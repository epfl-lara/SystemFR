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
  induction t; repeat step; eauto with omega.
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
    repeat step || f_equal; eauto with omega; eauto with bwf.
Qed.

(*
Lemma open_fun_late:
  (forall T k rep, wf T k -> open_fun k T rep = T) /\
  (forall t k rep, wf t k -> open_fun k t rep = t).
Proof.
  apply type_ind; 
    repeat step || tequality || t_typeequality; eauto with omega; eauto with bwf.
Qed.

Definition open_fun_late_type := proj1 open_fun_late.
Definition open_fun_late := proj2 open_fun_late.
*)

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
  induction t; repeat step; eauto.
Qed.

Hint Resolve wf_open_rev: bwf.

Lemma wf_open:
  forall t rep k, wf t (S k) -> wf rep k -> wf (open k t rep) k. 
Proof.
  induction t;
    repeat match goal with
           | H: _ |- _ => apply H
           | _ => step || omega
           end; eauto with bwf.
Qed.

Hint Resolve wf_open: bwf.

Lemma wf_subst:
  forall t l k,
    wf t k ->
    wfs l k ->
    wf (substitute t l) k.
Proof.
  induction t; steps; eauto with bwf.
Qed.

Hint Resolve wf_subst: bwf.
