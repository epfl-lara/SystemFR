Require Import Coq.Strings.String.
Require Import Omega.

Require Import SystemFR.Syntax.
Require Import SystemFR.Tactics.
Require Import SystemFR.AssocList.
Require Import SystemFR.Sets.
Require Import SystemFR.ListUtils.
Require Import SystemFR.TWFLemmas.
Require Import SystemFR.SubstitutionLemmas.
Require Import SystemFR.FVLemmas.


Open Scope string_scope.
Open Scope list_scope.

Opaque Nat.eq_dec.

Lemma open_close:
  forall t rep x k,
    wf t k ->
    open k (close k t x) rep = psubstitute t ((x, rep) :: nil) term_var.
Proof.
  induction t;
    repeat step || t_equality || t_listutils; eauto with omega.
Qed.

Lemma open_close2:
  forall t x k,
    wf t k ->
    open k (close k t x) (fvar x term_var) = t.
Proof.
  induction t;
    repeat step || t_equality || t_listutils; eauto with omega.
Qed.

Lemma topen_tclose:
  forall T rep x k,
    twf T k ->
    topen k (tclose k T x) rep = psubstitute T ((x, rep) :: nil) type_var.
Proof.
  induction T;
    repeat step || t_equality || t_listutils; eauto with omega.
Qed.

Lemma topen_tclose2:
  forall T X k,
    twf T k ->
    topen k (tclose k T X) (fvar X type_var) = T.
Proof.
  induction T;
    repeat step || t_equality || t_listutils; eauto with omega.
Qed.

Lemma topen_twice:
  forall A B R X k,
    ~(X ∈ pfv A type_var) ->
    ~(X ∈ pfv B type_var) ->
    twf A (S (S k)) ->
    twf B 1 ->
    twf R 0 ->
      topen k (topen (S k) A (topen 0 B R)) R =
      topen k (tclose k (topen (S k) A (topen 0 B (fvar X type_var))) X) R.
Proof.
  induction A; repeat step || t_equality || apply_any || t_listutils;
    eauto with btwf omega.
  - rewrite topen_tclose;
      repeat step || t_fv_open || t_listutils || apply twf_topen;
      eauto with btwf omega.
    + rewrite substitute_topen3; steps.
      rewrite substitute_nothing; steps.
      rewrite topen_none; steps; eauto with btwf.
      apply twf_monotone with 0; eauto with btwf omega.
    + apply twf_monotone with 0; try omega.
      apply twf_topen; steps.
Qed.
