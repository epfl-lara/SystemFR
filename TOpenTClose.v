From Stdlib Require Import String.
From Stdlib Require Import Psatz.

Require Export SystemFR.TWFLemmas.
Require Export SystemFR.SubstitutionLemmas.
Require Export SystemFR.FVLemmas.

Open Scope string_scope.
Open Scope list_scope.

Opaque PeanoNat.Nat.eq_dec.

Lemma open_close:
  forall t rep x k,
    wf t k ->
    open k (close k t x) rep = psubstitute t ((x, rep) :: nil) term_var.
Proof.
  induction t;
    repeat step || t_equality || list_utils; eauto with lia.
Qed.

Lemma open_close2:
  forall t x k,
    wf t k ->
    open k (close k t x) (fvar x term_var) = t.
Proof.
  induction t;
    repeat step || t_equality || list_utils; eauto with lia.
Qed.

Lemma topen_tclose:
  forall T rep x k,
    twf T k ->
    topen k (tclose k T x) rep = psubstitute T ((x, rep) :: nil) type_var.
Proof.
  induction T;
    repeat step || t_equality || list_utils; eauto with lia.
Qed.

Lemma topen_tclose2:
  forall T X k,
    twf T k ->
    topen k (tclose k T X) (fvar X type_var) = T.
Proof.
  induction T;
    repeat step || t_equality || list_utils; eauto with lia.
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
  induction A; repeat step || t_equality || apply_any || list_utils;
    eauto with twf lia.
  - rewrite topen_tclose;
      repeat step || fv_open || list_utils || apply twf_topen;
      eauto with twf lia.
    + rewrite substitute_topen3; steps.
      rewrite substitute_nothing; steps.
      rewrite topen_none; steps; eauto with twf.
      apply twf_monotone with 0; eauto with twf lia.
    + apply twf_monotone with 0; try lia.
      apply twf_topen; steps.
Qed.
