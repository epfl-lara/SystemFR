Require Import Coq.Strings.String.
Require Import Omega.

Require Import Termination.Syntax.
Require Import Termination.Tactics.
Require Import Termination.AssocList.
Require Import Termination.Sets.
Require Import Termination.ListUtils.
Require Import Termination.TWFLemmas.
Require Import Termination.SubstitutionLemmas.
Require Import Termination.FVLemmas.
Require Import Termination.WellFormed.

Open Scope string_scope.
Open Scope list_scope.

Opaque Nat.eq_dec.

Lemma topen_tclose:
  forall T rep x k,
    twf T k ->
    topen k (tclose k T x) rep = psubstitute T ((x, rep) :: nil) type_var.
Proof.
  induction T;
    repeat step || tequality || t_listutils; eauto with omega.
Qed.

(*
  topen 0 (topen 1 A (topen 0 B R)) R =
  topen k (tclose 0 (topen 1 A (topen 0 B X))) R
*)

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
  induction A; repeat step || tequality || apply_any || t_listutils;
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
