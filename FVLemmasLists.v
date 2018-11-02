
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.

Require Import Termination.Syntax.
Require Import Termination.Tactics.
Require Import Termination.TermProperties.
Require Import Termination.Sets.
Require Import Termination.AssocList.
Require Import Termination.FVLemmas.
Require Import Termination.TermList.
Require Import Termination.TypeList.
Require Import Termination.ListUtils.

Lemma satisfies_closed_mapping:
  forall P lterms gamma,
    satisfies P gamma lterms ->
    closed_mapping lterms.
Proof.
  induction lterms; repeat step || step_inversion satisfies; eauto.
Qed.

Hint Resolve satisfies_closed_mapping: bfv.

Lemma closed_mapping_append1:
  forall l1 l2,
    closed_mapping (l1 ++ l2) ->
    closed_mapping l1.
Proof.
  induction l1; steps; eauto.
Qed.

Lemma closed_mapping_append2:
  forall l1 l2,
    closed_mapping (l1 ++ l2) ->
    closed_mapping l2.
Proof.
  induction l1; steps.
Qed.

Hint Resolve closed_mapping_append1: b_cmap.
Hint Resolve closed_mapping_append2: b_cmap.

Lemma closed_mapping_append:
  forall l1 l2,
    closed_mapping l1 ->
    closed_mapping l2 ->
    closed_mapping (l1 ++ l2).
Proof.
  induction l1; steps.
Qed.

Hint Resolve closed_mapping_append: b_cmap.

Lemma closed_types_fvs:
  forall ltypes,
    closed_types ltypes ->
    closed_mapping ltypes.
Proof.
  induction ltypes; steps.
Qed.

Hint Resolve closed_types_fvs: b_cmap.

Lemma satisfies_fv_nil:
  forall P gamma lterms,
    satisfies P gamma lterms ->
    forall t,
      t ∈ range lterms ->
      fv t = nil.  
Proof.
  steps; eauto with bfv.
Qed.

Hint Resolve satisfies_fv_nil: bfv.

Lemma fv_satisfies_nil:
  forall P gamma lterms t,
    satisfies P gamma lterms ->
    subset (fv t) (support gamma) ->
    fv (substitute t lterms) = nil.
Proof.
  repeat step || t_termlist || t_listutils || apply fv_nils2 || rewrite_any;
    eauto with bfv b_cmap.
Qed.

Hint Resolve fv_satisfies_nil: bfv.
