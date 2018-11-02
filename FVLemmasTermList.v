
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.

Require Import Termination.Syntax.
Require Import Termination.Tactics.
Require Import Termination.TermProperties.
Require Import Termination.Sets.
Require Import Termination.AssocList.
Require Import Termination.FVLemmas.
Require Import Termination.TermList.

Lemma satisfies_closed_mapping:
  forall P l gamma,
    satisfies P gamma l ->
    closed_mapping l.
Proof.
  induction l; repeat step || step_inversion satisfies; eauto.
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

Lemma satisfies_fv_nil:
  forall P gamma l,
    satisfies P gamma l ->
    forall t,
      t ∈ range l ->
      fv t = nil.  
Proof.
  steps; eauto with bfv.
Qed.

Hint Resolve satisfies_fv_nil: bfv.

Lemma fv_satisfies_nil:
  forall P gamma l t,
    satisfies P gamma l ->
    subset (fv t) (support gamma) ->
    fv (substitute t l) = nil.
Proof.
  repeat step || tlist; eauto 4 with sets bfv.
Qed.

Hint Resolve fv_satisfies_nil: bfv.
