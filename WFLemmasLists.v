Require Import Termination.Tactics.
Require Import Termination.Syntax.
Require Import Termination.TermList.
Require Import Termination.TypeList.
Require Import Termination.WFLemmas.

Lemma satisfies_wfs:
  forall p lterms gamma,
    satisfies p gamma lterms ->
    wfs lterms 0.
Proof.
  induction lterms; repeat step || step_inversion satisfies; eauto with bwf.
Qed.

Hint Resolve satisfies_wfs: bwf.

Lemma satisfies_wfs_1:
  forall p lterms gamma,
    satisfies p gamma lterms ->
    wfs lterms 1.
Proof.
  steps; eauto with bwf.
Qed.

Hint Resolve satisfies_wfs_1: bwf.

Lemma closed_types_wfs:
  forall ltypes,
    closed_types ltypes ->
    wfs ltypes 0.
Proof.
  induction ltypes; steps.
Qed.

Hint Resolve closed_types_wfs: bwf.
