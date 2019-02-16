Require Import Termination.Tactics.
Require Import Termination.Syntax.
Require Import Termination.TermList.
Require Import Termination.WFLemmas.
Require Import Termination.WellFormed.

Lemma satisfies_wfs:
  forall p lterms gamma k,
    satisfies p gamma lterms ->
    wfs lterms k.
Proof.
  induction lterms; repeat step || step_inversion satisfies; eauto with bwf omega.
Qed.

Hint Resolve satisfies_wfs: bwf.

Lemma satisfies_twfs:
  forall p lterms gamma k,
    satisfies p gamma lterms ->
    twfs lterms k.
Proof.
  induction lterms; repeat step || step_inversion satisfies; eauto with btwf omega.
Qed.

Hint Resolve satisfies_twfs: btwf.
