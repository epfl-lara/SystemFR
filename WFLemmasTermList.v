Require Import Termination.Tactics.
Require Import Termination.Syntax.
Require Import Termination.TermList.
Require Import Termination.WFLemmas.

Lemma satisfies_wfs:
  forall p l gamma,
    satisfies p gamma l ->
    wfs l 0.
Proof.
  induction l; repeat step || step_inversion satisfies; eauto with bwf.
Qed.

Hint Resolve satisfies_wfs: bwf.

Lemma satisfies_wfs_1:
  forall p l gamma,
    satisfies p  gamma l ->
    wfs l 1.
Proof.
  steps; eauto with bwf.
Qed.

Hint Resolve satisfies_wfs_1: bwf.
