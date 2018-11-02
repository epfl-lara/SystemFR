Require Import Termination.Tactics.
Require Import Termination.Syntax.
Require Import Termination.TermList.
Require Import Termination.TypeList.
Require Import Termination.WFLemmas.

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

Lemma closed_types_wfs:
  forall l k,
    closed_terms l ->
    wfs l k.
Proof.
  induction l; steps; eauto with bwf omega.
Qed.

Hint Resolve closed_types_wfs: bwf.

Lemma closed_types_twfs:
  forall l k,
    closed_terms l ->
    twfs l k.
Proof.
  induction l; steps; eauto with btwf omega.
Qed.

Hint Resolve closed_types_twfs: btwf.
