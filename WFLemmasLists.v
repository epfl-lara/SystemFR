Require Export SystemFR.TermList.
Require Export SystemFR.WFLemmas.

Lemma satisfies_wfs:
  forall p lterms gamma k,
    satisfies p gamma lterms ->
    wfs lterms k.
Proof.
  induction lterms; repeat step || step_inversion satisfies; eauto with wf omega.
Qed.

Hint Resolve satisfies_wfs: wf.

Lemma satisfies_twfs:
  forall p lterms gamma k,
    satisfies p gamma lterms ->
    twfs lterms k.
Proof.
  induction lterms; repeat step || step_inversion satisfies; eauto with btwf omega.
Qed.

Hint Resolve satisfies_twfs: btwf.
