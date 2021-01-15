Require Export SystemFR.TermList.
Require Export SystemFR.WFLemmas.

Lemma satisfies_wfs:
  forall p lterms Γ k,
    satisfies p Γ lterms ->
    wfs lterms k.
Proof.
  induction lterms; repeat step || step_inversion satisfies; eauto with wf lia.
Qed.

#[global]
Hint Immediate satisfies_wfs: wf.

Lemma satisfies_twfs:
  forall p lterms Γ k,
    satisfies p Γ lterms ->
    twfs lterms k.
Proof.
  induction lterms; repeat step || step_inversion satisfies; eauto with twf lia.
Qed.

#[global]
Hint Immediate satisfies_twfs: twf.
