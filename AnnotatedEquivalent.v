Require Export SystemFR.Judgments.
Require Export SystemFR.AnnotatedTactics.
Require Export SystemFR.EquivalentStar.
Require Export SystemFR.TermListReducible.
Require Export SystemFR.SubstitutionErase.

Lemma annotated_equivalent_refl:
   forall tvars gamma t,
     is_erased_term t ->
     wf t 0 ->
     subset (fv t) (support gamma) ->
    [[ tvars; gamma ⊨ t ≡ t ]].
Proof.
  unfold annotated_equivalent, equivalent; repeat step;
    eauto using equivalent_refl with erased wf fv.

  apply equivalent_refl; eauto with erased wf fv.
  apply fv_nils2; repeat step || t_subset_erase || t_termlist;
    side_conditions;
    try solve [ rewrite_any; auto ].
Qed.

Lemma annotated_equivalent_trans:
  forall tvars gamma t1 t2 t3,
    [[ tvars; gamma ⊨ t1 ≡ t2 ]] ->
    [[ tvars; gamma ⊨ t2 ≡ t3 ]] ->
    [[ tvars; gamma ⊨ t1 ≡ t3 ]].
Proof.
  unfold annotated_equivalent, equivalent; steps;
    eauto using equivalent_trans.
Qed.

Lemma annotated_equivalent_sym:
  forall tvars gamma t1 t2,
    [[ tvars; gamma ⊨ t1 ≡ t2 ]] ->
    [[ tvars; gamma ⊨ t2 ≡ t1 ]].
Proof.
  unfold annotated_equivalent, equivalent; steps;
    eauto using equivalent_sym.
Qed.
