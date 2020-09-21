Require Export SystemFR.NatRecognizer.
Require Export SystemFR.EquivalentStar.

Lemma equivalent_value_nat:
  forall v v',
    cbv_value v ->
    is_nat_value v' ->
    [ v ≡ v' ] ->
    v = v'.
Proof.
  intros.
  equivalence_instantiate (nat_recognizer v'); steps;
    eauto using is_erased_term_nat_recognizer, wf_nat_recognizer, fv_nat_recognizer.

  unshelve epose proof (H5 _);
    repeat step;
    eauto using eval_nat_recognizer;
    eauto using true_nat_recognizer, eq_sym.
Qed.

Lemma equivalent_nat:
  forall t v,
    is_nat_value v ->
    [ t ≡ v ] ->
    t ~>* v.
Proof.
  intros.
  apply_anywhere equivalent_sym.
  eapply_anywhere equivalent_normalizing; eauto with star values;
    repeat step.
  apply_anywhere equivalent_sym.
  apply_anywhere equivalent_value_nat; steps.
Qed.

Lemma equivalent_star_nat:
  forall t t' v,
    is_nat_value v ->
    [ t ≡ t' ] ->
    t ~>* v ->
    t' ~>* v.
Proof.
  intros.
  pose proof H0 as HH; unfold equivalent_terms in HH; steps;
    eauto using equivalent_nat, equivalent_star, equivalent_trans, equivalent_sym.
Qed.
