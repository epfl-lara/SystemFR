Require Export SystemFR.NatRecognizer.
Require Export SystemFR.EquivalentStar.

Lemma equivalent_value_nat:
  forall v v',
    cbv_value v ->
    is_nat_value v' ->
    equivalent_terms v v' ->
    v = v'.
Proof.
  intros.
  equivalence_instantiate (nat_recognizer v'); steps;
    eauto using is_erased_term_nat_recognizer, wf_nat_recognizer, fv_nat_recognizer.

  unshelve epose proof (H5 _);
    unfold scbv_normalizing; eauto using eval_nat_recognizer with values;
    eauto using eq_sym, normalizing_nat_recognizer.
Qed.


Lemma equivalent_nat:
  forall t v,
    is_nat_value v ->
    equivalent_terms t v ->
    star scbv_step t v.
Proof.
  intros.
  equivalence_instantiate (lvar 0 term_var); steps.
  unshelve epose proof (H4 _); unfold scbv_normalizing; steps; eauto with star values.
  unfold scbv_normalizing in *; repeat step || t_invert_star; eauto with values.
  unshelve epose proof (equivalent_value_nat v1 v0 _ _ _);
    repeat step;
    eauto using equivalent_star, equivalent_trans, equivalent_sym.

  eapply equivalent_trans; eauto.
  top_level_unfold equivalent_terms; repeat step || destruct_and;
    eauto using equivalent_star, equivalent_sym.
Qed.

Lemma equivalent_star_nat:
  forall t t' v,
    is_nat_value v ->
    equivalent_terms t t' ->
    star scbv_step t v ->
    star scbv_step t' v.
Proof.
  intros.
  pose proof H0 as HH; unfold equivalent_terms in HH; steps;
    eauto using equivalent_nat, equivalent_star, equivalent_trans, equivalent_sym.
Qed.
