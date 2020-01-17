Require Export SystemFR.LiftEquivalenceLemmas.

Lemma equivalent_ite_true:
  forall b e1 e2,
    is_erased_term b ->
    is_erased_term e1 ->
    is_erased_term e2 ->
    wf b 0 ->
    wf e1 0 ->
    wf e2 0 ->
    star scbv_step b ttrue ->
    equivalent_terms (ite b e1 e2) e1.
Proof.
  eauto using equivalent_star, star_trans with cbvlemmas smallstep step_tactic.
Qed.

Lemma equivalent_ite_false:
  forall b e1 e2,
    is_erased_term b ->
    is_erased_term e1 ->
    is_erased_term e2 ->
    wf b 0 ->
    wf e1 0 ->
    wf e2 0 ->
    star scbv_step b tfalse ->
    equivalent_terms (ite b e1 e2) e2.
Proof.
  eauto using equivalent_star, star_trans with cbvlemmas smallstep step_tactic.
Qed.

Lemma equivalent_ite:
  forall t1 t2 t3 t,
    is_erased_term t1 ->
    is_erased_term t2 ->
    is_erased_term t3 ->
    wf t1 0 ->
    wf t2 0 ->
    wf t3 0 ->
    (star scbv_step t1 ttrue \/ star scbv_step t1 tfalse) ->
    (star scbv_step t1 ttrue -> equivalent_terms t2 t) ->
    (star scbv_step t1 tfalse -> equivalent_terms t3 t) ->
    equivalent_terms (ite t1 t2 t3) t.
Proof.
  steps; eauto using equivalent_ite_true, equivalent_ite_false, equivalent_sym, equivalent_trans.
Qed.

Lemma equivalent_ite_true2:
  forall b e1 e2 e,
    is_erased_term b ->
    is_erased_term e1 ->
    is_erased_term e2 ->
    wf b 0 ->
    wf e1 0 ->
    wf e2 0 ->
    star scbv_step b ttrue ->
    equivalent_terms e1 e ->
    equivalent_terms (ite b e1 e2) e.
Proof.
  eauto using equivalent_ite_true, equivalent_sym, equivalent_trans.
Qed.

Lemma equivalent_ite_false2:
  forall b e1 e2 e,
    is_erased_term b ->
    is_erased_term e1 ->
    is_erased_term e2 ->
    wf b 0 ->
    wf e1 0 ->
    wf e2 0 ->
    star scbv_step b tfalse ->
    equivalent_terms (ite b e1 e2) e ->
    equivalent_terms e2 e.
Proof.
  eauto using equivalent_ite_false, equivalent_sym, equivalent_trans.
Qed.

Lemma equivalent_ite_true3:
  forall b e1 e2 e,
    star scbv_step b ttrue ->
    equivalent_terms (ite b e1 e2) e ->
    equivalent_terms e1 e.
Proof.
  intros.
  eapply equivalent_trans; try eassumption.
  apply equivalent_sym.
  apply equivalent_ite_true; unfold equivalent_terms in *; steps.
Qed.

Lemma equivalent_ite_false3:
  forall b e1 e2 e,
    star scbv_step b tfalse ->
    equivalent_terms (ite b e1 e2) e ->
    equivalent_terms e2 e.
Proof.
  intros.
  eapply equivalent_trans; try eassumption.
  apply equivalent_sym.
  apply equivalent_ite_false; unfold equivalent_terms in *; steps.
Qed.
