Require Export SystemFR.LiftEquivalenceLemmas.

Lemma equivalent_match:
  forall t v tn t0 ts,
    is_nat_value v ->
    star scbv_step tn v ->
    is_erased_term tn ->
    is_erased_term t0 ->
    is_erased_term ts ->
    wf tn 0 ->
    wf t0 0 ->
    wf ts 1 ->
    (v = zero -> equivalent_terms t0 t) ->
    (forall v', v = succ v' -> equivalent_terms (open 0 ts v') t) ->
    equivalent_terms (tmatch tn t0 ts) t.
Proof.
  inversion 1; repeat step || t_invert_star;
    try solve [ eapply equivalent_trans; try eassumption; equivalent_star ].
Qed.

Lemma equivalent_match_zero:
  forall n e1 e2,
    is_erased_term n ->
    is_erased_term e1 ->
    is_erased_term e2 ->
    wf n 0 ->
    wf e1 0 ->
    wf e2 1 ->
    star scbv_step n zero ->
    equivalent_terms (tmatch n e1 e2) e1.
Proof.
  eauto using equivalent_star, star_trans with cbvlemmas smallstep step_tactic.
Qed.

Lemma equivalent_match_zero2:
  forall n e1 e2 e,
    star scbv_step n zero ->
    equivalent_terms (tmatch n e1 e2) e ->
    equivalent_terms e1 e.
Proof.
  intros.
  eapply equivalent_trans; try eassumption.
  apply equivalent_sym.
  apply equivalent_match_zero; unfold equivalent_terms in *; steps.
Qed.

Lemma equivalent_match_succ:
  forall n e1 e2 v,
    is_erased_term n ->
    is_erased_term e1 ->
    is_erased_term e2 ->
    is_erased_term v ->
    wf n 0 ->
    wf e1 0 ->
    wf e2 1 ->
    wf v 0 ->
    cbv_value v ->
    star scbv_step n (succ v) ->
    equivalent_terms (tmatch n e1 e2) (open 0 e2 v).
Proof.
  intros.
  apply equivalent_star; steps;
    eauto using star_trans, star_one with cbvlemmas smallstep.
Qed.

Lemma equivalent_match_succ2:
  forall n e1 e2 v e,
    cbv_value v ->
    is_erased_term v ->
    wf v 0 ->
    star scbv_step n (succ v) ->
    equivalent_terms (tmatch n e1 e2) e ->
    equivalent_terms (open 0 e2 v) e.
Proof.
  intros.
  eapply equivalent_trans; try eassumption.
  apply equivalent_sym.
  apply equivalent_match_succ; unfold equivalent_terms in *; steps.
Qed.
