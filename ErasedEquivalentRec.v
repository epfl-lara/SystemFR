Require Export SystemFR.EquivalentStar.

Lemma equivalent_rec:
  forall t v tn t0 ts,
    is_nat_value v ->
    star scbv_step tn v ->
    is_erased_term tn ->
    is_erased_term t0 ->
    is_erased_term ts ->
    wf tn 0 ->
    wf t0 0 ->
    wf ts 2 ->
    pfv tn term_var = nil ->
    pfv t0 term_var = nil ->
    pfv ts term_var = nil ->
    (v = zero -> equivalent_terms t0 t) ->
    (forall v', v = succ v' ->
           equivalent_terms (open 0 (open 1 ts v') (notype_lambda (notype_rec v' t0 ts))) t) ->
    equivalent_terms (notype_rec tn t0 ts) t.
Proof.
  inversion 1; repeat step || t_invert_star;
    try solve [ eapply equivalent_trans; try eassumption; equivalent_star ].
Qed.

Lemma equivalent_rec_zero:
  forall n e1 e2,
    is_erased_term n ->
    is_erased_term e1 ->
    is_erased_term e2 ->
    wf n 0 ->
    wf e1 0 ->
    wf e2 2 ->
    pfv n term_var = nil ->
    pfv e1 term_var = nil ->
    pfv e2 term_var = nil ->
    star scbv_step n zero ->
    equivalent_terms (notype_rec n e1 e2) e1.
Proof.
  intros; apply equivalent_star; repeat step || list_utils;
    eauto using star_trans with smallstep cbvlemmas.
Qed.

Lemma equivalent_rec_zero2:
  forall n e1 e2 e,
    star scbv_step n zero ->
    equivalent_terms (notype_rec n e1 e2) e ->
    equivalent_terms e1 e.
Proof.
  intros.
  eapply equivalent_trans; try eassumption.
  apply equivalent_sym.
  apply equivalent_rec_zero; unfold equivalent_terms in *; repeat step || list_utils.
Qed.

Lemma equivalent_rec_succ:
  forall n e1 e2 v,
    is_erased_term n ->
    is_erased_term e1 ->
    is_erased_term e2 ->
    is_erased_term v ->
    wf n 0 ->
    wf e1 0 ->
    wf e2 2 ->
    wf v 0 ->
    pfv n term_var = nil ->
    pfv e1 term_var = nil ->
    pfv e2 term_var = nil ->
    cbv_value v ->
    star scbv_step n (succ v) ->
    equivalent_terms (notype_rec n e1 e2)
                     (open 0 (open 1 e2 v) (notype_lambda (notype_rec v e1 e2))).
Proof.
  intros.
  apply equivalent_star; repeat step || list_utils;
    eauto using star_trans, star_one with cbvlemmas smallstep.
Qed.

Lemma equivalent_rec_succ2:
  forall n e1 e2 v e,
    cbv_value v ->
    is_erased_term v ->
    wf v 0 ->
    star scbv_step n (succ v) ->
    equivalent_terms (notype_rec n e1 e2) e ->
    equivalent_terms (open 0 (open 1 e2 v) (notype_lambda (notype_rec v e1 e2))) e.
Proof.
  intros.
  eapply equivalent_trans; try eassumption.
  apply equivalent_sym.
  apply equivalent_rec_succ; unfold equivalent_terms in *; repeat step || list_utils.
Qed.
