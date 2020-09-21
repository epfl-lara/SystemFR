Require Export SystemFR.EquivalentStar.

Lemma equivalent_ite_true:
  forall b e1 e2,
    is_erased_term b ->
    is_erased_term e1 ->
    is_erased_term e2 ->
    wf b 0 ->
    wf e1 0 ->
    wf e2 0 ->
    pfv b term_var = nil ->
    pfv e1 term_var = nil ->
    pfv e2 term_var = nil ->
    b ~>* ttrue ->
    [ ite b e1 e2 ≡ e1 ].
Proof.
  intros; eapply equivalent_star; repeat step || list_utils;
    eauto using star_trans with cbvlemmas smallstep.
Qed.

Lemma equivalent_ite_false:
  forall b e1 e2,
    is_erased_term b ->
    is_erased_term e1 ->
    is_erased_term e2 ->
    wf b 0 ->
    wf e1 0 ->
    wf e2 0 ->
    pfv b term_var = nil ->
    pfv e1 term_var = nil ->
    pfv e2 term_var = nil ->
    b ~>* tfalse ->
    [ ite b e1 e2 ≡ e2 ].
Proof.
  intros; eapply equivalent_star; repeat step || list_utils;
    eauto using star_trans with cbvlemmas smallstep.
Qed.

Lemma equivalent_ite:
  forall t1 t2 t3 t,
    is_erased_term t1 ->
    is_erased_term t2 ->
    is_erased_term t3 ->
    wf t1 0 ->
    wf t2 0 ->
    wf t3 0 ->
    pfv t1 term_var = nil ->
    pfv t2 term_var = nil ->
    pfv t3 term_var = nil ->
    (t1 ~>* ttrue \/ t1 ~>* tfalse) ->
    (t1 ~>* ttrue -> [ t2 ≡ t ]) ->
    (t1 ~>* tfalse -> [ t3 ≡ t ]) ->
    [ ite t1 t2 t3 ≡ t ].
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
    pfv b term_var = nil ->
    pfv e1 term_var = nil ->
    pfv e2 term_var = nil ->
    b ~>* ttrue ->
    [ e1 ≡ e ] ->
    [ ite b e1 e2 ≡ e ].
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
    pfv b term_var = nil ->
    pfv e1 term_var = nil ->
    pfv e2 term_var = nil ->
    b ~>* tfalse ->
    [ ite b e1 e2 ≡ e ] ->
    [ e2 ≡ e ].
Proof.
  eauto using equivalent_ite_false, equivalent_sym, equivalent_trans.
Qed.

Lemma equivalent_ite_true3:
  forall b e1 e2 e,
    b ~>* ttrue ->
    [ ite b e1 e2 ≡ e ] ->
    [ e1 ≡ e ].
Proof.
  intros.
  eapply equivalent_trans; try eassumption.
  apply equivalent_sym.
  apply equivalent_ite_true; unfold equivalent_terms in *; repeat step || list_utils.
Qed.

Lemma equivalent_ite_false3:
  forall b e1 e2 e,
    b ~>* tfalse ->
    [ ite b e1 e2 ≡ e ] ->
    [ e2 ≡ e ].
Proof.
  intros.
  eapply equivalent_trans; try eassumption.
  apply equivalent_sym.
  apply equivalent_ite_false; unfold equivalent_terms in *; repeat step || list_utils.
Qed.
