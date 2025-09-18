From Stdlib Require Import String.

Require Export SystemFR.EquivalentContext.
Require Export SystemFR.StepTactics.

Open Scope list_scope.

Definition nat_eq_fix: tree :=
  notype_tfix (
    notype_lambda (notype_lambda (
      tmatch (lvar 1 term_var)
        (tmatch (lvar 0 term_var)
          ttrue
          tfalse)
        (tmatch (lvar 1 term_var)
          tfalse
          (app (app (lvar 4 term_var) (lvar 1 term_var)) (lvar 0 term_var))
        )
    ))
  ).

Definition nat_eq (a: tree) (b: tree) :=
  app (app nat_eq_fix a) b.

Lemma nat_eq_zero_b:
  forall b,
    cbv_value b ->
    nat_eq zero b ~>* ttrue ->
    b = zero.
Proof.
  unfold nat_eq, nat_eq_fix.
  destruct 1;
    repeat step || t_invert_star || star_smallstep_app_onestep;
    eauto with lia;
    eauto with values.
Qed.

Lemma nat_eq_succ:
  forall a b,
    cbv_value a ->
    cbv_value b ->
    wf a 0 ->
    wf b 0 ->
    nat_eq (succ a) b ~>* ttrue ->
    exists b',
      b = succ b' /\
      nat_eq a b' ~>* ttrue.
Proof.
  unfold nat_eq, nat_eq_fix; steps.

  reverse_once.
  reverse_once; eauto with values.
  reverse_once; repeat open_none; eauto with values.
  reverse_once; repeat open_none; eauto with values.
  reverse_once; repeat open_none; eauto with values.
Qed.

Lemma nat_eq_nat:
  forall a b,
    cbv_value a ->
    cbv_value b ->
    wf a 0 ->
    wf b 0 ->
    nat_eq a b ~>* ttrue ->
      (a = zero \/ exists a', a = succ a').
Proof.
  unfold nat_eq, nat_eq_fix; steps.
  reverse_once.
  reverse_once.
  reverse_once; repeat open_none.
  reverse_once; eauto.
Qed.

Lemma nat_eq_sound:
  forall a, cbv_value a ->
    wf a 0 ->
    forall b,
      cbv_value b ->
      wf b 0 ->
      nat_eq a b ~>* ttrue ->
      a = b.
Proof.
  induction 1; steps;
    try solve [ apply_anywhere nat_eq_nat; steps; eauto with values ];
    try solve [ apply_anywhere nat_eq_zero_b; steps ].

  apply_anywhere nat_eq_succ; repeat step || f_equal || apply_any || step_inversion cbv_value.
Qed.

Ltac nat_eq_sound :=
  match goal with
  | H: nat_eq ?a ?b ~>* ttrue |- _ =>
    cbv_value a; cbv_value b;
    poseNew (Mark (a,b) "nat_eq_sound");
    unshelve epose proof (nat_eq_sound a _ _ b _ _ H)
  | H: [ nat_eq ?a ?b ≡ ttrue ] |- _ =>
    cbv_value a; cbv_value b;
    poseNew (Mark (a,b) "tlt_sound");
    unshelve epose proof (nat_eq_sound a _ _ b _ _ _)
  end.

Lemma open_nat_eq:
  forall a b k rep, open k (nat_eq a b) rep = nat_eq (open k a rep) (open k b rep).
Proof.
  steps.
Qed.

Lemma pfv_nat_eq:
  forall a b tag, pfv (nat_eq a b) tag = pfv a tag ++ pfv b tag.
Proof.
  steps.
Qed.

Lemma psubstitute_nat_eq:
  forall a b l tag,
    psubstitute (nat_eq a b) l tag = nat_eq (psubstitute a l tag) (psubstitute b l tag).
Proof.
  steps.
Qed.


Ltac one_step_aux :=
 eapply Relation_Operators.rt1n_trans; [ eauto using is_nat_value_build_nat with values smallstep cbvlemmas | idtac ];
   repeat step || (rewrite open_none in * by (repeat step; eauto using is_nat_value_build_nat with wf)).

Ltac one_step := unshelve one_step_aux; steps.

Lemma nat_eq_complete:
  forall n,
    nat_eq (build_nat n) (build_nat n) ~>* ttrue.
Proof.
  unfold nat_eq, nat_eq_fix.
  induction n; repeat step || one_step.
Qed.

Lemma nat_eq_complete2:
  forall v,
    is_nat_value v ->
    nat_eq v v ~>* ttrue.
Proof.
  repeat step || is_nat_value_buildable || apply nat_eq_complete.
Qed.

Lemma nat_eq_bool:
  forall v1, is_nat_value v1 ->
    forall v2, is_nat_value v2 ->
      nat_eq v1 v2 ~>* ttrue \/
      nat_eq v1 v2 ~>* tfalse.
Proof.
  induction 1; inversion 1;
    repeat step;
    eauto using nat_eq_complete2.

  - right. unfold nat_eq, nat_eq_fix.
    repeat one_step.

  - right. unfold nat_eq, nat_eq_fix.
    repeat one_step.

  - instantiate_any; steps.
    + left. unfold nat_eq, nat_eq_fix.
      repeat one_step.
    + right. unfold nat_eq, nat_eq_fix.
      repeat one_step.
Qed.

Lemma equivalent_nat_eq_terms:
  forall t1 t2 v1 v2,
    is_erased_term t1 ->
    is_erased_term t2 ->
    wf t1 0 ->
    wf t2 0 ->
    pfv t1 term_var = nil ->
    pfv t2 term_var = nil ->
    t1 ~>* v1 ->
    t2 ~>* v2 ->
    [ nat_eq t1 t2 ≡ nat_eq v1 v2 ].
Proof.
  unfold nat_eq, nat_eq_fix; repeat step || apply equivalent_app;
    try solve [ equivalent_star ];
    eauto 3 using equivalent_refl with step_tactic lia.
Qed.

Lemma equivalent_nat_eq_terms_trans:
  forall t1 t2 v1 v2 t,
    [ nat_eq t1 t2 ≡ t ] ->
    t1 ~>* v1 ->
    t2 ~>* v2 ->
    [ nat_eq v1 v2 ≡ t ].
Proof.
  intros.
  eapply equivalent_trans; try eassumption.
  apply equivalent_sym.
  apply equivalent_nat_eq_terms; steps;
    try solve [ unfold equivalent_terms in *; repeat step || list_utils ].
Qed.

Lemma is_erased_term_nat_eq:
  forall t1 t2,
    is_erased_term t1 ->
    is_erased_term t2 ->
    is_erased_term (nat_eq t1 t2).
Proof.
  unfold nat_eq; steps.
Qed.

Lemma wf_nat_eq:
  forall t1 t2 k,
    wf t1 k ->
    wf t2 k ->
    wf (nat_eq t1 t2) k.
Proof.
  unfold nat_eq; steps; eauto with lia.
Qed.
