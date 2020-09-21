Require Import Coq.Strings.String.

Require Export SystemFR.EquivalentContext.

Definition tlt_fix: tree :=
  notype_tfix (
    notype_lambda (notype_lambda (
      tmatch (lvar 1 term_var)
        (tmatch (lvar 0 term_var)
          tfalse
          ttrue)
        (tmatch (lvar 1 term_var)
          tfalse
          (app (app (lvar 4 term_var) (lvar 1 term_var)) (lvar 0 term_var))
        )
    ))
  ).

Definition tlt (a: tree) (b: tree) :=
  app (app tlt_fix a) b.

Lemma tlt_def:
  forall a b,
  app (app tlt_fix a) b = tlt a b.
Proof.
  reflexivity.
Qed.

Lemma tlt_a_zero:
  forall a,
    tlt a zero ~>* ttrue ->
    False.
Proof.
  unfold tlt, tlt_fix in *;
    repeat step || t_invert_star || star_smallstep_app_onestep || step_inversion cbv_value.
Qed.

Lemma tlt_zero_b:
  forall b,
    cbv_value b ->
    tlt zero b ~>* ttrue ->
    1 <= tree_size b.
Proof.
  destruct 1; repeat step;
    eauto with lia;
    try solve [ inversion H; unfold tlt in *;
      repeat step || t_invert_step || star_smallstep_app_onestep || t_invert_star
    ].
Qed.

Lemma tlt_something:
  forall a b,
    cbv_value a ->
    cbv_value b ->
    wf a 0 ->
    wf b 0 ->
    tlt a b ~>* ttrue ->
    exists b', b = succ b' /\
      (a = zero \/ exists a', a = succ a').
Proof.
  unfold tlt, tlt_fix; steps.
  reverse_once.
  reverse_once.
  reverse_once; repeat open_none.
  reverse_once; repeat open_none.
  - reverse_once; eauto.
  - reverse_once; eauto.
Qed.

Lemma tlt_succ:
  forall a b,
    cbv_value a ->
    cbv_value b ->
    wf a 0 ->
    wf b 0 ->
    tlt (succ a) (succ b) ~>* ttrue ->
    tlt a b ~>* ttrue.
Proof.
  unfold tlt, tlt_fix; steps.

  reverse_once; eauto with values.
  reverse_once; eauto with values.
  reverse_once; repeat open_none; eauto with values.
  reverse_once; repeat open_none; eauto with values.
  reverse_once; repeat open_none; eauto with values.
Qed.

Lemma tlt_sound:
  forall a, cbv_value a ->
    wf a 0 ->
    forall b,
      cbv_value b ->
      wf b 0 ->
      tlt a b ~>* ttrue ->
      tree_size a < tree_size b.
Proof.
  induction 1; steps; eauto using tlt_zero_b; eauto with lia;
    try solve [ apply_anywhere tlt_something; steps; eauto with values ].

  destruct H1; steps;
    try solve [ apply_anywhere tlt_something; steps; eauto with values ];
    eauto using le_n_S, tlt_succ.
Qed.

Ltac tlt_sound :=
  match goal with
  | H: tlt ?a ?b ~>* ttrue |- _ =>
    cbv_value a; cbv_value b;
    poseNew (Mark (a,b) "tlt_sound");
    unshelve epose proof (tlt_sound a _ _ b _ _ H)
  | H: [ tlt ?a ?b ≡ ttrue ] |- _ =>
    cbv_value a; cbv_value b;
    poseNew (Mark (a,b) "tlt_sound");
    unshelve epose proof (tlt_sound a _ _ b _ _ _)
  end.

Lemma open_tlt:
  forall a b k rep, open k (tlt a b) rep = tlt (open k a rep) (open k b rep).
Proof.
  unfold tlt; repeat step.
Qed.

Lemma pfv_tlt:
  forall a b tag, pfv (tlt a b) tag = pfv a tag ++ pfv b tag.
Proof.
  unfold tlt; repeat step || rewrite List.app_nil_r in *.
Qed.

Lemma psubstitute_tlt:
  forall a b l tag,
    psubstitute (tlt a b) l tag = tlt (psubstitute a l tag) (psubstitute b l tag).
Proof.
  unfold tlt; repeat step.
Qed.

Ltac one_step_aux :=
 eapply Relation_Operators.rt1n_trans; [ eauto using is_nat_value_build_nat with values smallstep cbvlemmas | idtac ];
   repeat step || (rewrite open_none in * by (repeat step; eauto using is_nat_value_build_nat with wf)).

Ltac one_step := unshelve one_step_aux; steps.

Lemma tlt_complete:
  forall a b,
    a < b ->
    tlt (build_nat a) (build_nat b) ~>* ttrue.
Proof.
  unfold tlt, tlt_fix; induction a; destruct b; repeat step || eauto with lia || one_step.
Qed.

Lemma tlt_complete2:
  forall a b,
    is_nat_value a ->
    is_nat_value b ->
    tree_size a < tree_size b ->
    tlt a b ~>* ttrue.
Proof.
  repeat step || is_nat_value_buildable || apply tlt_complete || rewrite tree_size_build_nat in *.
Qed.

Lemma equivalent_tlt_terms:
  forall t1 t2 v1 v2,
    is_erased_term t1 ->
    is_erased_term t2 ->
    wf t1 0 ->
    wf t2 0 ->
    pfv t1 term_var = nil ->
    pfv t2 term_var = nil ->
    t1 ~>* v1 ->
    t2 ~>* v2 ->
    [ tlt t1 t2 ≡ tlt v1 v2 ].
Proof.
  unfold tlt, tlt_fix; repeat step || apply equivalent_app;
    try solve [ equivalent_star ];
    eauto 3 using equivalent_refl with step_tactic lia.
Qed.

Lemma equivalent_tlt_terms_trans:
  forall t1 t2 v1 v2 t,
    [ tlt t1 t2 ≡ t ] ->
    t1 ~>* v1 ->
    t2 ~>* v2 ->
    [ tlt v1 v2 ≡ t ].
Proof.
  intros.
  eapply equivalent_trans; try eassumption.
  apply equivalent_sym.
  apply equivalent_tlt_terms; steps;
    try solve [ unfold equivalent_terms in *; repeat step || list_utils ].
Qed.

Lemma is_erased_term_tlt:
  forall t1 t2,
    is_erased_term t1 ->
    is_erased_term t2 ->
    is_erased_term (tlt t1 t2).
Proof.
  unfold tlt; steps.
Qed.

Lemma wf_tlt:
  forall t1 t2 k,
    wf t1 k ->
    wf t2 k ->
    wf (tlt t1 t2) k.
Proof.
  unfold tlt; steps; eauto with lia.
Qed.
