From Stdlib Require Import String.

Require Export SystemFR.ScalaDepSugar.
Require Export SystemFR.ErasedRecGen.
Require Export SystemFR.StepTactics.

Opaque reducible_values.

Lemma evaluate_list_match:
  forall ρ v t2 t3,
    valid_interpretation ρ ->
    wf t2 0 ->
    wf t3 2 ->
    is_erased_term t2 ->
    is_erased_term t3 ->
    pfv t2 term_var = nil ->
    pfv t3 term_var = nil ->
    [ ρ ⊨ v : List ]v -> (
      (v = tnil /\ list_match v t2 t3 ~>* t2) \/
      (exists h l,
         closed_value h /\
         closed_value l /\
         v = tcons h l /\
         [ ρ ⊨ h : T_top ]v /\
         [ ρ ⊨ l : List ]v /\
         [ list_match v t2 t3 ≡ open 0 (open 1 t3 h) l ]
      )
    ).
Proof.
  unfold List, list_match.
  intros.
  apply (reducible_values_unfold_gen _ _ _ _ 0) in H6;
    repeat step || simp_spos.
    simp_red_top_level_hyp; repeat step.

  - simp_red_top_level_hyp; left; steps; one_step.
  - simp_red_top_level_hyp; right; steps.
    eexists; eexists; repeat step || simp_red_goal; t_closer; eauto using reducible_value_expr.
    apply equivalent_trans with (open 0 (open 1 t3 (pi1 (pp a b))) (pi2 (pp a b))).
    + equivalent_star;
        eauto 3 with erased step_tactic;
        eauto 3 with wf step_tactic;
        try solve [ repeat apply pfv_shift_open || step ].

      apply star_one.
      eapply scbv_step_same.
      * apply SPBetaMatchRight; t_closer.
      * rewrite open_shift_open3; steps; t_closer;
          eauto 3 with wf step_tactic.
        rewrite open_shift_open4; steps; t_closer;
          eauto 3 with wf step_tactic.
        rewrite no_shift_open; t_closer.
        rewrite no_shift_open; t_closer.
        rewrite open_twice; steps; t_closer.

    + eapply equivalent_trans.
      * apply equivalent_context; steps;
          try solve [ apply is_erased_open; steps; t_closer ];
          try solve [ apply wf_open; steps; t_closer ];
          try solve [ apply fv_nils_open; steps; t_closer ].
        apply equivalent_star; repeat step || list_utils; t_closer.
        apply star_one.
        constructor; t_closer.
      * rewrite (swap_term_holes_open t3); steps; t_closer.
        rewrite (swap_term_holes_open t3); steps; t_closer.
        apply equivalent_context; steps;
          try solve [ apply is_erased_open; steps; t_closer ];
          try solve [ apply wf_open; steps; t_closer ];
          try solve [ apply fv_nils_open; steps; t_closer ];
          try solve [ apply wf_open; steps; t_closer; eauto with wf ].
        apply equivalent_star; repeat step || list_utils; t_closer.
        apply star_one.
        constructor; t_closer.
Qed.

Ltac evaluate_list_match :=
  match goal with
  | H: valid_interpretation ?ρ |- context[list_match ?v ?t2 ?t3] =>
    poseNew (Mark (v, t2, t3) "evaluate_list_match");
    unshelve epose proof (evaluate_list_match ρ v t2 t3 _ _ _ _ _ _ _ _)
  | H: valid_interpretation ?ρ, H2: context[list_match ?v ?t2 ?t3] |- _ =>
    poseNew (Mark (v, t2, t3) "evaluate_list_match");
    unshelve epose proof (evaluate_list_match ρ v t2 t3 _ _ _ _ _ _ _ _)
  | H: context[list_match ?v ?t2 ?t3] |- _ =>
    poseNew (Mark (v, t2, t3) "evaluate_list_match");
    unshelve epose proof (evaluate_list_match nil v t2 t3 _ _ _ _ _ _ _ _)
  end.

Lemma evaluate_list_match_scrut:
  forall t t' t2 t3,
    t ~>* t' ->
    list_match t t2 t3 ~>* list_match t' t2 t3.
Proof.
  unfold list_match; steps; eauto with cbvlemmas.
Qed.

Lemma evaluate_list_match2:
  forall ρ t t2 t3,
    valid_interpretation ρ ->
    wf t2 0 ->
    wf t3 2 ->
    is_erased_term t2 ->
    is_erased_term t3 ->
    pfv t2 term_var = nil ->
    pfv t3 term_var = nil ->
    [ ρ ⊨ t : List ] -> (
      (t ~>* tnil /\ list_match t t2 t3 ~>* t2) \/
      (exists h l,
         closed_value h /\
         closed_value l /\
         t ~>* tcons h l /\
         [ ρ ⊨ h : T_top ]v /\
         [ ρ ⊨ l : List ]v /\
         [ list_match t t2 t3 ≡ open 0 (open 1 t3 h) l ]
      )
    ).
Proof.
  intros.
  unfold reduces_to in * |-; steps.
  unshelve epose proof (evaluate_list_match ρ v t2 t3 _ _ _ _ _ _ _ _); steps.
  - left; steps; eauto using star_trans, evaluate_list_match_scrut.
  - right; exists h, l; steps.
    eapply equivalent_trans; eauto; equivalent_star; eauto using evaluate_list_match_scrut.
Qed.

Ltac evaluate_list_match2 :=
  match goal with
  | H: valid_interpretation ?ρ |- context[list_match ?t ?t2 ?t3] =>
    poseNew (Mark (t, t2, t3) "evaluate_list_match2");
    unshelve epose proof (evaluate_list_match2 ρ t t2 t3 _ _ _ _ _ _ _ _)
  | H: valid_interpretation ?ρ, _: context[list_match ?t ?t2 ?t3] |- _ =>
    poseNew (Mark (t, t2, t3) "evaluate_list_match2");
    unshelve epose proof (evaluate_list_match2 ρ t t2 t3 _ _ _ _ _ _ _ _)
  | _: context[list_match ?t ?t2 ?t3] |- _ =>
    poseNew (Mark (t, t2, t3) "evaluate_list_match2");
    unshelve epose proof (evaluate_list_match2 nil t t2 t3 _ _ _ _ _ _ _ _)
  end.
