Require Import Coq.Strings.String.

Require Export SystemFR.StepTactics.
Require Export SystemFR.ReducibilityEquivalent.
Require Export SystemFR.ErasedSingleton.

Opaque reducible_values.

Lemma fix_default_equivalent_fuel_fuel:
  forall t default fuel fuel',
    is_erased_term default ->
    is_erased_term t ->
    is_erased_term fuel ->
    wf default 0 ->
    wf fuel 0 ->
    wf t 1 ->
    pfv fuel term_var = nil ->
    pfv default term_var = nil ->
    pfv t term_var = nil ->
    equivalent_terms fuel fuel' ->
    equivalent_terms (fix_default' t default fuel) (fix_default' t default fuel').
Proof.
  unfold fix_default;
    repeat step.

  unshelve epose proof (equivalent_context (app (notype_tfix
        (notype_lambda
           (tmatch (lvar 0 term_var) default
              (shift_open 0 t (app (lvar 2 term_var) (lvar 0 term_var)))))) (lvar 0 term_var)) fuel fuel' _ _ _ _);
    repeat step || list_utils ||
           (open_none_by ltac:(eauto 2 with wf step_tactic)) ||
           open_none || apply pfv_shift_open || apply is_erased_term_shift_open;
    eauto with erased;
    eauto with wf step_tactic lia.
Qed.

Lemma evaluate_fix_default:
  forall t default fuel,
    is_nat_value fuel ->
    wf default 0 ->
    wf t 1 ->
    (fuel = zero /\ star scbv_step (fix_default' t default fuel) default) \/
    (exists fuel', fuel = succ fuel' /\
              star scbv_step (fix_default' t default fuel) (open 0 t (fix_default' t default fuel'))).
Proof.
  unfold fix_default'; inversion 1; steps.
  - left; steps.
    one_step; repeat open_none.
    repeat one_step.
  - right; eexists; steps.
    one_step; repeat open_none.
    one_step.
    one_step; repeat open_none_by ltac:(eauto 2 with wf step_tactic).
    repeat step || open_none || rewrite open_shift_open2 by (steps; eauto 2 with step_tactic wf).
    rewrite no_shift_open; steps; eauto with wf step_tactic.
Qed.

Ltac evaluate_fix_default :=
  match goal with
  | |- context[fix_default' ?t ?default ?fuel] =>
    poseNew (Mark (t, default, fuel) "evaluate_fix_default");
    unshelve epose proof (evaluate_fix_default t default fuel _ _ _)
  end.

Opaque fix_default'.

Lemma tfix_fuel_induction:
  forall fuel, is_nat_value fuel ->
    forall ρ t default T,
      valid_interpretation ρ ->
      is_erased_term t ->
      is_erased_term default ->
      wf default 0 ->
      wf t 1 ->
      pfv t term_var = nil ->
      pfv default term_var = nil ->
      is_erased_type T ->
      wf T 0 ->
      pfv T term_var = nil ->
      [ ρ | default : T ] ->
      (forall v, [ ρ | v : T ]v -> [ ρ | open 0 t v : T ]) ->
      [ ρ | fix_default' t default fuel : T ].
Proof.
  induction 1; intros; evaluate_fix_default; steps; eauto with is_nat_value.
  - eapply star_backstep_reducible;
      repeat step || apply pfv_fix_default || apply wf_fix_default || apply is_erased_term_fix_default;
      eauto.
  - eapply star_backstep_reducible;
      repeat step ||
             apply pfv_fix_default || apply wf_fix_default || apply is_erased_term_fix_default;
      eauto with wf fv erased.

    unshelve epose proof (IHis_nat_value ρ t default T _ _ _ _ _ _ _ _ _ _ _ _) as HH;
      steps.

    unfold reducible, reduces_to in HH; steps.
    apply reducibility_equivalent2 with (open 0 t v); steps;
      eauto with wf fv erased; eauto using reducible_value_expr.
    apply equivalent_sym.
    apply equivalent_context; steps; equivalent_star.
Qed.

Lemma tfix_fuel:
  forall fuel ρ t default T,
    valid_interpretation ρ ->
    is_erased_term t ->
    is_erased_term default ->
    wf default 0 ->
    wf t 1 ->
    pfv t term_var = nil ->
    pfv default term_var = nil ->
    is_erased_type T ->
    wf T 0 ->
    pfv T term_var = nil ->
    [ ρ | fuel : T_nat ] ->
    [ ρ | default : T ] ->
    (forall v, [ ρ | v : T ]v -> [ ρ | open 0 t v : T ]) ->
    [ ρ | fix_default' t default fuel : T ].
Proof.
  intros.
  unfold reducible, reduces_to in H9; steps.
  apply reducibility_equivalent2 with (fix_default' t default v);
    repeat step || apply tfix_fuel_induction ||
           apply fix_default_equivalent_fuel_fuel ||
           simp_red_top_level_hyp;
    eauto with erased wf fv;
    try solve [ apply equivalent_sym; equivalent_star ].
Qed.

Lemma open_tfix_helper:
  forall Θ Γ t default fuel x T,
    is_erased_term t ->
    wf t 1 ->
    subset (fv t) (support Γ) ->
    is_erased_type T ->
    wf T 0 ->
    subset (fv T) (support Γ) ->
    ~ x ∈ fv T ->
    ~ x ∈ pfv_context Γ term_var ->
    [ Θ; Γ ⊨ fuel : T_nat ] ->
    [ Θ; Γ ⊨ default : T ] ->
    [ Θ; (x, T) :: Γ ⊨ open 0 t (fvar x term_var) : T ] ->
    [ Θ; Γ ⊨ fix_default' t default fuel : T ].
Proof.
  unfold open_reducible;
    repeat step || t_instantiate_sat3;
    rewrite subst_fix_default; eauto with wf.
  apply tfix_fuel; steps; eauto with wf fv erased.
  unshelve epose proof (H9 ρ ((x, v) :: lterms) _ _ _);
    repeat step || apply SatCons || t_substitutions;
    eauto with fv wf twf erased.
Qed.

Lemma open_tfix_helper2:
  forall Γ t default fuel x T,
    is_erased_term t ->
    wf t 1 ->
    subset (fv t) (support Γ) ->
    is_erased_type T ->
    wf T 0 ->
    subset (fv T) (support Γ) ->
    ~ x ∈ fv T ->
    ~ x ∈ pfv_context Γ term_var ->
    [ Γ ⊨ fuel : T_nat ] ->
    [ Γ ⊨ default : T ] ->
    [ (x, T) :: Γ ⊨ open 0 t (fvar x term_var) : T ] ->
    [ Γ ⊨ fix_default' t default fuel : T ].
Proof.
  eauto using open_tfix_helper.
Qed.

Lemma open_global_fuel_nat:
  forall Θ Γ,
    [ Θ; Γ ⊨ global_fuel: T_nat ].
Proof.
  unfold open_reducible; steps.
  apply reducible_value_expr; repeat step || simp_red.
  rewrite substitute_nothing5; eauto using is_nat_global_fuel with fv.
Qed.

Lemma open_tfix:
  forall Γ t default x T,
    is_erased_term global_fuel ->
    is_erased_term default ->
    is_erased_term t ->
    wf t 1 ->
    wf default 0 ->
    subset (fv t) (support Γ) ->
    is_erased_type T ->
    wf T 0 ->
    subset (fv T) (support Γ) ->
    subset (fv default) (support Γ) ->
    ~ x ∈ fv T ->
    ~ x ∈ pfv_context Γ term_var ->
    [ Γ ⊨ default : T ] ->
    [ (x, T) :: Γ ⊨ open 0 t (fvar x term_var) : T ] ->
    [ Γ ⊨ fix_default t default : T_singleton T (fix_default t default) ].
Proof.
  unfold fix_default; intros.
  apply open_reducible_singleton;
    repeat step || apply is_erased_term_fix_default || apply wf_fix_default;
    eauto using is_nat_global_fuel with wf;
    eauto using open_tfix_helper2, open_global_fuel_nat.

  eapply subset_transitive; eauto using pfv_fix_default2;
    repeat step || sets || rewrite nat_value_fv;
    eauto using is_nat_global_fuel;
    eauto with sets.
Qed.
