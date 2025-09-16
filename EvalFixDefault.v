From Stdlib Require Import String.

Require Export SystemFR.EquivalentContext.
Require Export SystemFR.ScalaDepSugar.
Require Export SystemFR.StepTactics.

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
    [ fuel ≡ fuel' ] ->
    [ fix_default' t default fuel ≡ fix_default' t default fuel' ].
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
    (fuel = zero /\ fix_default' t default fuel ~>* default) \/
    (exists fuel', fuel = succ fuel' /\
               fix_default' t default fuel ~>* open 0 t (fix_default' t default fuel')).
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
