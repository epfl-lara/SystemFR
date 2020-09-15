Require Import List.
Import ListNotations.

Require Export SystemFR.ComputableEquality.
Require Export SystemFR.TypedEquality.

Opaque reducible_values.

Lemma computable_equality_typed_equality:
  forall theta T v1 v2,
    equivalent_at theta T v1 v2 ->
    computable_equality theta T ->
    wf T 0 ->
    pfv T term_var = nil ->
    valid_interpretation theta ->
    cbv_value v1 ->
    cbv_value v2 ->
    equivalent_terms v1 v2.
Proof.
  unfold computable_equality, computable_equality_with, equivalent_at;
    repeat step.

  unshelve epose proof
    (H8 (notype_lambda (app (app f_eq v1) (lvar 0 term_var))) _ _ _ _);
    repeat step || apply reducible_lambda || open_none;
    t_closer.

  - apply reducible_app2 with T;
      repeat step;
      eauto using reducible_value_expr.
    apply reducible_app2 with T;
      repeat step.

  - apply_any; steps; eauto using reducible_expr_value.
    apply equivalent_star_true with (app (app f_eq v1) v1).

    + eapply equivalent_square; eauto.
      * apply equivalent_star; repeat step || list_utils;
        eauto with erased wf fv.
        apply star_one.
        eapply scbv_step_same; eauto with smallstep; repeat step || open_none.
      * apply equivalent_star; repeat step || list_utils;
        eauto with erased wf fv.
        apply star_one.
        eapply scbv_step_same; eauto with smallstep; repeat step || open_none.

    + apply_any; eauto using reducible_expr_value;
        eauto using equivalent_refl with erased wf fv.
Qed.
