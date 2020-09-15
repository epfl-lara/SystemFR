Require Import List.
Import ListNotations.

Require Export SystemFR.TypedEquality.

Definition identity: tree := notype_lambda (lvar 0 term_var).
Definition pair_identity: tree := notype_lambda (pp (pi1 (lvar 0 term_var)) (pi2 (lvar 0 term_var))).

Lemma identity_pair_identity_not_equivalent:
  equivalent_terms identity pair_identity ->
  False.
Proof.
  unfold identity, pair_identity; intros.

  unshelve epose proof (equivalent_context (app (lvar 0 term_var) uu) _ _ _ _ _ H) as HH;
    repeat step.

  unshelve epose proof (equivalent_normalizing _ _ uu HH _ _);
    repeat step;
    eauto using star_one, scbv_step_same with smallstep values.

  apply_anywhere equivalent_value_unit; steps.

  star_smallstep_app_onestep; repeat step || t_invert_star.
Qed.

Lemma identity_pair_identity_equivalent_at:
  equivalent_at [] (T_arrow (T_prod T_nat T_nat) (T_prod T_nat T_nat)) identity pair_identity.
Proof.
  unfold equivalent_at;
    repeat step.
Admitted.
