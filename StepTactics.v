Require Export SystemFR.WFLemmas.
Require Export SystemFR.SmallStep.

Ltac one_step_aux :=
 eapply Relation_Operators.rt1n_trans;
   [ eauto using is_nat_value_build_nat with values smallstep cbvlemmas | idtac ];
   repeat step || (rewrite open_none in * by (repeat step; eauto using is_nat_value_build_nat with wf)).

Ltac one_step := unshelve one_step_aux; steps.
