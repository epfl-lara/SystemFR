Require Export SystemFR.WFLemmas.
Require Export SystemFR.SmallStep.
Require Export SystemFR.RelationClosures.

Ltac one_step_aux :=
 eapply Trans; [ eauto using is_nat_value_build_nat with values smallstep cbvlemmas | idtac ];
   repeat step || (rewrite open_none in * by (repeat step; eauto using is_nat_value_build_nat with wf)).

Ltac one_step := unshelve one_step_aux; steps.
