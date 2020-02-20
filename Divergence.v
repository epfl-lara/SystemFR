Require Export SystemFR.ReducibilityDefinition.

Definition div_reducible theta t T : Prop :=
  forall v,
    star scbv_step t v ->
    irred v ->
    reducible_values theta v T.
