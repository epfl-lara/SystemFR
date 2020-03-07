Require Export Equations.Equations.

Require Export SystemFR.RedTactics.

Opaque reducible_values.

Lemma reducible_values_top:
  forall theta v T,
    valid_interpretation theta ->
    reducible_values theta v T ->
    reducible_values theta v T_top.
Proof.
  repeat step || simp reducible_values;
    eauto using reducible_values_closed.
Qed.

Lemma reducible_top:
  forall theta t T,
    valid_interpretation theta ->
    reducible theta t T ->
    reducible theta t T_top.
Proof.
  eauto using reducible_values_top, reducible_values_exprs.
Qed.

Lemma open_reducible_top:
  forall tvars gamma t T,
    [ tvars; gamma ⊨ t : T ] ->
    [ tvars; gamma ⊨ t : T_top ].
Proof.
  unfold open_reducible;
    repeat step || t_instantiate_sat3;
    eauto using reducible_top.
Qed.
