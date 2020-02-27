Require Export SystemFR.RedTactics.
Require Export SystemFR.NatLessThan.

Lemma open_reducible_err:
  forall tvars gamma T,
    [ tvars; gamma ⊨ tfalse ≡ ttrue ] ->
    [ tvars; gamma ⊨ notype_err : T ].
Proof.
  unfold open_reducible, open_equivalent;
    repeat step || t_instantiate_sat3;
    eauto using false_true_not_equivalent with exfalso.
Qed.
