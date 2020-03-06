Require Export SystemFR.TypeSugar2.
Require Export SystemFR.ErasedRecGen.
Require Export SystemFR.ErasedSum.
Require Export SystemFR.ErasedPair.
Require Export SystemFR.ErasedTop.

Opaque strictly_positive.

Lemma open_reducible_nil:
  forall tvars gamma,
    [ tvars; gamma ⊨ tnil : List ].
Proof.
  intros.

  apply open_reducible_fold_gen2 with 0;
    repeat step || simp_spos;
    eauto with sets.

  apply open_reducible_left.
  apply open_reducible_unit.
Qed.

Lemma open_reducible_cons:
  forall tvars gamma h t T,
    [ tvars; gamma ⊨ t : List ] ->
    [ tvars; gamma ⊨ h : T ] ->
    [ tvars; gamma ⊨ tcons h t : List ].
Proof.
  intros.

  apply open_reducible_fold_gen2 with 0;
    repeat step || simp_spos;
    eauto with sets.

  apply open_reducible_right.
  apply open_reducible_pp;
    repeat step; eauto with sets;
    eauto using open_reducible_top.
Qed.
