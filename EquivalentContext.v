Require Export SystemFR.ShiftOpen.
Require Export SystemFR.LiftEquivalenceLemmas.

Lemma equivalent_context:
  forall C t1 t2,
    is_erased_term C ->
    wf C 1 ->
    equivalent_terms t1 t2 ->
    equivalent_terms (open 0 C t1) (open 0 C t2).
Proof.
  unfold equivalent_terms;
    steps;
    eauto with erased;
    eauto with wf.

  - unshelve epose proof (H6 (shift_open 0 C0 C) _ _);
      repeat step || rewrite <- open_shift_open_zero in *;
      eauto with erased;
      eauto with wf.

  - unshelve epose proof (H6 (shift_open 0 C0 C) _ _);
      repeat step || rewrite <- open_shift_open_zero in *;
      eauto with erased;
      eauto with wf.
Qed.
