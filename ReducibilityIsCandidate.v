Require Export SystemFR.ReducibilityEquivalent.

Opaque reducible_values.

Lemma reducibility_is_candidate:
  forall theta T,
    valid_interpretation theta ->
    is_erased_type T ->
    wf T 0 ->
    pfv T term_var = nil ->
    reducibility_candidate (fun v => reducible_values theta v T).
Proof.
  unfold reducibility_candidate; steps;
    eauto with erased fv wf values;
    eauto using reducibility_equivalent.
Qed.
