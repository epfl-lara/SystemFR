Require Export SystemFR.ReducibilityEquivalent.

Opaque reducible_values.

Lemma reducibility_is_candidate:
  forall ρ T,
    valid_interpretation ρ ->
    is_erased_type T ->
    wf T 0 ->
    pfv T term_var = nil ->
    reducibility_candidate (fun v => [ ρ ⊨ v : T ]v).
Proof.
  unfold reducibility_candidate; steps;
    eauto with erased fv wf values;
    eauto using reducibility_equivalent.
Qed.
