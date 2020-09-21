Require Export SystemFR.ReducibilityEquivalent.

Opaque reducible_values.

Lemma open_reducible_equivalent_elim:
  forall Θ Γ t1 t2 T,
    is_erased_type T ->
    wf T 0 ->
    subset (fv T) (support Γ) ->
    [ Θ; Γ ⊨ t1 ≡ t2 ] ->
    [ Θ; Γ ⊨ t1 : T ] ->
    [ Θ; Γ ⊨ t2 : T ].
Proof.
  unfold open_reducible, open_equivalent; steps.
  eapply reducibility_equivalent2; eauto; steps;
    eauto with erased fv wf.
Qed.
