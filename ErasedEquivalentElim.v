Require Export SystemFR.ReducibilityEquivalent.

Opaque reducible_values.

Lemma open_reducible_equivalent_elim:
  forall tvars gamma t1 t2 T,
    is_erased_type T ->
    wf T 0 ->
    subset (fv T) (support gamma) ->
    [ tvars; gamma ⊨ t1 ≡ t2 ] ->
    [ tvars; gamma ⊨ t1 : T ] ->
    [ tvars; gamma ⊨ t2 : T ].
Proof.
  unfold open_reducible, open_equivalent; steps.
  eapply reducibility_equivalent2; eauto; steps;
    eauto with erased fv wf.
Qed.
