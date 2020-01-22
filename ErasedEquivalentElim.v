Require Export SystemFR.ReducibilityEquivalent.

Lemma reducibility_equivalent2:
  forall T t1 t2 theta,
    equivalent_terms t1 t2 ->
    is_erased_type T ->
    wf T 0 ->
    pfv T term_var = nil ->
    valid_interpretation theta ->
    reducible theta t1 T ->
    reducible theta t2 T.
Proof.
  unfold reducible, reduces_to;
    repeat step; t_closer.

  equivalence_instantiate (lvar 0 term_var); unfold scbv_normalizing in *; repeat step.
  unshelve epose proof (H9 _); eauto with values; repeat step || t_deterministic_star.
  exists v2; steps.
  eapply reducibility_equivalent; eauto.
  apply equivalent_trans with t1.
  - apply equivalent_sym; equivalent_star.
  - eapply equivalent_trans; eauto.
    equivalent_star.
Qed.

Lemma open_reducible_equivalent_elim:
  forall tvars gamma t1 t2 T,
    is_erased_type T ->
    wf T 0 ->
    subset (fv T) (support gamma) ->
    [ tvars; gamma ⊨ t1 ≡ t2 ] ->
    [ tvars; gamma ⊨ t1 : T ] ->
    [ tvars; gamma ⊨ t2 : T ].
Proof.
  unfold open_reducible, equivalent; steps.
  eapply reducibility_equivalent2; eauto; steps;
    eauto with erased fv wf.
Qed.
