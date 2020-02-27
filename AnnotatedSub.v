Require Export SystemFR.Judgments.
Require Export SystemFR.ReducibilityLemmas.

Opaque reducible_values.

Lemma annotated_reducible_sub:
  forall tvars gamma t T1 T2,
    [[ tvars; gamma ⊨ T1 <: T2 ]] ->
    [[ tvars; gamma ⊨ t : T1 ]] ->
    [[ tvars; gamma ⊨ t : T2 ]].
Proof.
  unfold annotated_reducible, annotated_subtype, open_reducible, open_subtype, subtype;
    repeat step; eauto using reducible_values_exprs.
Qed.
