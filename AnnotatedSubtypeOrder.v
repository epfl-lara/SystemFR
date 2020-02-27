Require Export SystemFR.Judgments.

Lemma subtype_refl:
  forall tvars gamma T,
    [[ tvars; gamma ⊨ T <: T ]].
Proof.
  unfold annotated_subtype, open_subtype, subtype; steps.
Qed.

Lemma subtype_trans:
  forall tvars gamma T1 T2 T3,
    [[ tvars; gamma ⊨ T1 <: T2 ]] ->
    [[ tvars; gamma ⊨ T2 <: T3 ]] ->
    [[ tvars; gamma ⊨ T1 <: T3 ]].
Proof.
  unfold annotated_subtype, open_subtype, subtype; steps.
Qed.
