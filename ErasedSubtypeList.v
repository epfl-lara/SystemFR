Require Export SystemFR.ErasedList.

Opaque reducible_values.
Opaque Nil.
Opaque List.

Lemma nil_subtype_list:
  forall tvars gamma,
    [ tvars; gamma ⊨ Nil <: List ].
Proof.
  unfold subtype;
    repeat step.

    