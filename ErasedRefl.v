Require Export SystemFR.RedTactics.

Opaque reducible_values.

Lemma open_reducible_refl:
  forall Θ Γ t1 t2,
    [ Θ; Γ ⊨ t1 ≡ t2 ] ->
    [ Θ; Γ ⊨ uu : T_equiv t1 t2 ].
Proof.
  unfold open_equivalent, open_reducible,reduces_to;
    repeat step || exists uu || simp_red;
    t_closer.
Qed.
