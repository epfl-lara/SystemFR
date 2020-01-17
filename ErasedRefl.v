Require Export SystemFR.RedTactics.

Lemma open_reducible_refl:
  forall tvars gamma t1 t2,
    [ tvars; gamma ⊨ t1 ≡ t2 ] ->
    [ tvars; gamma ⊨ uu : T_equiv t1 t2 ].
Proof.
  unfold equivalent, open_reducible, reducible, reduces_to;
    repeat step || exists uu || simp_red;
    t_closer.
Qed.
