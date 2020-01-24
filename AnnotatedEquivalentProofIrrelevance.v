Require Export SystemFR.Judgments.
Require Export SystemFR.RedTactics.

Opaque reducible_values.

Lemma annotated_equivalent_proof_irrelevance:
  forall tvars gamma p t1 t2 t3 t4,
    [[ tvars; gamma ⊨ p : T_equiv t1 t2 ]] ->
    [[ tvars; gamma ⊨ p ≡ trefl t3 t4 ]].
Proof.
  unfold annotated_reducible, open_reducible, annotated_equivalent, equivalent, reducible, reduces_to;
    repeat step || t_instantiate_sat3 || simp_red || apply equivalent_star;
    t_closer.
Qed.
