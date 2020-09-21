Require Export SystemFR.Judgments.
Require Export SystemFR.RedTactics.

Opaque reducible_values.

Lemma annotated_equivalent_proof_irrelevance:
  forall Θ Γ p t1 t2 t3 t4,
    [[ Θ; Γ ⊨ p : T_equiv t1 t2 ]] ->
    [[ Θ; Γ ⊨ p ≡ trefl t3 t4 ]].
Proof.
  unfold open_reducible, open_equivalent, reduces_to;
    repeat step || t_instantiate_sat3 || simp_red || apply equivalent_star;
    t_closer.
Qed.
