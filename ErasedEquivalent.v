From Stdlib Require Import String.

Require Export SystemFR.RedTactics.

Opaque reducible_values.
Opaque makeFresh.

Lemma equivalent_weaken:
  forall ρ Γ x T u v l,
    subset (fv u) (support Γ) ->
    subset (fv v) (support Γ) ->
    (forall l,
      satisfies (reducible_values ρ) Γ l ->
      [ substitute u l ≡ substitute v l ]) ->
    satisfies (reducible_values ρ) ((x, T) :: Γ) l ->
    [ substitute u l ≡ substitute v l ].
Proof.
  intros.
    repeat step || step_inversion satisfies || t_substitutions.
Qed.

Lemma equivalent_error:
  forall Θ ρ Γ t T l,
    [ Θ; Γ ⊨ t : T ] ->
    valid_interpretation ρ ->
    satisfies (reducible_values ρ) Γ l ->
    support ρ = Θ ->
    [ notype_err ≡ substitute t l ] ->
    False.
Proof.
  repeat step || t_instantiate_sat2 ||
         equivalence_instantiate (app (notype_lambda ttrue) (lvar 0 term_var)).

  unshelve epose proof (H7 _);
    repeat step || t_invert_star || step_inversion cbv_value.

  unfold reduces_to in *; steps.
  eapply star_trans;
    eauto using star_one, scbv_step_same with cbvlemmas values smallstep.
Qed.
