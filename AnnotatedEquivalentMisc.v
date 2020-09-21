Require Import Coq.Lists.List.

Require Export SystemFR.AnnotatedTactics.
Require Export SystemFR.Judgments.
Require Export SystemFR.ErasedEquivalent.
Require Export SystemFR.TermListReducible.

Opaque reducible_values.

Lemma annotated_equivalent_weaken:
  forall Θ Γ x T u v,
    ~(x ∈ support Γ) ->
    subset (fv u) (support Γ) ->
    subset (fv v) (support Γ) ->
    [[ Θ; Γ ⊨ u ≡ v ]] ->
    [[ Θ; (x,T) :: Γ ⊨ u ≡ v ]].
Proof.
  unfold open_equivalent; steps.

  apply equivalent_weaken with ρ (erase_context Γ) x (erase_type T);
    repeat step;
    side_conditions.
Qed.

Lemma annotated_equivalent_type:
  forall Θ Γ p t1 t2,
    [[ Θ; Γ ⊨ p : T_equiv t1 t2 ]] ->
    [[ Θ; Γ ⊨ t1 ≡ t2 ]].
Proof.
  unfold open_reducible, reduces_to, open_equivalent;
    repeat step || t_instantiate_sat3 || simp_red.
Qed.

Lemma annotated_equivalent_weaken_hyp:
  forall Θ Γ1 Γ2 x T T' u v,
    ~(x ∈ support Γ2) ->
    subset (fv T) (support Γ2) ->
    subset (fv T') (support Γ2) ->
    NoDup (support Γ1 ++ x :: support Γ2) ->
    [[ Θ; Γ2 ⊨ T <: T' ]] ->
    [[ Θ; Γ1 ++ (x, T') :: Γ2 ⊨ u ≡ v ]] ->
    [[ Θ; Γ1 ++ (x, T) :: Γ2 ⊨ u ≡ v ]].
Proof.
  unfold open_equivalent, open_subtype; intros.

  eapply_any; eauto; repeat step || rewrite erase_context_append in *.
  apply satisfies_weaken with (erase_type T); eauto;
    repeat step || rewrite support_append;
    side_conditions;
    eauto.
Qed.

Lemma annotated_equivalent_error:
  forall Θ Γ e T1 T2,
    [[ Θ; Γ ⊨ e : T1 ]] ->
    [[ Θ; Γ ⊨ err T2 ≡ e ]] ->
    [[ Θ; Γ ⊨ ttrue ≡ tfalse ]].
Proof.
  unfold open_equivalent;
    repeat step || t_instantiate_sat3;
    eauto using equivalent_error with exfalso.
Qed.
