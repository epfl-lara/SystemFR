From Stdlib Require Import PeanoNat.

Require Export SystemFR.Judgments.
Require Export SystemFR.TypeErasureLemmas.
Require Export SystemFR.ErasedVar.

Lemma annotated_reducible_var:
  forall Θ Γ x T,
    lookup PeanoNat.Nat.eq_dec Γ x = Some T ->
    [[ Θ; Γ ⊨ fvar x term_var : T ]].
Proof.
  intros;
    apply open_reducible_var; auto using in_erased_context.
Qed.

Lemma annotated_reducible_weaken:
  forall Θ Γ x T u U,
    [[ Θ; Γ ⊨ u : U ]] ->
    ~(x ∈ support Γ) ->
    ~(x ∈ pfv u term_var) ->
    ~(x ∈ pfv U term_var) ->
    ~(x ∈ Θ) ->
    [[ Θ; (x,T) :: Γ ⊨ u : U ]].
Proof.
  intros;
    apply open_reducible_weaken;
    repeat step || rewrite erased_context_support in *;
    eauto with fv.
Qed.
