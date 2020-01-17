Require Import PeanoNat.

Require Export SystemFR.Judgments.
Require Export SystemFR.TypeErasureLemmas.
Require Export SystemFR.ErasedVar.

Lemma annotated_reducible_var:
  forall tvars gamma x T,
    lookup Nat.eq_dec gamma x = Some T ->
    [[ tvars; gamma ⊨ term_fvar x : T ]].
Proof.
  unfold annotated_reducible; intros;
    apply open_reducible_var; auto using in_erased_context.
Qed.

Lemma annotated_reducible_weaken:
  forall tvars gamma x T u U,
    [[ tvars; gamma ⊨ u : U ]] ->
    ~(x ∈ support gamma) ->
    ~(x ∈ pfv u term_var) ->
    ~(x ∈ pfv U term_var) ->
    ~(x ∈ tvars) ->
    [[ tvars; (x,T) :: gamma ⊨ u : U ]].
Proof.
  unfold annotated_reducible; intros;
    apply open_reducible_weaken;
    repeat step || rewrite erased_context_support in *;
    eauto with fv.
Qed.
