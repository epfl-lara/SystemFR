Require Import PeanoNat.

Require Export SystemFR.ErasedVar.
Require Export SystemFR.ErasedArrow.
Require Export SystemFR.ErasedSingleton.

Opaque reducible_values.
Opaque T_singleton.

Lemma open_tvar:
  forall Θ Γ x T,
    lookup Nat.eq_dec Γ x = Some T ->
    [ Θ; Γ ⊨ fvar x term_var : T_singleton T (fvar x term_var) ].
Proof.
  intros.
  eapply open_reducible_singleton; repeat step || t_lookup || unfold subset;
    eauto using open_reducible_var.
Qed.

Lemma open_tabs:
  forall Γ x t U V,
    wf U 0 ->
    wf t 1 ->
    subset (fv_context Γ) (support Γ) ->
    subset (fv U) (support Γ) ->
    subset (fv t) (support Γ) ->
    ~(x ∈ support Γ) ->
    ~(x ∈ fv t) ->
    ~(x ∈ fv V) ->
    is_erased_term t ->
    is_erased_type V ->
    [ (x, U) :: Γ ⊫ open 0 t (fvar x term_var) : open 0 V (fvar x term_var) ] ->
    [ Γ ⊫ notype_lambda t : T_singleton (T_arrow U V) (notype_lambda t) ].
Proof.
  eauto using open_reducible_singleton, open_reducible_lambda.
Qed.
