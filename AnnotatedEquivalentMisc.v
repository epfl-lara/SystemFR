Require Import Coq.Lists.List.

Require Export SystemFR.AnnotatedTactics.
Require Export SystemFR.Judgments.
Require Export SystemFR.ErasedEquivalent.
Require Export SystemFR.TermListReducible.

Opaque reducible_values.

Lemma annotated_equivalent_weaken:
  forall tvars gamma x T u v,
    ~(x ∈ support gamma) ->
    subset (fv u) (support gamma) ->
    subset (fv v) (support gamma) ->
    [[ tvars; gamma ⊨ u ≡ v ]] ->
    [[ tvars; (x,T) :: gamma ⊨ u ≡ v ]].
Proof.
  unfold annotated_equivalent, equivalent;
    steps.

  apply equivalent_weaken with theta (erase_context gamma) x (erase_type T);
    repeat step;
    side_conditions.
Qed.

Lemma annotated_equivalent_type:
  forall tvars gamma p t1 t2,
    [[ tvars; gamma ⊨ p : T_equiv t1 t2 ]] ->
    [[ tvars; gamma ⊨ t1 ≡ t2 ]].
Proof.
  unfold
    annotated_reducible, open_reducible, reducible, reduces_to, annotated_equivalent,
    equivalent;
    repeat step || t_instantiate_sat3 || simp_red.
Qed.

Lemma annotated_equivalent_weaken_hyp:
  forall tvars gamma1 gamma2 x T T' u v,
    ~(x ∈ support gamma2) ->
    subset (fv T) (support gamma2) ->
    subset (fv T') (support gamma2) ->
    NoDup (support gamma1 ++ x :: support gamma2) ->
    [[ tvars; gamma2 ⊨ T <: T' ]] ->
    [[ tvars; gamma1 ++ (x, T') :: gamma2 ⊨ u ≡ v ]] ->
    [[ tvars; gamma1 ++ (x, T) :: gamma2 ⊨ u ≡ v ]].
Proof.
  unfold annotated_equivalent, equivalent, annotated_subtype, subtype;
    repeat step || apply_any.

  eapply_any; eauto; repeat step || rewrite erase_context_append in *.
  apply satisfies_weaken with (erase_type T); eauto;
    repeat step || rewrite support_append;
    side_conditions;
    eauto.
Qed.

Lemma annotated_equivalent_error:
  forall tvars gamma e T1 T2,
    [[ tvars; gamma ⊨ e : T1 ]] ->
    [[ tvars; gamma ⊨ err T2 ≡ e ]] ->
    [[ tvars; gamma ⊨ ttrue ≡ tfalse ]].
Proof.
  unfold annotated_reducible, annotated_equivalent, equivalent;
    repeat step || t_instantiate_sat3;
    eauto using equivalent_error with exfalso.
Qed.
