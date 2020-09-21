Require Import Coq.Lists.List.

Require Export SystemFR.TreeLists.
Require Export SystemFR.ReducibilityLemmas.

Opaque reducible_values.

Lemma satisfies_erased_terms:
  forall ρ l Γ,
    valid_interpretation ρ ->
    satisfies (reducible_values ρ) Γ l ->
    erased_terms l.
Proof.
  induction l; repeat step || step_inversion satisfies;
    eauto with erased.
Qed.

Hint Immediate satisfies_erased_terms: erased.

Lemma satisfies_weaken:
  forall ρ Γ1 Γ2 x T T' l,
    (forall t l,
      satisfies (reducible_values ρ) Γ2 l ->
      [ ρ ⊨ t : substitute T l ]v ->
      [ ρ ⊨ t : substitute T' l ]v) ->
    subset (fv T) (support Γ2) ->
    subset (fv T') (support Γ2) ->
    NoDup (support (Γ1 ++ (x, T) :: Γ2)) ->
    satisfies (reducible_values ρ) (Γ1 ++ (x, T) :: Γ2) l ->
    satisfies (reducible_values ρ) (Γ1 ++ (x, T') :: Γ2) l.
Proof.
  induction Γ1;
    repeat step || list_utils || apply SatCons || step_inversion NoDup ||
           step_inversion satisfies.

  apply IHΓ1 with T; repeat step || list_utils; eauto.
Qed.
