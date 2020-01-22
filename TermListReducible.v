Require Import Coq.Lists.List.

Require Export SystemFR.TreeLists.
Require Export SystemFR.ReducibilityLemmas.

Opaque reducible_values.

Lemma satisfies_erased_terms:
  forall theta l gamma,
    valid_interpretation theta ->
    satisfies (reducible_values theta) gamma l ->
    erased_terms l.
Proof.
  induction l; repeat step || step_inversion satisfies;
    eauto with erased.
Qed.

Hint Resolve satisfies_erased_terms: erased.

Lemma satisfies_weaken:
  forall theta gamma1 gamma2 x T T' l,
    (forall t l,
      satisfies (reducible_values theta) gamma2 l ->
      reducible_values theta t (substitute T l) ->
      reducible_values theta t (substitute T' l)) ->
    subset (fv T) (support gamma2) ->
    subset (fv T') (support gamma2) ->
    NoDup (support (gamma1 ++ (x, T) :: gamma2)) ->
    satisfies (reducible_values theta) (gamma1 ++ (x, T) :: gamma2) l ->
    satisfies (reducible_values theta) (gamma1 ++ (x, T') :: gamma2) l.
Proof.
  induction gamma1;
    repeat step || list_utils || apply SatCons || step_inversion NoDup ||
           step_inversion satisfies.

  apply IHgamma1 with T; repeat step || list_utils; eauto.
Qed.
