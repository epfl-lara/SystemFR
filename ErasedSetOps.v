Require Import Equations.Equations.

Require Import Coq.Arith.PeanoNat.
Require Import Coq.Lists.List.

Require Export SystemFR.ErasedLet.
Require Export SystemFR.RedTactics.

Opaque reducible_values.
Opaque makeFresh.

Lemma reducible_intersection:
  forall ρ e T1 T2,
    valid_interpretation ρ ->
    [ ρ ⊨ e : T1 ] ->
    [ ρ ⊨ e : T2 ] ->
    [ ρ ⊨ e : T_intersection T1 T2 ].
Proof.
  unfold reduces_to;
    repeat step || t_deterministic_star.
  exists v0; repeat step || simp_red; t_closer.
Qed.

Lemma reducible_union:
  forall ρ e T1 T2,
    valid_interpretation ρ ->
    ([ ρ ⊨ e : T1 ] \/ [ ρ ⊨ e : T2 ]) ->
    [ ρ ⊨ e : T_union T1 T2 ].
Proof.
  unfold reduces_to;
    repeat step || t_deterministic_star;
  try solve [ exists v; repeat step || simp_red; t_closer ].
Qed.

Lemma open_reducible_intersection:
  forall Θ Γ e T1 T2,
    [ Θ; Γ ⊨ e : T1 ] ->
    [ Θ; Γ ⊨ e : T2 ] ->
    [ Θ; Γ ⊨ e : T_intersection T1 T2 ].
Proof.
  unfold open_reducible; repeat step || apply reducible_intersection.
Qed.

Lemma open_reducible_union_elim:
  forall Θ (Γ : context) t t' T1 T2 T z,
    subset (fv t') (support Γ) ->
    subset (fv T1) (support Γ) ->
    subset (fv T2) (support Γ) ->
    subset (fv T) (support Γ) ->
    wf t' 1 ->
    wf T1 0 ->
    wf T2 0 ->
    wf T 0 ->
    ~(z ∈ fv_context Γ) ->
    ~(z ∈ fv t') ->
    ~(z ∈ fv T) ->
    ~(z ∈ fv T1) ->
    ~(z ∈ fv T2) ->
    is_erased_term t' ->
    is_erased_type T ->
    [ Θ; Γ ⊨ t : T_union T1 T2 ] ->
    [ Θ; (z, T1) :: Γ ⊨ open 0 t' (fvar z term_var) : T ] ->
    [ Θ; (z, T2) :: Γ ⊨ open 0 t' (fvar z term_var) :  T ] ->
    [ Θ; Γ ⊨ app (notype_lambda t') t : T ].
Proof.
  unfold open_reducible; repeat step || t_instantiate_sat3 || top_level_unfold reduces_to || simp_red.

  - unshelve epose proof (H15 ρ ((z, v) :: lterms) _ _ _);
      repeat step || list_utils || apply SatCons || t_values_info2 || t_deterministic_star || t_substitutions ||
             apply reducible_let2 with (psubstitute (T_union T1 T2) lterms term_var);
      eauto with erased; eauto with fv; eauto with wf; eauto with twf.

  - unshelve epose proof (H16 ρ ((z, v) :: lterms) _ _ _);
      repeat step || list_utils || apply SatCons || t_values_info2 || t_deterministic_star || t_substitutions ||
             apply reducible_let2 with (psubstitute (T_union T1 T2) lterms term_var);
      eauto with erased; eauto with fv; eauto with wf; eauto with twf.
Qed.
