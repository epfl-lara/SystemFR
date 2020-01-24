Require Import Equations.Equations.

Require Import Coq.Arith.PeanoNat.
Require Import Coq.Lists.List.

Require Export SystemFR.ErasedLet.
Require Export SystemFR.RedTactics.

Opaque reducible_values.
Opaque makeFresh.

Lemma reducible_intersection:
  forall theta e T1 T2,
    valid_interpretation theta ->
    reducible theta e T1 ->
    reducible theta e T2 ->
    reducible theta e (T_intersection T1 T2).
Proof.
  unfold reducible, reduces_to;
    repeat step || t_deterministic_star.
  exists v0; repeat step || simp_red; t_closer.
Qed.

Lemma reducible_union:
  forall theta e T1 T2,
    valid_interpretation theta ->
    (reducible theta e T1 \/ reducible theta e T2) ->
    reducible theta e (T_union T1 T2).
Proof.
  unfold reducible, reduces_to;
    repeat step || t_deterministic_star;
  try solve [ exists v; repeat step || simp_red; t_closer ].
Qed.

Lemma open_reducible_intersection:
  forall tvars gamma e T1 T2,
    [ tvars; gamma ⊨ e : T1 ] ->
    [ tvars; gamma ⊨ e : T2 ] ->
    [ tvars; gamma ⊨ e : T_intersection T1 T2 ].
Proof.
  unfold open_reducible; repeat step || apply reducible_intersection.
Qed.

Lemma open_reducible_union_elim:
  forall tvars (gamma : context) t t' T1 T2 T z,
    subset (fv t') (support gamma) ->
    subset (fv T1) (support gamma) ->
    subset (fv T2) (support gamma) ->
    subset (fv T) (support gamma) ->
    wf t' 1 ->
    wf T1 0 ->
    wf T2 0 ->
    wf T 0 ->
    ~(z ∈ fv_context gamma) ->
    ~(z ∈ fv t') ->
    ~(z ∈ fv T) ->
    ~(z ∈ fv T1) ->
    ~(z ∈ fv T2) ->
    is_erased_term t' ->
    is_erased_type T ->
    [ tvars; gamma ⊨ t : T_union T1 T2 ] ->
    [ tvars; (z, T1) :: gamma ⊨ open 0 t' (fvar z term_var) : T ] ->
    [ tvars; (z, T2) :: gamma ⊨ open 0 t' (fvar z term_var) :  T ] ->
    [ tvars; gamma ⊨ app (notype_lambda t') t : T ].
Proof.
  unfold open_reducible; repeat step || t_instantiate_sat3 || top_level_unfold reducible || top_level_unfold reduces_to || simp_red.

  - unshelve epose proof (H15 theta ((z, v) :: lterms) _ _ _);
      repeat step || list_utils || apply SatCons || t_values_info2 || t_deterministic_star || t_substitutions ||
             apply reducible_let2 with (psubstitute (T_union T1 T2) lterms term_var);
      eauto with erased; eauto with fv; eauto with wf; eauto with twf.

  - unshelve epose proof (H16 theta ((z, v) :: lterms) _ _ _);
      repeat step || list_utils || apply SatCons || t_values_info2 || t_deterministic_star || t_substitutions ||
             apply reducible_let2 with (psubstitute (T_union T1 T2) lterms term_var);
      eauto with erased; eauto with fv; eauto with wf; eauto with twf.
Qed.
