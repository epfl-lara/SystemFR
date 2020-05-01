Require Export SystemFR.ReducibilitySubtype.
Require Export SystemFR.ReducibilityLemmas.
Require Export SystemFR.TermListReducible.
Require Export SystemFR.SubstitutionErase.
Require Export SystemFR.ScalaDepSugar.

Opaque reducible_values.

(*
Lemma open_equivalent_types_trans: forall Θ Γ T1 T2 T3,
  [ Θ; Γ ⊨ open 0 S t = S' ] ->
  [ Θ; Γ ⊨ T_exists (T_singleton T t) S = S' ].
Proof.
*)
(*
Lemma open_nexists: forall Θ Γ S T t,
  [ Θ; Γ ⊨ t : T ] ->
  [ Θ; Γ ⊨ T_exists (T_singleton T t) S = open 0 S t ].
Proof.
Admitted.
*)

Lemma nexists_1: forall ρ T t U T',
  (forall v, [ ρ | v : T_singleton U t ]v -> [ ρ | open 0 T v = T' ]) ->
  [ ρ | T_exists (T_singleton U t) T = T' ].
Proof.
  repeat step || simp_red.
Admitted.

Lemma open_nexists_1_helper: forall Θ Γ T t U T' x,
(*  [ Θ; Γ ⊨ t : T ] -> ?? *)
  [ Θ; (x, T_singleton U t) :: Γ ⊨ T = T' ] ->
  [ Θ; Γ ⊨ T_exists (T_singleton U t) T = T' ].
Proof.
Admitted.

Lemma open_nexists_1: forall Γ T t U T' x,
(*  [ Θ; Γ ⊨ t : T ] -> ?? *)
  [ (x, T_singleton U t) :: Γ ⊨ T = T' ] ->
  [ Γ ⊨ T_exists (T_singleton U t) T = T' ].
Proof.
  intros; eauto using open_nexists_1_helper.
Qed.

Lemma nexists_2: forall ρ S S' T T',
  valid_interpretation ρ ->
  is_erased_type T ->
  is_erased_type T' ->
  wf T 1 ->
  wf T' 1 ->
  pfv T term_var = nil ->
  pfv T' term_var = nil ->
  [ ρ | S = S' ] ->
  (forall a, [ ρ | a : S' ]v -> [ ρ | open 0 T a = open 0 T' a ]) ->
  [ ρ | T_exists S T = T_exists S' T' ].
Proof.
  intros.
  unfold equivalent_types;
    repeat step || simp_red || rewrite reducibility_rewrite;
    t_closer.

  - exists a; steps; eauto using equivalent_types_reducible_values.
  - exists a; steps; eauto using equivalent_types_reducible_values_back.
Qed.

Lemma open_nexists_2_helper: forall Θ Γ S S' T T' x,
  is_erased_type T ->
  is_erased_type T' ->
  wf T 1 ->
  wf T' 1 ->
  subset (fv T) (support Γ) ->
  subset (fv T') (support Γ) ->
  ~ x ∈ pfv S' term_var ->
  ~ x ∈ pfv_context Γ term_var ->
  [ Θ; Γ ⊨ S = S' ] ->
  [ Θ; (x, S') :: Γ ⊨ open 0 T (fvar x term_var) = open 0 T' (fvar x term_var) ] ->
  [ Θ; Γ ⊨ T_exists S T = T_exists S' T' ].
Proof.
  unfold open_equivalent_types; repeat step || apply nexists_2; t_closer.

  unshelve epose proof (H8 ρ ((x, a) :: l) _ _ _);
    repeat step || apply SatCons || t_substitutions; t_closer.
Qed.

Lemma open_nexists_2: forall Γ S S' T T' x,
  is_erased_type T ->
  is_erased_type T' ->
  wf T 1 ->
  wf T' 1 ->
  subset (fv T) (support Γ) ->
  subset (fv T') (support Γ) ->
  ~ x ∈ pfv S' term_var ->
  ~ x ∈ pfv_context Γ term_var ->
  [ Γ ⊨ S = S' ] ->
  [ (x, S') :: Γ ⊨ open 0 T (fvar x term_var) = open 0 T' (fvar x term_var) ] ->
  [ Γ ⊨ T_exists S T = T_exists S' T' ].
Proof.
  eauto using open_nexists_2_helper.
Qed.
