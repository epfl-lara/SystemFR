Require Export SystemFR.ReducibilitySubtype.
Require Export SystemFR.TermListReducible.
Require Export SystemFR.SubstitutionErase.
Require Export SystemFR.ScalaDepSugar.

Opaque reducible_values.
Opaque T_singleton.

Lemma ncons: forall ρ T1 T2 T1' T2',
  valid_interpretation ρ ->
  is_erased_type T2 ->
  is_erased_type T2' ->
  wf T2 0 ->
  wf T2' 0 ->
  [ ρ | T1 = T1' ] ->
  [ ρ | T2 = T2' ] ->
  [ ρ | Cons T1 T2 = Cons T1' T2' ].
Proof.
  intros; unfold equivalent_types, Cons;
    repeat step || simp_red_top_level_goal || simp_red_top_level_hyp;
    t_closer.

  - exists a; repeat step || simp_red_top_level_goal; eauto using equivalent_types_reducible_values.
    exists a0; repeat step || open_none; eauto using equivalent_types_reducible_values.
  - exists a; repeat step || simp_red_top_level_goal; eauto using equivalent_types_reducible_values_back.
    exists a0; repeat step || open_none; eauto using equivalent_types_reducible_values_back.
Qed.

Lemma substitute_Cons:
  forall T1 T2 l tag,
    psubstitute (Cons T1 T2) l tag = Cons (psubstitute T1 l tag) (psubstitute T2 l tag).
Proof.
  unfold Cons; repeat step.
Qed.

Opaque Cons.

Lemma open_ncons_helper: forall Θ Γ T1 T2 T1' T2',
  is_erased_type T2 ->
  is_erased_type T2' ->
  wf T2 0 ->
  wf T2' 0 ->
  [ Θ; Γ ⊨ T1 = T1' ] ->
  [ Θ; Γ ⊨ T2 = T2' ] ->
  [ Θ; Γ ⊨ Cons T1 T2 = Cons T1' T2' ].
Proof.
  unfold open_equivalent_types; repeat step || rewrite substitute_Cons || apply ncons;
    t_closer.
Qed.

Lemma open_ncons: forall Γ T1 T2 T1' T2',
  is_erased_type T2 ->
  is_erased_type T2' ->
  wf T2 0 ->
  wf T2' 0 ->
  [ Γ ⊨ T1 = T1' ] ->
  [ Γ ⊨ T2 = T2' ] ->
  [ Γ ⊨ Cons T1 T2 = Cons T1' T2' ].
Proof.
  eauto using open_ncons_helper.
Qed.
