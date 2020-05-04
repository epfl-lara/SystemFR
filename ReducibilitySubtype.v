Require Export SystemFR.ReducibilityLemmas.

Opaque reducible_values.

Lemma subtype_reducible_values:
  forall ρ v T1 T2,
    [ ρ | v : T1 ]v ->
    [ ρ | T1 <: T2 ] ->
    [ ρ | v : T2 ]v.
Proof.
  unfold subtype; steps.
Qed.

Lemma subtype_equivalent_types:
  forall ρ T1 T2,
    [ ρ | T1 = T2 ] ->
    [ ρ | T1 <: T2 ].
Proof.
  unfold subtype, equivalent_types; steps; eauto with eapply_any.
Qed.

Lemma subtype_equivalent_types_back:
  forall ρ T1 T2,
    [ ρ | T1 = T2 ] ->
    [ ρ | T2 <: T1 ].
Proof.
  unfold subtype, equivalent_types; steps; eauto with eapply_any.
Qed.

Lemma equivalent_types_refl:
  forall ρ T,
    [ ρ | T = T ].
Proof.
  unfold equivalent_types; steps; eauto with eapply_any.
Qed.

Lemma equivalent_types_sym:
  forall ρ T1 T2,
    [ ρ | T1 = T2 ] ->
    [ ρ | T2 = T1 ].
Proof.
  unfold equivalent_types; steps; eauto with eapply_any.
Qed.

Lemma equivalent_types_trans:
  forall ρ T1 T2 T3,
    [ ρ | T1 = T2 ] ->
    [ ρ | T2 = T3 ] ->
    [ ρ | T1 = T3 ].
Proof.
  unfold equivalent_types; steps; eauto with eapply_any.
  eapply H0; eapply H; auto.
Qed.

Lemma subtype_refl:
  forall ρ T,
    [ ρ | T <: T ].
Proof.
  unfold subtype; steps; eauto with eapply_any.
Qed.

Lemma subtype_trans:
  forall ρ T1 T2 T3,
    [ ρ | T1 <: T2 ] ->
    [ ρ | T2 <: T3 ] ->
    [ ρ | T1 <: T3 ].
Proof.
  unfold subtype; steps; eauto with eapply_any.
Qed.

Lemma equivalent_types_reducible_values:
  forall ρ v T1 T2,
    [ ρ | v : T1 ]v ->
    [ ρ | T1 = T2 ] ->
    [ ρ | v : T2 ]v.
Proof.
  eauto using subtype_reducible_values, subtype_equivalent_types.
Qed.

Lemma equivalent_types_reducible_values_back:
  forall ρ v T1 T2,
    [ ρ | v : T1 ]v ->
    [ ρ | T2 = T1 ] ->
    [ ρ | v : T2 ]v.
Proof.
  eauto using subtype_reducible_values, subtype_equivalent_types_back.
Qed.

Lemma subtype_reducible:
  forall ρ t T1 T2,
    [ ρ | t : T1 ] ->
    [ ρ | T1 <: T2 ] ->
    [ ρ | t : T2 ].
Proof.
  unfold subtype; steps; eauto using reducible_values_exprs.
Qed.

Lemma equivalent_types_reducible:
  forall ρ t T1 T2,
    [ ρ | t : T1 ] ->
    [ ρ | T1 = T2 ] ->
    [ ρ | t : T2 ].
Proof.
  eauto using subtype_reducible, subtype_equivalent_types.
Qed.

Lemma equivalent_types_reducible_back:
  forall ρ t T1 T2,
    [ ρ | t : T2 ] ->
    [ ρ | T1 = T2 ] ->
    [ ρ | t : T1 ].
Proof.
  eauto using subtype_reducible, subtype_equivalent_types_back.
Qed.

Lemma open_subtype_reducible:
  forall Θ Γ t T1 T2,
    [ Θ; Γ ⊨ t : T1 ] ->
    [ Θ; Γ ⊨ T1 <: T2 ] ->
    [ Θ; Γ ⊨ t : T2 ].
Proof.
  unfold open_subtype, open_reducible; steps; eauto using subtype_reducible.
Qed.

Lemma open_equivalent_types_reducible:
  forall Θ Γ t T1 T2,
    [ Θ; Γ ⊨ t : T1 ] ->
    [ Θ; Γ ⊨ T1 = T2 ] ->
    [ Θ; Γ ⊨ t : T2 ].
Proof.
  unfold open_equivalent_types, open_reducible; steps; eauto using equivalent_types_reducible.
Qed.

Lemma open_equivalent_types_reducible_back:
  forall Θ Γ t T1 T2,
    [ Θ; Γ ⊨ t : T1 ] ->
    [ Θ; Γ ⊨ T2 = T1 ] ->
    [ Θ; Γ ⊨ t : T2 ].
Proof.
  unfold open_equivalent_types, open_reducible; steps; eauto using equivalent_types_reducible_back.
Qed.

Lemma open_equivalent_subtype:
  forall Θ Γ T1 T2,
    [ Θ; Γ ⊨ T1 = T2 ] ->
    [ Θ; Γ ⊨ T1 <: T2 ].
Proof.
  unfold open_equivalent_types, open_subtype; steps; eauto using subtype_equivalent_types.
Qed.

Lemma open_equivalent_subtype_back:
  forall Θ Γ T1 T2,
    [ Θ; Γ ⊨ T1 = T2 ] ->
    [ Θ; Γ ⊨ T2 <: T1 ].
Proof.
  unfold open_equivalent_types, open_subtype; steps; eauto using subtype_equivalent_types_back.
Qed.

Lemma open_equivalent_types_refl:
  forall Θ Γ T,
    [ Θ; Γ ⊨ T = T ].
Proof.
  unfold open_equivalent_types; intros; eauto using equivalent_types_refl.
Qed.

Lemma open_equivalent_types_sym:
  forall Θ Γ T1 T2,
    [ Θ; Γ ⊨ T1 = T2 ] ->
    [ Θ; Γ ⊨ T2 = T1 ].
Proof.
  unfold open_equivalent_types; intros; eauto using equivalent_types_sym.
Qed.

Lemma open_equivalent_types_trans:
  forall Θ Γ T1 T2 T3,
    [ Θ; Γ ⊨ T1 = T2 ] ->
    [ Θ; Γ ⊨ T2 = T3 ] ->
    [ Θ; Γ ⊨ T1 = T3 ].
Proof.
  unfold open_equivalent_types; intros; eauto using equivalent_types_trans.
Qed.

Lemma open_subtype_refl:
  forall Θ Γ T,
    [ Θ; Γ ⊨ T <: T ].
Proof.
  unfold open_subtype; intros; eauto using subtype_refl.
Qed.

Lemma open_subtype_trans:
  forall Θ Γ T1 T2 T3,
    [ Θ; Γ ⊨ T1 <: T2 ] ->
    [ Θ; Γ ⊨ T2 <: T3 ] ->
    [ Θ; Γ ⊨ T1 <: T3 ].
Proof.
  unfold open_subtype; intros; eauto using subtype_trans.
Qed.
