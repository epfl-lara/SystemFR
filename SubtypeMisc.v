Require Export SystemFR.ReducibilitySubtype.
Require Export SystemFR.TypeSugar2.

Opaque reducible_values.

Lemma subtype_top:
  forall ρ T,
    valid_interpretation ρ ->
    [ ρ | T <: T_top ].
Proof.
  unfold subtype;
    repeat step || simp_red;
    eauto using reducible_values_closed.
Qed.

Lemma open_subtop_helper:
  forall Θ Γ T,
    [ Θ; Γ ⊨ T <: T_top ].
Proof.
  unfold open_subtype; intros; eauto using subtype_top.
Qed.

Lemma open_subtop:
  forall Γ T,
    [ Γ ⊨ T <: T_top ].
Proof.
  eauto using open_subtop_helper.
Qed.

Lemma subtype_refl:
  forall ρ T, [ ρ | T <: T ].
Proof.
  unfold subtype; steps.
Qed.

Lemma open_subrefl_helper:
  forall Θ Γ T,
    [ Θ; Γ ⊨ T <: T ].
Proof.
  unfold open_subtype; intros; eauto using subtype_refl.
Qed.

Lemma open_subrefl:
  forall Γ T,
    [ Γ ⊨ T <: T ].
Proof.
  eauto using open_subrefl_helper.
Qed.

Lemma subsing1:
  forall ρ T t,
    [ ρ | tsingleton T t <: T ].
Proof.
  unfold subtype, tsingleton; repeat step || simp_red.
Qed.

Lemma substitute_singleton:
  forall T t l tag,
    wfs l 0 ->
    psubstitute (tsingleton T t) l tag = tsingleton (psubstitute T l tag) (psubstitute t l tag).
Proof.
  unfold tsingleton; repeat step || t_equality || rewrite substitute_shift.
Qed.

Lemma subtype_trans:
  forall ρ T1 T2 T3,
    [ ρ | T1 <: T2 ] ->
    [ ρ | T2 <: T3 ] ->
    [ ρ | T1 <: T3 ].
Proof.
  unfold subtype; steps.
Qed.

Lemma open_subtype_trans:
  forall Θ Γ T1 T2 T3,
    [ Θ; Γ ⊨ T1 <: T2 ] ->
    [ Θ; Γ ⊨ T2 <: T3 ] ->
    [ Θ; Γ ⊨ T1 <: T3 ].
Proof.
  unfold open_subtype; steps; eauto using subtype_trans.
Qed.

Opaque tsingleton. (* for open_subsing1 *)

Lemma open_subsing1:
  forall Θ Γ T t,
    [ Θ; Γ ⊨ tsingleton T t <: T ].
Proof.
  unfold open_subtype; repeat step || rewrite substitute_singleton || apply subsing1;
    eauto with wf.
Qed.

Lemma open_subsing_helper:
  forall Θ Γ T1 T2 t,
    [ Θ; Γ ⊨ T1 <: T2 ] ->
    [ Θ; Γ ⊨ tsingleton T1 t <: T2 ].
Proof.
  eauto using open_subsing1, open_subtype_trans.
Qed.

Lemma open_subsing:
  forall Γ T1 T2 t,
    [ Γ ⊨ T1 <: T2 ] ->
    [ Γ ⊨ tsingleton T1 t <: T2 ].
Proof.
  eauto using open_subsing_helper.
Qed.

