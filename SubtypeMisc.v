Require Export SystemFR.ReducibilitySubtype.
Require Export SystemFR.ScalaDepSugar.

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

Lemma open_subrefl:
  forall Γ T,
    [ Γ ⊨ T <: T ].
Proof.
  eauto using open_subtype_refl.
Qed.

Lemma subsing1:
  forall ρ T t,
    [ ρ | T_singleton T t <: T ].
Proof.
  unfold subtype, T_singleton; repeat step || simp_red.
Qed.

Opaque T_singleton. (* for open_subsing1 *)

Lemma open_subsing1:
  forall Θ Γ T t,
    [ Θ; Γ ⊨ T_singleton T t <: T ].
Proof.
  unfold open_subtype; repeat step || rewrite substitute_singleton || apply subsing1;
    eauto with wf.
Qed.

Lemma open_subsing_helper:
  forall Θ Γ T1 T2 t,
    [ Θ; Γ ⊨ T1 <: T2 ] ->
    [ Θ; Γ ⊨ T_singleton T1 t <: T2 ].
Proof.
  eauto using open_subsing1, open_subtype_trans.
Qed.

Lemma open_subsing:
  forall Γ T1 T2 t,
    [ Γ ⊨ T1 <: T2 ] ->
    [ Γ ⊨ T_singleton T1 t <: T2 ].
Proof.
  eauto using open_subsing_helper.
Qed.
