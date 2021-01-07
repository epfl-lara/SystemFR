Require Export SystemFR.Untangle.
Require Export SystemFR.InferApp.

Lemma open_subnormwiden_helper:
  forall Θ Γ T1 T1' T2,
    widen T1 T1' ->
    [ Θ; Γ ⊨ T1' <: T2 ] ->
    [ Θ; Γ ⊨ T1  <: T2 ].
Proof.
  intros; eauto using widen_open_subtype, open_subtype_trans.
Qed.

Lemma open_subnormwiden:
  forall Γ T1 T1' T2,
    widen T1 T1' ->
    [ Γ ⊫ T1' <: T2 ] ->
    [ Γ ⊫ T1  <: T2 ].
Proof.
  eauto using open_subnormwiden_helper.
Qed.

Lemma open_subnorm:
  forall Γ T1 T1' T1'' T2 T2' T2'',
    [ Γ ⊫ T1 = T1' ] ->
    [ Γ ⊫ T2 = T2' ] ->
    untangle Γ T1' T1'' ->
    untangle Γ T2' T2'' ->
    [ Γ ⊫ T1'' <: T2'' ] ->
    [ Γ ⊫ T1 <: T2 ].
Proof.
  intros.
  eapply open_subtype_trans; eauto using open_equivalent_subtype.
  eapply open_subtype_trans; eauto using open_equivalent_subtype, untangle_open_equivalent_types.
  eapply open_subtype_trans; eauto.
  eapply open_subtype_trans; eauto using open_equivalent_subtype_back.
  eauto using open_equivalent_subtype_back, untangle_open_equivalent_types.
Qed.
