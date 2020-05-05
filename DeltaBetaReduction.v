Require Import PeanoNat.

Require Export SystemFR.RedTactics.
Require Export SystemFR.ScalaDepSugar.
Require Export SystemFR.EquivalentContext.

Opaque reducible_values.

Reserved Notation "'[' Γ ⊨ t1 '⤳*' t2 ']'" (Γ at level 60, t1 at level 60).

Inductive cbv_open_value: tree -> Prop :=
| OVVar: forall x, cbv_open_value (fvar x term_var)
| OVUnit: cbv_open_value uu
| OVZero: cbv_open_value zero
| OVSucc: forall v, cbv_open_value v -> cbv_open_value (succ v)
| OVFalse: cbv_open_value tfalse
| OVTrue: cbv_open_value ttrue
| OVPair: forall v1 v2, cbv_open_value v1 -> cbv_open_value v2 -> cbv_open_value (pp v1 v2)
| OVLambda: forall t, cbv_open_value (notype_lambda t)
| OVLeft : forall v, cbv_open_value v -> cbv_open_value (tleft v)
| OVRight: forall v, cbv_open_value v -> cbv_open_value (tright v)
.

Hint Constructors cbv_open_value: open_values.

Inductive delta_beta_reduction: context -> tree -> tree -> Prop :=
| DBVar:
    forall Γ x ty t v,
      wf t 0 ->
      lookup Nat.eq_dec Γ x = Some (T_singleton ty t) ->
      [ Γ ⊨ t ⤳* v ] ->
      [ Γ ⊨ fvar x term_var ⤳* v ]

| DBPair:
    forall Γ t1 t2 v1 v2,
      [ Γ ⊨ t1 ⤳* v1 ] ->
      [ Γ ⊨ t2 ⤳* v2 ] ->
      [ Γ ⊨ pp t1 t2 ⤳* pp v1 v2 ]

| DBFirst:
    forall Γ t v1 v2,
      is_erased_term v1 ->
      is_erased_term v2 ->
      wf v1 0 ->
      wf v2 0 ->
      subset (fv v1) (support Γ) ->
      subset (fv v2) (support Γ) ->
      cbv_open_value v1 ->
      cbv_open_value v2 ->
      [ Γ ⊨ t ⤳* pp v1 v2 ] ->
      [ Γ ⊨ pi1 t ⤳* v1 ]

| DBSecond:
    forall Γ t v1 v2,
      is_erased_term v1 ->
      is_erased_term v2 ->
      wf v1 0 ->
      wf v2 0 ->
      subset (fv v1) (support Γ) ->
      subset (fv v2) (support Γ) ->
      cbv_open_value v1 ->
      cbv_open_value v2 ->
      [ Γ ⊨ t ⤳* pp v1 v2 ] ->
      [ Γ ⊨ pi2 t ⤳* v2 ]

| DBRefl:
    forall Γ v,
      is_erased_term v ->
      wf v 0 ->
      subset (fv v) (support Γ) ->
      cbv_open_value v ->
      [ Γ ⊨ v ⤳* v ] (* when evaluation is finished *)

where "'[' Γ ⊨ t1 '⤳*' t2 ']'" := (delta_beta_reduction Γ t1 t2).

Lemma delta_beta_var:
  forall Θ Γ x ty t v,
    wf t 0 ->
    lookup Nat.eq_dec Γ x = Some (T_singleton ty t) ->
    [ Θ; Γ ⊨ t ≡ v ] ->
    [ Θ; Γ ⊨ fvar x term_var ≡ v ].
Proof.
  unfold open_equivalent, T_singleton;
    repeat step || t_lookup || erewrite satisfies_same_support in * by eauto.
  unshelve epose proof (satisfies_lookup2 _ _ _ _ _ _ H3 H0 matched);
    repeat step || simp_red || open_none || rewrite shift_nothing2 in * by eauto with wf;
    eauto using equivalent_trans.
Qed.

Lemma delta_beta_pair:
  forall Θ Γ t1 t2 t1' t2',
    [ Θ; Γ ⊨ t1 ≡ t1' ] ->
    [ Θ; Γ ⊨ t2 ≡ t2' ] ->
    [ Θ; Γ ⊨ pp t1 t2 ≡ pp t1' t2' ].
Proof.
  unfold open_equivalent; repeat step || apply equivalent_pp; eauto.
Qed.

Lemma open_equivalent_refl:
  forall Θ Γ t,
    is_erased_term t ->
    wf t 0 ->
    subset (fv t) (support Γ) ->
    [ Θ; Γ ⊨ t ≡ t ].
Proof.
  unfold open_equivalent; intros; apply equivalent_refl; steps;
    eauto with erased fv wf.
Qed.

Lemma equivalent_pi1_pp:
  forall v1 v2,
    is_erased_term v1 ->
    is_erased_term v2 ->
    wf v1 0 ->
    wf v2 0 ->
    pfv v1 term_var = nil ->
    pfv v2 term_var = nil ->
    cbv_value v1 ->
    cbv_value v2 ->
    [ pi1 (pp v1 v2) ≡ v1 ].
Proof.
  intros; equivalent_star.
Qed.

Lemma equivalent_pi2_pp:
  forall v1 v2,
    is_erased_term v1 ->
    is_erased_term v2 ->
    wf v1 0 ->
    wf v2 0 ->
    pfv v1 term_var = nil ->
    pfv v2 term_var = nil ->
    cbv_value v1 ->
    cbv_value v2 ->
    [ pi2 (pp v1 v2) ≡ v2 ].
Proof.
  intros; equivalent_star.
Qed.

Lemma lookup_value:
  forall l x v,
    are_values l ->
    lookup Nat.eq_dec l x = Some v ->
    cbv_value v.
Proof.
  induction l; steps; eauto.
Qed.

Lemma close_open_value:
  forall v l,
    cbv_open_value v ->
    are_values l ->
    subset (fv v) (support l) ->
    cbv_value (substitute v l).
Proof.
  induction 1; repeat step || sets;
    eauto using lookup_value;
    try solve [ unfold subset in *; repeat step || t_lookup; eauto with exfalso ];
    eauto with values.
Qed.

Lemma satisfies_are_values:
  forall l ρ Γ,
    valid_interpretation ρ ->
    satisfies (reducible_values ρ) Γ l ->
    are_values l.
Proof.
  induction l; repeat step || step_inversion satisfies; eauto with values.
Qed.

Lemma close_open_value2:
  forall v Γ ρ l,
    cbv_open_value v ->
    valid_interpretation ρ ->
    satisfies (reducible_values ρ) Γ l ->
    subset (fv v) (support Γ) ->
    cbv_value (psubstitute v l term_var).
Proof.
  intros; eapply close_open_value;
    repeat step || erewrite satisfies_same_support in * by eauto;
    eauto with values;
    eauto using satisfies_are_values.
Qed.

Lemma delta_beta_first:
  forall Θ Γ t v1 v2,
    is_erased_term v1 ->
    is_erased_term v2 ->
    wf v1 0 ->
    wf v2 0 ->
    subset (fv v1) (support Γ) ->
    subset (fv v2) (support Γ) ->
    cbv_open_value v1 ->
    cbv_open_value v2 ->
    [ Θ; Γ ⊨ t ≡ pp v1 v2 ] ->
    [ Θ; Γ ⊨ pi1 t ≡ v1 ].
Proof.
  unfold open_equivalent; repeat step || apply equivalent_pp; eauto.
  eapply equivalent_trans; eauto using equivalent_pi1.
  apply equivalent_pi1_pp; steps; eauto with erased wf fv;
    eauto using close_open_value2.
Qed.

Lemma delta_beta_second:
  forall Θ Γ t v1 v2,
    is_erased_term v1 ->
    is_erased_term v2 ->
    wf v1 0 ->
    wf v2 0 ->
    subset (fv v1) (support Γ) ->
    subset (fv v2) (support Γ) ->
    cbv_open_value v1 ->
    cbv_open_value v2 ->
    [ Θ; Γ ⊨ t ≡ pp v1 v2 ] ->
    [ Θ; Γ ⊨ pi2 t ≡ v2 ].
Proof.
  unfold open_equivalent; repeat step || apply equivalent_pp; eauto.
  eapply equivalent_trans; eauto using equivalent_pi2.
  apply equivalent_pi2_pp; steps; eauto with erased wf fv;
    eauto using close_open_value2.
Qed.

Lemma delta_beta_obs_equiv:
  forall Θ Γ t1 t2,
    [ Γ ⊨ t1 ⤳* t2 ] ->
    [ Θ; Γ ⊨ t1 ≡ t2 ].
Proof.
  induction 1; repeat step;
    eauto using delta_beta_var;
    eauto using delta_beta_pair;
    eauto using delta_beta_first;
    eauto using delta_beta_second;
    eauto using open_equivalent_refl.
Qed.
