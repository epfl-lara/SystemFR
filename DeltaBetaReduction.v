Require Import Coq.Strings.String.
From Equations Require Import Equations.
Require Import PeanoNat.

Require Export SystemFR.EquivalentContext.
Require Export SystemFR.ErasedList.
Require Export SystemFR.EquivalenceLemmas3.
Require Export SystemFR.EvalListMatch.
Require Export SystemFR.EvalFixDefault.

Opaque reducible_values.

Reserved Notation "'[' Γ ⊨ t1 '⤳*' t2 ']'" (at level 60, Γ at level 60, t1 at level 60).

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
      [ Γ ⊫ v1 : T_top ] ->
      [ Γ ⊫ v2 : T_top ] ->
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
      [ Γ ⊫ v1 : T_top ] ->
      [ Γ ⊫ v2 : T_top ] ->
      [ Γ ⊨ t ⤳* pp v1 v2 ] ->
      [ Γ ⊨ pi2 t ⤳* v2 ]

| DBApp1:
    forall Γ f t t' body v,
      is_erased_term t' ->
      is_erased_term body ->
      pfv t' term_var = nil ->
      pfv body term_var = nil ->
      wf t' 0 ->
      wf body 0 ->
      [ Γ ⊫ t' : T_top ] ->
      [ Γ ⊨ t ⤳* t' ] ->
      [ Γ ⊨ f ⤳* notype_lambda body ] ->
      [ Γ ⊨ open 0 body t' ⤳* v ] ->
      [ Γ ⊨ app f t ⤳* v ]

| DBApp2:
    forall Γ f f' t t',
      [ Γ ⊨ t ⤳* t' ] ->
      [ Γ ⊨ f ⤳* f' ] ->
      [ Γ ⊨ app f t ⤳* app f' t' ]


| DBNatMatch1:
    forall Γ t t0 ts v,
      is_erased_term ts ->
      wf ts 1 ->
      subset (fv ts) (support Γ) ->
      [ Γ ⊨ t ⤳* zero ] ->
      [ Γ ⊨ t0 ⤳* v ] ->
      [ Γ ⊨ tmatch t t0 ts ⤳* v ]

| DBNatMatch2:
    forall Γ t t0 ts t' v,
      is_erased_term t0 ->
      is_erased_term ts ->
      wf t0 0 ->
      wf ts 1 ->
      subset (fv t0) (support Γ) ->
      subset (fv ts) (support Γ) ->
      subset (fv v) (support Γ) ->
      [ Γ ⊫ t' : T_top ] ->
      [ Γ ⊨ t ⤳* succ t' ] ->
      [ Γ ⊨ open 0 ts t' ⤳* v ] ->
      [ Γ ⊨ tmatch t t0 ts ⤳* v ]

| DBNatMatch3:
    forall Γ t t' t0 ts,
      is_erased_term t0 ->
      is_erased_term ts ->
      wf t0 0 ->
      wf ts 1 ->
      subset (fv t0) (support Γ) ->
      subset (fv ts) (support Γ) ->
      [ Γ ⊨ t ⤳* t' ] ->
      [ Γ ⊨ tmatch t t0 ts ⤳* tmatch t' t0 ts ]

| DBListMatch1:
    forall Γ t t1 t2 v,
      is_erased_term t2 ->
      wf t2 2 ->
      subset (fv t2) (support Γ) ->
      [ Γ ⊨ t ⤳* tnil ] ->
      [ Γ ⊨ t1 ⤳* v ] ->
      [ Γ ⊨ list_match t t1 t2 ⤳* v ]

| DBListMatch2:
    forall Γ t1 t2 h t v,
      wf t1 0 ->
      wf t2 2 ->
      is_erased_term t1 ->
      is_erased_term t2 ->
      subset (fv t1) (support Γ) ->
      subset (fv t2) (support Γ) ->
      [ Γ ⊫ t : List ] ->
      [ Γ ⊨ t ⤳* tcons h t ] ->
      [ Γ ⊨ open 0 (open 1 t2 h) t ⤳* v ] ->
      [ Γ ⊨ list_match t t1 t2 ⤳* v ]

| DBListMatch3:
    forall Γ t t' t1 t2,
      is_erased_term t1 ->
      is_erased_term t2 ->
      wf t1 0 ->
      wf t2 2 ->
      subset (fv t1) (support Γ) ->
      subset (fv t2) (support Γ) ->
      [ Γ ⊨ t ⤳* t' ] ->
      [ Γ ⊨ list_match t t1 t2 ⤳* list_match t' t1 t2 ]

| DBLeft:
    forall Γ t v,
      [ Γ ⊨ t ⤳* v ] ->
      [ Γ ⊨ tleft t ⤳* tleft v ]

| DBRight:
    forall Γ t v,
      [ Γ ⊨ t ⤳* v ] ->
      [ Γ ⊨ tright t ⤳* tright v ]

| DBFix0:
    forall Γ t default v,
      wf default 0 ->
      wf t 1 ->
      is_erased_term default ->
      is_erased_term t ->
      subset (fv default) (support Γ) ->
      subset (fv t) (support Γ) ->
      [ Γ ⊨ default ⤳* v ] ->
      [ Γ ⊨ fix_default' t default zero  ⤳* v ]

| DBFix:
    forall Γ t default fuel v,
      is_nat_value fuel ->
      wf default 0 ->
      wf t 1 ->
      is_erased_term default ->
      is_erased_term t ->
      subset (fv default) (support Γ) ->
      subset (fv t) (support Γ) ->
      [ Γ ⊨ open 0 t (fix_default' t default fuel) ⤳* v ] ->
      [ Γ ⊨ fix_default' t default (succ fuel) ⤳* v ]

| DBRefl:
    forall Γ v,
      is_erased_term v ->
      wf v 0 ->
      subset (fv v) (support Γ) ->
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
  forall t1 t2,
    is_erased_term t1 ->
    is_erased_term t2 ->
    wf t1 0 ->
    wf t2 0 ->
    pfv t1 term_var = nil ->
    pfv t2 term_var = nil ->
    scbv_normalizing t1 ->
    scbv_normalizing t2 ->
    [ pi1 (pp t1 t2) ≡ t1 ].
Proof.
  unfold scbv_normalizing; steps.
  apply equivalent_trans with v0.
  - equivalent_star.
    eapply star_trans; eauto with cbvlemmas.
    eapply star_trans; eauto with cbvlemmas.
    eauto using star_one with smallstep.
  - apply equivalent_sym; equivalent_star.
Qed.

Lemma equivalent_pi2_pp:
  forall t1 t2,
    is_erased_term t1 ->
    is_erased_term t2 ->
    wf t1 0 ->
    wf t2 0 ->
    pfv t1 term_var = nil ->
    pfv t2 term_var = nil ->
    scbv_normalizing t1 ->
    scbv_normalizing t2 ->
    [ pi2 (pp t1 t2) ≡ t2 ].
Proof.
  unfold scbv_normalizing; steps.
  apply equivalent_trans with v.
  - equivalent_star.
    eapply star_trans; eauto with cbvlemmas.
    eapply star_trans; eauto with cbvlemmas.
    eauto using star_one with smallstep.
  - apply equivalent_sym; equivalent_star.
Qed.

Lemma lookup_value:
  forall l x v,
    are_values l ->
    lookup Nat.eq_dec l x = Some v ->
    cbv_value v.
Proof.
  induction l; steps; eauto.
Qed.

Lemma satisfies_are_values:
  forall l ρ Γ,
    valid_interpretation ρ ->
    satisfies (reducible_values ρ) Γ l ->
    are_values l.
Proof.
  induction l; repeat step || step_inversion satisfies; eauto with values.
Qed.

Lemma typable_normalizing:
  forall Θ Γ t T ρ l,
    [ Θ; Γ ⊨ t : T ] ->
    satisfies (reducible_values ρ) Γ l ->
    valid_interpretation ρ ->
    Θ = support ρ ->
    scbv_normalizing (psubstitute t l term_var).
Proof.
  unfold scbv_normalizing, open_reducible, reduces_to;
    repeat step || t_instantiate_sat3; eauto with values.
Qed.

Lemma delta_beta_first:
  forall Γ t t1 t2,
    is_erased_term t1 ->
    is_erased_term t2 ->
    wf t1 0 ->
    wf t2 0 ->
    subset (fv t1) (support Γ) ->
    subset (fv t2) (support Γ) ->
    [ Γ ⊫ t1 : T_top ] ->
    [ Γ ⊫ t2 : T_top ] ->
    [ Γ ⊫ t ≡ pp t1 t2 ] ->
    [ Γ ⊫ pi1 t ≡ t1 ].
Proof.
  unfold open_equivalent; repeat step; eauto.
  eapply equivalent_trans; eauto using equivalent_pi1.
  apply equivalent_pi1_pp; steps; eauto with erased wf fv;
    eauto using typable_normalizing.
Qed.

Lemma delta_beta_second:
  forall Γ t t1 t2,
    is_erased_term t1 ->
    is_erased_term t2 ->
    wf t1 0 ->
    wf t2 0 ->
    subset (fv t1) (support Γ) ->
    subset (fv t2) (support Γ) ->
    [ Γ ⊫ t1 : T_top ] ->
    [ Γ ⊫ t2 : T_top ] ->
    [ Γ ⊫ t ≡ pp t1 t2 ] ->
    [ Γ ⊫ pi2 t ≡ t2 ].
Proof.
  unfold open_equivalent; repeat step; eauto.
  eapply equivalent_trans; eauto using equivalent_pi2.
  apply equivalent_pi2_pp; steps; eauto with erased wf fv;
    eauto using typable_normalizing.
Qed.

Lemma equivalent_beta2:
  forall f t,
    is_erased_term t ->
    is_erased_term f ->
    pfv t term_var = nil ->
    pfv f term_var = nil ->
    wf t 0 ->
    wf f 1 ->
    scbv_normalizing t ->
    equivalent_terms (app (notype_lambda f) t) (open 0 f t).
Proof.
  unfold scbv_normalizing; repeat step; eauto using equivalent_beta.
Qed.

Lemma delta_beta_app1:
  forall Γ f t t' v body,
    is_erased_term t' ->
    is_erased_term body ->
    pfv t' term_var = nil ->
    pfv body term_var = nil ->
    wf t' 0 ->
    wf body 0 ->
    [ Γ ⊫ t' : T_top ] ->
    [ Γ ⊫ t ≡ t' ] ->
    [ Γ ⊫ f ≡ notype_lambda body ] ->
    [ Γ ⊫ open 0 body t' ≡ v ] ->
    [ Γ ⊫ app f t ≡ v ].
Proof.
  unfold open_equivalent; repeat step || t_instantiate_sat3 || t_substitutions.
  eapply equivalent_trans; eauto using equivalent_app.
  eapply equivalent_trans; eauto; repeat step || t_substitutions.
  eapply equivalent_beta2; steps; eauto using typable_normalizing;
    eauto with erased fv wf.
Qed.

Lemma delta_beta_app2:
  forall Θ Γ f f' t t',
    [ Θ; Γ ⊨ t ≡ t' ] ->
    [ Θ; Γ ⊨ f ≡ f' ] ->
    [ Θ; Γ ⊨ app f t ≡ app f' t' ].
Proof.
  unfold open_equivalent; repeat step || t_instantiate_sat3 || t_substitutions;
    eauto using equivalent_app.
Qed.

Lemma equivalent_match_scrut:
  forall t t' t0 ts,
    is_erased_term t0 ->
    is_erased_term ts ->
    wf t0 0 ->
    wf ts 1 ->
    pfv t0 term_var = nil ->
    pfv ts term_var = nil ->
    [ t ≡ t' ] ->
    [ tmatch t t0 ts ≡ tmatch t' t0 ts ].
Proof.
  intros.
  unshelve epose proof (equivalent_context (tmatch (lvar 0 term_var) t0 ts) _ _ _ _ _ H5);
    repeat step || list_utils || open_none;
    eauto with wf.
Qed.

Lemma equivalent_list_match_scrut:
  forall t t' t1 t2,
    is_erased_term t1 ->
    is_erased_term t2 ->
    wf t1 0 ->
    wf t2 2 ->
    pfv t1 term_var = nil ->
    pfv t2 term_var = nil ->
    [ t ≡ t' ] ->
    [ list_match t t1 t2 ≡ list_match t' t1 t2 ].
Proof.
  intros.
  unshelve epose proof (equivalent_context (list_match (lvar 0 term_var) t1 t2) _ _ _ _ _ H5);
    repeat step || list_utils || open_none ||
           (rewrite (open_none t1) in * by eauto with wf) ||
           (rewrite open_none in H6 by (steps; eauto with wf step_tactic));
    eauto 3 with wf erased fv step_tactic.
Qed.

Lemma delta_beta_match_zero:
  forall Θ Γ t t0 ts v,
    is_erased_term ts ->
    wf ts 1 ->
    subset (fv ts) (support Γ) ->
    [ Θ; Γ ⊨ t ≡ zero ] ->
    [ Θ; Γ ⊨ t0 ≡ v ] ->
    [ Θ; Γ ⊨ tmatch t t0 ts ≡ v ].
Proof.
  unfold open_equivalent; repeat step || t_instantiate_sat3.
  eapply equivalent_trans; eauto.
  eapply equivalent_trans; try apply equivalent_match_scrut; eauto;
    eauto with erased wf fv;
    equivalent_star.
Qed.

Lemma delta_beta_match_succ:
  forall Γ t t0 ts t' v,
    is_erased_term t0 ->
    is_erased_term ts ->
    wf t0 0 ->
    wf ts 1 ->
    subset (fv t0) (support Γ) ->
    subset (fv ts) (support Γ) ->
    subset (fv v) (support Γ) ->
    [ Γ ⊫ t' : T_top ] ->
    [ Γ ⊫ t ≡ succ t' ] ->
    [ Γ ⊫ open 0 ts t' ≡ v ] ->
    [ Γ ⊫ tmatch t t0 ts ≡ v ].
Proof.
  unfold open_equivalent, open_reducible;
    repeat step || t_instantiate_sat3_nil || t_substitutions.
  eapply equivalent_trans; eauto; repeat step || t_substitutions.
  eapply equivalent_trans; try apply equivalent_match_scrut;
    eauto with erased fv wf.
  top_level_unfold reduces_to; steps.
  eapply equivalent_trans; try apply equivalent_match_scrut;
    eauto with erased fv wf;
    try solve [ apply equivalent_succ; equivalent_star ].

  eapply equivalent_trans; try solve [ equivalent_star ].
  apply equivalent_context; eauto with erased wf fv.
  apply equivalent_sym; equivalent_star.
Qed.

Lemma delta_beta_match_scrut:
  forall Θ Γ t t' t0 ts,
    is_erased_term t0 ->
    is_erased_term ts ->
    wf t0 0 ->
    wf ts 1 ->
    subset (fv t0) (support Γ) ->
    subset (fv ts) (support Γ) ->
    [ Θ; Γ ⊨ t ≡ t' ] ->
    [ Θ; Γ ⊨ tmatch t t0 ts ≡ tmatch t' t0 ts ].
Proof.
  unfold open_equivalent; steps; apply equivalent_match_scrut;
    eauto with erased wf fv.
Qed.

Opaque list_match.

Lemma delta_beta_list_match_nil:
  forall Θ Γ t t1 t2 v,
    is_erased_term t2 ->
    wf t2 2 ->
    subset (fv t2) (support Γ) ->
    [ Θ; Γ ⊨ t ≡ tnil ] ->
    [ Θ; Γ ⊨ t1 ≡ v ] ->
    [ Θ; Γ ⊨ list_match t t1 t2 ≡ v ].
Proof.
  unfold open_equivalent; repeat step || t_instantiate_sat3 || rewrite substitute_list_match;
    eauto with wf.
  eapply equivalent_trans; eauto.
  eapply equivalent_trans; try apply equivalent_list_match_scrut; eauto;
    eauto with erased wf fv;
    try solve [ equivalent_star ].

  evaluate_list_match; repeat step; eauto with wf fv erased.
  - apply reducible_nil; auto.
  - equivalent_star; eauto 3 with wf erased fv step_tactic.
  - unfold tcons in *; steps.
Qed.

Opaque List.

Lemma equivalent_right_eval_left:
  forall t t' v,
    cbv_value v  ->
    [ t ≡ tright t' ] ->
    t ~>* tleft v ->
    False.
Proof.
  intros.
  apply right_left_equivalence with t' v; auto.
  eapply equivalent_trans; eauto using equivalent_sym; equivalent_star.
Qed.

Lemma equivalent_right_eval_nil:
  forall t t',
    [ t ≡ tright t' ] ->
    t ~>* tnil ->
    False.
Proof.
  intros.
  apply equivalent_right_eval_left with t t' uu; steps.
Qed.

Lemma equivalent_context2:
  forall C t1 t1' t2 t2',
    is_erased_term C ->
    wf C 2 ->
    pfv C term_var = nil ->
    [ t1 ≡ t1' ] ->
    [ t2 ≡ t2' ] ->
    [ open 0 (open 1 C t1) t2 ≡ open 0 (open 1 C t1') t2' ].
Proof.
  intros.
  eapply equivalent_trans; try solve [ apply equivalent_context; steps; eauto with erased wf fv ].
  repeat rewrite (swap_term_holes_open C); steps; eauto with wf.
  apply equivalent_context; steps; eauto with erased wf fv.
Qed.

Lemma delta_beta_list_match_cons:
  forall Γ h t t1 t2 v,
    wf t1 0 ->
    wf t2 2 ->
    is_erased_term t1 ->
    is_erased_term t2 ->
    subset (fv t1) (support Γ) ->
    subset (fv t2) (support Γ) ->
    [ Γ ⊫ t : List ] ->
    [ Γ ⊫ t ≡ tcons h t ] ->
    [ Γ ⊫ open 0 (open 1 t2 h) t ≡ v ] ->
    [ Γ ⊫ list_match t t1 t2 ≡ v ].
Proof.
  unfold open_equivalent, open_reducible;
    repeat step || t_instantiate_sat3_nil || t_substitutions || rewrite substitute_list_match;
    eauto with wf.

  eapply equivalent_trans; eauto.

  eapply equivalent_trans; try apply equivalent_list_match_scrut; eauto;
    eauto with erased wf fv;
    try solve [ equivalent_star ].

  evaluate_list_match2; repeat step || t_invert_star || unfold tcons in *; eauto with wf fv erased;
    eauto using reducibility_equivalent2, is_erased_list, wf_list;
    try solve [ unfold tnil in *; repeat step || t_invert_star ].

  eapply equivalent_trans; eauto.
  apply_anywhere right_right_star.
  apply equivalent_context2; steps; eauto with fv wf erased.
  - apply equivalent_sym; equivalent_star; eauto using pp_pp_star_1.
  - apply equivalent_sym; equivalent_star; eauto using pp_pp_star_2.
Qed.

Lemma delta_beta_list_match_scrut:
  forall Θ Γ t t' t1 t2,
    is_erased_term t1 ->
    is_erased_term t2 ->
    wf t1 0 ->
    wf t2 2 ->
    subset (fv t1) (support Γ) ->
    subset (fv t2) (support Γ) ->
    [ Θ; Γ ⊨ t ≡ t' ] ->
    [ Θ; Γ ⊨ list_match t t1 t2 ≡ list_match t' t1 t2 ].
Proof.
  unfold open_equivalent; repeat step || rewrite substitute_list_match;
    try apply equivalent_list_match_scrut;
    eauto with erased wf fv.
Qed.

Lemma open_equivalent_context:
  forall Θ Γ t1 t2 C,
    is_erased_term C ->
    wf C 1 ->
    subset (fv C) (support Γ) ->
    [ Θ; Γ ⊨ t1 ≡ t2 ] ->
    [ Θ; Γ ⊨ open 0 C t1 ≡ open 0 C t2 ].
Proof.
  unfold open_equivalent;
    repeat step || t_instantiate_sat3 || t_substitutions || apply equivalent_context;
    eauto with fv wf erased.
Qed.

Lemma delta_beta_left:
  forall Θ Γ t t',
    [ Θ; Γ ⊨ t ≡ t' ] ->
    [ Θ; Γ ⊨ tleft t ≡ tleft t' ].
Proof.
  intros.
  unshelve epose proof (open_equivalent_context _ _ _ _ (tleft (lvar 0 term_var)) _ _ _ H);
    steps; eauto with sets.
Qed.

Lemma delta_beta_right:
  forall Θ Γ t t',
    [ Θ; Γ ⊨ t ≡ t' ] ->
    [ Θ; Γ ⊨ tright t ≡ tright t' ].
Proof.
  intros.
  unshelve epose proof (open_equivalent_context _ _ _ _ (tright (lvar 0 term_var)) _ _ _ H);
    steps; eauto with sets.
Qed.

Opaque fix_default'.

Lemma delta_beta_fix_zero:
  forall Γ t default v,
    wf default 0 ->
    wf t 1 ->
    is_erased_term default ->
    is_erased_term t ->
    subset (fv default) (support Γ) ->
    subset (fv t) (support Γ) ->
    [ Γ ⊫ default ≡ v ] ->
    [ Γ ⊫ fix_default' t default zero ≡ v ].
Proof.
  unfold open_equivalent; repeat step || rewrite subst_fix_default; eauto with wf.

  evaluate_fix_default; steps; eauto with wf.
  eapply equivalent_trans; eauto.

  equivalent_star; eauto 4 with fv erased wf step_tactic.
Qed.

Lemma delta_beta_fix_succ:
  forall Γ t default fuel v,
    is_nat_value fuel ->
    wf default 0 ->
    wf t 1 ->
    is_erased_term default ->
    is_erased_term t ->
    subset (fv default) (support Γ) ->
    subset (fv t) (support Γ) ->
    [ Γ ⊫ open 0 t (fix_default' t default fuel) ≡ v ] ->
    [ Γ ⊫ fix_default' t default (succ fuel) ≡ v ].
Proof.
  unfold open_equivalent; repeat step || t_instantiate_sat3_nil || t_substitutions ||
                                 rewrite subst_fix_default in * by eauto with wf.
  evaluate_fix_default; repeat step || rewrite (substitute_nothing5 fuel) in * by eauto with fv;
    eauto with wf; eauto with is_nat_value.
  eapply equivalent_trans; eauto.
  equivalent_star; eauto with erased wf fv step_tactic.
Qed.

Lemma delta_beta_obs_equiv:
  forall Γ t1 t2,
    [ Γ ⊨ t1 ⤳* t2 ] ->
    [ Γ ⊫ t1 ≡ t2 ].
Proof.
  induction 1; repeat step;
    eauto using delta_beta_var;
    eauto using delta_beta_pair;
    eauto using delta_beta_first;
    eauto using delta_beta_second;
    eauto using delta_beta_app1;
    eauto using delta_beta_app2;
    eauto using delta_beta_match_zero;
    eauto using delta_beta_match_succ;
    eauto using delta_beta_match_scrut;
    eauto using delta_beta_list_match_nil;
    eauto using delta_beta_list_match_cons;
    eauto using delta_beta_list_match_scrut;
    eauto using delta_beta_left;
    eauto using delta_beta_right;
    eauto using delta_beta_fix_zero;
    eauto using delta_beta_fix_succ;
    eauto using open_equivalent_refl.
Qed.
