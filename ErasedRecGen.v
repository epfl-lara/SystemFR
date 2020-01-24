Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Equations.Equations.

Require Export SystemFR.ErasedRec.
Require Export SystemFR.ErasedNat.

Require Export SystemFR.FVLemmasLists.
Require Export SystemFR.WFLemmasLists.

Require Export SystemFR.StrictPositivityPush.
Require Export SystemFR.StrictPositivityPull.
Require Export SystemFR.StrictPositivitySubst.

Require Export SystemFR.BaseTypeLemmas.
Require Export SystemFR.BaseTypeSyntaxLemmas.

Require Import Omega.

Opaque reducible_values.
Opaque strictly_positive.
Opaque makeFresh.

Lemma non_empty_nat:
  forall theta, non_empty theta T_nat.
Proof.
  unfold non_empty; intros; exists zero; repeat step || simp_red.
Qed.

Ltac t_instantiate_reducible3 :=
  match goal with
  | H1: reducible_values _ ?v ?T, H3: forall a, _ -> _ -> _ |- _ =>
    poseNew (Mark (v,H3) "t_instantiate_reducible");
    unshelve epose proof (H3 v _ H1)
  end.


(** Rules for unfold **)

Lemma reducible_values_unfold_gen:
  forall T0 Ts theta v X,
    wf T0 0 ->
    wf Ts 0 ->
    twf T0 0 ->
    twf Ts 1 ->
    ~(X ∈ pfv Ts type_var) ->
    strictly_positive (topen 0 Ts (fvar X type_var)) (X :: nil) ->
    is_erased_type T0 ->
    is_erased_type Ts ->
    pfv T0 term_var = nil ->
    pfv Ts term_var = nil ->
    valid_interpretation theta ->
    reducible_values theta v (intersect T0 Ts) ->
    reducible_values theta v (topen 0 Ts (intersect T0 Ts)).
Proof.
  unfold intersect in *; repeat step.
  apply strictly_positive_push_forall2 with X;
    repeat match goal with
           | H: reducible_values _ _ (T_forall _ _) |- _ => simp reducible_values in H
           | H: reducible_values _ _ (T_rec _ _ _) |- _ => simp reducible_values in H
           | H1: reducible_values _ ?v T_nat, H3: forall a, _ -> _ -> _ |- _ =>
             poseNew (Mark (v,H3) "t_instantiate_reducible");
             unshelve epose proof (H3 (succ v) _ _ _ _)
           | _ => step || (rewrite open_none in * by steps) || apply reducible_values_succ || list_utils
           end;
      eauto using non_empty_nat;
      eauto with erased;
      try solve [ t_closing ];
      eauto 3 using smallstep_succ_zero with exfalso.

  apply reducibility_subst_head in H23;
    repeat step || t_invert_star || list_utils ||
           (rewrite (is_erased_term_tfv v') in * by eauto with erased);
      eauto with twf wf erased fv values.

  lazymatch goal with
  | H: star scbv_step ?v1 ?v2 |- _ =>
    unshelve epose proof (star_smallstep_value v1 v2 H _); clear H2
  end;
    repeat step || list_utils;
    eauto with values.
Qed.

Lemma reducible_unfold_gen:
  forall T0 Ts theta t X,
    wf T0 0 ->
    wf Ts 0 ->
    twf T0 0 ->
    twf Ts 1 ->
    ~(X ∈ pfv Ts type_var) ->
    strictly_positive (topen 0 Ts (fvar X type_var)) (X :: nil) ->
    is_erased_type T0 ->
    is_erased_type Ts ->
    pfv T0 term_var = nil ->
    pfv Ts term_var = nil ->
    valid_interpretation theta ->
    reducible theta t (intersect T0 Ts) ->
    reducible theta t (topen 0 Ts (intersect T0 Ts)).
Proof.
  unfold reducible, reduces_to; steps.
  exists v; repeat step || apply star_unfold_fold;
    try solve [ t_closing ];
    eauto using reducible_values_unfold_gen.
Qed.

Lemma open_reducible_unfold_gen:
  forall T0 Ts tvars gamma t X,
    wf T0 0 ->
    wf Ts 0 ->
    twf T0 0 ->
    twf Ts 1 ->
    ~(X ∈ pfv Ts type_var) ->
    strictly_positive (topen 0 Ts (fvar X type_var)) (X :: nil) ->
    is_erased_type T0 ->
    is_erased_type Ts ->
    subset (fv T0) (support gamma) ->
    subset (fv Ts) (support gamma) ->
    [ tvars; gamma ⊨ t : intersect T0 Ts ] ->
    [ tvars; gamma ⊨ t : topen 0 Ts (intersect T0 Ts) ].
Proof.
  unfold open_reducible;
    repeat step || rewrite substitute_topen;
    eauto with twf.

  apply reducible_unfold_gen with
    (makeFresh (
      pfv (psubstitute Ts lterms term_var) type_var ::
      pfv Ts type_var ::
      nil
    )); steps;
    eauto with wf;
    eauto with fv;
    eauto with twf;
    eauto with erased;
    try finisher.

  rewrite substitute_topen2;
    repeat step;
    eauto with twf.

  apply strictly_positive_subst;
    repeat step || apply is_erased_type_topen; eauto with twf; eauto with fv.
  eapply strictly_positive_rename_one; eauto;
    repeat step; try finisher.
Qed.

(** Rules for unfold_in **)

Lemma reducible_unfold_in_gen:
  forall T0 Ts theta t1 t2 X T,
    wf T0 0 ->
    wf Ts 0 ->
    twf T0 0 ->
    twf Ts 1 ->
    wf t1 0 ->
    wf t2 0 ->
    pfv t1 term_var = nil ->
    pfv t2 term_var = nil ->
    is_erased_term t1 ->
    is_erased_term t2 ->
    ~(X ∈ pfv Ts type_var) ->
    strictly_positive (topen 0 Ts (fvar X type_var)) (X :: nil) ->
    is_erased_type T0 ->
    is_erased_type Ts ->
    pfv T0 term_var = nil ->
    pfv Ts term_var = nil ->
    valid_interpretation theta ->
    reducible theta t1 (intersect T0 Ts) ->
    (forall v,
      equivalent_terms t1 v ->
      reducible_values theta v (topen 0 Ts (intersect T0 Ts)) ->
      reducible theta (open 0 t2 v) T) ->
    reducible theta (app (notype_lambda t2) t1) T.
Proof.
  intros.
  match goal with
  | H: reducible _ _ (intersect _ _) |- _ => unfold reducible, reduces_to in H
  end; steps.

  eapply star_backstep_reducible; eauto with cbvlemmas values;
    repeat step || list_utils;
    eauto with wf twf fv erased.

  eapply backstep_reducible; eauto with smallstep values;
    repeat step || list_utils;
    eauto with wf twf fv erased;
    try t_closing.

  apply_any;
    eauto using reducible_values_unfold_gen;
    eauto using equivalent_star.
Qed.

Lemma open_reducible_unfold_in_gen:
  forall T0 Ts tvars gamma t1 t2 X T p y,
    ~(p ∈ tvars) ->
    ~(p ∈ pfv_context gamma term_var) ->
    ~(p ∈ support gamma) ->
    ~(p ∈ fv t1) ->
    ~(p ∈ fv t2) ->
    ~(p ∈ fv T0) ->
    ~(p ∈ fv Ts) ->
    ~(p ∈ fv T) ->
    ~(y ∈ tvars) ->
    ~(y ∈ pfv_context gamma term_var) ->
    ~(y ∈ support gamma) ->
    ~(y ∈ fv t1) ->
    ~(y ∈ fv t2) ->
    ~(y ∈ fv T0) ->
    ~(y ∈ fv Ts) ->
    ~(y ∈ fv T) ->
    wf T0 0 ->
    wf Ts 0 ->
    twf T0 0 ->
    twf Ts 1 ->
    wf t1 0 ->
    wf t2 0 ->
    is_erased_term t1 ->
    is_erased_term t2 ->
    subset (pfv t1 term_var) (support gamma) ->
    subset (pfv t2 term_var) (support gamma) ->
    ~(p = y) ->
    ~(X ∈ pfv Ts type_var) ->
    strictly_positive (topen 0 Ts (fvar X type_var)) (X :: nil) ->
    is_erased_type T0 ->
    is_erased_type Ts ->
    subset (fv T0) (support gamma) ->
    subset (fv Ts) (support gamma) ->
    [ tvars; gamma ⊨ t1 : intersect T0 Ts ] ->
    [ tvars; (p, T_equiv t1 (fvar y term_var)) ::
             (y, topen 0 Ts (intersect T0 Ts)) ::
             gamma ⊨
        open 0 t2 (fvar y term_var) : T ] ->
    [ tvars; gamma ⊨ app (notype_lambda t2) t1 : T ].
Proof.
  unfold open_reducible;
    repeat step || rewrite substitute_topen;
    eauto with twf.

  apply reducible_unfold_in_gen with
    (psubstitute T0 lterms term_var)
    (psubstitute Ts lterms term_var)
    (makeFresh (
      pfv (psubstitute Ts lterms term_var) type_var ::
      pfv Ts type_var ::
      nil
    )); steps;
    eauto with wf;
    eauto with twf;
    eauto with erased;
    eauto with fv;
    try finisher.

  - rewrite substitute_topen2;
      repeat step;
      eauto with twf.

    apply strictly_positive_subst;
      repeat step || apply is_erased_type_topen; eauto with twf; eauto with fv.
    eapply strictly_positive_rename_one; eauto;
      repeat step; try finisher.

  - unshelve epose proof (H33 theta ((p, uu) :: (y,v) :: lterms) _ _ _);
      repeat match goal with
             | |- reducible_values _ _ (T_equiv _ _) => simp reducible_values
             | _ => step || list_utils || nodup || apply SatCons || t_substitutions || fv_open
             end;
        t_closer.
Qed.


(** Fold Rules **)

Lemma reducible_values_fold_gen:
  forall T0 Ts theta v X,
    wf T0 0 ->
    wf Ts 0 ->
    twf T0 0 ->
    twf Ts 1 ->
    ~(X ∈ pfv Ts type_var) ->
    strictly_positive (topen 0 Ts (fvar X type_var)) (X :: nil) ->
    is_erased_type T0 ->
    is_erased_type Ts ->
    pfv T0 term_var = nil ->
    pfv Ts term_var = nil ->
    valid_interpretation theta ->
    (forall v,
        reducible_values theta v (topen 0 Ts (T_rec zero T0 Ts)) ->
        reducible_values theta v T0) ->
    reducible_values theta v (topen 0 Ts (intersect T0 Ts)) ->
    reducible_values theta v (intersect T0 Ts).
Proof.
  unfold intersect in *; repeat step.
  simp reducible_values; repeat step || (rewrite open_none in * by steps); try solve [ t_closing ].

  unshelve epose proof
           (strictly_positive_pull_forall _ _ _ _ _ X _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H11) as HH;
    repeat step || list_utils; eauto using non_empty_nat;
      eauto with wf.

  simp_red_nat.
  t_invert_nat_value; repeat step || simp_red;
    try solve [ t_closing ];
    eauto with smallstep.
  - (* case a = 0, we use the decreasing property *)
    left; repeat step || apply_any.
    unshelve epose proof (HH zero _);
      repeat step || simp_red || rewrite open_none in * by steps.
  - (* case a = n+1 *)
    right; exists v0, (makeFresh (
                     support theta ::
                     pfv v0 type_var ::
                     pfv T0 type_var ::
                     pfv Ts type_var ::
                     (X :: nil) ::
                     nil));
    repeat step;
    try finisher.

    apply reducibility_subst_head2;
      repeat step || list_utils;
      try finisher;
      eauto with wf twf.

    unshelve epose proof (HH v0 _); repeat step || simp_red || rewrite open_none in * by steps.
Qed.

Lemma reducible_fold_gen:
  forall T0 Ts theta t X,
    wf T0 0 ->
    wf Ts 0 ->
    twf T0 0 ->
    twf Ts 1 ->
    ~(X ∈ pfv Ts type_var) ->
    strictly_positive (topen 0 Ts (fvar X type_var)) (X :: nil) ->
    is_erased_type T0 ->
    is_erased_type Ts ->
    pfv T0 term_var = nil ->
    pfv Ts term_var = nil ->
    valid_interpretation theta ->
    (forall v,
        reducible_values theta v (topen 0 Ts (T_rec zero T0 Ts)) ->
        reducible_values theta v T0) ->
    reducible theta t (topen 0 Ts (intersect T0 Ts)) ->
    reducible theta t (intersect T0 Ts).
Proof.
  unfold reducible, reduces_to;
    repeat step.
  exists v; repeat step;
    try solve [ t_closing ];
    eauto using reducible_values_fold_gen;
    eauto with cbvlemmas.
Qed.

Lemma open_reducible_fold_gen:
  forall T0 Ts tvars gamma t X,
    wf T0 0 ->
    wf Ts 0 ->
    twf T0 0 ->
    twf Ts 1 ->
    ~(X ∈ pfv Ts type_var) ->
    strictly_positive (topen 0 Ts (fvar X type_var)) (X :: nil) ->
    is_erased_type T0 ->
    is_erased_type Ts ->
    subset (fv T0) (support gamma) ->
    subset (fv Ts) (support gamma) ->
    (forall theta l,
        valid_interpretation theta ->
        satisfies (reducible_values theta) gamma l ->
        support theta = tvars ->
        (forall v,
            reducible_values theta v
                             (topen 0 (psubstitute Ts l term_var)
                                    (T_rec zero
                                           (psubstitute T0 l term_var)
                                           (psubstitute Ts l term_var))) ->
            reducible_values theta v (psubstitute T0 l term_var))) ->
    [ tvars; gamma ⊨ t : topen 0 Ts (intersect T0 Ts) ] ->
    [ tvars; gamma ⊨ t : intersect T0 Ts ].
Proof.
  unfold open_reducible; steps.
  apply reducible_fold_gen with X;
    repeat step || apply subst_erased_type || t_instantiate_sat4;
    eauto with wf;
    eauto with twf;
    eauto using pfv_in_subst with fv;
    eauto with erased.

  - rewrite substitute_topen2;
      repeat step || apply strictly_positive_subst || apply is_erased_type_topen ||
      eauto with twf;
      eauto with fv.
  - rewrite_anywhere substitute_topen; eauto with twf.
Qed.

Lemma open_reducible_fold_gen2:
  forall T0 Ts tvars gamma t X,
    wf T0 0 ->
    wf Ts 0 ->
    twf T0 0 ->
    twf Ts 1 ->
    ~(X ∈ pfv Ts type_var) ->
    strictly_positive (topen 0 Ts (fvar X type_var)) (X :: nil) ->
    is_erased_type T0 ->
    is_erased_type Ts ->
    subset (fv T0) (support gamma) ->
    subset (fv Ts) (support gamma) ->
    base_type X (topen 0 Ts (fvar X type_var)) T0 ->
    [ tvars; gamma ⊨ t : topen 0 Ts (intersect T0 Ts) ] ->
    [ tvars; gamma ⊨ t : intersect T0 Ts ].
Proof.
  intros; apply open_reducible_fold_gen with X; steps.
  apply base_type_approx with X (topen 0 Ts (fvar X type_var))
    (fun v => reducible_values theta v (T_rec zero (psubstitute T0 l term_var) (psubstitute Ts l term_var)));
    repeat step || apply reducibility_is_candidate || list_utils;
    eauto with wf fv;
    eauto with erased.

  rewrite <- substitute_topen2; steps; eauto with twf.
  apply reducibility_subst_head2;
    repeat step || list_utils || apply reducibility_is_candidate ||
           rewrite fv_subst_different_tag in * by (steps; eauto with fv);
    eauto with fv wf twf erased;
    eauto using reducibility_is_candidate.
Qed.
