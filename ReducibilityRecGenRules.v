Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Equations.Equations.

Require Import SystemFR.Sets.
Require Import SystemFR.Tactics.
Require Import SystemFR.Syntax.
Require Import SystemFR.TermList.
Require Import SystemFR.SmallStep.
Require Import SystemFR.AssocList.
Require Import SystemFR.EquivalenceLemmas.
Require Import SystemFR.ListUtils.
Require Import SystemFR.SubstitutionLemmas.
Require Import SystemFR.StarRelation.
Require Import SystemFR.SizeLemmas.
Require Import SystemFR.StarLemmas.
Require Import SystemFR.TypeErasure.
Require Import SystemFR.SubstitutionErase.
Require Import SystemFR.TreeLists.
Require Import SystemFR.TermListReducible.
Require Import SystemFR.StarInversions.
Require Import SystemFR.EquivalentWithRelation.
Require Import SystemFR.EqualWithRelation.
Require Import SystemFR.TermProperties.
Require Import SystemFR.ErasedTermLemmas.
Require Import SystemFR.OpenTOpen.
Require Import SystemFR.StarInversions.

Require Import SystemFR.Equivalence.
Require Import SystemFR.EquivalenceLemmas.

Require Import SystemFR.ReducibilityCandidate.
Require Import SystemFR.ReducibilityDefinition.
Require Import SystemFR.ReducibilityLemmas.
Require Import SystemFR.ReducibilityRenaming.
Require Import SystemFR.ReducibilityUnused.
Require Import SystemFR.ReducibilitySubst.
Require Import SystemFR.ReducibilityRecRules.
Require Import SystemFR.ReducibilityNatRules.
Require Import SystemFR.RedTactics.

Require Import SystemFR.Freshness.


Require Import SystemFR.WFLemmas.
Require Import SystemFR.FVLemmasLists.
Require Import SystemFR.WFLemmasLists.

Require Import SystemFR.NoTypeFVar.

Require Import SystemFR.StrictPositivity.
Require Import SystemFR.StrictPositivityLemmas.
Require Import SystemFR.StrictPositivityLemma.
Require Import SystemFR.StrictPositivityPush.
Require Import SystemFR.StrictPositivityPull.
Require Import SystemFR.StrictPositivitySubst.

Require Import SystemFR.BaseType.
Require Import SystemFR.BaseTypeLemmas.
Require Import SystemFR.BaseTypeSyntaxLemmas.

Require Import Omega.

Opaque reducible_values.
Opaque strictly_positive.
Opaque makeFresh.

Set Program Mode.

Lemma fold_in_intersect:
  forall theta t T0 Ts,
    wf T0 0 ->
    wf Ts 0 ->
    valid_interpretation theta ->
    reducible_values theta t (intersect T0 Ts) ->
    exists v, closed_value v /\ t = notype_tfold v.
Proof.
  unfold intersect;
    repeat match goal with
           | H: reducible_values _ _ (T_forall _ _) |- _ => simp reducible_values in H
           | _ => step || (rewrite open_none in * by steps)
           | H: _ |- _  => apply fold_in_rec with theta T0 Ts zero
           | H: forall a, _ -> _ |-  _ =>
               poseNew (Mark 0 "once");
               unshelve epose proof (H zero _ _)
           | _ => simp reducible_values
           end.
Qed.

Ltac t_fold_in_intersect :=
  match goal with
  | H1: valid_interpretation ?theta, H2: reducible_values ?theta ?t (intersect ?T0 ?Ts) |- _ =>
     is_var t;
     unshelve epose proof (fold_in_intersect theta t T0 Ts _ _ H1 H2)
  end.

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
    valid_interpretation theta ->
    reducible_values theta (notype_tfold v) (intersect T0 Ts) ->
    reducible_values theta v (topen 0 Ts (intersect T0 Ts)).
Proof.
  unfold intersect in *; repeat step.
  apply strictly_positive_push_forall2 with X;
    repeat match goal with
           | H: reducible_values _ _ (T_forall _ _) |- _ => simp reducible_values in H
           | H: reducible_values _ _ (T_rec _ _ _) |- _ => simp reducible_values in H
           | H1: reducible_values _ ?v T_nat, H3: forall a, _ -> _ -> _ |- _ =>
             poseNew (Mark (v,H3) "t_instantiate_reducible");
             unshelve epose proof (H3 (succ v) _ _)
           | _ => step || (rewrite open_none in * by steps) || apply reducible_values_succ
           end;
      eauto using non_empty_nat;
      eauto with berased;
      try solve [ t_closing ];
      eauto 3 using smallstep_succ_zero with falsity.

  apply reducibility_subst_head in H22;
    repeat step || t_invert_star || t_listutils ||
           (rewrite is_erased_term_tfv in H14 by (eauto with berased));
      eauto with btwf bwf berased.

  lazymatch goal with
  | H: star small_step ?v1 ?v2 |- _ =>
    unshelve epose proof (star_smallstep_value v1 v2 H _); clear H2
  end;
    repeat step || t_listutils;
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
    valid_interpretation theta ->
    reducible theta t (intersect T0 Ts) ->
    reducible theta (tunfold t) (topen 0 Ts (intersect T0 Ts)).
Proof.
  unfold reducible, reduces_to;
    repeat step || t_fold_in_intersect.
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
    open_reducible tvars gamma t (intersect T0 Ts) ->
    open_reducible tvars gamma (tunfold t) (topen 0 Ts (intersect T0 Ts)).
Proof.
  unfold open_reducible;
    repeat step || rewrite substitute_topen;
    eauto with btwf.

  apply reducible_unfold_gen with
    (makeFresh (
      pfv (psubstitute Ts lterms term_var) type_var ::
      pfv Ts type_var ::
      nil
    )); steps;
    eauto with bwf;
    eauto with btwf;
    eauto with berased;
    try finisher.

  rewrite substitute_topen2;
    repeat step;
    eauto with btwf.

  apply strictly_positive_subst;
    repeat step || apply is_erased_type_topen; eauto with btwf; eauto with bfv.
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
    valid_interpretation theta ->
    reducible theta t1 (intersect T0 Ts) ->
    (forall v,
      equivalent t1 (notype_tfold v) ->
      reducible_values theta v (topen 0 Ts (intersect T0 Ts)) ->
      reducible theta (open 0 t2 v) T) ->
    reducible theta (tunfold_in t1 t2) T.
Proof.
  intros.
  match goal with
  | H: reducible _ _ (intersect _ _) |- _ => unfold reducible, reduces_to in H
  end.
  repeat step || t_fold_in_intersect.
  eapply star_backstep_reducible; eauto with bsteplemmas;
    repeat step || t_listutils;
    eauto with bwf btwf bfv berased.
  unfold closed_value in *; steps.
  eapply backstep_reducible; eauto with smallstep;
    repeat step || t_listutils;
    eauto with bwf btwf bfv berased;
    try t_closing.
  apply_any;
    eauto using reducible_values_unfold_gen;
    eauto with b_equiv.
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
    open_reducible tvars gamma t1 (intersect T0 Ts) ->
    open_reducible tvars
             ((p, T_equal t1 (notype_tfold (fvar y term_var))) ::
              (y, topen 0 Ts (intersect T0 Ts)) ::
              gamma)
             (open 0 t2 (fvar y term_var)) T ->
    open_reducible tvars gamma (tunfold_in t1 t2) T.
Proof.
  unfold open_reducible;
    repeat step || rewrite substitute_topen;
    eauto with btwf.

  apply reducible_unfold_in_gen with
    (psubstitute T0 lterms term_var)
    (psubstitute Ts lterms term_var)
    (makeFresh (
      pfv (psubstitute Ts lterms term_var) type_var ::
      pfv Ts type_var ::
      nil
    )); steps;
    eauto with bwf;
    eauto with btwf;
    eauto with berased;
    eauto with bfv;
    try finisher.

  - rewrite substitute_topen2;
      repeat step;
      eauto with btwf.

    apply strictly_positive_subst;
      repeat step || apply is_erased_type_topen; eauto with btwf; eauto with bfv.
    eapply strictly_positive_rename_one; eauto;
      repeat step; try finisher.

  - unshelve epose proof (H31 theta ((p, uu) :: (y,v) :: lterms) _ _ _);
      repeat match goal with
             | |- reducible_values _ _ (T_equal _ _) => simp reducible_values
             | _ => tac0
             end.
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
    valid_interpretation theta ->
    (forall v,
        reducible_values theta v (topen 0 Ts (T_rec zero T0 Ts)) ->
        reducible_values theta v T0) ->
    reducible_values theta v (topen 0 Ts (intersect T0 Ts)) ->
    reducible_values theta (notype_tfold v) (intersect T0 Ts).
Proof.
  unfold intersect in *; repeat step.
  simp reducible_values; repeat step || (rewrite open_none in * by steps); try solve [ t_closing ].

  unshelve epose proof (strictly_positive_pull_forall _ _ _ _ _ X _ _ _ _ _ _ _ _ _ _ _ _ H9) as HH;
    repeat step; eauto using non_empty_nat;
      eauto with bwf.

  simp reducible_values in H12.
  t_invert_nat_value; repeat step || simp_red;
    try solve [ t_closing ];
    eauto with smallstep.
  - (* case a = 0, we use the decreasing property *)
    left; exists v; repeat step || apply_any.
    unshelve epose proof (HH zero _);
      repeat step || simp_red || rewrite open_none in * by steps.
  - (* case a = n+1 *)
    right; exists v0, v, (makeFresh (
                     support theta ::
                     pfv v0 type_var ::
                     pfv T0 type_var ::
                     pfv Ts type_var ::
                     (X :: nil) ::
                     nil));
    repeat step;
    try finisher.

    apply reducibility_subst_head2;
      repeat step || t_listutils;
      try finisher;
      eauto with bwf btwf.

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
    valid_interpretation theta ->
    (forall v,
        reducible_values theta v (topen 0 Ts (T_rec zero T0 Ts)) ->
        reducible_values theta v T0) ->
    reducible theta t (topen 0 Ts (intersect T0 Ts)) ->
    reducible theta (notype_tfold t) (intersect T0 Ts).
Proof.
  unfold reducible, reduces_to;
    repeat step.
  exists (notype_tfold t'); repeat step;
    try solve [ t_closing ];
    eauto using reducible_values_fold_gen;
    eauto with bsteplemmas.
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
    open_reducible tvars gamma t (topen 0 Ts (intersect T0 Ts)) ->
    open_reducible tvars gamma (notype_tfold t) (intersect T0 Ts).
Proof.
  unfold open_reducible; steps.
  apply reducible_fold_gen with X;
    repeat step || apply subst_erased_type || t_instantiate_sat4;
    eauto with bwf;
    eauto with btwf;
    eauto using pfv_in_subst with bfv;
    eauto with berased.

  - rewrite substitute_topen2;
      repeat step || apply strictly_positive_subst || apply is_erased_type_topen ||
      eauto with btwf;
      eauto with bfv.
  - rewrite substitute_topen in H12; eauto with btwf.
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
    base_type X (topen 0 Ts (fvar X type_var)) T0 ->
    open_reducible tvars gamma t (topen 0 Ts (intersect T0 Ts)) ->
    open_reducible tvars gamma (notype_tfold t) (intersect T0 Ts).
Proof.
  intros; apply open_reducible_fold_gen with X; steps.
  apply base_type_approx with X (topen 0 Ts (fvar X type_var))
    (fun v => reducible_values theta v (T_rec zero (psubstitute T0 l term_var) (psubstitute Ts l term_var)));
    eauto with bwf bfv;
    eauto using reducibility_is_candidate;
    eauto with berased.

  rewrite <- substitute_topen2; steps; eauto with btwf.
  apply reducibility_subst_head2;
    repeat step || t_listutils || apply reducibility_is_candidate ||
           rewrite fv_subst_different_tag in * by (steps; eauto with bfv);
    eauto with bfv bwf btwf berased;
    eauto using reducibility_is_candidate.
Qed.
