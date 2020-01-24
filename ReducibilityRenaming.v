Require Import Equations.Equations.
Require Import Equations.Prop.Subterm.

Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import PeanoNat.
Require Import Omega.

Require Export SystemFR.IdRelation.
Require Export SystemFR.RedTactics.

Open Scope list_scope.

Opaque reducible_values.
Opaque makeFresh.
Opaque lt.

Definition renamable_prop T: Prop :=
  forall T' t theta theta' rel,
    equivalent_with_relation rel theta theta' equivalent_rc ->
    equal_with_relation type_var rel T T' ->
      reducible_values theta t T <->
      reducible_values theta' t T'.

Lemma reducible_rename_induct:
  forall theta theta' rel A A' v,
    renamable_prop A ->
    equal_with_relation type_var rel A A' ->
    equivalent_with_relation rel theta theta' equivalent_rc ->
    reducible_values theta v A ->
    reducible_values theta' v A'.
Proof.
  unfold renamable_prop; repeat step || eapply_any.
Qed.

Lemma reducible_rename_induct_back:
  forall theta theta' rel A A' v,
    renamable_prop A ->
    equal_with_relation type_var rel A A' ->
    equivalent_with_relation rel theta theta' equivalent_rc ->
    reducible_values theta' v A' ->
    reducible_values theta v A.
Proof.
  unfold renamable_prop; repeat step || eapply_any.
Qed.

Lemma reducible_rename_induct_open:
  forall theta theta' rel B B' v a,
    renamable_prop (open 0 B a) ->
    equal_with_relation type_var rel B B' ->
    equivalent_with_relation rel theta theta' equivalent_rc ->
    reducible_values theta v (open 0 B a) ->
    is_erased_term a ->
    reducible_values theta' v (open 0 B' a).
Proof.
  unfold renamable_prop; repeat step || eapply_any || apply equal_with_relation_open2 || apply equal_with_relation_refl;
    eauto with fv.
Qed.

Lemma reducible_rename_induct_open_back:
  forall theta theta' rel B B' v a,
    renamable_prop (open 0 B a) ->
    equal_with_relation type_var rel B B' ->
    equivalent_with_relation rel theta theta' equivalent_rc ->
    reducible_values theta' v (open 0 B' a) ->
    is_erased_term a ->
    reducible_values theta v (open 0 B a).
Proof.
  unfold renamable_prop; repeat step || eapply_any || apply equal_with_relation_open2 || apply equal_with_relation_refl;
    eauto with fv.
Qed.

Ltac t_induct :=
  solve [ eapply reducible_rename_induct; eauto 1; eauto 1 with prop_until ].

Ltac t_induct_back :=
  solve [ eapply reducible_rename_induct_back; eauto 1; eauto 1 with prop_until ].

Ltac t_induct_open :=
  solve [
    eapply reducible_rename_induct_open; eauto 1; eauto 1 with prop_until; t_closer
  ].

Ltac t_induct_open_back :=
  solve [
    eapply reducible_rename_induct_open_back; eauto 1; eauto 1 with prop_until; t_closer
  ].

Ltac t_induct_all := t_induct || t_induct_back || t_induct_open || t_induct_open_back.

Ltac t_prove_reduces_to :=
  match goal with
  | H: forall a, _ -> _ -> _ -> _ -> reduces_to _ _ |- _ => apply H; eauto; [ idtac ]
  | H: forall a, _ -> _ -> _ -> _ -> reduces_to _ _ |- _ => apply H; eauto; fail
  end.

Lemma reducible_rename_reduces_to:
  forall T1 T2 t theta theta' rel A' B' a,
    equivalent_with_relation rel theta theta' equivalent_rc ->
    prop_until renamable_prop (S (type_nodes T1 + type_nodes T2), notype_err) ->
    is_erased_term a ->
    wf a 0 ->
    pfv a term_var = nil ->
    reducible_values theta' a A' ->
    is_erased_type T2 ->
    is_erased_type B' ->
    (forall a,
        is_erased_term a ->
        wf a 0 ->
        pfv a term_var = nil ->
        reducible_values theta a T1 ->
        reduces_to (fun t0 : tree => reducible_values theta t0 (open 0 T2 a)) (app t a)) ->
    equal_with_relation type_var rel T1 A' ->
    equal_with_relation type_var rel T2 B' ->
    reduces_to (fun t0 : tree => reducible_values theta' t0 (open 0 B' a)) (app t a).
Proof.
  repeat step || t_reduces_to || t_reduces_to2 || t_prove_reduces_to || t_induct_all.
Qed.

Lemma reducible_rename_reduces_to_back:
  forall T1 T2 t theta theta' rel A' B' a,
    equivalent_with_relation rel theta theta' equivalent_rc ->
    prop_until renamable_prop (S (type_nodes T1 + type_nodes T2), notype_err) ->
    is_erased_term a ->
    wf a 0 ->
    pfv a term_var = nil ->
    reducible_values theta a T1 ->
    is_erased_type T2 ->
    is_erased_type B' ->
    (forall a,
        is_erased_term a ->
        wf a 0 ->
        pfv a term_var = nil ->
        reducible_values theta' a A' ->
        reduces_to (fun t0 : tree => reducible_values theta' t0 (open 0 B' a)) (app t a)) ->
    equal_with_relation type_var rel T1 A' ->
    equal_with_relation type_var rel T2 B' ->
    reduces_to (fun t0 : tree => reducible_values theta t0 (open 0 T2 a)) (app t a).
Proof.
  repeat step || t_reduces_to || t_reduces_to2 || t_prove_reduces_to || t_induct_all.
Qed.

Lemma reducible_rename_fvar: forall m n f, prop_at renamable_prop m (fvar n f).
Proof.
  unfold prop_at, renamable_prop; intros.
  force_invert equal_with_relation;
      repeat step || destruct_tag || simp_red || t_lookup || t_lookup_same || t_instantiate_rel;
      try solve [ eapply equivalent_rc_left; eauto 1 ];
      try solve [ eapply equivalent_rc_right; eauto 1 ].
Qed.

Hint Immediate reducible_rename_fvar: b_rename.

Lemma reducible_rename_arrow: forall m T1 T2, prop_until renamable_prop m -> prop_at renamable_prop m (T_arrow T1 T2).
Proof.
  unfold prop_at, get_measure; intros; unfold renamable_prop;
  repeat step || simp_red || step_inversion equal_with_relation;
    eauto 2 using reducible_rename_reduces_to;
    eauto 2 using reducible_rename_reduces_to_back;
    eauto 2 with erased.
Qed.

Hint Immediate reducible_rename_arrow: b_rename.

Lemma reducible_rename_prod: forall m T1 T2, prop_until renamable_prop m -> prop_at renamable_prop m (T_prod T1 T2).
Proof.
  unfold prop_at, get_measure; intros; unfold renamable_prop;
  repeat step || simp_red || step_inversion equal_with_relation || find_exists || t_induct_all;
  eauto with erased.
Qed.

Hint Immediate reducible_rename_prod: b_rename.

Lemma reducible_rename_sum:
  forall m T1 T2,
    prop_until renamable_prop m ->
    prop_at renamable_prop m (T_sum T1 T2).
Proof.
  unfold prop_at; intros; unfold renamable_prop;
  repeat step || simp_red || step_inversion equal_with_relation || find_exists || t_induct_all.
Qed.

Hint Immediate reducible_rename_sum: b_rename.

Lemma reducible_rename_refine: forall m T b, prop_until renamable_prop m -> prop_at renamable_prop m (T_refine T b).
Proof.
  unfold prop_at; intros; unfold renamable_prop;
  repeat step || simp_red || step_inversion equal_with_relation || t_induct_all || equal_with_erased.
Qed.

Hint Immediate reducible_rename_refine: b_rename.

Lemma reducible_rename_type_refine:
  forall m T1 T2, prop_until renamable_prop m -> prop_at renamable_prop m (T_type_refine T1 T2).
Proof.
  unfold prop_at; intros; unfold renamable_prop;
  repeat step || simp_red || step_inversion equal_with_relation || t_induct_all || find_exists_open;
  eauto 2 with erased.
Qed.

Hint Immediate reducible_rename_type_refine: b_rename.

Lemma reducible_rename_intersection: forall m T1 T2, prop_until renamable_prop m -> prop_at renamable_prop m (T_intersection T1 T2).
Proof.
  unfold prop_at; intros; unfold renamable_prop;
  repeat step || simp_red || step_inversion equal_with_relation || t_induct_all.
Qed.

Hint Immediate reducible_rename_intersection: b_rename.

Lemma reducible_rename_union: forall m T1 T2, prop_until renamable_prop m -> prop_at renamable_prop m (T_union T1 T2).
Proof.
  unfold prop_at; intros; unfold renamable_prop;
  repeat match goal with
         | H1: equal_with_relation _ _ ?T ?T',
           H: reducible_values _ ?t ?T |- reducible_values _ ?t ?T' \/ _ => left
         | H1: equal_with_relation _ _ ?T' ?T,
           H: reducible_values _ ?t ?T |- reducible_values _ ?t ?T' \/ _ => left
         | H1: equal_with_relation _ _ ?T ?T',
           H: reducible_values _ ?t ?T |- _ \/ reducible_values _ ?t ?T' => right
         | H1: equal_with_relation _ _ ?T' ?T,
           H: reducible_values _ ?t ?T |- _ \/ reducible_values _ ?t ?T' => right
         | _ => step || simp_red || step_inversion equal_with_relation || t_induct_all || find_exists
         end.
Qed.

Hint Immediate reducible_rename_union: b_rename.

Lemma reducible_rename_equal: forall m t1 t2, prop_until renamable_prop m -> prop_at renamable_prop m (T_equiv t1 t2).
Proof.
  unfold prop_at; intros; unfold renamable_prop;
  repeat step || simp_red || step_inversion equal_with_relation || t_induct_all ||
         unfold equivalent_terms in * || equal_with_erased;
  eauto with apply_any.
Qed.

Hint Immediate reducible_rename_equal: b_rename.

Lemma reducible_rename_forall: forall m T1 T2, prop_until renamable_prop m -> prop_at renamable_prop m (T_forall T1 T2).
Proof.
  unfold prop_at; intros; unfold renamable_prop;
  repeat step || simp_red || step_inversion equal_with_relation ||
         t_induct_all || t_instantiate_reducible_erased;
  eauto 2 with erased;
  eauto 2 with wf.
Qed.

Hint Immediate reducible_rename_forall: b_rename.

Lemma reducible_rename_exists: forall m T1 T2, prop_until renamable_prop m -> prop_at renamable_prop m (T_exists T1 T2).
Proof.
  unfold prop_at; intros; unfold renamable_prop;
  repeat match goal with
         | H1: equal_with_relation _ _ ?T ?T',
           H: reducible_values _ ?t ?T |- exists _ _, _ /\ _ /\ reducible_values _ _ ?T' /\ _ => exists t
         | H1: equal_with_relation _ _ ?T' ?T,
           H: reducible_values _ ?t ?T |- exists _ _, _ /\ _ /\ reducible_values _ _ ?T' /\ _ => exists t
         | _ => step || simp_red || step_inversion equal_with_relation || t_induct_all
         end;
  eauto 2 with erased.
Qed.

Hint Immediate reducible_rename_exists: b_rename.

Lemma reducible_rename_type_abs: forall m T, prop_until renamable_prop m -> prop_at renamable_prop m (T_abs T).
Proof.
  unfold prop_at; intros; unfold renamable_prop;
  repeat match goal with
         | H1: equal_with_relation _ ?rel ?T ?T' |- exists X, (X ∈ ?L -> False) /\ _ =>
             exists (makeFresh (L :: (range rel) :: (range (swap rel)) :: (pfv T type_var) :: (pfv T' type_var) :: nil))
         | _ => step || simp_red || step_inversion equal_with_relation
         end; try finisher.

  - instantiate_any.
    eapply reducible_rename_induct; try eassumption;
      repeat step || apply equivalent_with_relation_topen ||
             apply equivalent_with_relation_add || apply equal_with_relation_topen;
      eauto 1 with prop_until;
      eauto 2 using equivalent_rc_refl;
      try finisher.

  - instantiate_any.
    eapply reducible_rename_induct_back; try eassumption;
      repeat step || apply equivalent_with_relation_topen ||
             apply equivalent_with_relation_add || apply equal_with_relation_topen;
      eauto 1 with prop_until;
      eauto 2 using equivalent_rc_refl;
      try finisher.
Qed.

Hint Immediate reducible_rename_type_abs: b_rename.

Lemma reducible_rename_rec: forall m n T0 Ts, prop_until renamable_prop m -> prop_at renamable_prop m (T_rec n T0 Ts).
Proof.
  unfold prop_at; intros; unfold renamable_prop;
  repeat match goal with
         | H: star scbv_step _ zero |- _ \/ _ => left
         | H: star scbv_step _ (succ _) |- _ => right
         | _ => step || simp_red || step_inversion equal_with_relation ||
               equal_with_erased || find_exists || t_induct_all
         end.

  - unshelve eexists n', (makeFresh (pfv T0' type_var :: pfv Ts' type_var ::  support theta' :: nil)), _, _; eauto;
      repeat step || finisher.
    eapply reducible_rename_induct; try eassumption;
      repeat step || unfold equivalent_rc ||
             apply equivalent_with_relation_topen ||
             apply equivalent_with_relation_add ||
             apply equal_with_relation_topen;
      eauto 1 with prop_until;
      try finisher.

    + eapply reducible_rename_induct; try eassumption;
        repeat step; eauto with prop_until;
          eauto using equal_with_relation_refl with fv equal_with_relation.

    + eapply reducible_rename_induct_back; try eassumption;
        repeat step; eauto with prop_until;
          eauto using equal_with_relation_refl with fv equal_with_relation.

  - (* case recursive type at n + 1 *)
   unshelve eexists n'0, (makeFresh (pfv T0 type_var :: pfv Ts type_var :: support theta :: nil)), _, _; eauto;
      repeat step || finisher.

   eapply reducible_rename_induct_back; try eassumption;
     repeat step || unfold equivalent_rc ||
            apply equivalent_with_relation_topen ||
            apply equivalent_with_relation_add ||
            apply equal_with_relation_topen;
     eauto 1 with prop_until;
     try finisher.

   + eapply reducible_rename_induct; try eassumption;
       repeat step; eauto with prop_until;
         eauto using equal_with_relation_refl with fv equal_with_relation.

   + eapply reducible_rename_induct_back; try eassumption;
       repeat step; eauto with prop_until;
         eauto using equal_with_relation_refl with fv equal_with_relation.
Qed.

Hint Immediate reducible_rename_rec: b_rename.

Lemma reducible_rename_aux: forall (m: measure_domain) T, prop_at renamable_prop m T.
Proof.
  induction m using measure_induction; destruct T;
    eauto 2 with b_rename;
    try solve [ unfold prop_at; intros; unfold renamable_prop; repeat step || simp_red || step_inversion equal_with_relation ].
Qed.

Lemma reducible_rename :
  forall T T' t theta theta' rel,
    reducible_values theta t T ->
    equivalent_with_relation rel theta theta' equivalent_rc ->
    equal_with_relation type_var rel T T' ->
    reducible_values theta' t T'     .
Proof.
  intros; eapply (reducible_rename_aux _ T eq_refl T' t theta theta' rel); eauto 1.
Qed.

Lemma reducible_rename_one:
  forall RC theta v T X Y,
    reducible_values ((X,RC) :: theta) v (topen 0 T (fvar X type_var)) ->
    (X ∈ pfv T type_var -> False) ->
    (Y ∈ pfv T type_var -> False) ->
    reducible_values ((Y,RC) :: theta) v (topen 0 T (fvar Y type_var)).
Proof.
  intros.
  eapply (reducible_rename _ _ _ _ _ ((X,Y) :: idrel (pfv T type_var))); eauto;
    repeat step || t_idrel || t_lookup ||
           apply equivalent_with_relation_add ||
           apply equal_with_relation_topen ||
           apply equal_with_idrel ||
           unfold equivalent_with_relation;
           eauto using equivalent_at_refl, equivalent_rc_refl.
Qed.

Ltac reducible_rename_one :=
  match goal with
  | H: reducible_values ((?X,?RC) :: ?theta) ?v (topen 0 ?T (fvar ?X type_var)) |-
       reducible_values ((?Y,?RC) :: ?theta) ?v (topen 0 ?T (fvar ?Y type_var)) =>
    apply reducible_rename_one with X
  end.

Lemma reducible_rename_one_rc:
  forall RC RC' theta v T X Y,
    reducible_values ((X,RC) :: theta) v (topen 0 T (fvar X type_var)) ->
    equivalent_rc RC RC' ->
    (X ∈ pfv T type_var -> False) ->
    (Y ∈ pfv T type_var -> False) ->
    reducible_values ((Y,RC') :: theta) v (topen 0 T (fvar Y type_var)).
Proof.
  intros.
  eapply (reducible_rename _ _ _ _ _ ((X,Y) :: idrel (pfv T type_var))); eauto;
    repeat step || t_idrel || t_lookup ||
           apply equivalent_with_relation_add ||
           apply equal_with_relation_topen ||
           apply equal_with_idrel ||
           unfold equivalent_with_relation;
           eauto using equivalent_rc_refl, equivalent_at_refl.
Qed.

Lemma reducible_rename_rc:
  forall RC RC' theta v T X,
    reducible_values ((X, RC) :: theta) v (topen 0 T (fvar X type_var)) ->
    equivalent_rc RC RC' ->
    (X ∈ pfv T type_var -> False) ->
    reducible_values ((X, RC') :: theta) v (topen 0 T (fvar X type_var)).
Proof.
  eauto using reducible_rename_one_rc.
Qed.

Lemma reducible_rename_permute:
  forall T theta1 theta2 X Y (RC : tree -> Prop) v,
    ~(Y ∈ support theta1) ->
    ~(X ∈ pfv T type_var) ->
    ~(Y ∈ pfv T type_var) ->
    reducible_values ((X, RC) :: theta1 ++ theta2) v (topen 0 T (fvar X type_var)) ->
    reducible_values (theta1 ++ (Y, RC) :: theta2) v (topen 0 T (fvar Y type_var)).
Proof.
  intros.
  eapply (reducible_rename _ _ _ _ _ ((X,Y) :: idrel (pfv T type_var))); eauto;
    repeat step || apply valid_interpretation_append || apply equal_with_relation_topen;
    eauto using equal_with_idrel.

  apply equivalent_with_relation_permute2; steps; eauto using equivalent_rc_refl.
Qed.
