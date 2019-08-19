Require Import Equations.Equations.
Require Import Equations.Prop.Subterm.

Require Import Coq.Strings.String.
Require Import Coq.Lists.List.

Require Import SystemFR.Syntax.
Require Import SystemFR.Tactics.
Require Import SystemFR.Sets.
Require Import SystemFR.TermList.
Require Import SystemFR.AssocList.
Require Import SystemFR.SizeLemmas.
Require Import SystemFR.ListUtils.
Require Import SystemFR.SmallStep.
Require Import SystemFR.StarRelation.
Require Import SystemFR.SubstitutionLemmas.
Require Import SystemFR.Freshness.
Require Import SystemFR.Equivalence.
Require Import SystemFR.IdRelation.
Require Import SystemFR.SetLemmas.
Require Import SystemFR.EqualWithRelation.
Require Import SystemFR.EquivalentWithRelation.
Require Import SystemFR.ErasedTermLemmas.
Require Import SystemFR.TermProperties.

Require Import SystemFR.FVLemmas.
Require Import SystemFR.FVLemmasLists.

Require Import SystemFR.ReducibilityCandidate.
Require Import SystemFR.ReducibilityDefinition.
Require Import SystemFR.ReducibilityLemmas.
Require Import SystemFR.ReducibilityMeasure.

Require Import SystemFR.RedTactics.

Require Import PeanoNat.

Require Import Omega.

Open Scope list_scope.

Opaque reducible_values.
Opaque makeFresh.
Opaque lt.

Ltac t_bewr_constructor :=
  match goal with
  | |- equal_with_relation _ _ _ => constructor
  end.

(* The property that we wnat to prove for a type T and a measure m *)
Definition renamable_prop (m: measure_domain) T: Prop :=
  forall (T' t : tree) (theta theta' : interpretation) (rel : map nat nat),
    get_measure T = m ->
    valid_interpretation theta ->
    valid_interpretation theta' ->
    equivalent_with_relation rel theta theta' equivalent_rc ->
    equal_with_relation rel T T' ->
      (reducible_values theta t T <-> reducible_values theta' t T').

Definition renamable_prop_IH m: Prop := forall m', m' << m -> forall T', renamable_prop m' T'.

Lemma reducible_rename_induct:
  forall (theta theta' : interpretation) (rel : map nat nat) A A' v n0 n1 n2,
    renamable_prop_IH (n0, (n1, n2)) ->
    equal_with_relation rel A A' ->
    equivalent_with_relation rel theta theta' equivalent_rc ->
    reducible_values theta v A ->
    valid_interpretation theta ->
    valid_interpretation theta' ->
    count_interpret A <= n0 ->
    typeNodes A < n1 ->
    reducible_values theta' v A'.
Proof.
  unfold renamable_prop_IH; intros.
  match goal with
  | IH: forall m, _ << _ -> _ ,
    H1: reducible_values ?theta ?t ?T,
    H2: equal_with_relation ?rel ?T ?T' |-
      reducible_values ?theta' ?t ?T' =>
        unshelve eapply (IH (get_measure T) _ T T' t theta theta' rel); eauto
  end.
  repeat step || unfold get_measure;
    try solve [ apply leq_lt_measure; steps ].
Qed.

Lemma reducible_rename_induct_back:
  forall (theta theta' : interpretation) (rel : map nat nat) A A' v n0 n1 n2,
    renamable_prop_IH (n0, (n1, n2)) ->
    equal_with_relation rel A A' ->
    equivalent_with_relation rel theta theta' equivalent_rc ->
    reducible_values theta' v A' ->
    valid_interpretation theta ->
    valid_interpretation theta' ->
    typeNodes A < n1 ->
    count_interpret A <= n0 ->
    reducible_values theta v A.
Proof.
  unfold renamable_prop_IH; intros.
  match goal with
  | IH: forall m, _ << _ -> _ ,
    H1: reducible_values ?theta' ?t ?T',
    H2: equal_with_relation ?rel ?T ?T' |-
      reducible_values ?theta ?t ?T =>
        unshelve eapply (IH (get_measure T) _ T T' t theta theta' rel); eauto
  end.
  repeat step || unfold get_measure;
    try solve [ apply leq_lt_measure; steps ].
Qed.

Ltac t_apply_ih :=
  lazymatch goal with
  | IH: forall m, _ << _ -> _ ,
    H1: reducible_values ?theta' ?t ?T',
    H2: equivalent_with_relation ?rel ?theta ?theta' _ |-
      reducible_values ?theta ?t ?T =>
        unshelve eapply (IH (get_measure T) _ T T' t theta theta' rel); eauto
  | IH: forall m, _ << _ -> _ ,
    H1: reducible_values ?theta ?t ?T,
    H2: equivalent_with_relation ?rel ?theta ?theta' _ |-
      reducible_values ?theta' ?t ?T' =>
        unshelve eapply (IH (get_measure T) _ T T' t theta theta' rel); eauto
  end.

Lemma reducible_rename_induct_open:
  forall (theta theta' : interpretation) (rel : map nat nat) B B' v a n0 n1 n2,
    renamable_prop_IH (n0, (n1, n2)) ->
    equal_with_relation rel B B' ->
    equivalent_with_relation rel theta theta' equivalent_rc ->
    reducible_values theta v (open 0 B a) ->
    valid_interpretation theta ->
    valid_interpretation theta' ->
    is_erased_term a ->
    typeNodes (open 0 B a) < n1 ->
    count_interpret (open 0 B a) <= n0 ->
    reducible_values theta' v (open 0 B' a).
Proof.
  unfold renamable_prop_IH; intros.
  t_apply_ih;
    repeat step || apply leq_lt_measure || apply equal_with_relation_open; eauto with bfv.
Qed.

Lemma reducible_rename_induct_open_back:
  forall (theta theta' : interpretation) (rel : map nat nat) B B' v a n0 n1 n2,
    renamable_prop_IH (n0, (n1, n2)) ->
    equal_with_relation rel B B' ->
    equivalent_with_relation rel theta theta' equivalent_rc ->
    reducible_values theta' v (open 0 B' a) ->
    valid_interpretation theta ->
    valid_interpretation theta' ->
    is_erased_term a ->
    typeNodes (open 0 B a) < n1 ->
    count_interpret (open 0 B a) <= n0 ->
    reducible_values theta v (open 0 B a).
Proof.
  unfold renamable_prop_IH; intros.
  t_apply_ih; repeat step || apply leq_lt_measure || apply equal_with_relation_open; eauto with bfv.
Qed.

Ltac t_induct :=
  solve [ eapply reducible_rename_induct; eauto 1; steps; try omega ].

Ltac t_induct_back :=
  solve [ eapply reducible_rename_induct_back; eauto 1; steps; try omega ].

Ltac t_induct_open :=
  solve [ eapply reducible_rename_induct_open; eauto 1; repeat step || autorewrite with bsize; try omega; eauto 2 with berased ].

Ltac t_induct_open_back :=
  solve [ eapply reducible_rename_induct_open_back; eauto 1; repeat step || autorewrite with bsize; try omega; eauto 2 with berased ].

Ltac t_induct_all := t_induct || t_induct_back || t_induct_open || t_induct_open_back.

Ltac t_prove_reduces_to :=
  match goal with
  | H: forall a, _ -> _ -> reduces_to _ _ |- _ => apply H; eauto 2 with berased; [ idtac ]
  | H: forall a, _ -> _ -> reduces_to _ _ |- _ => apply H; eauto 2 with berased; fail
  end.

Lemma reducible_rename_reduces_to:
  forall (T1 T2 t : tree) (theta theta' : interpretation) (rel : map nat nat) A' B' a,
    equivalent_with_relation rel theta theta' equivalent_rc ->
    renamable_prop_IH (count_interpret T1 + count_interpret T2, (S (typeNodes T1 + typeNodes T2), notype_err)) ->
    reducible_values theta' a A' ->
    is_erased_type T2 ->
    is_erased_type B' ->
    valid_interpretation theta ->
    valid_interpretation theta' ->
    (forall a : tree,
        is_erased_term a ->
        reducible_values theta a T1 ->
        reduces_to (fun t0 : tree => reducible_values theta t0 (open 0 T2 a)) (app t a)) ->
    equal_with_relation rel T1 A' ->
    equal_with_relation rel T2 B' ->
    reduces_to (fun t0 : tree => reducible_values theta' t0 (open 0 B' a)) (app t a).
Proof.
  repeat step || t_reduces_to || t_reduces_to2 || t_prove_reduces_to || t_induct_all.
Qed.

Lemma reducible_rename_reduces_to_back:
  forall (T1 T2 t : tree) (theta theta' : interpretation) (rel : map nat nat) A' B' a,
    equivalent_with_relation rel theta theta' equivalent_rc ->
    renamable_prop_IH (count_interpret T1 + count_interpret T2, (S (typeNodes T1 + typeNodes T2), notype_err)) ->
    reducible_values theta a T1 ->
    is_erased_type T2 ->
    is_erased_type B' ->
    valid_interpretation theta ->
    valid_interpretation theta' ->
    (forall a : tree,
        is_erased_term a ->
        reducible_values theta' a A' ->
        reduces_to (fun t0 : tree => reducible_values theta' t0 (open 0 B' a)) (app t a)) ->
    equal_with_relation rel T1 A' ->
    equal_with_relation rel T2 B' ->
    reduces_to (fun t0 : tree => reducible_values theta t0 (open 0 T2 a)) (app t a).
Proof.
  repeat step || t_reduces_to || t_reduces_to2 || t_prove_reduces_to || t_induct_all.
Qed.

Lemma reducible_rename_fvar: forall m n f, renamable_prop m (fvar n f).
Proof.
  unfold renamable_prop;
  repeat step || destruct_tag || step_inversion equal_with_relation || simp_red || t_lookup || t_lookup_same || t_instantiate_rel;
    try solve [ eapply equivalent_rc_left; eauto 1 ];
    try solve [ eapply equivalent_rc_right; eauto 1 ].
Qed.

Hint Immediate reducible_rename_fvar: b_rename.

Lemma reducible_rename_arrow: forall m T1 T2, renamable_prop_IH m -> renamable_prop m (T_arrow T1 T2).
Proof.
  unfold renamable_prop, get_measure;
  repeat step || simp_red || step_inversion equal_with_relation;
    eauto 2 using reducible_rename_reduces_to;
    eauto 2 using reducible_rename_reduces_to_back;
    eauto 2 with berased.
Qed.

Hint Immediate reducible_rename_arrow: b_rename.

Lemma reducible_rename_prod: forall m T1 T2, renamable_prop_IH m -> renamable_prop m (T_prod T1 T2).
Proof.
  unfold renamable_prop, get_measure;
  repeat step || simp_red || step_inversion equal_with_relation || find_exists || t_induct_all;
  eauto 2 with berased.
Qed.

Hint Immediate reducible_rename_prod: b_rename.

Lemma reducible_rename_sum: forall m T1 T2, renamable_prop_IH m -> renamable_prop m (T_sum T1 T2).
Proof.
  unfold renamable_prop;
  repeat step || simp_red || step_inversion equal_with_relation || find_exists || t_induct_all.
Qed.

Hint Immediate reducible_rename_sum: b_rename.

Lemma reducible_rename_refine: forall m T b, renamable_prop_IH m -> renamable_prop m (T_refine T b).
Proof.
  unfold renamable_prop;
  repeat step || simp_red || step_inversion equal_with_relation || t_induct_all || t_equal_with_erased.
Qed.

Hint Immediate reducible_rename_refine: b_rename.

Lemma reducible_rename_type_refine: forall m T1 T2, renamable_prop_IH m -> renamable_prop m (T_type_refine T1 T2).
Proof.
  unfold renamable_prop;
  repeat step || simp_red || step_inversion equal_with_relation || t_induct_all || find_exists_open;
  eauto 2 with berased.
Qed.

Hint Immediate reducible_rename_type_refine: b_rename.

Lemma reducible_rename_let: forall m t T, renamable_prop_IH m -> renamable_prop m (T_let t T).
Proof.
  unfold renamable_prop;
  repeat step || simp_red || step_inversion equal_with_relation || t_induct_all || find_smallstep_value2 || t_equal_with_erased;
  eauto 2 with berased.
Qed.

Hint Immediate reducible_rename_let: b_rename.

Lemma reducible_rename_singleton: forall m t, renamable_prop_IH m -> renamable_prop m (T_singleton t).
Proof.
  unfold renamable_prop;
  repeat step || simp_red || step_inversion equal_with_relation || t_induct_all || t_equal_with_erased.
Qed.

Hint Immediate reducible_rename_singleton: b_rename.

Lemma reducible_rename_intersection: forall m T1 T2, renamable_prop_IH m -> renamable_prop m (T_intersection T1 T2).
Proof.
  unfold renamable_prop;
  repeat step || simp_red || step_inversion equal_with_relation || t_induct_all.
Qed.

Hint Immediate reducible_rename_intersection: b_rename.

Lemma reducible_rename_union: forall m T1 T2, renamable_prop_IH m -> renamable_prop m (T_union T1 T2).
Proof.
  unfold renamable_prop;
  repeat match goal with
         | H1: equal_with_relation _ ?T ?T',
           H: reducible_values _ ?t ?T |- reducible_values _ ?t ?T' \/ _ => left
         | H1: equal_with_relation _ ?T' ?T,
           H: reducible_values _ ?t ?T |- reducible_values _ ?t ?T' \/ _ => left
         | H1: equal_with_relation _ ?T ?T',
           H: reducible_values _ ?t ?T |- _ \/ reducible_values _ ?t ?T' => right
         | H1: equal_with_relation _ ?T' ?T,
           H: reducible_values _ ?t ?T |- _ \/ reducible_values _ ?t ?T' => right
         | _ => step || simp_red || step_inversion equal_with_relation || t_induct_all || find_exists
         end.
Qed.

Hint Immediate reducible_rename_union: b_rename.

Lemma reducible_rename_equal: forall m t1 t2, renamable_prop_IH m -> renamable_prop m (T_equal t1 t2).
Proof.
  unfold renamable_prop;
  repeat step || simp_red || step_inversion equal_with_relation || t_induct_all || t_equal_with_erased.
Qed.

Hint Immediate reducible_rename_equal: b_rename.

Lemma reducible_rename_forall: forall m T1 T2, renamable_prop_IH m -> renamable_prop m (T_forall T1 T2).
Proof.
  unfold renamable_prop;
  repeat step || simp_red || step_inversion equal_with_relation || t_induct_all || t_instantiate_reducible_erased;
  eauto 2 with berased.
Qed.

Hint Immediate reducible_rename_forall: b_rename.

Lemma reducible_rename_exists: forall m T1 T2, renamable_prop_IH m -> renamable_prop m (T_exists T1 T2).
Proof.
  unfold renamable_prop;
  repeat match goal with
         | H1: equal_with_relation _ ?T ?T',
           H: reducible_values _ ?t ?T |- exists _ _, reducible_values _ _ ?T' /\ _ => exists t
         | H1: equal_with_relation _ ?T' ?T,
           H: reducible_values _ ?t ?T |- exists _ _, reducible_values _ _ ?T' /\ _ => exists t
         | _ => step || simp_red || step_inversion equal_with_relation || t_induct_all
         end;
  eauto 2 with berased.
Qed.

Hint Immediate reducible_rename_exists: b_rename.

Lemma reducible_rename_type_abs: forall m T, renamable_prop_IH m -> renamable_prop m (T_abs T).
Proof.
  unfold renamable_prop, renamable_prop_IH;
  repeat match goal with
         | H1: equal_with_relation ?rel ?T ?T' |- exists X, (X ∈ ?L -> False) /\ _ =>
             exists (makeFresh (L :: (range rel) :: (range (swap rel)) :: (pfv T type_var) :: (pfv T' type_var) :: nil))
         | _ => step || simp_red || step_inversion equal_with_relation
         end; try finisher.

  - instantiate_any.
    lazymatch goal with
    | IH: forall m, _ << _ ->  _ ,
      H1: reducible_values ((?X,?RC) :: ?theta) ?t ?T,
      H2: equal_with_relation ?rel _ _ |-
        reducible_values ((?M,?RC) :: ?theta') ?t ?T' =>
          unshelve epose proof
            (IH (get_measure T) _ T T' t
                 ((X,RC) :: theta)
                 ((M,RC) :: theta')
                 ((X,M) :: rel)
                 _ _ _ _ _
            )
    end;
      repeat
        steps || (progress autorewrite with bsize in * ) || t_fv_open || t_listutils ||
        unfold get_measure ||
        apply equivalent_with_relation_add || finisher ||
        apply equal_with_relation_topen ||
        apply right_lex, left_lex ||
        (rewrite substitute_topen3 in * by steps);
      try omega;
      eauto using in_remove_support;
      eauto using equivalent_rc_refl.

  - instantiate_any.
    lazymatch goal with
    | IH: forall m, _ << _ ->  _ ,
      H1: reducible_values ((?X,?RC) :: ?theta) ?t ?T,
      H2: equal_with_relation ?rel _ _ |-
        reducible_values ((?M,?RC) :: ?theta') ?t ?T' =>
          unshelve epose proof
            (IH (get_measure T) _ T T' t
                 ((X,RC) :: theta)
                 ((M,RC) :: theta')
                 ((X,M) :: (swap rel))
                 _ _ _ _ _
            )
    end;
      repeat
        steps || (progress autorewrite with bsize in * ) || t_fv_open || t_listutils ||
        unfold get_measure ||
        apply equivalent_with_relation_add || finisher ||
        apply equal_with_relation_topen ||
        apply equivalent_with_relation_swap ||
        apply equal_with_relation_swap ||
        apply leq_lt_measure ||
        match goal with
        | H: equal_with_relation _ _ _ |- _ =>
          try (rewrite (equal_with_relation_count_interpret _ _ _ H) in * by steps);
          try (rewrite (equal_with_relation_size _ _ _ H) in * by steps)
        end ||
        (rewrite substitute_topen3 in * by steps);
      try omega;
      eauto using in_remove_support;
      eauto using equivalent_rc_refl;
      eauto 2 using equivalent_rc_sym.
Qed.

Hint Immediate reducible_rename_type_abs: b_rename.

Lemma reducible_rename_rec: forall m n T0 Ts, renamable_prop_IH m -> renamable_prop m (T_rec n T0 Ts).
Proof.
  unfold renamable_prop, renamable_prop_IH;
  repeat match goal with
         | H: star small_step _ zero |- _ \/ _ => left
         | H: star small_step _ (succ _) |- _ => right
         | _ => step || simp_red || step_inversion equal_with_relation || t_equal_with_erased || find_exists || t_induct_all
         end.

  - (* case recursive type at n + 1 *)
    unshelve eexists n', (makeFresh (pfv T0' type_var :: pfv Ts' type_var ::  support theta' :: nil)), _, _; eauto;
      repeat step || finisher.
    lazymatch goal with
    | IH: forall m, _ << _ -> _ ,
      H1: reducible_values ((?X,?RC1) :: ?theta) ?t ?T,
      H2: equal_with_relation ?rel _ _ |-
        reducible_values ((?M,?RC2) :: ?theta') ?t ?T' =>
          unshelve epose proof
            (IH (get_measure T) _ T T' t
                 ((X,RC1) :: theta)
                 ((M,RC2) :: theta')
                 ((X,M) :: rel)
                 _ _ _ _ _
            )
    end;
      repeat
        unfold get_measure ||
        steps || (progress autorewrite with bsize in * ) || t_fv_open || t_listutils ||
        apply equivalent_with_relation_add || finisher ||
        apply equal_with_relation_topen ||
        unfold equivalent_rc ||
        apply equal_with_relation_refl ||
        (rewrite substitute_topen3 in * by steps) ||
        t_apply_ih || t_bewr_constructor;
      try solve [ apply leq_lt_measure; omega ];
      try solve [ apply right_lex, right_lex, lt_index_step; auto ];
      eauto using in_remove_support;
      eauto using reducibility_is_candidate;
      eauto with bfv.

  - (* case recursive type at n + 1 *)
   unshelve eexists n'0, (makeFresh (pfv T0 type_var :: pfv Ts type_var :: support theta :: nil)), _, _; eauto;
      repeat step || finisher.
    lazymatch goal with
    | IH: forall m, _ << _ ->  _ ,
      H1: reducible_values ((?X,?RC1) :: ?theta) ?t ?T,
      H2: equal_with_relation ?rel _ _ |-
        reducible_values ((?M,?RC2) :: ?theta') ?t ?T' =>
          unshelve epose proof
            (IH (get_measure T) _ T T' t
                 ((X,RC1) :: theta)
                 ((M,RC2) :: theta')
                 ((X,M) :: (swap rel))
                 _ _ _ _ _
            )
    end;
      repeat
        unfold get_measure ||
        steps || (progress autorewrite with bsize in * ) || t_fv_open || t_listutils ||
        apply equivalent_with_relation_add || finisher ||
        apply equal_with_relation_topen ||
        unfold equivalent_rc ||
        apply equivalent_with_relation_swap ||
        apply equal_with_relation_swap ||
        apply equal_with_relation_refl ||
        match goal with
        | H: equal_with_relation _ _ _ |- _ =>
          rewrite (equal_with_relation_size _ _ _ H) in * by steps;
          rewrite (equal_with_relation_count_interpret _ _ _ H) in * by steps
        end ||
        (rewrite substitute_topen3 in * by steps) ||
        t_apply_ih || t_bewr_constructor;
      try solve [ apply leq_lt_measure; omega ];
      try solve [ apply right_lex, right_lex, lt_index_step; auto ];
      eauto using in_remove_support;
      eauto using reducibility_is_candidate;
      eauto with bfv;
      try solve [ apply_any; assumption ].
Qed.

Hint Immediate reducible_rename_rec: b_rename.

Lemma reducible_rename_interpret: forall m T, renamable_prop_IH m -> renamable_prop m (T_interpret T).
Proof.
  unfold renamable_prop;
  repeat step || simp_red || step_inversion equal_with_relation || t_ewr_star.
  - exists t2'; unfold renamable_prop_IH in *;
      repeat step || t_apply_ih || apply left_lex ||
        match goal with
        | H: equal_with_relation _ _ _ |- _ =>
          rewrite <- (equal_with_relation_count_interpret _ _ _ H) in * by steps
        end; try omega;
        eauto 2 using equal_with_relation_irred.
  - exists t1'; unfold renamable_prop_IH in *;
      repeat step || t_apply_ih || apply left_lex ||
        match goal with
        | H: equal_with_relation _ _ _ |- _ =>
          rewrite <- (equal_with_relation_count_interpret _ _ _ H) in * by steps
        end; try omega;
        eauto 2 using equal_with_relation_irred_back.
Qed.

Hint Immediate reducible_rename_interpret: b_rename.

Lemma reducible_rename_aux: forall m T, renamable_prop m T.
Proof.
  induction m using measure_induction; destruct T;
    eauto 2 with b_rename;
    try solve [ unfold renamable_prop; repeat step || simp_red || step_inversion equal_with_relation ].
Qed.

Lemma reducible_rename :
  forall T T' t (theta theta' : interpretation) rel,
    reducible_values theta t T ->
    valid_interpretation theta ->
    valid_interpretation theta' ->
    equivalent_with_relation rel theta theta' equivalent_rc ->
    equal_with_relation rel T T' ->
    reducible_values theta' t T'     .
Proof.
  intros; eapply (reducible_rename_aux _ T T' t theta theta' rel); eauto 1.
Qed.

Lemma reducible_rename_one:
  forall RC theta v T X Y,
    reducible_values ((X,RC) :: theta) v (topen 0 T (fvar X type_var)) ->
    valid_interpretation theta ->
    reducibility_candidate RC ->
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

Lemma reducible_rename_one_rc:
  forall RC RC' theta v T X Y,
    reducible_values ((X,RC) :: theta) v (topen 0 T (fvar X type_var)) ->
    valid_interpretation theta ->
    reducibility_candidate RC ->
    reducibility_candidate RC' ->
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

Lemma reducible_rename_permute:
  forall T theta1 theta2 X Y (RC : tree -> Prop) v,
    valid_interpretation theta1 ->
    valid_interpretation theta2 ->
    reducibility_candidate RC ->
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
