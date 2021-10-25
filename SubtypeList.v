Require Export SystemFR.ReducibilityOpenEquivalent.
Require Export SystemFR.ScalaDepSugar.
Require Export SystemFR.EvalListMatch.
Require Export SystemFR.ErasedSingleton.
Require Export SystemFR.EquivalenceLemmas3.

Opaque reducible_values.

Lemma nil_subtype_list:
  forall Θ Γ,
    [ Θ; Γ ⊨ Nil <: List ].
Proof.
  unfold open_subtype;
    repeat step || rewrite subst_list || simp_red_top_level_hyp.
Qed.

Lemma open_subcons_helper:
  forall Θ Γ H T,
    [ Θ; Γ ⊨ Cons H T <: List ].
Proof.
  unfold open_subtype;
    repeat step || rewrite subst_list || simp_red_top_level_hyp || open_none.
Qed.

Lemma open_subcons1:
  forall Γ H T,
    [ Γ ⊫ Cons H T <: List ].
Proof.
  eauto using open_subcons_helper.
Qed.

Opaque List.

Lemma open_subcons2_helper:
  forall Θ Γ H H' T T',
    is_erased_type T' ->
    wf T 0 ->
    wf T' 0 ->
    [ Θ; Γ ⊨ H <: H' ] ->
    [ Θ; Γ ⊨ T <: T' ] ->
    [ Θ; Γ ⊨ Cons H T <: Cons H' T' ].
Proof.
  unfold open_subtype;
    repeat step || simp_red_top_level_hyp || simp_red_top_level_goal || open_none;
    eauto 2 with erased.

  exists a; repeat step || simp_red.
  exists a0; repeat step || simp_red || open_none; eauto.
Qed.

Lemma open_subcons2:
  forall Γ H H' T T',
    is_erased_type T' ->
    wf T 0 ->
    wf T' 0 ->
    [ Γ ⊫ H <: H' ] ->
    [ Γ ⊫ T <: T' ] ->
    [ Γ ⊫ Cons H T <: Cons H' T' ].
Proof.
  eauto using open_subcons2_helper.
Qed.

Lemma subtype_list_match_scrut:
  forall ρ t t' T2 T3,
    valid_interpretation ρ ->
    is_erased_type T2 ->
    is_erased_type T3 ->
    wf T2 0 ->
    wf T3 2 ->
    pfv T2 term_var = nil ->
    pfv T3 term_var = nil ->
    [ t ≡ t' ] ->
    [ ρ ⊨ List_Match t T2 T3 <: List_Match t' T2 T3 ].
Proof.
  unfold List_Match; intros.
  unshelve epose proof (reducibility_open_equivalent
   (T_union
      (T_type_refine T2 (T_equiv (lvar 1 term_var) tnil))
      (T_exists T_top
        (T_exists List
          (T_type_refine T3
            (T_equiv (lvar 3 term_var) (tcons (lvar 2 term_var) (lvar 1 term_var)))))))
   t t' ρ v _ _ _ _ _ _);
    repeat step || list_utils || open_none;
    t_closer.
Qed.

Lemma left_right_equiv:
  forall v1 v2,
    cbv_value v1 ->
    cbv_value v2 ->
    [ tleft v1 ≡ tright v2 ] ->
    False.
Proof.
  intros;
    apply_anywhere equivalent_value_left;
    repeat step;
    eauto with values.
Qed.

Lemma closed_value_is_value:
  forall v, closed_value v -> cbv_value v.
Proof.
  t_closer.
Qed.

#[export]
 Hint Resolve closed_value_is_value: values.

Lemma reducible_list_match_nil:
  forall ρ v t T1 T2,
    t ~>* tnil ->
    wf t 0 ->
    pfv t term_var = nil ->
    wf T1 0 ->
    valid_interpretation ρ ->
    [ ρ ⊨ v : List_Match t T1 T2 ]v ->
    [ ρ ⊨ v : T1 ]v.
Proof.
  unfold List_Match;
    repeat step || simp_red || open_none.

  exfalso; apply left_right_equiv with uu (pp a a0);
    eauto using left_right_equiv, equivalent_trans, equivalent_sym, equivalent_star with values.
Qed.


Lemma reducible_list_match_cons:
  forall ρ v t T1 T2 hd tl,
    closed_value hd ->
    closed_value tl ->
    t ~>* tcons hd tl ->
    wf t 0 ->
    wf T2 2 ->
    pfv t term_var = nil ->
    pfv T2 term_var = nil ->
    valid_interpretation ρ ->
    [ ρ ⊨ v : List_Match t T1 T2 ]v ->
    [ ρ ⊨ v : open 0 (open 1 T2 hd) tl ]v.
Proof.
  unfold List_Match;
    repeat step || simp_red || open_none.

  - exfalso; apply left_right_equiv with uu (pp hd tl);
      eauto with values.
    eapply equivalent_trans; eauto using equivalent_sym; equivalent_star.

  - eapply reducibility_open_equivalent2; eauto;
      repeat step.

    + apply pair_equiv_1 with a0 tl; eauto; t_closer.
      apply tright_equiv; eauto with values.
      eapply equivalent_sym.
      eapply equivalent_trans; eauto.
      eapply equivalent_sym; equivalent_star.

    + apply pair_equiv_2 with a hd; eauto; t_closer.
      apply tright_equiv; eauto with values.
      eapply equivalent_sym.
      eapply equivalent_trans; eauto.
      eapply equivalent_sym; equivalent_star.
Qed.

Opaque List_Match.

Lemma open_sub_list_match_scrut_helper:
  forall Θ Γ t t' T2 T3,
    is_erased_type T2 ->
    is_erased_type T3 ->
    wf T2 0 ->
    wf T3 2 ->
    subset (fv T2) (support Γ) ->
    subset (fv T3) (support Γ) ->
    [ Θ; Γ ⊨ t ≡ t' ] ->
    [ Θ; Γ ⊨ List_Match t T2 T3 = List_Match t' T2 T3 ].
Proof.
  unfold open_equivalent_types, equivalent_types, open_equivalent;
    repeat step || rewrite substitute_List_Match in * by eauto with wf.
  - eapply subtype_list_match_scrut; steps; eauto with erased wf fv.
  - eapply subtype_list_match_scrut; steps; eauto with erased wf fv;
      eauto using equivalent_sym.
Qed.

Lemma open_sub_list_match_scrut:
  forall Γ t t' T2 T3,
    is_erased_type T2 ->
    is_erased_type T3 ->
    wf T2 0 ->
    wf T3 2 ->
    subset (fv T2) (support Γ) ->
    subset (fv T3) (support Γ) ->
    [ Γ ⊫ t ≡ t' ] ->
    [ Γ ⊫ List_Match t T2 T3 = List_Match t' T2 T3 ].
Proof.
  eauto using open_sub_list_match_scrut_helper.
Qed.

Lemma elim_singleton:
  forall ρ v T t,
    wf t 0 ->
    [ ρ ⊨ v: T_singleton T t ]v ->
      ([ ρ ⊨ v: T ]v /\ [ v ≡ t ]).
Proof.
  unfold T_singleton;
    repeat step || simp_red || (rewrite shift_nothing2 in * by auto) || (rewrite open_none in * by auto).
Qed.

Opaque T_singleton.
Opaque List_Match.
Opaque list_match.

Lemma valid_interpretation_nil:
  valid_interpretation nil.
Proof.
  repeat step.
Qed.

Lemma equivalent_with_relation_nil:
  forall T (l1 l2: map nat T) equiv,
    equivalent_with_relation nil l1 l2 equiv.
Proof.
  unfold equivalent_with_relation;
    repeat step.
Qed.

Lemma list_values_denotation:
  forall ρ ρ' v,
    [ ρ ⊨ v : List ]v ->
    [ ρ' ⊨ v : List ]v.
Proof.
  intros; eapply reducible_rename; eauto;
    repeat step;
    eauto using equivalent_with_relation_nil;
    apply equal_with_relation_refl;
    repeat step.
Qed.

Lemma list_denotation:
  forall ρ ρ' t,
    [ ρ ⊨ t : List ] ->
    [ ρ' ⊨ t : List ].
Proof.
  unfold reduces_to; repeat step; eauto using list_values_denotation.
Qed.

Lemma invert_list_match_equiv:
  forall v t t1 t2,
    cbv_value v ->
    wf t1 0 ->
    wf t2 2 ->
    is_erased_term t1 ->
    is_erased_term t2 ->
    pfv t1 term_var = nil ->
    pfv t2 term_var = nil ->
    [ t : List ] ->
    [ list_match t t1 t2 ≡ v ] -> (
      (t ~>* tnil /\ [ t1 ≡ v ]) \/
      (exists hd tl,
        closed_value hd /\
        closed_value tl /\
        [ tl : List ]v /\
        t ~>* tcons hd tl /\
        [ open 0 (open 1 t2 hd) tl ≡ v ]
      )
    ).
Proof.
  intros; apply_anywhere equivalent_value; repeat step || evaluate_list_match2.
  - left; repeat step.
    eapply equivalent_trans; eauto.
    equivalent_star; eauto using star_many_steps, value_irred.
  - right; repeat step.
    exists h, l; repeat step; eauto;
      repeat step;
      eauto using valid_interpretation_nil with erased wf fv.
    eapply equivalent_trans; eauto.
    apply equivalent_sym.
    apply equivalent_trans with (list_match t t1 t2); eauto.
    apply equivalent_sym; equivalent_star.
Qed.

Ltac invert_list_match_equiv :=
  match goal with
  | H: [ list_match _ _ _ ≡ ?v ] |- _ => apply_anywhere invert_list_match_equiv
  | H: [ ?v ≡ list_match _ _ _ ] |- _ => apply equivalent_sym in H; apply invert_list_match_equiv in H
  end.

Lemma open_sub_list_case_split:
  forall Θ Γ t2 t3 T2 T3 T t ev x y,
    is_erased_type T2 ->
    is_erased_type T3 ->
    is_erased_term t ->
    is_erased_term t2 ->
    is_erased_term t3 ->
    wf T2 0 ->
    wf T3 2 ->
    wf t 0 ->
    wf t2 0 ->
    wf t3 2 ->
    subset (fv t) (support Γ) ->
    subset (fv t2) (support Γ) ->
    subset (fv t3) (support Γ) ->
    subset (fv T3) (support Γ) ->
    ev <> x ->
    ev <> y ->
    x <> y ->
    ~ ev ∈ pfv t term_var ->
    ~ ev ∈ pfv t3 term_var ->
    ~ ev ∈ pfv T3 term_var ->
    ~ ev ∈ pfv T term_var ->
    ~ ev ∈ pfv_context Γ term_var ->
    ~ x ∈ pfv_context Γ term_var ->
    ~ y ∈ pfv_context Γ term_var ->
    ~ x ∈ pfv t term_var ->
    ~ y ∈ pfv t term_var ->
    ~ x ∈ pfv t3 term_var ->
    ~ x ∈ pfv T term_var ->
    ~ y ∈ pfv t3 term_var ->
    ~ x ∈ pfv T3 term_var ->
    ~ y ∈ pfv T3 term_var ->
    ~ y ∈ pfv T term_var ->
    [ Θ; Γ ⊨ t : List ] ->
    [ Θ; Γ ⊨ T_singleton T2 t2  <: T ] ->
    [ Θ; (ev, T_equiv t (tcons (fvar x term_var) (fvar y term_var))) ::
         (y, List) ::
         (x, T_top) ::
         Γ ⊨
      T_singleton
        (open 0 (open 1 T3 (fvar x term_var)) (fvar y term_var))
        (open 0 (open 1 t3 (fvar x term_var)) (fvar y term_var)) <: T ] ->
    [ Θ; Γ ⊨ T_singleton (List_Match t T2 T3) (list_match t t2 t3)  <: T ].
Proof.
  intros; unfold open_subtype;
    repeat step || eauto with wf || apply_anywhere elim_singleton ||
           rewrite substitute_singleton, substitute_list_match, substitute_List_Match in * by eauto with wf.

  invert_list_match_equiv; repeat step; t_closer.

  (* case where `t` (after substitution) reduces to nil *)
  - apply H32;
      repeat step || rewrite substitute_singleton || apply reducible_values_singleton;
      eauto with wf;
      eauto with values;
      eauto 2 using equivalent_sym;
      eauto using reducible_list_match_nil with wf fv.

  (* case where `t` (after substitution) reduces to cons *)
  - unshelve epose proof H33 ρ ((ev, uu) :: (y, tl) :: (x, hd) :: l) _ _ _ v _;
      repeat step || apply SatCons || list_utils || simp_red || t_substitutions ||
             rewrite substitute_singleton || rewrite subst_list || apply reducible_values_singleton ||
             rewrite substitute_open3 by (repeat step || fv_open; t_closer);
      try solve [ equivalent_star ];
      t_closer;
      eauto using list_values_denotation.

    eapply reducible_list_match_cons; eauto;
      t_closer.

  - eapply list_denotation; eauto with eapply_any.
Qed.
