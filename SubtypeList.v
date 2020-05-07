Require Export SystemFR.ReducibilityOpenEquivalent.
Require Export SystemFR.ScalaDepSugar.

Opaque reducible_values.

Lemma nil_subtype_list:
  forall Θ Γ,
    [ Θ; Γ ⊨ Nil <: List ].
Proof.
  unfold open_subtype, subtype;
    repeat step || rewrite subst_list || simp_red_top_level_hyp.
Qed.

Lemma open_subcons_helper:
  forall Θ Γ H T,
    [ Θ; Γ ⊨ Cons H T <: List ].
Proof.
  unfold open_subtype, subtype;
    repeat step || rewrite subst_list || simp_red_top_level_hyp || open_none.
Qed.

Lemma open_subcons1:
  forall Γ H T,
    [ Γ ⊨ Cons H T <: List ].
Proof.
  eauto using open_subcons_helper.
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
    [ ρ | List_Match t T2 T3 <: List_Match t' T2 T3 ].
Proof.
  unfold List_Match, subtype; intros.
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
    [ Γ ⊨ t ≡ t' ] ->
    [ Γ ⊨ List_Match t T2 T3 = List_Match t' T2 T3 ].
Proof.
  eauto using open_sub_list_match_scrut_helper.
Qed.
