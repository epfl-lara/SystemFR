Require Export SystemFR.ErasedRefine.
Require Export SystemFR.ErasedTypeRefine.
Require Export SystemFR.ErasedSetOps.

Require Export SystemFR.TypeSugar.

Require Import Coq.Lists.List.

Lemma open_reducible_T_ite:
  forall tvars gamma T1 T2 b t1 t2 x,
    wf t1 0 ->
    wf t2 0 ->
    wf T1 0 ->
    wf T2 0 ->
    is_erased_term t1 ->
    is_erased_term t2 ->
    is_erased_type T1 ->
    is_erased_type T2 ->
    subset (fv b) (support gamma) ->
    subset (fv t1) (support gamma) ->
    subset (fv t2) (support gamma) ->
    subset (fv T1) (support gamma) ->
    subset (fv T2) (support gamma) ->
    ~(x ∈ fv b) ->
    ~(x ∈ fv t1) ->
    ~(x ∈ fv t2) ->
    ~(x ∈ fv T1) ->
    ~(x ∈ fv T2) ->
    ~(x ∈ fv_context gamma) ->
    ~(x ∈ tvars) ->
    is_erased_term b ->
    is_erased_term t1 ->
    is_erased_term t2 ->
    [ tvars; gamma ⊨ b : T_bool ] ->
    [ tvars; (x, T_equiv b ttrue) :: gamma ⊨ t1 : T1 ] ->
    [ tvars; (x, T_equiv b tfalse) :: gamma ⊨ t2 : T2 ] ->
    [ tvars; gamma ⊨ ite b t1 t2 : T_ite b T1 T2 ].
Proof.
  unfold open_reducible; repeat step || t_instantiate_sat3.
  repeat apply reducible_union || step || top_level_unfold reducible || top_level_unfold reduces_to || simp_red.

  - left.
    apply reducible_refine; repeat step || (rewrite open_none by eauto with wf);
      eauto with wf erased fv;
      try solve [ apply equivalent_star; steps; eauto with fv wf erased ].

    eapply star_backstep_reducible; repeat step || list_utils; eauto with cbvlemmas;
      eauto with fv wf erased.

    eapply backstep_reducible; eauto with smallstep; repeat step || list_utils;
      eauto with fv wf erased.

    unshelve epose proof (H23 theta ((x, uu) :: lterms) _ _); tac1;
      try solve [ apply equivalent_star; steps; eauto with erased wf fv ].

  - right.
    apply reducible_refine; repeat step || (rewrite open_none by eauto with wf) || list_utils;
      eauto with wf fv erased;
      try solve [
        apply equivalent_star; repeat step || list_utils; eauto with erased wf fv;
        eapply star_trans; eauto using star_smallstep_ite_cond; eauto using star_one with smallstep
      ].

    eapply star_backstep_reducible; repeat step || list_utils; eauto with cbvlemmas;
      eauto with fv;
      eauto with wf;
      eauto with erased.

    eapply backstep_reducible; eauto with smallstep; repeat step || list_utils;
      eauto with fv wf erased.

    unshelve epose proof (H24 theta ((x, uu) :: lterms) _ _); tac1;
      try solve [ apply equivalent_star; steps; eauto with erased wf fv ].
Qed.
