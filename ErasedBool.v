Require Import Equations.Equations.
Require Import Coq.Lists.List.

Require Export SystemFR.RedTactics.

Opaque reducible_values.
Opaque makeFresh.

Lemma reducible_true:
  forall theta, reducible_values theta ttrue T_bool.
Proof.
  repeat step || simp_red.
Qed.

Lemma open_reducible_true:
  forall theta gamma,
    open_reducible theta gamma ttrue T_bool.
Proof.
  unfold open_reducible, reducible, reduces_to, closed_term in *; steps;
    eauto using reducible_true with star.
Qed.

Lemma reducible_false:
  forall theta, reducible_values theta tfalse T_bool.
Proof.
  repeat step || simp_red.
Qed.

Lemma open_reducible_false:
  forall theta gamma,
    open_reducible theta gamma tfalse T_bool.
Proof.
  unfold open_reducible, reducible, reduces_to, closed_term in *; steps;
    eauto using reducible_false with star.
Qed.

Lemma reducible_ite:
  forall theta T b t1 t2,
    wf t1 0 ->
    wf t2 0 ->
    pfv t1 term_var = nil ->
    pfv t2 term_var = nil ->
    is_erased_term t1 ->
    is_erased_term t2 ->
    valid_interpretation theta ->
    reducible theta b T_bool ->
    (equivalent_terms b ttrue -> reducible theta t1 T) ->
    (equivalent_terms b tfalse -> reducible theta t2 T) ->
    reducible theta (ite b t1 t2) T.
Proof.
  repeat step || top_level_unfold reducible || top_level_unfold reduces_to ||
         top_level_unfold closed_term ||
         simp reducible_values in *.

  - apply star_backstep_reducible with (ite ttrue t1 t2); repeat step || t_listutils;
      auto with cbvlemmas; eauto with fv; eauto with wf.
    eapply backstep_reducible; repeat step || t_listutils;
      eauto 2 with smallstep;
      eauto with fv;
      eauto with wf;
      eauto using equivalent_star.

  - apply star_backstep_reducible with (ite tfalse t1 t2); repeat step || t_listutils;
      auto with cbvlemmas; eauto with fv; eauto with wf.
    eapply backstep_reducible; repeat step || t_listutils;
      eauto 2 with smallstep;
      eauto with fv;
      eauto with wf;
      eauto using equivalent_star.
Qed.

Lemma open_reducible_ite:
  forall tvars gamma T b t1 t2 x,
    wf t1 0 ->
    wf t2 0 ->
    subset (fv t1) (support gamma) ->
    subset (fv t2) (support gamma) ->
    ~(x ∈ fv b) ->
    ~(x ∈ fv T) ->
    ~(x ∈ fv_context gamma) ->
    ~(x ∈ tvars) ->
    is_erased_term b ->
    is_erased_term t1 ->
    is_erased_term t2 ->
    open_reducible tvars gamma b T_bool ->
    open_reducible tvars ((x, T_equiv b ttrue) :: gamma) t1 T ->
    open_reducible tvars ((x, T_equiv b tfalse) :: gamma) t2 T ->
    open_reducible tvars gamma (ite b t1 t2) T.
Proof.
  intros; unfold open_reducible; steps.

  unfold open_reducible in *; apply reducible_ite; repeat step || t_termlist;
    eauto with wf;
    eauto using subset_same with fv;
    eauto with erased.

  - unshelve epose proof (H11 _ ((x, uu) :: lterms) _ _ _); tac1.
  - unshelve epose proof (H12 _ ((x, uu) :: lterms) _ _ _); tac1.
Qed.
