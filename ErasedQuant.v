Require Export SystemFR.ErasedLet.
Require Export SystemFR.ReducibilityStep.

Opaque reducible_values.
Opaque makeFresh.

Lemma reducible_forall:
  forall theta t U V A,
    valid_interpretation theta ->
    reducible theta t A ->
    wf U 0 ->
    fv U = nil ->
    is_erased_type V ->
    (forall u, reducible_values theta u U -> reducible theta t (open 0 V u)) ->
    reducible theta t (T_forall U V).
Proof.
  unfold reducible, reduces_to;
  repeat step || t_listutils || unfold reducible, reduces_to || simp_red ||
         rewrite reducibility_rewrite;
    eauto 2 with cbvlemmas;
    eauto with fv wf;
    eauto using red_is_val.

  exists v; repeat step || simp_red || t_deterministic_star || instantiate_any;
    t_closer.
Qed.

Lemma open_reducible_forall:
  forall tvars gamma x t U V A,
    ~(x ∈ fv t) ->
    ~(x ∈ fv U) ->
    ~(x ∈ fv V) ->
    ~(x ∈ fv_context gamma) ->
    open_reducible tvars gamma t A ->
    wf U 0 ->
    subset (fv U) (support gamma) ->
    subset (fv t) (support gamma) ->
    is_erased_type V ->
    open_reducible tvars ((x, U) :: gamma) t (open 0 V (term_fvar x)) ->
    open_reducible tvars gamma t (T_forall U V).
Proof.
  unfold open_reducible in *; repeat step || t_instantiate_sat3.

  eapply reducible_forall; steps; t_closer.
  unshelve epose proof (H8 theta ((x,u) :: lterms) _ _ _); tac1.
Qed.

Lemma open_reducible_exists_elim:
  forall tvars (gamma : context) p U V t T u v,
    ~(u ∈ fv_context gamma) ->
    ~(u ∈ fv t) ->
    ~(u ∈ fv U) ->
    ~(u ∈ fv V) ->
    ~(u ∈ fv T) ->
    ~(v ∈ fv_context gamma) ->
    ~(u ∈ fv t) ->
    ~(v ∈ fv U) ->
    ~(v ∈ fv V) ->
    ~(v ∈ fv T) ->
    ~(u = v) ->
    wf U 0 ->
    wf V 1 ->
    wf t 1 ->
    wf T 0 ->
    is_erased_type T ->
    is_erased_term t ->
    subset (fv U) (support gamma) ->
    subset (fv V) (support gamma) ->
    subset (fv t) (support gamma) ->
    open_reducible tvars gamma p (T_exists U V) ->
    open_reducible tvars
                   ((v, open 0 V (term_fvar u)) :: (u, U) :: gamma)
                   (open 0 t (term_fvar v)) T ->
    open_reducible tvars gamma (app (notype_lambda t) p) T.
Proof.
  unfold open_reducible; repeat step || t_instantiate_sat3.
  pose proof H5 as Copy.
  unfold reducible, reduces_to in H5.
  repeat step || t_instantiate_sat3 || t_listutils || simp_red || t_deterministic_star ||
         apply reducible_let2 with
             (T_exists (psubstitute U lterms term_var) (psubstitute V lterms term_var)); t_closer.

  unshelve epose proof (H20 theta ((v, v1) :: (u,a) :: lterms) _ _ _); tac1.
Qed.

Lemma open_reducible_forall_inst:
  forall (tvars : list nat) (gamma : context) (t1 t2 U V : tree),
    is_erased_term t1 ->
    is_erased_term t2 ->
    wf t1 0 ->
    wf t2 0 ->
    wf V 1 ->
    subset (pfv t1 term_var) (support gamma) ->
    subset (pfv t2 term_var) (support gamma) ->
    open_reducible tvars gamma t1 (T_forall U V) ->
    open_reducible tvars gamma t2 U ->
    open_reducible tvars gamma t1 (open 0 V t2).
Proof.
  repeat step || unfold open_reducible, reducible, reduces_to in * || simp_red ||
         t_instantiate_sat3 || find_smallstep_value;
    try t_closing;
    eauto with fv wf.

  rewrite substitute_open; eauto with wf.
  eapply reducibility_values_rtl; try eassumption; steps;
    eauto with wf;
    eauto with erased.
Qed.
