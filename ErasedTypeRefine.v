Require Import Equations.Equations.

Require Import Coq.Arith.PeanoNat.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.

Require Export SystemFR.ErasedLet.
Require Export SystemFR.ReducibilityStep.

Opaque reducible_values.
Opaque makeFresh.

Lemma reducible_type_refine:
  forall theta t1 t2 A B,
    valid_interpretation theta ->
    is_erased_type B ->
    wf B 1 ->
    reducible theta t1 A ->
    reducible theta t2 (open 0 B t1) ->
    reducible theta t1 (T_type_refine A B).
Proof.
  unfold reducible, reduces_to in *; repeat step;
    eauto with wf; eauto with fv.

  eexists; steps; eauto;
    repeat step || simp_red; t_closer.
  eexists; eapply reducibility_values_ltr; eauto; steps;
    t_closer.
Qed.

Lemma open_reducible_type_refine:
  forall tvars gamma t1 t2 A B,
    is_erased_type B ->
    wf B 1 ->
    open_reducible tvars gamma t1 A ->
    open_reducible tvars gamma t2 (open 0 B t1) ->
    open_reducible tvars gamma t1 (T_type_refine A B).
Proof.
  unfold open_reducible;
    repeat step || t_instantiate_sat3 || t_substitutions || eapply reducible_type_refine;
    eauto with erased;
    try solve [ unshelve eauto with wf; auto ].
Qed.

Lemma open_reducible_get_refinement_witness:
  forall tvars gamma t1 t2 A B T x,
    ~(x ∈ tvars) ->
    ~(x ∈ fv_context gamma) ->
    ~(x ∈ fv t1) ->
    ~(x ∈ fv t2) ->
    ~(x ∈ fv T) ->
    ~(x ∈ fv A) ->
    ~(x ∈ fv B) ->
    wf t1 0 ->
    wf t2 0 ->
    wf B 1 ->
    is_erased_term t2 ->
    subset (fv t1) (support gamma) ->
    subset (fv t2) (support gamma) ->
    open_reducible tvars gamma t1 (T_type_refine A B) ->
    open_reducible tvars ((x, open 0 B t1) :: gamma) t2 T ->
    open_reducible tvars gamma (app (notype_lambda t2) uu) T.
Proof.
  unfold open_reducible; repeat step || t_instantiate_sat3.
  eapply backstep_reducible; eauto with smallstep values;
    repeat step || t_listutils; eauto with fv wf erased.
  rewrite open_none; eauto with wf.
  top_level_unfold reducible; top_level_unfold reduces_to; repeat step || simp_red.

  unshelve epose proof (H13 theta ((x, p) :: lterms) _ _ _); tac1.
  eapply reducibility_values_rtl; eauto;
    repeat step;
    eauto with wf;
    eauto with erased.
Qed.
