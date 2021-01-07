Require Import Equations.Equations.
Require Import Coq.Lists.List.

Require Export SystemFR.ReducibilityOpenEquivalent.
Require Export SystemFR.ErasedTypeRefine.
Require Export SystemFR.ErasedArrow.
Require Export SystemFR.ScalaDepSugar.
Require Export SystemFR.ReducibilitySubtype.
Require Export SystemFR.SubtypeMisc.

Opaque reducible_values.
Opaque makeFresh.

Lemma substitute_type_application:
  forall T1 T2 l tag,
    psubstitute (type_application T1 T2) l tag =
    type_application (psubstitute T1 l tag) (psubstitute T2 l tag).
Proof.
  unfold type_application; steps.
Qed.

Lemma reducible_type_application:
  forall ρ f t A B C,
    valid_interpretation ρ ->
    wf A 0 ->
    wf B 1 ->
    wf C 0 ->
    is_erased_type A ->
    is_erased_type B ->
    is_erased_type C ->
    pfv A term_var = nil ->
    pfv B term_var = nil ->
    pfv C term_var = nil ->
    [ ρ ⊨ f : T_arrow A B ] ->
    [ ρ ⊨ t : C ] ->
    [ ρ ⊨ C <: A ] ->
    [ ρ ⊨ app f t : type_application (T_arrow A B) C ].
Proof.
  unfold type_application; intros.
  apply reducible_type_refine with uu;
    repeat step || list_utils;
    eauto with wf.

  - unshelve epose proof (
      reducible_app ρ A B f t _ _ _ _ _ _
    ) as R;
      repeat step;
      eauto using reducible_values_exprs.

    eapply subtype_reducible; try eassumption;
      eauto using subtype_top.

  - repeat rewrite open_none by t_closer.

    apply reducible_value_expr;
      repeat step || simp_red_top_level_goal;
      t_closer.

    unfold reduces_to in *; steps.

    exists v0; repeat step; t_closer.
    repeat rewrite open_none by t_closer.

    clear H15.

    simp_red; repeat step; t_closer.

    exists v; repeat step; t_closer.
    repeat rewrite open_none by t_closer.

    simp_red; steps.
    apply equivalent_app;
      try solve [ apply equivalent_sym; equivalent_star ].
Qed.

Lemma open_reducible_type_application:
  forall tvars gamma f t A B C,
    wf A 0 ->
    wf B 1 ->
    wf C 0 ->
    is_erased_type A ->
    is_erased_type B ->
    is_erased_type C ->
    subset (fv A) (support gamma) ->
    subset (fv B) (support gamma) ->
    subset (fv C) (support gamma) ->
    [ tvars; gamma ⊨ f : T_arrow A B ] ->
    [ tvars; gamma ⊨ t : C ] ->
    [ tvars; gamma ⊨ C <: A ] ->
    [ tvars; gamma ⊨ app f t : type_application (T_arrow A B) C ].
Proof.
  unfold open_reducible, open_subtype.
  intros.
  unfold substitute; steps.
  apply reducible_type_application;
    repeat step || unfold subtype;
    eauto with wf;
    eauto with erased;
    eauto with fv.
Qed.
