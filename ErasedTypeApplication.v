Require Import Equations.Equations.
Require Import Coq.Lists.List.

Require Export SystemFR.ReducibilityOpenEquivalent.
Require Export SystemFR.ErasedTypeRefine.
Require Export SystemFR.ErasedArrow.

Opaque reducible_values.
Opaque makeFresh.

Definition type_application T1 T2 : tree :=
  T_type_refine T_top (
    T_exists T1 (
      T_exists T2 (
        T_equiv (app (lvar 1 term_var) (lvar 0 term_var)) (lvar 2 term_var)
      )
    )
  ).

Definition closed_subtype theta T1 T2 : Prop :=
  forall v,
    reducible_values theta v T1 ->
    reducible_values theta v T2.

Lemma reducible_subtype:
  forall theta t T1 T2,
    reducible theta t T1 ->
    valid_interpretation theta ->
    closed_subtype theta T1 T2 ->
    reducible theta t T2.
Proof.
  unfold closed_subtype; intros;
    eauto using reducible_values_exprs.
Qed.

Lemma closed_subtype_top:
  forall theta T,
    valid_interpretation theta ->
    closed_subtype theta T T_top.
Proof.
  unfold closed_subtype;
    repeat step || simp_red;
    eauto using reducible_values_closed.
Qed.

Lemma substitute_type_application:
  forall T1 T2 l tag,
    psubstitute (type_application T1 T2) l tag =
    type_application (psubstitute T1 l tag) (psubstitute T2 l tag).
Proof.
  unfold type_application; steps.
Qed.

Lemma reducible_type_application:
  forall theta f t A B C,
    valid_interpretation theta ->
    wf A 0 ->
    wf B 1 ->
    wf C 0 ->
    is_erased_type A ->
    is_erased_type B ->
    is_erased_type C ->
    pfv A term_var = nil ->
    pfv B term_var = nil ->
    pfv C term_var = nil ->
    reducible theta f (T_arrow A B) ->
    reducible theta t C ->
    closed_subtype theta C A ->
    reducible theta (app f t) (type_application (T_arrow A B) C).
Proof.
  unfold closed_subtype, type_application; intros.
  apply reducible_type_refine with uu;
    repeat step || list_utils;
    eauto with wf.

  - unshelve epose proof (
      reducible_app theta A B f t _ _ _ _ _ _
    ) as R;
      repeat step;
      eauto using reducible_values_exprs.

    eapply reducible_subtype; try eassumption;
      eauto using closed_subtype_top.

  - repeat rewrite open_none by t_closer.

    apply reducible_value_expr;
      repeat step || simp_red;
      t_closer.

    unfold reducible, reduces_to in *; steps.

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
  unfold open_reducible, subtype.
  intros.
  unfold substitute; steps.
  apply reducible_type_application;
    repeat step || unfold closed_subtype;
    eauto with wf;
    eauto with erased;
    eauto with fv.
Qed.
