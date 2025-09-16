From Equations Require Import Equations.
From Stdlib Require Import List.
Import ListNotations.

Require Export SystemFR.ErasedTypeRefine.
Require Export SystemFR.ErasedArrow.
Require Export SystemFR.ErasedTypeApplication.

Require Export SystemFR.ReducibilityEquivalent.

Opaque reducible_values.
Opaque makeFresh.

Definition type_open T1 T2 : tree :=
  T_exists T2 (shift_open 0 T1 (lvar 0 term_var)).

(*
Definition equivalent_terms_at (theta: interpretation) T t1 t2 :=
  is_erased_term t1 /\
  is_erased_term t2 /\
  wf t1 0 /\
  wf t2 0 /\
  pfv t1 term_var = nil /\
  pfv t2 term_var = nil /\
  forall C,
    (forall v, reducible_values theta v T ->
          div_reducible theta (open 0 C v) T_top) ->
    is_erased_term C ->
    wf C 1 ->
    pfv C term_var = nil ->
    scbv_normalizing (open 0 C t1) <-> scbv_normalizing (open 0 C t2).
*)
(*
Lemma singleton_identity:
  is_singleton [] []
    (notype_lambda (lvar 0 term_var))
    (T_arrow T_nat (singleton (lvar 0 term_var))).
Proof.
  unfold is_singleton;
    repeat step || simp_red;
    t_closer.

  - unfold reduces_to; steps; t_closer.
    exists a; repeat step || simp_red || rewrite open_none by auto; t_closer.
    + exists uu; repeat step || simp_red; eauto using equivalent_refl.

    + apply star_one.
      constructor; t_closer.

  - unfold equivalent_terms_at;
      repeat step;
      t_closer.
*)

Definition sub_singleton tvars gamma v T : Prop :=
  forall theta l v',
    valid_interpretation theta ->
    satisfies (reducible_values theta) gamma l  ->
    support theta = tvars ->
    reducible_values theta v' (psubstitute T l term_var) ->
    equivalent_terms v' (psubstitute v l term_var).

Lemma reducibility_open_equivalent2:
  forall T t1 t2 ρ t,
    [ ρ ⊨ t : open 0 T t1 ] ->
    valid_interpretation ρ ->
    is_erased_type T ->
    wf T 1 ->
    pfv T term_var = nil ->
    [ t1 ≡ t2 ] ->
    [ ρ ⊨ t : open 0 T t2 ].
Proof.
  eauto using reducibility_open_equivalent, reducible_values_exprs.
Qed.

Lemma open_subtype_type_application:
  forall tvars gamma A B C c,
    wf A 0 ->
    wf B 1 ->
    wf C 0 ->
    wf c 0 ->
    is_erased_term c ->
    is_erased_type A ->
    is_erased_type B ->
    is_erased_type C ->
    subset (fv A) (support gamma) ->
    subset (fv B) (support gamma) ->
    subset (fv C) (support gamma) ->
    subset (fv c) (support gamma) ->
    sub_singleton tvars gamma c C ->
    [ tvars; gamma ⊨ C <: A ] ->
    [ tvars; gamma ⊨ type_application (T_arrow A B) C <: open 0 B c ].
Proof.
  unfold open_subtype;
    repeat step || simp_red ||
           (rewrite open_none in * by eauto with wf) ||
           (rewrite (open_none v) in * by t_closer) ||
           (rewrite (open_none (psubstitute C l term_var) 1) in * by eauto with wf).

  apply reducible_expr_value; t_closer.

  eapply reducibility_equivalent2; try eassumption;
    repeat step ||
           apply wf_open || apply wf_subst ||
           apply is_erased_type_open || apply subst_erased_type;
    t_closer.

  - apply fv_nils2; eauto with fv.
    eapply subset_transitive; eauto using fv_open;
      repeat step || sets;
      t_closer.

  - t_substitutions.
    apply reducibility_open_equivalent2 with a0;
      repeat step || apply_any; t_closer.
Qed.

Lemma sub_singleton_value:
  forall v T,
    closed_value v ->
    sub_singleton [] [] v (T_singleton T v).
Proof.
  unfold sub_singleton;
    repeat step || simp_red ||
           (rewrite open_none in * by t_closer) ||
           (rewrite shift_nothing2 in * by t_closer).
Qed.
