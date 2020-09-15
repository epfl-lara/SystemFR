Require Import Equations.Equations.

Require Import Coq.Lists.List.
Import ListNotations.

Require Export SystemFR.TypeSugar.

Opaque T_reducible.
Opaque reducible_values.

Definition T_equivalent_at A t1 t2: tree :=
  T_type_refine
    T_unit
      (T_intersection
        (T_forall
           (T_arrow A T_bool)
           (T_equiv (app (lvar 0 term_var) t1) (app (lvar 0 term_var) t2))
        )
        (T_intersection (T_reducible t1 A) (T_reducible t2 A))
      ).

Lemma subst_equivalent_at:
  forall A t1 t2 l tag,
    psubstitute (T_equivalent_at A t1 t2) l tag =
    T_equivalent_at (psubstitute A l tag) (psubstitute t1 l tag) (psubstitute t2 l tag).
Proof.
  unfold T_equivalent_at;
    repeat step.
Qed.

Definition equivalent_at theta A t1 t2: Prop :=
  reducible theta t1 A /\
  reducible theta t2 A /\
  forall f,
    is_erased_term f ->
    wf f 0 ->
    pfv f term_var = nil ->
    reducible_values theta f (T_arrow A T_bool) ->
    equivalent_terms (app f t1) (app f t2).

Lemma equivalent_at_prop_type:
  forall theta A t1 t2,
    is_erased_type A ->
    is_erased_term t1 ->
    is_erased_term t2 ->
    wf A 0 ->
    wf t1 0 ->
    wf t2 0 ->
    twf A 0 ->
    equivalent_at theta A t1 t2 ->
    reducible_values theta uu (T_equivalent_at A t1 t2).
Proof.
  unfold equivalent_at, T_equivalent_at;
    repeat step || simp_red_top_level_goal ||
           (rewrite open_none in * by t_closer);
    t_closer;
    eauto using is_erased_type_T_reducible.

  exists uu;
    repeat step || simp_red_goal || apply reducible_values_prop_type ||
           (rewrite open_T_reducible in * by auto) ||
           (rewrite open_none in * by t_closer);
    t_closer.
Qed.

Lemma equivalent_at_type_prop:
  forall theta A t1 t2 p,
    is_erased_type A ->
    is_erased_term t1 ->
    is_erased_term t2 ->
    wf A 0 ->
    wf t1 0 ->
    wf t2 0 ->
    pfv A term_var = nil ->
    pfv t1 term_var = nil ->
    pfv t2 term_var = nil ->
    twf A 0 ->
    valid_interpretation theta ->
    reducible_values theta p (T_equivalent_at A t1 t2) ->
    equivalent_at theta A t1 t2.
Proof.
  unfold equivalent_at, T_equivalent_at;
    repeat step || simp reducible_values in H10 || list_utils ||
         apply_anywhere reducible_values_type_prop ||
         (rewrite open_T_reducible in * by auto) ||
         (rewrite open_none in * by t_closer) ||
         (rewrite topen_none in * by t_closer);
    t_closer.

  unshelve epose proof (H25 _ _ _ _ H14) as HH;
    repeat step.

  simp reducible_values in HH;
    repeat step || (rewrite open_none in * by t_closer).
Qed.

Lemma equivalent_at_type_prop2:
  forall theta A t1 t2 p,
    is_erased_type A ->
    is_erased_term t1 ->
    is_erased_term t2 ->
    wf A 0 ->
    wf t1 0 ->
    wf t2 0 ->
    pfv A term_var = nil ->
    pfv t1 term_var = nil ->
    pfv t2 term_var = nil ->
    twf A 0 ->
    valid_interpretation theta ->
    reducible theta p (T_equivalent_at A t1 t2) ->
    equivalent_at theta A t1 t2.
Proof.
  unfold reducible, reduces_to;
    repeat step;
    eauto using equivalent_at_type_prop.
Qed.
