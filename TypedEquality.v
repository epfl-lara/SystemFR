From Equations Require Import Equations.

From Stdlib Require Import List.
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

Definition equivalent_at ρ A t1 t2: Prop :=
  [ ρ ⊨ t1 : A ] /\
  [ ρ ⊨ t2 : A ] /\
  forall f,
    is_erased_term f ->
    wf f 0 ->
    pfv f term_var = nil ->
    [ ρ ⊨ f : T_arrow A T_bool ]v ->
    [ app f t1 ≡ app f t2 ].

Notation "[ ρ ⊨ t1 ≡ t2 : A ]" := (equivalent_at ρ A t1 t2)
  (at level 60, ρ at level 60, t1 at level 60, t2 at level 60).
Notation "[ t1 ≡ t2 : A ]" := ([ nil ⊨ t1 ≡ t2 : A ])
  (at level 60, t1 at level 60, t2 at level 60).

Lemma equivalent_at_prop_type:
  forall ρ A t1 t2,
    is_erased_type A ->
    is_erased_term t1 ->
    is_erased_term t2 ->
    wf A 0 ->
    wf t1 0 ->
    wf t2 0 ->
    twf A 0 ->
    [ ρ ⊨ t1 ≡ t2 : A ] ->
    [ ρ ⊨ uu : T_equivalent_at A t1 t2 ]v.
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
  forall ρ A t1 t2 p,
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
    valid_interpretation ρ ->
    [ ρ ⊨ p : T_equivalent_at A t1 t2 ]v ->
    [ ρ ⊨ t1 ≡ t2 : A ].
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
  forall ρ A t1 t2 p,
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
    valid_interpretation ρ ->
    [ ρ ⊨ p : T_equivalent_at A t1 t2 ] ->
    [ ρ ⊨ t1 ≡ t2 : A ].
Proof.
  unfold reduces_to;
    repeat step;
    eauto using equivalent_at_type_prop.
Qed.
