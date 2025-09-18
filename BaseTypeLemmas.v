From Stdlib Require Import List.
From Stdlib Require Import String.

Require Export SystemFR.ReducibilityUnused.
Require Export SystemFR.BaseType.

From Stdlib Require Import Psatz.

Opaque reducible_values.

Lemma base_type_open:
  forall X T T0, base_type X T T0 -> forall k a,
    is_erased_term a ->
    base_type X (open k T a) (open k T0 a).
Proof.
  induction 1; repeat step || constructor || fv_open || list_utils || rewrite is_erased_term_tfv in * by assumption;
    eauto with fv;
    eauto with erased.
Qed.

Lemma base_type_erased:
  forall X T T0,
    base_type X T T0 ->
    is_erased_type T0.
Proof.
  induction 1; steps.
Qed.

#[export]
Hint Immediate base_type_erased: erased.

Lemma base_type_approx_aux:
  forall n X Ts T ρ l v RC,
    type_nodes T < n ->
    wfs l 0 ->
    pclosed_mapping l type_var ->
    base_type X Ts T ->
    erased_terms l ->
    valid_interpretation ρ ->
    reducibility_candidate RC ->
    (* RC can be instantiated by the denotation of T_rec zero T0 Ts *)
    reducible_values ((X, RC) :: ρ) v (psubstitute Ts l term_var) ->
    [ ρ ⊨ v : psubstitute T l term_var ]v.
Proof.
  induction n; intros; try lia; inversion H2;
    repeat match goal with
    | _ =>
      step || simp_red || find_exists ||
      (rewrite substitute_open2 in * by (t_closing; eauto with fv))
    end;
    try lia;
    try solve [ eapply_any; steps; eauto with lia ];
    try solve [ eapply_any; repeat step || autorewrite with bsize in *;
                eauto 1; try lia; eauto 2 using base_type_open; eauto 2 with erased ];
    t_closer;
    eauto 2 using reducible_values_closed with step_tactic;
    try solve [ eapply reducible_unused3; eauto 1; repeat step || rewrite fv_subst_different_tag in * by steps ].
Qed.

Lemma base_type_approx:
  forall X Ts T ρ l v RC,
    (* RC can be instantiated by the denotation of T_rec zero T0 Ts *)
    reducible_values ((X, RC) :: ρ) v (psubstitute Ts l term_var) ->
    wfs l 0 ->
    pclosed_mapping l type_var ->
    base_type X Ts T ->
    erased_terms l ->
    valid_interpretation ρ ->
    reducibility_candidate RC ->
    [ ρ ⊨ v : psubstitute T l term_var ]v.
Proof.
  intros; eauto using base_type_approx_aux.
Qed.
