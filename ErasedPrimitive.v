Require Export SystemFR.ReducibilityOpenEquivalent.

Opaque reducible_values.
Opaque makeFresh.

Hint Rewrite PeanoNat.Nat.leb_le: primitives.
Hint Rewrite PeanoNat.Nat.leb_gt: primitives.
Hint Rewrite PeanoNat.Nat.ltb_lt: primitives.
Hint Rewrite PeanoNat.Nat.ltb_ge: primitives.

Opaque PeanoNat.Nat.leb.
Opaque PeanoNat.Nat.ltb.

Lemma last_step_unary_primitive:
  forall v1 v o,
    cbv_value v1 ->
    cbv_value v ->
    unary_primitive o v1 ~>* v ->
    unary_primitive o v1 ~> v.
Proof.
  intros.
  inversion H1; clear H1.
  destruct v; steps; step_inversion cbv_value.
  force_invert scbv_step;
    repeat star_smallstep_value || steps || constructor || no_step ; eauto with values smallstep ;
      try solve [eapply scbv_step_same; [constructor |]; steps].
Qed.

Lemma last_step_binary_primitive:
  forall v1 v2 v o,
    cbv_value v1 ->
    cbv_value v2 ->
    cbv_value v ->
    binary_primitive o v1 v2 ~>* v ->
    binary_primitive o v1 v2 ~> v.
Proof.
  intros.
  inversion H2; clear H2.
  destruct v; steps; step_inversion cbv_value.
  force_invert scbv_step;
    repeat star_smallstep_value || steps || constructor || no_step ; eauto with values smallstep ;
      try solve [eapply scbv_step_same; [constructor |]; steps].
Qed.

Ltac last_step_binary_primitive :=
    apply_anywhere last_step_binary_primitive; eauto with values;
    force_invert scbv_step; repeat build_nat_inj || steps || autorewrite with primitives in *.

Ltac reducible_values_primitive :=
  unfold reduces_to; intros ;
  repeat simp_red ;
  repeat is_nat_value_buildable ; steps ;
      (unfold closed_term; repeat light || rewrite app_eq_nil_iff ; eauto 1 with fv wf erased) ||
      (eexists; split; [ idtac | (apply star_one; constructor; try reflexivity )] ;
      eauto using is_nat_value_build_nat).

Ltac reducible_primitive f :=
  intros;
  repeat top_level_unfold reduces_to || steps || simp_red || is_nat_value_buildable;
  eapply star_backstep_reducible;
    try apply star_smallstep_binary_primitive; eauto ;
    repeat steps || list_utils || simp_red || apply f || eauto with values cbvlemmas ; t_closer.

(* Not *)

Lemma reducible_values_primitive_Not:
  forall ρ v1,
    [ ρ ⊨ v1 : T_bool ]v ->
    [ ρ ⊨ unary_primitive Not v1 : T_bool ].
Proof.
  unfold reduces_to;
    repeat steps || simp_red; t_closer ;
      solve [
          eexists ; split ; [idtac | (apply star_one ; constructor ; try reflexivity)] ;  steps ].
  Qed.

Lemma reducible_primitive_Not:
  forall ρ t1,
    valid_interpretation ρ ->
    [ ρ ⊨ t1 : T_bool ] ->
    [ ρ ⊨ unary_primitive Not t1 : T_bool ].
Proof.
  reducible_primitive reducible_values_primitive_Not.
  Qed.

Lemma open_reducible_primitive_Not:
  forall Θ Γ t1,
    [ Θ;Γ ⊨ t1 : T_bool ] ->
    [ Θ;Γ ⊨ unary_primitive Not t1 : T_bool ].
Proof. unfold open_reducible; steps;  eauto using reducible_primitive_Not. Qed.

(* Plus *)

Lemma reducible_values_primitive_Plus:
  forall ρ v1 v2,
    [ ρ ⊨ v1 : T_nat ]v ->
    [ ρ ⊨ v2 : T_nat ]v ->
    [ ρ ⊨ binary_primitive Plus v1 v2 : T_nat ].
Proof. reducible_values_primitive. Qed.

Lemma reducible_primitive_Plus:
  forall ρ t1 t2,
    valid_interpretation ρ ->
    [ ρ ⊨ t1 : T_nat ] ->
    [ ρ ⊨ t2 : T_nat ] ->
    [ ρ ⊨ binary_primitive Plus t1 t2 : T_nat ].
Proof. reducible_primitive reducible_values_primitive_Plus. Qed.

Lemma open_reducible_primitive_Plus:
  forall Θ Γ t1 t2,
    [Θ; Γ ⊨ t1 : T_nat] ->
    [Θ; Γ ⊨ t2 : T_nat] ->
    [Θ; Γ ⊨ binary_primitive Plus t1 t2 : T_nat].
Proof. unfold open_reducible; steps ; eauto using reducible_primitive_Plus. Qed.

(* Minus *)


Lemma reducible_values_primitive_Minus:
  forall ρ v1 v2,
    [ ρ ⊨ v1 : T_nat ]v ->
    [ ρ ⊨ v2 : T_nat ]v ->
    [ binary_primitive Geq v1 v2 ≡ ttrue ] ->
    [ ρ ⊨ binary_primitive Minus v1 v2 : T_nat ].
Proof.
  reducible_values_primitive.
  apply_anywhere equivalent_true.
  last_step_binary_primitive.
Qed.

Lemma reducible_primitive_Minus:
  forall ρ t1 t2,
    valid_interpretation ρ ->
    [ ρ ⊨ t1 : T_nat ] ->
    [ ρ ⊨ t2 : T_nat ] ->
    [ binary_primitive Geq t1 t2 ≡ ttrue ] ->
    [ ρ ⊨ binary_primitive Minus t1 t2 : T_nat ].
Proof. reducible_primitive reducible_values_primitive_Minus.
       eapply equivalent_trans; eauto.
       apply equivalent_sym, equivalent_star; eauto with cbvlemmas smallstep wf fv; t_closer.
       apply star_smallstep_binary_primitive; eauto with values.
Qed.

Lemma open_reducible_primitive_Minus:
  forall Θ Γ t1 t2,
    [Θ; Γ ⊨ t1 : T_nat] ->
    [Θ; Γ ⊨ t2 : T_nat] ->
    [Θ; Γ ⊨ binary_primitive Geq t1 t2 ≡ ttrue ] ->
    [Θ; Γ ⊨ binary_primitive Minus t1 t2 : T_nat].
Proof. unfold open_reducible, open_equivalent; steps;
         eauto using reducible_primitive_Minus.
Qed.

(* Mul *)

Lemma reducible_values_primitive_Mul:
  forall ρ v1 v2,
    [ ρ ⊨ v1 : T_nat ]v ->
    [ ρ ⊨ v2 : T_nat ]v ->
    [ ρ ⊨ binary_primitive Mul v1 v2 : T_nat ].
Proof. reducible_values_primitive. Qed.

Lemma reducible_primitive_Mul:
  forall ρ t1 t2,
    valid_interpretation ρ ->
    [ ρ ⊨ t1 : T_nat ] ->
    [ ρ ⊨ t2 : T_nat ] ->
    [ ρ ⊨ binary_primitive Mul t1 t2 : T_nat ].
Proof. reducible_primitive reducible_values_primitive_Mul. Qed.

Lemma open_reducible_primitive_Mul:
  forall Θ Γ t1 t2,
    [Θ; Γ ⊨ t1 : T_nat] ->
    [Θ; Γ ⊨ t2 : T_nat] ->
    [Θ; Γ ⊨ binary_primitive Mul t1 t2 : T_nat].
Proof. unfold open_reducible; steps ; eauto using reducible_primitive_Mul. Qed.

(* Div *)

Lemma reducible_values_primitive_Div:
  forall ρ v1 v2 ,
    [ ρ ⊨ v1 : T_nat ]v ->
    [ ρ ⊨ v2 : T_nat ]v ->
    [ binary_primitive Gt v2 zero ≡ ttrue] ->
    [ ρ ⊨ binary_primitive Div v1 v2 : T_nat ].
Proof. reducible_values_primitive. apply_anywhere equivalent_true. last_step_binary_primitive. Qed.

Lemma reducible_primitive_Div:
  forall ρ t1 t2,
    valid_interpretation ρ ->
    [ ρ ⊨ t1 : T_nat ] ->
    [ ρ ⊨ t2 : T_nat ] ->
    [ binary_primitive Gt t2 zero ≡ ttrue] ->
    [ ρ ⊨ binary_primitive Div t1 t2 : T_nat ].
Proof.
  reducible_primitive reducible_values_primitive_Div.
  eapply equivalent_trans; eauto.
  apply equivalent_sym, equivalent_star; eauto with cbvlemmas smallstep wf fv; t_closer.
Qed.

Lemma open_reducible_primitive_Div:
  forall Θ Γ t1 t2,
    [Θ; Γ ⊨ t1 : T_nat] ->
    [Θ; Γ ⊨ t2 : T_nat] ->
    [Θ; Γ ⊨ binary_primitive Gt t2 zero ≡ ttrue ] ->
    [Θ; Γ ⊨ binary_primitive Div t1 t2 : T_nat].
Proof. unfold open_reducible, open_equivalent; steps ; eauto using reducible_primitive_Div. Qed.

(* Lt *)

Lemma reducible_values_primitive_Lt:
  forall ρ v1 v2,
    [ ρ ⊨ v1 : T_nat ]v ->
    [ ρ ⊨ v2 : T_nat ]v ->
    [ ρ ⊨ binary_primitive Lt v1 v2 : T_bool ].
Proof. reducible_values_primitive. steps. Qed.

Lemma reducible_primitive_Lt:
  forall ρ t1 t2,
    valid_interpretation ρ ->
    [ ρ ⊨ t1 : T_nat ] ->
    [ ρ ⊨ t2 : T_nat ] ->
    [ ρ ⊨ binary_primitive Lt t1 t2 : T_bool ].
Proof. reducible_primitive reducible_values_primitive_Lt. Qed.

Lemma open_reducible_primitive_Lt:
  forall Θ Γ t1 t2,
    [Θ; Γ ⊨ t1 : T_nat] ->
    [Θ; Γ ⊨ t2 : T_nat] ->
    [Θ; Γ ⊨ binary_primitive Lt t1 t2 : T_bool].
Proof. unfold open_reducible; steps ; eauto using reducible_primitive_Lt. Qed.

(* Leq *)

Lemma reducible_values_primitive_Leq:
  forall ρ v1 v2,
    [ ρ ⊨ v1 : T_nat ]v ->
    [ ρ ⊨ v2 : T_nat ]v ->
    [ ρ ⊨ binary_primitive Leq v1 v2 : T_bool ].
Proof. reducible_values_primitive. steps. Qed.

Lemma reducible_primitive_Leq:
  forall ρ t1 t2,
    valid_interpretation ρ ->
    [ ρ ⊨ t1 : T_nat ] ->
    [ ρ ⊨ t2 : T_nat ] ->
    [ ρ ⊨ binary_primitive Leq t1 t2 : T_bool ].
Proof. reducible_primitive reducible_values_primitive_Leq. Qed.

Lemma open_reducible_primitive_Leq:
  forall Θ Γ t1 t2,
    [Θ; Γ ⊨ t1 : T_nat] ->
    [Θ; Γ ⊨ t2 : T_nat] ->
    [Θ; Γ ⊨ binary_primitive Leq t1 t2 : T_bool].
Proof. unfold open_reducible; steps ; eauto using reducible_primitive_Leq. Qed.

(* Gt *)

Lemma reducible_values_primitive_Gt:
  forall ρ v1 v2,
    [ ρ ⊨ v1 : T_nat ]v ->
    [ ρ ⊨ v2 : T_nat ]v ->
    [ ρ ⊨ binary_primitive Gt v1 v2 : T_bool ].
Proof. reducible_values_primitive. steps. Qed.

Lemma reducible_primitive_Gt:
  forall ρ t1 t2,
    valid_interpretation ρ ->
    [ ρ ⊨ t1 : T_nat ] ->
    [ ρ ⊨ t2 : T_nat ] ->
    [ ρ ⊨ binary_primitive Gt t1 t2 : T_bool ].
Proof. reducible_primitive reducible_values_primitive_Gt. Qed.

Lemma open_reducible_primitive_Gt:
  forall Θ Γ t1 t2,
    [Θ; Γ ⊨ t1 : T_nat] ->
    [Θ; Γ ⊨ t2 : T_nat] ->
    [Θ; Γ ⊨ binary_primitive Gt t1 t2 : T_bool].
Proof. unfold open_reducible; steps ; eauto using reducible_primitive_Gt. Qed.

(* Geq *)

Lemma reducible_values_primitive_Geq:
  forall ρ v1 v2,
    [ ρ ⊨ v1 : T_nat ]v ->
    [ ρ ⊨ v2 : T_nat ]v ->
    [ ρ ⊨ binary_primitive Geq v1 v2 : T_bool ].
Proof. reducible_values_primitive. steps. Qed.

Lemma reducible_primitive_Geq:
  forall ρ t1 t2,
    valid_interpretation ρ ->
    [ ρ ⊨ t1 : T_nat ] ->
    [ ρ ⊨ t2 : T_nat ] ->
    [ ρ ⊨ binary_primitive Geq t1 t2 : T_bool ].
Proof. reducible_primitive reducible_values_primitive_Geq. Qed.

Lemma open_reducible_primitive_Geq:
  forall Θ Γ t1 t2,
    [Θ; Γ ⊨ t1 : T_nat] ->
    [Θ; Γ ⊨ t2 : T_nat] ->
    [Θ; Γ ⊨ binary_primitive Geq t1 t2 : T_bool].
Proof. unfold open_reducible; steps ; eauto using reducible_primitive_Geq. Qed.

(* Eq *)

Lemma reducible_values_primitive_Eq:
  forall ρ v1 v2,
    [ ρ ⊨ v1 : T_nat ]v ->
    [ ρ ⊨ v2 : T_nat ]v ->
    [ ρ ⊨ binary_primitive Eq v1 v2 : T_bool ].
Proof. reducible_values_primitive. steps. Qed.

Lemma reducible_primitive_Eq:
  forall ρ t1 t2,
    valid_interpretation ρ ->
    [ ρ ⊨ t1 : T_nat ] ->
    [ ρ ⊨ t2 : T_nat ] ->
    [ ρ ⊨ binary_primitive Eq t1 t2 : T_bool ].
Proof. reducible_primitive reducible_values_primitive_Eq. Qed.

Lemma open_reducible_primitive_Eq:
  forall Θ Γ t1 t2,
    [Θ; Γ ⊨ t1 : T_nat] ->
    [Θ; Γ ⊨ t2 : T_nat] ->
    [Θ; Γ ⊨ binary_primitive Eq t1 t2 : T_bool].
Proof. unfold open_reducible; steps ; eauto using reducible_primitive_Eq. Qed.

(* Neq *)

Lemma reducible_values_primitive_Neq:
  forall ρ v1 v2,
    [ ρ ⊨ v1 : T_nat ]v ->
    [ ρ ⊨ v2 : T_nat ]v ->
    [ ρ ⊨ binary_primitive Neq v1 v2 : T_bool ].
Proof. reducible_values_primitive. steps. Qed.

Lemma reducible_primitive_Neq:
  forall ρ t1 t2,
    valid_interpretation ρ ->
    [ ρ ⊨ t1 : T_nat ] ->
    [ ρ ⊨ t2 : T_nat ] ->
    [ ρ ⊨ binary_primitive Neq t1 t2 : T_bool ].
Proof. reducible_primitive reducible_values_primitive_Neq. Qed.

Lemma open_reducible_primitive_Neq:
  forall Θ Γ t1 t2,
    [Θ; Γ ⊨ t1 : T_nat] ->
    [Θ; Γ ⊨ t2 : T_nat] ->
    [Θ; Γ ⊨ binary_primitive Neq t1 t2 : T_bool].
Proof. unfold open_reducible; steps ; eauto using reducible_primitive_Neq. Qed.

(* And *)

Lemma reducible_values_primitive_And:
  forall ρ v1 v2,
    [ ρ ⊨ v1 : T_bool ]v ->
    [ ρ ⊨ v2 : T_bool ]v ->
    [ ρ ⊨ binary_primitive And v1 v2 : T_bool ].
Proof. reducible_values_primitive. Qed.

Lemma reducible_primitive_And:
  forall ρ t1 t2,
    valid_interpretation ρ ->
    [ ρ ⊨ t1 : T_bool ] ->
    [ ρ ⊨ t2 : T_bool ] ->
    [ ρ ⊨ binary_primitive And t1 t2 : T_bool ].
Proof. reducible_primitive reducible_values_primitive_And. Qed.

Lemma open_reducible_primitive_And:
  forall Θ Γ t1 t2,
    [Θ; Γ ⊨ t1 : T_bool] ->
    [Θ; Γ ⊨ t2 : T_bool] ->
    [Θ; Γ ⊨ binary_primitive And t1 t2 : T_bool].
Proof. unfold open_reducible; steps ; eauto using reducible_primitive_And. Qed.

(* Or *)

Lemma reducible_values_primitive_Or:
  forall ρ v1 v2,
    [ ρ ⊨ v1 : T_bool ]v ->
    [ ρ ⊨ v2 : T_bool ]v ->
    [ ρ ⊨ binary_primitive Or v1 v2 : T_bool ].
Proof. reducible_values_primitive. Qed.

Lemma reducible_primitive_Or:
  forall ρ t1 t2,
    valid_interpretation ρ ->
    [ ρ ⊨ t1 : T_bool ] ->
    [ ρ ⊨ t2 : T_bool ] ->
    [ ρ ⊨ binary_primitive Or t1 t2 : T_bool ].
Proof. reducible_primitive reducible_values_primitive_Or. Qed.

Lemma open_reducible_primitive_Or:
  forall Θ Γ t1 t2,
    [Θ; Γ ⊨ t1 : T_bool] ->
    [Θ; Γ ⊨ t2 : T_bool] ->
    [Θ; Γ ⊨ binary_primitive Or t1 t2 : T_bool].
Proof. unfold open_reducible; steps ; eauto using reducible_primitive_Or. Qed.


Hint Resolve open_reducible_primitive_And: primitives.
Hint Resolve open_reducible_primitive_Div: primitives.
Hint Resolve open_reducible_primitive_Eq: primitives.
Hint Resolve open_reducible_primitive_Geq: primitives.
Hint Resolve open_reducible_primitive_Gt: primitives.
Hint Resolve open_reducible_primitive_Leq: primitives.
Hint Resolve open_reducible_primitive_Lt: primitives.
Hint Resolve open_reducible_primitive_Minus: primitives.
Hint Resolve open_reducible_primitive_Mul: primitives.
Hint Resolve open_reducible_primitive_Neq: primitives.
Hint Resolve open_reducible_primitive_Or: primitives.
Hint Resolve open_reducible_primitive_Plus: primitives.
Hint Resolve open_reducible_primitive_Not: primitives.
