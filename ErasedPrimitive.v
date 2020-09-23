Require Export SystemFR.ReducibilityOpenEquivalent.

Opaque reducible_values.
Opaque makeFresh.

Ltac reducible_values_primitive :=
  unfold reduces_to, closed_term ;
    repeat step || simp_red || is_nat_value_buildable ; t_closer ;
      eexists; split; [ idtac | (apply star_one; constructor; try reflexivity ) ];
      eauto using is_nat_value_build_nat.
Ltac reducible_primitive f :=
  intros;
  repeat top_level_unfold reduces_to || steps || simp_red || is_nat_value_buildable;
  eapply star_backstep_reducible;
    try apply star_smallstep_binary_primitive; eauto ;
    repeat steps || list_utils || simp_red || apply f || eauto with values cbvlemmas ; t_closer.

Hint Rewrite PeanoNat.Nat.leb_le: primitives.
Hint Rewrite PeanoNat.Nat.leb_gt: primitives.
Hint Rewrite PeanoNat.Nat.ltb_lt: primitives.
Hint Rewrite PeanoNat.Nat.ltb_ge: primitives.

Ltac equivalent_binary_primitive :=
  lazymatch goal with
  | H: binary_primitive ?o ?v1 ?v2 ~>* ?v |- _ =>
    cbv_value v1 ; cbv_value v2 ;
      inversion H; clear H; t_invert_step ;
        try solve [exfalso; eauto with smallstep values ] ;
        repeat build_nat_inj || subst ;
        destruct_match; star_smallstep_value; try discriminate; eauto with values ;
        repeat autorewrite with primitives in *
  end.


(* Plus *)

Lemma reducible_values_primitive_plus:
  forall ρ v1 v2,
    [ ρ ⊨ v1 : T_nat ]v ->
    [ ρ ⊨ v2 : T_nat ]v ->
    [ ρ ⊨ binary_primitive Plus v1 v2 : T_nat ].
Proof. reducible_values_primitive. Qed.

Lemma reducible_primitive_plus:
  forall ρ t1 t2,
    valid_interpretation ρ ->
    [ ρ ⊨ t1 : T_nat ] ->
    [ ρ ⊨ t2 : T_nat ] ->
    [ ρ ⊨ binary_primitive Plus t1 t2 : T_nat ].
Proof. reducible_primitive reducible_values_primitive_plus. Qed.

Lemma open_reducible_primitive_plus:
  forall Θ Γ t1 t2,
    [Θ; Γ ⊨ t1 : T_nat] ->
    [Θ; Γ ⊨ t2 : T_nat] ->
    [Θ; Γ ⊨ binary_primitive Plus t1 t2 : T_nat].
Proof. unfold open_reducible; steps ; eauto using reducible_primitive_plus. Qed.

(* Minus *)

Lemma reducible_values_primitive_minus:
  forall ρ v1 v2,
    [ ρ ⊨ v1 : T_nat ]v ->
    [ ρ ⊨ v2 : T_nat ]v ->
    [ binary_primitive Geq v1 v2 ≡ ttrue ] ->
    [ ρ ⊨ binary_primitive Minus v1 v2 : T_nat ].
Proof. reducible_values_primitive. apply_anywhere equivalent_true. equivalent_binary_primitive. steps. Qed.

Lemma reducible_primitive_minus:
  forall ρ t1 t2,
    valid_interpretation ρ ->
    [ ρ ⊨ t1 : T_nat ] ->
    [ ρ ⊨ t2 : T_nat ] ->
    [ binary_primitive Geq t1 t2 ≡ ttrue ] ->
    [ ρ ⊨ binary_primitive Minus t1 t2 : T_nat ].
Proof. reducible_primitive reducible_values_primitive_minus.
       eapply equivalent_trans; eauto.
       apply equivalent_sym, equivalent_star; eauto with cbvlemmas smallstep wf fv; t_closer.
       apply star_smallstep_binary_primitive; eauto with values.
Qed.

Lemma open_reducible_primitive_minus:
  forall Θ Γ t1 t2,
    [Θ; Γ ⊨ t1 : T_nat] ->
    [Θ; Γ ⊨ t2 : T_nat] ->
    [Θ; Γ ⊨ binary_primitive Geq t1 t2 ≡ ttrue ] ->
    [Θ; Γ ⊨ binary_primitive Minus t1 t2 : T_nat].
Proof. unfold open_reducible, open_equivalent; steps;
         eauto using reducible_primitive_minus.
Qed.

(* Mul *)

Lemma reducible_values_primitive_mul:
  forall ρ v1 v2,
    [ ρ ⊨ v1 : T_nat ]v ->
    [ ρ ⊨ v2 : T_nat ]v ->
    [ ρ ⊨ binary_primitive Mul v1 v2 : T_nat ].
Proof. reducible_values_primitive. Qed.

Lemma reducible_primitive_mul:
  forall ρ t1 t2,
    valid_interpretation ρ ->
    [ ρ ⊨ t1 : T_nat ] ->
    [ ρ ⊨ t2 : T_nat ] ->
    [ ρ ⊨ binary_primitive Mul t1 t2 : T_nat ].
Proof. reducible_primitive reducible_values_primitive_mul. Qed.

Lemma open_reducible_primitive_mul:
  forall Θ Γ t1 t2,
    [Θ; Γ ⊨ t1 : T_nat] ->
    [Θ; Γ ⊨ t2 : T_nat] ->
    [Θ; Γ ⊨ binary_primitive Mul t1 t2 : T_nat].
Proof. unfold open_reducible; steps ; eauto using reducible_primitive_mul. Qed.

(* Div *)

Lemma reducible_values_primitive_div:
  forall ρ v1 v2 ,
    [ ρ ⊨ v1 : T_nat ]v ->
    [ ρ ⊨ v2 : T_nat ]v ->
    [ binary_primitive Gt v2 zero ≡ ttrue] ->
    [ ρ ⊨ binary_primitive Div v1 v2 : T_nat ].
Proof. reducible_values_primitive. apply_anywhere equivalent_true. equivalent_binary_primitive. steps. Qed.

Lemma reducible_primitive_div:
  forall ρ t1 t2,
    valid_interpretation ρ ->
    [ ρ ⊨ t1 : T_nat ] ->
    [ ρ ⊨ t2 : T_nat ] ->
    [ binary_primitive Gt t2 zero ≡ ttrue] ->
    [ ρ ⊨ binary_primitive Div t1 t2 : T_nat ].
Proof.
  reducible_primitive reducible_values_primitive_div.
  eapply equivalent_trans; eauto.
  apply equivalent_sym, equivalent_star; eauto with cbvlemmas smallstep wf fv; t_closer.
Qed.

Lemma open_reducible_primitive_div:
  forall Θ Γ t1 t2,
    [Θ; Γ ⊨ t1 : T_nat] ->
    [Θ; Γ ⊨ t2 : T_nat] ->
    [Θ; Γ ⊨ binary_primitive Gt t2 zero ≡ ttrue ] ->
    [Θ; Γ ⊨ binary_primitive Div t1 t2 : T_nat].
Proof. unfold open_reducible, open_equivalent; steps ; eauto using reducible_primitive_div. Qed.

(* Lt *)

Lemma reducible_values_primitive_lt:
  forall ρ v1 v2,
    [ ρ ⊨ v1 : T_nat ]v ->
    [ ρ ⊨ v2 : T_nat ]v ->
    [ ρ ⊨ binary_primitive Lt v1 v2 : T_bool ].
Proof. reducible_values_primitive. steps. Qed.

Lemma reducible_primitive_lt:
  forall ρ t1 t2,
    valid_interpretation ρ ->
    [ ρ ⊨ t1 : T_nat ] ->
    [ ρ ⊨ t2 : T_nat ] ->
    [ ρ ⊨ binary_primitive Lt t1 t2 : T_bool ].
Proof. reducible_primitive reducible_values_primitive_lt. Qed.

Lemma open_reducible_primitive_lt:
  forall Θ Γ t1 t2,
    [Θ; Γ ⊨ t1 : T_nat] ->
    [Θ; Γ ⊨ t2 : T_nat] ->
    [Θ; Γ ⊨ binary_primitive Lt t1 t2 : T_bool].
Proof. unfold open_reducible; steps ; eauto using reducible_primitive_lt. Qed.

(* Leq *)

Lemma reducible_values_primitive_leq:
  forall ρ v1 v2,
    [ ρ ⊨ v1 : T_nat ]v ->
    [ ρ ⊨ v2 : T_nat ]v ->
    [ ρ ⊨ binary_primitive Leq v1 v2 : T_bool ].
Proof. reducible_values_primitive. steps. Qed.

Lemma reducible_primitive_leq:
  forall ρ t1 t2,
    valid_interpretation ρ ->
    [ ρ ⊨ t1 : T_nat ] ->
    [ ρ ⊨ t2 : T_nat ] ->
    [ ρ ⊨ binary_primitive Leq t1 t2 : T_bool ].
Proof. reducible_primitive reducible_values_primitive_leq. Qed.

Lemma open_reducible_primitive_leq:
  forall Θ Γ t1 t2,
    [Θ; Γ ⊨ t1 : T_nat] ->
    [Θ; Γ ⊨ t2 : T_nat] ->
    [Θ; Γ ⊨ binary_primitive Leq t1 t2 : T_bool].
Proof. unfold open_reducible; steps ; eauto using reducible_primitive_leq. Qed.

(* Gt *)

Lemma reducible_values_primitive_gt:
  forall ρ v1 v2,
    [ ρ ⊨ v1 : T_nat ]v ->
    [ ρ ⊨ v2 : T_nat ]v ->
    [ ρ ⊨ binary_primitive Gt v1 v2 : T_bool ].
Proof. reducible_values_primitive. steps. Qed.

Lemma reducible_primitive_gt:
  forall ρ t1 t2,
    valid_interpretation ρ ->
    [ ρ ⊨ t1 : T_nat ] ->
    [ ρ ⊨ t2 : T_nat ] ->
    [ ρ ⊨ binary_primitive Gt t1 t2 : T_bool ].
Proof. reducible_primitive reducible_values_primitive_gt. Qed.

Lemma open_reducible_primitive_gt:
  forall Θ Γ t1 t2,
    [Θ; Γ ⊨ t1 : T_nat] ->
    [Θ; Γ ⊨ t2 : T_nat] ->
    [Θ; Γ ⊨ binary_primitive Gt t1 t2 : T_bool].
Proof. unfold open_reducible; steps ; eauto using reducible_primitive_gt. Qed.

(* Geq *)

Lemma reducible_values_primitive_geq:
  forall ρ v1 v2,
    [ ρ ⊨ v1 : T_nat ]v ->
    [ ρ ⊨ v2 : T_nat ]v ->
    [ ρ ⊨ binary_primitive Geq v1 v2 : T_bool ].
Proof. reducible_values_primitive. steps. Qed.

Lemma reducible_primitive_geq:
  forall ρ t1 t2,
    valid_interpretation ρ ->
    [ ρ ⊨ t1 : T_nat ] ->
    [ ρ ⊨ t2 : T_nat ] ->
    [ ρ ⊨ binary_primitive Geq t1 t2 : T_bool ].
Proof. reducible_primitive reducible_values_primitive_geq. Qed.

Lemma open_reducible_primitive_geq:
  forall Θ Γ t1 t2,
    [Θ; Γ ⊨ t1 : T_nat] ->
    [Θ; Γ ⊨ t2 : T_nat] ->
    [Θ; Γ ⊨ binary_primitive Geq t1 t2 : T_bool].
Proof. unfold open_reducible; steps ; eauto using reducible_primitive_geq. Qed.

(* Eq *)

Lemma reducible_values_primitive_eq:
  forall ρ v1 v2,
    [ ρ ⊨ v1 : T_nat ]v ->
    [ ρ ⊨ v2 : T_nat ]v ->
    [ ρ ⊨ binary_primitive Eq v1 v2 : T_bool ].
Proof. reducible_values_primitive. steps. Qed.

Lemma reducible_primitive_eq:
  forall ρ t1 t2,
    valid_interpretation ρ ->
    [ ρ ⊨ t1 : T_nat ] ->
    [ ρ ⊨ t2 : T_nat ] ->
    [ ρ ⊨ binary_primitive Eq t1 t2 : T_bool ].
Proof. reducible_primitive reducible_values_primitive_eq. Qed.

Lemma open_reducible_primitive_eq:
  forall Θ Γ t1 t2,
    [Θ; Γ ⊨ t1 : T_nat] ->
    [Θ; Γ ⊨ t2 : T_nat] ->
    [Θ; Γ ⊨ binary_primitive Eq t1 t2 : T_bool].
Proof. unfold open_reducible; steps ; eauto using reducible_primitive_eq. Qed.

(* Neq *)

Lemma reducible_values_primitive_neq:
  forall ρ v1 v2,
    [ ρ ⊨ v1 : T_nat ]v ->
    [ ρ ⊨ v2 : T_nat ]v ->
    [ ρ ⊨ binary_primitive Neq v1 v2 : T_bool ].
Proof. reducible_values_primitive. steps. Qed.

Lemma reducible_primitive_neq:
  forall ρ t1 t2,
    valid_interpretation ρ ->
    [ ρ ⊨ t1 : T_nat ] ->
    [ ρ ⊨ t2 : T_nat ] ->
    [ ρ ⊨ binary_primitive Neq t1 t2 : T_bool ].
Proof. reducible_primitive reducible_values_primitive_neq. Qed.

Lemma open_reducible_primitive_neq:
  forall Θ Γ t1 t2,
    [Θ; Γ ⊨ t1 : T_nat] ->
    [Θ; Γ ⊨ t2 : T_nat] ->
    [Θ; Γ ⊨ binary_primitive Neq t1 t2 : T_bool].
Proof. unfold open_reducible; steps ; eauto using reducible_primitive_neq. Qed.
