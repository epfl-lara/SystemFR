From Stdlib Require Import String.
From Stdlib Require Import List.

Require Export SystemFR.RedTactics.

Opaque reducible_values.

Lemma in_satisfies_left_right:
  forall Γ1 Γ2 S l1 l2 P z,
    satisfies P (Γ1 ++ Γ2) (l1 ++ l2) ->
    subset S (support Γ2) ->
    z ∈ support Γ1 ->
    z ∈ S ->
    False.
Proof.
  repeat step || t_satisfies_nodup || rewrite support_append in * || list_utils ||
         apply_anywhere NoDup_append;
    eauto using NoDup_append with sets.
Qed.

Lemma satisfies_insert_nat_succ:
  forall ρ Γ1 Γ2 b x y l1 l2 v,
    satisfies (reducible_values ρ) (Γ1 ++ Γ2) (l1 ++ l2) ->
    satisfies (reducible_values ρ) Γ2 l2 ->
    psubstitute b l2 term_var ~>* succ v ->
    support Γ1 = support l1 ->
    support Γ2 = support l2 ->
    closed_term (psubstitute b l2 term_var) ->
    subset (pfv b term_var) (support Γ2) ->
    ~(x ∈ pfv b term_var) ->
    ~(x ∈ pfv_context Γ1 term_var) ->
    ~(x ∈ pfv_context Γ2 term_var) ->
    ~(y ∈ pfv b term_var) ->
    ~(y ∈ pfv_context Γ1 term_var) ->
    ~(y ∈ pfv_context Γ2 term_var) ->
    ~(x = y) ->
    is_nat_value v ->
    satisfies (reducible_values ρ)
              (Γ1 ++ (x, T_equiv b (succ (fvar y term_var))) :: (y, T_nat) :: Γ2)
              (l1 ++ (x, uu) :: (y, v) :: l2).
Proof.
  repeat step || apply satisfies_insert || list_utils || simp_red || t_substitutions;
    try solve [ apply equivalent_star; t_closer ];
    eauto 2 with fv wf twf;
    eauto 2 using in_satisfies_left_right.
Qed.

Lemma satisfies_cons_nat_succ:
  forall ρ Γ b x y l v,
    satisfies (reducible_values ρ) Γ l ->
    psubstitute b l term_var ~>* succ v ->
    closed_term (psubstitute b l term_var) ->
    ~(x ∈ pfv b term_var) ->
    ~(x ∈ pfv_context Γ term_var) ->
    ~(y ∈ pfv b term_var) ->
    ~(y ∈ pfv_context Γ term_var) ->
    ~(x = y) ->
    is_nat_value v ->
    satisfies (reducible_values ρ)
              ((x, T_equiv b (succ (fvar y term_var))) :: (y, T_nat) :: Γ)
              ((x, uu) :: (y, v) :: l).
Proof.
  repeat step || apply SatCons || list_utils || simp_red || t_substitutions;
    try solve [ apply equivalent_star; t_closer ];
    eauto 2 with fv wf twf;
    eauto 2 using in_satisfies_left_right.
Qed.

Lemma satisfies_insert2:
  forall ρ Γ1 Γ2 b x l1 l2 t,
    satisfies (reducible_values ρ) (Γ1 ++ Γ2) (l1 ++ l2) ->
    satisfies (reducible_values ρ) Γ2 l2 ->
    psubstitute b l2 term_var ~>* t ->
    support Γ1 = support l1 ->
    support Γ2 = support l2 ->
    closed_term (psubstitute b l2 term_var) ->
    subset (pfv b term_var) (support Γ2) ->
    ~(x ∈ pfv b term_var) ->
    ~(x ∈ pfv_context Γ1 term_var) ->
    ~(x ∈ pfv_context Γ2 term_var) ->
    closed_term t ->
    satisfies (reducible_values ρ) (Γ1 ++ (x, T_equiv b t) :: Γ2)
              (l1 ++ (x, uu) :: l2).
Proof.
  repeat step || apply satisfies_insert || list_utils || simp_red || t_substitutions ||
         rewrite (substitute_nothing5 t) by t_closer;
    try solve [ equivalent_star ];
    t_closer;
    eauto 2 using in_satisfies_left_right.
Qed.

Lemma satisfies_insert3:
  forall ρ Γ b x l t,
    satisfies (reducible_values ρ) Γ l ->
    psubstitute b l term_var ~>* t ->
    closed_term (psubstitute b l term_var) ->
    ~(x ∈ pfv b term_var) ->
    ~(x ∈ pfv_context Γ term_var) ->
    closed_term t ->
    satisfies (reducible_values ρ)
              ((x, T_equiv b t) :: Γ)
              ((x, uu) :: l).
Proof.
  repeat step || apply SatCons || list_utils || simp_red || t_substitutions ||
         rewrite (substitute_nothing5 t) by t_closer;
    try solve [ equivalent_star ];
    t_closer;
    eauto 2 using in_satisfies_left_right.
Qed.
