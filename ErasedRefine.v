Require Import Equations.Equations.

Require Import Coq.Arith.PeanoNat.
Require Import Coq.Lists.List.

Require Export SystemFR.ErasedLet2.

Opaque reducible_values.
Opaque makeFresh.

Lemma reducible_refine:
  forall ρ t A b,
    [ ρ ⊨ t : A ] ->
    wf b 1 ->
    wf t 0 ->
    valid_interpretation ρ ->
    is_erased_term b ->
    fv b = nil ->
    (forall v,
      [ ρ ⊨ v : A ]v ->
      [ t ≡ v ] ->
      [ open 0 b v ≡ ttrue ]) ->
    [ ρ ⊨ t : T_refine A b ].
Proof.
  unfold reduces_to in *; repeat step;
    eauto with wf; eauto with fv.

  eexists; steps; eauto.
  repeat step || simp_red || apply equivalent_true || apply_any || apply equivalent_star;
    t_closer.
Qed.

Lemma open_reducible_refine:
  forall Θ Γ t A b x p,
    wf b 1 ->
    wf t 0 ->
    subset (fv t) (support Γ) ->
    ~(p ∈ fv b) ->
    ~(p ∈ fv t) ->
    ~(p ∈ fv A) ->
    ~(p ∈ fv_context Γ) ->
    ~(x ∈ fv b) ->
    ~(x ∈ fv A) ->
    ~(x ∈ fv_context Γ) ->
    ~(x = p) ->
    is_erased_term b ->
    subset (fv b) (support Γ) ->
    (forall ρ l,
        valid_interpretation ρ ->
        support ρ = Θ ->
        satisfies (reducible_values ρ) ((p,T_equiv (fvar x term_var) t) :: (x, A) :: Γ) l ->
        [ substitute (open 0 b (fvar x term_var)) l ≡ ttrue ]) ->
    [ Θ; Γ ⊨ t : A ] ->
    [ Θ; Γ ⊨ t : T_refine A b ].
Proof.
  unfold open_reducible; repeat step || t_instantiate_sat3.

  apply reducible_refine; steps; t_closer.

  unshelve epose proof (H12 ρ ((p, uu) :: (x,v) :: lterms) _ _ _);
    repeat step || apply SatCons || list_utils || t_substitutions || simp_red;
    eauto using equivalent_sym;
    eauto with fv wf twf.
Qed.

Lemma subtype_refine:
  forall ρ (Γ : context) A B p q (x : nat) t l,
    wf q 1 ->
    is_erased_term q ->
    ~(x ∈ fv_context Γ) ->
    ~(x ∈ fv A) ->
    ~(x ∈ fv p) ->
    ~(x ∈ fv q) ->
    subset (fv q) (support Γ) ->
    valid_interpretation ρ ->
    (forall l,
        satisfies (reducible_values ρ) ((x, T_refine A p) :: Γ) l ->
        [ substitute (open 0 q (fvar x term_var)) l ≡ ttrue ]) ->
    (forall t l,
        satisfies (reducible_values ρ) Γ l ->
        [ ρ ⊨ t : substitute A l ]v -> [ ρ ⊨ t : substitute B l ]v) ->
    satisfies (reducible_values ρ) Γ l ->
    reducible_values ρ t (T_refine (substitute A l) (substitute p l)) ->
    reducible_values ρ t (T_refine (substitute B l) (substitute q l)).
Proof.
  repeat step || simp_red || unshelve eauto with wf erased fv.

  unshelve epose proof (H7 ((x,t) :: l) _);
    repeat step || apply SatCons || list_utils || t_substitutions || simp_red;
    eauto using equivalent_true;
    eauto with fv wf twf.
Qed.

Lemma subtype_refine4:
  forall ρ (Γ : context) T A p (x : nat) t l,
    ~(x ∈ fv_context Γ) ->
    ~(x ∈ fv T) ->
    ~(x ∈ fv p) ->
    is_erased_term p ->
    wf p 1 ->
    subset (fv p) (support Γ) ->
    valid_interpretation ρ ->
    (forall l,
        satisfies (reducible_values ρ) ((x, T) :: Γ) l ->
        [ substitute (open 0 p (fvar x term_var)) l ≡ ttrue ]) ->
    (forall t l,
        satisfies (reducible_values ρ) Γ l ->
        [ ρ ⊨ t : substitute T l ]v -> [ ρ ⊨ t : substitute A l ]v) ->
      satisfies (reducible_values ρ) Γ l ->
      [ ρ ⊨ t : substitute T l ]v ->
      reducible_values ρ t (T_refine (substitute A l) (substitute p l)).
Proof.
  repeat step || simp_red || unshelve t_closer.

  unshelve epose proof (H6 ((x,t) :: l) _);
    repeat step || apply SatCons || list_utils || t_substitutions || simp_red;
    eauto using equivalent_true;
    eauto with fv wf twf.
Qed.

Lemma subtype_refine5:
  forall ρ Γ T A b (x p : nat) t l,
    ~(p ∈ fv_context Γ) ->
    ~(p ∈ fv A) ->
    ~(p ∈ fv T) ->
    ~(p ∈ fv b) ->
    ~(x ∈ fv_context Γ) ->
    ~(x ∈ fv A) ->
    ~(x ∈ fv T) ->
    ~(x ∈ fv b) ->
    ~(x = p) ->
    [ support ρ; (p, T_equiv (open 0 b (fvar x term_var)) ttrue) :: (x, A) :: Γ ⊨
        fvar x term_var : T ] ->
    valid_interpretation ρ ->
    satisfies (reducible_values ρ) Γ l ->
    reducible_values ρ t (T_refine (substitute A l) (substitute b l)) ->
    [ ρ ⊨ t : substitute T l ]v.
Proof.
  unfold open_reducible; repeat step || simp_red; eauto with wf.

  unshelve epose proof (H8 ρ ((p, uu) :: (x,t) :: l) _ _ _);
    repeat step || apply SatCons || list_utils || t_substitutions || simp_red || fv_open;
    eauto with fv wf twf;
    eauto using red_is_val, reducible_expr_value;
    try solve [ equivalent_star ].
Qed.
