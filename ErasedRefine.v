Require Import Equations.Equations.

Require Import Coq.Arith.PeanoNat.
Require Import Coq.Lists.List.

Require Export SystemFR.ErasedLet2.
Require Export SystemFR.NatCompare.

Opaque reducible_values.
Opaque makeFresh.

Lemma reducible_refine:
  forall theta t A b,
    reducible theta t A ->
    wf b 1 ->
    wf t 0 ->
    valid_interpretation theta ->
    is_erased_term b ->
    fv b = nil ->
    (forall v,
        reducible_values theta v A ->
        equivalent_terms t v ->
        equivalent_terms (open 0 b v) ttrue) ->
    reducible theta t (T_refine A b).
Proof.
  unfold reducible, reduces_to in *; repeat step;
    eauto with wf; eauto with fv.

  eexists; steps; eauto.
  repeat step || simp_red || apply equivalent_true || apply_any || apply equivalent_star;
    t_closer.
Qed.

Lemma open_reducible_refine:
  forall tvars gamma t A b x p,
    wf b 1 ->
    wf t 0 ->
    subset (fv t) (support gamma) ->
    ~(p ∈ fv b) ->
    ~(p ∈ fv t) ->
    ~(p ∈ fv A) ->
    ~(p ∈ fv_context gamma) ->
    ~(x ∈ fv b) ->
    ~(x ∈ fv A) ->
    ~(x ∈ fv_context gamma) ->
    ~(x = p) ->
    is_erased_term b ->
    subset (fv b) (support gamma) ->
    (forall theta l,
        valid_interpretation theta ->
        support theta = tvars ->
        satisfies (reducible_values theta) ((p,T_equiv (fvar x term_var) t) :: (x, A) :: gamma) l ->
        equivalent_terms (substitute (open 0 b (fvar x term_var)) l) ttrue) ->
    [ tvars; gamma ⊨ t : A ] ->
    [ tvars; gamma ⊨ t : T_refine A b ].
Proof.
  unfold open_reducible; repeat step || t_instantiate_sat3.

  apply reducible_refine; steps; t_closer.

  unshelve epose proof (H12 theta ((p, uu) :: (x,v) :: lterms) _ _ _);
    repeat step || apply SatCons || list_utils || t_substitutions || simp_red;
    eauto using equivalent_sym;
    eauto with fv wf twf.
Qed.

Lemma subtype_refine:
  forall theta (gamma : context) A B p q (x : nat) t l,
    wf q 1 ->
    is_erased_term q ->
    ~(x ∈ fv_context gamma) ->
    ~(x ∈ fv A) ->
    ~(x ∈ fv p) ->
    ~(x ∈ fv q) ->
    subset (fv q) (support gamma) ->
    valid_interpretation theta ->
    (forall l,
        satisfies (reducible_values theta) ((x, T_refine A p) :: gamma) l ->
        equivalent_terms (substitute (open 0 q (fvar x term_var)) l) ttrue) ->
    (forall t l,
        satisfies (reducible_values theta) gamma l ->
        reducible_values theta t (substitute A l) -> reducible_values theta t (substitute B l)) ->
    satisfies (reducible_values theta) gamma l ->
    reducible_values theta t (T_refine (substitute A l) (substitute p l)) ->
    reducible_values theta t (T_refine (substitute B l) (substitute q l)).
Proof.
  repeat step || simp_red || unshelve eauto with wf erased fv.

  unshelve epose proof (H7 ((x,t) :: l) _);
    repeat step || apply SatCons || list_utils || t_substitutions || simp_red;
    eauto using equivalent_true;
    eauto with fv wf twf.
Qed.

Lemma subtype_refine4:
  forall theta (gamma : context) T A p (x : nat) t l,
    ~(x ∈ fv_context gamma) ->
    ~(x ∈ fv T) ->
    ~(x ∈ fv p) ->
    is_erased_term p ->
    wf p 1 ->
    subset (fv p) (support gamma) ->
    valid_interpretation theta ->
    (forall l,
        satisfies (reducible_values theta) ((x, T) :: gamma) l ->
        equivalent_terms (substitute (open 0 p (fvar x term_var)) l) ttrue) ->
    (forall t l,
        satisfies (reducible_values theta) gamma l ->
        reducible_values theta t (substitute T l) -> reducible_values theta t (substitute A l)) ->
      satisfies (reducible_values theta) gamma l ->
      reducible_values theta t (substitute T l) ->
      reducible_values theta t (T_refine (substitute A l) (substitute p l)).
Proof.
  repeat step || simp_red || unshelve t_closer.

  unshelve epose proof (H6 ((x,t) :: l) _);
    repeat step || apply SatCons || list_utils || t_substitutions || simp_red;
    eauto using equivalent_true;
    eauto with fv wf twf.
Qed.

Lemma subtype_refine5:
  forall theta gamma T A b (x p : nat) t l,
    ~(p ∈ fv_context gamma) ->
    ~(p ∈ fv A) ->
    ~(p ∈ fv T) ->
    ~(p ∈ fv b) ->
    ~(x ∈ fv_context gamma) ->
    ~(x ∈ fv A) ->
    ~(x ∈ fv T) ->
    ~(x ∈ fv b) ->
    ~(x = p) ->
    [ support theta; (p, T_equiv (open 0 b (fvar x term_var)) ttrue) :: (x, A) :: gamma ⊨
        fvar x term_var : T ] ->
    valid_interpretation theta ->
    satisfies (reducible_values theta) gamma l ->
    reducible_values theta t (T_refine (substitute A l) (substitute b l)) ->
    reducible_values theta t (substitute T l).
Proof.
  unfold open_reducible; repeat step || simp_red; eauto with wf.

  unshelve epose proof (H8 theta ((p, uu) :: (x,t) :: l) _ _ _);
    repeat step || apply SatCons || list_utils || t_substitutions || simp_red || fv_open;
    eauto with fv wf twf;
    eauto using red_is_val, reducible_expr_value;
    try solve [ equivalent_star ].
Qed.
