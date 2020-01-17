Require Import Equations.Equations.

Require Import Coq.Arith.PeanoNat.
Require Import Coq.Lists.List.

Require Export SystemFR.ErasedLetTermRules.
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
    open_reducible tvars gamma t A ->
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
    (forall theta l,
        valid_interpretation theta ->
        support theta = tvars ->
        satisfies (reducible_values theta) ((p,T_equiv (term_fvar x) t) :: (x, A) :: gamma) l ->
        equivalent_terms (substitute (open 0 b (term_fvar x)) l) ttrue) ->
    open_reducible tvars gamma t (T_refine A b).
Proof.
  unfold open_reducible; repeat step || t_instantiate_sat3.

  apply reducible_refine; steps; t_closer.

  unshelve epose proof (H12 theta ((p, uu) :: (x,v) :: lterms) _ _ _); tac1;
    eauto using equivalent_sym.
Qed.

Lemma subtype_refine:
  forall tvars theta (gamma : context) A B p q (x : nat) t l,
    wf q 1 ->
    is_erased_term q ->
    ~(x ∈ fv_context gamma) ->
    ~(x ∈ fv A) ->
    ~(x ∈ fv p) ->
    ~(x ∈ fv q) ->
    valid_interpretation theta ->
    support theta = tvars ->
    (forall l,
        satisfies (reducible_values theta) ((x, T_refine A p) :: gamma) l ->
        equivalent_terms (substitute (open 0 q (term_fvar x)) l) ttrue) ->
    (forall t l,
        satisfies (reducible_values theta) gamma l ->
        reducible_values theta t (substitute A l) -> reducible_values theta t (substitute B l)) ->
    satisfies (reducible_values theta) gamma l ->
    reducible_values theta t (T_refine (substitute A l) (substitute p l)) ->
    reducible_values theta t (T_refine (substitute B l) (substitute q l)).
Proof.
  repeat step || simp_red; unshelve eauto with wf; eauto with erased.

  unshelve epose proof (H7 ((x,t) :: l) _); tac1;
    eauto using equivalent_true.
Qed.

Lemma subtype_refine4:
  forall theta (gamma : context) T A p (x : nat) t l,
    ~(x ∈ fv_context gamma) ->
    ~(x ∈ fv T) ->
    ~(x ∈ fv p) ->
    is_erased_term p ->
    wf p 1 ->
    valid_interpretation theta ->
    (forall l,
        satisfies (reducible_values theta) ((x, T) :: gamma) l ->
        equivalent_terms (substitute (open 0 p (term_fvar x)) l) ttrue) ->
    (forall t l,
        satisfies (reducible_values theta) gamma l ->
        reducible_values theta t (substitute T l) -> reducible_values theta t (substitute A l)) ->
      satisfies (reducible_values theta) gamma l ->
      reducible_values theta t (substitute T l) ->
      reducible_values theta t (T_refine (substitute A l) (substitute p l)).
Proof.
  repeat step || simp_red || unshelve t_closer.

  unshelve epose proof (H5 ((x,t) :: l) _); tac1;
    eauto using equivalent_true.
Qed.

Lemma subtype_refine5:
  forall tvars theta gamma T A b (x p : nat) t l,
    ~(p ∈ fv_context gamma) ->
    ~(p ∈ fv A) ->
    ~(p ∈ fv T) ->
    ~(p ∈ fv b) ->
    ~(x ∈ fv_context gamma) ->
    ~(x ∈ fv A) ->
    ~(x ∈ fv T) ->
    ~(x ∈ fv b) ->
    ~(x = p) ->
    open_reducible tvars
                   ((p, T_equiv (open 0 b (term_fvar x)) ttrue) :: (x, A) :: gamma)
                   (term_fvar x)
                   T ->
    valid_interpretation theta ->
    support theta = tvars ->
    satisfies (reducible_values theta) gamma l ->
    reducible_values theta t (T_refine (substitute A l) (substitute b l)) ->
    reducible_values theta t (substitute T l).
Proof.
  unfold open_reducible; repeat step || simp_red; eauto with wf.

  unshelve epose proof (H8 theta ((p, uu) :: (x,t) :: l) _ _ _); tac1;
    eauto using red_is_val, reducible_expr_value;
    try solve [ apply equivalent_star; eauto with erased; eauto with wf ].
Qed.
