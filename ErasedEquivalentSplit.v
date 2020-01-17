Require Export SystemFR.SatisfiesLemmas.
Require Export SystemFR.ErasedEquivalentIte.
Require Export SystemFR.ErasedEquivalentMatch.
Require Export SystemFR.ErasedEquivalentRec.

Lemma equivalent_split_bool:
  forall theta gamma1 gamma2 b t t' x l,
    ~(x ∈ fv b) ->
    ~(x ∈ fv t) ->
    ~(x ∈ fv t') ->
    ~(x ∈ fv_context gamma1) ->
    ~(x ∈ fv_context gamma2) ->
    subset (fv b) (support gamma2) ->
    [ support theta; gamma2 ⊨ b : T_bool ] ->
    valid_interpretation theta ->
    (forall l,
       satisfies (reducible_values theta) (gamma1 ++ (x, T_equiv b ttrue) :: gamma2) l ->
       equivalent_terms (substitute t l) (substitute t' l)) ->
    (forall l,
       satisfies (reducible_values theta) (gamma1 ++ (x, T_equiv b tfalse) :: gamma2) l ->
       equivalent_terms (substitute t l) (substitute t' l)) ->
    satisfies (reducible_values theta) (gamma1 ++ gamma2) l ->
    equivalent_terms (substitute t l) (substitute t' l).
Proof.
  unfold open_reducible, reducible, reduces_to;
    repeat step || simp_red || t_sat_cut || t_instantiate_sat3 || t_sat_add;
    eauto 2 with b_sat;
    eauto 2 with b_equiv_subst.
Qed.

Lemma equivalent_split_nat:
  forall theta gamma1 gamma2 n t t' x y l,
    ~(x ∈ fv_context gamma1) ->
    ~(x ∈ fv_context gamma2) ->
    ~(x ∈ fv n) ->
    ~(x ∈ fv t) ->
    ~(x ∈ fv t') ->
    ~(y ∈ fv_context gamma1) ->
    ~(y ∈ fv_context gamma2) ->
    ~(y ∈ fv n) ->
    ~(y ∈ fv t) ->
    ~(y ∈ fv t') ->
    ~(x = y) ->
    subset (fv n) (support gamma2) ->
    [ support theta; gamma2 ⊨ n : T_nat ] ->
    valid_interpretation theta ->
    (forall l,
       satisfies (reducible_values theta) (gamma1 ++ (x, T_equiv n zero) :: gamma2) l ->
       equivalent_terms (substitute t l) (substitute t' l)) ->
    (forall l,
       satisfies (reducible_values theta)
                 (gamma1 ++ (x, T_equiv n (succ (fvar y term_var))) :: (y, T_nat) :: gamma2)
                 l ->
       equivalent_terms (substitute t l) (substitute t' l)) ->
    satisfies (reducible_values theta) (gamma1 ++ gamma2) l ->
    equivalent_terms (substitute t l) (substitute t' l).
Proof.
  unfold open_reducible, reducible, reduces_to;
    repeat step || t_instantiate_sat3 || simp_red || t_sat_cut.

  force_invert is_nat_value; repeat step || t_sat_add;
    eauto 2 with b_sat;
    eauto 2 with b_equiv_subst.
Qed.

Lemma reducible_equivalent_ite:
  forall theta gamma t1 t2 t3 t x l,
    ~(x ∈ fv_context gamma) ->
    ~(x ∈ fv t1) ->
    ~(x ∈ fv t2) ->
    ~(x ∈ fv t3) ->
    ~(x ∈ fv t) ->
    is_erased_term t2 ->
    is_erased_term t3 ->
    wf t2 0 ->
    wf t3 0 ->
    valid_interpretation theta ->
    [ support theta; gamma ⊨ t1 : T_bool ] ->
    satisfies (reducible_values theta) gamma l ->
    (forall l,
       satisfies (reducible_values theta) ((x, T_equiv t1 ttrue) :: gamma) l ->
       equivalent_terms (substitute t2 l) (substitute t l)) ->
    (forall l,
       satisfies (reducible_values theta) ((x, T_equiv t1 tfalse) :: gamma) l ->
       equivalent_terms (substitute t3 l) (substitute t l)) ->
    equivalent_terms (ite (substitute t1 l) (substitute t2 l) (substitute t3 l)) (substitute t l).
 Proof.
   unfold open_reducible;
     repeat step || apply equivalent_ite || t_instantiate_sat3 || simp_red ||
            t_deterministic_star || unfold reducible, reduces_to in * || t_sat_add;
     eauto 2 with b_sat;
     eauto 2 with b_equiv_subst;
     t_closer.
Qed.

Lemma reducible_equivalent_match:
  forall theta gamma tn t0 ts t n p l,
    ~(p ∈ fv_context gamma) ->
    ~(p ∈ fv tn) ->
    ~(p ∈ fv ts) ->
    ~(p ∈ fv t0) ->
    ~(p ∈ fv t) ->
    ~(n ∈ fv_context gamma) ->
    ~(n ∈ fv ts) ->
    ~(n ∈ fv tn) ->
    ~(n ∈ fv t) ->
    ~(n = p) ->
    open_reducible (support theta) gamma tn T_nat ->
    valid_interpretation theta ->
    is_erased_term t0 ->
    is_erased_term ts ->
    wf t0 0 ->
    wf ts 1 ->
    (forall l,
       satisfies (reducible_values theta) ((p, T_equiv tn zero) :: gamma) l ->
       equivalent_terms (substitute t0 l) (substitute t l)) ->
    (forall l,
       satisfies (reducible_values theta)
                 ((p, T_equiv tn (succ (fvar n term_var))) :: (n, T_nat) :: gamma)
                 l ->
       equivalent_terms (substitute (open 0 ts (fvar n term_var)) l) (substitute t l)) ->
    satisfies (reducible_values theta) gamma l ->
    equivalent_terms (tmatch (substitute tn l) (substitute t0 l) (substitute ts l)) (substitute t l).
Proof.
  unfold open_reducible, reducible, reduces_to; repeat step || t_instantiate_sat3 || simp_red.
  eapply equivalent_match; eauto;
    repeat step || t_sat_add || step_inversion is_nat_value;
      eauto 2 with b_sat;
      eauto 2 with b_equiv_subst;
      t_closer.
Qed.

Lemma reducible_equivalent_rec:
  forall theta gamma tn t0 ts t n p l,
    ~(p ∈ fv_context gamma) ->
    ~(p ∈ fv tn) ->
    ~(p ∈ fv ts) ->
    ~(p ∈ fv t0) ->
    ~(p ∈ fv t) ->
    ~(n ∈ fv_context gamma) ->
    ~(n ∈ fv ts) ->
    ~(n ∈ fv tn) ->
    ~(n ∈ fv t0) ->
    ~(n ∈ fv t) ->
    ~(n = p) ->
    is_erased_term t0 ->
    is_erased_term ts ->
    wf t0 0 ->
    wf ts 2 ->
    [ support theta; gamma ⊨ tn : T_nat ] ->
    valid_interpretation theta ->
    (forall l,
       satisfies (reducible_values theta) ((p, T_equiv tn zero) :: gamma) l ->
       equivalent_terms (substitute t0 l) (substitute t l)) ->
    (forall l,
       satisfies (reducible_values theta)
                 ((p, T_equiv tn (succ (fvar n term_var))) :: (n, T_nat) :: gamma) l ->
       equivalent_terms
         (substitute
            (open 0
                  (open 1 ts (fvar n term_var))
                  (notype_lambda (notype_rec (fvar n term_var) t0 ts))) l)
         (substitute t l)) ->
    satisfies (reducible_values theta) gamma l ->
    equivalent_terms (notype_rec (substitute tn l) (substitute t0 l) (substitute ts l))
               (substitute t l).
Proof.
  unfold open_reducible, reducible, reduces_to; repeat step || t_instantiate_sat3 || simp_red.
  eapply equivalent_rec; eauto;
    repeat step || t_sat_add || step_inversion is_nat_value;
    eauto 2 with b_sat;
    eauto 2 with b_equiv_subst;
    t_closer.
Qed.
