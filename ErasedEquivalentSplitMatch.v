Require Import Coq.Lists.List.

Require Export SystemFR.RedTactics.
Require Export SystemFR.ErasedEquivalentMatch.

Opaque reducible_values.
Opaque makeFresh.

Lemma equivalent_split_match:
  forall theta gamma1 gamma2 n t t' e1 e2 e x y v l,
    [ support theta; gamma2 ⊨ n : T_nat ] ->
    valid_interpretation theta ->
    (forall z, z ∈ support gamma1 -> z ∈ fv e1 -> False) ->
    (forall z, z ∈ support gamma1 -> z ∈ fv e2 -> False) ->
    (forall z, z ∈ support gamma1 -> z ∈ fv e -> False) ->
    (forall z, z ∈ support gamma1 -> z ∈ fv n -> False) ->
    ~(x ∈ fv_context gamma1) ->
    ~(x ∈ fv_context gamma2) ->
    ~(x ∈ fv t) ->
    ~(x ∈ fv t') ->
    ~(y ∈ fv e) ->
    ~(y ∈ fv e1) ->
    ~(y ∈ fv e2) ->
    ~(y ∈ fv n) ->
    ~(y ∈ fv t) ->
    ~(y ∈ fv t') ->
    ~(y ∈ fv_context gamma1) ->
    ~(y ∈ fv_context gamma2) ->
    ~(v ∈ fv e) ->
    ~(v ∈ fv e1) ->
    ~(v ∈ fv e2) ->
    ~(v ∈ fv n) ->
    ~(v ∈ fv t) ->
    ~(v ∈ fv t') ->
    ~(v ∈ fv_context gamma1) ->
    ~(v ∈ fv_context gamma2) ->
    NoDup (x :: y :: v :: nil) ->
    subset (fv n ++ fv e1 ++ fv e2) (support gamma2) ->
    subset (fv e) (support gamma2) ->
    (forall l,
          satisfies (reducible_values theta)
                    (gamma1 ++ (x, T_equiv e1 e) :: (y, T_equiv n zero) :: gamma2)
                    l ->
          equivalent_terms (substitute t l) (substitute t' l)) ->
    (forall l,
          satisfies (reducible_values theta)
                    (gamma1 ++
                            (x, T_equiv (open 0 e2 (fvar v term_var)) e)
                            :: (y, T_equiv n (succ (fvar v term_var))) :: (v, T_nat) :: gamma2) l ->
          equivalent_terms (substitute t l) (substitute t' l)) ->
    satisfies (reducible_values theta) (gamma1 ++ (x, T_equiv (tmatch n e1 e2) e) :: gamma2) l ->
    wf n 0 ->
    wf e1 0 ->
    wf e2 1 ->
    equivalent_terms (substitute t l) (substitute t' l).
Proof.
  unfold open_reducible, reducible, reduces_to;
    repeat step || list_utils || t_sat_cut || t_instantiate_sat3 ||
           t_termlist || step_inversion satisfies ||
           simp_red.

  t_invert_nat_value; steps.

  - unshelve epose proof (H28 (l1 ++ (x, uu) :: (y, uu) :: lterms) _);
      repeat step || apply satisfies_insert || step_inversion NoDup ||
             list_utils || t_substitutions || simp_red;
      t_closer;
      eauto using equivalent_match_zero2;
      eauto using satisfies_drop;
      try solve [ equivalent_star ].

  - unshelve epose proof (H29 (l1 ++ (x, uu) :: (y, uu) :: (v, v1) :: lterms) _);
      clear H28; clear H29;
      repeat step || apply satisfies_insert || step_inversion NoDup ||
             list_utils || t_substitutions || simp_red || fv_open;
      t_closer;
      eauto with twf;
      eauto using equivalent_match_succ2 with values erased wf;
      eauto using satisfies_drop;
      try solve [ equivalent_star ].
Qed.
