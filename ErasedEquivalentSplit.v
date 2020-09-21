Require Export SystemFR.SatisfiesLemmas.
Require Export SystemFR.ErasedEquivalentIte.
Require Export SystemFR.ErasedEquivalentMatch.

Opaque reducible_values.

Lemma equivalent_split_bool:
  forall ρ Γ1 Γ2 b t t' x l,
    ~(x ∈ fv b) ->
    ~(x ∈ fv t) ->
    ~(x ∈ fv t') ->
    ~(x ∈ fv_context Γ1) ->
    ~(x ∈ fv_context Γ2) ->
    subset (fv b) (support Γ2) ->
    [ support ρ; Γ2 ⊨ b : T_bool ] ->
    valid_interpretation ρ ->
    (forall l,
       satisfies (reducible_values ρ) (Γ1 ++ (x, T_equiv b ttrue) :: Γ2) l ->
       [ substitute t l ≡ substitute t' l ]) ->
    (forall l,
       satisfies (reducible_values ρ) (Γ1 ++ (x, T_equiv b tfalse) :: Γ2) l ->
       [ substitute t l ≡ substitute t' l ]) ->
    satisfies (reducible_values ρ) (Γ1 ++ Γ2) l ->
    [ substitute t l ≡ substitute t' l ].
Proof.
  unfold open_reducible,reduces_to;
    repeat step || simp_red || satisfies_cut || t_instantiate_sat3 || t_sat_add;
    eauto 2 with b_equiv_subst;
    try solve [ eapply satisfies_insert2; eauto; t_closer ].
Qed.

Lemma equivalent_split_nat:
  forall ρ Γ1 Γ2 n t t' x y l,
    ~(x ∈ fv_context Γ1) ->
    ~(x ∈ fv_context Γ2) ->
    ~(x ∈ fv n) ->
    ~(x ∈ fv t) ->
    ~(x ∈ fv t') ->
    ~(y ∈ fv_context Γ1) ->
    ~(y ∈ fv_context Γ2) ->
    ~(y ∈ fv n) ->
    ~(y ∈ fv t) ->
    ~(y ∈ fv t') ->
    ~(x = y) ->
    subset (fv n) (support Γ2) ->
    [ support ρ; Γ2 ⊨ n : T_nat ] ->
    valid_interpretation ρ ->
    (forall l,
       satisfies (reducible_values ρ) (Γ1 ++ (x, T_equiv n zero) :: Γ2) l ->
       [ substitute t l ≡ substitute t' l ]) ->
    (forall l,
       satisfies (reducible_values ρ)
                 (Γ1 ++ (x, T_equiv n (succ (fvar y term_var))) :: (y, T_nat) :: Γ2)
                 l ->
       [ substitute t l ≡ substitute t' l ]) ->
    satisfies (reducible_values ρ) (Γ1 ++ Γ2) l ->
    [ substitute t l ≡ substitute t' l ].
Proof.
  unfold open_reducible,reduces_to;
    repeat step || t_instantiate_sat3 || simp_red || satisfies_cut.

  force_invert is_nat_value; repeat step || t_sat_add;
    eauto 2 with b_equiv_subst;
    try solve [ eapply satisfies_insert2; eauto; t_closer ];
    try solve [ eapply satisfies_insert_nat_succ; eauto; t_closer ].
Qed.

Lemma reducible_equivalent_ite:
  forall ρ Γ t1 t2 t3 t x l,
    ~(x ∈ fv_context Γ) ->
    ~(x ∈ fv t1) ->
    ~(x ∈ fv t2) ->
    ~(x ∈ fv t3) ->
    ~(x ∈ fv t) ->
    is_erased_term t2 ->
    is_erased_term t3 ->
    wf t2 0 ->
    wf t3 0 ->
    subset (fv t2) (support Γ) ->
    subset (fv t3) (support Γ) ->
    valid_interpretation ρ ->
    [ support ρ; Γ ⊨ t1 : T_bool ] ->
    satisfies (reducible_values ρ) Γ l ->
    (forall l,
       satisfies (reducible_values ρ) ((x, T_equiv t1 ttrue) :: Γ) l ->
       [ substitute t2 l ≡ substitute t l ]) ->
    (forall l,
       satisfies (reducible_values ρ) ((x, T_equiv t1 tfalse) :: Γ) l ->
       [ substitute t3 l ≡ substitute t l ]) ->
    [ ite (substitute t1 l) (substitute t2 l) (substitute t3 l) ≡ substitute t l ].
 Proof.
   unfold open_reducible;
     repeat step || apply equivalent_ite || t_instantiate_sat3 || simp_red ||
            t_deterministic_star || unfold reduces_to in * || t_sat_add;
     eauto 2 with b_equiv_subst;
     t_closer;
     try solve [ eapply satisfies_insert3; eauto; t_closer ].
Qed.

Lemma reducible_equivalent_match:
  forall ρ Γ tn t0 ts t n p l,
    ~(p ∈ fv_context Γ) ->
    ~(p ∈ fv tn) ->
    ~(p ∈ fv ts) ->
    ~(p ∈ fv t0) ->
    ~(p ∈ fv t) ->
    ~(n ∈ fv_context Γ) ->
    ~(n ∈ fv ts) ->
    ~(n ∈ fv tn) ->
    ~(n ∈ fv t) ->
    ~(n = p) ->
    [ support ρ; Γ ⊨ tn : T_nat ] ->
    valid_interpretation ρ ->
    is_erased_term t0 ->
    is_erased_term ts ->
    wf t0 0 ->
    wf ts 1 ->
    subset (fv t0) (support Γ) ->
    subset (fv ts) (support Γ) ->
    (forall l,
       satisfies (reducible_values ρ) ((p, T_equiv tn zero) :: Γ) l ->
       [ substitute t0 l ≡ substitute t l ]) ->
    (forall l,
       satisfies (reducible_values ρ)
                 ((p, T_equiv tn (succ (fvar n term_var))) :: (n, T_nat) :: Γ)
                 l ->
       [ substitute (open 0 ts (fvar n term_var)) l ≡ substitute t l ]) ->
    satisfies (reducible_values ρ) Γ l ->
    [ tmatch (substitute tn l) (substitute t0 l) (substitute ts l) ≡ substitute t l ].
Proof.
  unfold open_reducible,reduces_to; repeat step || t_instantiate_sat3 || simp_red.
  eapply equivalent_match; eauto;
    repeat step || t_sat_add || step_inversion is_nat_value;
      eauto 2 with b_equiv_subst;
      t_closer;
      try solve [ eapply satisfies_insert3; eauto; t_closer ];
      try solve [ eapply satisfies_cons_nat_succ; eauto; t_closer ].
Qed.
