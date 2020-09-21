Require Export SystemFR.RedTactics.
Require Export SystemFR.ErasedEquivalentIte.

Opaque reducible_values.
Opaque makeFresh.

Lemma equivalent_split_ite:
  forall ρ Γ1 Γ2 b e1 e2 t t' e x y l,
    [ support ρ; Γ2 ⊨ b : T_bool ] ->
    valid_interpretation ρ ->
    (forall z, z ∈ support Γ1 -> z ∈ fv e1 -> False) ->
    (forall z, z ∈ support Γ1 -> z ∈ fv e2 -> False) ->
    (forall z, z ∈ support Γ1 -> z ∈ fv e -> False) ->
    (forall z, z ∈ support Γ1 -> z ∈ fv b -> False) ->
    ~(x ∈ fv_context Γ1) ->
    ~(x ∈ fv t) ->
    ~(x ∈ fv t') ->
    ~(y ∈ fv e) ->
    ~(y ∈ fv e1) ->
    ~(y ∈ fv e2) ->
    ~(y ∈ fv b) ->
    ~(y ∈ fv t) ->
    ~(y ∈ fv t') ->
    ~(y ∈ fv_context Γ1) ->
    ~(y ∈ fv_context Γ2) ->
    ~(x = y) ->
    subset (fv b ++ fv e1 ++ fv e2) (support Γ2) ->
    subset (fv e) (support Γ2) ->
    wf e 0 ->
    wf b 0 ->
    wf e1 0 ->
    wf e2 0 ->
    (forall l,
       satisfies (reducible_values ρ)
                 (Γ1 ++ (x, T_equiv e1 e) :: (y, T_equiv b ttrue) :: Γ2)
                 l ->
       [ substitute t l ≡ substitute t' l ]) ->
    (forall l,
       satisfies (reducible_values ρ)
                 (Γ1 ++ (x, T_equiv e2 e) :: (y, T_equiv b tfalse) :: Γ2)
                 l ->
       [ substitute t l ≡ substitute t' l ]) ->
    satisfies (reducible_values ρ) (Γ1 ++ (x, T_equiv (ite b e1 e2) e) :: Γ2) l ->
    [ substitute t l ≡ substitute t' l ].
Proof.
  unfold open_reducible,reduces_to;
    repeat step || list_utils || satisfies_cut || t_instantiate_sat3 || t_termlist || step_inversion satisfies ||
           simp_red.

  - unshelve epose proof (H23 (l1 ++ (x, uu) :: (y, uu) :: lterms) _);
      repeat step || apply satisfies_insert || list_utils || t_substitutions || simp_red;
      t_closer;
      eauto using equivalent_ite_true3;
      eauto using satisfies_drop;
      try solve [ equivalent_star ].

  - unshelve epose proof (H24 (l1 ++ (x, uu) :: (y, uu) :: lterms) _);
      repeat step || apply satisfies_insert || list_utils || t_substitutions || simp_red;
      t_closer;
      eauto using equivalent_ite_false3;
      eauto using satisfies_drop;
      try solve [ equivalent_star ].
Qed.
