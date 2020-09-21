Require Export SystemFR.FVLemmasLists.

Lemma satisfies_insert:
  forall (P: tree -> tree -> Prop) Γ1 Γ2 l1 l2 t T x,
    ~(x ∈ fv T) ->
    ~(x ∈ fv_context Γ2) ->
    pfv t term_var = nil ->
    pfv t type_var = nil ->
    wf t 0 ->
    twf t 0 ->
    P t (substitute T l2) ->
    support Γ1 = support l1 ->
    ~(x ∈ support Γ1) ->
    ~(x ∈ fv_context Γ1) ->
    (forall z, z ∈ support Γ1 -> z ∈ fv T -> False) ->
    satisfies P (Γ1 ++ Γ2) (l1 ++ l2) ->
    satisfies P (Γ1 ++ (x,T) :: Γ2) (l1 ++ (x,t) :: l2).
Proof.
  induction Γ1; destruct l1;
    repeat step || step_inversion satisfies || apply SatCons || list_utils ||
           (rewrite substitute_skip by (steps; eauto with fv b_cmap)); eauto.
Qed.

Lemma satisfies_drop:
  forall (P: tree -> tree -> Prop) Γ1 Γ2 l1 l2 t T x,
    support Γ1 = support l1 ->
    ~(x ∈ fv_context Γ1) ->
    satisfies P (Γ1 ++ (x,T) :: Γ2) (l1 ++ (x,t) :: l2) ->
    satisfies P (Γ1 ++ Γ2) (l1 ++ l2).
Proof.
  induction Γ1; destruct l1;
    repeat step || step_inversion satisfies || apply SatCons || list_utils ||
           (rewrite substitute_skip in * by (steps; eauto with fv b_cmap)); eauto.
Qed.
