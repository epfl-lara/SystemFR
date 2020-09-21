Require Export SystemFR.Judgments.
Require Export SystemFR.AnnotatedTactics.
Require Export SystemFR.ErasedIte.

Lemma annotated_reducible_T_ite:
  forall Θ Γ b t1 t2 T1 T2 x,
    ~(x ∈ fv_context Γ) ->
    ~(x ∈ fv b) ->
    ~(x ∈ fv t1) ->
    ~(x ∈ fv t2) ->
    ~(x ∈ fv T1) ->
    ~(x ∈ fv T2) ->
    ~(x ∈ Θ) ->
    wf t1 0 ->
    wf t2 0 ->
    wf T1 0 ->
    wf T2 0 ->
    subset (fv b) (support Γ) ->
    subset (fv t1) (support Γ) ->
    subset (fv t2) (support Γ) ->
    subset (fv T1) (support Γ) ->
    subset (fv T2) (support Γ) ->
    [[ Θ; Γ ⊨ b : T_bool ]] ->
    [[ Θ; (x, T_equiv b ttrue) :: Γ ⊨ t1 : T1 ]] ->
    [[ Θ; (x, T_equiv b tfalse) :: Γ ⊨ t2 : T2 ]] ->
    [[ Θ; Γ ⊨ ite b t1 t2 : T_ite b T1 T2 ]].
Proof.
  intros; apply open_reducible_T_ite with x;
    repeat step;
    side_conditions.
Qed.
