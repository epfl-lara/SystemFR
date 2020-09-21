Require Export SystemFR.Judgments.
Require Export SystemFR.AnnotatedTactics.
Require Export SystemFR.ErasedBool.

Lemma annotated_reducible_true:
  forall Θ Γ,
    [[ Θ; Γ ⊨ ttrue : T_bool ]].
Proof.
  eauto using open_reducible_true.
Qed.

Lemma annotated_reducible_false:
  forall Θ Γ,
    [[ Θ; Γ ⊨ tfalse : T_bool ]].
Proof.
  intros; eauto using open_reducible_false.
Qed.

Lemma annotated_reducible_ite:
  forall Θ Γ b t1 t2 T x,
    ~(x ∈ fv_context Γ) ->
    ~(x ∈ fv b) ->
    ~(x ∈ fv t1) ->
    ~(x ∈ fv t2) ->
    ~(x ∈ fv T) ->
    ~(x ∈ Θ) ->
    wf t1 0 ->
    wf t2 0 ->
    subset (fv t1) (support Γ) ->
    subset (fv t2) (support Γ) ->
    [[ Θ; Γ ⊨ b : T_bool ]] ->
    [[ Θ; (x, T_equiv b ttrue)  :: Γ ⊨ t1 : T ]] ->
    [[ Θ; (x, T_equiv b tfalse) :: Γ ⊨ t2 : T ]] ->
    [[ Θ; Γ ⊨ ite b t1 t2 : T ]].
Proof.
  repeat step || apply open_reducible_ite with x;
    side_conditions.
Qed.
