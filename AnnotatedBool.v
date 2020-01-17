Require Export SystemFR.Judgments.
Require Export SystemFR.AnnotatedTactics.
Require Export SystemFR.ErasedBool.

Lemma annotated_reducible_true:
  forall tvars gamma,
    [[ tvars; gamma ⊨ ttrue : T_bool ]].
Proof.
  unfold annotated_reducible;
    repeat step; eauto using open_reducible_true.
Qed.

Lemma annotated_reducible_false:
  forall tvars gamma,
    [[ tvars; gamma ⊨ tfalse : T_bool ]].
Proof.
  unfold annotated_reducible;
    repeat step; eauto using open_reducible_false.
Qed.

Lemma annotated_reducible_ite:
  forall tvars gamma b t1 t2 T x,
    ~(x ∈ fv_context gamma) ->
    ~(x ∈ fv b) ->
    ~(x ∈ fv t1) ->
    ~(x ∈ fv t2) ->
    ~(x ∈ fv T) ->
    ~(x ∈ tvars) ->
    wf t1 0 ->
    wf t2 0 ->
    subset (fv t1) (support gamma) ->
    subset (fv t2) (support gamma) ->
    [[ tvars; gamma ⊨ b : T_bool ]] ->
    [[ tvars; (x, T_equiv b ttrue)  :: gamma ⊨ t1 : T ]] ->
    [[ tvars; (x, T_equiv b tfalse) :: gamma ⊨ t2 : T ]] ->
    [[ tvars; gamma ⊨ ite b t1 t2 : T ]].
Proof.
  unfold annotated_reducible;
    repeat step || apply open_reducible_ite with x;
    side_conditions.
Qed.
