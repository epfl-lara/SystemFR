Require Export SystemFR.Judgments.
Require Export SystemFR.AnnotatedTactics.
Require Export SystemFR.ErasedIte.

Lemma annotated_reducible_T_ite:
  forall tvars gamma b t1 t2 T1 T2 x,
    ~(x ∈ fv_context gamma) ->
    ~(x ∈ fv b) ->
    ~(x ∈ fv t1) ->
    ~(x ∈ fv t2) ->
    ~(x ∈ fv T1) ->
    ~(x ∈ fv T2) ->
    ~(x ∈ tvars) ->
    wf t1 0 ->
    wf t2 0 ->
    wf T1 0 ->
    wf T2 0 ->
    subset (fv t1) (support gamma) ->
    subset (fv t2) (support gamma) ->
    subset (fv T1) (support gamma) ->
    subset (fv T2) (support gamma) ->
    [[ tvars; gamma ⊨ b : T_bool ]] ->
    [[ tvars; (x, T_equiv b ttrue) :: gamma ⊨ t1 : T1 ]] ->
    [[ tvars; (x, T_equiv b tfalse) :: gamma ⊨ t2 : T2 ]] ->
    [[ tvars; gamma ⊨ ite b t1 t2 : T_ite b T1 T2 ]].
Proof.
  unfold annotated_reducible;
    repeat step.

  apply open_reducible_T_ite with x;
    repeat step;
    side_conditions.
Qed.
