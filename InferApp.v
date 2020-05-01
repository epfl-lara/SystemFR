Require Export SystemFR.ScalaDepSugar.
Require Export SystemFR.ErasedArrow.
Require Export SystemFR.ReducibilitySubtype.

Inductive widen: tree -> tree -> Prop :=
| WidenSingleton:
    forall ty1 ty2 f,
      widen
        (T_singleton (T_arrow ty1 ty2) f)
        (T_arrow ty1 (T_singleton ty2 (app f (lvar 0 term_var))))
| WidenSingleton2:
    forall ty f ty',
      widen ty ty' ->
      widen (T_singleton ty f) ty'
| WidenRefl:
    forall ty, widen ty ty
.

Lemma widen_open_subtype:
  forall Θ Γ ty1 ty2,
    widen ty1 ty2 ->
    [ Θ; Γ ⊨ ty1 <: ty2 ].
Proof.
  induction 1;
    repeat step.
Admitted.

Lemma open_tapp_helper:
  forall Θ Γ t1 t2 S T U,
    is_erased_type T ->
    wf T 1 ->
    subset (fv T) (support Γ) ->
    [ Θ; Γ ⊨ t1 : U ] ->
    widen U (T_arrow S T) ->
    [ Θ; Γ ⊨ t2 : S ] ->
    [ Θ; Γ ⊨ app t1 t2 : open 0 T t2 ].
Proof.
  intros; eapply open_reducible_app; eauto.
  eauto using widen_open_subtype, open_subtype_reducible.
Qed.

Lemma open_tapp:
  forall Γ t1 t2 S T U,
    is_erased_type T ->
    wf T 1 ->
    subset (fv T) (support Γ) ->
    [ Γ ⊨ t1 : U ] ->
    widen U (T_arrow S T) ->
    [ Γ ⊨ t2 : S ] ->
    [ Γ ⊨ app t1 t2 : open 0 T t2 ].
Proof.
  eauto using open_tapp_helper.
Qed.
