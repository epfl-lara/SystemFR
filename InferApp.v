Require Export SystemFR.ErasedArrow.
Require Export SystemFR.ErasedSingleton.
Require Export SystemFR.ReducibilitySubtype.

Opaque reducible_values.

Inductive widen: tree -> tree -> Prop :=
| WidenSingleton:
    forall ty1 ty2 f,
      is_erased_term f ->
      is_erased_type ty2 ->
      wf f 0 ->
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

Lemma reducible_equiv:
  forall ρ t1 t2,
    [ t1 ≡ t2 ] ->
    [ ρ | uu : T_equiv t1 t2 ].
Proof.
  intros; unfold reducible, reduces_to; repeat step || exists uu || simp_red; t_closer.
Qed.

Lemma widen_singleton_arrow:
  forall Θ Γ ty1 ty2 f,
    is_erased_term f ->
    is_erased_type ty2 ->
    wf f 0 ->
    [Θ; Γ ⊨ T_singleton (T_arrow ty1 ty2) f <:
            T_arrow ty1 (T_singleton ty2 (app f (lvar 0 term_var))) ].
Proof.
  unfold open_subtype, subtype;
    repeat step || simp_red || open_none || apply reducible_type_refine with uu ||
           (rewrite shift_nothing2 in * by eauto with wf) || list_utils ||
           apply reducible_equiv || t_instantiate_reducible ||
           apply equivalent_app ||
           rewrite reducibility_rewrite in *;
    eauto with wf fv erased;
    eauto using reducible_values_closed;
    try solve [ apply equivalent_refl; eauto with wf fv erased ].
Qed.

Lemma singleton_subtype:
  forall Θ Γ ty f,
    [ Θ; Γ ⊨ T_singleton ty f <: ty ].
Proof.
  unfold open_subtype, subtype; repeat step || simp_red.
Qed.

Lemma widen_singleton:
  forall Θ Γ ty ty' f,
    [Θ; Γ ⊨ ty <: ty'] ->
    [Θ; Γ ⊨ T_singleton ty f <: ty'].
Proof.
  eauto using open_subtype_trans, singleton_subtype.
Qed.

Lemma widen_open_subtype:
  forall Θ Γ ty1 ty2,
    widen ty1 ty2 ->
    [ Θ; Γ ⊨ ty1 <: ty2 ].
Proof.
  induction 1; repeat step;
    eauto using widen_singleton_arrow;
    eauto using widen_singleton.
Qed.

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
