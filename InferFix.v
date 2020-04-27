Require Export SystemFR.ReducibilityLemmas.
Require Export SystemFR.TypeSugar2.
Require Export SystemFR.StepTactics.

Lemma subst_fix_default:
  forall t default fuel l tag,
    wfs l 0 ->
    psubstitute (fix_default t default fuel) l tag =
    fix_default (psubstitute t l tag) (psubstitute default l tag) (psubstitute fuel l tag).
Proof.
  unfold fix_default; repeat step || t_equality || rewrite substitute_shift_open in *.
Qed.

Lemma evaluate_fix_default:
  forall t default fuel,
    is_nat_value fuel ->
    wf default 0 ->
    wf t 1 ->
    (fuel = zero /\ star scbv_step (fix_default t default fuel) default) \/
    (exists fuel', fuel = succ fuel' /\
              star scbv_step (fix_default t default fuel) (open 0 t (fix_default t default fuel'))).
Proof.
  unfold fix_default; inversion 1; steps.
  - left; steps.
    one_step; repeat open_none.
    repeat one_step.
  - right; eexists; steps.
    one_step; repeat open_none.
    one_step.
    one_step; repeat open_none_by ltac:(eauto 2 with wf step_tactic).

    .
    rewrite (open_none _ 3).
    admit.
    eauto with wf step_tactic.
    apply wf_shift_open2; steps.
    eauto with wf step_tactic.


    wf_shift_open2

    open_none.
    rewrite open_none. in * by auto.
    star_one_step
  


Opaque fix_default.

Lemma tfix_fuel:
  forall ρ t default fuel T,
    is_nat_value fuel
    [ ρ | default : T ] ->
    (forall v, [ ρ | v : T ]v -> [ ρ | open 0 t v : T ]) ->
    [ ρ | fix_default t default fuel : T ].
Proof.
Admitted.

Lemma open_tfix_helper:
  forall Θ Γ t default fuel x T,
    [ Θ; Γ ⊨ fuel : T_nat ] ->
    [ Θ; Γ ⊨ default : T ] ->
    [ Θ; (x, T) :: Γ ⊨ open 0 t (fvar x term_var) : T ] ->
    [ Θ; Γ ⊨ fix_default t default fuel : T ].
Proof.
  unfold open_reducible; steps.
²Admitted.

Lemma open_tfix:
  forall Γ t default fuel x T,
    [ Γ ⊨ fuel : T_nat ] ->
    [ Γ ⊨ default : T ] ->
    [ (x, T) :: Γ ⊨ open 0 t (fvar x term_var) : T ] ->
    [ Γ ⊨ fix_default t default fuel : T ].
Proof.
  eauto using open_tfix_helper.
Qed.
