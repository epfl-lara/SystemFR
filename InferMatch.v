Require Import Coq.Strings.String.

Require Export SystemFR.StepTactics.
Require Export SystemFR.ErasedRecGen.
Require Export SystemFR.ErasedSingleton.

Opaque reducible_values.

Lemma evaluate_list_match:
  forall ρ v t2 t3,
    valid_interpretation ρ ->
    wf t2 0 ->
    wf t3 2 ->
    is_erased_term t2 ->
    is_erased_term t3 ->
    pfv t2 term_var = nil ->
    pfv t3 term_var = nil ->
    [ ρ | v : List ]v -> (
      (v = tnil /\ star scbv_step (list_match v t2 t3) t2) \/
      (exists h l,
         v = tcons h l /\
         [ list_match v t2 t3 ≡ open 0 (open 1 t3 h) l ]
      )
    ).
Proof.
  unfold List, list_match.
  intros.
  apply (reducible_values_unfold_gen _ _ _ _ 0) in H6;
    repeat step || simp_spos || simp_red_top_level_hyp.

  - left; steps; one_step.
  - right; eexists; eexists; steps.
    apply equivalent_trans with (open 0 (open 1 t3 (pi1 (pp a b))) (pi2 (pp a b))).
    + equivalent_star;
        eauto 3 with erased step_tactic;
        eauto 3 with wf step_tactic;
        try solve [ repeat apply pfv_shift_open || step ].

      apply star_one.
      eapply scbv_step_same.
      apply SPBetaMatchRight; t_closer.
      rewrite open_shift_open2; steps; t_closer;
        eauto 3 with wf step_tactic.
      rewrite no_shift_open; t_closer.
      rewrite open_shift_open2; steps; t_closer;
        eauto 3 with wf step_tactic.

      2
    eauto with smallstep.
    apply Trans.
    one_step.


    open_none; auto.

Opaque list_match.
Opaque List_Match.

  
  
  simp_red; steps.
  

  
  intros.
  unfold List
  repeat step || simp_red.


Lemma tmatch:
  forall ρ t t2 t3 T2 T3,
    [ ρ | t : List ] ->
    [ ρ | t2 : T2 ] ->
    (forall h t, [ ρ | h : T_top ] -> [ ρ | t : List ] ->
            [ ρ | open 0 (open 1 t3 h) t : open 0 (open 1 T3 h) t ]) ->
    [ ρ | list_match t t2 t3 : List_Match t T2 T3 ].
Proof.
Admitted.

Lemma open_tmatch_helper:
  forall Θ Γ t t2 t3 T2 T3 x1 x2,
    ~ x1 ∈ support Γ ->
    ~ x2 ∈ support Γ ->
    [ Θ; Γ ⊨ t : List ] ->
    [ Θ; Γ ⊨ t2 : T2 ] ->
    [ Θ; (x1, T_top) :: (x2, List) :: Γ ⊨
        open 0 (open 1 t3 (fvar x1 term_var)) (fvar x2 term_var) :
        open 0 (open 1 T3 (fvar x1 term_var)) (fvar x2 term_var) ] ->
    [ Θ; Γ ⊨ list_match t t2 t3 : List_Match t T2 T3 ].
Proof.
  unfold open_reducible;
    repeat step || apply tmatch ||
           rewrite substitute_list_match || rewrite substitute_List_Match;
    eauto with wf.
Admitted.

Lemma open_tmatch:
  forall Γ t t2 t3 T2 T3 x1 x2,
    ~ x1 ∈ support Γ ->
    ~ x2 ∈ support Γ ->
    [ Γ ⊨ t : List ] ->
    [ Γ ⊨ t2 : T2 ] ->
    [ (x1, T_top) :: (x2, List) :: Γ ⊨
        open 0 (open 1 t3 (fvar x1 term_var)) (fvar x2 term_var) :
        open 0 (open 1 T3 (fvar x1 term_var)) (fvar x2 term_var) ] ->
    [ Γ ⊨ list_match t t2 t3 : List_Match t T2 T3 ].
Proof.
  eauto using open_tmatch_helper.
Qed.
