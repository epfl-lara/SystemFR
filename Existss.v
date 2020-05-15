Require Import Coq.Lists.List.

Require Export SystemFR.ReducibilityLemmas.
Require Export SystemFR.CloseLemmas.
Require Export SystemFR.SubstitutionErase.
Require Export SystemFR.Functional.

Opaque reducible_values.

Fixpoint T_existss n T1 T2 :=
  match n with
  | 0 => T2
  | S n' => T_exists T1 (T_existss n' T1 T2)
  end.

Definition T_exists_vars xs T1 T2 :=
  T_existss (List.length xs) T1 (closes 0 T2 (rev xs)).

Lemma psubstitute_texistss:
  forall n T1 T2 l tag,
    psubstitute (T_existss n T1 T2) l tag =
    T_existss n (psubstitute T1 l tag) (psubstitute T2 l tag).
Proof.
  induction n; repeat step || rewrite_any.
Qed.

Lemma substitute_closes:
  forall xs t l tag k,
    (forall x, x ∈ support l -> x ∈ xs -> False) ->
    pclosed_mapping l term_var ->
    psubstitute (closes k t xs) l tag = closes k (psubstitute t l tag) xs.
Proof.
  induction xs;
    repeat step || rewrite substitute_close by (steps; eauto);
    try solve [ rewrite_any; steps; eauto ].
Qed.

Lemma psubstitute_texists_vars:
  forall xs T1 T2 l tag,
    (forall x, x ∈ support l -> x ∈ xs -> False) ->
    pclosed_mapping l term_var ->
    psubstitute (T_exists_vars xs T1 T2) l tag =
    T_exists_vars xs (psubstitute T1 l tag) (psubstitute T2 l tag).
Proof.
  unfold T_exists_vars; intros; rewrite psubstitute_texistss; apply f_equal.
  rewrite substitute_closes; repeat step || rewrite <- in_rev in *; eauto.
Qed.

Lemma is_erased_type_existss:
  forall n T1 T2,
    is_erased_type T1 ->
    is_erased_type T2 ->
    is_erased_type (T_existss n T1 T2).
Proof.
  induction n; repeat step || apply_any.
Qed.

Hint Resolve is_erased_type_existss: erased.

Lemma open_existss:
  forall n T1 T2 k rep,
    wf T1 0 ->
    open k (T_existss n T1 T2) rep =
    T_existss n T1 (open (n + k) T2 rep).
Proof.
  induction n; steps; repeat step || t_equality || open_none || rewrite_any ||
                             rewrite PeanoNat.Nat.add_succ_r.
Qed.

Lemma reducible_exists_vars:
  forall xs ρ v vs T1 T2,
    wf T1 0 ->
    wf T2 0 ->
    is_erased_type T1 ->
    is_erased_type T2 ->
    List.Forall (fun v => [ ρ | v : T1 ]v) vs ->
    List.length xs = List.length vs ->
    valid_interpretation ρ ->
    (forall z v', z ∈ xs -> v' ∈ vs -> z ∈ fv v' -> False) ->
    [ ρ | v : psubstitute T2 (List.combine xs vs) term_var ]v ->
    [ ρ | v : T_exists_vars xs T1 T2 ]v.
Proof.
  induction xs; repeat step || t_substitutions.
  unshelve epose proof
    (IHxs ρ v l T1 (psubstitute T2 ((a,t) :: nil) term_var) _ _ _ _ _ _ _ _ _); steps; eauto;
    try solve [
      rewrite <- substitute_cons2; repeat step || rewrite support_combine in * by auto; eauto
    ];
    eauto 3 with erased step_tactic;
    eauto 3 with wf step_tactic.

  unfold T_exists_vars in *.
  simp_red_goal; steps; eauto 4 with erased; eauto using reducible_values_closed.
  exists t; repeat step || rewrite open_existss; eauto with erased fv wf.
  rewrite <- rev_length at 2.
  rewrite open_closes; steps; eauto with wf fv.
Qed.

Lemma reducible_exists_vars2_helper:
  forall xs ρ v T1 T2,
    wf T1 0 ->
    wf T2 0 ->
    is_erased_type T1 ->
    is_erased_type T2 ->
    valid_interpretation ρ ->
    [ ρ | v : T_exists_vars xs T1 T2 ]v ->
    (exists vs,
      List.Forall (fun v => [ ρ | v : T1 ]v) vs /\
      length vs = length xs /\
      [ ρ | v : psubstitute T2 (combine xs vs) term_var ]v).
Proof.
  induction xs; repeat step || t_substitutions || simp_red_top_level_hyp;
    eauto 2 with step_tactic.

  rewrite open_existss in *; eauto with wf.
  rewrite <- rev_length in * at 2.
  rewrite open_closes in *; eauto with wf fv.
  rewrite rev_length in *.

  unshelve epose proof (IHxs _ _ _ _ _ _ _ _ _ H9); steps;
    eauto 2 with wf step_tactic;
    eauto 2 with erased step_tactic.

  exists (a0 :: vs); steps; eauto.
  rewrite substitute_cons2; repeat step || (erewrite reducible_val_fv in * by eauto).
Qed.

Lemma reducible_exists_vars2:
  forall xs ρ v T1 T2,
    wf T1 0 ->
    wf T2 0 ->
    is_erased_type T1 ->
    is_erased_type T2 ->
    valid_interpretation ρ ->
    [ ρ | v : T_exists_vars xs T1 T2 ]v ->
    (exists vs,
      List.Forall (fun v => [ ρ | v : T1 ]v) vs /\
      functional (combine xs vs) /\
      length vs = length xs /\
      [ ρ | v : psubstitute T2 (combine xs vs) term_var ]v).
Proof.
  intros.
  apply_anywhere reducible_exists_vars2_helper; steps.
  pose proof (functionalize (combine xs vs)); repeat step || list_utils2.
  exists (range l'); repeat step || list_utils || list_utils2 || rewrite Forall_forall in *.
  erewrite subst_permutation in * |-; eauto.
Qed.
