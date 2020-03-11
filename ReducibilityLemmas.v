Require Import Coq.Strings.String.

Require Import Equations.Equations.

Require Export SystemFR.TermList.
Require Export SystemFR.SizeLemmas.
Require Export SystemFR.StarLemmas.
Require Export SystemFR.StarInversions.
Require Export SystemFR.ErasedTermLemmas.

Require Export SystemFR.FVLemmasEval.
Require Export SystemFR.WFLemmasEval.
Require Export SystemFR.TWFLemmas.

Require Export SystemFR.ReducibilityCandidate.
Require Export SystemFR.ReducibilityDefinition.

Require Import Omega.

Opaque reducible_values. (* workaround for rewriting speed *)

Lemma reducible_values_closed:
  forall theta v T,
    reducible_values theta v T ->
    valid_interpretation theta ->
    closed_value v.
Proof.
  destruct T;
    repeat simp_red || step || destruct_tag || unfold closed_value, closed_term in *;
      eauto using in_valid_interpretation_erased with erased;
      eauto using in_valid_interpretation_pfv with fv;
      eauto using in_valid_interpretation_wf with wf;
      eauto using in_valid_interpretation_value;
      eauto 2 using is_nat_value_erased;
      eauto 2 using is_nat_value_value.
Qed.

Ltac t_reducible_values_closed :=
  match goal with
  | H1: valid_interpretation ?theta, H2: reducible_values ?theta ?v ?T |- _ =>
      poseNew (Mark v "reducible_values_closed");
      pose proof (reducible_values_closed _ _ _ H2 H1)
  end.

Lemma reducible_values_props:
  forall theta t T tag,
    reducible_values theta t T ->
    valid_interpretation theta ->
      (is_erased_term t /\ pfv t tag = nil /\ wf t 0 /\ cbv_value t).
Proof.
  intros theta t T tag H1 H2; destruct tag;
    pose proof (reducible_values_closed theta t T H1 H2);
    unfold closed_value, closed_term in *; steps;
      eauto using is_erased_term_tfv.
Qed.

Lemma reducible_values_erased:
  forall theta t T,
    reducible_values theta t T ->
    valid_interpretation theta ->
    is_erased_term t.
Proof.
  intros theta t T H1 H2.
  pose proof (reducible_values_props theta t T term_var H1 H2); steps.
Qed.

Hint Immediate reducible_values_erased: erased.

Lemma reducible_erased:
  forall theta t T,
    reducible theta t T ->
    valid_interpretation theta ->
    is_erased_term t.
Proof.
  unfold reducible, reduces_to, closed_term; steps.
Qed.

Hint Immediate reducible_erased: erased.

Lemma reducible_val_fv:
  forall theta t T tag,
    reducible_values theta t T ->
    valid_interpretation theta ->
    pfv t tag = nil.
Proof.
  intros theta t T tag H1 H2.
  pose proof (reducible_values_props theta t T tag H1 H2); steps.
Qed.

Hint Immediate reducible_val_fv: fv.

Lemma fv_red:
  forall t x tag theta T,
    valid_interpretation theta ->
    reducible_values theta t T ->
    x ∈ pfv t tag ->
    False.
Proof.
  intros; erewrite reducible_val_fv in *; eauto; steps.
Qed.

Ltac t_fv_red :=
  match goal with
  | H1: valid_interpretation ?theta, H2: reducible_values ?theta ?t _, H3: _ ∈ pfv ?t _ |- _ =>
    apply False_ind; apply (fv_red _ _ _ _ _ H1 H2 H3)
  end.

Lemma reducible_val_wf:
  forall theta t T k,
    reducible_values theta t T ->
    valid_interpretation theta ->
    wf t k.
Proof.
  intros theta t T k H1 H2.
  pose proof (reducible_values_props theta t T term_var H1 H2); steps; eauto with wf.
Qed.

Hint Immediate reducible_val_wf: wf.

Lemma reducible_val_twf:
  forall theta t T k,
    reducible_values theta t T ->
    valid_interpretation theta ->
    twf t k.
Proof.
  intros theta t T k H1 H2.
  pose proof (reducible_values_props theta t T term_var H1 H2); steps;
    eauto using is_erased_term_twf.
Qed.

Hint Immediate reducible_val_twf: twf.

Lemma red_is_val:
  forall theta v T,
    reducible_values theta v T ->
    valid_interpretation theta ->
    cbv_value v.
Proof.
  intros theta t T H1 H2.
  pose proof (reducible_values_props theta t T term_var H1 H2); steps.
Qed.

Hint Immediate red_is_val: values.

Lemma red_irred:
  forall theta v T,
    valid_interpretation theta ->
    reducible_values theta v T ->
    irred v.
Proof.
  eauto using red_is_val, value_irred.
Qed.

Lemma reducible_normalizing:
  forall theta e T,
    valid_interpretation theta ->
    reducible theta e T ->
    scbv_normalizing e.
Proof.
  unfold reducible, reduces_to, closed_term, scbv_normalizing; destruct T; steps;
    eauto using red_is_val with fv wf.
Qed.

Ltac t_red :=
  match goal with
         | _ => deterministic_step || step
         | _ => progress (simp reducible in *)
         | H1: scbv_step ?t1 _,
           H2: star scbv_step ?t1 _ |- _ => inversion H2; clear H2
         | _ => progress (autounfold with props in *)
         | _ => progress (autorewrite with bsize in *)
         | _ => progress (autorewrite with bsem in *)
         end.

Ltac t_reduction :=
  repeat
    t_red ||
    unshelve eauto 3 with smallstep;
      try omega;
      eauto 2 with wf;
      eauto 2 with fv.

Ltac t_values_info2 :=
  match goal with
  | H1: valid_interpretation ?theta, H2: reducible_values ?theta ?t ?T  |- _ =>
    poseNew (Mark t "redvalval");
    pose proof (red_is_val _ _ _ H2 H1)
  end.

Lemma smallstep_reducible_aux:
  forall n theta t T,
    type_nodes T < n ->
    valid_interpretation theta ->
    reducible theta t T ->
    forall t',
      scbv_step t t' ->
      reducible theta t' T.
Proof.
  unfold reducible; unfold reduces_to, closed_term;
    steps;
    eauto 2 with wf;
    eauto 2 with fv;
    eauto with erased.

  repeat match goal with
         | H: star scbv_step _ ?t |- _ => exists t
         | H1: star scbv_step ?t _, H2: scbv_step ?t _ |- _ =>
            poseNew (Mark 0 "inversion");
            inversion H1
         | H1: reducible_values _ ?v _,
           H2: scbv_step ?v ?t |- _ =>
              apply False_ind; apply evaluate_step with v t; eauto 4 with values
         | _ => step || deterministic_step
         end;
    eauto using red_is_val.
Qed.

Lemma smallstep_reducible:
  forall theta t t' T,
    valid_interpretation theta ->
    scbv_step t t' ->
    reducible theta t T ->
    reducible theta t' T.
Proof.
  eauto using smallstep_reducible_aux.
Qed.

Lemma star_smallstep_reducible:
  forall t t',
    star scbv_step t t' ->
    forall theta T,
      valid_interpretation theta ->
      reducible theta t T ->
      reducible theta t' T.
Proof.
  induction 1; steps; eauto using smallstep_reducible.
Qed.

Lemma backstep_reducible_aux:
  forall n theta t' T,
    type_nodes T < n ->
    valid_interpretation theta ->
    reducible theta t' T ->
    forall t,
      pfv t term_var = nil ->
      wf t 0 ->
      is_erased_term t ->
      scbv_step t t' ->
      reducible theta t T.
Proof.
  unfold reducible; unfold reduces_to, closed_term; steps; eauto with star.
Qed.

Lemma backstep_reducible:
  forall theta t t' T,
    valid_interpretation theta ->
    scbv_step t t' ->
    pfv t term_var = nil ->
    wf t 0 ->
    is_erased_term t ->
    reducible theta t' T ->
    reducible theta t T.
Proof.
  eauto using backstep_reducible_aux.
Qed.

Lemma star_backstep_reducible:
  forall t t' theta,
    star scbv_step t t' ->
    valid_interpretation theta ->
    pfv t term_var = nil ->
    wf t 0 ->
    is_erased_term t ->
    forall T,
      reducible theta t' T ->
      reducible theta t T.
Proof.
  induction 1; steps; eauto 7 using backstep_reducible with fv wf erased.
Qed.

Lemma reducible_values_exprs:
  forall theta t T T',
    valid_interpretation theta ->
    (forall t, reducible_values theta t T -> reducible_values theta t T') ->
    reducible theta t T ->
    reducible theta t T'.
Proof.
  unfold reducible, reduces_to; steps; eauto.
Qed.

Ltac use_red_ind :=
  match goal with
  | H1: forall T v t t', _,
    H2: scbv_step ?t1 ?t2 |- reducible_values ?v (open 0 ?T ?t1) =>
      unshelve epose proof (H1 T v t1 t2  _ _ _)
  | H1: forall T v t t', _,
    H2: scbv_step ?t1 ?t2 |- reducible_values ?v (open 0 ?T ?t2) =>
      unshelve epose proof (H1 T v t1 t2  _ _ _)
  end.

Ltac guess_red :=
  match goal with
  | H: star scbv_step ?t1 ?t2 |- exists t, star scbv_step ?t1 t /\ _ =>
    exists t2
  end.

Fixpoint are_values (l: list (nat * tree)) :=
  match l with
  | nil => True
  | (x,v) :: l' => cbv_value v /\ are_values l'
  end.

Lemma reducible_values_list:
  forall theta l gamma,
    valid_interpretation theta ->
    satisfies (reducible_values theta) gamma l ->
    are_values l.
Proof.
  induction l; repeat step || step_inversion satisfies; eauto using red_is_val.
Qed.

Hint Immediate reducible_values_list: values.

Lemma reducible_expr_value:
  forall theta v T,
    cbv_value v ->
    reducible theta v T ->
    reducible_values theta v T.
Proof.
  unfold reducible, reduces_to; repeat step || t_invert_star.
Qed.

Lemma reducible_wf:
  forall theta t T k,
    reducible theta t T -> wf t k.
Proof.
  unfold reducible, reduces_to, closed_term; steps; eauto with wf.
Qed.

Hint Immediate reducible_wf: wf.

Lemma reducible_twf:
  forall theta t T k,
    reducible theta t T -> twf t k.
Proof.
  unfold reducible, reduces_to, closed_term; steps; eauto using is_erased_term_twf.
Qed.

Hint Immediate reducible_twf: twf.

Lemma reducible_fv:
  forall theta t T tag, reducible theta t T -> pfv t tag = nil.
Proof.
  destruct tag; unfold reducible, reduces_to, closed_term; steps; eauto using is_erased_term_tfv.
Qed.

Hint Immediate reducible_fv: fv.

Lemma reducible_value_expr:
  forall theta t T,
    valid_interpretation theta ->
    reducible_values theta t T ->
    reducible theta t T.
Proof.
  unfold reducible, reduces_to, closed_term; steps;
    eauto with wf;
    eauto with fv;
    eauto with star;
    eauto with erased.
Qed.

Lemma reduces_to_value:
  forall theta T t v,
    reduces_to (fun v => reducible_values theta v T) t ->
    valid_interpretation theta ->
    cbv_value v ->
    star scbv_step t v ->
    reducible_values theta v T.
Proof.
  unfold reduces_to;
    repeat step || t_deterministic_star;
    eauto using red_is_val.
Qed.
