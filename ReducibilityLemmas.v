Require Import Coq.Strings.String.

Require Import Equations.Equations.

Require Import SystemFR.AssocList.
Require Import SystemFR.Tactics.
Require Import SystemFR.Syntax.
Require Import SystemFR.SmallStep.
Require Import SystemFR.TermProperties.
Require Import SystemFR.SizeLemmas.
Require Import SystemFR.SubstitutionLemmas.
Require Import SystemFR.SmallStepIrredLemmas.
Require Import SystemFR.TermList.
Require Import SystemFR.ListUtils.
Require Import SystemFR.SizeLemmas.
Require Import SystemFR.SmallStepSubstitutions.
Require Import SystemFR.StarLemmas.
Require Import SystemFR.StarInversions.
Require Import SystemFR.ErasedTermLemmas.
Require Import SystemFR.Trees.
Require Import SystemFR.Sets.
Require Import SystemFR.StarRelation.

Require Import SystemFR.FVLemmas.
Require Import SystemFR.FVLemmasEval.

Require Import SystemFR.WFLemmas.
Require Import SystemFR.WFLemmasEval.
Require Import SystemFR.TWFLemmas.

Require Import SystemFR.ReducibilityCandidate.
Require Import SystemFR.ReducibilityDefinition.

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
      eauto using in_valid_interpretation_erased with berased;
      eauto using in_valid_interpretation_pfv with bfv;
      eauto using in_valid_interpretation_wf with bwf;
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
      (is_erased_term t /\ pfv t tag = nil /\ wf t 0 /\ is_value t).
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

Hint Resolve reducible_values_erased: berased.

Lemma reducible_erased:
  forall theta t T,
    reducible theta t T ->
    valid_interpretation theta ->
    is_erased_term t.
Proof.
  unfold reducible, reduces_to, closed_term; steps.
Qed.

Hint Resolve reducible_erased: berased.

Lemma reducible_val_fv:
  forall theta t T tag,
    reducible_values theta t T ->
    valid_interpretation theta ->
    pfv t tag = nil.
Proof.
  intros theta t T tag H1 H2.
  pose proof (reducible_values_props theta t T tag H1 H2); steps.
Qed.

Hint Resolve reducible_val_fv: bfv.

Lemma fv_in_reducible_val:
  forall theta v T x tag,
    reducible_values theta v T ->
    valid_interpretation theta ->
    x ∈ pfv v tag ->
    False.
Proof.
  intros. erewrite reducible_val_fv in *; eauto.
Qed.

Lemma reducible_val_wf:
  forall theta t T,
    reducible_values theta t T ->
    valid_interpretation theta ->
    wf t 0.
Proof.
  intros theta t T H1 H2.
  pose proof (reducible_values_props theta t T term_var H1 H2); steps.
Qed.

Hint Resolve reducible_val_wf: bwf.

Lemma reducible_val_twf:
  forall theta t T,
    reducible_values theta t T ->
    valid_interpretation theta ->
    twf t 0.
Proof.
  intros theta t T H1 H2.
  pose proof (reducible_values_props theta t T term_var H1 H2); steps;
    eauto using is_erased_term_twf.
Qed.

Hint Resolve reducible_val_twf: btwf.

Lemma red_is_val:
  forall theta v T,
    reducible_values theta v T ->
    valid_interpretation theta ->
    is_value v.
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
    normalizing e.
Proof.
  unfold reducible, reduces_to, closed_term, normalizing; destruct T; steps;
    eauto using red_is_val with bfv bwf.
Qed.

Ltac t_red :=
  match goal with
         | _ => t_deterministic_step || step
         | _ => progress (simp reducible in *)
         | H1: small_step ?t1 _,
           H2: star small_step ?t1 _ |- _ => inversion H2; clear H2
         | _ => progress (autounfold with props in *)
         | _ => progress (autorewrite with bsize in *)
         | _ => progress (autorewrite with bsem in *)
         end.

Ltac t_reduction :=
  repeat
    t_red ||
    unshelve eauto 3 with smallstep;
      try omega;
      eauto 2 with bwf;
      eauto 2 with bfv.

Ltac t_red_irred :=
  match goal with
  | H1: star small_step ?t ?t1,
    H2: star small_step ?t ?t2,
    H3: irred ?t1 |- _ =>
    poseNew (Mark (t1,t2) "equality");
    unshelve epose proof (star_smallstep_irred2 _ _ H1 _ H2 H3 _)
  end.

Ltac t_values_info2 :=
  match goal with
(*  | H: is_value ?v, H2: context[erase ?v] |- _ =>
    poseNew (Mark v "erase_value");
    pose proof (erase_value v H) *)
  | H1: valid_interpretation ?theta, H2: reducible_values ?theta ?t ?T  |- _ =>
    poseNew (Mark t "redvalval");
    pose proof (red_is_val _ _ _ H2 H1)
  end.

Lemma smallstep_reducible_aux:
  forall n theta t T,
    size T < n ->
    valid_interpretation theta ->
    reducible theta t T ->
    forall t',
      small_step t t' ->
      reducible theta t' T.
Proof.
  unfold reducible; unfold reduces_to, closed_term;
    steps;
    eauto 2 with bwf;
    eauto 2 with bfv;
    eauto with berased.

  repeat match goal with
         | H: star small_step _ ?t |- _ => exists t
         | H1: star small_step ?t _, H2: small_step ?t _ |- _ =>
            poseNew (Mark 0 "inversion");
            inversion H1
         | H1: reducible_values _ ?v _,
           H2: small_step ?v ?t |- _ =>
              apply False_ind; apply evaluate_step with v t; eauto 4 with values
         | _ => step || t_deterministic_step
         end;
    eauto using red_is_val.
Qed.

Lemma smallstep_reducible:
  forall theta t t' T,
    valid_interpretation theta ->
    small_step t t' ->
    reducible theta t T ->
    reducible theta t' T.
Proof.
  eauto using smallstep_reducible_aux.
Qed.

Lemma star_smallstep_reducible:
  forall t t',
    star small_step t t' ->
    forall theta T,
      valid_interpretation theta ->
      reducible theta t T ->
      reducible theta t' T.
Proof.
  induction 1; steps; eauto using smallstep_reducible.
Qed.

Lemma backstep_reducible_aux:
  forall n theta t' T,
    size T < n ->
    valid_interpretation theta ->
    reducible theta t' T ->
    forall t,
      pfv t term_var = nil ->
      wf t 0 ->
      is_erased_term t ->
      small_step t t' ->
      reducible theta t T.
Proof.
  unfold reducible; unfold reduces_to, closed_term; steps; eauto with smallstep.
Qed.

Lemma backstep_reducible:
  forall theta t t' T,
    valid_interpretation theta ->
    small_step t t' ->
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
    star small_step t t' ->
    valid_interpretation theta ->
    pfv t term_var = nil ->
    wf t 0 ->
    is_erased_term t ->
    forall T,
      reducible theta t' T ->
      reducible theta t T.
Proof.
  induction 1; steps; eauto 7 using backstep_reducible with bfv bwf berased.
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
    H2: small_step ?t1 ?t2 |- reducible_values ?v (open 0 ?T ?t1) =>
      unshelve epose proof (H1 T v t1 t2  _ _ _)
  | H1: forall T v t t', _,
    H2: small_step ?t1 ?t2 |- reducible_values ?v (open 0 ?T ?t2) =>
      unshelve epose proof (H1 T v t1 t2  _ _ _)
  end.

Ltac guess_red :=
  match goal with
  | H: star small_step ?t1 ?t2 |- exists t, star small_step ?t1 t /\ _ =>
    exists t2
  end.

Lemma reducible_values_list:
  forall theta l gamma,
    valid_interpretation theta ->
    satisfies (reducible_values theta) gamma l ->
    are_values l.
Proof.
  induction l; repeat step || step_inversion satisfies; eauto using red_is_val.
Qed.

Hint Resolve reducible_values_list: values.

Lemma reducible_expr_value:
  forall theta v T,
    is_value v ->
    reducible theta v T ->
    reducible_values theta v T.
Proof.
  unfold reducible, reduces_to; repeat step || t_invert_star.
Qed.

Lemma reducible_wf:
  forall theta t T,
    reducible theta t T -> wf t 0.
Proof.
  unfold reducible, reduces_to, closed_term; steps.
Qed.

Hint Resolve reducible_wf: bwf.

Lemma reducible_twf:
  forall theta t T,
    reducible theta t T -> twf t 0.
Proof.
  unfold reducible, reduces_to, closed_term; steps; eauto using is_erased_term_twf.
Qed.

Hint Resolve reducible_twf: btwf.

Lemma reducible_fv:
  forall theta t T tag, reducible theta t T -> pfv t tag = nil.
Proof.
  destruct tag; unfold reducible, reduces_to, closed_term; steps; eauto using is_erased_term_tfv.
Qed.

Hint Resolve reducible_fv: bfv.

Lemma reducible_value_expr:
  forall theta t T,
    valid_interpretation theta ->
    reducible_values theta t T ->
    reducible theta t T.
Proof.
  unfold reducible, reduces_to, closed_term; steps;
    eauto with bwf;
    eauto with bfv;
    eauto with smallstep;
    eauto with berased.
Qed.

Ltac t_values_info3 :=
  match goal with
  | H: is_value ?v, H2: satisfies _ _ ?l |- _ =>
    is_var v;
    poseNew (Mark (v,l) "is_value_subst");
    unshelve epose proof (is_value_subst _ H l _); eauto 2 using reducible_values_list
  end.

Lemma reducibility_is_candidate:
  forall (theta : interpretation) V,
    valid_interpretation theta ->
    reducibility_candidate (fun v => reducible_values theta v V).
Proof.
  unfold reducibility_candidate; steps;
    eauto with bwf bfv;
    eauto using red_is_val;
    eauto with berased.
Qed.
