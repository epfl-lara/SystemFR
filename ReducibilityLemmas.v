Require Import Coq.Strings.String.

Require Import Equations.Equations.

Require Export SystemFR.StarLemmas.
Require Export SystemFR.StarInversions.
Require Export SystemFR.ErasedTermLemmas.

Require Export SystemFR.FVLemmasEval.
Require Export SystemFR.WFLemmasEval.
Require Export SystemFR.TWFLemmas.

Require Export SystemFR.ReducibilityDefinition.

Require Import Psatz.

Opaque reducible_values. (* workaround for rewriting speed *)

Lemma reducible_values_closed:
  forall ρ v T,
    [ ρ ⊨ v : T ]v ->
    valid_interpretation ρ ->
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
  | H1: valid_interpretation ?ρ, H2: [ ?ρ ⊨ ?v : ?T ]v |- _ =>
      poseNew (Mark v "reducible_values_closed");
      pose proof (reducible_values_closed _ _ _ H2 H1)
  end.

Lemma reducible_values_props:
  forall ρ v T tag,
    [ ρ ⊨ v : T ]v ->
    valid_interpretation ρ ->
      (is_erased_term v /\ pfv v tag = nil /\ wf v 0 /\ cbv_value v).
Proof.
  intros ρ v T tag H1 H2; destruct tag;
    pose proof (reducible_values_closed ρ v T H1 H2);
    unfold closed_value, closed_term in *; steps;
      eauto using is_erased_term_tfv.
Qed.

Lemma reducible_values_erased:
  forall ρ v T,
    [ ρ ⊨ v : T ]v ->
    valid_interpretation ρ ->
    is_erased_term v.
Proof.
  intros ρ v T H1 H2.
  pose proof (reducible_values_props ρ v T term_var H1 H2); steps.
Qed.

Hint Immediate reducible_values_erased: erased.

Lemma reducible_erased:
  forall ρ v T,
    [ ρ ⊨ v : T ] ->
    valid_interpretation ρ ->
    is_erased_term v.
Proof.
  unfold reduces_to, closed_term; steps.
Qed.

Hint Immediate reducible_erased: erased.

Lemma reducible_val_fv:
  forall ρ v T tag,
    [ ρ ⊨ v : T ]v ->
    valid_interpretation ρ ->
    pfv v tag = nil.
Proof.
  intros ρ v T tag H1 H2.
  pose proof (reducible_values_props ρ v T tag H1 H2); steps.
Qed.

Hint Immediate reducible_val_fv: fv.

Lemma fv_red:
  forall v x tag ρ T,
    valid_interpretation ρ ->
    [ ρ ⊨ v : T ]v ->
    x ∈ pfv v tag ->
    False.
Proof.
  intros; erewrite reducible_val_fv in *; eauto; steps.
Qed.

Ltac t_fv_red :=
  match goal with
  | H1: valid_interpretation ?ρ, H2: [ ?ρ ⊨ ?t : _ ]v, H3: _ ∈ pfv ?t _ |- _ =>
    apply False_ind; apply (fv_red _ _ _ _ _ H1 H2 H3)
  end.

Lemma reducible_val_wf:
  forall ρ v T k,
    [ ρ ⊨ v : T ]v ->
    valid_interpretation ρ ->
    wf v k.
Proof.
  intros ρ v T k H1 H2.
  pose proof (reducible_values_props ρ v T term_var H1 H2); steps; eauto with wf.
Qed.

Hint Immediate reducible_val_wf: wf.

Lemma reducible_val_twf:
  forall ρ v T k,
    [ ρ ⊨ v : T ]v ->
    valid_interpretation ρ ->
    twf v k.
Proof.
  intros ρ v T k H1 H2.
  pose proof (reducible_values_props ρ v T term_var H1 H2); steps;
    eauto using is_erased_term_twf.
Qed.

Hint Immediate reducible_val_twf: twf.

Lemma red_is_val:
  forall ρ v T,
    [ ρ ⊨ v : T ]v ->
    valid_interpretation ρ ->
    cbv_value v.
Proof.
  intros ρ v T H1 H2.
  pose proof (reducible_values_props ρ v T term_var H1 H2); steps.
Qed.

Hint Immediate red_is_val: values.

Lemma red_irred:
  forall ρ v T,
    valid_interpretation ρ ->
    [ ρ ⊨ v : T ]v ->
    irred v.
Proof.
  eauto using red_is_val, value_irred.
Qed.

Lemma reducible_normalizing:
  forall ρ e T,
    valid_interpretation ρ ->
    [ ρ ⊨ e : T ] ->
    scbv_normalizing e.
Proof.
  unfold reduces_to, closed_term, scbv_normalizing; destruct T; steps;
    eauto using red_is_val with fv wf.
Qed.

Ltac t_red :=
  match goal with
         | _ => deterministic_step || step
         | _ => progress (simp reducible in *)
         | H1: ?t1 ~> _,
           H2: ?t1 ~>* _ |- _ => inversion H2; clear H2
         | _ => progress (autounfold with props in *)
         | _ => progress (autorewrite with bsize in *)
         | _ => progress (autorewrite with bsem in *)
         end.

Ltac t_reduction :=
  repeat
    t_red ||
    unshelve eauto 3 with smallstep;
      try lia;
      eauto 2 with wf;
      eauto 2 with fv.

Ltac t_values_info2 :=
  match goal with
  | H1: valid_interpretation ?ρ, H2: [ ?ρ ⊨ ?t : ?T ]v  |- _ =>
    poseNew (Mark t "redvalval");
    pose proof (red_is_val _ _ _ H2 H1)
  end.

Lemma smallstep_reducible_aux:
  forall n ρ t T,
    type_nodes T < n ->
    valid_interpretation ρ ->
    [ ρ ⊨ t : T ] ->
    forall t',
      t ~> t' ->
      [ ρ ⊨ t' : T ].
Proof.
  unfold reduces_to, closed_term;
    steps;
    eauto 2 with wf;
    eauto 2 with fv;
    eauto with erased.

  repeat match goal with
         | H: _ ~>* ?t |- _ => exists t
         | H1: ?t ~>* _, H2: ?t ~> _ |- _ =>
            poseNew (Mark 0 "inversion");
            inversion H1
         | H1: [ _ ⊨ ?v : _ ]v,
           H2: ?v ~> ?t |- _ =>
              apply False_ind; apply evaluate_step with v t; eauto 4 with values
         | _ => step || deterministic_step
         end;
    eauto using red_is_val.
Qed.

Lemma smallstep_reducible:
  forall ρ t t' T,
    valid_interpretation ρ ->
    t ~> t' ->
    [ ρ ⊨ t : T ] ->
    [ ρ ⊨ t' : T ].
Proof.
  eauto using smallstep_reducible_aux.
Qed.

Lemma star_smallstep_reducible:
  forall t t',
    t ~>* t' ->
    forall ρ T,
      valid_interpretation ρ ->
      [ ρ ⊨ t : T ] ->
      [ ρ ⊨ t' : T ].
Proof.
  induction 1; steps; eauto using smallstep_reducible.
Qed.

Lemma backstep_reducible_aux:
  forall n ρ t' T,
    type_nodes T < n ->
    valid_interpretation ρ ->
    [ ρ ⊨ t' : T ] ->
    forall t,
      pfv t term_var = nil ->
      wf t 0 ->
      is_erased_term t ->
      t ~> t' ->
      [ ρ ⊨ t : T ].
Proof.
  unfold reduces_to, closed_term; steps; eauto with star.
Qed.

Lemma backstep_reducible:
  forall ρ t t' T,
    valid_interpretation ρ ->
    t ~> t' ->
    pfv t term_var = nil ->
    wf t 0 ->
    is_erased_term t ->
    [ ρ ⊨ t' : T ] ->
    [ ρ ⊨ t : T ].
Proof.
  eauto using backstep_reducible_aux.
Qed.

Lemma star_backstep_reducible:
  forall t t' ρ,
    t ~>* t' ->
    valid_interpretation ρ ->
    pfv t term_var = nil ->
    wf t 0 ->
    is_erased_term t ->
    forall T,
      [ ρ ⊨ t' : T ] ->
      [ ρ ⊨ t : T ].
Proof.
  induction 1; steps; eauto 7 using backstep_reducible with fv wf erased.
Qed.

Lemma reducible_values_exprs:
  forall ρ t T T',
    valid_interpretation ρ ->
    (forall v, [ ρ ⊨ v : T ]v -> [ ρ ⊨ v : T' ]v) ->
    [ ρ ⊨ t : T ] ->
    [ ρ ⊨ t : T' ].
Proof.
  unfold reduces_to; steps; eauto.
Qed.

Ltac guess_red :=
  match goal with
  | H: ?t1 ~>* ?t2 |- exists t, ?t1 ~>* t /\ _ =>
    exists t2
  end.

Fixpoint are_values (l: list (nat * tree)) :=
  match l with
  | nil => True
  | (x,v) :: l' => cbv_value v /\ are_values l'
  end.

Lemma reducible_values_list:
  forall ρ l Γ,
    valid_interpretation ρ ->
    satisfies (reducible_values ρ) Γ l ->
    are_values l.
Proof.
  induction l; repeat step || step_inversion satisfies; eauto using red_is_val.
Qed.

Hint Immediate reducible_values_list: values.

Lemma reducible_expr_value:
  forall ρ v T,
    cbv_value v ->
    [ ρ ⊨ v : T ] ->
    [ ρ ⊨ v : T ]v.
Proof.
  unfold reduces_to; repeat step || t_invert_star.
Qed.

Lemma reducible_wf:
  forall ρ t T k,
    [ ρ ⊨ t : T ] -> wf t k.
Proof.
  unfold reduces_to, closed_term; steps; eauto with wf.
Qed.

Hint Immediate reducible_wf: wf.

Lemma reducible_twf:
  forall ρ t T k,
    [ ρ ⊨ t : T ] -> twf t k.
Proof.
  unfold reduces_to, closed_term; steps; eauto using is_erased_term_twf.
Qed.

Hint Immediate reducible_twf: twf.

Lemma reducible_fv:
  forall ρ t T tag, [ ρ ⊨ t : T ] -> pfv t tag = nil.
Proof.
  destruct tag; unfold reduces_to, closed_term; steps; eauto using is_erased_term_tfv.
Qed.

Hint Immediate reducible_fv: fv.

Lemma reducible_value_expr:
  forall ρ v T,
    valid_interpretation ρ ->
    [ ρ ⊨ v : T ]v ->
    [ ρ ⊨ v : T ].
Proof.
  unfold reduces_to, closed_term; steps;
    eauto with wf;
    eauto with fv;
    eauto with star;
    eauto with erased.
Qed.

Lemma reduces_to_value:
  forall ρ T t v,
    reduces_to (fun v => [ ρ ⊨ v : T ]v) t ->
    valid_interpretation ρ ->
    cbv_value v ->
    t ~>* v ->
    [ ρ ⊨ v : T ]v.
Proof.
  unfold reduces_to;
    repeat step || t_deterministic_star;
    eauto using red_is_val.
Qed.
