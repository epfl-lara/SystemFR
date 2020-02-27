Require Export SystemFR.SubstitutionLemmas.
Require Export SystemFR.PrimitiveSize.
Require Export SystemFR.PrimitiveRecognizers.
Require Export SystemFR.SmallStep.
Require Export SystemFR.RelationClosures.

Lemma is_erased_term_twf:
  forall t k,
    is_erased_term t ->
    twf t k.
Proof.
  induction t; steps.
Qed.

Hint Immediate is_erased_term_twf: twf.

Lemma twf_open2:
  forall T k i v,
    twf T k ->
    closed_value v ->
    twf (open i T v) k.
Proof.
  unfold closed_value, closed_term; intros; apply twf_open; steps; eauto with twf.
Qed.

Hint Immediate twf_open2: twf.

Lemma is_erased_open:
  forall t k rep,
    is_erased_term t ->
    is_erased_term rep ->
    is_erased_term (open k t rep).
Proof.
  induction t; steps.
Qed.

Hint Resolve is_erased_open: erased.

Lemma is_erased_type_open:
  forall t k rep,
    is_erased_type t ->
    is_erased_term rep ->
    is_erased_type (open k t rep).
Proof.
  induction t; steps; eauto with erased.
Qed.

Hint Resolve is_erased_type_open: erased.

Lemma is_erased_type_open2:
  forall T i v,
    is_erased_type T ->
    closed_value v ->
    is_erased_type (open i T v).
Proof.
  unfold closed_value, closed_term; intros; apply is_erased_type_open; steps.
Qed.

Hint Immediate is_erased_type_open2: erased.

Lemma is_erased_type_topen:
  forall t k rep,
    is_erased_type t ->
    is_erased_type rep ->
    is_erased_type (topen k t rep).
Proof.
  induction t; repeat step || rewrite topen_none by eauto with twf.
Qed.

Hint Resolve is_erased_type_topen: erased.

Lemma is_erased_open2:
  forall t k rep,
    is_erased_term (open k t rep) ->
    is_erased_term t.
Proof.
  induction t; steps; eauto.
Qed.

Lemma is_erased_term_tfv:
  forall t,
    is_erased_term t ->
    pfv t type_var = nil.
Proof.
  induction t; repeat step || list_utils.
Qed.

Hint Immediate is_erased_term_tfv: fv.

Lemma is_erased_topen:
  forall t k rep,
    is_erased_term t ->
    is_erased_term rep ->
    is_erased_term (topen k t rep).
Proof.
  induction t; steps.
Qed.

Hint Resolve is_erased_topen: erased.

Lemma is_erased_topen2:
  forall t k rep,
    is_annotated_term t ->
    is_erased_term (topen k t rep) ->
    is_erased_term t.
Proof.
  induction t; steps; eauto.
Qed.

Lemma is_erased_term_tsize:
  forall n, is_erased_term (build_nat n).
Proof.
  eauto using is_nat_value_erased, is_nat_value_build_nat.
Qed.

Hint Immediate is_erased_term_tsize: erased.

Lemma is_erased_is_pair:
  forall v, is_erased_term (is_pair v).
Proof.
  destruct v; steps.
Qed.

Hint Immediate is_erased_is_pair: erased.

Lemma is_erased_is_succ:
  forall v, is_erased_term (is_succ v).
Proof.
  destruct v; steps.
Qed.

Hint Immediate is_erased_is_succ: erased.

Lemma is_erased_is_lambda:
  forall v, is_erased_term (is_lambda v).
Proof.
  destruct v; steps.
Qed.

Hint Immediate is_erased_is_lambda: erased.

Lemma erase_scbv_step:
  forall t1 t2,
    scbv_step t1 t2 ->
    is_erased_term t1 ->
    is_erased_term t2.
Proof.
  induction 1; steps; eauto 3 using is_erased_open with step_tactic;
    eauto with erased.
Qed.

Hint Immediate erase_scbv_step: erased.

Lemma erase_star_scbv_step:
  forall t1 t2,
    star scbv_step t1 t2 ->
    is_erased_term t1 ->
    is_erased_term t2.
Proof.
  induction 1; steps; eauto using erase_scbv_step.
Qed.

Hint Immediate erase_star_scbv_step: erased.

Lemma is_erased_subst:
  forall t l,
    is_erased_term t ->
    psubstitute t l type_var = t.
Proof.
  intros; rewrite substitute_nothing5; eauto with fv.
Qed.

Lemma is_erased_term_type:
  forall t,
    is_erased_term t ->
    is_erased_type t ->
    False.
Proof.
  destruct t; steps.
Qed.

Lemma is_erased_term_tclose:
  forall t X k,
    is_erased_term t ->
    is_erased_term (tclose k t X).
Proof.
  induction t;
    repeat step;
    eauto.
Qed.

Lemma is_erased_type_tclose:
  forall T X k,
    is_erased_type T ->
    is_erased_type (tclose k T X).
Proof.
  induction T;
    repeat step;
    eauto using is_erased_term_tclose.
Qed.
