Require Import SystemFR.Syntax.
Require Import SystemFR.Tactics.
Require Import SystemFR.PrimitiveSize.
Require Import SystemFR.StarRelation.

Inductive is_value: tree -> Prop :=
| IVUnit: is_value uu
| IVZero: is_value zero
| IVSucc: forall v, is_value v -> is_value (succ v)
| IVFalse: is_value tfalse
| IVTrue: is_value ttrue
| IVPair: forall v1 v2, is_value v1 -> is_value v2 -> is_value (pp v1 v2)
| IVLambda: forall t, is_value (notype_lambda t)
| IVTypeAbs: forall t, is_value (type_abs t)
| IVVar: forall x, is_value (fvar x term_var)
| IVFold: forall v, is_value v -> is_value (notype_tfold v)
| IVLeft: forall v, is_value v -> is_value (tleft v)
| IVRight: forall v, is_value v -> is_value (tright v)
.

Hint Constructors is_value: values.

Inductive is_nat_value: tree -> Prop :=
| INVZero: is_nat_value zero
| INVSucc: forall v, is_nat_value v -> is_nat_value (succ v).

Hint Constructors is_nat_value: b_inv.

Ltac t_is_value t :=
  unify t zero ||
  unify t uu ||
  unify t tfalse ||
  unify t ttrue ||
  match goal with
  | H: is_value t |- _ => idtac
  | H: is_nat_value t |- _ => idtac
  | _ => match t with
        | succ ?v => t_is_value v
        | pp ?v1 ?v2 => t_is_value v1; t_is_value v2
        | fvar _ term_var => idtac
        | notype_lambda _ => idtac
        | notype_tfold ?v => t_is_value v
        | tleft ?v => t_is_value v
        | tright ?v => t_is_value v
        end
  end.

Ltac t_invert_nat_value :=
  match goal with
  | H: is_nat_value _ |- _ => inversion H
  end.

Lemma is_nat_value_build_nat:
  forall n, is_nat_value (build_nat n).
Proof.
  induction n; steps; eauto with b_inv.
Qed.

Inductive small_step: tree -> tree -> Prop :=
(* beta reduction *)
| SPBetaProj1: forall v1 v2,
    is_value v1 ->
    is_value v2 ->
    small_step (pi1 (pp v1 v2)) v1
| SPBetaProj2: forall v1 v2,
    is_value v1 ->
    is_value v2 ->
    small_step (pi2 (pp v1 v2)) v2

| SPBetaApp: forall t v,
    is_value v ->
    small_step
      (app (notype_lambda t) v)
      (open 0 t v)

| SPBetaTypeInst: forall t,
    small_step (notype_inst (type_abs t)) t

| SPBetaLet: forall t v,
    is_value v ->
    small_step
      (notype_tlet v t)
      (open 0 t v)

| SPBetaIte1: forall t1 t2,
    small_step (ite ttrue t1 t2) t1
| SPBetaIte2: forall t1 t2,
    small_step (ite tfalse t1 t2) t2

| SPBetaRec0: forall t0 ts,
    small_step
      (notype_rec zero t0 ts)
      t0
| SPBetaRecS: forall v t0 ts,
    is_value v ->
    small_step
      (notype_rec (succ v) t0 ts)
      (open 0 (open 1 ts v) (notype_lambda (notype_rec v t0 ts)))

(* `notype_tfix` has a dummy hole which is used for type annotation in the `tfix` tree.
   During evaluation, we fill it with a zero *)
| SPBetaFix: forall ts,
    small_step (notype_tfix ts) (open 0 (open 1 ts zero) (notype_lambda (notype_tfix ts)))

| SPBetaMatch0: forall t0 ts,
    small_step
      (tmatch zero t0 ts)
      t0
| SPBetaMatchS: forall v t0 ts,
    is_value v ->
    small_step
      (tmatch (succ v) t0 ts)
      (open 0 ts v)

| SPBetaMatchLeft: forall v tl tr,
    is_value v ->
    small_step (sum_match (tleft v) tl tr) (open 0 tl v)
| SPBetaMatchRight: forall v tl tr,
    is_value v ->
    small_step (sum_match (tright v) tl tr) (open 0 tr v)

| SPBetaFold:
    forall v, is_value v ->
         small_step (tunfold (notype_tfold v)) v
| SPBetaFold2:
    forall v t,
      is_value v ->
      small_step (tunfold_in (notype_tfold v) t) (open 0 t v)

| SPBetaSize:
    forall v,
      is_value v ->
      pfv v term_var = nil ->
      small_step (tsize v) (build_nat (tsize_semantics v))

(* reduction inside terms *)
| SPTypeInst: forall t1 t2,
    small_step t1 t2 ->
    small_step (notype_inst t1) (notype_inst t2)
| SPAppLeft: forall t1 t2 t,
    small_step t1 t2 ->
    small_step (app t1 t) (app t2 t)
| SPAppRight: forall t1 t2 v,
    is_value v ->
    small_step t1 t2 ->
    small_step (app v t1) (app v t2)
| SPPairL: forall t1 t2 t,
    small_step t1 t2 ->
    small_step (pp t1 t) (pp t2 t)
| SPPairR: forall t1 t2 v,
    small_step t1 t2 ->
    is_value v ->
    small_step (pp v t1) (pp v t2)
| SPProj1: forall t1 t2,
    small_step t1 t2 ->
    small_step (pi1 t1) (pi1 t2)
| SPProj2: forall t1 t2,
    small_step t1 t2 ->
    small_step (pi2 t1) (pi2 t2)

| SPSucc: forall t1 t2,
    small_step t1 t2 ->
    small_step (succ t1) (succ t2)
| SPRec: forall t1 t2 t0 ts,
    small_step t1 t2 ->
    small_step (notype_rec t1 t0 ts) (notype_rec t2 t0 ts)
| SPMatch: forall t1 t2 t0 ts,
    small_step t1 t2 ->
    small_step (tmatch t1 t0 ts) (tmatch t2 t0 ts)

| SPIte: forall t1 t1' t2 t3,
    small_step t1 t1' ->
    small_step (ite t1 t2 t3) (ite t1' t2 t3)
| SPLet: forall t1 t1' t2,
    small_step t1 t1' ->
    small_step (notype_tlet t1 t2) (notype_tlet t1' t2)

| SPFold: forall t1 t2,
    small_step t1 t2 ->
    small_step (notype_tfold t1) (notype_tfold t2)
| SPUnfold: forall t1 t2,
    small_step t1 t2 ->
    small_step (tunfold t1) (tunfold t2)
| SPUnfold2: forall t1 t2 t,
    small_step t1 t2 ->
    small_step (tunfold_in t1 t) (tunfold_in t2 t)

| SPLeft: forall t1 t2,
    small_step t1 t2 ->
    small_step (tleft t1) (tleft t2)
| SPRight: forall t1 t2,
    small_step t1 t2 ->
    small_step (tright t1) (tright t2)
| SPSumMatch: forall t1 t2 tl tr,
    small_step t1 t2 ->
    small_step (sum_match t1 tl tr) (sum_match t2 tl tr)

| SPTSize: forall t1 t2,
    small_step t1 t2 ->
    small_step (tsize t1) (tsize t2)
.

Hint Constructors small_step: smallstep.

Ltac t_invert_step :=
  match goal with
  | _ => step_inversion small_step
  | H: small_step (app _ _) _ |- _ => inversion H; clear H
  | H: small_step (notype_inst _) _ |- _ => inversion H; clear H
  | H: small_step (tunfold _) _ |- _ => inversion H; clear H
  | H: small_step (tunfold_in _ _) _ |- _ => inversion H; clear H
  | H: small_step (ite _ _ _) _ |- _ => inversion H; clear H
  | H: small_step (notype_rec _ _ _) _ |- _ => inversion H; clear H
  | H: small_step (tmatch _ _ _) _ |- _ => inversion H; clear H
  | H: small_step (pp _ _) _ |- _ => inversion H; clear H
  | H: small_step (notype_tlet _ _) _ |- _ => inversion H; clear H
  | H: small_step (pi1 _) _ |- _ => inversion H; clear H
  | H: small_step (pi2 _) _ |- _ => inversion H; clear H
  | H: small_step (sum_match _ _ _) _ |- _ => inversion H; clear H
  | H: small_step (tsize _) _ |- _ => inversion H; clear H
  end.

Lemma evaluate_step:
  forall v,
    is_value v ->
    forall t,
      small_step v t ->
      False.
Proof.
  induction 1;
    repeat
      step || step_inversion is_value || t_invert_step;
    eauto.
Qed.

Lemma evaluate_step2:
  forall t v,
    small_step v t ->
    is_value v ->
    False.
Proof.
  intros; eapply evaluate_step; eauto.
Qed.

Lemma evaluate_step3:
  forall t t',
    small_step t t' ->
    forall e,
      t = notype_lambda e ->
      False.
Proof.
  steps; t_invert_step.
Qed.

Lemma evaluate_step4:
  forall t t',
    small_step t t' ->
    forall e,
      t = type_abs e ->
      False.
Proof.
  steps; t_invert_step.
Qed.

Lemma is_nat_value_value:
  forall v,
    is_nat_value v ->
    is_value v.
Proof.
  induction 1; steps; eauto with values.
Qed.

Hint Immediate is_nat_value_value: values.

Lemma is_nat_value_erased:
  forall v,
    is_nat_value v ->
    is_erased_term v.
Proof.
  induction 1; steps.
Qed.

Hint Immediate is_nat_value_erased: berased.

Ltac t_nostep :=
  match goal with
  | H: is_value err |- _ => inversion H
  | H1: is_value ?v,
    H2: small_step ?v ?t |- _ =>
    apply False_ind; apply evaluate_step with v t; auto 2
  | H1: is_nat_value ?v,
    H2: small_step ?v ?t |- _ =>
    apply False_ind; apply evaluate_step with v t; eauto 2 with values
  | H1: is_value ?v1,
    H2: is_value ?v2,
    H3: small_step (pp ?v1 ?v2) ?t |- _ =>
    apply False_ind; apply evaluate_step with (pp v1 v2) t; auto with values
  | H1: is_value ?v,
    H3: small_step (succ ?v) ?t |- _ =>
    apply False_ind; apply evaluate_step with (succ v) t; auto with values
  | _ => t_invert_step; fail
  end.

Hint Immediate evaluate_step2: smallstep.
Hint Immediate evaluate_step3: smallstep.

Lemma deterministic_step:
  forall t1 t2,
    small_step t1 t2 ->
    forall t3,
      small_step t1 t3 ->
      t2 = t3.
Proof.
  induction 1; repeat step || t_equality;
    try solve [ repeat step || t_invert_step || t_nostep || t_equality ].
Qed.

Ltac t_deterministic_step :=
  match goal with
  | H1: small_step ?t1 ?t2,
    H2: small_step ?t1 ?t3 |- _ =>
    pose proof (deterministic_step _ _ H1 _ H2); clear H2
  end.

Hint Extern 50 => t_deterministic_step: smallstep.

Ltac hyp_value v :=
  match goal with
  | H: is_value v |- _ => idtac
  end.

Ltac t_not_hyp_value t := tryif hyp_value t then fail else idtac.

Definition closed_term t :=
  pfv t term_var = nil /\
  wf t 0 /\
  is_erased_term t.

Definition closed_value v :=
  closed_term v /\
  is_value v.
