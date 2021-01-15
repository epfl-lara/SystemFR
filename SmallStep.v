Require Import String.
Require Import Relations.

Require Export SystemFR.PrimitiveSize.
Require Export SystemFR.PrimitiveRecognizers.


Inductive cbv_value: tree -> Prop :=
| IVUnit: cbv_value uu
| IVZero: cbv_value zero
| IVSucc: forall v, cbv_value v -> cbv_value (succ v)
| IVFalse: cbv_value tfalse
| IVTrue: cbv_value ttrue
| IVPair: forall v1 v2, cbv_value v1 -> cbv_value v2 -> cbv_value (pp v1 v2)
| IVLambda: forall t, cbv_value (notype_lambda t)
| IVLeft: forall v, cbv_value v -> cbv_value (tleft v)
| IVRight: forall v, cbv_value v -> cbv_value (tright v)
.

#[global]
Hint Constructors cbv_value: values.

Inductive is_nat_value: tree -> Prop :=
| INVZero: is_nat_value zero
| INVSucc: forall v, is_nat_value v -> is_nat_value (succ v)
.

#[global]
Hint Constructors is_nat_value: is_nat_value.

Ltac cbv_value t :=
  match goal with
  | H: cbv_value t |- _ => idtac
  | H: is_nat_value t |- _ => idtac
  | _ => match t with
        | zero => idtac
        | uu => idtac
        | tfalse => idtac
        | ttrue => idtac
        | succ ?v => cbv_value v
        | pp ?v1 ?v2 => cbv_value v1; cbv_value v2
        | notype_lambda _ => idtac
        | tleft ?v => cbv_value v
        | tright ?v => cbv_value v
        | build_nat ?n => idtac
        end
  end.

Ltac not_cbv_value t := tryif cbv_value t then fail else idtac.

Ltac t_invert_nat_value :=
  match goal with
  | H: is_nat_value _ |- _ => inversion H
  end.


Lemma is_nat_value_buildable:
  forall v, is_nat_value v ->
    exists n, v = build_nat n.
Proof.
  induction 1; steps.
  - exists 0; steps.
  - exists (S n); steps.
Qed.


Ltac is_nat_value_buildable :=
  match goal with
  | H: is_nat_value ?v |- _ =>
    poseNew (Mark v "is_nat_value_buildable");
    pose proof (is_nat_value_buildable v H)
  end.


Lemma tree_size_build_nat:
  forall n, tree_size (build_nat n) = n.
Proof.
  induction n; steps.
Qed.

Lemma is_nat_value_build_nat:
  forall n, is_nat_value (build_nat n).
Proof.
  induction n; steps; eauto with is_nat_value.
Qed.

Lemma cbv_value_build_nat:
  forall n, cbv_value (build_nat n).
Proof.
  induction n; steps; eauto with values.
Qed.

Lemma cbv_value_is_pair:
  forall v, cbv_value (is_pair v).
Proof.
  destruct v; steps.
Qed.

Lemma cbv_value_is_succ:
  forall v, cbv_value (is_succ v).
Proof.
  destruct v; steps.
Qed.

Lemma cbv_value_is_lambda:
  forall v, cbv_value (is_lambda v).
Proof.
  destruct v; steps.
Qed.


#[global]
Hint Immediate is_nat_value_build_nat: values.
#[global]
Hint Immediate cbv_value_build_nat: values.
#[global]
Hint Immediate cbv_value_is_pair: values.
#[global]
Hint Immediate cbv_value_is_succ: values.
#[global]
Hint Immediate cbv_value_is_lambda: values.

Reserved Notation "t1 '~>' t2" (at level 20).

Inductive scbv_step: tree -> tree -> Prop :=
(* beta reduction *)
| SPBetaProj1: forall v1 v2,
    cbv_value v1 ->
    cbv_value v2 ->
    pi1 (pp v1 v2) ~> v1
| SPBetaProj2: forall v1 v2,
    cbv_value v1 ->
    cbv_value v2 ->
    pi2 (pp v1 v2) ~> v2

| SPBetaApp: forall t v,
    cbv_value v ->
    scbv_step
      (app (notype_lambda t) v)
      (open 0 t v)

| SPBetaIte1: forall t1 t2,
    ite ttrue t1 t2 ~> t1
| SPBetaIte2: forall t1 t2,
    ite tfalse t1 t2 ~> t2

(* `notype_tfix` has a dummy hole which is used for type annotation in the `tfix` tree.
   During evaluation, we fill it with a zero *)
| SPBetaFix: forall ts,
    notype_tfix ts ~> open 0 (open 1 ts zero) (notype_tfix ts)

| SPBetaMatch0: forall t0 ts,
    tmatch zero t0 ts ~> t0
| SPBetaMatchS: forall v t0 ts,
    cbv_value v ->
    tmatch (succ v) t0 ts ~> open 0 ts v

| SPBetaMatchLeft: forall v tl tr,
    cbv_value v ->
    sum_match (tleft v) tl tr ~> open 0 tl v
| SPBetaMatchRight: forall v tl tr,
    cbv_value v ->
    sum_match (tright v) tl tr ~> open 0 tr v

| SPBetaSize:
    forall v,
      cbv_value v ->
      tsize v ~> build_nat (tsize_semantics v)

| SPBetaIsPair:
    forall v,
      cbv_value v ->
      boolean_recognizer 0 v ~> is_pair v
| SPBetaIsSucc:
    forall v,
      cbv_value v ->
      boolean_recognizer 1 v ~> is_succ v
| SPBetaIsLambda:
    forall v,
      cbv_value v ->
      boolean_recognizer 2 v ~> is_lambda v

(* Primitive beta reduction *)
| SPBetaPlus: forall v1 v2 n1 n2,
    v1 = build_nat n1 ->
    v2 = build_nat n2 ->
    scbv_step (binary_primitive Plus v1 v2) (build_nat (n1 + n2))
| SPBetaMinus: forall v1 v2 n1 n2,
    v1 = build_nat n1 ->
    v2 = build_nat n2 ->
    n1 >= n2 ->
    scbv_step (binary_primitive Minus v1 v2) (build_nat (n1 - n2))
| SPBetaMul: forall v1 v2 n1 n2,
    v1 = build_nat n1 ->
    v2 = build_nat n2 ->
    scbv_step (binary_primitive Mul v1 v2) (build_nat (n1 * n2))
| SPBetaDiv: forall v1 v2 n1 n2,
    v1 = build_nat n1 ->
    v2 = build_nat n2 ->
    n2 > 0 ->
    scbv_step (binary_primitive Div v1 v2) (build_nat (PeanoNat.Nat.div n1 n2))
| SPBetaEq: forall v1 v2 n1 n2,
    v1 = build_nat n1 ->
    v2 = build_nat n2 ->
    scbv_step (binary_primitive Eq  v1 v2) (if PeanoNat.Nat.eqb n1 n2 then ttrue else tfalse)
| SPBetaNeq: forall v1 v2 n1 n2,
    v1 = build_nat n1 ->
    v2 = build_nat n2 ->
    scbv_step (binary_primitive Neq v1 v2) (if (PeanoNat.Nat.eq_dec n1 n2) then tfalse else ttrue)
| SPBetaLt: forall v1 v2 n1 n2,
    v1 = build_nat n1 ->
    v2 = build_nat n2 ->
    scbv_step (binary_primitive Lt  v1 v2) (if PeanoNat.Nat.ltb n1 n2 then ttrue else tfalse)
| SPBetaLeq: forall v1 v2 n1 n2,
    v1 = build_nat n1 ->
    v2 = build_nat n2 ->
    scbv_step (binary_primitive Leq v1 v2) (if PeanoNat.Nat.leb n1 n2 then ttrue else tfalse)
| SPBetaGt: forall v1 v2 n1 n2,
    v1 = build_nat n1 ->
    v2 = build_nat n2 ->
    scbv_step (binary_primitive Gt  v1 v2) (if PeanoNat.Nat.leb n1 n2 then tfalse else ttrue)
| SPBetaGeq: forall v1 v2 n1 n2,
    v1 = build_nat n1 ->
    v2 = build_nat n2 ->
    scbv_step (binary_primitive Geq v1 v2) (if PeanoNat.Nat.ltb n1 n2 then tfalse else ttrue)

| SPBetaNot1: scbv_step (unary_primitive Not ttrue) tfalse
| SPBetaNot2: scbv_step (unary_primitive Not tfalse) ttrue

| SPBetaAnd1: scbv_step (binary_primitive And ttrue ttrue) ttrue
| SPBetaAnd2: scbv_step (binary_primitive And ttrue tfalse) tfalse
| SPBetaAnd3: scbv_step (binary_primitive And tfalse ttrue) tfalse
| SPBetaAnd4: scbv_step (binary_primitive And tfalse tfalse) tfalse

| SPBetaOr1: scbv_step (binary_primitive Or tfalse tfalse) tfalse
| SPBetaOr2: scbv_step (binary_primitive Or tfalse ttrue) ttrue
| SPBetaOr3: scbv_step (binary_primitive Or ttrue tfalse) ttrue
| SPBetaOr4: scbv_step (binary_primitive Or ttrue ttrue) ttrue

(* reduction inside terms *)
| SPAppLeft: forall t1 t2 t,
    t1 ~> t2 ->
    app t1 t ~> app t2 t
| SPAppRight: forall t1 t2 v,
    cbv_value v ->
    t1 ~> t2 ->
    app v t1 ~> app v t2
| SPPairL: forall t1 t2 t,
    t1 ~> t2 ->
    pp t1 t ~> pp t2 t
| SPPairR: forall t1 t2 v,
    t1 ~> t2 ->
    cbv_value v ->
    pp v t1 ~> pp v t2
| SPProj1: forall t1 t2,
    t1 ~> t2 ->
    pi1 t1 ~> pi1 t2
| SPProj2: forall t1 t2,
    t1 ~> t2 ->
    pi2 t1 ~> pi2 t2

| SPSucc: forall t1 t2,
    t1 ~> t2 ->
    succ t1 ~> succ t2
| SPMatch: forall t1 t2 t0 ts,
    t1 ~> t2 ->
    tmatch t1 t0 ts ~> tmatch t2 t0 ts

| SPUnaryPrimitive: forall o t1 t2,
    scbv_step t1 t2 ->
    scbv_step (unary_primitive o t1) (unary_primitive o t2)
| SPBinaryPrimitive1: forall o t1 t2 t,
    scbv_step t1 t2 ->
    scbv_step (binary_primitive o t1 t) (binary_primitive o t2 t)
| SPBinaryPrimitive2: forall o v t1 t2,
    scbv_step t1 t2 ->
    cbv_value v ->
    scbv_step (binary_primitive o v t1) (binary_primitive o v t2)

| SPIte: forall t1 t1' t2 t3,
    t1 ~> t1' ->
    ite t1 t2 t3 ~> ite t1' t2 t3

| SPLeft: forall t1 t2,
    t1 ~> t2 ->
    tleft t1 ~> tleft t2
| SPRight: forall t1 t2,
    t1 ~> t2 ->
    tright t1 ~> tright t2
| SPSumMatch: forall t1 t2 tl tr,
    t1 ~> t2 ->
    sum_match t1 tl tr ~> sum_match t2 tl tr

| SPTSize: forall t1 t2,
    t1 ~> t2 ->
    tsize t1 ~> tsize t2

| SPRecognizer: forall r t1 t2,
    t1 ~> t2 ->
    boolean_recognizer r t1 ~> boolean_recognizer r t2
  where "t1 ~> t2" := (scbv_step t1 t2).

Notation "t1 ~>* t2" := (Relation_Operators.clos_refl_trans_1n _ scbv_step t1 t2) (at level 20).

#[global]
Hint Constructors scbv_step: smallstep.

Lemma scbv_step_same:
  forall t1 t2 t3,
    t1 ~> t2 ->
    t2 = t3 ->
    t1 ~> t3.
Proof.
  steps.
Qed.

Ltac t_invert_step :=
  match goal with
  | _ => step_inversion scbv_step
  | H: boolean_recognizer _ _ ~> _ |- _ => inversion H; clear H
  | H: app _ _ ~> _ |- _ => inversion H; clear H
  | H: tunfold _ ~> _ |- _ => inversion H; clear H
  | H: tunfold_in _ _ ~> _ |- _ => inversion H; clear H
  | H: ite _ _ _ ~> _ |- _ => inversion H; clear H
  | H: tmatch _ _ _ ~> _ |- _ => inversion H; clear H
  | H: pp _ _ ~> _ |- _ => inversion H; clear H
  | H: pi1 _ ~> _ |- _ => inversion H; clear H
  | H: pi2 _ ~> _ |- _ => inversion H; clear H
  | H: sum_match _ _ _ ~> _ |- _ => inversion H; clear H
  | H: tsize _ ~> _ |- _ => inversion H; clear H
  | H: unary_primitive _ _ ~> _ |- _ => inversion H; clear H
  | H: binary_primitive _ _ _ ~> _ |- _ => inversion H; clear H
  end.

Lemma evaluate_step:
  forall v,
    cbv_value v ->
    forall t,
      v ~> t ->
      False.
Proof.
  induction 1;
    repeat
      step || step_inversion cbv_value || t_invert_step;
    eauto.
Qed.

Lemma evaluate_step2:
  forall t v,
    v ~> t ->
    cbv_value v ->
    False.
Proof.
  intros; eapply evaluate_step; eauto.
Qed.

Lemma evaluate_step3:
  forall t t',
    t ~> t' ->
    forall e,
      t = notype_lambda e ->
      False.
Proof.
  steps; t_invert_step.
Qed.

Lemma evaluate_step4:
  forall t t',
    t ~> t' ->
    forall e,
      t = type_abs e ->
      False.
Proof.
  steps; t_invert_step.
Qed.

Lemma is_nat_value_value:
  forall v,
    is_nat_value v ->
    cbv_value v.
Proof.
  induction 1; steps; eauto with values.
Qed.

#[global]
Hint Immediate is_nat_value_value: values.

Lemma evaluate_step_build_nat:
  forall t n,
    scbv_step (build_nat n) t -> False.
Proof.
  eauto using evaluate_step2 with values.
Qed.
#[global]
Hint Immediate evaluate_step_build_nat: smallstep.

Lemma is_nat_value_erased:
  forall v,
    is_nat_value v ->
    is_erased_term v.
Proof.
  induction 1; steps.
Qed.

#[global]
Hint Immediate is_nat_value_erased: erased.

Ltac no_step :=
  match goal with
  | H: cbv_value err |- _ => inversion H
  | H: build_nat ?n ~> ?t |- _ => apply evaluate_step_build_nat in H; apply False_ind, H
  | H1: cbv_value ?v,
    H2: ?v ~> ?t |- _ =>
    apply False_ind; apply evaluate_step with v t; auto 2
  | H1: is_nat_value ?v,
    H2: ?v ~> ?t |- _ =>
    apply False_ind; apply evaluate_step with v t; eauto 2 with values
  | H1: cbv_value ?v1,
    H2: cbv_value ?v2,
    H3: pp ?v1 ?v2 ~> ?t |- _ =>
    apply False_ind; apply evaluate_step with (pp v1 v2) t; auto with values
  | H1: cbv_value ?v,
    H3: succ ?v ~> ?t |- _ =>
    apply False_ind; apply evaluate_step with (succ v) t; auto with values
  | _ => t_invert_step; fail
  end.

#[global]
Hint Immediate evaluate_step2: smallstep.
#[global]
Hint Immediate evaluate_step3: smallstep.

Lemma deterministic_step:
  forall t1 t2,
    t1 ~> t2 ->
    forall t3,
      t1 ~> t3 ->
      t2 = t3.
Proof.
  induction 1; repeat light || t_equality;
    try solve [ t_invert_step; repeat light || no_step || t_equality || build_nat_inj ];
    try solve [ t_invert_step; repeat light; try t_invert_step; repeat light || no_step || t_equality ].
Qed.

Ltac deterministic_step :=
  match goal with
  | H1: ?t1 ~> ?t2,
    H2: ?t1 ~> ?t3 |- _ =>
    pose proof (deterministic_step _ _ H1 _ H2); clear H2
  end.

#[global]
Hint Extern 1 => deterministic_step: smallstep.

Definition closed_term t :=
  pfv t term_var = nil /\
  wf t 0 /\
  is_erased_term t.

Definition closed_value v :=
  closed_term v /\
  cbv_value v.

Lemma cbv_value_open:
  forall v k rep,
    cbv_value v ->
    cbv_value (open k v rep).
Proof.
  induction 1;
    repeat step;
    eauto with values.
Qed.

Lemma cbv_value_subst:
  forall v l tag,
    cbv_value v ->
    cbv_value (psubstitute v l tag).
Proof.
  induction 1;
    repeat step;
    eauto with values.
Qed.
