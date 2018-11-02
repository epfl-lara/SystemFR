Require Import Termination.Syntax.
Require Import Termination.Tactics.

Inductive is_value: term -> Prop :=
| IVUnit: is_value uu
| IVZero: is_value zero
| IVSucc:
    forall v,
      is_value v ->
      is_value (succ v)
| IVFalse: is_value tfalse
| IVTrue: is_value ttrue
| IVPair:
    forall v1 v2,
      is_value v1 ->
      is_value v2 ->
      is_value (pp v1 v2)
| IVLambda: forall T t,
    is_value (lambda T t)
| IVVar: forall x,
    is_value (fvar x)
| IVRefl:
    is_value trefl
.

Fixpoint is_nat_value (t: term): Prop :=
  match t with
  | zero => True
  | succ t' => is_nat_value t'
  | _ => False
  end.

Inductive small_step: term -> term -> Prop :=
(* beta reduction *)
| SPBetaProj1: forall v1 v2,
    is_value v1 ->
    is_value v2 ->
    small_step (pi1 (pp v1 v2)) v1
| SPBetaProj2: forall v1 v2,
    is_value v1 ->
    is_value v2 ->
    small_step (pi2 (pp v1 v2)) v2 

| SPBetaApp: forall T t v,
    is_value v ->
    small_step
      (app (lambda T t) v)
      (open 0 t v)

| SPBetaLet: forall t T v,
    is_value v ->
    small_step
      (tlet v T t)
      (open 0 t v)

| SPBetaIte1: forall t1 t2,
    small_step (ite ttrue t1 t2) t1
| SPBetaIte2: forall t1 t2,
    small_step (ite tfalse t1 t2) t2
      
| SPBetaRec0: forall T t0 ts,
    small_step
      (rec T zero t0 ts)
      t0
| SPBetaRecS: forall T v t0 ts,
    is_value v ->
    small_step
      (rec T (succ v) t0 ts)
      (open 0 (open 1 ts v) (lambda T_unit (rec T v t0 ts)))

| SPBetaMatch0: forall t0 ts,
    small_step
      (tmatch zero t0 ts)
      t0
| SPBetaMatchS: forall v t0 ts,
    is_value v ->
    small_step
      (tmatch (succ v) t0 ts)
      (open 0 ts v)

(* reduction inside terms *)
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
| SPRec: forall T t1 t2 t0 ts,
    small_step t1 t2 ->
    small_step (rec T t1 t0 ts) (rec T t2 t0 ts)
| SPMatch: forall t1 t2 t0 ts,
    small_step t1 t2 ->
    small_step (tmatch t1 t0 ts) (tmatch t2 t0 ts)
| SPIte: forall t1 t1' t2 t3,
    small_step t1 t1' ->
    small_step (ite t1 t2 t3) (ite t1' t2 t3)
| SPLet: forall t1 t1' T t2,
    small_step t1 t1' ->
    small_step (tlet t1 T t2) (tlet t1' T t2)
.

Ltac t_invert_step :=
  match goal with
  | H: small_step err _ |- _ => inversion H
  | H: small_step zero _ |- _ => inversion H; clear H
  | H: small_step tfalse _ |- _ => inversion H; clear H
  | H: small_step ttrue _ |- _ => inversion H; clear H
  | H: small_step (succ _) _ |- _ => inversion H; clear H
  | H: small_step (fvar _) _ |- _ => inversion H; clear H
  | H: small_step (app _ _) _ |- _ => inversion H; clear H
  | H: small_step (ite _ _ _) _ |- _ => inversion H; clear H
  | H: small_step (lambda _ _) _ |- _ => inversion H; clear H
  | H: small_step (rec _ _ _ _) _ |- _ => inversion H; clear H
  | H: small_step (pp _ _) _ |- _ => inversion H; clear H
  | H: small_step (tlet _ _ _) _ |- _ => inversion H; clear H
  | H: small_step (pi1 _) _ |- _ => inversion H; clear H
  | H: small_step (pi2 _) _ |- _ => inversion H; clear H
  end.

Hint Extern 50 => t_invert_step: smallstep.

Lemma evaluate_step:
  forall v,
    is_value v ->
    forall t,
      small_step v t ->
      False.
Proof.
  induction 1; repeat step || step_inversion (small_step,is_value) || t_invert_step || firstorder.
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
    forall T e,
      t = lambda T e ->
      False.
Proof.
  induction 1; steps.
Qed.

Hint Resolve IVUnit: values.
Hint Resolve IVZero: values.
Hint Resolve IVSucc: values.
Hint Resolve IVFalse: values.
Hint Resolve IVTrue: values.
Hint Resolve IVPair: values.
Hint Resolve IVLambda: values.
Hint Resolve IVVar: values.
Hint Resolve IVRefl: values.

Hint Resolve SPBetaProj1: smallstep.
Hint Resolve SPBetaProj2: smallstep.
Hint Resolve SPBetaApp: smallstep.
Hint Resolve SPBetaLet: smallstep.
Hint Resolve SPBetaRec0: smallstep.
Hint Resolve SPBetaRecS: smallstep.
Hint Resolve SPBetaMatch0: smallstep.
Hint Resolve SPBetaMatchS: smallstep.
Hint Resolve SPBetaIte1: smallstep.
Hint Resolve SPBetaIte2: smallstep.

Hint Resolve SPAppLeft: smallstep.
Hint Resolve SPAppRight: smallstep.
Hint Resolve SPPairL: smallstep.
Hint Resolve SPPairR: smallstep.
Hint Resolve SPProj1: smallstep.
Hint Resolve SPProj2: smallstep.
Hint Resolve SPSucc: smallstep.
Hint Resolve SPRec: smallstep.
Hint Resolve SPMatch: smallstep.
Hint Resolve SPIte: smallstep.
Hint Resolve SPLet: smallstep.

Lemma is_nat_value_value:
  forall v,
    is_nat_value v ->
    is_value v.
Proof.
  induction v; steps; eauto with values.
Qed.

Hint Resolve is_nat_value_value: values.

Ltac t_nostep :=
  match goal with
  | H: is_value err |- _ => inversion H
  | H1: is_value ?v,
    H2: small_step ?v ?t |- _ =>
    apply False_ind; apply evaluate_step with v t
  | H1: is_nat_value ?v,
    H2: small_step ?v ?t |- _ =>
    apply False_ind; apply evaluate_step with v t; eauto 2 with values
  | H: small_step (lambda ?T ?e) ?t2 |- _ =>
    apply False_ind; apply evaluate_step3 with (lambda T e) t2 T e; auto with values
  | H1: is_value ?v1,
    H2: is_value ?v2,    
    H3: small_step (pp ?v1 ?v2) ?t |- _ =>
    apply False_ind; apply evaluate_step with (pp v1 v2) t; auto with values 
  | H1: is_value ?v, 
    H3: small_step (succ ?v) ?t |- _ =>
    apply False_ind; apply evaluate_step with (succ v) t; auto with values
  end.

Hint Resolve evaluate_step2: smallstep.
Hint Resolve evaluate_step3: smallstep.
Hint Extern 50 => t_nostep: smallstep.

Lemma deterministic_step:
  forall t1 t2 t3,
    small_step t1 t2 ->
    small_step t1 t3 ->
    t2 = t3.
Proof.
  induction t1; inversion 1; inversion 1; repeat steps || tequality;
    eauto 3 with step_tactic values smallstep.
Qed.
        
Ltac t_deterministic_step :=
  match goal with
  | H1: small_step ?t1 ?t2,
    H2: small_step ?t1 ?t3 |- _ =>
    pose proof (deterministic_step _ _ _ H1 H2); clear H2
  end.

Hint Extern 50 => t_deterministic_step: smallstep.

Ltac hyp_value v :=
  match goal with
  | H: is_value v |- _ => idtac
  end.

Ltac t_not_hyp_value t := tryif hyp_value t then fail else idtac.
