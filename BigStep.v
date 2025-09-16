Require Import SystemFR.Trees.
Require Import SystemFR.Syntax.
Require Import SystemFR.RewriteTactics.
Require Import SystemFR.PrimitiveRecognizers.
Require Import SystemFR.FVLemmas.
Require Import SystemFR.FVLemmasEval.
Require Import SystemFR.WFLemmasEval.
Require Import SystemFR.WFLemmas.
Require Import SystemFR.Evaluator.
Require Import SystemFR.StarLemmas.

From Stdlib Require Import String.

Reserved Notation "t '~~>*' v" (at level 20).

Inductive bcbv_step: tree -> tree -> Prop :=
  (* unit *)
  | BSuu : uu ~~>* uu
  (* nat *)
  | BSzero : zero ~~>* zero
  | BSsucc : forall t v,
      t ~~>* v ->
        succ t ~~>* succ v
  | BSmatch0 : forall t t0 ts v,
      t ~~>* zero -> 
      t0 ~~>* v -> 
        tmatch t t0 ts ~~>* v
  | BSmatchS : forall t v t0 ts v',
      t ~~>* succ v -> 
      open 0 ts v ~~>* v' -> 
        tmatch t t0 ts ~~>* v'
  | BSplus : forall t1 t2 n1 n2,
      t1 ~~>* build_nat n1 ->
      t2 ~~>* build_nat n2 ->
        binary_primitive Plus t1 t2 ~~>* build_nat (n1 + n2)
  | BSminus : forall t1 t2 n1 n2,
      t1 ~~>* build_nat n1 ->
      t2 ~~>* build_nat n2 ->
      n1 >= n2 ->
        binary_primitive Minus t1 t2 ~~>* build_nat (n1 - n2)
  | BSmul : forall t1 t2 n1 n2,
      t1 ~~>* build_nat n1 ->
      t2 ~~>* build_nat n2 ->
        binary_primitive Mul t1 t2 ~~>* build_nat (n1 * n2)
  | BSdiv : forall t1 t2 n1 n2,
      t1 ~~>* build_nat n1 ->
      t2 ~~>* build_nat n2 ->
      n2 > 0 ->
        binary_primitive Div t1 t2 ~~>* build_nat (PeanoNat.Nat.div n1 n2)
  | BSeq : forall t1 t2 n1 n2,
      t1 ~~>* build_nat n1 ->
      t2 ~~>* build_nat n2 ->
        binary_primitive Eq t1 t2 ~~>* (if PeanoNat.Nat.eqb n1 n2 then ttrue else tfalse)
  | BSneq : forall t1 t2 n1 n2,
      t1 ~~>* build_nat n1 ->
      t2 ~~>* build_nat n2 ->
        binary_primitive Neq t1 t2 ~~>* (if PeanoNat.Nat.eq_dec n1 n2 then tfalse else ttrue)
  | BSlt : forall t1 t2 n1 n2,
      t1 ~~>* build_nat n1 ->
      t2 ~~>* build_nat n2 ->
        binary_primitive Lt t1 t2 ~~>* (if PeanoNat.Nat.ltb n1 n2 then ttrue else tfalse)
  | BSleq : forall t1 t2 n1 n2,
      t1 ~~>* build_nat n1 ->
      t2 ~~>* build_nat n2 ->
        binary_primitive Leq t1 t2 ~~>* (if PeanoNat.Nat.leb n1 n2 then ttrue else tfalse)
  | BSgt : forall t1 t2 n1 n2,
      t1 ~~>* build_nat n1 ->
      t2 ~~>* build_nat n2 ->
        binary_primitive Gt t1 t2 ~~>* (if PeanoNat.Nat.leb n1 n2 then tfalse else ttrue)
  | BSget : forall t1 t2 n1 n2,
      t1 ~~>* build_nat n1 ->
      t2 ~~>* build_nat n2 ->
        binary_primitive Geq t1 t2 ~~>* (if PeanoNat.Nat.ltb n1 n2 then tfalse else ttrue)
  (* function *)
  | BSlambda : forall t, 
      notype_lambda t ~~>* notype_lambda t 
  | BSapp : forall t1 b1 t2 v2 v,
      t1 ~~>* notype_lambda b1 ->
      t2 ~~>* v2 ->
      open 0 b1 v2 ~~>* v ->
        app t1 t2 ~~>* v
  | BSfix : forall t v, 
      open 0 (open 1 t zero) (notype_tfix t) ~~>* v ->
        notype_tfix t ~~>* v
  (* pair *)
  | BSpair : forall t1 t2 v1 v2,
      t1 ~~>* v1 ->
      t2 ~~>* v2 ->
        pp t1 t2 ~~>* pp v1 v2
  | BSproj1 : forall t v1 v2,
      t ~~>* pp v1 v2 ->
        pi1 t ~~>* v1 
  | BSproj2 : forall t v1 v2,
      t ~~>* pp v1 v2 ->
        pi2 t ~~>* v2
  (* boolean *)
  | BStrue : ttrue ~~>* ttrue
  | BSfalse : tfalse ~~>* tfalse
  | BSitetrue : forall c t1 v1 t2,
      c ~~>* ttrue ->
      t1 ~~>* v1 ->
        ite c t1 t2 ~~>* v1 
  | BSitefalse : forall c t1 t2 v2, 
      c ~~>* tfalse ->
      t2 ~~>* v2 ->
        ite c t1 t2 ~~>* v2 
  | BSisPair : forall t v,
      t ~~>* v ->
        boolean_recognizer 0 t ~~>* is_pair v 
  | BSisSucc : forall t v, 
      t ~~>* v ->
        boolean_recognizer 1 t ~~>* is_succ v 
  | BSisLambda : forall t v,
      t ~~>* v ->
        boolean_recognizer 2 t ~~>* is_lambda v 
  | BSnot1 : forall t,
      t ~~>* ttrue ->
        unary_primitive Not t ~~>* tfalse
  | BSnot2 : forall t,
      t ~~>* tfalse ->
        unary_primitive Not t ~~>* ttrue
  | BSand1 : forall t1 t2, 
      t1 ~~>* ttrue -> 
      t2 ~~>* ttrue ->
        binary_primitive And t1 t2 ~~>* ttrue
  | BSand2 : forall t1 t2, 
      t1 ~~>* ttrue -> 
      t2 ~~>* tfalse ->
        binary_primitive And t1 t2 ~~>* tfalse
  | BSand3 : forall t1 t2, 
      t1 ~~>* tfalse -> 
      t2 ~~>* ttrue ->
        binary_primitive And t1 t2 ~~>* tfalse
  | BSand4 : forall t1 t2, 
      t1 ~~>* tfalse -> 
      t2 ~~>* tfalse ->
        binary_primitive And t1 t2 ~~>* tfalse
  | BSor1 : forall t1 t2, 
      t1 ~~>* ttrue -> 
      t2 ~~>* ttrue ->
        binary_primitive Or t1 t2 ~~>* ttrue
  | BSor2 : forall t1 t2, 
      t1 ~~>* ttrue -> 
      t2 ~~>* tfalse ->
        binary_primitive Or t1 t2 ~~>* ttrue
  | BSor3 : forall t1 t2, 
      t1 ~~>* tfalse -> 
      t2 ~~>* ttrue ->
        binary_primitive Or t1 t2 ~~>* ttrue
  | BSor4 : forall t1 t2, 
      t1 ~~>* tfalse -> 
      t2 ~~>* tfalse ->
        binary_primitive Or t1 t2 ~~>* tfalse
  (* either *)
  | BSleft : forall t v, 
      t ~~>* v -> 
        tleft t ~~>* tleft v 
  | BSright : forall t v, 
      t ~~>* v -> 
        tright t ~~>* tright v 
  | BSmatchLeft : forall t v tr tl v',
      t ~~>* tleft v -> 
      open 0 tl v ~~>* v' ->
        sum_match t tl tr ~~>* v'
  | BSmatchRight : forall t v tr tl v',
      t ~~>* tright v -> 
      open 0 tr v ~~>* v' ->
        sum_match t tl tr ~~>* v'
  (* size *)
  | BSsize : forall t v, 
      t ~~>* v ->
        tsize t ~~>* build_nat (tsize_semantics v)
where "t '~~>*' v" := (bcbv_step t v).

#[export]
Hint Constructors bcbv_step : bcbv_step.

Lemma bs_closed_term: forall t1 t2, t1 ~~>* t2 -> closed_term t1 -> closed_value t2.
Proof.
  induction 1; repeat light || apply_any; t_closing;
  eauto with fv erased wf; try solve [inversion H4; eauto].
  repeat light || eapply wf_open; eauto with wf.
  repeat light || eapply is_erased_open; eauto with erased.
Qed.

#[export] Hint Resolve bs_closed_term : values.

Lemma bs_value: forall t v, t ~~>* v -> cbv_value v.
Proof.
  induction 1; repeat light || destruct_match; auto with values;
  inversion IHbcbv_step; light.
Qed.

Lemma value_bs: forall v, cbv_value v -> v ~~>* v .
Proof.
  induction 1; eauto with bcbv_step.
Qed.

#[export]
Hint Immediate bs_value value_bs : values.

Lemma bs_unique: forall t v1 v2, 
  t ~~>* v1 -> 
  t ~~>* v2 ->
    v1 = v2.
Proof.
  intros; generalize dependent v2;
  induction H; inversion 1; 
  repeat light || t_equality 
  || invert_constructor_equalities || build_nat_inj 
  || instantiate_any || destruct_match.
Qed.

Ltac instantiate_bs_unique := 
  match goal with
  | H : ?v ~~>* _,
    H': ?v ~~>* _ |- _ =>
      poseNew (Mark v "bs_unique");
      pose proof bs_unique _ _ _ H H'
  end.

(* Equivalance small step*)

Ltac big_step_value := 
  match goal with
  | H: ?v ~~>* ?v' |- _ =>
    unshelve epose proof value_bs v _; 
    try solve [
      repeat light || destruct_match;
      eauto with values
    ];
    instantiate_bs_unique;
    repeat light
  | |- ?v ~~>* ?v =>
    apply value_bs;
    eauto with values;
    fail
  end.

Lemma ss_bs: forall t1 t2, t1 ~> t2 -> 
  forall v, t2 ~~>* v -> t1 ~~>* v.
Proof.
  induction 1;
  try solve [ 
    inversion 1; 
    repeat light; 
    try instantiate_any;
    eauto with bcbv_step values;
    constructor; auto
  ]; try solve [
    repeat light || big_step_value 
    || constructor || destruct_match;
    eauto with bcbv_step values
  ].
Qed.

Lemma tcss_bs: forall t v, 
  cbv_value v -> t ~>* v ->
    t ~~>* v.
Proof.
  induction 2.
  eauto using value_bs.
  eauto using ss_bs.
Qed.

Ltac bs_tccs := 
  match goal with
  | H1 : ?t1 ~>* ?v1,
    H2 : ?t2 ~>* ?v2
    |- binary_primitive ?op ?t1 ?t2 ~>* _ =>
      eapply star_trans with (binary_primitive op v1 t2);
      eauto with cbvlemmas smallstep star values;
      eapply star_trans with (binary_primitive op v1 v2);
      eauto with cbvlemmas smallstep star values
  | H : ?t ~>* ?v 
    |- unary_primitive ?op ?t ~>* _ => 
      eapply star_trans with (unary_primitive op v);
      eauto with cbvlemmas smallstep star values
  | H : ?t ~>* ?v 
    |- boolean_recognizer ?id ?t ~>* _ => 
      eapply star_trans with (boolean_recognizer id v);
      eauto with cbvlemmas smallstep star values
  | H1 : ?t1 ~>* ?v1,
    H2 :   _ ~>* ?v2 
    |- tmatch ?t _ _ ~>* ?v2 => 
      eapply star_trans with (tmatch v1 _ _);
      eauto with cbvlemmas smallstep star values
  | H1 : ?c ~>* ?b,
    H2 :  _ ~>* ?v 
    |- ite ?c _ _ ~>* ?v => 
      eapply star_trans with (ite b _ _);
      eauto with cbvlemmas smallstep star values
  | H1 : ?t ~>* ?v,
    H2 : open 0 _ _ ~>* ?v'
    |- sum_match ?t _ _ ~>* ?v' => 
      eapply star_trans with (sum_match v _ _);
      eauto with cbvlemmas smallstep star values
  | H : ?t ~>* pp ?v1 ?v2 
    |- ?C ?t ~>* _ => 
      is_constructor C; 
      eapply star_trans with (C (pp v1 v2));
      eauto with cbvlemmas smallstep star values
  end.

Ltac invert_cbv_value := 
  match goal with 
  | H : cbv_value (?C _) |- _ => 
    is_constructor C; inversion H
  | H : cbv_value (?C _ _) |- _ => 
    is_constructor C; inversion H
  end.

Lemma bs_tccs: forall t v, 
  t ~~>* v -> t ~>* v.
Proof.
  induction 1; 
  try solve [constructor]; 
  eauto with cbvlemmas; 
  try solve [
    eapply star_trans;
    eauto with cbvlemmas smallstep star values
  ]; repeat apply_anywhere bs_value; 
  try invert_cbv_value;
  try bs_tccs.
  (* 4 *)
  - (* app *)
    eapply star_trans with (app (notype_lambda b1) t2);
    eauto with cbvlemmas smallstep star values.
    eapply star_trans with (app (notype_lambda b1) v2);
    eauto with cbvlemmas smallstep star values.
  - (* tsize *)
    eapply star_trans with (tsize v);
    eauto with cbvlemmas smallstep star values.
Qed.

