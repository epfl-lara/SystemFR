Require Export SystemFR.Syntax.

Inductive lift (rel: tree -> tree -> Prop): tree -> tree -> Prop :=
| LiBase: forall t1 t2, rel t1 t2 -> lift rel t1 t2

| LiFVar:
    forall X tag,
      lift rel (fvar X tag) (fvar X tag)

| LiLVar:
    forall i tag,
      lift rel (lvar i tag) (lvar i tag)

| LiNoTypeErr:
    lift rel notype_err notype_err

| LiErr:
    forall T1 T2,
      lift rel T1 T2 ->
      lift rel (err T1) (err T2)

| LiUU:
    lift rel uu uu

| LiTrue:
    lift rel ttrue ttrue
| LiFalse:
    lift rel tfalse tfalse

| LiZero:
    lift rel zero zero

| LiUnit:
    lift rel T_unit T_unit
| LiBool:
    lift rel T_bool T_bool
| LiNat:
    lift rel T_nat T_nat

| LiTop:
    lift rel T_top T_top
| LiBot:
    lift rel T_bot T_bot

| LiTSize:
    forall t t',
      lift rel t t' ->
      lift rel (tsize t) (tsize t')
| LiNoTypeLambda:
    forall t t',
      lift rel t t' ->
      lift rel (notype_lambda t) (notype_lambda t')
| LiLambda:
    forall T T' t t',
      lift rel T T' ->
      lift rel t t' ->
      lift rel (lambda T t) (lambda T' t')
| LiApp:
    forall t1 t1' t2 t2',
      lift rel t1 t1' ->
      lift rel t2 t2' ->
      lift rel (app t1 t2) (app t1' t2')
| LiForallInst:
    forall t1 t1' t2 t2',
      lift rel t1 t1' ->
      lift rel t2 t2' ->
      lift rel (forall_inst t1 t2) (forall_inst t1' t2')

| LiPP:
    forall t1 t1' t2 t2',
      lift rel t1 t1' ->
      lift rel t2 t2' ->
      lift rel (pp t1 t2) (pp t1' t2')
| LiPi1:
    forall t t',
      lift rel t t' ->
      lift rel (pi1 t) (pi1 t')
| LiPi2:
    forall t t',
      lift rel t t' ->
      lift rel (pi2 t) (pi2 t')

| LiBecause:
    forall t1 t1' t2 t2',
      lift rel t1 t1' ->
      lift rel t2 t2' ->
      lift rel (because t1 t2) (because t1' t2')
| LiGetProof:
    forall t1 t1' t2 t2',
      lift rel t1 t1' ->
      lift rel t2 t2' ->
      lift rel (get_refinement_witness t1 t2) (get_refinement_witness t1' t2')

| LiIte:
    forall t1 t1' t2 t2' t3 t3',
      lift rel t1 t1' ->
      lift rel t2 t2' ->
      lift rel t3 t3' ->
      lift rel (ite t1 t2 t3) (ite t1' t2' t3')
| LiRecognizer:
    forall r t t',
      lift rel t t' ->
      lift rel (boolean_recognizer r t) (boolean_recognizer r t')

| LiSucc:
    forall t t',
      lift rel t t' ->
      lift rel (succ t) (succ t')
| LiNoTypeRec:
    forall t1 t1' t2 t2' t3 t3',
      lift rel t1 t1' ->
      lift rel t2 t2' ->
      lift rel t3 t3' ->
      lift rel (notype_rec t1 t2 t3) (notype_rec t1' t2' t3')
| LiRec:
    forall t1 t1' t2 t2' t3 t3' T T',
      lift rel T T' ->
      lift rel t1 t1' ->
      lift rel t2 t2' ->
      lift rel t3 t3' ->
      lift rel (rec T t1 t2 t3) (rec T' t1' t2' t3')
| LiMatch:
    forall t1 t1' t2 t2' t3 t3',
      lift rel t1 t1' ->
      lift rel t2 t2' ->
      lift rel t3 t3' ->
      lift rel (tmatch t1 t2 t3) (tmatch t1' t2' t3')

| LiNoTypeLet:
    forall t1 t1' t2 t2',
      lift rel t1 t1' ->
      lift rel t2 t2' ->
      lift rel (notype_tlet t1 t2) (notype_tlet t1' t2')
| LiLet:
    forall T T' t1 t1' t2 t2',
      lift rel T T' ->
      lift rel t1 t1' ->
      lift rel t2 t2' ->
      lift rel (tlet t1 T t2) (tlet t1' T' t2')

| LiRefl:
    forall t1 t1' t2 t2',
      lift rel t1 t1' ->
      lift rel t2 t2' ->
      lift rel (trefl t1 t2) (trefl t1' t2')

| LiTypeAbs:
    forall t t',
      lift rel t t' ->
      lift rel (type_abs t) (type_abs t')
| LiTypeInst:
    forall t t' T T',
      lift rel T T' ->
      lift rel t t' ->
      lift rel (type_inst t T) (type_inst t' T')

| LiFix:
    forall t t' T T',
      lift rel T T' ->
      lift rel t t' ->
      lift rel (tfix T t) (tfix T' t')
| LiNoTypeFix:
    forall t t',
      lift rel t t' ->
      lift rel (notype_tfix t) (notype_tfix t')

| LiFold:
    forall t t' T T',
      lift rel T T' ->
      lift rel t t' ->
      lift rel (tfold T t) (tfold T' t')
| LiUnfold:
    forall t t',
      lift rel t t' ->
      lift rel (tunfold t) (tunfold t')
| LiUnfoldIn:
    forall t1 t1' t2 t2',
      lift rel t1 t1' ->
      lift rel t2 t2' ->
      lift rel (tunfold_in t1 t2) (tunfold_in t1' t2')
| LiUnfoldPosIn:
    forall t1 t1' t2 t2',
      lift rel t1 t1' ->
      lift rel t2 t2' ->
      lift rel (tunfold_pos_in t1 t2) (tunfold_pos_in t1' t2')

| LiLeft:
    forall t t',
      lift rel t t' ->
      lift rel (tleft t) (tleft t')

| LiRight:
    forall t t',
      lift rel t t' ->
      lift rel (tright t) (tright t')
| LiSumMatch:
    forall t1 t1' t2 t2' t3 t3',
      lift rel t1 t1' ->
      lift rel t2 t2' ->
      lift rel t3 t3' ->
      lift rel (sum_match t1 t2 t3) (sum_match t1' t2' t3')


| LiTypeCheck:
    forall t t' T T',
      lift rel t t' ->
      lift rel T T' ->
      lift rel (typecheck t T) (typecheck t' T')

| LiRefine:
    forall t t' T T',
      lift rel T T' ->
      lift rel t t' ->
      lift rel (T_refine T t) (T_refine T' t')
| LiTypeRefine:
    forall A A' B B',
      lift rel A A' ->
      lift rel B B' ->
      lift rel (T_type_refine A B) (T_type_refine A' B')

| LiProd:
    forall A A' B B',
      lift rel A A' ->
      lift rel B B' ->
      lift rel (T_prod A B) (T_prod A' B')
| LiArrow:
    forall A A' B B',
      lift rel A A' ->
      lift rel B B' ->
      lift rel (T_arrow A B) (T_arrow A' B')
| LiSum:
    forall A A' B B',
      lift rel A A' ->
      lift rel B B' ->
      lift rel (T_sum A B) (T_sum A' B')

| LiIntersection:
    forall A A' B B',
      lift rel A A' ->
      lift rel B B' ->
      lift rel (T_intersection A B) (T_intersection A' B')
| LiUnion:
    forall A A' B B',
      lift rel A A' ->
      lift rel B B' ->
      lift rel (T_union A B) (T_union A' B')

| LiEqual:
    forall t1 t1' t2 t2',
      lift rel t1 t1' ->
      lift rel t2 t2' ->
      lift rel (T_equiv t1 t2) (T_equiv t1' t2')

| LiForall:
    forall A A' B B',
      lift rel A A' ->
      lift rel B B' ->
      lift rel (T_forall A B) (T_forall A' B')
| LiExists:
    forall A A' B B',
      lift rel A A' ->
      lift rel B B' ->
      lift rel (T_exists A B) (T_exists A' B')
| LiAbs:
    forall T T',
      lift rel T T' ->
      lift rel (T_abs T) (T_abs T')
| LiTRec:
    forall n T0 Ts n' T0' Ts',
      lift rel n n' ->
      lift rel T0 T0' ->
      lift rel Ts Ts' ->
      lift rel (T_rec n T0 Ts) (T_rec n' T0' Ts')
.

Hint Constructors lift: lift.

Lemma lift_sym:
  forall (R: tree -> tree -> Prop) t1 t2,
    (forall t1 t2, R t1 t2 -> R t2 t1) ->
    lift R t1 t2 ->
    lift R t2 t1.
Proof.
  induction 2; steps;
    eauto with lift.
Qed.

Lemma lift_eq:
  forall t1 t2,
    lift eq t1 t2 ->
    t1 = t2.
Proof.
  induction 1; steps.
Qed.

Lemma lift_refl:
  forall rel t,
    lift rel t t.
Proof.
  induction t; steps; eauto with lift.
Qed.

Lemma lift_ext:
  forall (r r': tree -> tree -> Prop) t1 t2,
    lift r t1 t2 ->
    (forall e1 e2, r e1 e2 -> r' e1 e2) ->
    lift r' t1 t2.
Proof.
  induction 1; steps;
    eauto with lift;
    eauto with lift apply_any.
Qed.

Lemma lift_swap:
  forall (R: tree -> tree -> Prop) t1 t2,
    lift R t1 t2 ->
    lift (fun e1 e2 => R e2 e1) t2 t1.
Proof.
  induction 1; steps;
    eauto with lift.
Qed.

Lemma lift_swap':
  forall (R R': tree -> tree -> Prop) t1 t2,
    lift R t1 t2 ->
    (forall e1 e2, R e1 e2 -> R' e2 e1) ->
    lift R' t2 t1.
Proof.
  induction 1; steps;
    eauto with lift.
Qed.

Lemma lift_insert:
  forall t1 t2 t3 t1' t3',
    lift (fun e e' => e = t1 /\ e' = t3) t1' t3' ->
    exists t2',
      lift (fun e e' => e = t1 /\ e' = t2) t1' t2' /\
      lift (fun e e' => e = t2 /\ e' = t3) t2' t3'.
Proof.
  induction 1;
    steps; eauto with lift.
  exists t2; steps; eauto with lift step_tactic.
Qed.

Lemma lift_open:
  forall t t1 t2 k r,
    lift r t1 t2 ->
    lift r (open k t t1) (open k t t2).
Proof.
  induction t;
    repeat step;
    eauto 6 with lift.
Qed.

(*
Lemma lift_open:
  forall t1 t2 t1' t2' a k,
    lift (fun e e' => e = open k t1 a /\ e' = open k t2 a) t1' t2' ->
    lift (fun e e' => e = t1 /\ e' = t2) t1' t2'.
Proof.
  induction 1; steps; eauto with lift.
  constructor.
*)
