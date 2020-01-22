Require Export SystemFR.Syntax.

Inductive term_lift (rel: tree -> tree -> Prop): tree -> tree -> Prop :=
| LiBase: forall t1 t2, rel t1 t2 -> term_lift rel t1 t2

| LiFVar:
    forall X,
      term_lift rel (fvar X term_var) (fvar X term_var)

| LiLVar:
    forall i,
      term_lift rel (lvar i term_var) (lvar i term_var)

| LiNoTypeErr:
    term_lift rel notype_err notype_err

| LiErr:
    forall T1 T2,
      term_lift rel T1 T2 ->
      term_lift rel (err T1) (err T2)

| LiUU:
    term_lift rel uu uu

| LiTrue:
    term_lift rel ttrue ttrue
| LiFalse:
    term_lift rel tfalse tfalse

| LiZero:
    term_lift rel zero zero

| LiUnit:
    term_lift rel T_unit T_unit
| LiBool:
    term_lift rel T_bool T_bool
| LiNat:
    term_lift rel T_nat T_nat

| LiTop:
    term_lift rel T_top T_top
| LiBot:
    term_lift rel T_bot T_bot

| LiTSize:
    forall t t',
      term_lift rel t t' ->
      term_lift rel (tsize t) (tsize t')
| LiNoTypeLambda:
    forall t t',
      term_lift rel t t' ->
      term_lift rel (notype_lambda t) (notype_lambda t')
| LiLambda:
    forall T T' t t',
      term_lift rel T T' ->
      term_lift rel t t' ->
      term_lift rel (lambda T t) (lambda T' t')
| LiApp:
    forall t1 t1' t2 t2',
      term_lift rel t1 t1' ->
      term_lift rel t2 t2' ->
      term_lift rel (app t1 t2) (app t1' t2')
| LiForallInst:
    forall t1 t1' t2 t2',
      term_lift rel t1 t1' ->
      term_lift rel t2 t2' ->
      term_lift rel (forall_inst t1 t2) (forall_inst t1' t2')

| LiPP:
    forall t1 t1' t2 t2',
      term_lift rel t1 t1' ->
      term_lift rel t2 t2' ->
      term_lift rel (pp t1 t2) (pp t1' t2')
| LiPi1:
    forall t t',
      term_lift rel t t' ->
      term_lift rel (pi1 t) (pi1 t')
| LiPi2:
    forall t t',
      term_lift rel t t' ->
      term_lift rel (pi2 t) (pi2 t')

| LiBecause:
    forall t1 t1' t2 t2',
      term_lift rel t1 t1' ->
      term_lift rel t2 t2' ->
      term_lift rel (because t1 t2) (because t1' t2')
| LiGetProof:
    forall t1 t1' t2 t2',
      term_lift rel t1 t1' ->
      term_lift rel t2 t2' ->
      term_lift rel (get_refinement_witness t1 t2) (get_refinement_witness t1' t2')

| LiIte:
    forall t1 t1' t2 t2' t3 t3',
      term_lift rel t1 t1' ->
      term_lift rel t2 t2' ->
      term_lift rel t3 t3' ->
      term_lift rel (ite t1 t2 t3) (ite t1' t2' t3')
| LiRecognizer:
    forall r t t',
      term_lift rel t t' ->
      term_lift rel (boolean_recognizer r t) (boolean_recognizer r t')

| LiSucc:
    forall t t',
      term_lift rel t t' ->
      term_lift rel (succ t) (succ t')
| LiNoTypeRec:
    forall t1 t1' t2 t2' t3 t3',
      term_lift rel t1 t1' ->
      term_lift rel t2 t2' ->
      term_lift rel t3 t3' ->
      term_lift rel (notype_rec t1 t2 t3) (notype_rec t1' t2' t3')
| LiRec:
    forall t1 t1' t2 t2' t3 t3' T T',
      term_lift rel T T' ->
      term_lift rel t1 t1' ->
      term_lift rel t2 t2' ->
      term_lift rel t3 t3' ->
      term_lift rel (rec T t1 t2 t3) (rec T' t1' t2' t3')
| LiMatch:
    forall t1 t1' t2 t2' t3 t3',
      term_lift rel t1 t1' ->
      term_lift rel t2 t2' ->
      term_lift rel t3 t3' ->
      term_lift rel (tmatch t1 t2 t3) (tmatch t1' t2' t3')

| LiNoTypeLet:
    forall t1 t1' t2 t2',
      term_lift rel t1 t1' ->
      term_lift rel t2 t2' ->
      term_lift rel (notype_tlet t1 t2) (notype_tlet t1' t2')
| LiLet:
    forall T T' t1 t1' t2 t2',
      term_lift rel T T' ->
      term_lift rel t1 t1' ->
      term_lift rel t2 t2' ->
      term_lift rel (tlet t1 T t2) (tlet t1' T' t2')

| LiRefl:
    forall t1 t1' t2 t2',
      term_lift rel t1 t1' ->
      term_lift rel t2 t2' ->
      term_lift rel (trefl t1 t2) (trefl t1' t2')

| LiTypeAbs:
    forall t t',
      term_lift rel t t' ->
      term_lift rel (type_abs t) (type_abs t')
| LiTypeInst:
    forall t t' T T',
      term_lift rel T T' ->
      term_lift rel t t' ->
      term_lift rel (type_inst t T) (type_inst t' T')

| LiFix:
    forall t t' T T',
      term_lift rel T T' ->
      term_lift rel t t' ->
      term_lift rel (tfix T t) (tfix T' t')
| LiNoTypeFix:
    forall t t',
      term_lift rel t t' ->
      term_lift rel (notype_tfix t) (notype_tfix t')

| LiFold:
    forall t t' T T',
      term_lift rel T T' ->
      term_lift rel t t' ->
      term_lift rel (tfold T t) (tfold T' t')
| LiUnfold:
    forall t t',
      term_lift rel t t' ->
      term_lift rel (tunfold t) (tunfold t')
| LiUnfoldIn:
    forall t1 t1' t2 t2',
      term_lift rel t1 t1' ->
      term_lift rel t2 t2' ->
      term_lift rel (tunfold_in t1 t2) (tunfold_in t1' t2')
| LiUnfoldPosIn:
    forall t1 t1' t2 t2',
      term_lift rel t1 t1' ->
      term_lift rel t2 t2' ->
      term_lift rel (tunfold_pos_in t1 t2) (tunfold_pos_in t1' t2')

| LiLeft:
    forall t t',
      term_lift rel t t' ->
      term_lift rel (tleft t) (tleft t')

| LiRight:
    forall t t',
      term_lift rel t t' ->
      term_lift rel (tright t) (tright t')
| LiSumMatch:
    forall t1 t1' t2 t2' t3 t3',
      term_lift rel t1 t1' ->
      term_lift rel t2 t2' ->
      term_lift rel t3 t3' ->
      term_lift rel (sum_match t1 t2 t3) (sum_match t1' t2' t3')


| LiTypeCheck:
    forall t t' T T',
      term_lift rel t t' ->
      term_lift rel T T' ->
      term_lift rel (typecheck t T) (typecheck t' T')
.

Hint Constructors term_lift: term_lift.

Lemma term_lift_sym:
  forall (R: tree -> tree -> Prop) t1 t2,
    (forall t1 t2, R t1 t2 -> R t2 t1) ->
    term_lift R t1 t2 ->
    term_lift R t2 t1.
Proof.
  induction 2; steps;
    eauto with term_lift.
Qed.

Lemma term_lift_eq:
  forall t1 t2,
    term_lift eq t1 t2 ->
    t1 = t2.
Proof.
  induction 1; steps.
Qed.

Lemma term_lift_refl:
  forall rel t,
    is_erased_term t ->
    term_lift rel t t.
Proof.
  induction t; steps; eauto with term_lift.
Qed.

Lemma term_lift_ext:
  forall (r r': tree -> tree -> Prop) t1 t2,
    term_lift r t1 t2 ->
    (forall e1 e2, r e1 e2 -> r' e1 e2) ->
    term_lift r' t1 t2.
Proof.
  induction 1; steps;
    eauto with term_lift;
    eauto with term_lift apply_any.
Qed.

Lemma term_lift_swap:
  forall (R: tree -> tree -> Prop) t1 t2,
    term_lift R t1 t2 ->
    term_lift (fun e1 e2 => R e2 e1) t2 t1.
Proof.
  induction 1; steps;
    eauto with term_lift.
Qed.

Lemma term_lift_swap':
  forall (R R': tree -> tree -> Prop) t1 t2,
    term_lift R t1 t2 ->
    (forall e1 e2, R e1 e2 -> R' e2 e1) ->
    term_lift R' t2 t1.
Proof.
  induction 1; steps;
    eauto with term_lift.
Qed.

Lemma term_lift_open:
  forall t t1 t2 k r,
    is_erased_term t ->
    term_lift r t1 t2 ->
    term_lift r (open k t t1) (open k t t2).
Proof.
  induction t;
    repeat step;
    eauto 6 with term_lift.
Qed.
