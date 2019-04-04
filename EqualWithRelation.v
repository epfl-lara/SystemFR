Require Import Coq.Strings.String.

Require Import SystemFR.AssocList.
Require Import SystemFR.Tactics.
Require Import SystemFR.Sets.
Require Import SystemFR.Trees.
Require Import SystemFR.Syntax.
Require Import SystemFR.ListUtils.
Require Import SystemFR.SizeLemmas.

Require Import SystemFR.ReducibilityCandidate.

Require Import PeanoNat.

Open Scope list_scope.

Inductive equal_with_relation rel: tree -> tree -> Prop :=
| EWRTVar:
    forall X X',
      lookup Nat.eq_dec rel X = Some X' ->
      lookup Nat.eq_dec (swap rel) X' = Some X ->
      equal_with_relation rel (fvar X type_var) (fvar X' type_var)
| EWRFVar:
    forall X,
      equal_with_relation rel(fvar X term_var) (fvar X term_var)
| EWRLVar:
    forall i tag,
      equal_with_relation rel (lvar i tag) (lvar i tag)
| EWRNoTypeErr:
    equal_with_relation rel notype_err notype_err
| EWRErr:
    forall T1 T2,
      equal_with_relation rel T1 T2 ->
      equal_with_relation rel (err T1) (err T2)
| EWRUU:
    equal_with_relation rel uu uu
| EWRTSize:
    forall t t',
      equal_with_relation rel t t' ->
      equal_with_relation rel (tsize t) (tsize t')
| EWRNoTypeLambda:
    forall t t',
      equal_with_relation rel t t' ->
      equal_with_relation rel (notype_lambda t) (notype_lambda t')
| EWRLambda:
    forall T T' t t',
      equal_with_relation rel T T' ->
      equal_with_relation rel t t' ->
      equal_with_relation rel (lambda T t) (lambda T' t')
| EWRApp:
    forall t1 t1' t2 t2',
      equal_with_relation rel t1 t1' ->
      equal_with_relation rel t2 t2' ->
      equal_with_relation rel (app t1 t2) (app t1' t2')
| EWRForallInst:
    forall t1 t1' t2 t2',
      equal_with_relation rel t1 t1' ->
      equal_with_relation rel t2 t2' ->
      equal_with_relation rel (forall_inst t1 t2) (forall_inst t1' t2')
| EWRPP:
    forall t1 t1' t2 t2',
      equal_with_relation rel t1 t1' ->
      equal_with_relation rel t2 t2' ->
      equal_with_relation rel (pp t1 t2) (pp t1' t2')
| EWRPi1:
    forall t t',
      equal_with_relation rel t t' ->
      equal_with_relation rel (pi1 t) (pi1 t')
| EWRPi2:
    forall t t',
      equal_with_relation rel t t' ->
      equal_with_relation rel (pi2 t) (pi2 t')
| EWRTrue:
    equal_with_relation rel ttrue ttrue
| EWRFalse:
    equal_with_relation rel tfalse tfalse
| EWRIte:
    forall t1 t1' t2 t2' t3 t3',
      equal_with_relation rel t1 t1' ->
      equal_with_relation rel t2 t2' ->
      equal_with_relation rel t3 t3' ->
      equal_with_relation rel (ite t1 t2 t3) (ite t1' t2' t3')
| EWRZero:
    equal_with_relation rel zero zero
| EWRSucc:
    forall t t',
      equal_with_relation rel t t' ->
      equal_with_relation rel (succ t) (succ t')
| EWRNoTypeRec:
    forall t1 t1' t2 t2' t3 t3',
      equal_with_relation rel t1 t1' ->
      equal_with_relation rel t2 t2' ->
      equal_with_relation rel t3 t3' ->
      equal_with_relation rel (notype_rec t1 t2 t3) (notype_rec t1' t2' t3')
| EWRRec:
    forall t1 t1' t2 t2' t3 t3' T T',
      equal_with_relation rel T T' ->
      equal_with_relation rel t1 t1' ->
      equal_with_relation rel t2 t2' ->
      equal_with_relation rel t3 t3' ->
      equal_with_relation rel (rec T t1 t2 t3) (rec T' t1' t2' t3')
| EWRMatch:
    forall t1 t1' t2 t2' t3 t3',
      equal_with_relation rel t1 t1' ->
      equal_with_relation rel t2 t2' ->
      equal_with_relation rel t3 t3' ->
      equal_with_relation rel (tmatch t1 t2 t3) (tmatch t1' t2' t3')
| EWRNoTypeLet:
    forall t1 t1' t2 t2',
      equal_with_relation rel t1 t1' ->
      equal_with_relation rel t2 t2' ->
      equal_with_relation rel (notype_tlet t1 t2) (notype_tlet t1' t2')
| EWRLet:
    forall T T' t1 t1' t2 t2',
      equal_with_relation rel T T' ->
      equal_with_relation rel t1 t1' ->
      equal_with_relation rel t2 t2' ->
      equal_with_relation rel (tlet t1 T t2) (tlet t1' T' t2')

| EWRNoTypeRefl:
    equal_with_relation rel notype_trefl notype_trefl
| EWRRefl:
    forall t1 t1' t2 t2',
      equal_with_relation rel t1 t1' ->
      equal_with_relation rel t2 t2' ->
      equal_with_relation rel (trefl t1 t2) (trefl t1' t2')

| EWRTypeAbs:
    forall t t',
      equal_with_relation rel t t' ->
      equal_with_relation rel (type_abs t) (type_abs t')
| EWRTypeInst:
    forall t t' T T',
      equal_with_relation rel T T' ->
      equal_with_relation rel t t' ->
      equal_with_relation rel (type_inst t T) (type_inst t' T')
| EWRNoTypeInst:
    forall t t',
      equal_with_relation rel t t' ->
      equal_with_relation rel (notype_inst t) (notype_inst t')

| EWRFix:
    forall t t' T T',
      equal_with_relation rel T T' ->
      equal_with_relation rel t t' ->
      equal_with_relation rel (tfix T t) (tfix T' t')
| EWRNoTypeFix:
    forall t t',
      equal_with_relation rel t t' ->
      equal_with_relation rel (notype_tfix t) (notype_tfix t')
| EWRNoTypeFold:
    forall t t',
      equal_with_relation rel t t' ->
      equal_with_relation rel (notype_tfold t) (notype_tfold t')
| EWRFold:
    forall t t' T T',
      equal_with_relation rel T T' ->
      equal_with_relation rel t t' ->
      equal_with_relation rel (tfold T t) (tfold T' t')
| EWRUnfold:
    forall t t',
      equal_with_relation rel t t' ->
      equal_with_relation rel (tunfold t) (tunfold t')
| EWRUnfoldIn:
    forall t1 t1' t2 t2',
      equal_with_relation rel t1 t1' ->
      equal_with_relation rel t2 t2' ->
      equal_with_relation rel (tunfold_in t1 t2) (tunfold_in t1' t2')

| EWRLeft:
    forall t t',
      equal_with_relation rel t t' ->
      equal_with_relation rel (tleft t) (tleft t')

| EWRRight:
    forall t t',
      equal_with_relation rel t t' ->
      equal_with_relation rel (tright t) (tright t')
| EWRSumMatch:
    forall t1 t1' t2 t2' t3 t3',
      equal_with_relation rel t1 t1' ->
      equal_with_relation rel t2 t2' ->
      equal_with_relation rel t3 t3' ->
      equal_with_relation rel (sum_match t1 t2 t3) (sum_match t1' t2' t3')


| EWRUnit:
    equal_with_relation rel T_unit T_unit
| EWRBool:
    equal_with_relation rel T_bool T_bool
| EWRNat:
    equal_with_relation rel T_nat T_nat
| EWRRefine:
    forall t t' T T',
      equal_with_relation rel T T' ->
      equal_with_relation rel t t' ->
      equal_with_relation rel (T_refine T t) (T_refine T' t')
| EWRProd:
    forall A A' B B',
      equal_with_relation rel A A' ->
      equal_with_relation rel B B' ->
      equal_with_relation rel (T_prod A B) (T_prod A' B')
| EWRArrow:
    forall A A' B B',
      equal_with_relation rel A A' ->
      equal_with_relation rel B B' ->
      equal_with_relation rel (T_arrow A B) (T_arrow A' B')
| EWRSum:
    forall A A' B B',
      equal_with_relation rel A A' ->
      equal_with_relation rel B B' ->
      equal_with_relation rel (T_sum A B) (T_sum A' B')
| EWRTLet:
    forall t t' A A' B B',
      equal_with_relation rel t t' ->
      equal_with_relation rel A A' ->
      equal_with_relation rel B B' ->
      equal_with_relation rel (T_let t A B) (T_let t' A' B')
| EWRSingleton:
    forall t t',
      equal_with_relation rel t t' ->
      equal_with_relation rel (T_singleton t) (T_singleton t')
| EWRIntersection:
    forall A A' B B',
      equal_with_relation rel A A' ->
      equal_with_relation rel B B' ->
      equal_with_relation rel (T_intersection A B) (T_intersection A' B')
| EWRUnion:
    forall A A' B B',
      equal_with_relation rel A A' ->
      equal_with_relation rel B B' ->
      equal_with_relation rel (T_union A B) (T_union A' B')

| EWRTop:
    equal_with_relation rel T_top T_top
| EWRBot:
    equal_with_relation rel T_bot T_bot

| EWREqual:
    forall t1 t1' t2 t2',
      equal_with_relation rel t1 t1' ->
      equal_with_relation rel t2 t2' ->
      equal_with_relation rel (T_equal t1 t2) (T_equal t1' t2')


| EWRForall:
    forall A A' B B',
      equal_with_relation rel A A' ->
      equal_with_relation rel B B' ->
      equal_with_relation rel (T_forall A B) (T_forall A' B')
| EWRExists:
    forall A A' B B',
      equal_with_relation rel A A' ->
      equal_with_relation rel B B' ->
      equal_with_relation rel (T_exists A B) (T_exists A' B')
| EWRAbs:
    forall T T',
      equal_with_relation rel T T' ->
      equal_with_relation rel (T_abs T) (T_abs T')
| EWRTRec:
    forall n T0 Ts n' T0' Ts',
      equal_with_relation rel n n' ->
      equal_with_relation rel T0 T0' ->
      equal_with_relation rel Ts Ts' ->
      equal_with_relation rel (T_rec n T0 Ts) (T_rec n' T0' Ts').

Hint Constructors equal_with_relation: bewr.

Lemma equal_with_erased_term1:
  forall t1 t2 rel,
    equal_with_relation rel t1 t2 ->
    is_erased_term t1 ->
    t1 = t2.
Proof.
  induction 1; steps.
Qed.

Lemma equal_with_erased_term2:
  forall t1 t2 rel,
    equal_with_relation rel t1 t2 ->
    is_erased_term t2 ->
    t1 = t2.
Proof.
  induction 1; steps.
Qed.

Ltac t_equal_with_erased :=
  match goal with
  | H1: equal_with_relation ?rel ?t1 ?t2,
    H2: is_erased_term ?t1 |- _ =>
    poseNew (Mark t2 "is_erased");
    unshelve epose proof (equal_with_erased_term1 t1 t2 rel H1 H2)
  | H1: equal_with_relation ?rel ?t1 ?t2,
    H2: is_erased_term ?t2 |- _ =>
    poseNew (Mark t1 "is_erased");
    unshelve epose proof (equal_with_erased_term2 t1 t2 rel H1 H2)
  end.

Lemma equal_with_relation_swap:
  forall t1 t2 rel,
    equal_with_relation rel t1 t2 ->
    equal_with_relation (swap rel) t2 t1.
Proof.
  induction 1; repeat step || rewrite swap_twice in * || constructor.
Qed.

Lemma equal_with_relation_refl:
  forall t rel,
    pfv t type_var = nil ->
    equal_with_relation rel t t.
Proof.
  induction t; repeat step || t_listutils || destruct_tag;
    try solve [ unfold singleton in *; unfold add in *; steps ];
    eauto 6 with bewr.
Qed.

Lemma equal_with_relation_refl2:
  forall t rel,
    (forall x, x ∈ pfv t type_var -> lookup Nat.eq_dec rel x = Some x) ->
    (forall x, x ∈ pfv t type_var -> lookup Nat.eq_dec (swap rel) x = Some x) ->
    equal_with_relation rel t t.
Proof.
  induction t; repeat step || t_listutils || constructor || apply_any || destruct_tag.
Qed.

Lemma equal_with_relation_topen:
  forall rel t1 t2,
    equal_with_relation rel t1 t2 ->
    forall x y k,
      (x ∈ pfv t1 type_var -> False) ->
      (y ∈ pfv t2 type_var -> False) ->
      equal_with_relation ((x,y) :: rel)
                          (topen k t1 (fvar x type_var))
                          (topen k t2 (fvar y type_var)).
Proof.
  induction 1; repeat step || constructor || t_listutils || apply_any.
Qed.

Lemma equal_with_relation_open:
  forall rel t1 t2,
    equal_with_relation rel t1 t2 ->
    forall a k,
      pfv a type_var = nil ->
      equal_with_relation rel (open k t1 a) (open k t2 a).
Proof.
  induction 1; repeat step || constructor;
    eauto using equal_with_relation_refl.
Qed.

Lemma equal_with_relation_size:
  forall t1 t2 rel,
    equal_with_relation rel t1 t2 ->
    size t1 = size t2.
Proof.
  induction 1; steps.
Qed.

Lemma equal_with_relation_pfv:
  forall T T' rel X,
    equal_with_relation rel T T' ->
    X ∈ pfv T type_var ->
    exists X',
      X' ∈ pfv T' type_var /\
      lookup Nat.eq_dec rel X = Some X' /\
      lookup Nat.eq_dec (swap rel) X' = Some X.
Proof.
  induction 1;
    repeat match goal with
           | H1: equal_with_relation ?rel ?T ?T',
             H2: ?X ∈ pfv ?T type_var,
             H3: forall _ _ _, _ -> _ -> _ |- _ => pose proof (H3 _ _ _ H1 H2); clear H3
           | _ => step || t_listutils || destruct_tag
           end;
    try solve [ eexists; repeat step || t_listutils; eauto ].
Qed.

Ltac t_equal_with_relation_pfv :=
  match goal with
  | H1: equal_with_relation ?rel ?T ?T',
    H2: ?X ∈ pfv ?T type_var |- _ =>
    poseNew (Mark H1 "equal_with_relation_pfv");
    pose proof (equal_with_relation_pfv _ _ _ _ H1 H2)
  end.

Lemma equal_with_relation_pfv2:
  forall T T' rel X',
    equal_with_relation rel T T' ->
    X' ∈ pfv T' type_var ->
    exists X,
      X ∈ pfv T type_var /\
      lookup Nat.eq_dec rel X = Some X' /\
      lookup Nat.eq_dec (swap rel) X' = Some X.
Proof.
  intros.
  apply equal_with_relation_swap in H.
  repeat step || t_equal_with_relation_pfv || eexists || rewrite swap_twice in *; eauto.
Qed.

Ltac t_equal_with_relation_pfv2 :=
  match goal with
  | H1: equal_with_relation ?rel ?T ?T',
    H2: ?X ∈ pfv ?T' type_var |- _ =>
    poseNew (Mark H1 "equal_with_relation_pfv2");
    pose proof (equal_with_relation_pfv2 _ _ _ _ H1 H2)
  | _ => t_equal_with_relation_pfv
  end.
