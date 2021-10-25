Require Import Coq.Strings.String.
Require Import PeanoNat.

Require Export SystemFR.SizeLemmas.
Require Export SystemFR.StarLemmas.
Require Export SystemFR.FVLemmasEval.

Open Scope list_scope.

Inductive equal_with_relation tag rel: tree -> tree -> Prop :=
| EWRTVar:
    forall X X',
      lookup PeanoNat.Nat.eq_dec rel X = Some X' ->
      lookup PeanoNat.Nat.eq_dec (swap rel) X' = Some X ->
      equal_with_relation tag rel (fvar X tag) (fvar X' tag)
| EWRFVar:
    forall X tag',
      tag <> tag' ->
      equal_with_relation tag rel (fvar X tag') (fvar X tag')
| EWRLVar:
    forall i tag',
      equal_with_relation tag rel (lvar i tag') (lvar i tag')
| EWRNoTypeErr:
    equal_with_relation tag rel notype_err notype_err
| EWRErr:
    forall T1 T2,
      equal_with_relation tag rel T1 T2 ->
      equal_with_relation tag rel (err T1) (err T2)
| EWRUU:
    equal_with_relation tag rel uu uu
| EWRTSize:
    forall t t',
      equal_with_relation tag rel t t' ->
      equal_with_relation tag rel (tsize t) (tsize t')
| EWRNoTypeLambda:
    forall t t',
      equal_with_relation tag rel t t' ->
      equal_with_relation tag rel (notype_lambda t) (notype_lambda t')
| EWRLambda:
    forall T T' t t',
      equal_with_relation tag rel T T' ->
      equal_with_relation tag rel t t' ->
      equal_with_relation tag rel (lambda T t) (lambda T' t')
| EWRApp:
    forall t1 t1' t2 t2',
      equal_with_relation tag rel t1 t1' ->
      equal_with_relation tag rel t2 t2' ->
      equal_with_relation tag rel (app t1 t2) (app t1' t2')
| EWRForallInst:
    forall t1 t1' t2 t2',
      equal_with_relation tag rel t1 t1' ->
      equal_with_relation tag rel t2 t2' ->
      equal_with_relation tag rel (forall_inst t1 t2) (forall_inst t1' t2')

| EWRPP:
    forall t1 t1' t2 t2',
      equal_with_relation tag rel t1 t1' ->
      equal_with_relation tag rel t2 t2' ->
      equal_with_relation tag rel (pp t1 t2) (pp t1' t2')
| EWRPi1:
    forall t t',
      equal_with_relation tag rel t t' ->
      equal_with_relation tag rel (pi1 t) (pi1 t')
| EWRPi2:
    forall t t',
      equal_with_relation tag rel t t' ->
      equal_with_relation tag rel (pi2 t) (pi2 t')

| EWRBecause:
    forall t1 t1' t2 t2',
      equal_with_relation tag rel t1 t1' ->
      equal_with_relation tag rel t2 t2' ->
      equal_with_relation tag rel (because t1 t2) (because t1' t2')
| EWRGetProof:
    forall t1 t1' t2 t2',
      equal_with_relation tag rel t1 t1' ->
      equal_with_relation tag rel t2 t2' ->
      equal_with_relation tag rel (get_refinement_witness t1 t2) (get_refinement_witness t1' t2')

| EWRTrue:
    equal_with_relation tag rel ttrue ttrue
| EWRFalse:
    equal_with_relation tag rel tfalse tfalse
| EWRIte:
    forall t1 t1' t2 t2' t3 t3',
      equal_with_relation tag rel t1 t1' ->
      equal_with_relation tag rel t2 t2' ->
      equal_with_relation tag rel t3 t3' ->
      equal_with_relation tag rel (ite t1 t2 t3) (ite t1' t2' t3')
| EWRRecognizer:
    forall r t t',
      equal_with_relation tag rel t t' ->
      equal_with_relation tag rel (boolean_recognizer r t) (boolean_recognizer r t')

| EWRZero:
    equal_with_relation tag rel zero zero
| EWRSucc:
    forall t t',
      equal_with_relation tag rel t t' ->
      equal_with_relation tag rel (succ t) (succ t')
| EWRMatch:
    forall t1 t1' t2 t2' t3 t3',
      equal_with_relation tag rel t1 t1' ->
      equal_with_relation tag rel t2 t2' ->
      equal_with_relation tag rel t3 t3' ->
      equal_with_relation tag rel (tmatch t1 t2 t3) (tmatch t1' t2' t3')

| EWRUnaryPrimitive:
    forall o t1 t1',
      equal_with_relation tag rel t1 t1' ->
      equal_with_relation tag rel (unary_primitive o t1) (unary_primitive o t1')
| EWRBinaryPrimitive:
    forall o t1 t1' t2 t2',
      equal_with_relation tag rel t1 t1' ->
      equal_with_relation tag rel t2 t2' ->
      equal_with_relation tag rel (binary_primitive o t1 t2) (binary_primitive o t1' t2')

| EWRNoTypeLet:
    forall t1 t1' t2 t2',
      equal_with_relation tag rel t1 t1' ->
      equal_with_relation tag rel t2 t2' ->
      equal_with_relation tag rel (notype_tlet t1 t2) (notype_tlet t1' t2')
| EWRLet:
    forall T T' t1 t1' t2 t2',
      equal_with_relation tag rel T T' ->
      equal_with_relation tag rel t1 t1' ->
      equal_with_relation tag rel t2 t2' ->
      equal_with_relation tag rel (tlet t1 T t2) (tlet t1' T' t2')

| EWRRefl:
    forall t1 t1' t2 t2',
      equal_with_relation tag rel t1 t1' ->
      equal_with_relation tag rel t2 t2' ->
      equal_with_relation tag rel (trefl t1 t2) (trefl t1' t2')

| EWRTypeAbs:
    forall t t',
      equal_with_relation tag rel t t' ->
      equal_with_relation tag rel (type_abs t) (type_abs t')
| EWRTypeInst:
    forall t t' T T',
      equal_with_relation tag rel T T' ->
      equal_with_relation tag rel t t' ->
      equal_with_relation tag rel (type_inst t T) (type_inst t' T')

| EWRFix:
    forall t t' T T',
      equal_with_relation tag rel T T' ->
      equal_with_relation tag rel t t' ->
      equal_with_relation tag rel (tfix T t) (tfix T' t')
| EWRNoTypeFix:
    forall t t',
      equal_with_relation tag rel t t' ->
      equal_with_relation tag rel (notype_tfix t) (notype_tfix t')

| EWRFold:
    forall t t' T T',
      equal_with_relation tag rel T T' ->
      equal_with_relation tag rel t t' ->
      equal_with_relation tag rel (tfold T t) (tfold T' t')
| EWRUnfold:
    forall t t',
      equal_with_relation tag rel t t' ->
      equal_with_relation tag rel (tunfold t) (tunfold t')
| EWRUnfoldIn:
    forall t1 t1' t2 t2',
      equal_with_relation tag rel t1 t1' ->
      equal_with_relation tag rel t2 t2' ->
      equal_with_relation tag rel (tunfold_in t1 t2) (tunfold_in t1' t2')
| EWRUnfoldPosIn:
    forall t1 t1' t2 t2',
      equal_with_relation tag rel t1 t1' ->
      equal_with_relation tag rel t2 t2' ->
      equal_with_relation tag rel (tunfold_pos_in t1 t2) (tunfold_pos_in t1' t2')

| EWRLeft:
    forall t t',
      equal_with_relation tag rel t t' ->
      equal_with_relation tag rel (tleft t) (tleft t')

| EWRRight:
    forall t t',
      equal_with_relation tag rel t t' ->
      equal_with_relation tag rel (tright t) (tright t')
| EWRSumMatch:
    forall t1 t1' t2 t2' t3 t3',
      equal_with_relation tag rel t1 t1' ->
      equal_with_relation tag rel t2 t2' ->
      equal_with_relation tag rel t3 t3' ->
      equal_with_relation tag rel (sum_match t1 t2 t3) (sum_match t1' t2' t3')


| EWRTypeCheck:
    forall t t' T T',
      equal_with_relation tag rel t t' ->
      equal_with_relation tag rel T T' ->
      equal_with_relation tag rel (typecheck t T) (typecheck t' T')

| EWRUnit:
    equal_with_relation tag rel T_unit T_unit
| EWRBool:
    equal_with_relation tag rel T_bool T_bool
| EWRNat:
    equal_with_relation tag rel T_nat T_nat

| EWRRefine:
    forall t t' T T',
      equal_with_relation tag rel T T' ->
      equal_with_relation tag rel t t' ->
      equal_with_relation tag rel (T_refine T t) (T_refine T' t')
| EWRTypeRefine:
    forall A A' B B',
      equal_with_relation tag rel A A' ->
      equal_with_relation tag rel B B' ->
      equal_with_relation tag rel (T_type_refine A B) (T_type_refine A' B')

| EWRProd:
    forall A A' B B',
      equal_with_relation tag rel A A' ->
      equal_with_relation tag rel B B' ->
      equal_with_relation tag rel (T_prod A B) (T_prod A' B')
| EWRArrow:
    forall A A' B B',
      equal_with_relation tag rel A A' ->
      equal_with_relation tag rel B B' ->
      equal_with_relation tag rel (T_arrow A B) (T_arrow A' B')
| EWRSum:
    forall A A' B B',
      equal_with_relation tag rel A A' ->
      equal_with_relation tag rel B B' ->
      equal_with_relation tag rel (T_sum A B) (T_sum A' B')

| EWRIntersection:
    forall A A' B B',
      equal_with_relation tag rel A A' ->
      equal_with_relation tag rel B B' ->
      equal_with_relation tag rel (T_intersection A B) (T_intersection A' B')
| EWRUnion:
    forall A A' B B',
      equal_with_relation tag rel A A' ->
      equal_with_relation tag rel B B' ->
      equal_with_relation tag rel (T_union A B) (T_union A' B')

| EWRTop:
    equal_with_relation tag rel T_top T_top
| EWRBot:
    equal_with_relation tag rel T_bot T_bot

| EWREqual:
    forall t1 t1' t2 t2',
      equal_with_relation tag rel t1 t1' ->
      equal_with_relation tag rel t2 t2' ->
      equal_with_relation tag rel (T_equiv t1 t2) (T_equiv t1' t2')


| EWRForall:
    forall A A' B B',
      equal_with_relation tag rel A A' ->
      equal_with_relation tag rel B B' ->
      equal_with_relation tag rel (T_forall A B) (T_forall A' B')
| EWRExists:
    forall A A' B B',
      equal_with_relation tag rel A A' ->
      equal_with_relation tag rel B B' ->
      equal_with_relation tag rel (T_exists A B) (T_exists A' B')
| EWRAbs:
    forall T T',
      equal_with_relation tag rel T T' ->
      equal_with_relation tag rel (T_abs T) (T_abs T')
| EWRTRec:
    forall n T0 Ts n' T0' Ts',
      equal_with_relation tag rel n n' ->
      equal_with_relation tag rel T0 T0' ->
      equal_with_relation tag rel Ts Ts' ->
      equal_with_relation tag rel (T_rec n T0 Ts) (T_rec n' T0' Ts')
.

#[export]
Hint Constructors equal_with_relation: equal_with_relation.

Lemma equal_with_relation_deterministic:
  forall tag rel t t1,
    equal_with_relation tag rel t t1 ->
    forall t2,
      equal_with_relation tag rel t t2 ->
      t1 = t2.
Proof.
  induction 1; inversion 1;
    repeat step || instantiate_any; eauto with equal_with_relation.
Qed.

Ltac equal_with_relation_deterministic :=
  match goal with
  | H1: equal_with_relation ?tag ?rel ?t ?t1,
    H2: equal_with_relation ?tag ?rel ?t ?t2 |- _ =>
    pose proof (equal_with_relation_deterministic _ _ _ _ H1 _ H2); clear H1
  end.

Lemma equal_with_erased_term1:
  forall t1 t2 rel,
    equal_with_relation type_var rel t1 t2 ->
    is_erased_term t1 ->
    t1 = t2.
Proof.
  induction 1; steps.
Qed.

Lemma equal_with_erased_term2:
  forall t1 t2 rel,
    equal_with_relation type_var rel t1 t2 ->
    is_erased_term t2 ->
    t1 = t2.
Proof.
  induction 1; steps.
Qed.

Ltac equal_with_erased :=
  match goal with
  | H1: equal_with_relation type_var ?rel ?t1 ?t2,
    H2: is_erased_term ?t1 |- _ =>
    poseNew (Mark t2 "is_erased");
    unshelve epose proof (equal_with_erased_term1 t1 t2 rel H1 H2)
  | H1: equal_with_relation type_var ?rel ?t1 ?t2,
    H2: is_erased_term ?t2 |- _ =>
    poseNew (Mark t1 "is_erased");
    unshelve epose proof (equal_with_erased_term2 t1 t2 rel H1 H2)
  end.

Lemma equal_with_relation_swap:
  forall t1 t2 tag rel,
    equal_with_relation tag rel t1 t2 ->
    equal_with_relation tag (swap rel) t2 t1.
Proof.
  induction 1; repeat step || rewrite swap_twice in * || constructor.
Qed.

Lemma equal_with_relation_refl:
  forall t tag rel,
    pfv t tag = nil ->
    equal_with_relation tag rel t t.
Proof.
  induction t; repeat step || list_utils || destruct_tag;
    try solve [ unfold singleton in *; unfold add in *; steps ];
    eauto 6 with equal_with_relation.
Qed.

Lemma equal_with_relation_refl2:
  forall t tag rel,
    (forall x, x ∈ pfv t tag -> lookup PeanoNat.Nat.eq_dec rel x = Some x) ->
    (forall x, x ∈ pfv t tag -> lookup PeanoNat.Nat.eq_dec (swap rel) x = Some x) ->
    equal_with_relation tag rel t t.
Proof.
  induction t;
    repeat light || destruct_match || constructor || list_utils || apply_any.
Qed.

Lemma equal_with_relation_topen:
  forall tag rel t1 t2,
    equal_with_relation tag rel t1 t2 ->
    forall x y k,
      (x ∈ pfv t1 tag -> False) ->
      (y ∈ pfv t2 tag -> False) ->
      equal_with_relation tag ((x,y) :: rel)
                          (topen k t1 (fvar x tag))
                          (topen k t2 (fvar y tag)).
Proof.
  induction 1; repeat step || constructor || list_utils || apply_any.
Qed.

Lemma equal_with_relation_open:
  forall tag rel t1 t2,
    equal_with_relation tag rel t1 t2 ->
    forall x y k,
      (x ∈ pfv t1 tag -> False) ->
      (y ∈ pfv t2 tag -> False) ->
      equal_with_relation tag ((x,y) :: rel)
                          (open k t1 (fvar x tag))
                          (open k t2 (fvar y tag)).
Proof.
  induction 1; repeat step || constructor || list_utils || apply_any.
Qed.

Lemma equal_with_relation_open2:
  forall tag rel t1 t2,
    equal_with_relation tag rel t1 t2 ->
    forall k v1 v2,
      equal_with_relation tag rel v1 v2 ->
      equal_with_relation tag rel (open k t1 v1) (open k t2 v2).
Proof.
  induction 1; repeat step; eauto 6 with equal_with_relation.
Qed.

Lemma equal_with_relation_size:
  forall tag rel t1 t2,
    equal_with_relation tag rel t1 t2 ->
    type_nodes t1 = type_nodes t2.
Proof.
  induction 1; steps.
Qed.

Lemma equal_with_relation_pfv:
  forall T T' tag rel X,
    equal_with_relation tag rel T T' ->
    X ∈ pfv T tag ->
    exists X',
      X' ∈ pfv T' tag /\
      lookup PeanoNat.Nat.eq_dec rel X = Some X' /\
      lookup PeanoNat.Nat.eq_dec (swap rel) X' = Some X.
Proof.
  induction 1;
    repeat match goal with
           | H1: equal_with_relation ?tag ?rel ?T ?T',
             H2: ?X ∈ pfv ?T ?tag,
             H3: forall _ _ _, _ -> _ -> _ |- _ => pose proof (H3 _ _ _ H1 H2); clear H3
           | _ => step || list_utils || destruct_tag
           end;
    try solve [ eexists; repeat step || list_utils; eauto ].
Qed.

Ltac t_equal_with_relation_pfv :=
  match goal with
  | H1: equal_with_relation ?tag ?rel ?T ?T',
    H2: ?X ∈ pfv ?T ?tag |- _ =>
    poseNew (Mark H1 "equal_with_relation_pfv");
    pose proof (equal_with_relation_pfv _ _ _ _ _ H1 H2)
  end.

Lemma equal_with_relation_pfv2:
  forall tag rel T T' X',
    equal_with_relation tag rel T T' ->
    X' ∈ pfv T' tag ->
    exists X,
      X ∈ pfv T tag /\
      lookup PeanoNat.Nat.eq_dec rel X = Some X' /\
      lookup PeanoNat.Nat.eq_dec (swap rel) X' = Some X.
Proof.
  intros.
  apply equal_with_relation_swap in H.
  repeat step || t_equal_with_relation_pfv || eexists || rewrite swap_twice in *; eauto.
Qed.

Ltac t_equal_with_relation_pfv2 :=
  match goal with
  | H1: equal_with_relation ?tag ?rel ?T ?T',
    H2: ?X ∈ pfv ?T' ?tag |- _ =>
    poseNew (Mark H1 "equal_with_relation_pfv2");
    pose proof (equal_with_relation_pfv2 _ _ _ _ _ H1 H2)
  | _ => t_equal_with_relation_pfv
  end.

Lemma equal_with_relation_pfv_nil:
  forall T T' rel tag,
    equal_with_relation tag rel T T' ->
    pfv T tag = nil ->
    pfv T' tag = nil.
Proof.
  induction 1; repeat step || list_utils || unfold singleton, add in *.
Qed.

Lemma equal_with_relation_pfv_nil2:
  forall T T' rel tag,
    equal_with_relation tag rel T T' ->
    pfv T' tag = nil ->
    pfv T tag = nil.
Proof.
  induction 1; repeat step || list_utils || unfold singleton, add in *.
Qed.

Ltac t_ewr_nil :=
  match goal with
  | H1: equal_with_relation ?tag ?rel ?T ?T',
    H2: pfv ?T _ = nil |- _ =>
    poseNew (Mark T' "ewr_nil");
    pose proof (equal_with_relation_pfv_nil _ _ _ _ H1 H2)
  | H1: equal_with_relation ?tag ?rel ?T ?T',
    H2: pfv ?T' _ = nil |- _ =>
    poseNew (Mark T "ewr_nil2");
    pose proof (equal_with_relation_pfv_nil2 _ _ _ _ H1 H2)
  end.

Lemma equal_with_relation_value:
  forall tag rel v1 v2,
    equal_with_relation tag rel v1 v2 ->
    cbv_value v1 ->
    cbv_value v2.
Proof.
  induction 1; repeat step || step_inversion cbv_value;
    eauto with values.
Qed.

Lemma equal_with_relation_value2:
  forall tag rel v1 v2,
    equal_with_relation tag rel v1 v2 ->
    cbv_value v2 ->
    cbv_value v1.
Proof.
  induction 1; repeat step || step_inversion cbv_value;
    eauto with values.
Qed.

Lemma equal_with_relation_build_nat:
  forall n t rel tag,
    equal_with_relation tag rel t (build_nat n) ->
    t = build_nat n.
Proof.
  induction n;
    repeat steps || step_inversion equal_with_relation.
  apply IHn in H2; steps.
Qed.

Lemma equal_with_relation_build_nat2:
  forall n t rel tag,
    equal_with_relation tag rel (build_nat n) t ->
    t = build_nat n.
Proof.
  induction n;
    repeat steps || step_inversion equal_with_relation.
  apply IHn in H1; steps.
Qed.


Ltac t_ewr_value :=
  match goal with
  | H1: equal_with_relation _ _ ?v ?v2, H2: cbv_value ?v |- _ =>
    poseNew (Mark v2 "ewr_value");
    pose proof (equal_with_relation_value _ _ _ _ H1 H2)
  | H1: equal_with_relation _ _ ?v1 ?v, H2: cbv_value ?v |- _ =>
    poseNew (Mark v1 "ewr_value");
    pose proof (equal_with_relation_value2 _ _ _ _ H1 H2)
  end.

Lemma equal_with_relation_tsize:
  forall tag rel t1 t2,
    equal_with_relation tag rel t1 t2 ->
    tsize_semantics t1 = tsize_semantics t2.
Proof.
  induction 1; steps.
Qed.

Lemma equal_with_relation_pair:
  forall tag rel t1 t2,
    equal_with_relation tag rel t1 t2 ->
    is_pair t1 = is_pair t2.
Proof.
  induction 1; steps.
Qed.

Lemma equal_with_relation_lambda:
  forall tag rel t1 t2,
    equal_with_relation tag rel t1 t2 ->
    is_lambda t1 = is_lambda t2.
Proof.
  induction 1; steps.
Qed.

Lemma equal_with_relation_succ:
  forall tag rel t1 t2,
    equal_with_relation tag rel t1 t2 ->
    is_succ t1 = is_succ t2.
Proof.
  induction 1; steps.
Qed.

Lemma equal_with_relation_nat:
  forall tag rel n,
    equal_with_relation tag rel (build_nat n) (build_nat n).
Proof.
  induction n; repeat step || constructor.
Qed.

Lemma equal_with_relation_pair_refl:
  forall tag rel t,
    equal_with_relation tag rel (is_pair t) (is_pair t).
Proof.
  destruct t; repeat step.
Qed.

Lemma equal_with_relation_succ_refl:
  forall tag rel t,
    equal_with_relation tag rel (is_succ t) (is_succ t).
Proof.
  destruct t; repeat step.
Qed.

Lemma equal_with_relation_lambda_refl:
  forall tag rel t,
    equal_with_relation tag rel (is_lambda t) (is_lambda t).
Proof.
  destruct t; repeat step.
Qed.

Lemma equal_with_relation_scbv_step:
  forall tag rel t1 t2,
    equal_with_relation tag rel t1 t2 ->
    forall t1',
      t1 ~> t1' ->
      exists t2',
        t2 ~> t2' /\
        equal_with_relation tag rel t1' t2'.
Proof.
  induction 1; inversion 1;
    repeat step || t_ewr_nil || t_ewr_value || instantiate_any ||
      step_inversion equal_with_relation ||
      apply equal_with_relation_open2 ||
      eapply_anywhere equal_with_relation_build_nat2 ||
      (erewrite equal_with_relation_tsize by eauto) ||
      (erewrite equal_with_relation_lambda by eauto) ||
      (erewrite equal_with_relation_succ by eauto) ||
      (erewrite equal_with_relation_pair by eauto) ||
      (eexists; split; [ solve [ eauto with smallstep ] | idtac ]);
      eauto with equal_with_relation;
      eauto using equal_with_relation_nat with smallstep;
      eauto using equal_with_relation_pair_refl with smallstep;
      eauto using equal_with_relation_lambda_refl with smallstep;
      eauto using equal_with_relation_succ_refl with smallstep.
Qed.


Ltac equal_with_relation_scbv_step :=
  match goal with
  | H1: equal_with_relation _ ?rel ?t1 ?t2, H2: ?t1 ~> ?t1' |- _ =>
    poseNew (Mark (H1,H2) "ewr_scbv_step");
    pose proof (equal_with_relation_scbv_step _ _ _ _ H1 _ H2)
  end.

Lemma equal_with_relation_star:
  forall t1 t1',
    t1 ~>* t1' ->
    forall tag rel t2,
      equal_with_relation tag rel t1 t2 ->
      exists t2',
        t2 ~>* t2' /\
        equal_with_relation tag rel t1' t2'.
Proof.
  induction 1;
    repeat match goal with
           | _ => step || equal_with_relation_scbv_step
           | H1: forall _ _ _, equal_with_relation _ _ _ _ -> _,
             H2: equal_with_relation _ _ _ _ |- _ => apply H1 in H2
           end; eauto with smallstep star.
Qed.

Lemma equal_with_relation_star2:
  forall tag rel t1 t2 t2',
    t2 ~>* t2' ->
    equal_with_relation tag rel t1 t2 ->
    exists t1',
      t1 ~>* t1' /\
      equal_with_relation tag rel t1' t2'.
Proof.
  intros.
  apply equal_with_relation_swap in H0.
  eapply equal_with_relation_star in H0; try eassumption; steps.
  eexists; split; eauto.
  apply equal_with_relation_swap in H2;
    repeat step || rewrite swap_twice in *.
Qed.

Ltac t_ewr_star :=
  match goal with
  | H1: equal_with_relation _ ?rel ?t1 ?t2, H2: ?t1 ~>* ?t1' |- _ =>
    poseNew (Mark 0 "ewr_star");
    pose proof (equal_with_relation_star _ _ _ H2 _ _ H1)
  | H1: equal_with_relation _ ?rel ?t1 ?t2, H2: ?t2 ~>* ?t2' |- _ =>
    poseNew (Mark 0 "ewr_star");
    pose proof (equal_with_relation_star2 _ _ _ _ _ H2 H1)
  end.

Ltac equal_with_relation_scbv_step_back :=
  match goal with
  | H1: equal_with_relation _ ?rel ?t1 ?t2, H2: ?t2 ~> ?t2' |- _ =>
    poseNew (Mark (H1,H2) "ewr_scbv_step");
    unshelve epose proof (equal_with_relation_scbv_step _ (swap rel) t2 t1 _ _ H2);
    eauto using equal_with_relation_swap
  end.

Lemma equal_with_relation_irred:
  forall tag rel T1 T2,
    equal_with_relation tag rel T1 T2 ->
    irred T1 ->
    irred T2.
Proof.
  unfold irred; repeat step || equal_with_relation_scbv_step_back;
    eauto.
Qed.

Lemma equal_with_relation_irred_back:
  forall tag rel T1 T2,
    equal_with_relation tag rel T1 T2 ->
    irred T2 ->
    irred T1.
Proof.
  intros; eauto using equal_with_relation_irred, equal_with_relation_swap.
Qed.


Lemma equal_with_relation_erased_term:
  forall tag rel t1 t2,
    equal_with_relation tag rel t1 t2 ->
    is_erased_term t1 ->
    is_erased_term t2.
Proof.
  induction 1; steps.
Qed.

Lemma equal_with_relation_erased_type:
  forall tag rel T1 T2,
    equal_with_relation tag rel T1 T2 ->
    is_erased_type T1 ->
    is_erased_type T2.
Proof.
  induction 1; steps; eauto using equal_with_relation_erased_term.
Qed.

Lemma equal_with_relation_erased_type_back:
  forall tag rel T1 T2,
    equal_with_relation tag rel T1 T2 ->
    is_erased_type T2 ->
    is_erased_type T1.
Proof.
  eauto using equal_with_relation_swap, equal_with_relation_erased_type.
Qed.

#[export]
Hint Immediate equal_with_relation_erased_term: erased.
#[export]
Hint Immediate equal_with_relation_erased_type: erased.
#[export]
Hint Immediate equal_with_relation_erased_type_back: erased.
