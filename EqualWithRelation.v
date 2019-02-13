Require Import Coq.Strings.String.

Require Import Termination.AssocList.
Require Import Termination.Tactics.
Require Import Termination.Sets.
Require Import Termination.Trees.
Require Import Termination.Syntax.
Require Import Termination.ListUtils.
Require Import Termination.SizeLemmas.

Require Import Termination.ReducibilityCandidate.

Require Import PeanoNat.

Open Scope list_scope.

Fixpoint equal_with_relation rel t t' :=
  match t, t' with
  | fvar x type_var, fvar x' type_var =>
    lookup Nat.eq_dec rel x = Some x' /\
    lookup Nat.eq_dec (swap rel) x' = Some x
  | fvar x term_var, fvar x' term_var => x = x'
  | lvar i tag, lvar i' tag' => i = i' /\ tag = tag'
  | err, err => True

  | uu, uu => True

  | notype_lambda t, notype_lambda t' => equal_with_relation rel t t'
  | lambda T t, lambda T' t' => equal_with_relation rel T T' /\ equal_with_relation rel t t'
  | app t1 t2, app t1' t2' => equal_with_relation rel t1 t1' /\ equal_with_relation rel t2 t2'

  | pp t1 t2, pp t1' t2' => equal_with_relation rel t1 t1' /\ equal_with_relation rel t2 t2'
  | pi1 t, pi1 t' => equal_with_relation rel t t'
  | pi2 t, pi2 t' => equal_with_relation rel t t'

  | ttrue, ttrue => True
  | tfalse, tfalse => True
  | ite t1 t2 t3, ite t1' t2' t3' =>
      equal_with_relation rel t1 t1' /\
      equal_with_relation rel t2 t2' /\
      equal_with_relation rel t3 t3'

  | zero, zero => True
  | succ t, succ t' => equal_with_relation rel t t'
  | notype_rec t1 t2 t3, notype_rec t1' t2' t3' =>
      equal_with_relation rel t1 t1' /\
      equal_with_relation rel t2 t2' /\
      equal_with_relation rel t3 t3'
  | rec T t1 t2 t3, rec T' t1' t2' t3' =>
      equal_with_relation rel T T' /\
      equal_with_relation rel t1 t1' /\
      equal_with_relation rel t2 t2' /\
      equal_with_relation rel t3 t3'
  | tmatch t1 t2 t3, tmatch t1' t2' t3' =>
      equal_with_relation rel t1 t1' /\
      equal_with_relation rel t2 t2' /\
      equal_with_relation rel t3 t3'

  | notype_tlet t1 t2, notype_tlet t1' t2' =>
      equal_with_relation rel t1 t1' /\
      equal_with_relation rel t2 t2'
  | tlet t1 A t2, tlet t1' A' t2' =>
      equal_with_relation rel A A' /\
      equal_with_relation rel t1 t1' /\
      equal_with_relation rel t2 t2'
  | trefl, trefl => True

  | type_abs t, type_abs t' =>
      equal_with_relation rel t t'
  | type_inst t T, type_inst t' T' =>
      equal_with_relation rel t t' /\
      equal_with_relation rel T T'
  | notype_inst t, notype_inst t' =>
      equal_with_relation rel t t'

  | tfix T t, tfix T' t' =>
      equal_with_relation rel T T' /\
      equal_with_relation rel t t'
  | notype_tfix t, notype_tfix t' =>
      equal_with_relation rel t t'
  | tfold t, tfold t' =>
      equal_with_relation rel t t'
  | tunfold t, tunfold t' =>
      equal_with_relation rel t t'

  | tleft t, tleft t' =>
      equal_with_relation rel t t'
  | tright t, tright t' =>
      equal_with_relation rel t t'
  | sum_match t tl tr, sum_match t' tl' tr' =>
      equal_with_relation rel t t' /\
      equal_with_relation rel tl tl' /\
      equal_with_relation rel tr tr'

  | T_unit, T_unit => True
  | T_bool, T_bool => True
  | T_nat, T_nat => True
  | T_refine A p, T_refine A' p' =>
      equal_with_relation rel A A' /\
      equal_with_relation rel p p'
  | T_prod A B, T_prod A' B' =>
      equal_with_relation rel A A' /\
      equal_with_relation rel B B'
  | T_arrow A B, T_arrow A' B' =>
      equal_with_relation rel A A' /\
      equal_with_relation rel B B'
  | T_sum A B, T_sum A' B' =>
      equal_with_relation rel A A' /\
      equal_with_relation rel B B'

  | T_let t A B, T_let t' A' B' =>
      equal_with_relation rel t t' /\
      equal_with_relation rel A A' /\
      equal_with_relation rel B B'
  | T_singleton t, T_singleton t' =>
      equal_with_relation rel t t'
  | T_intersection A B, T_intersection A' B' =>
      equal_with_relation rel A A' /\
      equal_with_relation rel B B'
  | T_union A B, T_union A' B' =>
      equal_with_relation rel A A' /\
      equal_with_relation rel B B'
  | T_top, T_top => True
  | T_bot, T_bot => True
  | T_equal t1 t2, T_equal t1' t2' =>
      equal_with_relation rel t1 t1' /\
      equal_with_relation rel t2 t2'
  | T_forall A B, T_forall A' B' =>
      equal_with_relation rel A A' /\
      equal_with_relation rel B B'
  | T_exists A B, T_exists A' B' =>
      equal_with_relation rel A A' /\
      equal_with_relation rel B B'
  | T_abs T, T_abs T' =>
      equal_with_relation rel T T'
  | T_rec n T0 Ts, T_rec n' T0' Ts' =>
      equal_with_relation rel n n' /\
      equal_with_relation rel T0 T0' /\
      equal_with_relation rel Ts Ts'

  | _, _ => False
  end.


Lemma equal_with_erased_term1:
  forall t1 t2 rel,
    equal_with_relation rel t1 t2 ->
    is_erased_term t1 ->
    t1 = t2.
Proof.
  induction t1;
    repeat match goal with
           | H: forall x, _, H2: equal_with_relation _ _ _ |- _ =>
            unshelve epose proof (H _ _ H2); clear H2
           | _ => step
           end.
Qed.

Lemma equal_with_erased_term2:
  forall t1 t2 rel,
    equal_with_relation rel t1 t2 ->
    is_erased_term t2 ->
    t1 = t2.
Proof.
  induction t1;
    repeat match goal with
           | H: forall x, _, H2: equal_with_relation _ _ _ |- _ =>
              unshelve epose proof (H _ _ H2); clear H2
           | _ => step
           end.
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
  induction t1; repeat step || rewrite swap_twice in *.
Qed.

Lemma equal_with_relation_refl:
  forall t rel,
    pfv t type_var = nil ->
    equal_with_relation rel t t.
Proof.
  induction t; repeat step || t_listutils;
   try solve [ unfold singleton in *; unfold add in *; steps ].
Qed.

Lemma equal_with_relation_refl2:
  forall t rel,
    (forall x, x ∈ pfv t type_var -> lookup Nat.eq_dec rel x = Some x) ->
    (forall x, x ∈ pfv t type_var -> lookup Nat.eq_dec (swap rel) x = Some x) ->
    equal_with_relation rel t t.
Proof.
  induction t; repeat step || t_listutils || eapply_any.
Qed.

Lemma equal_with_relation_topen:
  forall t1 t2 x y rel k,
    (x ∈ pfv t1 type_var -> False) ->
    (y ∈ pfv t2 type_var -> False) ->
    equal_with_relation rel t1 t2 ->
    equal_with_relation ((x,y) :: rel)
                        (topen k t1 (fvar x type_var))
                        (topen k t2 (fvar y type_var)).
Proof.
  induction t1; destruct t2; intros; try destruct_tag;
    simpl in *; intuition auto;
      try solve [ repeat step || t_listutils ].
Qed.

Lemma equal_with_relation_open:
  forall t1 t2 a rel k,
    pfv a type_var = nil ->
    equal_with_relation rel t1 t2 ->
    equal_with_relation rel (open k t1 a) (open k t2 a).
Proof.
  induction t1; destruct t2; intros; try destruct_tag; simpl in *; intuition auto; steps;
    eauto using equal_with_relation_refl.
Qed.

Lemma equal_with_relation_size:
  forall t1 t2 rel,
    equal_with_relation rel t1 t2 ->
    size t1 = size t2.
Proof.
  induction t1;
    repeat match goal with
           | _ => step
           | H: _ |- _ => erewrite H; eauto
           end.
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
  induction T;
    repeat match goal with
           | H1: equal_with_relation ?rel ?T ?T',
             H2: ?X ∈ pfv ?T type_var,
             H3: forall _ _ _, _ -> _ -> _ |- _ => pose proof (H3 _ _ _ H1 H2); clear H3
           | _ => step || t_listutils || destruct_tag
           end; eauto;
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
