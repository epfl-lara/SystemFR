Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Init.Datatypes.
Require Import Coq.Arith.PeanoNat.

Require Import Termination.Syntax.
Require Import Termination.Tactics.
Require Import Termination.ListUtils.
Require Import Termination.AssocList.
Require Import Termination.Sets.
Require Import Termination.SetLemmas.

Ltac slow_instantiations :=
  match goal with
  | H1: ?x ∈ fv ?t, H2: forall x, x ∈ fv (open _ ?t _) -> _ |- _ =>
    unshelve epose proof (H2 x _); clear H2
  | H1: ?x ∈ fv ?t, H2: forall x, x ∈ fv (open _ ?t _) -> _ |- _ =>
    unshelve epose proof (H2 x _); clear H2
  | H1: ?x ∈ fv ?t, H2: forall x, x ∈ fv (open _ (open _ ?t _) _) -> _ |- _ =>
    unshelve epose proof (H2 x _); clear H2
  | H1: ?x ∈ fv ?t, H2: forall x, x ∈ fv (open _ (open _ ?t _) _) -> _ |- _ =>
    unshelve epose proof (H2 x _); clear H2
  | H1: ?x ∈ ?L, H2: forall x, x ∈ ?L ++ _ -> _ |- _ =>
    unshelve epose proof (H2 x _); clear H2
  end.

Lemma fv_context_support:
  forall gamma x,
   x ∈ support gamma ->
   x ∈ fv_context gamma.
Proof.
  induction gamma; repeat step || t_listutils.
Qed.

Hint Resolve fv_context_support: bfv.

Lemma fv_lookup:
  forall gamma x T,
    lookup Nat.eq_dec gamma x = Some T ->
    subset (fv T) (fv_context gamma).
Proof.
  induction gamma; repeat step || t_sets || unfold subset in * || t_listutils; eauto.
Qed.

Lemma fv_lookup2:
  forall gamma x T y,
    lookup Nat.eq_dec gamma x = Some T ->
    y ∈ fv T ->
    y ∈ fv_context gamma.
Proof.
  induction gamma; repeat step || t_sets || unfold subset in * || t_listutils; eauto.
Qed.

Lemma fv_lookup3:
  forall gamma x T,
    lookup Nat.eq_dec gamma x = Some T ->
    x ∈ fv_context gamma.
Proof.
  induction gamma; repeat step || t_listutils; eauto.
Qed.

Lemma fv_lookup4:
  forall l x T y,
    lookup Nat.eq_dec l x = Some T ->
    y ∈ fv T ->
    y ∈ fv_range l.
Proof.
  induction l; repeat step || t_sets || unfold subset in * || t_listutils; eauto.
Qed.

Hint Resolve fv_lookup: bfv.
Hint Resolve fv_lookup2: bfv.
Hint Resolve fv_lookup3: bfv.
Hint Resolve fv_lookup4: bfv.

Lemma fv_in_open:
  forall t x r k,
    x ∈ fv t ->
    x ∈ fv (open k t r).
Proof.
  induction t; repeat step || t_listutils.
Qed.

Hint Resolve fv_in_open: bfv.

Lemma fv_open:
  forall t rep k,
    subset (fv (open k t rep)) (fv t ++ fv rep).
Proof.
  induction t;
    repeat match goal with
           | H: _, H2: _ |- _ =>
             apply (H _ _ _) in H2
           | _ => step || t_listutils
           | _ => unfold subset in *
           end.
Qed.

Lemma fv_open2:
  (forall t rep k y,
     y ∈ fv (open k t rep) ->
     y ∈ fv t ++ fv rep).
Proof.
  induction t;
    repeat match goal with
           | H: _, H2: _ |- _ =>
             apply (H _ _ _) in H2
           | _ => step || t_listutils
           end.
Qed.

Lemma fv_nils_open:
  forall t rep k,
    fv t = nil ->
    fv rep = nil ->
    fv (open k t rep) = nil.
Proof.
  intros;
  rewrite <- (empty_list_rewrite nat) in *;
    repeat match goal with
           | H: ?x ∈ fv (open _ _ _) |- _ =>
               poseNew (Mark H "fv_open2");
               pose proof (fv_open2 _ _ _ _ H) 
           | _ => step || t_listutils
           end; eauto.
Qed.

Hint Resolve fv_nils_open: bfv.
  
  
Lemma fv_subst:
  forall t x rep, subset (fv (substitute t ((x,rep) :: nil))) (((fv t) - x) ++ fv rep).
Proof.
  induction t;
    repeat match goal with
           | H: forall x, _, H2: _ |- _ => apply H in H2 
           | _ => step || t_listutils || unfold subset in *
           end; eauto with sets.
Qed.

Hint Resolve fv_subst: bfv.

Lemma fv_subst2:
  forall t l,
    subset (fv      (substitute t l))      (((fv t) -- (support l)) ++ fv_range l).
Proof.
  induction t;
    repeat match goal with
           | H: forall x, _, H2: _ |- _ => apply H in H2 
           | _ => step || t_listutils || unfold subset in *
           end;
    eauto with sets;
    eauto with bfv.
Qed.

Hint Resolve fv_subst2: bfv.

Lemma fv_subst3:
  forall t x rep y,
      y <> x ->
      y ∈ fv t ->
      y ∈ fv (substitute t ((x,rep) :: nil)).
Proof.
  induction t;
    repeat match goal with
    | H: forall x, _, H2: _ |- _ => apply H in H2 
    | H: forall x rep z, z ∈ ?F ?t - x -> _,
      H2: ?z ∈ ?F ?t,
      H3: ?z = ?y -> False
      |- context[(?y,?rep)] =>
         poseNew (Mark (H,z,y,rep) "instance");
         unshelve epose proof (H y rep z _)
    | _ => step || t_listutils || unfold subset in *
    end.  
Qed.

Hint Resolve fv_subst3: bfv.

Lemma fv_subst3_context:
  forall gamma x rep y,
    y <> x ->    
    y ∈ fv_context gamma ->
    y ∈ fv_context (substitute_context gamma ((x,rep) :: nil)).
Proof.
  induction gamma;
    repeat match goal with
           | _ => step || t_listutils || unfold subset in *
           end; eauto with bfv.
Qed.  

Hint Resolve fv_subst3_context: bfv.

Lemma closed_mapping_lookup:
  forall l x t,
    closed_mapping l ->
    lookup Nat.eq_dec l x = Some t ->
    fv t = nil.
Proof.
  induction l; steps; eauto.
Qed.

Hint Resolve closed_mapping_lookup: bfv.

Lemma closed_mapping_range:
  forall l t,
    closed_mapping l ->
    t ∈ range l ->
    fv t = nil.
Proof.
  induction l; steps; eauto.
Qed.

Hint Resolve closed_mapping_range: bfv.
  
Lemma fv_nils:
  forall t l,
    fv t = nil ->
    closed_mapping l ->
    fv (substitute t l) = nil.
Proof.
  induction t;
    repeat match goal with
           | H: forall x, _ -> _ -> _, H1: _, H2: _ |- _ => pose proof (H _ H1 H2); clear H
           | H: _ = nil |- _ => rewrite H
           | _ => step || t_listutils
           end; eauto with bfv.
Qed.

Hint Resolve fv_nils: bfv.

Lemma closed_mapping_fv:
  forall l x,
    closed_mapping l ->
    x ∈ fv_range l ->
    False.
Proof.
  induction l; repeat step || t_listutils; eauto.
Qed.

Lemma closed_mapping_fv2:
  forall l x y t,
    closed_mapping l ->
    lookup Nat.eq_dec l x = Some t ->
    y ∈ fv t ->
    False.
Proof.
  induction l; repeat step || t_listutils; eauto.
Qed.
  
Lemma fv_nils2:
  forall t l,
    subset (fv t) (support l) ->
    closed_mapping l ->
    fv (substitute t l) = nil.
Proof.
  induction t;
    repeat match goal with
           | H: forall x, _ -> _ -> _, H1: _, H2: _ |- _ => pose proof (H _ H1 H2); clear H
           | H: forall x, ?s = x \/ False -> _ |- _ => unshelve epose proof (H s _); clear H
           | H1: forall x, x ∈ ?l ++ _ -> _, H2: ?x ∈ ?l |- _ =>
             poseNew (Mark (x,l) "instance");
             unshelve epose proof (H1 x _)
           | H1: forall x, x ∈ _ ++ ?l -> _, H2: ?x ∈ ?l |- _ =>
             poseNew (Mark (x,l) "instance right");
             unshelve epose proof (H1 x _)
           | H1: forall x, x ∈ _ ++ _ ++ ?l -> _, H2: ?x ∈ ?l |- _ =>
             poseNew (Mark (x,l) "instance rright");
             unshelve epose proof (H1 x _)
           | H1: forall x, x ∈ _ ++ _ ++ ?l ++ _ -> _, H2: ?x ∈ ?l |- _ =>
             poseNew (Mark (x,l) "instance 3/4");
             unshelve epose proof (H1 x _)
           | H1: forall x, x ∈ _ ++ _ ++ _ ++ ?l -> _, H2: ?x ∈ ?l |- _ =>
             poseNew (Mark (x,l) "instance 4/4");
             unshelve epose proof (H1 x _)
           | H1: forall x, x ∈ _ ++ ?l ++ _ -> _, H2: ?x ∈ ?l |- _ =>
             poseNew (Mark (x,l) "instance middle");
             unshelve epose proof (H1 x _)
           | H: _ = nil |- _ => rewrite H
           | H: ?x ∈ fv (substitute ?t ?l) |- _ =>
             poseNew (Mark (x,t,l) "fv subst");
             pose proof (in_subset _ _ x (fv_subst2 t l) H)
           | _ => step || t_listutils
           | _ => progress (rewrite <- empty_list_rewrite in *)
           | _ => progress (unfold subset in *)
           end;
           eauto 2 with bfv;
           eauto using closed_mapping_fv with falsity;
           eauto using closed_mapping_fv2 with falsity.                            
Qed.
                            
Hint Resolve fv_nils2: bfv.

Ltac t_fv_open :=
  match goal with
  | H: _ |- _ => apply fv_open2 in H
  end.