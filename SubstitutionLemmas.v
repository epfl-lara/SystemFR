Require Import Coq.Lists.List.
Require Import Coq.Arith.PeanoNat.

Require Import Termination.Syntax.
Require Import Termination.ListUtils.
Require Import Termination.AssocList.
Require Import Termination.Tactics.
Require Import Termination.Sets.
Require Import Termination.SmallStep.
Require Import Termination.WFLemmas.
Require Import Termination.FVLemmas.

Lemma substitute_nothing:
  forall t l,
    (forall x, x ∈ fv t -> x ∈ support l -> False) ->
    substitute t l = t.
Proof.
  induction t;
    repeat match goal with
           | _ => progress (
                   step ||
                   t_listutils ||
                   (rewrite in_app_iff in *) ||
                   unfold fv in * ||
                   tequality ||
                   apply_any
                  )
           | x: nat, H: _ |- _ => apply H with x
           end; eauto with falsity.
Qed.

Lemma substitute_nothing2:
  forall t x e l,
    ~(x ∈ fv t) ->
    substitute t ((x,e) :: l) = substitute t l.
Proof.
  induction t;
    repeat step || unfold fv in * || (rewrite in_app_iff in *) || tequality || apply_any.
Qed.
                    
Lemma substitute_nothing3:
  forall t, substitute t nil = t.
Proof.
  induction t; steps.
Qed.

Hint Rewrite substitute_nothing3: bsubst.

Lemma substitute_nothing_context:
  forall gamma, substitute_context gamma nil = gamma.
Proof.
  induction gamma; repeat step || autorewrite with bsubst in *.
Qed.

Hint Rewrite substitute_nothing_context: bsubst.

Lemma substitute_nothing4:
  forall t l,
    (forall x, x ∈ fv t -> False) ->
    substitute t l = t.
Proof.
  intros; apply substitute_nothing; eauto.
Qed.

Lemma substitute_nothing5:
  forall t l,
    fv t = nil ->
    substitute t l = t.
Proof.
  intros; apply substitute_nothing; repeat step || t_listutils.
Qed.

Lemma substitute_cons:
  forall t x l rep,
    fv rep = nil ->
    substitute t ((x,rep) :: l) = substitute (substitute t ((x,rep) :: nil)) l.
Proof.
  induction t;
    repeat match goal with
           | H: _ = nil |- _ => rewrite H in *
           | _ => step || tequality || rewrite substitute_nothing4
           end; eauto.
Qed.

Lemma substitute_cons2:
  forall t x l rep,
    (forall z, z ∈ fv rep -> z ∈ support l -> False) ->
    substitute t ((x,rep) :: l) = substitute (substitute t ((x,rep) :: nil)) l.
Proof.
  induction t;
    repeat match goal with
           | H: _ = nil |- _ => rewrite H in *
           | _ => step || tequality || rewrite substitute_nothing
           end; eauto.
Qed.
                                          
Lemma substitute_cons3:
  forall t x l rep,
    substitute t ((x, substitute rep l) :: l) =
    substitute (substitute t ((x,rep) :: nil)) l.
Proof.
  induction t; steps.
Qed.

Lemma substitute_append:
  forall l1 l2 t,
    NoDup (l1 ++ l2) ->
    closed_mapping l1 ->
    substitute t (l1 ++ l2) = substitute (substitute t l1) l2.
Proof.
  induction l1;
    repeat match goal with
           | |- context[substitute ?t ((?x,?rep) :: ?l)] =>
             noUnify l (@nil (nat * term)); rewrite (substitute_cons t x l rep)
           | _ => step || step_inversion NoDup || autorewrite with bsubst
           end.
Qed.  

Lemma substitute_cons_context:
  forall gamma x l rep,
    fv rep = nil ->
    substitute_context gamma ((x,rep) :: l) =
      substitute_context (substitute_context gamma ((x,rep) :: nil)) l.
Proof.
  induction gamma; repeat step.
  f_equal; repeat step || rewrite substitute_cons; eauto.
Qed.

Lemma substitute_open:
  forall t, forall k rep l, 
     wfs l k ->
     substitute (open k t rep) l =
     open k (substitute t l) (substitute rep l).
Proof.
  induction t;
    repeat match goal with
           | |- ?t = open ?k ?t ?rep => symmetry; apply open_none
           | _ => step || tequality
           end; eauto with bwf.
Qed.

Hint Resolve substitute_open: bsubst.

Lemma substitute_open2:
  forall t, forall k rep l,
      wfs l k ->
      (forall x, x ∈ fv rep -> x ∈ support l -> False) ->
      open k (substitute t l) rep = substitute (open k t rep) l.
Proof.        
  intros; rewrite <- (substitute_nothing rep l) at 1; steps; eauto.
  symmetry; apply substitute_open; steps.
Qed.

Hint Resolve substitute_open2: bsubst.    

Lemma substitute_open3:
  forall t k x rep l,
    wfs l k ->
    wf rep k ->
    (x ∈ fv t -> False) ->
    substitute (open k t (fvar x)) ((x, rep) :: l) =
    open k (substitute t l) rep.
Proof.
  intros.
  rewrite substitute_open; steps.
  rewrite substitute_nothing2; steps.
Qed.

Hint Rewrite substitute_open3: bsubst.    

Lemma same_support_substitute:
  forall gamma l,
    support (substitute_context gamma l) = support gamma.
Proof.
  induction gamma; steps.
Qed.

Hint Rewrite same_support_substitute: bsubst.
  
Lemma lookup_subst:
  forall gamma x T l,
    lookup Nat.eq_dec gamma x = Some T ->
    lookup Nat.eq_dec (substitute_context gamma l) x = Some (substitute T l).
Proof.
  induction gamma; steps.
Qed.  

Hint Resolve lookup_subst: bsubst.

Lemma lookup_subst2:
  forall gamma x l,
    lookup Nat.eq_dec gamma x = None ->
    lookup Nat.eq_dec (substitute_context gamma l) x = None.
Proof.
  induction gamma; steps.
Qed.  

Hint Immediate lookup_subst2: bsubst.

Definition equivalent_subst (l1 l2: list (nat * term)): Prop :=
  forall s t,
    lookup Nat.eq_dec l1 s = Some t <->
    lookup Nat.eq_dec l2 s = Some t.

Lemma subst_permutation:
  forall t l1 l2, equivalent_subst l1 l2 -> substitute t l1 = substitute t l2.
Proof.
  unfold equivalent_subst; induction t;
    repeat match goal with
           | _ => step || tequality
           | H: forall x, _ |- _ => rewrite H in *
           | H: forall x, _ |- _ => rewrite <- H in * (* careful with non-termination :) *)
           end.
Qed.

Definition weak_equivalent_subst (vars: list nat) (l1 l2: list (nat * term)): Prop :=
  forall s t,
    s ∈ vars -> (
      lookup Nat.eq_dec l1 s = Some t <->
      lookup Nat.eq_dec l2 s = Some t
    ).

Lemma weak_subst_permutation:
  forall t l1 l2, weak_equivalent_subst (fv t) l1 l2 -> substitute t l1 = substitute t l2.
Proof.
  unfold weak_equivalent_subst, fv; induction t;
    repeat match goal with
           | _ => step || tequality || t_listutils
           | _ => solve [ rewrite_any; steps ]
           | _ => solve [ rewrite_back_any; steps ]
           | _ => solve [
                   apply_any; repeat step || t_listutils;
                   apply_any; repeat step || t_listutils;
                    eauto with step_tactic blistutils
                 ]
           end.
Qed.
    
Lemma substitute_skip:
  forall l1 l2 t x e,
    ~(x ∈ fv t) ->
    substitute t (l1 ++ (x,e) :: l2) = substitute t (l1 ++ l2).
Proof.
  intros.
  apply weak_subst_permutation.
  unfold weak_equivalent_subst; steps.
  - erewrite lookup_remove2 in H1; steps; eauto.
  - erewrite lookup_remove2; steps; eauto.
Qed.

Lemma obvious_equivalence:
  forall l1 x e l2,
    ~(x ∈ support l1) ->
    equivalent_subst
      ((x, e) :: l1 ++ l2)
      (l1 ++ (x,e) :: l2).
Proof.
  unfold equivalent_subst; induction l1;
    repeat match goal with
           | _ => progress (step || autorewrite with blookup in *)
           | H: _ |- _ => apply H
           end; eauto with blookup.
Qed.
                            
Lemma obvious_equivalence2:
  forall l1 x e l2,
    ~(x ∈ support l1) ->
    equivalent_subst
      (l1 ++ (x,e) :: l2)
      ((x, e) :: l1 ++ l2).
Proof.
  unfold equivalent_subst; induction l1;
    repeat match goal with
           | _ => progress (step || autorewrite with blookup in *)
           | H: _ |- _ => apply H
           end; eauto with blookup.
Qed.

Opaque lookup.

Lemma equivalent_append:
  forall l1 l2 l,
    (forall z, z ∈ support l1 <-> z ∈ support l2) ->
    equivalent_subst l1 l2 ->
    equivalent_subst (l1 ++ l) (l2 ++ l).
Proof.
  unfold equivalent_subst;
    repeat step || t_lookup || t_lookupor || t_listutils;  
    auto using lookupWeaken with bcongruence bapply_any;  
    auto 6 using lookupRight2, lookupNoneSupport with bapply_any step_tactic.
Qed.
