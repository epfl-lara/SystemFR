Require Import Coq.Lists.List.
Require Import Coq.Arith.PeanoNat.

Require Export SystemFR.Syntax.
Require Export SystemFR.ListUtils.
Require Export SystemFR.AssocList.
Require Export SystemFR.Tactics.

Require Export SystemFR.SmallStep.
Require Export SystemFR.WFLemmas.
Require Export SystemFR.TWFLemmas.


Lemma substitute_nothing:
  forall t l tag,
    (forall x, x ∈ pfv t tag -> x ∈ support l -> False) ->
    psubstitute t l tag = t.
Proof.
  induction t;
    repeat match goal with
           | _ => progress (
                   step ||
                   t_listutils ||
                   (rewrite in_app_iff in *) ||
                   unfold fv in * ||
                   t_equality ||
                   apply_any
                  )
           | x: nat, H: _ |- _ => apply H with x
           end; eauto with exfalso blookup.
Qed.

Lemma substitute_nothing2:
  forall t x e l tag,
    ~(x ∈ pfv t tag) ->
    psubstitute t ((x,e) :: l) tag = psubstitute t l tag.
Proof.
  induction t;
    repeat step || (rewrite in_app_iff in *) || t_equality || apply_any.
Qed.

Lemma substitute_nothing3:
  forall t tag, psubstitute t nil tag = t.
Proof.
  induction t; steps.
Qed.

Hint Rewrite substitute_nothing3: bsubst.

Lemma substitute_nothing_context:
  forall gamma tag, psubstitute_context gamma nil tag = gamma.
Proof.
  induction gamma; repeat step || autorewrite with bsubst in *.
Qed.

Hint Rewrite substitute_nothing_context: bsubst.

Lemma substitute_nothing4:
  forall t l tag,
    (forall x, x ∈ pfv t tag -> False) ->
    psubstitute t l tag = t.
Proof.
  intros; apply substitute_nothing; eauto.
Qed.

Lemma substitute_nothing5:
  forall t l tag,
    pfv t tag = nil ->
    psubstitute t l tag = t.
Proof.
  intros; apply substitute_nothing; repeat step || t_listutils.
Qed.

Lemma substitute_cons:
  forall t x l rep tag,
    pfv rep tag = nil ->
    psubstitute t ((x,rep) :: l) tag =
    psubstitute (psubstitute t ((x,rep) :: nil) tag) l tag.
Proof.
  induction t;
    repeat match goal with
           | H: _ = nil |- _ => rewrite H in *
           | _ => step || t_equality || rewrite substitute_nothing4
           end; eauto.
Qed.

Lemma substitute_cons2:
  forall t x l rep tag,
    (forall z, z ∈ pfv rep tag -> z ∈ support l -> False) ->
    psubstitute t ((x,rep) :: l) tag =
    psubstitute (psubstitute t ((x,rep) :: nil) tag) l tag.
Proof.
  induction t;
    repeat match goal with
           | H: _ = nil |- _ => rewrite H in *
           | _ => step || t_equality || rewrite substitute_nothing
           end; eauto.
Qed.

Lemma substitute_cons3:
  forall t x l rep tag,
    psubstitute t ((x, psubstitute rep l tag) :: l) tag =
    psubstitute (psubstitute t ((x,rep) :: nil) tag) l tag.
Proof.
  induction t; steps.
Qed.

Lemma substitute_append:
  forall l1 l2 t tag,
    pclosed_mapping l1 tag ->
    psubstitute t (l1 ++ l2) tag = psubstitute (psubstitute t l1 tag) l2 tag.
Proof.
  induction l1;
    repeat match goal with
           | |- context[psubstitute ?t ((?x,?rep) :: ?l) ?tag] =>
             noUnify l (@nil (nat * tree)); rewrite (substitute_cons t x l rep tag)
           | _ => step || step_inversion NoDup || autorewrite with bsubst
           end.
Qed.

Lemma substitute_cons_context:
  forall gamma x l rep tag,
    pfv rep tag = nil ->
    psubstitute_context gamma ((x,rep) :: l) tag =
      psubstitute_context (psubstitute_context gamma ((x,rep) :: nil) tag) l tag.
Proof.
  induction gamma;
    repeat match goal with
           | _ => step
           | |- _ :: _ = _ :: _ => f_equal
           | |- (_, _) = (_, _) => f_equal
           | _ => rewrite substitute_cons by eauto
           end.
Qed.

Lemma substitute_open:
  forall t, forall k rep l tag,
     wfs l k ->
     psubstitute (open k t rep) l tag =
     open k (psubstitute t l tag) (psubstitute rep l tag).
Proof.
  induction t;
    repeat match goal with
           | |- ?t = open ?k ?t ?rep => symmetry; apply open_none
           | _ => step || t_equality
           end; eauto with wf.
Qed.

Hint Resolve substitute_open: bsubst.

Lemma substitute_topen:
  forall t, forall k rep l tag,
     twfs l k ->
     psubstitute (topen k t rep) l tag =
     topen k (psubstitute t l tag) (psubstitute rep l tag).
Proof.
  induction t;
    repeat match goal with
           | |- ?t = topen ?k ?t ?rep => symmetry; apply topen_none
           | _ => step || t_equality
           end; eauto with btwf.
Qed.

Lemma substitute_open2:
  forall t, forall k rep l tag,
      wfs l k ->
      (forall x, x ∈ pfv rep tag -> x ∈ support l -> False) ->
      open k (psubstitute t l tag) rep = psubstitute (open k t rep) l tag.
Proof.
  intros; rewrite <- (substitute_nothing rep l) at 1; steps; eauto.
  symmetry; apply substitute_open; steps.
Qed.

Hint Resolve substitute_open2: bsubst.

Lemma substitute_topen2:
  forall t, forall k rep l tag,
      twfs l k ->
      (forall x, x ∈ pfv rep tag -> x ∈ support l -> False) ->
      topen k (psubstitute t l tag) rep = psubstitute (topen k t rep) l tag.
Proof.
  intros; rewrite <- (substitute_nothing rep l) at 1; steps; eauto.
  symmetry; apply substitute_topen; steps.
Qed.

Lemma substitute_open3:
  forall t k x rep l tag,
    wfs l k ->
    wf rep k ->
    (x ∈ pfv t tag -> False) ->
    psubstitute (open k t (fvar x tag)) ((x, rep) :: l) tag =
    open k (psubstitute t l tag) rep.
Proof.
  intros.
  rewrite substitute_open; steps.
  rewrite substitute_nothing2; steps.
Qed.

Hint Resolve substitute_open3: bsubst.

Lemma substitute_topen3:
  forall t k x rep l tag,
    twfs l k ->
    twf rep k ->
    (x ∈ pfv t tag -> False) ->
    psubstitute (topen k t (fvar x tag)) ((x, rep) :: l) tag =
    topen k (psubstitute t l tag) rep.
Proof.
  intros.
  rewrite substitute_topen; steps.
  rewrite substitute_nothing2; steps.
Qed.

Lemma same_support_substitute:
  forall gamma l tag,
    support (psubstitute_context gamma l tag) = support gamma.
Proof.
  induction gamma; steps.
Qed.

Hint Rewrite same_support_substitute: bsubst.

Lemma lookup_subst:
  forall gamma x T l tag,
    lookup Nat.eq_dec gamma x = Some T ->
      lookup Nat.eq_dec (psubstitute_context gamma l tag) x =
      Some (psubstitute T l tag).
Proof.
  induction gamma; steps.
Qed.

Hint Resolve lookup_subst: bsubst.

Lemma lookup_subst2:
  forall gamma x l tag,
    lookup Nat.eq_dec gamma x = None ->
    lookup Nat.eq_dec (psubstitute_context gamma l tag) x = None.
Proof.
  induction gamma; steps.
Qed.

Hint Immediate lookup_subst2: bsubst.

Definition equivalent_subst (l1 l2: list (nat * tree)): Prop :=
  forall s t,
    lookup Nat.eq_dec l1 s = Some t <->
    lookup Nat.eq_dec l2 s = Some t.

Lemma subst_permutation:
  forall t l1 l2 tag,
    equivalent_subst l1 l2 ->
    psubstitute t l1 tag = psubstitute t l2 tag.
Proof.
  unfold equivalent_subst; induction t;
    repeat match goal with
           | _ => step || t_equality
           | H: forall x, _ |- _ => rewrite H in *
           | H: forall x, _ |- _ => rewrite <- H in * (* careful with non-termination :) *)
           end.
Qed.

Lemma NoDup_cons:
  forall l (x : nat) (rep : tree),
    NoDup l ->
    ~(x ∈ l) ->
    NoDup (l ++ x :: nil).
Proof.
  induction l; repeat step || t_listutils || step_inversion NoDup.
Qed.

Lemma substitute_cons4:
  forall l t x rep tag,
    ~(x ∈ support l) ->
    pclosed_mapping l tag ->
    psubstitute t ((x,rep) :: l) tag =
    psubstitute (psubstitute t l tag) ((x,rep) :: nil) tag.
Proof.
  intros.
  rewrite (subst_permutation _ _ (l ++ ((x,rep) :: nil)));
    repeat step || unfold equivalent_subst || t_lookup ||
           (progress rewrite obvious_lookup in * by steps) ||
           (rewrite substitute_append by steps) ||
           t_lookupor;
    eauto with blookup.
Qed.

Definition weak_equivalent_subst { T } (vars: list nat) (l1 l2: list (nat * T)): Prop :=
  forall s t,
    s ∈ vars -> (
      lookup Nat.eq_dec l1 s = Some t <->
      lookup Nat.eq_dec l2 s = Some t
    ).

Lemma weaker_equivalent_subst:
  forall {T} vars vars' (l1 l2: list (nat * T)),
    (forall x, x ∈ vars' -> x ∈ vars) ->
    weak_equivalent_subst vars l1 l2 ->
    weak_equivalent_subst vars' l1 l2.
Proof.
  unfold weak_equivalent_subst; repeat step || apply_any.
Qed.

Lemma weaker_equivalent_subst2:
  forall {T} vars vars' (l1 l2: list (nat * T)) y t,
    (forall x, x ∈ vars' -> x ∈ vars \/ x = y) ->
    weak_equivalent_subst vars l1 l2 ->
    weak_equivalent_subst vars' ((y,t) :: l1) ((y,t) :: l2).
Proof.
  unfold weak_equivalent_subst; repeat step || instantiate_any || apply_any.
Qed.

Lemma weak_equivalent_subst_sym:
  forall T vars (l1 l2: list (nat * T)),
    weak_equivalent_subst vars l1 l2 ->
    weak_equivalent_subst vars l2 l1.
Proof.
  unfold weak_equivalent_subst; repeat step || apply_any.
Qed.

Lemma weak_subst_permutation:
  forall t l1 l2 tag,
    weak_equivalent_subst (pfv t tag) l1 l2 ->
    psubstitute t l1 tag = psubstitute t l2 tag.
Proof.
  unfold weak_equivalent_subst; induction t;
    repeat match goal with
           | _ => step || t_equality || t_listutils
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
  forall l1 l2 t x e tag,
    ~(x ∈ pfv t tag) ->
    psubstitute t (l1 ++ (x,e) :: l2) tag = psubstitute t (l1 ++ l2) tag.
Proof.
  intros.
  apply weak_subst_permutation.
  unfold weak_equivalent_subst; steps.
  - erewrite lookup_remove2 in H1; steps; eauto.
  - erewrite lookup_remove2; steps; eauto.
Qed.

Lemma substitute_skip_one:
  forall l t x1 x2 e1 e2 tag,
    ~(x2 ∈ pfv t tag) ->
    psubstitute t ((x1, e1) :: (x2, e2) :: l) tag = psubstitute t ((x1,e1) :: l) tag.
Proof.
  intros.
  rewrite cons_app.
  rewrite substitute_skip; steps.
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
    auto using lookupWeaken with bcongruence apply_any;
    auto 6 using lookupRight2, lookupNoneSupport with apply_any step_tactic.
Qed.
