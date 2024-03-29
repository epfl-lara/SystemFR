Require Import Coq.Strings.String.
Require Import Coq.Lists.List.

Require Export SystemFR.ListSetLemmas.

Require Import PeanoNat.

Close Scope string_scope.

Definition map X Y := list (X * Y).
Definition decidable X := forall (x1 x2: X), { x1 = x2 } + { x1 <> x2 }.

Fixpoint support {X Y} (m: map X Y): list X :=
  match m with
  | nil => nil
  | (x,_) :: m' => x :: support m'
  end.

Fixpoint range {X Y} (m: map X Y): list Y :=
  match m with
  | nil => nil
  | (_, y) :: m' => y :: range m'
  end.

Fixpoint lookup {X Y} (eq_dec: decidable X) (m: map X Y) (x: X): option Y :=
  match m with
  | nil => None
  | (a,b) :: m' =>
    if (eq_dec a x)
    then Some b
    else lookup eq_dec m' x
  end.

Fixpoint lookupRest {X Y} (eq_dec: decidable X) (m: map X Y) x: option (Y * map X Y) :=
  match m with
  | nil => None
  | (y,tau) :: m' =>
    if (eq_dec x y)
    then Some ((tau,m'))
    else lookupRest eq_dec m' x
  end.

Lemma lookupRestSuffix:
  forall X Y eq_dec (m: map X Y) x (y: Y) suffix,
    lookupRest eq_dec m x = Some (y,suffix) ->
    exists m', m = (m' ++ suffix).
Proof.
  induction m; repeat step.
  - exists ((x0,y) :: nil); repeat step.
  - pose proof (IHm _ _ _ H); steps.
    exists ((x0,y0) :: m'); steps.
Qed.

#[export]
Hint Immediate lookupRestSuffix: blookup.

Lemma lookupRestLookup:
  forall X Y eq_dec (m: map X Y) x y suffix,
    lookupRest eq_dec m x = Some (y,suffix) ->
    lookup eq_dec m x = Some y.
Proof.
  induction m; repeat step; eauto.
Qed.

#[export]
Hint Immediate lookupRestLookup: blookup.

Lemma lookupLookupRest:
  forall X Y eq_dec (m: map X Y) x y,
    lookup eq_dec m x = Some y ->
    exists suffix,
      lookupRest eq_dec m x = Some (y,suffix).
Proof.
  induction m; repeat step; eauto.
Qed.


(* fresh s Γ holds if variable x does not appear in the context Γ *)
Definition fresh { X Y } (m: map X Y) x := ~(x ∈ support m).
#[export]
Hint Unfold fresh: core.

Lemma lookupSupport:
  forall X Y eq_dec (m: map X Y) (x: X) (y: Y),
    lookup eq_dec m x = Some y -> x ∈ support m.
Proof.
  induction m; steps; eauto.
Qed.

Lemma support_append:
  forall X Y (m1 m2: map X Y),
    support (m1 ++ m2) = support m1 ++ support m2.
Proof.
  induction m1; steps.
Qed.

#[export] Hint Rewrite support_append: list_utils.

Fixpoint map_values {X Y Z} (f: Y -> Z) (l: map X Y) :=
  match l with
  | nil => nil
  | (x,T) :: l' => (x, f T) :: map_values f l'
  end.

Lemma lookupNoneSupport: forall X Y eq_dec (m: map X Y) x,
  ~(x ∈ support m) ->
  lookup eq_dec m x = None.
Proof.
  induction m; repeat step.
Qed.

#[export]
Hint Immediate lookupNoneSupport: blookup.

Lemma lookupNoneSupport2:
  forall X Y eq_dec (m: map X Y) x,
    lookup eq_dec m x = None ->
    x ∈ support m ->
    False.
Proof.
  induction m; repeat step; eauto.
Qed.

#[export]
Hint Immediate lookupNoneSupport2: blookup.

Lemma lookupSomeSupport:
  forall X Y eq_dec (m: map X Y) x A,
    lookup eq_dec m x = Some A ->
    x ∈ support m.
Proof.
  induction m; repeat step || unfold fv_context in * || sets; eauto.
Qed.

#[export]
Hint Immediate lookupSomeSupport: blookup.

Lemma lookupRange:
  forall X Y eq_dec (m: map X Y) x y,
    lookup eq_dec m x = Some y ->
    y ∈ range m.
Proof.
  induction m; steps; eauto.
Qed.

Lemma lookupNoneAppend1:
  forall X Y eq_dec (l1 l2: map X Y) x,
    lookup eq_dec (l1 ++ l2) x = None ->
    lookup eq_dec l1 x = None.
Proof.
  induction l1; steps; eauto.
Qed.

Lemma lookupNoneAppend2:
  forall X Y eq_dec (l1 l2: map X Y) x,
    lookup eq_dec (l1 ++ l2) x = None ->
    lookup eq_dec l2 x = None.
Proof.
  induction l1; steps.
Qed.

Lemma lookupAppendNoDup:
  forall X Y eq_dec (l1 l2: map X Y) x,
    x ∈ support l2 ->
    ~(x ∈ support l1) ->
    lookup eq_dec l2 x = lookup eq_dec (l1 ++ l2)%list x.
Proof.
  induction l1; repeat step || sets || unfold fv_context in *.
Qed.

#[export]
Hint Resolve lookupAppendNoDup: blookup.

Lemma lookupAppendOr:
  forall X Y eq_dec (l1 l2: map X Y) x,
    lookup eq_dec (l1 ++ l2) x = lookup eq_dec l1 x \/
    (
      lookup eq_dec l1 x = None /\
      lookup eq_dec (l1 ++ l2) x = lookup eq_dec l2 x
    ).
Proof.
  induction l1; steps.
Qed.

Lemma lookupWeaken:
  forall X Y eq_dec (l1 l2: map X Y) x t,
    lookup eq_dec l1 x = Some t ->
    lookup eq_dec (l1 ++ l2) x = Some t.
Proof.
  induction l1; steps.
Qed.

#[export]
Hint Resolve lookupWeaken: blookup.

Lemma lookupAppendNone:
  forall X Y eq_dec (l1 l2: map X Y) x,
    lookup eq_dec l1 x = None ->
    lookup eq_dec l2 x = None ->
    lookup eq_dec (l1 ++ l2) x = None.
Proof.
  induction l1; steps.
Qed.

#[export]
Hint Resolve lookupAppendNone: blookup.

Lemma lookupRight:
  forall X Y eq_dec (l1 l2: map X Y) x,
    lookup eq_dec l1 x = None ->
    lookup eq_dec (l1 ++ l2) x = lookup eq_dec l2 x.
Proof.
  induction l1; steps.
Qed.

#[export]
Hint Resolve lookupRight: blookup.

Lemma lookupRight2:
  forall X Y eq_dec (l1 l2: map X Y) x r,
    lookup eq_dec l1 x = None ->
    lookup eq_dec l2 x = r ->
    lookup eq_dec (l1 ++ l2) x = r.
Proof.
  induction l1; steps.
Qed.

Lemma lookupNil: forall X Y eq_dec (m: map X Y) x,
  @lookup X Y eq_dec nil x = None.
Proof.
  steps.
Qed.

#[export] Hint Rewrite lookupNil: blookup.

Lemma lookupMap:
  forall X Y Z
         (eq_dec: forall x1 x2: X, { x1 = x2 } + { x1 <> x2 })
         (m: map X Y) (f: Y -> Z) x,
    lookup eq_dec (map_values f m) x = option_map f (lookup eq_dec m x).
Proof.
  induction m; steps.
Qed.

Ltac t_lookup :=
  match goal with
  | H: lookup ?e ?g ?x = Some ?t |- _ =>
    poseNew (Mark (g,x,t) "lookupSomeSupport");
    poseNew (lookupSomeSupport _ _ e _ _ _ H)
  | H: lookup ?e ?g ?x = Some ?t |- _ =>
    poseNew (Mark (g,x,t) "lookupRange");
    poseNew (lookupRange _ _ e _ _ _ H)
  | H: lookup ?e ?g ?x = None |- _ =>
    poseNew (Mark (g,x) "lookupNoneSupport2");
    poseNew (lookupNoneSupport2 _ _ e _ _ H)
  | H: lookup ?e (?l1 ++ ?l2)%list ?x = None |- _ =>
    poseNew (Mark (l1,l2,x) "lookupNoneAppend1");
    poseNew (lookupNoneAppend1 _ _ e _ _ H)
  | H: lookup ?e (?l1 ++ ?l2)%list ?x = None |- _ =>
    poseNew (Mark (l1,l2,x) "lookupNoneAppend2");
    poseNew (lookupNoneAppend2 _ _ e _ _ _ H)
  | H: context[lookup (map_values _ _) _] |- _ => rewrite lookupMap in H
  end.

Ltac t_lookupor :=
  match goal with
  | H: lookup ?e (?l1 ++ ?l2)%list ?x = Some ?t |- _ =>
    poseNew (Mark (l1,l2,x) "lookupAppendOr");
    poseNew (lookupAppendOr _ _ e l1 l2 x)
  end.

Lemma obvious_lookup:
  forall X Y Γ1 (x: X) (U: Y) Γ2 dec,
    ~(x ∈ support Γ1) ->
    lookup dec (Γ1 ++ (x,U) :: Γ2) x = Some U.
Proof.
  induction Γ1;
    repeat match goal with
           |  _ => step || step_inversion is_context || t_lookup
           end.
Qed.

#[export] Hint Rewrite obvious_lookup using assumption: blookup.

Lemma lookup_remove:
  forall {A B} Γ1 (x y: A) U Γ2 y (T: B) dec,
    lookup dec (Γ1 ++ (x, U) :: Γ2) y = Some T ->
    x <> y ->
    lookup dec (Γ1 ++ Γ2) y = Some T.
Proof.
  induction Γ1; steps; eauto.
Qed.

#[export]
Hint Immediate lookup_remove: blookup.

Lemma lookup_remove2:
  forall {A B} Γ1 (x y: A) U Γ2 y dec,
    x <> y ->
    @lookup A B dec (Γ1 ++ (x, U) :: Γ2) y = @lookup A B dec (Γ1 ++ Γ2) y.
Proof.
  induction Γ1; steps; eauto.
Qed.

Fixpoint remove_support (l: list (nat * nat)) x :=
  match l with
  | nil => nil
  | (a,b) :: ls =>
    if PeanoNat.Nat.eq_dec a x
    then remove_support ls x
    else (a,b) :: remove_support ls x
  end.

Lemma in_remove_support:
  forall l x, x ∈ support (remove_support l x) -> False.
Proof.
  induction l; steps; eauto.
Qed.

Lemma in_remove_support2:
  forall l x y, x ∈ support (remove_support l y) -> x ∈ support l.
Proof.
  induction l; steps; eauto.
Qed.

Lemma nodup_remove_support:
  forall l x, NoDup (support l) -> NoDup (support (remove_support l x)).
Proof.
  induction l; repeat step || step_inversion NoDup; eauto using in_remove_support2.
Qed.

Lemma in_remove_support_range:
  forall l x y, x ∈ range (remove_support l y) -> x ∈ range l.
Proof.
  induction l; steps; eauto.
Qed.

Lemma nodup_remove_support_range:
  forall l x, NoDup (range l) -> NoDup (range (remove_support l x)).
Proof.
  induction l; repeat step || step_inversion NoDup; eauto using in_remove_support_range.
Qed.

Fixpoint swap (l: list (nat * nat)) :=
  match l with
  | nil => nil
  | (x,y) :: l' => (y,x) :: swap l'
  end.

Lemma range_swap:
  forall l, range (swap l) = support l.
Proof.
  induction l; steps.
Qed.

Lemma swap_twice:
  forall l, swap (swap l) = l.
Proof.
  induction l; steps.
Qed.

Lemma lookup_same:
  forall X Y eq (l: list (X * Y)) x y1 y2,
    lookup eq l x = Some y1 ->
    lookup eq l x = Some y2 ->
    y1 = y2.
Proof.
  repeat step || rewrite_any.
Qed.

Ltac t_lookup_same :=
  match goal with
  | H1: lookup _ ?l ?x = Some ?y1,
    H2: lookup _ ?l ?x = Some ?y2 |- _ =>
      pose proof (lookup_same _ _ _ _ _ _ _ H1 H2); clear H2
  end.

Lemma lookupMap2:
  forall X Y Z
         (eq_dec: forall x1 x2: X, { x1 = x2 } + { x1 <> x2 })
         (m: map X Y) (f: Y -> Z) x z,
    lookup eq_dec (map_values f m) x = Some z ->
    exists y, lookup eq_dec m x = Some y /\ f y  = z.
Proof.
  induction m; steps; eauto.
Qed.

Ltac t_lookupMap2 :=
  match goal with
  | H: Some _ = lookup _ _ _ |- _ => apply eq_sym in H
  | H: lookup _ (map_values _ _) _ = Some _ |- _ =>
    poseNew (Mark H "lookupMap2");
    pose proof (lookupMap2 _ _ _ _ _ _ _ _ H)
  end.

Ltac t_lookup_rewrite :=
  match goal with
  | H: lookup _ (_ ++ _) _ = lookup _ _ _ |- _ => rewrite H in *
  end.

Lemma support_map_values:
  forall X Y Z (f: Y -> Z) (l: map X Y), support (map_values f l) = support l.
Proof.
  induction l; steps.
Qed.

Lemma lookup_combine_map:
  forall A B eq_dec (xs: list A) f l (t1 t2: B) x,
    lookup eq_dec (combine xs l) x = Some t1 ->
    lookup eq_dec (combine xs (List.map f l)) x = Some t2 ->
    t2 = f t1.
Proof.
  induction xs; repeat step; eauto.
Qed.

Lemma lookup_combine_some_none:
  forall A B eq_dec (xs: list A) (l1 l2: list B) t x,
    List.length l1 = List.length l2 ->
    lookup eq_dec (combine xs l1) x = Some t ->
    lookup eq_dec (combine xs l2) x = None ->
    False.
Proof.
  induction xs; steps; eauto.
Qed.

Lemma support_combine:
  forall A B (l1: list A) (l2: list B),
    length l1 = length l2 ->
    support (combine l1 l2) = l1.
Proof.
  induction l1; destruct l2; repeat step || apply f_equal.
Qed.

Lemma range_combine:
  forall A B (l1: list A) (l2: list B),
    length l1 = length l2 ->
    range (combine l1 l2) = l2.
Proof.
  induction l1; destruct l2; repeat step || apply f_equal.
Qed.

Lemma lookup_some_in:
  forall A (l: map nat A) x a,
    lookup Nat.eq_dec l x = Some a ->
    (x, a) ∈ l.
Proof.
  induction l; steps.
Qed.

Lemma in_map_in_support:
  forall A B (l: map A B) p,
    p ∈ l ->
    (fst p) ∈ support l.
Proof.
  induction l; steps.
Qed.

Lemma lookup_support:
  forall A (l: map nat A) x,
   x ∈ support l ->
   exists a, lookup Nat.eq_dec l x = Some a.
Proof.
  induction l; repeat step; eauto.
Qed.

Lemma lookup_support2:
  forall A (l1 l2: map nat A) x,
   (forall s t, lookup Nat.eq_dec l1 s = Some t <-> lookup Nat.eq_dec l2 s = Some t) ->
   x ∈ support l1 ->
   x ∈ support l2.
Proof.
  intros.
  apply_anywhere lookup_support; repeat step.
  pose proof (H x a); repeat step || t_lookup.
Qed.

Lemma range_append:
  forall A B (l1 l2: map A B),
    range (l1 ++ l2) = range l1 ++ range l2.
Proof.
  induction l1; repeat step.
Qed.

Lemma recombine:
  forall A B (m: map A B),
    combine (support m) (range m) = m.
Proof.
  induction m; steps.
Qed.

Lemma length_support:
  forall A B (l: map A B), length (support l) = length l.
Proof.
  induction l; steps.
Qed.

Lemma length_range:
  forall A B (l: map A B), length (range l) = length l.
Proof.
  induction l; steps.
Qed.

Lemma support_nil:
  forall A B (l: map A B), support l = nil <-> l = nil.
Proof.
  destruct l; steps.
Qed.

Ltac list_utils2 :=
  rewrite map_length in * || rewrite support_nil in * || rewrite in_map_iff in * ||
  rewrite range_append in * || rewrite range_combine in * ||
  rewrite List.map_map in * || rewrite support_combine in * ||
  rewrite length_support in * || rewrite length_range in * ||
  rewrite length_zero_iff_nil in * ||
  rewrite recombine in * ||
  Forall_inst.

Lemma find_snd:
  forall A B a (l1: list A) (l2: list B),
    a ∈ l1 ->
    length l1 = length l2 ->
    exists b, (a, b) ∈ combine l1 l2.
Proof.
  induction l1; repeat step || instantiate_any; eauto.
  pose proof (IHl1 _ H1 H); steps; eauto.
Qed.

Ltac find_snd :=
  match goal with
  | H1: context[combine ?l1 ?l2],
    H2: ?x ∈ ?l1 |- _ =>
    poseNew (Mark (l1, l2) "first_snd");
    unshelve epose proof (find_snd _ _ _ l1 l2 H2 _)
  end.

Lemma find_fst:
  forall A B b (l1: list A) (l2: list B),
    b ∈ l2 ->
    length l1 = length l2 ->
    exists a, (a, b) ∈ combine l1 l2.
Proof.
  induction l1; repeat step || instantiate_any; eauto.
  apply_anywhere eq_sym; list_utils2; steps.
Qed.

Ltac find_fst :=
  match goal with
  | H1: context[combine ?l1 ?l2],
    H2: ?x ∈ ?l2 |- _ =>
    poseNew (Mark (l1, l2) "first_fst");
    unshelve epose proof (find_fst _ _ _ l1 l2 H2 _)
  end.

Lemma combine_middle_point:
  forall A B C (l1: list A) (l2: list B) (l3: list C) a c,
    length l1 = length l2 ->
    length l2 = length l3 ->
    (a, c) ∈ combine l1 l3 ->
    exists b,
      (a, b) ∈ combine l1 l2 /\
      (b, c) ∈ combine l2 l3.
Proof.
  induction l1; destruct l2; destruct l3;
    repeat step; eauto.
  pose proof (IHl1 _ _ _ _ H H0 H2); steps; eauto.
Qed.
