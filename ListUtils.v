Require Import Psatz.

Require Import Coq.Lists.List.
Require Import Coq.Strings.String.

Require Import Coq.Arith.PeanoNat.

Require Export SystemFR.Tactics.

Notation "A - n" := (List.remove PeanoNat.Nat.eq_dec n A).
Notation "A ++ B" := (List.app A B).
Notation "x ∈ A" := (In x A) (at level 70).

Definition empty {T}: list T := nil.

Definition add {T} (s: list T) (t: T) := t :: s.

Definition singleton {T} (t: T): list T := add nil t.

Fixpoint diff {A} (dec: forall a b: A, { a = b } + { a <> b }) (l1 l2: list A): list A :=
  match l2 with
  | nil => l1
  | x :: xs => diff dec (remove dec x l1) xs
  end.

Notation "A -- B" := (diff PeanoNat.Nat.eq_dec A B) (at level 50).

Lemma add_mem: forall {T} (s: list T) x, x ∈ (add s x).
  steps.
Qed.

Hint Resolve add_mem: sets.

Lemma add_more: forall {T} (s: list T) x y,
    x ∈ s ->
    x ∈ add s y.
Proof.
  steps.
Qed.

Hint Resolve add_more: sets.

Definition subset {T} (l1 l2: list T) :=
  forall x, x ∈ l1 -> x ∈ l2.

Definition equal_set {T} (l1 l2: list T) :=
  forall x, x ∈ l1 <-> x ∈ l2.

Lemma not_in_append: forall {T} l1 l2 (x: T),
    ~(x ∈ l1 ++ l2) ->
    (~(x ∈ l1) /\ ~(x ∈ l2)).
Proof.
  steps; eauto with *.
Qed.

Lemma in_remove:
  forall S x y,
   x ∈ S - y <-> x ∈ S /\ x <> y.
Proof.
  induction S; repeat step || rewrite IHS in *.
Qed.

Hint Rewrite in_remove: list_utils.

Lemma in_diff:
  forall S2 x S1,
   x ∈ S1 -- S2 <-> x ∈ S1 /\ ~(x ∈ S2).
Proof.
  induction S2; repeat step || rewrite IHS2 in * || autorewrite with list_utils in *.
Qed.

Hint Rewrite in_diff: list_utils.

Lemma app_eq_nil_iff:
  forall A (l l': list A),
    l ++ l' = nil <-> (l = nil /\ l' = nil).
Proof.
  destruct l; steps.
Qed.

Hint Rewrite List.app_nil_r: list_utils.

Ltac list_utils :=
  match goal with
  | H: _ = nil |- _ => rewrite H in *
  | H: nil = _ ++ _ :: _ |- _ => apply False_ind; apply (app_cons_not_nil _ _ _ H)
  | H: context[_ ∈ _ ++ _] |- _  => rewrite in_app_iff in H
  | |- context[_ ∈ _ ++ _] => rewrite in_app_iff
  | H: forall n, n ∈ (?s1 ++ ?s2) -> _, 
    H': ?n ∈ ?s1 |- _ => unshelve epose proof H n _; repeat light || rewrite in_app_iff
  | H: forall n, n ∈ (?s1 ++ ?s2) -> _, 
    H': ?n ∈ ?s2 |- _ => unshelve epose proof H n _; repeat light || rewrite in_app_iff
  | H: ?x ∈ ?l |- context[map ?f ?l] =>
    poseNew (Mark (f,l,x) "in_map");
    poseNew (in_map _ _ f l x)
  | H: ?y ∈ map ?f ?l |- _ =>
    poseNew (Mark (y,f,l) "in_map_iff");
    poseNew (proj1 (in_map_iff f l y) H)
  | H:  (?x ∈ ?l1 ++ ?l2) -> False |- _ =>
    poseNew (Mark (l1,l2,x) "not_in_append");
    poseNew (not_in_append l1 l2 x H)
  | |- context[?l1 ++ ?l2 = nil]  => rewrite (app_eq_nil_iff _ l1 l2)
  | H: context[?l1 ++ ?l2 = nil] |- _  => rewrite (app_eq_nil_iff _ l1 l2) in H
  | _ => progress (autorewrite with list_utils in *)
  end.

Lemma empty_list:
  forall A (l: list A),
    (forall x, x ∈ l -> False) ->
    l = nil.
Proof.
  destruct l; steps; eauto with exfalso.
Qed.

Hint Resolve empty_list: list_utils.

Hint Extern 50 => list_utils: list_utils.

Lemma empty_list_rewrite:
  forall A (l: list A),
    (forall x, x ∈ l -> False) <->
    l = nil.
Proof.
  destruct l; steps; eauto with exfalso.
Qed.

Lemma empty_list2:
  forall A (l: list A) x,
    l = nil ->
    x ∈ l ->
    False.
Proof.
  steps.
Qed.

Lemma NoDup_append:
  forall A (l1 l2: list A) x,
    NoDup (l1 ++ l2) ->
    x ∈ l1 ->
    x ∈ l2 ->
    False.
Proof.
  induction l1; repeat step || step_inversion NoDup || list_utils; eauto.
Qed.

Lemma cons_append:
  forall A (l1 l2: list A) x,
    l1 ++ x :: l2 = (l1 ++ (x :: nil)) ++ l2.
Proof.
  repeat step || rewrite <- List.app_assoc.
Qed.

Lemma cons_app:
  forall X (x: X) (xs: list X),
    x :: xs = (x :: nil) ++ xs.
Proof.
  steps.
Qed.

Lemma NoDup_false:
  forall T (x: T) l,
    NoDup (x :: x :: l) ->
    False.
Proof.
  repeat step || step_inversion NoDup.
Qed.

Lemma NoDup_false2:
  forall T (x y: T) l,
    NoDup (x :: y :: x :: l) ->
    False.
Proof.
  repeat step || step_inversion NoDup.
Qed.

Lemma NoDup_false3:
  forall T (x y: T) l,
    NoDup (y :: x :: x :: l) ->
    False.
Proof.
  repeat step || step_inversion NoDup.
Qed.

Ltac nodup :=
  apply_anywhere NoDup_false ||
  apply_anywhere NoDup_false2 ||
  apply_anywhere NoDup_false3.
