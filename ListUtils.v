Require Import Termination.Tactics.
Require Import Termination.Sets.

Require Import Omega.

Require Import Coq.Lists.List.
Require Import Coq.Strings.String.

Lemma notInAppend: forall {T} l1 l2 (x: T),
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

Hint Rewrite in_remove: blistutils.

Lemma in_diff:
  forall S2 x S1,
   x ∈ S1 -- S2 <-> x ∈ S1 /\ ~(x ∈ S2).
Proof.
  induction S2; repeat step || rewrite IHS2 in * || autorewrite with blistutils in *.
Qed.

Hint Rewrite in_diff: blistutils.

Lemma app_eq_nil_iff:
  forall A (l l': list A),
    l ++ l' = nil <-> (l = nil /\ l' = nil).
Proof.
  destruct l; steps.
Qed.

Ltac t_listutils :=
  match goal with
  | H: _ = nil |- _ => rewrite H in *
  | H: nil = _ ++ _ :: _ |- _ => apply False_ind; apply (app_cons_not_nil _ _ _ H)
  | H: context[_ ∈ _ ++ _] |- _  => rewrite in_app_iff in H
  | |- context[_ ∈ _ ++ _] => rewrite in_app_iff
  | H: ?x ∈ ?l |- context[map ?f ?l] =>
    poseNew (Mark (f,l,x) "in_map");
    poseNew (in_map _ _ f l x)
  | H: ?y ∈ map ?f ?l |- _ =>
    poseNew (Mark (y,f,l) "in_map_iff");
    poseNew (proj1 (in_map_iff f l y) H)
  | H:  (?x ∈ ?l1 ++ ?l2) -> False |- _ =>
    poseNew (Mark (l1,l2,x) "notInAppend");
    poseNew (notInAppend l1 l2 x H)
  | |- context[?l1 ++ ?l2 = nil]  => rewrite (app_eq_nil_iff _ l1 l2)
  | H: context[?l1 ++ ?l2 = nil] |- _  => rewrite (app_eq_nil_iff _ l1 l2) in H
  | _ => progress (autorewrite with blistutils in *)
  end.

Lemma empty_list:
  forall A (l: list A),
    (forall x, x ∈ l -> False) ->
    l = nil.
Proof.
  destruct l; steps; eauto with falsity.
Qed.

Hint Resolve empty_list: blistutils.

Hint Extern 50 => t_listutils: blistutils.

Lemma empty_list_rewrite:
  forall A (l: list A),
    (forall x, x ∈ l -> False) <->
    l = nil.
Proof.
  destruct l; steps; eauto with falsity.
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
  induction l1; repeat step || step_inversion NoDup || t_listutils; eauto.
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
