Require Import Coq.Strings.String.
Require Import Coq.Lists.List.

Require Import Termination.ListUtils.
Require Import Termination.Tactics.
Require Import Termination.Sets.

Lemma in_subset:
  forall {T} (l1 l2: list T) (x: T),
    subset l1 l2 -> x ∈ l1 -> x ∈ l2.
Proof.
  steps.
Qed.

Hint Resolve in_subset: sets.

Lemma singleton_subset:
  forall {T} (l: list T) (x: T),
    subset (singleton x) l <->
    x ∈ l.
Proof.
  unfold subset; unfold singleton; steps.
Qed.

Hint Resolve singleton_subset: sets.

Lemma union_left:
  forall {T} (l1 l2 l: list T),
    subset l1 l ->
    subset l2 l ->
    subset (l1 ++ l2) l.
Proof.
  induction l1; unfold subset in *; steps; eauto.
Qed.

Lemma union_right1:
  forall {T} (l1 l2: list T),
    subset l1 (l1 ++ l2).
Proof.
  induction l1; unfold subset in *; steps.
Qed.

Lemma union_right2:
  forall {T} (l1 l2: list T),
    subset l2 (l1 ++ l2).
Proof.
  induction l1; unfold subset in *; steps.
Qed.

Hint Resolve union_left union_right1 union_right2: sets.

Lemma empty_is_subset:
  forall {T} (l: list T),
    subset empty l.
Proof.
  unfold subset; steps.
Qed.

Hint Immediate empty_is_subset: sets.

Lemma subset_transitive:
  forall {T} (l1 l2 l3: list T),
    subset l1 l2 ->
    subset l2 l3 ->
    subset l1 l3.
Proof.
  unfold subset; steps.
Qed.

Hint Immediate subset_transitive: sets.

Lemma subset_union:
  forall {T} (A1 A2 B1 B2: list T),
    subset A1 B1 ->
    subset A2 B2 ->
    subset (A1 ++ A2) (B1 ++ B2).
Proof.
  eauto with sets.
Qed.

Hint Immediate subset_union: sets.

Lemma subset_union2:
  forall {T} (A1 A2 B: list T),
    subset A1 B ->
    subset A2 B ->
    subset (A1 ++ A2) B.
Proof.
  eauto with sets.
Qed.


Hint Resolve subset_union2: sets.

Lemma subset_union3:
  forall T (A1 A2 B: list T),
    (subset A1 B /\ subset A2 B) <->
    subset (A1 ++ A2) B.
Proof.
  repeat step || eauto with sets || unfold subset in *.
Qed.

Lemma subset_add:
  forall T (x: T) A B,
    subset (x :: A) B <-> (x ∈ B /\ subset A B).
Proof.
  repeat step || unfold subset in *.
Qed.

Hint Resolve subset_add: sets.

Lemma subset_add2:
  forall T (x: T) A B,
    subset A B ->
    subset A (x :: B).
Proof.
  repeat step || unfold subset in *.
Qed.

Hint Resolve subset_add2: sets.

Lemma subset_add3:
  forall T (x: T) A B,
    ~(x ∈ A) ->
    subset A (x :: B) ->
    subset A B.
Proof.
  repeat step || unfold subset in * || instantiate_any.
Qed.

Hint Resolve subset_add3: sets.

Lemma subset_add4:
  forall T (x y: T) A B,
    ~(x ∈ A) ->
    ~(y ∈ A) ->
    subset A (x :: y :: B) ->
    subset A B.
Proof.
  repeat step || unfold subset in * || instantiate_any.
Qed.

Hint Resolve subset_add4: sets.

Lemma subset_add5:
  forall T (x y z: T) A B,
    ~(x ∈ A) ->
    ~(y ∈ A) ->
    ~(z ∈ A) ->
    subset A (x :: y :: z :: B) ->
    subset A B.
Proof.
  repeat step || unfold subset in * || instantiate_any.
Qed.

Hint Resolve subset_add5: sets.

Lemma subset_insert:
  forall T (x: T) A B1 B2,
    subset A (B1 ++ B2) ->
    subset A (B1 ++ x :: B2).
Proof.
  induction B1;
    repeat step || t_listutils || unfold subset in * || instantiate_any.
Qed.

Hint Resolve subset_insert: sets.

Ltac t_sets :=
  match goal with
  | H1: subset ?L1 ?L2, H2: ?X ∈ ?L1 |- _ =>
    poseNew (Mark (L1,L2,X) "in_subset");
    poseNew (in_subset L1 L2 X)
  | _ => rewrite <- subset_union3 in *
  | _ => rewrite subset_add in *
  | _ => rewrite singleton_subset in *
  | _ => apply subset_union2
  end.

Ltac set_solver := t_sets.

Hint Rewrite <- (@subset_union3 nat): t_simp_set.
Hint Rewrite (@subset_add nat): t_simp_set.
Hint Rewrite (@singleton_subset nat): t_simp_set.

Ltac t_sets2 :=
  repeat autorewrite with t_simp_set in * || step ||
         t_listutils || unfold subset in * || instantiate_any.

Lemma subset_same:
  forall T (A B C: set T),
    subset A B ->
    B = C ->
    subset A C.
Proof.
  intuition.
Qed.

Hint Resolve subset_same: sets.
