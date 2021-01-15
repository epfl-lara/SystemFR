Require Import Coq.Strings.String.
Require Import Coq.Lists.List.

Require Export SystemFR.ListUtils.

Lemma subset_refl:
  forall A (s: list A), subset s s.
Proof.
  unfold subset; steps.
Qed.

Lemma in_subset:
  forall {T} (l1 l2: list T) (x: T),
    subset l1 l2 -> x ∈ l1 -> x ∈ l2.
Proof.
  steps.
Qed.

#[global]
Hint Resolve in_subset: sets.

Lemma singleton_subset:
  forall {T} (l: list T) (x: T),
    subset (singleton x) l <->
    x ∈ l.
Proof.
  unfold subset; unfold singleton; steps.
Qed.

#[global]
Hint Resolve singleton_subset: sets.

Lemma singleton_subset2:
  forall {T} (l: list T) (x: T),
    subset (singleton x) (x :: l).
Proof.
  unfold subset; unfold singleton; steps.
Qed.

#[global]
Hint Resolve singleton_subset2: sets.

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

#[global]
Hint Resolve union_left union_right1 union_right2: sets.

Lemma union_weaken1:
  forall {T} (l1 l2 s: list T),
    subset (l1 ++ l2) s ->
    subset l1 s.
Proof.
  induction l1; unfold subset in *; repeat step || apply_any || list_utils.
Qed.

Lemma union_weaken2:
  forall {T} (l1 l2 s: list T),
    subset (l1 ++ l2) s ->
    subset l2 s.
Proof.
  induction l1; unfold subset in *; repeat step || apply_any || list_utils.
Qed.

Lemma union_weaken3:
  forall {T} (l1 l2 l3 l4 s: list T),
    subset (l1 ++ l2 ++ l3 ++ l4) s ->
    subset l3 s.
Proof.
  induction l1; unfold subset in *; repeat step || apply_any || list_utils.
Qed.

Lemma union_weaken4:
  forall {T} (l1 l2 l3 l4 s: list T),
    subset (l1 ++ l2 ++ l3 ++ l4) s ->
    subset l4 s.
Proof.
  induction l1; unfold subset in *; repeat step || apply_any || list_utils.
Qed.

#[global]
Hint Immediate union_weaken1: sets.
#[global]
Hint Immediate union_weaken2: sets.
#[global]
Hint Immediate union_weaken3: sets.
#[global]
Hint Immediate union_weaken4: sets.

Lemma empty_is_subset:
  forall {T} (l: list T),
    subset empty l.
Proof.
  unfold subset; steps.
Qed.

#[global]
Hint Immediate empty_is_subset: sets.

Lemma subset_transitive:
  forall {T} (l1 l2 l3: list T),
    subset l1 l2 ->
    subset l2 l3 ->
    subset l1 l3.
Proof.
  unfold subset; steps.
Qed.

#[global]
Hint Immediate subset_transitive: sets.

Lemma subset_union:
  forall {T} (A1 A2 B1 B2: list T),
    subset A1 B1 ->
    subset A2 B2 ->
    subset (A1 ++ A2) (B1 ++ B2).
Proof.
  eauto with sets.
Qed.

#[global]
Hint Immediate subset_union: sets.

Lemma subset_union2:
  forall {T} (A1 A2 B: list T),
    subset A1 B ->
    subset A2 B ->
    subset (A1 ++ A2) B.
Proof.
  eauto with sets.
Qed.

#[global]
Hint Resolve subset_union2: sets.

Lemma subset_union3:
  forall T (A1 A2 B: list T),
    (subset A1 B /\ subset A2 B) <->
    subset (A1 ++ A2) B.
Proof.
  steps; eauto 2 with sets.
Qed.

Lemma subset_add:
  forall T (x: T) A B,
    subset (x :: A) B <-> (x ∈ B /\ subset A B).
Proof.
  repeat step || unfold subset in *.
Qed.

Lemma subset_add2:
  forall T (x: T) A B,
    subset A B ->
    subset A (x :: B).
Proof.
  repeat step || unfold subset in *.
Qed.

#[global]
Hint Immediate subset_add2: sets.

Lemma subset_add3:
  forall T (x: T) A B,
    ~(x ∈ A) ->
    subset A (x :: B) ->
    subset A B.
Proof.
  repeat step || unfold subset in * || instantiate_any.
Qed.

#[global]
Hint Immediate subset_add3: sets.

Lemma subset_add4:
  forall T (x y: T) A B,
    ~(x ∈ A) ->
    ~(y ∈ A) ->
    subset A (x :: y :: B) ->
    subset A B.
Proof.
  repeat step || unfold subset in * || instantiate_any.
Qed.

#[global]
Hint Immediate subset_add4: sets.

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

#[global]
Hint Immediate subset_add5: sets.

Lemma subset_insert:
  forall T (x: T) A B1 B2,
    subset A (B1 ++ B2) ->
    subset A (B1 ++ x :: B2).
Proof.
  induction B1;
    repeat step || list_utils || unfold subset in * || instantiate_any.
Qed.

#[global]
Hint Immediate subset_insert: sets.

Hint Rewrite <- (@subset_union3 nat): simp_set.
Hint Rewrite (@subset_add nat): simp_set.
Hint Rewrite (@singleton_subset nat): simp_set.

Ltac sets :=
  match goal with
  | H1: subset ?L1 ?L2, H2: ?X ∈ ?L1 |- _ =>
    poseNew (Mark (L1,L2,X) "in_subset");
    poseNew (in_subset L1 L2 X)
  | _ => autorewrite with simp_set in * || list_utils
  | _ => apply subset_union2
  end.

Lemma subset_same:
  forall T (A B C: list T),
    subset A B ->
    B = C ->
    subset A C.
Proof.
  intuition.
Qed.

Lemma subset_singleton:
  forall A (x: A) l,
    subset (singleton x) l ->
    (x ∈ l -> False) ->
    False.
Proof.
  unfold subset; steps.
Qed.

Lemma in_left:
  forall A (x: A) l1 l2,
    x ∈ l1 ->
    x ∈ l1 ++ l2.
Proof.
  repeat step || list_utils.
Qed.

Lemma in_right:
  forall A (x: A) l1 l2,
    x ∈ l2 ->
    x ∈ l1 ++ l2.
Proof.
  repeat step || list_utils.
Qed.

Lemma fair_split:
  forall A l1 l1' l2 l2' (x: A),
    (forall z, z ∈ l1 -> z ∈ l1') ->
    (forall z, z ∈ l2 -> z ∈ l2') ->
    x ∈ l1 ++ l2 ->
    x ∈ l1' ++ l2'.
Proof.
  repeat step || list_utils.
Qed.

Ltac t_fair_split :=
  match goal with
  | H: ?x ∈ ?l1 ++ ?l2 |- ?x ∈ ?l1' ++ ?l2' => apply fair_split with l1 l2
  end.

Lemma strange_split:
  forall A l1 l1' l2 l2' l3 (x: A),
    (forall z, z ∈ l1 -> z ∈ l1' ++ l3) ->
    (forall z, z ∈ l2 -> z ∈ l2' ++ l3) ->
    x ∈ l1 ++ l2 ->
    x ∈ (l1' ++ l2') ++ l3.
Proof.
  repeat step || list_utils || instantiate_any.
Qed.

Ltac t_strange_split :=
  match goal with
  | H: ?x ∈ ?l1 ++ ?l2 |- ?x ∈ (?l1' ++ ?l2') ++ ?l3 =>
    apply strange_split with l1 l2
  end.

Lemma strange_split3:
  forall A l1 l1' l2 l2' l3 l3' l4 (x: A),
    (forall z, z ∈ l1 -> z ∈ l1' ++ l4) ->
    (forall z, z ∈ l2 -> z ∈ l2' ++ l4) ->
    (forall z, z ∈ l3 -> z ∈ l3' ++ l4) ->
    x ∈ l1 ++ l2 ++ l3 ->
    x ∈ (l1' ++ l2' ++ l3') ++ l4.
Proof.
  repeat step || list_utils || instantiate_any.
Qed.

Ltac t_strange_split3 :=
  match goal with
  | H: ?x ∈ ?l1 ++ ?l2 ++ ?l3 |- ?x ∈ (?l1' ++ ?l2' ++ ?l3') ++ ?l4 =>
    apply strange_split3 with l1 l2 l3
  end.

Lemma strange_split4:
  forall A l1 l1' l2 l2' l3 l3' l4 l4' l5 (x: A),
    (forall z, z ∈ l1 -> z ∈ l1' ++ l5) ->
    (forall z, z ∈ l2 -> z ∈ l2' ++ l5) ->
    (forall z, z ∈ l3 -> z ∈ l3' ++ l5) ->
    (forall z, z ∈ l4 -> z ∈ l4' ++ l5) ->
    x ∈ l1 ++ l2 ++ l3 ++ l4 ->
    x ∈ (l1' ++ l2' ++ l3' ++ l4') ++ l5.
Proof.
  repeat step || list_utils || instantiate_any.
Qed.

Ltac t_strange_split4 :=
  match goal with
  | H: ?x ∈ ?l1 ++ ?l2 ++ ?l3 ++ ?l4 |- ?x ∈ (?l1' ++ ?l2' ++ ?l3' ++ ?l4') ++ ?l5 =>
    apply strange_split4 with l1 l2 l3 l4
  end.

Lemma in_middle:
  forall A (x: A) (s1 s2: list A),
    x ∈ s1 ++ x :: s2.
Proof.
  induction s1; steps.
Qed.

#[global]
Hint Immediate in_middle: sets.

Lemma subset_left:
  forall A (s1 s2 s3: list A),
    subset s1 s2 ->
    subset s1 (s2 ++ s3).
Proof.
  eauto with sets.
Qed.

Lemma in_middle2:
  forall A (x: A) (s1 s2 s3: list A),
    x ∈ (s1 ++ x :: s2) ++ s3.
Proof.
  induction s1; steps.
Qed.

#[global]
Hint Immediate in_middle2: sets.

Lemma subset_middle:
  forall A (x: A) (s s1 s2: list A),
    ~(x ∈ s) ->
    subset s (s1 ++ x :: s2) ->
    subset s (s1 ++ s2).
Proof.
  unfold subset; induction s1; repeat step || list_utils || instantiate_any.
Qed.

#[global]
Hint Immediate subset_middle: sets.

Lemma subset_middle2:
  forall A (x y: A) (s s1 s2: list A),
    ~(x ∈ s) ->
    ~(y ∈ s) ->
    subset s (s1 ++ x :: y :: s2) ->
    subset s (s1 ++ s2).
Proof.
  unfold subset; induction s1; repeat step || list_utils || instantiate_any.
Qed.

Lemma subset_middle3:
  forall A (x y: A) (s s1 s2: list A),
    ~(y ∈ s) ->
    subset s (s1 ++ x :: y :: s2) ->
    subset s (s1 ++ x :: s2).
Proof.
  unfold subset; induction s1; repeat step || list_utils || instantiate_any.
Qed.

Lemma subset_middle4:
  forall A (x y z: A) (s s1 s2: list A),
    ~(y ∈ s) ->
    ~(z ∈ s) ->
    subset s (s1 ++ x :: y :: z :: s2) ->
    subset s (s1 ++ x :: s2).
Proof.
  unfold subset; induction s1; repeat step || list_utils || instantiate_any.
Qed.

Lemma subset_middle5:
  forall A (x: A) (s s1 s2 s3: list A),
    ~(x ∈ s) ->
    subset s ((s1 ++ x :: s2) ++ s3) ->
    subset s ((s1 ++ s2) ++ s3).
Proof.
  unfold subset; induction s1; repeat step || list_utils || instantiate_any.
Qed.

Lemma subset_middle6:
  forall A (x y: A) (s s1 s2 s3: list A),
    ~(x ∈ s) ->
    ~(y ∈ s) ->
    subset s ((s1 ++ x :: y :: s2) ++ s3) ->
    subset s ((s1 ++ s2) ++ s3).
Proof.
  unfold subset; induction s1; repeat step || list_utils || instantiate_any.
Qed.

#[global]
Hint Immediate subset_middle5: sets.

Lemma subset_middle7:
  forall A (x y: A) (s s1 s2 s3: list A),
    ~(y ∈ s) ->
    subset s ((s1 ++ x :: y :: s2) ++ s3) ->
    subset s ((s1 ++ x :: s2) ++ s3).
Proof.
  unfold subset; induction s1; repeat step || list_utils || instantiate_any.
Qed.

Lemma subset_middle_indirect:
  forall A (s1 s2: list A),
    subset s2 (s1 ++ s2).
Proof.
  intros; eauto with sets.
Qed.

#[global]
Hint Immediate subset_middle_indirect: sets.

Lemma subset_middle_indirect2:
  forall A (x: A) (s1 s2: list A),
    subset s2 (s1 ++ x :: s2).
Proof.
  intros; eauto with sets.
Qed.

#[global]
Hint Immediate subset_middle_indirect2: sets.

Lemma subset_right:
  forall A (s1 s2 s3: list A),
    subset s1 s3 ->
    subset s1 (s2 ++ s3).
Proof.
  eauto with sets.
Qed.

Lemma subset_right2:
  forall A x (s1 s2 s3: list A),
    subset s1 s3 ->
    subset s1 (s2 ++ x :: s3).
Proof.
  repeat step || apply subset_right; eauto 2 with sets.
Qed.

Lemma subset_right3:
  forall A x (s1 s2 s3 s4: list A),
    subset s1 s3 ->
    subset s1 ((s2 ++ x :: s3) ++ s4).
Proof.
  eauto using subset_left, subset_right, subset_add2.
Qed.

Lemma subset_right4:
  forall A x (s1 s2 s3 s4: list A),
    subset s1 (s3 ++ s4) ->
    subset s1 ((s2 ++ x :: s3) ++ s4).
Proof.
  repeat step || list_utils || unfold subset in * || instantiate_any.
Qed.

Lemma subset_right5:
  forall A x (s1 s2: list A),
    subset s1 s2 ->
    subset s1 (x :: s2).
Proof.
  eauto with sets.
Qed.

Lemma subset_right6:
  forall A (s s1 s2 s3: list A),
    subset s (s2 ++ s3) ->
    subset s ((s1 ++ s2) ++ s3).
Proof.
  repeat step || list_utils || unfold subset in * || instantiate_any.
Qed.

#[global]
Hint Immediate subset_right: sets.
#[global]
Hint Immediate subset_right2: sets.
#[global]
Hint Immediate subset_right3: sets.
#[global]
Hint Immediate subset_right4: sets.
#[global]
Hint Immediate subset_right5: sets.
#[global]
Hint Immediate subset_right6: sets.
