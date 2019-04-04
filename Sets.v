Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Arith.PeanoNat.

Require Import SystemFR.Tactics.

Definition set (T: Type) := list T.

Notation "A - n" := (List.remove Nat.eq_dec n A).
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

Notation "A -- B" := (diff Nat.eq_dec A B) (at level 50).

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
