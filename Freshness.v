From Stdlib Require Import List.
From Stdlib Require Import Psatz.

Require Export SystemFR.Tactics.
Require Export SystemFR.ListUtils.

Require Export SystemFR.AssocList.

Open Scope list_scope.

Fixpoint max (l: list nat): nat :=
  match l with
  | nil => 0
  | x :: xs => x + max xs
  end.

Definition succ_max l := S (max l).

Lemma in_list_smaller (l: list nat): forall (w: nat), In w l -> w <= max l.
Proof.
  induction l; repeat step || instantiate_any; lia.
Qed.

Ltac t_list_smaller :=
  match goal with
  | H: _ |- _ => apply in_list_smaller in H
  end.

Lemma freshMakeFresh: forall {T} (Γ: list (nat * T)),
    fresh Γ (succ_max (support Γ)).
Proof.
  unfold succ_max;
  repeat step || t_list_smaller; lia.
Qed.

Lemma freshMakeFresh2: forall (l: list nat),
    succ_max l ∈ l -> False.
Proof.
  unfold succ_max;
  repeat step || t_list_smaller; lia.
Qed.

#[export]
Hint Immediate freshMakeFresh freshMakeFresh2: fresh.

Fixpoint makeFresh (ll: list (list nat)): nat :=
  match ll with
  | nil => 0
  | l :: ls => S (max (makeFresh ls :: l))
  end.

Lemma length_makeFresh:
  forall ll l,
    l ∈ ll ->
    makeFresh ll > max l.
Proof.
  induction ll; repeat step || list_utils || instantiate_any;
    eauto with lia.
Qed.

Lemma in_makeFresh:
  forall ll l,
    l ∈ ll ->
    makeFresh ll ∈ l ->
    False.
Proof.
  intros.
  apply length_makeFresh in H.
  repeat step || t_list_smaller; lia.
Qed.

Lemma eq_makeFresh:
  forall ll x,
    (x :: nil) ∈ ll ->
    x = makeFresh ll ->
    False.
Proof.
  intros.
  apply length_makeFresh in H; steps; eauto with lia.
Qed.

Ltac finisher :=
  match goal with
  | H: makeFresh ?LL ∈ ?L |- _ => solve [ apply False_ind;
                                         apply (in_makeFresh LL L); cbn; intuition auto ]
  | H: ?S = makeFresh ?LL |- _ => solve [ apply False_ind;
                                         apply (eq_makeFresh LL S); cbn; intuition auto ]
  | H: makeFresh ?LL = ?S |- _ => solve [ apply False_ind;
                                         apply (eq_makeFresh LL S); cbn; intuition auto ]
  end.

Lemma instantiate1:
  forall F P L,
    (forall x, (x ∈ L -> False) -> P x) ->
    P (makeFresh (F :: L :: nil)).
Proof.
  repeat step || apply_any || finisher || t_list_smaller; lia.
Qed.

Lemma instantiate2:
  forall F P L,
    (forall x y, (x ∈ L -> False) -> (y ∈ L -> False) -> (x = y -> False) -> P x y) ->
    P (makeFresh (F :: L :: nil))
      (S (makeFresh (F :: L :: nil))).
Proof.
  repeat step || apply_any || finisher || t_list_smaller; eauto with lia.
Qed.

Lemma instantiate3:
  forall F P L,
    (forall x y z, (x ∈ L -> False) -> (y ∈ L -> False) -> (z ∈ L -> False) -> (NoDup (x :: y :: z :: nil)) -> P x y z) ->
    P (makeFresh (F :: L :: nil))
      (S (makeFresh (F :: L :: nil)))
      (S (S (makeFresh (F :: L :: nil)))).
Proof.
  repeat step || apply_any || finisher || t_list_smaller; eauto with lia.
Qed.

Lemma instantiate4:
  forall F P L,
    (forall x y z t, (x ∈ L -> False) -> (y ∈ L -> False) -> (z ∈ L -> False) -> (t ∈ L -> False) ->
                (NoDup (x :: y :: z :: t :: nil)) -> P x y z t) ->
    P (makeFresh (F :: L :: nil))
      (S (makeFresh (F :: L :: nil)))
      (S (S (makeFresh (F :: L :: nil))))
      (S (S (S (makeFresh (F :: L :: nil))))).
Proof.
  repeat step || apply_any || finisher || t_list_smaller; eauto with lia.
Qed.


Ltac fresh_instantiations F :=
  match goal with
  | H: _ |- _ => apply (instantiate1 F) in H
  | H: _ |- _ => apply (instantiate2 F) in H
  | H: _ |- _ => apply (instantiate3 F) in H
  | H: _ |- _ => apply (instantiate4 F) in H
  end.

Ltac fresh_instantiations0 := fresh_instantiations (@nil nat).

Ltac fresh_instantiations1 :=
  match goal with
  | x: nat, H: _ |- _ => apply (instantiate1 (x :: nil)) in H
  | x: nat, H: _ |- _ => apply (instantiate2 (x :: nil)) in H
  | x: nat, H: _ |- _ => apply (instantiate3 (x :: nil)) in H
  | x: nat, H: _ |- _ => apply (instantiate4 (x :: nil)) in H
  end.
