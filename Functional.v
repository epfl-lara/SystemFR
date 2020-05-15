Require Import PeanoNat.
Require Import Psatz.
Require Import Coq.Lists.List.

Require Export SystemFR.AssocList.
Require Export SystemFR.SubstitutionLemmas.

Definition functional { A B } (m: map A B) :=
  forall a b1 b2,
    (a, b1) ∈ m ->
    (a, b2) ∈ m ->
    b1 = b2.

Lemma functional_head:
  forall A B a b1 b2 (m: map A B),
    functional ((a, b1) :: m) ->
    (a, b2) ∈ m ->
    b1 = b2.
Proof.
  unfold functional; steps; eauto.
Qed.

Lemma functional_tail:
  forall A B a b (m: map A B),
    functional ((a, b) :: m) ->
    functional m.
Proof.
  unfold functional; steps; eauto.
Qed.

Lemma functional_tail2:
  forall A B a1 a2 b1 b2 (m: map A B),
    functional ((a1, b1) :: (a2, b2) :: m) ->
    functional ((a1, b1) :: m).
Proof.
  unfold functional; steps; eauto 6.
Qed.

Lemma functional_get_or_else:
  forall T a b (m: map nat T),
    functional m ->
    functional (m ++ (a, get_or_else (lookup Nat.eq_dec m a) b) :: nil).
Proof.
  unfold functional, get_or_else;
    repeat step || list_utils || t_lookup; eauto;
    try solve [ apply_anywhere lookup_some_in; steps; eauto ];
    try solve [ apply_anywhere in_map_in_support; steps; eauto ];
    eauto using in_combine_l with exfalso.
Qed.

Lemma functionalize_helper:
  forall n (l: map nat tree),
   length l < n ->
   exists l',
     functional l' /\
      (forall y, y ∈ range l' -> y ∈ range l) /\
     support l = support l' /\
     equivalent_subst l l'.
Proof.
  induction n; steps; try lia.
  pose proof (decide_empty _ l); steps.
  - unfold functional, equivalent_subst; exists nil; steps.
  - unshelve epose proof (@exists_last _ l _);
      repeat step || destruct_refinement.
    unshelve epose proof (IHn x _); repeat step || rewrite app_length in *; try lia.
    exists (l' ++ (n0, get_or_else (lookup Nat.eq_dec l' n0) t) :: nil);
      repeat step || apply equivalent_subst_snoc || list_utils || list_utils2;
      eauto 2 using functional_get_or_else.
    unfold get_or_else; steps; eauto using lookupRange.
Qed.

Lemma functionalize:
  forall (l: map nat tree),
    exists l',
      functional l' /\
      (forall y, y ∈ range l' -> y ∈ range l) /\
      support l = support l' /\
      equivalent_subst l l'.
Proof.
  eauto using functionalize_helper.
Qed.

Lemma functionalize_subst:
  forall t l tag,
  exists l',
    functional l' /\
    psubstitute t l tag = psubstitute t l' tag.
Proof.
  intros.
  pose proof (functionalize l); steps;
    eauto using subst_permutation.
Qed.

Lemma functional_trans:
  forall A B C (l1: list A) (l2: list B) (l3: list C),
    length l1 = length l2 ->
    length l2 = length l3 ->
    functional (combine l1 l2) ->
    functional (combine l2 l3) ->
    functional (combine l1 l3).
Proof.
  unfold functional; repeat step.
  unshelve epose proof (combine_middle_point _ _ _ l1 l2 l3 a b1 _ _ H3); steps.
  unshelve epose proof (combine_middle_point _ _ _ l1 l2 l3 a b2 _ _ H4); steps.
  pose proof (H1 _ _ _ H6 H8); steps.
  pose proof (H2 _ _ _ H7 H9); steps.
Qed.
