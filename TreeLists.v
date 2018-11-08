Require Import Termination.Tactics.
Require Import Termination.Trees.
Require Import Termination.AssocList.

Open Scope list_scope.

Fixpoint erased_terms (l: list (nat * tree)) :=
  match l with
  | nil => True
  | (x,t) :: l' => is_erased_term t /\ erased_terms l'
  end.

Lemma erased_term_in_list:
  forall l t x eq,
    erased_terms l ->
    lookup eq l x = Some t ->
    is_erased_term t.
Proof.
  induction l; steps; eauto.
Qed.

Hint Resolve erased_term_in_list: berased.

Fixpoint annotated_types (l: list (nat * tree)) :=
  match l with
  | nil => True
  | (x,t) :: l' => is_annotated_type t /\ annotated_types l'
  end.

Lemma annotated_type_in_list:
  forall l t x eq,
    annotated_types l ->
    lookup eq l x = Some t ->
    is_annotated_type t.
Proof.
  induction l; steps; eauto.
Qed.

Hint Resolve annotated_type_in_list: bannot.

Lemma annotated_types_append:
  forall l1 l2,
    annotated_types (l1 ++ l2) <-> (annotated_types l1 /\ annotated_types l2).
Proof.
  induction l1 as [ | x l1 IH ];
    repeat step;
    try solve [ apply (IH l1); steps ];
    try solve [ apply (IH l2); steps ].
Qed.

Hint Rewrite annotated_types_append: bannot.
