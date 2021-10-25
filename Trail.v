Require Export SystemFR.ErasedQuant.

Opaque reducible_values.

(** This file specifies with axioms a model for updates and lookups in trails *)

(** We assume that we have a type `T_tree` that represents a tree of values, together with *)
(** an encoding of their types *)
Parameter T_tree: tree.
Axiom tree_fv: forall tag, pfv T_tree tag = nil.
Axiom wf_tree: wf T_tree 0.
Axiom is_erased_type_tree: is_erased_type T_tree.
#[export]
Hint Resolve tree_fv: fv.
#[export]
Hint Resolve wf_tree: wf.
#[export]
Hint Resolve is_erased_type_tree: erased.

(* We assume we have an empty tree *)
Parameter empty_tree: tree.
Axiom empty_tree_type: [ empty_tree : T_tree ]v.

(** We consider a type `T_key` that represents a sequence of selections in a tree *)
Parameter T_key: tree.
Axiom key_fv: forall tag, pfv T_key tag = nil.
Axiom wf_key: wf T_key 0.
Axiom is_erased_type_key: is_erased_type T_key.
#[export]
Hint Resolve key_fv: fv.
#[export]
Hint Resolve wf_key: wf.
#[export]
Hint Resolve is_erased_type_key: erased.

(** These types have no free variables, so substitutions keep them unchanged *)
Lemma substitute_tree:
  forall l tag, psubstitute T_tree l tag = T_tree.
Proof.
  intros; apply substitute_nothing5; eauto using tree_fv.
Qed.

Lemma substitute_key:
  forall l tag, psubstitute T_key l tag = T_key.
Proof.
  intros; apply substitute_nothing5; eauto using key_fv.
Qed.

(** We consider a `tlookup` function that for a type `A` and a tree `t` looks up a value at the *)
(** root of the tree. If the tag at the root corresponds to type `A`, it returns the value at the *)
(** root. Otherwise, it returns the empty list `tnil` or `tleft uu`. We assume that the type *)
(** `A` that appears in `tlookup` contain the empty list, which is the case for the types `T_top` *)
(** and `List` presented in the paper.  *)
(** tlookup: (A: type) -> T_tree -> A *)
Parameter tlookup: tree -> tree -> tree.

Axiom open_lookup:
  forall k A t rep,
    open k (tlookup A t) rep = tlookup (open k A rep) (open k t rep).

Axiom substitute_lookup:
  forall A t l tag,
    psubstitute (tlookup A t) l tag =
    tlookup (psubstitute A l tag) (psubstitute t l tag).

Axiom wf_lookup:
  forall k A t,
    wf A k ->
    wf t k ->
    wf (tlookup A t) k.
#[export]
Hint Resolve wf_lookup: wf.

Axiom is_erased_term_lookup:
  forall A t,
    is_erased_type A ->
    is_erased_term t ->
    is_erased_term (tlookup A t).
#[export]
Hint Resolve is_erased_term_lookup: erased.

Axiom lookup_type:
  forall A tree,
    [ tleft uu : A ]v ->
    [ tree : T_tree ]v ->
    [ tlookup A tree : A ].

Axiom lookup_onto:
  forall a A,
    [ a : A ]v ->
    exists tree,
      [ tree : T_tree ]v /\
      [ tlookup A tree ≡ a ].

Axiom lookup_fv:
  forall A trail tag,
    pfv (tlookup A trail) tag = pfv A tag ++ pfv trail tag.

(** We also assume we have a function `select`, that uses a sequence of selections to select a *)
(** subtree of a tree *)
(** select: T_key -> T_tree -> T_tree *)
Parameter select: tree -> tree -> tree.

Axiom select_type:
  forall key tree,
    [ key : T_key ]v ->
    [ tree : T_tree ]v ->
    [ select key tree : T_tree ]v.

Axiom evaluate_select:
  forall key trail1 trail2,
    trail1 ~>* trail2 ->
    select key trail1 ~>* select key trail2.

Axiom wf_select:
  forall k t1 t2,
    wf t1 k ->
    wf t2 k ->
    wf (select t1 t2) k.

Axiom psubstitute_select:
  forall t1 t2 l tag,
    psubstitute (select t1 t2) l tag =
    select (psubstitute t1 l tag) (psubstitute t2 l tag).

Axiom open_select:
  forall k t1 t2 rep,
    open k (select t1 t2) rep =
    select (open k t1 rep) (open k t2 rep).

Axiom pfv_select:
  forall t1 t2 tag, pfv (select t1 t2) tag = pfv t1 tag ++ pfv t2 tag.

Axiom is_erased_term_select:
  forall t1 t2,
    is_erased_term t1 ->
    is_erased_term t2 ->
    is_erased_term (select t1 t2).

#[export]
Hint Resolve wf_select: wf.
#[export]
Hint Resolve is_erased_term_select: erased.

Lemma open_tdots:
  forall Γ key tree,
    [ key : T_key ]v ->
    [ Γ ⊫ tree : T_tree ] ->
    [ Γ ⊫ select key tree : T_tree ].
Proof.
  unfold open_reducible;
    repeat step || rewrite psubstitute_select ||
           t_instantiate_sat3_nil || rewrite substitute_tree.

  top_level_unfold reduces_to; steps.
  eapply star_backstep_reducible; try apply evaluate_select; eauto;
    repeat step || rewrite pfv_select || list_utils || rewrite substitute_tree in * ||
           apply wf_select || apply is_erased_term_select ||
           (rewrite substitute_nothing5 by (steps; eapply reducible_val_fv; eauto; steps));
    try solve [ eapply reducible_val_fv; eauto; steps ];
    try solve [ eapply reducible_val_wf; eauto; steps ];
    try solve [ eapply reducible_values_erased; eauto; steps ];
    t_closer.

  apply reducible_value_expr; repeat step || list_utils2;
    eauto using select_type.
Qed.


(** prefix specifies for two sequences of selections whether the first is a prefix of the second *)
(** prefix: T_key -> T_key -> Prop *)
Parameter prefix: tree -> tree -> Prop.

(** Finally, `update` takes a tree, a key `k`, another tree, and copies the latter in the first *)
(** tree at at position `k` *)
(** update: T_tree -> T_key -> T_tree -> T_tree *)
Parameter update: tree -> tree -> tree -> tree.

Axiom update_type:
  forall old_tree key tree,
    [ old_tree : T_tree ]v ->
    [ key : T_key ]v ->
    [ tree : T_tree ]v ->
    [ update old_tree key tree : T_tree ]v.

Axiom wf_update:
  forall k t1 t2 t3,
    wf t1 k ->
    wf t2 k ->
    wf t3 k ->
    wf (update t1 t2 t3) k.

Axiom open_update:
  forall t1 t2 t3 k rep,
    open k (update t1 t2 t3) rep =
    update (open k t1 rep) (open k t2 rep) (open k t3 rep).

Axiom psubstitute_update:
  forall t1 t2 t3 l tag,
    psubstitute (update t1 t2 t3) l tag =
    update (psubstitute t1 l tag) (psubstitute t2 l tag) (psubstitute t3 l tag).

Axiom pfv_update:
  forall t1 t2 t3 tag,
    pfv (update t1 t2 t3) tag = pfv t1 tag ++ pfv t2 tag ++ pfv t3 tag.

Axiom is_erased_term_update:
  forall t1 t2 t3,
    is_erased_term t1 ->
    is_erased_term t2 ->
    is_erased_term t3 ->
    is_erased_term (update t1 t2 t3).


(** Updates that happen on selections which are not prefixes of another are commutative *)
Axiom update_commutative:
  forall key1 key2 old_tree tree1 tree2,
    [ key1 : T_key ]v ->
    [ key2 : T_key ]v ->
    [ tree1 : T_tree ]v ->
    [ tree2 : T_tree ]v ->
    [ old_tree : T_tree ]v ->
    ~ prefix key1 key2 ->
    ~ prefix key2 key1 ->
      update (update old_tree key2 tree2) key1 tree1 =
      update (update old_tree key1 tree1) key2 tree2.

(** Selecting at a key after an update gives back the replaced tree *)
Axiom select_update:
  forall key old_tree tree,
    select key (update old_tree key tree) = tree.

#[export]
Hint Resolve pfv_update: pfv.
#[export]
Hint Resolve wf_update: wf.
#[export]
Hint Resolve is_erased_term_update: erased.
