Require Export SystemFR.ErasedQuant.

Opaque reducible_values.

(** This file specifies with axioms a model for updates and lookups in trails *)

(** We assume that we have a type `T_tree` that represents a tree of values *)
Parameter T_tree: tree.
Axiom map_fv: forall tag, pfv T_tree tag = nil.
Axiom wf_map: wf T_tree 0.
Axiom is_erased_type_map: is_erased_type T_tree.
Hint Resolve map_fv: fv.
Hint Resolve wf_map: wf.
Hint Resolve is_erased_type_map: erased.

(** We consider a type `T_key` that represents a sequence of selections in a tree *)
Parameter T_key: tree.
Axiom key_fv: forall tag, pfv T_key tag = nil.
Axiom wf_key: wf T_key 0.
Axiom is_erased_type_key: is_erased_type T_key.
Hint Resolve key_fv: fv.
Hint Resolve wf_key: wf.
Hint Resolve is_erased_type_key: erased.

(** A `trail` is a pair made of a selection in `T_key` and a tree `T_tree` *)
Definition T_trail: tree := T_prod T_key T_tree.
Lemma trail_fv: forall tag, pfv T_trail tag = nil.
Proof. repeat step || list_utils; eauto with fv. Qed.
Hint Resolve trail_fv: fv.
Lemma wf_trail: wf T_trail 0.
Proof. steps; eauto with wf. Qed.
Hint Resolve wf_trail: wf.
Lemma is_erased_type_trail: is_erased_type T_trail.
Proof. steps; eauto with erased. Qed.
Hint Resolve is_erased_type_trail: erased.

(** `empty_trail` represents an empty tree with no selection *)
Parameter empty_trail: tree.
Axiom empty_trail_type: [ empty_trail : T_trail ]v.

(** These types have no free variables, so substitutions keep them unchanged *)
Lemma substitute_map:
  forall l tag, psubstitute T_tree l tag = T_tree.
Proof.
  intros; apply substitute_nothing5; eauto using map_fv.
Qed.

Lemma substitute_key:
  forall l tag, psubstitute T_key l tag = T_key.
Proof.
  intros; apply substitute_nothing5; eauto using key_fv.
Qed.

Lemma substitute_trail:
  forall l tag, psubstitute T_trail l tag = T_trail.
Proof.
  repeat step || rewrite substitute_map || rewrite substitute_key.
Qed.

Opaque T_trail.

(** Then, we consider a `tlookup` function that for a type `A` looks up a value in *)
(** the tree. If there is a value of type `A` at the position designated by the trail, `tlookup` *)
(** returns it. Otherwise, it returns the empty list `tnil` or `tleft uu`. We assume that the type *)
(** A that appears in `tlookup` contain the empty list, which is the case for the types `T_top` and *)
(** `List` presented in the paper.  *)
(** tlookup: (A: type) -> T_trail -> A *)
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
Hint Resolve wf_lookup: wf.

Axiom is_erased_term_lookup:
  forall A t,
    is_erased_type A ->
    is_erased_term t ->
    is_erased_term (tlookup A t).
Hint Resolve is_erased_term_lookup: erased.

Axiom lookup_type:
  forall A trail,
    [ tleft uu : A ]v ->
    [ trail : T_trail ]v ->
    [ tlookup A trail : A ].

Axiom lookup_onto:
  forall a A,
    [ a : A ]v ->
    exists trail,
      [ trail : T_trail ]v /\
      [ tlookup A trail ≡ a ].

Axiom lookup_fv:
  forall A trail tag,
    pfv (tlookup A trail) tag = pfv A tag ++ pfv trail tag.

(** We also assume we have a function `append_key`, that adds a sequence of selections to an
    existing trail *)
(** append_key: T_key -> T_trail -> T_trail *)
Parameter append_key: tree -> tree -> tree.

Axiom append_key_trail:
  forall key trail,
    [ key : T_key ]v ->
    [ trail : T_trail ]v ->
    [ append_key key trail : T_trail ]v.

Axiom evaluate_append_key:
  forall key trail1 trail2,
    star scbv_step trail1 trail2 ->
    star scbv_step (append_key key trail1) (append_key key trail2).

Axiom wf_append_key:
  forall k t1 t2,
    wf t1 k ->
    wf t2 k ->
    wf (append_key t1 t2) k.

Axiom psubstitute_append_key:
  forall t1 t2 l tag,
    psubstitute (append_key t1 t2) l tag =
    append_key (psubstitute t1 l tag) (psubstitute t2 l tag).

Axiom open_append_key:
  forall k t1 t2 rep,
    open k (append_key t1 t2) rep =
    append_key (open k t1 rep) (open k t2 rep).

Axiom pfv_append_key:
  forall t1 t2 tag, pfv (append_key t1 t2) tag = pfv t1 tag ++ pfv t2 tag.

Axiom is_erased_term_append_key:
  forall t1 t2,
    is_erased_term t1 ->
    is_erased_term t2 ->
    is_erased_term (append_key t1 t2).

Hint Resolve wf_append_key: wf.
Hint Resolve is_erased_term_append_key: erased.

Lemma open_tdots:
  forall Γ key trail,
    [ key : T_key ]v ->
    [ Γ ⊨ trail : T_trail ] ->
    [ Γ ⊨ append_key key trail : T_trail ].
Proof.
  unfold open_reducible;
    repeat step || rewrite psubstitute_append_key ||
           t_instantiate_sat3_nil || rewrite substitute_trail.

  top_level_unfold reducible; top_level_unfold reduces_to; steps.
  eapply star_backstep_reducible; try apply evaluate_append_key; eauto;
    repeat step || rewrite pfv_append_key || list_utils || rewrite substitute_trail in * ||
           apply wf_append_key || apply is_erased_term_append_key ||
           (rewrite substitute_nothing5 by (steps; eapply reducible_val_fv; eauto; steps));
    try solve [ eapply reducible_val_fv; eauto; steps ];
    try solve [ eapply reducible_val_wf; eauto; steps ];
    try solve [ eapply reducible_values_erased; eauto; steps ];
    t_closer.

  apply reducible_value_expr; repeat step || list_utils2;
    eauto using append_key_trail.
Qed.


(** prefix specifies for two sequences of selections whether the first is a prefix of the second *)
(** prefix: T_key -> T_key -> Prop *)
Parameter prefix: tree -> tree -> Prop.

(** Finally, `update` takes a trail, a key `k`, and a trail, and copies the subtree designated by the
    second trail at position `k` in the first trail *)
(** update: T_trail -> T_key -> T_trail -> T_trail *)
Parameter update: tree -> tree -> tree -> tree.

Axiom update_type:
  forall old_trail key trail,
    [ old_trail : T_trail ]v ->
    [ key : T_key ]v ->
    [ trail : T_trail ]v ->
    [ update old_trail key trail : T_trail ]v.

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

Axiom update_commutative:
  forall key1 key2 old_trail trail1 trail2,
    [ key1 : T_key ]v ->
    [ key2 : T_key ]v ->
    [ trail1 : T_trail ]v ->
    [ trail2 : T_trail ]v ->
    [ old_trail : T_trail ]v ->
    ~ prefix key1 key2 ->
    ~ prefix key2 key1 ->
      update (update old_trail key2 trail2) key1 trail1 =
      update (update old_trail key1 trail1) key2 trail2.

Hint Resolve pfv_update: pfv.
Hint Resolve wf_update: wf.
Hint Resolve is_erased_term_update: erased.


(** Terms `f` that take a trail as argument and only perform lookups on the subtree designated by *)
(** the key satisfy the following property, described by the type `T_tau` *)
(** forall trail key old_trail,
      [ old_trail : T_trail ]v ->
      [ trail : T_trail ]v ->
      [ key : T_key ]v ->
      [ app f trail ≡ app f (append_key key (update old_trail key trail)) ] *)

Definition T_tau: tree :=
  T_type_refine T_top ( (* f *)
    T_forall T_trail ( (* old_trail *)
      T_forall T_key ( (* key *)
        T_forall T_trail ( (* trail *)
          T_equiv
            (app (lvar 3 term_var) (lvar 0 term_var))
            (app (lvar 3 term_var) (append_key (lvar 1 term_var)
              (update (lvar 2 term_var) (lvar 1 term_var) (lvar 0 term_var))))
        )
      )
    )
  ).

Lemma tau_fv: forall tag, pfv T_tau tag = nil.
Proof.
  repeat step || list_utils || rewrite pfv_append_key || rewrite pfv_update;
    eauto with fv.
Qed.

Lemma wf_tau: wf T_tau 0.
Proof.
  repeat step || list_utils || apply wf_append_key || apply wf_update;
    eauto with wf.
Qed.

Lemma is_erased_type_tau: is_erased_type T_tau.
Proof.
  repeat step || list_utils || apply is_erased_term_append_key || apply is_erased_term_update;
    eauto with erased.
Qed.

Hint Resolve wf_tau: wf.
Hint Resolve tau_fv: fv.
Hint Resolve is_erased_type_tau: erased.

Lemma substitute_tau:
  forall l tag, psubstitute T_tau l tag = T_tau.
Proof.
  intros; apply substitute_nothing5; eauto using tau_fv.
Qed.

Lemma tau_property_values:
  forall f trail key old_trail,
    [ f : T_tau ]v ->
    [ old_trail : T_trail ]v ->
    [ trail : T_trail ]v ->
    [ key : T_key ]v ->
    [ app f trail ≡ app f (append_key key (update old_trail key trail)) ].
Proof.
  unfold T_tau; repeat step.
  simp_red; repeat step || open_none.
  apply reducible_value_expr in H; steps.
  apply (reducible_forall_inst _ _ old_trail) in H;
    repeat step || list_utils || apply wf_append_key || apply wf_update ||
                rewrite pfv_append_key || rewrite pfv_update ||
                rewrite open_update in * || rewrite open_append_key in * ||
                open_none;
    eauto with wf;
    eauto with fv;
    eauto using reducible_value_expr.
  apply (reducible_forall_inst _ _ key) in H;
    repeat step || list_utils || apply wf_append_key || apply wf_update ||
                rewrite pfv_append_key || rewrite pfv_update ||
                apply wf_open || apply fv_nils_open ||
                rewrite open_update in * || rewrite open_append_key in * ||
                open_none;
    eauto with wf;
    eauto with fv;
    eauto using reducible_value_expr.
  apply (reducible_forall_inst _ _ trail) in H;
    repeat step || list_utils || open_none || apply wf_append_key || apply wf_update ||
                rewrite pfv_append_key || rewrite pfv_update ||
                rewrite open_update in * || rewrite open_append_key in * ||
                apply wf_open || apply fv_nils_open ||
                (rewrite open_none by repeat step || apply wf_append_key || apply wf_update;
                 eauto with wf);
    eauto with wf;
    eauto with fv;
    eauto using reducible_value_expr.

  unfold reducible, reduces_to in H; repeat step || simp_red.
Qed.

Lemma tau_property:
  forall f trail key old_trail,
    [ f : T_tau ] ->
    [ old_trail : T_trail ]v ->
    [ trail : T_trail ]v ->
    [ key : T_key ]v ->
    [ app f trail ≡ app f (append_key key (update old_trail key trail)) ].
Proof.
  intros.
  unfold reducible, reduces_to in *; steps.
  apply equivalent_trans with (app v trail).
  - apply equivalent_app; steps; equivalent_star;
      try solve [ eapply reducible_values_erased; eauto; steps ];
      try solve [ eapply reducible_val_wf; eauto; steps ];
      try solve [ eapply reducible_val_fv; eauto; steps ].

  - apply equivalent_trans with (app v (append_key key (update old_trail key trail)));
      eauto using tau_property_values.
    apply equivalent_sym, equivalent_app; equivalent_star;
      repeat step || apply wf_append_key || apply wf_update ||
             apply is_erased_term_append_key || apply is_erased_term_update ||
             rewrite pfv_append_key || rewrite pfv_update || list_utils;
      try solve [ eapply reducible_values_erased; eauto; steps ];
      try solve [ eapply reducible_val_wf; eauto; steps ];
      try solve [ eapply reducible_val_fv; eauto; steps ].
Qed.
