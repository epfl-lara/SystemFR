Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Init.Datatypes.
Require Import Coq.Arith.PeanoNat.

Require Export SystemFR.Syntax.

Ltac slow_instantiations :=
  match goal with
  | H1: ?x ∈ pfv ?t ?tag, H2: forall x, x ∈ pfv (open _ ?t _) ?tag -> _ |- _ =>
    unshelve epose proof (H2 x _); clear H2
  | H1: ?x ∈ pfv ?t ?tag, H2: forall x, x ∈ pfv (open _ ?t _) ?tag -> _ |- _ =>
    unshelve epose proof (H2 x _); clear H2
  | H1: ?x ∈ pfv ?t ?tag, H2: forall x, x ∈ pfv (topen _ ?t _) ?tag -> _ |- _ =>
    unshelve epose proof (H2 x _); clear H2
  | H1: ?x ∈ pfv ?t ?tag, H2: forall x, x ∈ pfv (topen _ ?t _) ?tag -> _ |- _ =>
    unshelve epose proof (H2 x _); clear H2
  | H1: ?x ∈ pfv ?t ?tag, H2: forall x, x ∈ pfv (open _ (open _ ?t _) _) ?tag -> _ |- _ =>
    unshelve epose proof (H2 x _); clear H2
  | H1: ?x ∈ pfv ?t ?tag, H2: forall x, x ∈ pfv (open _ (open _ ?t _) _) ?tag -> _ |- _ =>
    unshelve epose proof (H2 x _); clear H2
  | H1: ?x ∈ ?L, H2: forall x, x ∈ ?L ++ _ -> _ |- _ =>
    unshelve epose proof (H2 x _); clear H2
  end.

Lemma fv_context_support:
  forall gamma x tag,
   x ∈ support gamma ->
   x ∈ pfv_context gamma tag.
Proof.
  induction gamma; repeat step || t_listutils.
Qed.

Hint Resolve fv_context_support: fv.

Lemma fv_lookup:
  forall gamma x T tag,
    lookup Nat.eq_dec gamma x = Some T ->
    subset (pfv T tag) (pfv_context gamma tag).
Proof.
  induction gamma;
    repeat step || unfold subset in * || t_listutils; eauto.
Qed.

Lemma fv_lookup2:
  forall gamma x T y tag,
    lookup Nat.eq_dec gamma x = Some T ->
    y ∈ pfv T tag ->
    y ∈ pfv_context gamma tag.
Proof.
  induction gamma; repeat step || t_sets || unfold subset in * || t_listutils; eauto.
Qed.

Lemma fv_lookup3:
  forall gamma x T tag,
    lookup Nat.eq_dec gamma x = Some T ->
    x ∈ pfv_context gamma tag.
Proof.
  induction gamma; repeat step || t_listutils; eauto.
Qed.

Lemma fv_lookup4:
  forall l x T y tag,
    lookup Nat.eq_dec l x = Some T ->
    y ∈ pfv T tag ->
    y ∈ pfv_range l tag.
Proof.
  induction l; repeat step || t_sets || unfold subset in * || t_listutils; eauto.
Qed.

Hint Resolve fv_lookup: fv.
Hint Resolve fv_lookup2: fv.
Hint Resolve fv_lookup3: fv.
Hint Resolve fv_lookup4: fv.

Lemma fv_in_open:
  forall t x r k tag,
    x ∈ pfv t tag ->
    x ∈ pfv (open k t r) tag.
Proof.
  induction t; repeat light || t_fair_split.
Qed.

Hint Resolve fv_in_open: fv.

Lemma fv_in_topen:
  forall t x r k tag,
    x ∈ pfv t tag ->
    x ∈ pfv (topen k t r) tag.
Proof.
  induction t; repeat light || t_fair_split.
Qed.

Hint Resolve fv_in_topen: fv.

Lemma fv_open2:
  (forall t rep k y tag,
     y ∈ pfv (open k t rep) tag ->
     y ∈ pfv t tag ++ pfv rep tag).
Proof.
  induction t;
    repeat light;
    try solve [ apply in_left; assumption ];
    try solve [ eapply_any; eauto 1 ];
    try solve [ steps ];
    try solve [ t_strange_split; repeat light || eapply_any ];
    try solve [ t_strange_split3; repeat light || eapply_any ];
    try solve [ t_strange_split4; repeat light || eapply_any ].
Qed.

Lemma fv_topen2:
  (forall t rep k y tag,
     y ∈ pfv (topen k t rep) tag ->
     y ∈ pfv t tag ++ pfv rep tag).
Proof.
  induction t;
    repeat light;
    try solve [ apply in_left; assumption ];
    try solve [ eapply_any; eauto 1 ];
    try solve [ steps ];
    try solve [ t_strange_split; repeat light || eapply_any ];
    try solve [ t_strange_split3; repeat light || eapply_any ];
    try solve [ t_strange_split4; repeat light || eapply_any ].
Qed.

Ltac t_fv_open :=
  match goal with
  | H: _ ∈ pfv (open _ _ _) _  |- _ => apply fv_open2 in H
  | H: _ ∈ pfv (topen _ _ _) _  |- _ => apply fv_topen2 in H
  end.

Lemma fv_open:
  forall t rep k tag,
    subset (pfv (open k t rep) tag) (pfv t tag ++ pfv rep tag).
Proof.
  unfold subset; repeat step || t_fv_open.
Qed.

Lemma fv_topen:
  forall t rep k tag,
    subset (pfv (topen k t rep) tag) (pfv t tag ++ pfv rep tag).
Proof.
  unfold subset; repeat step || t_fv_open.
Qed.

Lemma fv_nils_open:
  forall t rep k tag,
    pfv t tag = nil ->
    pfv rep tag = nil ->
    pfv (open k t rep) tag = nil.
Proof.
  intros;
  rewrite <- (empty_list_rewrite nat) in *;
    repeat step || t_listutils || t_fv_open; eauto.
Qed.

Hint Resolve fv_nils_open: fv.

Lemma fv_nils_topen:
  forall t rep k tag,
    pfv t tag = nil ->
    pfv rep tag = nil ->
    pfv (topen k t rep) tag = nil.
Proof.
  intros;
  rewrite <- (empty_list_rewrite nat) in *;
    repeat step || t_listutils || t_fv_open; eauto.
Qed.

Hint Resolve fv_nils_topen: fv.

Lemma fv_subst_lemma:
  forall s1 s1' s2 s2' s3 x,
    subset s1 (s1' - x ++ s3) ->
    subset s2 (s2' - x ++ s3) ->
    subset (s1 ++ s2) ((s1' ++ s2') - x ++ s3).
Proof.
  unfold subset; repeat step || t_listutils || instantiate_any.
Qed.

Lemma fv_subst:
  forall t x rep tag,
    subset (pfv (psubstitute t ((x,rep) :: nil) tag) tag)
           (((pfv t tag) - x) ++ pfv rep tag).
Proof.
  induction t;
    repeat step || apply fv_subst_lemma;
    eauto 2 with sets.
Qed.

Hint Resolve fv_subst: fv.

Lemma fv_subst2_lemma:
  forall s1 s1' s2 s2' s3 s,
    subset s1 (s1' -- s ++ s3) ->
    subset s2 (s2' -- s ++ s3) ->
    subset (s1 ++ s2) ((s1' ++ s2') -- s ++ s3).
Proof.
  unfold subset; repeat step || t_listutils || instantiate_any.
Qed.

Lemma fv_subst2:
  forall t l tag,
    subset (pfv (psubstitute t l tag) tag)
           (((pfv t tag) -- (support l)) ++ pfv_range l tag).
Proof.
  induction t;
    repeat step || apply fv_subst2_lemma;
    eauto 2 with sets;
    try solve [ unfold subset; repeat step || t_listutils; eauto with fv blookup ].
Qed.

Hint Resolve fv_subst2: fv.

Lemma fv_subst3:
  forall t x rep y tag,
    y <> x ->
    y ∈ pfv t tag ->
    y ∈ pfv (substitute t ((x,rep) :: nil)) tag.
Proof.
  induction t;
    repeat match goal with
    | H1: forall a b c d, _,
      H2: ?z ∈ pfv ?t ?tag |- _ =>
       solve [ eapply H1 in H2; steps; eauto ]
    | _ => step || t_listutils || unfold subset in *
    end.
Qed.

Hint Resolve fv_subst3: fv.

Lemma closed_mapping_lookup:
  forall l x t tag,
    pclosed_mapping l tag ->
    lookup Nat.eq_dec l x = Some t ->
    pfv t tag = nil.
Proof.
  induction l; steps; eauto.
Qed.

Hint Resolve closed_mapping_lookup: fv.

Lemma closed_mapping_range:
  forall l t tag,
    pclosed_mapping l tag ->
    t ∈ range l ->
    pfv t tag = nil.
Proof.
  induction l; steps; eauto.
Qed.

Hint Resolve closed_mapping_range: fv.

Lemma fv_nils:
  forall t l tag,
    pfv t tag = nil ->
    pclosed_mapping l tag ->
    pfv (psubstitute t l tag) tag = nil.
Proof.
  induction t;
    repeat match goal with
           | H: forall x, _ -> _ -> _, H1: _, H2: _ |- _ => pose proof (H _ H1 H2); clear H
           | H: _ = nil |- _ => rewrite H
           | _ => step || t_listutils
           end; eauto with fv.
Qed.

Hint Resolve fv_nils: fv.

Lemma closed_mapping_fv:
  forall l x tag,
    pclosed_mapping l tag ->
    x ∈ pfv_range l tag ->
    False.
Proof.
  induction l; repeat step || t_listutils; eauto.
Qed.

Lemma closed_mapping_fv2:
  forall l x y t tag,
    pclosed_mapping l tag ->
    lookup Nat.eq_dec l x = Some t ->
    y ∈ pfv t tag ->
    False.
Proof.
  induction l; repeat step || t_listutils; eauto.
Qed.

Lemma fv_nils2:
  forall t l tag,
    subset (pfv t tag) (support l) ->
    pclosed_mapping l tag ->
    pfv (psubstitute t l tag) tag = nil.
Proof.
  induction t;
    repeat match goal with
           | _ => step || t_listutils
           end;
      eauto 2 with fv;
      eauto 2 using closed_mapping_fv with exfalso;
      eauto 2 using closed_mapping_fv2 with exfalso;
      try solve [ rewrite (@singleton_subset nat) in *; repeat step || t_lookup ];
      try solve [ apply_any; eauto 2 with sets ].
Qed.

Hint Resolve fv_nils2: fv.
