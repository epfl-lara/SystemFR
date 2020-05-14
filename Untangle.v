Require Import Psatz.
Require Import PeanoNat.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.

Require Export SystemFR.ScalaDepSugar.
Require Export SystemFR.ReducibilitySubtype.
Require Export SystemFR.EquivalentContext.
Require Export SystemFR.TOpenTClose.
Require Export SystemFR.CloseLemmas.
Require Export SystemFR.SubstitutionErase.
Require Export SystemFR.TermListReducible.
Require Export SystemFR.ReducibilityOpenEquivalent.
Require Export SystemFR.FVLemmasClose.
Require Export SystemFR.WFLemmasClose.

Opaque reducible_values.

Parameter T_key: tree.
Parameter T_map: tree.
Hypothesis key_fv: forall tag, pfv T_key tag = nil.
Hypothesis map_fv: forall tag, pfv T_map tag = nil.
Hypothesis wf_key: wf T_key 0.
Hypothesis wf_map: wf T_map 0.
Hypothesis is_erased_type_key: is_erased_type T_key.
Hypothesis is_erased_type_map: is_erased_type T_map.

Definition T_trail: tree := T_prod T_key T_map.

Hint Resolve wf_key: wf.
Hint Resolve wf_map: wf.

Hint Resolve is_erased_type_key: erased.
Hint Resolve is_erased_type_map: erased.

Lemma wf_trail: wf T_trail 0.
Proof. steps; eauto with wf. Qed.

Hint Resolve wf_trail: wf.

Lemma is_erased_type_trail: is_erased_type T_trail.
Proof. steps; eauto with erased. Qed.

Hint Resolve is_erased_type_trail: erased.

Lemma substitute_map:
  forall l tag, psubstitute T_map l tag = T_map.
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

Definition app2 f a b := app (app f a) b.
Definition app3 f a b c := app (app (app f a) b) c.

(* tlookup: T_map -> T_key -> T_top *)
Parameter tlookup: tree -> tree -> tree.

(* concat: T_key -> T_key -> T_key *)
Parameter concat: tree -> tree -> tree.

(* append_key: T_key -> T_trail -> T_trail *)
Parameter append_key: tree -> tree -> tree.

Hypothesis append_key_trail:
  forall key trail,
    [ key : T_key ]v ->
    [ trail : T_trail ]v ->
    [ append_key key trail : T_trail ]v.

Hypothesis wf_append_key:
  forall k t1 t2,
    wf t1 k ->
    wf t2 k ->
    wf (append_key t1 t2) k.

Hypothesis psubstitute_append_key:
  forall t1 t2 l tag,
    psubstitute (append_key t1 t2) l tag =
    append_key (psubstitute t1 l tag) (psubstitute t2 l tag).

Hypothesis pfv_append_key:
  forall t1 t2 tag, pfv (append_key t1 t2) tag = pfv t1 tag ++ pfv t2 tag.

Hypothesis is_erased_term_append_key:
  forall t1 t2,
    is_erased_term t1 ->
    is_erased_term t2 ->
    is_erased_term (append_key t1 t2).

Hint Resolve wf_append_key: wf.
Hint Resolve is_erased_term_append_key: erased.

(* prefix: T_key -> T_key -> T_bool *)
Parameter prefix: tree -> tree -> tree.

Parameter empty_map: tree (* T_map *).
Hypothesis empty_map_type: [ empty_map : T_map ].

(* update: T_trail -> T_key -> T_trail -> T_trail *)
(* `update old_trail key trail` returns `old_trail` where `trail` is now rooted at `key` *)
Parameter update: tree -> tree -> tree -> tree.

Hypothesis update_type:
  forall old_trail key trail,
    [ old_trail : T_trail ]v ->
    [ key : T_key ]v ->
    [ trail : T_trail ]v ->
    [ update old_trail key trail : T_trail ]v.

Hypothesis wf_update:
  forall k t1 t2 t3,
    wf t1 k ->
    wf t2 k ->
    wf t3 k ->
    wf (update t1 t2 t3) k.

Hypothesis psubstitute_update:
  forall t1 t2 t3 l tag,
    psubstitute (update t1 t2 t3) l tag =
    update (psubstitute t1 l tag) (psubstitute t2 l tag) (psubstitute t3 l tag).

Hypothesis pfv_update:
  forall t1 t2 t3 tag,
    pfv (update t1 t2 t3) tag = pfv t1 tag ++ pfv t2 tag ++ pfv t3 tag.

Hypothesis is_erased_term_update:
  forall t1 t2 t3,
    is_erased_term t1 ->
    is_erased_term t2 ->
    is_erased_term t3 ->
    is_erased_term (update t1 t2 t3).

Hint Resolve wf_update: wf.
Hint Resolve is_erased_term_update: erased.

(*
(* `update`'s are commutative when keys are not prefixes of one another *)
Hypothesis update_spec:
  forall key1 fresh_key1 fresh_map1 key2 fresh_key2 fresh_map2 map,
    [ key1 : T_key ] ->
    [ key2 : T_key ] ->
    [ fresh_key1 : T_key ] ->
    [ fresh_key2 : T_key ] ->
    [ fresh_map1 : T_map ] ->
    [ fresh_map2 : T_map ] ->
    [ map : T_map ] ->
    [ prefix fresh_key1 fresh_key2 ≡ tfalse ] ->
    [ prefix fresh_key2 fresh_key1 ≡ tfalse ] ->
    [ update key1 fresh_key1 fresh_map1 (update key2 fresh_key2 fresh_map2 map) ≡
      update key2 fresh_key2 fresh_map2 (update key1 fresh_key1 fresh_map1 map) ].
*)

(*
Hypothesis update_spec3:
  forall key fresh_key fresh_map map key',
    [ prefix key key' ≡ tfalse ] ->
    [ tlookup map key' ≡ tlookup (update key fresh_key fresh_map map) key' ].
*)

(* Terms that take a map and a key `k`, and only lookup the map on keys greater or
   equal than `k` satisfy the following property, described by the type `T_tau` *)
Parameter T_tau: tree.

Hypothesis tau_fv: forall tag, pfv T_tau tag = nil.
Hypothesis wf_tau: wf T_tau 0.
Hypothesis is_erased_type_tau: is_erased_type T_tau.

Hint Resolve wf_tau: wf.
Hint Resolve is_erased_type_tau: erased.

Lemma substitute_tau:
  forall l tag, psubstitute T_tau l tag = T_tau.
Proof.
  intros; apply substitute_nothing5; eauto using tau_fv.
Qed.

Lemma tau_property:
  forall f map key trail,
    [ f : T_tau ] ->
    [ map : T_map ]v ->
    [ trail : T_trail ]v ->
    [ key : T_key ]v ->
    [ app f trail ≡ app f (update map key trail) ].
Admitted.

Ltac equivalent_refl :=
  match goal with
  | |- [ _ ≡ _ ] => apply equivalent_refl
  end.

(*
Lemma tau2_example:
  forall f1 f2 fresh_key1 fresh_key2 fresh_map1 fresh_map2 key1 key2,
    [ f1 : T_tau ] ->
    [ f2 : T_tau ] ->
    [ key1 : T_key ] ->
    [ key2 : T_key ] ->
    [ fresh_key1 : T_key ] ->
    [ fresh_key2 : T_key ] ->
    [ fresh_map1 : T_map ] ->
    [ fresh_map2 : T_map ] ->
    [ prefix fresh_key1 fresh_key2 ≡ tfalse ] ->
    [ prefix fresh_key2 fresh_key1 ≡ tfalse ] ->
    exists map,
      [ app2 f1 fresh_map1 fresh_key1 ≡ app2 f1 map key1 ] /\
      [ app2 f2 fresh_map2 fresh_key2 ≡ app2 f2 map key2 ].
Proof.
  intros.
  exists (update key1 fresh_key1 fresh_map1 (update key2 fresh_key2 fresh_map2 empty_map)); steps.
  - pose proof (tau_property _ key1 fresh_key1 fresh_map1
      (update key2 fresh_key2 fresh_map2 empty_map) H); auto.
  - pose proof (tau_property _ key2 fresh_key2 fresh_map2
      (update key1 fresh_key1 fresh_map1 empty_map) H0); auto.
    eapply equivalent_trans; eauto;
      repeat apply equivalent_app || apply update_spec || equivalent_refl;
      eauto 2 using reducible_erased with step_tactic;
      eauto 2 using reducible_wf with step_tactic;
      eauto 2 using reducible_fv with step_tactic;
      eauto using empty_map_type.
Qed.
*)

Fixpoint T_existss n T1 T2 :=
  match n with
  | 0 => T2
  | S n' => T_exists T1 (T_existss n' T1 T2)
  end.

Definition T_exists_vars xs T1 T2 :=
  T_existss (List.length xs) T1 (closes 0 T2 (rev xs)).

Lemma wfs_combine:
  forall l1 l2 k T,
    List.Forall (fun t => [ t : T ]) l2 ->
    wfs (List.combine l1 l2) k.
Proof.
  induction l1; steps; eauto 3 with wf step_tactic.
Qed.

Lemma wf_var:
  forall n k, wf (fvar n term_var) k.
Proof. steps. Qed.

Hint Resolve wf_var: wf.

Lemma wfs_combine2:
  forall xs f keys m,
    wf f 0 ->
    List.Forall (fun key => [ key : T_key ]) keys ->
    wfs (List.combine xs (List.map (fun key : tree => app f (pp key (fvar m term_var))) keys)) 0.
Proof.
  induction xs; destruct keys; steps; eauto with wf.
Qed.

Lemma wfs_combine3:
  forall xs f keys m,
    wf f 0 ->
    List.Forall (fun key => [ key : T_key ]) keys ->
    wfs (List.combine xs (List.map (fun key : tree => app f (append_key key (fvar m term_var))) keys)) 0.
Proof.
  induction xs; destruct keys; steps; eauto with wf.
Qed.

Lemma wfs_combine4:
  forall xs f ys,
    wf f 0 ->
    wfs (List.combine xs (List.map (fun y => app f (fvar y term_var)) ys)) 0.
Proof.
  induction xs; destruct ys; steps.
Qed.

Lemma wfs_combine5:
  forall l1 l2 k,
    List.Forall (fun t => wf t k) l2 ->
    wfs (List.combine l1 l2) k.
Proof.
  induction l1; steps.
Qed.

Lemma lookup_combine_map:
  forall eq_dec (xs: list nat) f l (t1 t2: tree) x,
    lookup eq_dec (List.combine xs l) x = Some t1 ->
    lookup eq_dec (List.combine xs (List.map f l)) x = Some t2 ->
    t2 = f t1.
Proof.
  induction xs; repeat step; eauto.
Qed.

Lemma lookup_combine_some_none:
  forall eq_dec (xs: list nat) (l1 l2: list tree) t x,
    List.length l1 = List.length l2 ->
    lookup eq_dec (List.combine xs l1) x = Some t ->
    lookup eq_dec (List.combine xs l2) x = None ->
    False.
Proof.
  induction xs; steps; eauto.
Qed.

Lemma psubstitute_texistss:
  forall n T1 T2 l tag,
    psubstitute (T_existss n T1 T2) l tag =
    T_existss n (psubstitute T1 l tag) (psubstitute T2 l tag).
Proof.
  induction n; repeat step || rewrite_any.
Qed.

Lemma substitute_closes:
  forall xs t l tag k,
    (forall x, x ∈ support l -> x ∈ xs -> False) ->
    pclosed_mapping l term_var ->
    psubstitute (closes k t xs) l tag = closes k (psubstitute t l tag) xs.
Proof.
  induction xs;
    repeat step || rewrite substitute_close by (steps; eauto);
    try solve [ rewrite_any; steps; eauto ].
Qed.

Lemma psubstitute_texists_vars:
  forall xs T1 T2 l tag,
    (forall x, x ∈ support l -> x ∈ xs -> False) ->
    pclosed_mapping l term_var ->
    psubstitute (T_exists_vars xs T1 T2) l tag =
    T_exists_vars xs (psubstitute T1 l tag) (psubstitute T2 l tag).
Proof.
  unfold T_exists_vars; intros; rewrite psubstitute_texistss; apply f_equal.
  rewrite substitute_closes; repeat step || rewrite <- in_rev in *; eauto.
Qed.

Lemma subst_subst:
  forall t l ts xs tag,
    (forall x, x ∈ pfv t tag -> x ∈ support l -> False) ->
    psubstitute (psubstitute t (List.combine xs ts) tag) l tag =
    psubstitute t (List.combine xs (List.map (fun t' => psubstitute t' l tag) ts)) tag.
Proof.
  induction t; repeat step || t_equality;
    eauto 4 using lookup_combine_some_none, List.map_length with exfalso;
    try solve [ rewrite_any; steps; eapply_any; repeat step || list_utils; eauto ];
    try solve [ eapply_anywhere lookup_combine_map; eauto ];
    try solve [ t_lookup; eauto with exfalso ].
Qed.

Lemma support_combine:
  forall A B (l1: list A) (l2: list B),
    List.length l1 = List.length l2 ->
    support (List.combine l1 l2) = l1.
Proof.
  induction l1; destruct l2; repeat step || apply f_equal.
Qed.

Lemma range_combine:
  forall A B (l1: list A) (l2: list B),
    List.length l1 = List.length l2 ->
    range (List.combine l1 l2) = l2.
Proof.
  induction l1; destruct l2; repeat step || apply f_equal.
Qed.

Lemma subst_subst2:
  forall t l ts xs tag,
    length ts = length xs ->
    (forall x, x ∈ xs -> x ∈ support l -> False) ->
    pclosed_mapping l tag ->
    psubstitute (psubstitute t (List.combine xs ts) tag) l tag =
    psubstitute (psubstitute t l tag)
                (List.combine xs (List.map (fun t' => psubstitute t' l tag) ts)) tag.
Proof.
  induction t; repeat step || t_equality;
    eauto 4 using lookup_combine_some_none, List.map_length with exfalso;
    try solve [ eapply_anywhere lookup_combine_map; eauto ];
    try solve [ rewrite substitute_nothing5; eauto with fv ].

  repeat step || t_lookup || rewrite support_combine in * by auto;
    eauto with exfalso.
Qed.

Lemma list_map_subst:
  forall l f t m v,
    (forall e, e ∈ l -> m ∈ fv e -> False) ->
    List.map (fun e => app f (pp (psubstitute e ((m, v) :: nil) term_var) t)) l =
    List.map (fun e => app f (pp e t)) l.
Proof.
  induction l; repeat step || t_substitutions || t_equality; eauto.
Qed.

Lemma list_map_subst2:
  forall l f m v,
    (forall e, e ∈ l -> m ∈ fv e -> False) ->
    List.map (fun key => app f (psubstitute (append_key key (fvar m term_var))
                                                     ((m, v) :: nil) term_var)) l =
    List.map (fun key => app f (append_key key v)) l.
Proof.
  induction l; repeat step || t_substitutions || rewrite psubstitute_append_key || t_equality; eauto.
Qed.

Fixpoint opens k t reps :=
  match reps with
  | nil => t
  | rep :: reps => opens (S k) (open k t rep) reps
  end.

Lemma is_erased_type_existss:
  forall n T1 T2,
    is_erased_type T1 ->
    is_erased_type T2 ->
    is_erased_type (T_existss n T1 T2).
Proof.
  induction n; repeat step || apply_any.
Qed.

Hint Resolve is_erased_type_existss.

Lemma open_existss:
  forall n T1 T2 k rep,
    wf T1 0 ->
    open k (T_existss n T1 T2) rep =
    T_existss n T1 (open (n + k) T2 rep).
Proof.
  induction n; steps; repeat step || t_equality || open_none || rewrite_any ||
                             rewrite PeanoNat.Nat.add_succ_r.
Qed.

Lemma open_close3:
  forall t k1 k2 x rep,
    fv rep = nil ->
    wf rep 0 ->
    k1 <> k2 ->
    open k1 (close k2 t x) rep =
    close k2 (open k1 t rep) x.
Proof.
  induction t; repeat step || t_equality || rewrite_any || rewrite close_nothing2 by auto.
Qed.

Lemma open_closes:
  forall xs x T v i,
    fv v = nil ->
    wf v 0 ->
    wf T 0 ->
    open (length xs + i) (closes i T (xs ++ x :: nil)) v =
    closes i (psubstitute T ((x, v) :: nil) term_var) xs.
Proof.
  induction xs; repeat step || rewrite open_close; eauto with wf.
  rewrite open_close3; steps; eauto with lia.
  rewrite <- PeanoNat.Nat.add_succ_r.
  rewrite_any; steps.
Qed.

Lemma open_closes_zero:
  forall xs x T v,
    fv v = nil ->
    wf v 0 ->
    wf T 0 ->
    open (length xs) (closes 0 T (xs ++ x :: nil)) v =
    closes 0 (psubstitute T ((x, v) :: nil) term_var) xs.
Proof.
  intros.
  rewrite <- (PeanoNat.Nat.add_0_r (length xs)); eauto using open_closes.
Qed.

Lemma reducible_exists_vars:
  forall xs ρ v vs T1 T2,
    wf T1 0 ->
    wf T2 0 ->
    is_erased_type T1 ->
    is_erased_type T2 ->
    List.Forall (fun v => [ ρ | v : T1 ]v) vs ->
    List.length xs = List.length vs ->
    valid_interpretation ρ ->
    (forall z v', z ∈ xs -> v' ∈ vs -> z ∈ fv v' -> False) ->
    [ ρ | v : psubstitute T2 (List.combine xs vs) term_var ]v ->
    [ ρ | v : T_exists_vars xs T1 T2 ]v.
Proof.
  induction xs; repeat step || t_substitutions.
  unshelve epose proof
    (IHxs ρ v l T1 (psubstitute T2 ((a,t) :: nil) term_var) _ _ _ _ _ _ _ _ _); steps; eauto;
    try solve [
      rewrite <- substitute_cons2; repeat step || rewrite support_combine in * by auto; eauto
    ];
    eauto 3 with erased step_tactic;
    eauto 3 with wf step_tactic.

  unfold T_exists_vars in *.
  simp_red_goal; steps; eauto 4 with erased; eauto using reducible_values_closed.
  exists t; repeat step || rewrite open_existss; eauto with erased fv wf.
  rewrite <- rev_length at 2.
  rewrite open_closes; steps; eauto with wf fv.
Qed.

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

Lemma functional_trail:
  forall A B a b (m: map A B),
    functional ((a, b) :: m) ->
    functional m.
Proof.
  unfold functional; steps; eauto.
Qed.

Ltac destruct_refinement :=
  match goal with
  | H: { _: _ | _ } |- _ => destruct H
  | H: { _: _ & _ } |- _ => destruct H
  end.

Definition get_or_else { A } (opt: option A) (a: A) :=
  match opt with
  | None => a
  | Some x => x
  end.

Lemma lookup_some_in:
  forall A (l: map nat A) x a,
    lookup Nat.eq_dec l x = Some a ->
    (x, a) ∈ l.
Proof.
  induction l; steps.
Qed.

Lemma in_map_in_support:
  forall A B (l: map A B) p,
    p ∈ l ->
    (fst p) ∈ support l.
Proof.
  induction l; steps.
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

Lemma decide_empty:
  forall T (l: list T), l = nil \/ ~ l = nil.
Proof.
  destruct l; steps; right; steps.
Qed.

Lemma lookup_support:
  forall A (l: map nat A) x,
   x ∈ support l ->
   exists a, lookup Nat.eq_dec l x = Some a.
Proof.
  induction l; repeat step; eauto.
Qed.

Lemma lookup_support2:
  forall A (l1 l2: map nat A) x,
   (forall s t, lookup Nat.eq_dec l1 s = Some t <-> lookup Nat.eq_dec l2 s = Some t) ->
   x ∈ support l1 ->
   x ∈ support l2.
Proof.
  intros.
  apply_anywhere lookup_support; repeat step.
  pose proof (H x a); repeat step || t_lookup.
Qed.

Lemma equivalent_subst_snoc:
  forall l1 l2 a b,
    equivalent_subst l1 l2 ->
    equivalent_subst
      (l1 ++ (a, b) :: nil)
      (l2 ++ (a, get_or_else (lookup Nat.eq_dec l2 a) b) :: nil).
Proof.
  unfold equivalent_subst, get_or_else;
    repeat step || list_utils || t_lookup || t_lookupor ||
           (rewrite obvious_lookup in * by auto);
    try solve [ apply lookupWeaken; steps; apply_any; steps ];
    try solve [ unshelve epose proof (H s _); eauto; steps ].

  - rewrite obvious_lookup in *; repeat step || t_lookup.
    + apply eq_sym in H8; unshelve epose proof (H s b); repeat step || t_lookup.
    + clear_marked. rewrite H8 in H0.
      unshelve epose proof (H s t); repeat step || t_lookup.
  - apply obvious_lookup; repeat step; eauto using lookup_support2.
Qed.

Lemma support_nil:
  forall A B (l: map A B), support l = nil <-> l = nil.
Proof.
  destruct l; steps.
Qed.

Lemma forall_inst:
  forall A (P: A -> Prop) l x,
    x ∈ l ->
    Forall P l ->
    P x.
Proof.
  repeat step || rewrite Forall_forall in *.
Qed.

Ltac forall_inst :=
  match goal with
  | H1: ?x ∈ ?l, H2: Forall ?P ?l |- _ =>
    poseNew (Mark (x, H2) "forall_inst");
    pose proof (forall_inst _ _ _ _ H1 H2)
  end.

Lemma range_append:
  forall A B (l1 l2: map A B),
    range (l1 ++ l2) = range l1 ++ range l2.
Proof.
  induction l1; repeat step.
Qed.

Lemma recombine:
  forall A B (m: map A B),
    combine (support m) (range m) = m.
Proof.
  induction m; steps.
Qed.

Lemma length_support:
  forall A B (l: map A B), length (support l) = length l.
Proof.
  induction l; steps.
Qed.

Lemma length_range:
  forall A B (l: map A B), length (range l) = length l.
Proof.
  induction l; steps.
Qed.

Ltac list_utils2 :=
  rewrite map_length in * || rewrite support_nil in * || rewrite in_map_iff in * ||
  rewrite range_append in * || rewrite range_combine in * ||
  rewrite List.map_map in * || rewrite support_combine in * ||
  rewrite length_support in * || rewrite length_range in * ||
  rewrite length_zero_iff_nil in * ||
  rewrite recombine in * ||
  forall_inst.

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

Lemma reducible_exists_vars2_helper:
  forall xs ρ v T1 T2,
    wf T1 0 ->
    wf T2 0 ->
    is_erased_type T1 ->
    is_erased_type T2 ->
    valid_interpretation ρ ->
    [ ρ | v : T_exists_vars xs T1 T2 ]v ->
    (exists vs,
      List.Forall (fun v => [ ρ | v : T1 ]v) vs /\
      length vs = length xs /\
      [ ρ | v : psubstitute T2 (combine xs vs) term_var ]v).
Proof.
  unfold functional; induction xs; repeat step || t_substitutions || simp_red_top_level_hyp;
    eauto 2 with step_tactic.

  rewrite open_existss in *; eauto with wf.
  rewrite <- rev_length in * at 2.
  rewrite open_closes in *; eauto with wf fv.
  rewrite rev_length in *.

  unshelve epose proof (IHxs _ _ _ _ _ _ _ _ _ H9); steps;
    eauto 2 with wf step_tactic;
    eauto 2 with erased step_tactic.

  exists (a0 :: vs); steps; eauto.
  rewrite substitute_cons2; repeat step || (erewrite reducible_val_fv in * by eauto).
Qed.

Lemma reducible_exists_vars2:
  forall xs ρ v T1 T2,
    wf T1 0 ->
    wf T2 0 ->
    is_erased_type T1 ->
    is_erased_type T2 ->
    valid_interpretation ρ ->
    [ ρ | v : T_exists_vars xs T1 T2 ]v ->
    (exists vs,
      List.Forall (fun v => [ ρ | v : T1 ]v) vs /\
      functional (combine xs vs) /\
      length vs = length xs /\
      [ ρ | v : psubstitute T2 (combine xs vs) term_var ]v).
Proof.
  intros.
  apply_anywhere reducible_exists_vars2_helper; steps.
  pose proof (functionalize (combine xs vs)); repeat step || list_utils2.
  exists (range l'); repeat step || list_utils || list_utils2 || rewrite Forall_forall in *.
  erewrite subst_permutation in * |-; eauto.
Qed.

Definition apps fs ts := List.map (fun p => app (fst p) (snd p)) (combine fs ts).

Lemma combine_equivalent_wfs1:
  forall ts1 ts2 xs,
    length xs = length ts1 ->
    length xs = length ts2 ->
    (forall t1 t2, (t1, t2) ∈ combine ts1 ts2 -> [ t1 ≡ t2 ]) ->
    wfs (combine xs ts1) 0.
Proof.
  induction ts1; destruct ts2; destruct xs;
    repeat step || list_utils || list_utils2; eauto.
  unshelve epose proof (H1 a t _); steps; t_closer.
Qed.

Lemma combine_equivalent_wfs2:
  forall ts1 ts2 xs,
    length xs = length ts1 ->
    length xs = length ts2 ->
    (forall t1 t2, (t1, t2) ∈ combine ts1 ts2 -> [ t1 ≡ t2 ]) ->
    wfs (combine xs ts2) 0.
Proof.
  induction ts1; destruct ts2; destruct xs;
    repeat step || list_utils || list_utils2; eauto.
  unshelve epose proof (H1 a t _); steps; t_closer.
Qed.

Lemma combine_wfs3:
  forall xs ts,
    (forall x t, (x, t) ∈ combine xs ts -> wf t 0) ->
    wfs (combine xs ts) 0.
Proof.
  induction xs; destruct ts;
    repeat step || list_utils || list_utils2; eauto.
Qed.

Lemma combine_wfs4:
  forall xs ts,
    (forall t, t ∈ ts -> wf t 0) ->
    wfs (combine xs ts) 0.
Proof.
  induction xs; destruct ts;
    repeat step || list_utils || list_utils2; eauto.
Qed.

Lemma combine_wfs5:
  forall xs ts,
    Forall (fun v => wf v 0) ts ->
    wfs (combine xs ts) 0.
Proof.
  intros; apply combine_wfs4; apply Forall_forall; auto.
Qed.

Lemma combine_equivalent_is_erased_term:
  forall xs ts,
    Forall is_erased_term ts ->
    erased_terms (combine xs ts).
Proof.
  induction xs; destruct ts;
    repeat step || list_utils || list_utils2; eauto.
Qed.

Lemma combine_closed_mapping:
  forall xs ts tag,
    Forall (fun t => pfv t tag = nil) ts ->
    pclosed_mapping (combine xs ts) tag.
Proof.
  induction xs; destruct ts;
    repeat step || list_utils || list_utils2; eauto.
Qed.

Lemma pfv_in_subst2:
  forall T (l : list (nat * tree)) tag x,
    pclosed_mapping l tag ->
    x ∈ pfv (psubstitute T l tag) tag ->
    ~x ∈ support l.
Proof.
  intros.
  epose proof (fv_subst2 _ _ _ x H0);
    repeat step || list_utils;
    eauto using closed_mapping_fv.
Qed.

Lemma reducibility_equivalent_substititions_helper:
  forall xs T ρ v ts1 ts2,
    [ ρ | v : psubstitute T (combine xs ts1) term_var ]v ->
    valid_interpretation ρ ->
    length ts1 = length xs ->
    length ts2 = length xs ->
    is_erased_type T ->
    wf T 0 ->
    (forall t1 t2, (t1, t2) ∈ combine ts1 ts2 -> [ t1 ≡ t2 ]) ->
    Forall (fun v => wf v 0) ts1 ->
    Forall (fun v => wf v 0) ts2 ->
    Forall (fun v => pfv v term_var = nil) ts1 ->
    Forall (fun v => pfv v term_var = nil) ts2 ->
    Forall is_erased_term ts1 ->
    Forall is_erased_term ts2 ->
    (forall x, x ∈ fv T -> x ∈ xs) ->
    [ ρ | v : psubstitute T (combine xs ts2) term_var ]v.
Proof.
  induction xs; repeat step || t_substitutions.
  rewrite <- (open_close2 T a 0) by auto.
  rewrite substitute_open3; steps;
    try solve [ apply combine_equivalent_wfs4; repeat step || rewrite Forall_forall in *; eauto ];
    try solve [ apply_anywhere fv_close; steps ].

  eapply reducibility_open_equivalent; eauto;
    repeat step || apply subst_erased_type || apply wf_subst || apply wf_close;
    eauto with erased wf fv;
    eauto using combine_equivalent_is_erased_term.

  - rewrite substitute_open2;
      repeat step || list_utils || list_utils2 ||
             rewrite open_close by auto;
      eauto using combine_wfs5.
    apply IHxs with l0;
      repeat step || apply subst_erased_type || apply wf_subst || t_pfv_in_subst;
      eauto.
    + rewrite <- substitute_cons; steps.
    + clear_marked; apply pfv_in_subst2 in H6; steps.
      instantiate_any; steps.
  - apply wfs_monotone2.
    apply combine_wfs4; repeat step || rewrite Forall_forall in *; eauto with wf.
  - apply fv_nils2; repeat step || list_utils2 || unfold subset || apply_anywhere fv_close;
      eauto using combine_closed_mapping.
    apply_anywhere H12; steps.
  - apply combine_wfs5; auto.
Qed.

Lemma find_snd:
  forall A B a (l1: list A) (l2: list B),
    a ∈ l1 ->
    length l1 = length l2 ->
    exists b, (a, b) ∈ combine l1 l2.
Proof.
  induction l1; repeat step || instantiate_any; eauto.
  pose proof (IHl1 _ H1 H); steps; eauto.
Qed.

Ltac find_snd :=
  match goal with
  | H1: context[combine ?l1 ?l2],
    H2: ?x ∈ ?l1 |- _ =>
    poseNew (Mark (x, l1, l2) "first_snd");
    unshelve epose proof (find_snd _ _ _ l1 l2 H2 _)
  end.

Lemma find_fst:
  forall A B b (l1: list A) (l2: list B),
    b ∈ l2 ->
    length l1 = length l2 ->
    exists a, (a, b) ∈ combine l1 l2.
Proof.
  induction l1; repeat step || instantiate_any; eauto.
  apply_anywhere eq_sym; list_utils2; steps.
Qed.

Ltac find_fst :=
  match goal with
  | H1: context[combine ?l1 ?l2],
    H2: ?x ∈ ?l2 |- _ =>
    poseNew (Mark (x, l1, l2) "first_fst");
    unshelve epose proof (find_fst _ _ _ l1 l2 H2 _)
  end.

Lemma reducibility_equivalent_substititions:
  forall xs T ρ v ts1 ts2,
    [ ρ | v : psubstitute T (combine xs ts1) term_var ]v ->
    valid_interpretation ρ ->
    length ts1 = length xs ->
    length ts2 = length xs ->
    is_erased_type T ->
    wf T 0 ->
    (forall t1 t2, (t1, t2) ∈ combine ts1 ts2 -> [ t1 ≡ t2 ]) ->
    (forall x, x ∈ fv T -> x ∈ xs) ->
    [ ρ | v : psubstitute T (combine xs ts2) term_var ]v.
Proof.
  intros; eapply reducibility_equivalent_substititions_helper; try eassumption;
    repeat step || rewrite Forall_forall || find_fst || find_snd;
    eauto using combine_equivalent_wfs1;
    try solve [ instantiate_any; t_closer ].
Qed.

Lemma erased_terms_combine:
  forall xs f ys,
    is_erased_term f ->
    erased_terms (combine xs (List.map (fun y : nat => app f (fvar y term_var)) ys)).
Proof.
  induction xs; destruct ys; steps.
Qed.

Lemma wfs_combine6:
  forall xs fs keys m,
    Forall (fun key => [ key : T_key ]v) keys ->
    Forall (fun t => wf t 0) fs ->
    length keys = length xs ->
    length fs = length xs ->
    wfs
      (combine xs
         (List.map (fun p => app (fst p) (snd p))
            (combine fs (List.map (fun key => append_key key (fvar m term_var)) keys)))) 0.
Proof.
  induction xs; destruct fs; destruct keys;
    repeat step || apply wf_append_key;
    eauto using reducible_val_wf with step_tactic.
Qed.

Lemma wfs_combine7:
  forall xs fs keys m,
    Forall (fun key => [ key : T_key ]v) keys ->
    Forall (fun t => wf t 0) fs ->
    length keys = length xs ->
    length fs = length xs ->
    wfs (combine xs (apps fs (List.map (fun key : tree => append_key key (fvar m term_var)) keys))) 0.
Proof.
  induction xs; destruct fs; destruct keys;
    repeat step || apply wf_append_key;
    eauto using reducible_val_wf with step_tactic.
Qed.

Lemma list_map_apps:
  forall fs ts l tag,
    length fs = length ts ->
    List.map (fun t => psubstitute t l tag) (apps fs ts) =
    apps (List.map (fun t => psubstitute t l tag) fs) (List.map (fun t => psubstitute t l tag) ts).
Proof.
  induction fs; destruct ts; repeat step || t_equality; eauto.
Qed.

Lemma apps_cons:
  forall f fs t ts,
    apps (f :: fs) (t :: ts) = app f t :: apps fs ts.
Proof.
  steps.
Qed.

Lemma length_apps_cons:
  forall f fs t ts,
    length (apps (f :: fs) (t :: ts)) = 1 + length (apps fs ts).
Proof.
  repeat step.
Qed.

Opaque apps.

Lemma length_apps:
  forall fs ts,
    length fs = length ts ->
    length (apps fs ts) = length fs.
Proof.
  induction fs; destruct ts; try solve [
    repeat step || rewrite length_apps_cons; try lia
  ].
  intros.
  rewrite length_apps_cons; cbn; apply f_equal; apply_any; steps.
Qed.

Lemma substitute_nothing6:
  forall fs m v,
    (forall f, f ∈ fs -> m ∈ fv f -> False) ->
    List.map (fun t => psubstitute t ((m, v) :: nil) term_var) fs = fs.
Proof.
  induction fs; repeat step || t_substitutions || apply f_equal; eauto.
Qed.

Lemma list_map_subst3:
  forall keys m v,
    Forall (fun key => [ key : T_key ]v) keys ->
    List.map (fun x => psubstitute (append_key x (fvar m term_var)) ((m, v) :: nil) term_var) keys =
    List.map (fun x => append_key x v) keys.
Proof.
  induction keys;
    repeat step || rewrite psubstitute_append_key || t_substitutions.
  rewrite substitute_nothing5; eauto using reducible_val_fv with step_tactic.
  apply f_equal; eauto.
Qed.

Lemma wfs_combine8:
  forall xs fs ys,
    length fs = length xs ->
    length ys = length xs ->
    Forall (fun f => wf f 0) fs ->
    wfs (combine xs (apps fs (List.map (fun y : nat => fvar y term_var) ys))) 0.
Proof.
  induction xs; destruct fs; destruct ys; intros;
    repeat rewrite apps_cons in * || step.
Qed.

Lemma erased_terms_combine2:
  forall xs fs ys,
    length fs = length xs ->
    length ys = length xs ->
    Forall is_erased_term fs ->
    erased_terms (combine xs (apps fs (List.map (fun y => fvar y term_var) ys))).
Proof.
  induction xs; destruct fs; destruct ys; intros;
    repeat rewrite apps_cons in * || step.
Qed.

Lemma erased_terms_combine3:
  forall xs keys fs m,
    length fs = length xs ->
    length keys = length xs ->
    Forall is_erased_term fs ->
    Forall (fun key => [ key : T_key ]v) keys ->
    erased_terms (combine xs (apps fs (List.map (fun key => append_key key (fvar m term_var)) keys))).
Proof.
  induction xs; destruct keys; destruct fs; intros;
    repeat rewrite apps_cons in * || step || apply is_erased_term_append_key;
    try solve [ eapply reducible_values_erased; eauto; steps ].
Qed.

Lemma forall_append_key_trails:
  forall keys trail,
    Forall (fun key => [ key : T_key ]v) keys ->
    [ trail : T_trail ]v ->
    Forall (fun t => [ t : T_trail ]v) (List.map (fun key : tree => append_key key trail) keys).
Proof.
  induction keys; repeat step || constructor; eauto using append_key_trail.
Qed.

Lemma list_map_subst4:
  forall keys a l,
    Forall (fun key : tree => [key : T_key ]v) keys ->
    [ a : T_trail ]v ->
    List.map (fun x => psubstitute (append_key x a) l term_var) keys =
    List.map (fun x => append_key x a) keys.
Proof.
  induction keys; repeat step || t_substitutions || rewrite psubstitute_append_key.
  repeat rewrite substitute_nothing5 by eauto using reducible_val_fv with step_tactic.
  apply f_equal; eauto.
Qed.

Lemma list_map_subst5:
  forall ys l,
    (forall y, y ∈ ys -> y ∈ support l -> False) ->
    List.map (fun x =>
       match lookup PeanoNat.Nat.eq_dec l x with
       | Some e => e
       | None => fvar x term_var
       end) ys =
    List.map (fun x => fvar x term_var) ys.
Proof.
  induction ys; repeat step || t_lookup || apply f_equal; eauto with exfalso.
Qed.

Lemma list_map_subst6:
  forall fs l ys zs,
    (forall f, f ∈ fs -> subset (fv f) (support l)) ->
    pclosed_mapping l term_var ->
    List.map
      (fun f =>
         psubstitute (psubstitute f l term_var)
         (combine ys zs) term_var)
      fs =
    List.map
      (fun f => psubstitute f l term_var)
      fs.
Proof.
  induction fs; repeat step; eauto.
  rewrite substitute_nothing5; eauto with fv.
  apply f_equal; eauto.
Qed.

Lemma list_map_change_list:
  forall A B C (l1: list A) (l2: list B) (f: A -> C) (g: B -> C),
    (forall a b, (a, b) ∈ combine l1 l2 -> f a = g b) ->
    length l1 = length l2 ->
    List.map f l1 = List.map g l2.
Proof.
  induction l1; destruct l2; repeat step || f_equal.
Qed.

Lemma lookup_combine:
  forall A B (l1: list nat) (l2: list A) x a (f: A -> B),
    length l1 = length l2 ->
    functional (combine l1 l2) ->
    (x, a) ∈ combine l1 l2 ->
    lookup Nat.eq_dec (combine l1 (List.map f l2)) x = Some (f a).
Proof.
  induction l1; destruct l2; repeat step || step_inversion NoDup;
    eauto using in_combine_l with exfalso;
    try solve [ eapply_anywhere functional_head; eauto; steps ];
    eauto using functional_trail.
Qed.

Lemma list_map_subst7:
  forall ys keys a,
    length ys = length keys ->
    functional (combine ys keys) ->
    List.map
      (fun y =>
         match
           lookup PeanoNat.Nat.eq_dec
             (combine ys (List.map (fun key => append_key key a) keys)) y
         with
         | Some e1 => e1
         | None => fvar y term_var
         end) ys =
    List.map (fun key => append_key key a) keys.
Proof.
  intros; apply list_map_change_list; repeat step || step_inversion NoDup;
    eauto using in_combine_l with exfalso;
    try solve [ erewrite_anywhere lookup_combine; eauto; steps ].
Qed.

Lemma lookup_combine2:
  forall A B (l1: list nat) (l2: list A) x a (f: A -> B),
    length l1 = length l2 ->
    functional (combine l1 l2) ->
    (x, a) ∈ combine l1 l2 ->
    lookup Nat.eq_dec (combine l1 l2) x = Some a.
Proof.
  induction l1; destruct l2; repeat step || step_inversion NoDup;
    eauto using in_combine_l with exfalso;
    try solve [ eapply_anywhere functional_head; eauto; steps ];
    eauto using functional_trail.
Qed.

Lemma list_map_subst8:
  forall ys vs l,
    length vs = length ys ->
    functional (combine ys vs) ->
    (forall y, y ∈ ys -> y ∈ support l -> False) ->
    List.map
      (fun x =>
       psubstitute
         match lookup Nat.eq_dec l x with
         | Some e => e
         | None => fvar x term_var
         end (combine ys vs) term_var) ys = vs.
Proof.
  intros.
  rewrite <- map_id.
  apply list_map_change_list;
    repeat step || step_inversion NoDup || t_lookup || list_utils2;
    eauto using in_combine_l with exfalso;
    try solve [ erewrite_anywhere lookup_combine2; eauto; steps ].
Qed.

(* empty_trail: T_trail *)
Parameter empty_trail: tree.
Hypothesis empty_trail_type: [ empty_trail : T_trail ]v.

Definition global_trail keys vs :=
  fold_left (fun acc p => update acc (fst p) (snd p)) (combine keys vs) empty_trail.

Lemma is_erased_term_global_trail':
  forall keys vs acc0,
    is_erased_term acc0 ->
    Forall is_erased_term keys ->
    Forall is_erased_term vs ->
    is_erased_term (fold_left (fun acc p => update acc (fst p) (snd p)) (combine keys vs) acc0).
Proof.
  induction keys; repeat step || apply_any; eauto with erased.
Qed.

Lemma wfs_global_trail':
  forall keys vs acc0,
    wf acc0 0 ->
    Forall (fun v => wf v 0) keys ->
    Forall (fun v => wf v 0) vs ->
    wf (fold_left (fun acc p => update acc (fst p) (snd p)) (combine keys vs) acc0) 0.
Proof.
  induction keys; repeat step || apply_any; eauto with wf.
Qed.

Lemma fvs_global_trail':
  forall keys vs acc0 tag,
    pfv acc0 tag = nil ->
    Forall (fun v => pfv v tag = nil) keys ->
    Forall (fun v => pfv v tag = nil) vs ->
    pfv (fold_left (fun acc p => update acc (fst p) (snd p)) (combine keys vs) acc0) tag = nil.
Proof.
  induction keys; repeat step || apply_any || rewrite pfv_update || list_utils.
Qed.

Lemma global_trail_is_trail':
  forall keys vs acc0,
    [ acc0 : T_trail ]v  ->
    Forall (fun key => [ key : T_key ]v) keys ->
    Forall (fun trail => [ trail : T_trail ]v) vs ->
    [ fold_left (fun acc p => update acc (fst p) (snd p)) (combine keys vs) acc0 : T_trail ]v.
Proof.
  induction keys; repeat step || apply_any; eauto using update_type.
Qed.

Lemma typed_erased_terms:
  forall ρ T l,
    valid_interpretation ρ ->
    Forall (fun v => [ ρ | v : T ]v) l ->
    Forall is_erased_term l.
Proof.
  induction l; repeat step || constructor;
    try solve [ eapply reducible_values_erased; eauto using empty_trail_type; steps ].
Qed.

Lemma typed_erased_terms':
  forall T l,
    Forall (fun v => [ v : T ]v) l ->
    Forall is_erased_term l.
Proof.
  intros; eapply typed_erased_terms; eauto; steps.
Qed.

Lemma typed_wfs:
  forall ρ T l,
    valid_interpretation ρ ->
    Forall (fun v => [ ρ | v : T ]v) l ->
    Forall (fun v => wf v 0) l.
Proof.
  induction l; repeat step || constructor;
    try solve [ eapply reducible_val_wf; eauto using empty_trail_type; steps ].
Qed.

Lemma typed_wfs':
  forall T l,
    Forall (fun v => [ v : T ]v) l ->
    Forall (fun v => wf v 0) l.
Proof.
  intros; eapply typed_wfs; eauto; steps.
Qed.

Lemma typed_fv:
  forall ρ T l tag,
    valid_interpretation ρ ->
    Forall (fun v => [ ρ | v : T ]v) l ->
    Forall (fun v => pfv v tag = nil) l.
Proof.
  induction l; repeat step || constructor;
    try solve [ eapply reducible_val_fv; eauto using empty_trail_type; steps ].
Qed.

Lemma typed_fv':
  forall T l tag,
    Forall (fun v => [ v : T ]v) l ->
    Forall (fun v => pfv v tag = nil) l.
Proof.
  intros; eapply typed_fv; eauto; steps.
Qed.

Lemma is_erased_term_global_trail:
  forall keys vs,
    Forall is_erased_term keys ->
    Forall is_erased_term vs ->
    is_erased_term (global_trail keys vs).
Proof.
  intros; apply is_erased_term_global_trail'; steps;
    try solve [ eapply reducible_values_erased; eauto using empty_trail_type; steps ].
Qed.

Lemma wfs_global_trail:
  forall keys vs,
    Forall (fun v => wf v 0) keys ->
    Forall (fun v => wf v 0) vs ->
    wf (global_trail keys vs) 0.
Proof.
  intros; apply wfs_global_trail'; steps;
    try solve [ eapply reducible_val_wf; eauto using empty_trail_type; steps ].
Qed.

Lemma fvs_global_trail:
  forall keys vs tag,
    Forall (fun v => pfv v tag = nil) keys ->
    Forall (fun v => pfv v tag = nil) vs ->
    pfv (global_trail keys vs) tag = nil.
Proof.
  intros; apply fvs_global_trail'; steps;
    try solve [ eapply reducible_val_fv; eauto using empty_trail_type; steps ].
Qed.

Lemma fvs_global_trail2:
  forall keys vs tag x,
    Forall (fun key => [ key : T_key ]v) keys ->
    Forall (fun trail => [ trail : T_trail ]v) vs ->
    x ∈ pfv (global_trail keys vs) tag ->
    False.
Proof.
  intros; rewrite fvs_global_trail in *; steps; eauto using typed_fv'.
Qed.

Lemma global_trail_is_trail:
  forall keys vs,
    Forall (fun key => [ key : T_key ]v) keys ->
    Forall (fun trail => [ trail : T_trail ]v) vs ->
    [ global_trail keys vs : T_trail ]v.
Proof.
  intros; apply global_trail_is_trail'; steps; eauto using empty_trail_type.
Qed.


Definition good_trail (trail: tree) (key: tree) (trail': tree) : Prop :=
  forall f,
    [ f: T_tau ] ->
    [ app f trail' ≡ app f (append_key key trail) ].

Lemma good_trail_equivalent:
  forall key trail trail' f,
    good_trail trail key trail' ->
    [ f : T_tau ] ->
    [ app f trail' ≡ app f (append_key key trail) ].
Proof.
  unfold good_trail; steps.
Qed.

Lemma global_trail_good_trail':
  forall keys vs key v acc,
    length keys = length vs ->
    (key, v) ∈ combine keys vs ->
    good_trail (fold_left (fun acc p => update acc (fst p) (snd p)) (combine keys vs) acc) key v.
Proof.
  induction keys; destruct vs; repeat step.
  
Admitted.

Lemma global_trail_good_trail:
  forall keys vs key v,
    length keys = length vs ->
    (key, v) ∈ combine keys vs ->
    good_trail (global_trail keys vs) key v.
Proof.
  intros; apply global_trail_good_trail'; steps.
Qed.

Opaque global_trail.

(* Using the tau property, we can untangle *)
Inductive untangle: context -> tree -> tree -> Prop :=
| UntangleFreshen:
    forall Γ T T' template xs ys fs keys m,
      List.NoDup (xs ++ ys) ->
      T  = substitute template
        (List.combine xs (apps fs (List.map (fun key => pp key (fvar m term_var)) keys))) ->
      T' = substitute template
        (List.combine xs (apps fs (List.map (fun y => fvar y term_var) ys))) ->
      untangle Γ
               (T_exists T_trail (close 0 T m))
               (T_exists_vars ys T_trail T')

| UntangleRefl: forall Γ T, untangle Γ T T
.

Lemma in_combine_equivalent:
  forall fs keys vs t1 l t2 trail,
    length fs = length vs ->
    length fs = length keys ->
    (forall f, f ∈ fs -> [ psubstitute f l term_var : T_tau ]) ->
    (forall key v, (key, v) ∈ combine keys vs -> good_trail trail key v) ->
    (t1, t2) ∈
      combine
        (apps (List.map (fun f => psubstitute f l term_var) fs) vs)
        (apps (List.map (fun f => psubstitute f l term_var) fs)
          (List.map (fun x => append_key x trail) keys)) ->
    [t1 ≡ t2].
Proof.
  induction fs; destruct keys; destruct vs;
    repeat rewrite apps_cons in * || step;
    try solve [ apply IHfs with keys vs l trail; steps ].

  unshelve epose proof (H1 a _); steps.
  unshelve epose proof (H2 t t0 _); steps;
    eauto using good_trail_equivalent.
Qed.

Lemma in_combine_equivalent':
  forall fs keys vs t1 l t2,
    length fs = length vs ->
    length fs = length keys ->
    (forall f, f ∈ fs -> [ psubstitute f l term_var : T_tau ]) ->
    (t1, t2) ∈
      combine
        (apps (List.map (fun f => psubstitute f l term_var) fs) vs)
        (apps (List.map (fun f => psubstitute f l term_var) fs)
          (List.map (fun x => append_key x (global_trail keys vs)) keys)) ->
    [t1 ≡ t2].
Proof.
  intros; apply in_combine_equivalent with fs keys vs l (global_trail keys vs); steps;
    eauto using global_trail_good_trail.
Qed.

Lemma untangle_freshen:
  forall Γ fs template xs ys keys m,
    List.NoDup (xs ++ ys) ->
    is_erased_type template ->
    wf template 0 ->
    Forall (fun key => [ key : T_key ]v) keys ->
    Forall (fun f => wf f 0) fs ->
    Forall is_erased_term fs ->
    functional (combine ys keys) ->
    ~ m ∈ fv template ->
    length keys = length xs ->
    length fs = length xs ->
    length ys = length xs ->
    (forall f, f ∈ fs -> m ∈ fv f -> False) ->
    (forall y, y ∈ ys -> y ∈ support Γ -> False) ->
    (forall y, y ∈ ys -> y ∈ fv template -> False) ->
    (forall x, x ∈ xs -> x ∈ support Γ -> False) ->
    (forall f, f ∈ fs -> subset (fv f) (support Γ)) ->
    (forall f, f ∈ fs -> [ Γ ⊨ f : T_tau ]) ->
    (forall x, x ∈ fv template -> x ∈ xs \/ x ∈ support Γ) ->
    [Γ
    ⊨ T_exists T_trail
        (close 0
           (psubstitute template
              (List.combine xs
                (apps fs (List.map (fun key => append_key key (fvar m term_var)) keys))) term_var)
            m) =
    T_exists_vars ys T_trail
      (psubstitute template
                   (List.combine xs (apps fs (List.map (fun y => fvar y term_var) ys)))
                   term_var) ].
Proof.
  unfold open_equivalent_types, equivalent_types; intros;
    repeat step || list_utils || list_utils2 || simp_red_top_level_hyp || rewrite substitute_trail in *.

  - rewrite substitute_open2 in *; repeat step || list_utils; eauto with wf.
    rewrite open_close in *; steps; eauto using wfs_combine7 with wf.
    rewrite (subst_subst template) in * |-;
      repeat step || t_substitutions ||
             (rewrite substitute_nothing6 in * by auto) ||
             (rewrite list_map_apps in * by repeat step || list_utils2) ||
             rewrite List.map_map in *.
    rewrite list_map_subst3 in *; steps; eauto.
    rewrite psubstitute_texists_vars;
      repeat step || rewrite substitute_trail || rewrite <- satisfies_same_support in *;
      eauto with fv;
      eauto using var_in_support.
    apply reducible_exists_vars with (List.map (fun key => append_key key a) keys);
      repeat step || apply wf_subst || apply subst_erased_type || list_utils || list_utils2 ||
             forall_inst || (erewrite reducible_val_fv in * by eauto) ||
             apply wfs_combine8 || apply erased_terms_combine2 || rewrite pfv_append_key in *;
      eauto 3 with wf step_tactic;
      eauto with erased;
      try solve [ eapply satisfies_erased_terms; eauto; steps ];
      eauto 2 using forall_append_key_trails.

    rewrite (subst_subst2 template) in * |-;
      repeat step || list_utils2 || rewrite list_map_subst4 in * ||
             (rewrite length_apps by (repeat step || list_utils2)) ||
             (rewrite list_map_apps in * by repeat step || list_utils2);
      eauto using var_in_support;
      eauto with fv.

    rewrite (subst_subst2 template);
      repeat step || t_substitutions || list_utils2 ||
             (rewrite length_apps by (repeat step || list_utils2)) ||
             (rewrite substitute_nothing6 in * by auto) ||
             (rewrite list_map_apps in * by repeat step || list_utils2) ||
             (rewrite list_map_subst5 by (steps; eauto using var_in_support));
      eauto using var_in_support;
      eauto with fv.

    rewrite (subst_subst (psubstitute template l term_var));
      repeat step || t_substitutions || list_utils2 ||
             (rewrite length_apps by (repeat step || list_utils2)) ||
             (rewrite substitute_nothing6 in * by auto) ||
             (rewrite list_map_apps in * by repeat step || list_utils2);
      eauto using var_in_support;
      eauto with fv;
      try solve [ t_pfv_in_subst; eauto with fv ].

    rewrite list_map_subst6; repeat step || erewrite satisfies_same_support in * by eauto;
      eauto with fv.
    rewrite list_map_subst7; repeat step || erewrite satisfies_same_support in * by eauto;
      eauto with fv.

  - rewrite psubstitute_texists_vars in *;
      repeat step || rewrite substitute_trail in * || rewrite <- satisfies_same_support in *;
      eauto with fv;
      eauto using var_in_support.

    apply_anywhere reducible_exists_vars2;
      repeat step || apply subst_erased_type || apply wf_subst;
      eauto using wfs_combine8, erased_terms_combine2 with wf fv erased;
      try solve [ eapply satisfies_erased_terms; eauto; steps ].

    rewrite (subst_subst2 template) in *;
      repeat step || t_substitutions || list_utils2 ||
             (rewrite length_apps by (repeat step || list_utils2)) ||
             (rewrite substitute_nothing6 in * by auto) ||
             (rewrite list_map_apps in * by repeat step || list_utils2) ||
             (rewrite list_map_subst5 by (steps; eauto using var_in_support));
      eauto using var_in_support;
      eauto with fv.

    rewrite (subst_subst (psubstitute template l term_var)) in *;
      repeat step || t_substitutions || list_utils2 ||
             (rewrite length_apps by (repeat step || list_utils2)) ||
             (rewrite substitute_nothing6 in * by auto) ||
             (rewrite list_map_apps in * by repeat step || list_utils2);
      eauto using var_in_support;
      eauto with fv;
      try solve [ t_pfv_in_subst; eauto with fv ].

    rewrite list_map_subst6 in *; repeat step || erewrite satisfies_same_support in * by eauto;
      eauto with fv.
    rewrite list_map_subst8 in *; repeat step || erewrite satisfies_same_support in * by eauto;
      eauto with fv.

    simp_red_goal; repeat step || apply subst_erased_type || apply is_erased_type_close;
      eauto 3 with erased step_tactic;
      eauto 3 using wfs_combine8, erased_terms_combine3 with wf fv erased;
      try solve [ eapply satisfies_erased_terms; eauto; steps ];
      try solve [ eapply reducible_values_closed; eauto; steps ].

     exists (global_trail keys vs); repeat step;
       eauto using typed_erased_terms', is_erased_term_global_trail;
       eauto using typed_fv', fvs_global_trail;
       eauto using typed_wfs', wfs_global_trail;
       eauto using global_trail_is_trail.

    rewrite substitute_open2 in *; repeat step || list_utils; eauto with wf;
      eauto using fvs_global_trail2.
    rewrite open_close in *; steps; eauto using wfs_combine7 with wf.
    rewrite (subst_subst template);
      repeat step || t_substitutions ||
             (rewrite substitute_nothing6 in * by auto) ||
             (rewrite list_map_apps in * by repeat step || list_utils2) ||
             rewrite List.map_map in *.
    rewrite list_map_subst3 in *; steps; eauto.

    rewrite (subst_subst2 template);
      repeat step || list_utils2 || rewrite list_map_subst4 in * ||
             (rewrite length_apps by (repeat step || list_utils2)) ||
             (rewrite list_map_apps in * by repeat step || list_utils2);
      eauto using var_in_support;
      eauto with fv;
      eauto using global_trail_is_trail.

    eapply reducibility_equivalent_substititions; try eassumption;
      repeat step || list_utils || list_utils2 || apply subst_erased_type ||
             t_pfv_in_subst ||
             rewrite length_apps by (repeat step || list_utils2);
      eauto with erased wf fv;
      try solve [ eapply satisfies_erased_terms; eauto; steps ].

    + apply in_combine_equivalent' with fs keys vs l; steps.
      unfold open_reducible in *; repeat step.
      unshelve epose proof (H15 f _ nil l _ _ _);
        repeat step || rewrite substitute_tau in *.

    + instantiate_any; steps.
      clear_marked; apply_anywhere pfv_in_subst2; steps; eauto with fv.
Qed.

Lemma untangle_open_equivalent_types:
  forall Γ T1 T2,
    untangle Γ T1 T2 ->
    [ Γ ⊨ T1 = T2 ].
Proof.
  induction 1; eauto using open_equivalent_types_refl; steps.
Admitted.

(*
| UntangleFreshen:
    forall Γ f T T' template xs ys keys m,
      incomparable (List.map fst keys)
      (forall k1, k
      List.NoDup (xs ++ ys) ->
      T  = substitute template
        (List.combine xs (List.map (fun key => app f (pp key (fvar m term_var))) keys)) ->
      T' = substitute template
        (List.combine xs (List.map (fun y => app f (fvar y term_var)) ys)) ->
      untangle Γ
               (T_exists T_trail (close 0 T m))
               (T_exists_vars ys T_trail T')
*)

  (*
| UntangleFreshen:
    forall Γ T key,
      untangle Γ
        (T_exists T_trail (shift_open 1 T (pp key (lvar 0 term_var))))
        (T_exists T_trail (T_exists T_trail T))
*)
  

  (*
| UntangleFreshen:
    forall Γ f T T' template xs ys keys m,
      List.NoDup (xs ++ ys) ->
      T  = substitute template
        (List.combine xs (List.map (fun key => app f (pp key (fvar m term_var))) keys)) ->
      T' = substitute template
        (List.combine xs (List.map (fun y => app f (fvar y term_var)) ys)) ->
      untangle Γ
               (T_exists T_trail (close 0 T m))
               (T_exists_vars ys T_trail T')
*)

(*



(*
| UntangleTauSingleton:
    forall Γ f T T' T'' x y z ps,
(*      List.NoDup (xs ++ ys ++ zs) ->
      ~ y ∈ fv T'' ->
      ~ z ∈ fv T'' -> *)
(*      [ (f: List -> Nat) :: Γ ⊨ f : T_tau ] -> *)
(*      T = substitute T'' (List.map (fun x => app f (trailOf ps (fvar y term_var))) xs -> *)
      T  = substitute T'' ((x, app f (trailOf ps (fvar y term_var))) :: nil) ->
      T' = substitute T'' ((x, app f (fvar z term_var)) :: nil) ->
      untangle Γ
               (T_exists List (close 0 T y))
               (T_exists List (T_exists List (close 1 T' z)))
*)


Fixpoint trailOf (ps: list tree) (t: tree) :=
  match ps with
  | nil => t
  | x :: xs => tcons x (trailOf xs t)
  end.

Fixpoint trailOf' (ps: list nat) (t: tree) : tree :=
  match ps with
  | nil => t
  | x :: xs => tcons (build_nat x) (trailOf' xs t)
  end.

Definition append : tree. Admitted.
Definition apply_append t1 t2 := app (app append t1) t2.

Definition tau_star (f: tree) : Prop :=
  forall (vs: list nat) (prefixes: list (list nat)),
    List.NoDup prefixes ->
    exists suffix, forall v prefix,
      [ suffix : List ]v ->
      (v, prefix) ∈ List.combine vs prefixes ->
      [ app f (trailOf' prefix suffix) ≡ build_nat v ].

Definition tau_star' (f: tree) : Prop :=
  forall (trails: list tree) (prefixes: list (list nat)),
    List.NoDup prefixes ->
    (forall trail, trail ∈ trails -> [ trail : List ]v) ->
    exists suffix, [ suffix : List ]v /\ forall trail prefix,
      (trail, prefix) ∈ List.combine trails prefixes ->
      [ app f (trailOf' prefix suffix) ≡ app f trail ].

Definition T_same_type T1 T2 : tree :=
  T_intersection
    (T_forall T1 (T_exists T2 (T_equiv (lvar 0 term_var) (lvar 1 term_var))))
    (T_forall T2 (T_exists T1 (T_equiv (lvar 0 term_var) (lvar 1 term_var)))).

Definition T_tau': tree :=
  T_type_refine T_top ( (* f *)
    T_forall List ( (* prefix *)
      T_forall List ( (* trail *)
        T_exists List ( (* suffix *)
          T_equiv
            (app (lvar 3 term_var) (lvar 1 term_var))
            (app (lvar 3 term_var) (apply_append (lvar 2 term_var) (lvar 1 term_var)))
        )
      )
    )
  ).



Definition tau_star'' (f: tree) : Prop :=
  forall (trails: list tree) (prefixes: list (list nat)),
    List.NoDup prefixes ->
    (forall trail, trail ∈ trails -> [ trail : List ]v) ->
    exists suffix, [ suffix : List ]v /\ forall trail prefix,
      (trail, prefix) ∈ List.combine trails prefixes ->
      [ app f (trailOf' prefix suffix) ≡ app f trail ].

*)


(*
exists p, { f (1 :: p) } <: exists p, { f p }  OK
exists p, { f p } <: exists p, { f (1 :: p) }  from Tau

exists p, { (f p, 0) }_Top <: exists p' { (f (1 :: p'), 0) }_Top

let
  t ≡ (f p, 0) for some p
  we know there exists p', such that f p ≡ f (1 :: p')
  t ≡ (f p, 0) ≡ (f (1 :: p'), 0)
*)

(* WRONG
exists p p', { (f p, f (1 :: p')) }_Top <: exists p' { (f (1 :: p'), f (1 :: p')) }_Top

let
  t ≡ (f p, f (1 :: p')) for some p and p'

  we know there exists p'', such that f p ≡ f (1 :: p'')
  t ≡ (f p, f (1 :: p')) ≡ (f (1 :: p''), (1 :: p'))
*)

(*
exists p p', { (f p, g (2 :: p')) }_Top <: exists p' { (f (1 :: p'), g (2 :: p')) }_Top


exists p1 p2, { (f nil p1, g nil p2 }_Top <: exists p' { (f [1] p', g [2] p') }_Top

let
  t ≡ (f p, f (2 :: p')) for some p and p'

  define prefix1 = 1 and prefix2 = 2
  define trail1 = p, and trail2 = 2 :: p'

by the property, there exists p'' such that
f (1 :: p'') ≡ f p
f (2 :: p'') ≡ f (2 :: p')

so t ≡ (f (1 :: p''), f (2 :: p'')) and so

t :  exists p'' { (f (1 :: p''), f (2 :: p'')) }_Top


  we know there exists p'', such that f p ≡ f (1 :: p'')

  t ≡ (f p        , f (2 :: p'))
    ≡ (f (1 :: p''), f (2 :: p'))
*)

(*

Property for f1, ..., fn:

forall trail1, ..., trailn
  forall distinct prefix1, ..., prefix_n,
  exists suffix,
    f1 (prefix1 ++ suffix)  ≡ f trail1 and
    ...
    fn (prefix_n ++ suffix) ≡ f trailn
*)

(*
forall v1, ..., vn: Nat
  forall distinct prefix1, ..., prefix_n,
  exists suffix,
    choose (prefix1 ++ suffix)  ≡ v1 and
    ...
    choose (prefix_n ++ suffix) ≡ vn
*)


(* def h(p: List)(f: List -> Nat) :=
     [ ...
       f [1] p
*)

(*

[[ t: A ]] = exists x: A, x = t

[[ A <-> B ]] = {{ uu | (A -> B) * (B -> A) }}
[[ A <-> B ]] = forall x: A, [ x : B ] intersect ...

About choose_nat, we know:

P(choose_nat) =
  forall v1, ..., vn,
  forall distinct prefix1, ..., prefix_n,
  exists suffix,
    choose_nat (prefix1 ++ suffix) -> v1 and
    ...
    choose_nat (prefix_n ++ suffix) -> vn

We want to prove: choose[Nat]: Tau(z, Nat)
Consider a prefix

( -> ) consider a suffix, and consider choose_nat (prefix ++ suffix) ->* v1
       for prefix1 = <>
       there exists suffix1, choose_nat suffix1 ->* v1

( <- ) consider a suffix, and consider choose_nat suffix ->* v1
       for prefix1 = prefix
       there exists suffix1, choose_nat (prefix1 ++ suffix1) ->* v1

-------------------------------------------------

The tau property:
  forall prefix,
    (exists suffix, { f suffix }) <:
    (exists suffix, { f (prefix ++ sufix) })

  forall prefix, suffix, exists suffix', f suffix = f (prefix ++ suffix')

  forall prefix, Nat <: exists suffix, { choose (prefix ++ sufix) }


tau' property:
  exists suffix, forall prefix,
    exists mid, f suffix = f (prefix ++ mid ++ suffix)


tau2 property:
  forall v1, v2
  forall distinct prefix1, prefix2,
  exists suffix,
    choose (prefix1 ++ suffix) -> v1 and
    choose (prefix2 ++ suffix) -> v2

  forall distinct prefix1, prefix2,
    Nat * Nat <:
    exists suffix, { choose (prefix1 ++ sufix), choose (prefix2 ++ suffix)  }


taun property:
  forall v1, ..., vn,
  forall distinct prefix1, ..., prefix_n,
  exists suffix,
    choose_nat (prefix1 ++ suffix) -> v1 and
    ...
    choose_nat (prefix_n ++ suffix) -> vn

  forall distinct prefix1, ..., prefix_n,
    Nat * Nat * ... * Nat <:
    exists suffix, { choose (prefix1 ++ sufix), ..., choose (prefix_n ++ suffix)  }
*)

(*
[ f :
T_type_refine T_top ( (* f *)
  T_forall ListListNat ( (* trails *)
    T_forall ListListNat ( (* prefixes *)
      T_intersection
        (no_duplicate prefixes ≡ true)
        (T_exists ListNat ( (* suffix *)
          prefixes.map(prefix => app f (apply_append prefix suffix)) ≡
          trails.map(f)
*)

(*
(* forall prefix, trail, exists suffix, f trail = f (prefix ++ suffix) *)
Definition T_tau: tree :=
  T_type_refine T_top (
    T_forall List (T_same_type
      (T_exists List (T_singleton T_top (app (lvar 2 term_var)
        (apply_append (lvar 1 term_var) (lvar 0 term_var) ))))
      (T_exists List (T_singleton T_top (app (lvar 2 term_var) (lvar 0 term_var))))
    )
  ).
*)
