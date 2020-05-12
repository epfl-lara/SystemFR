Require Export SystemFR.ScalaDepSugar.
Require Export SystemFR.ReducibilitySubtype.
Require Export SystemFR.EquivalentContext.
Require Export SystemFR.TOpenTClose.
Require Export SystemFR.CloseLemmas.

Opaque reducible_values.

Parameter T_key: tree.
Parameter T_map: tree.
Hypothesis key_fv: forall tag, pfv T_key tag = nil.
Hypothesis map_fv: forall tag, pfv T_map tag = nil.
Hypothesis key_wf: forall k, wf T_key k.
Hypothesis map_wf: forall k, wf T_map k.

Definition T_trail: tree := T_prod T_key T_map.

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

(* prefix: T_key -> T_key -> T_bool *)
Parameter prefix: tree -> tree -> tree.

Parameter empty_map: tree (* T_map *).
Hypothesis empty_map_type: [ empty_map : T_map ].

(* update: T_key -> T_key -> T_map -> T_map -> T_map *)
Parameter update: tree -> tree -> tree -> tree -> tree.

(* `update` returns a map such that the submap rooted at `old_key` is now rooted at `new_key` *)
(*  forall key fresh_key fresh_map map δ,
    [ tlookup fresh_map (concat fresh_key δ) ≡
      tlookup (update key fresh_key fresh_map map) (concat key δ) ] *)

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

(*
Hypothesis update_spec3:
  forall key fresh_key fresh_map map key',
    [ prefix key key' ≡ tfalse ] ->
    [ tlookup map key' ≡ tlookup (update key fresh_key fresh_map map) key' ].
*)

(* Terms that take a map and a key `k`, and only lookup the map on keys greater or
   equal than `k` satisfy the following property, described by the type `T_tau` *)
Parameter T_tau: tree.
Lemma tau_property:
  forall f key fresh_key fresh_map map,
    [ f : T_tau ] ->
    [ app2 f fresh_map fresh_key ≡ app2 f (update key fresh_key fresh_map map) key ].
Admitted.

Ltac equivalent_refl :=
  match goal with
  | |- [ _ ≡ _ ] => apply equivalent_refl
  end.

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

Fixpoint closes k T xs :=
  match xs with
  | nil => T
  | x :: xs => close k (closes (S k) T xs) x
  end.

Fixpoint T_existss n T1 T2 :=
  match n with
  | 0 => T2
  | S n' => T_exists T1 (T_existss n' T1 T2)
  end.

Definition T_exists_vars xs T1 T2 :=
  T_existss (List.length xs) T1 (closes 0 T2 xs).

Definition incomparable (keys : list tree) : Prop.
Admitted.

(* Using the tau property, we can untangle *)
Inductive untangle: context -> tree -> tree -> Prop :=
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

| UntangleRefl: forall Γ T, untangle Γ T T
.

Opaque List.

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

Lemma wfs_combine2:
  forall xs f keys m,
    wf f 0 ->
    List.Forall (fun key => [ key : T_key ]) keys ->
    wfs (List.combine xs (List.map (fun key : tree => app f (pp key (fvar m term_var))) keys)) 0.
Proof.
  induction xs; destruct keys; steps; eauto with wf.
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
  induction n; steps.
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
  rewrite substitute_closes; steps; eauto.
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

Lemma list_map_subst:
  forall l f t m v,
    (forall e, e ∈ l -> m ∈ fv e -> False) ->
    List.map (fun e => app f (pp (psubstitute e ((m, v) :: nil) term_var) t)) l =
    List.map (fun e => app f (pp e t)) l.
Proof.
  induction l; repeat step || t_substitutions || t_equality; eauto.
Qed.

Fixpoint opens k t reps :=
  match goal with
  | 

Lemma reducible_existss:
  forall xs ρ v vs T1 T2,
    List.Forall (fun v => [ ρ | v : T1 ]v) vs =
    [ ρ | v : opens 0 T2 vs ]v ->
    [ ρ | v : T_existss n T1 T2 ]v.
Proof.
  unfold T_exists_vars; steps.
Admitted.

Lemma reducible_exists_vars:
  forall xs ρ v vs T1 T2,
    List.Forall (fun v => [ ρ | v : T1 ]v) vs =
    [ ρ | v : psubstitute T2 (List.combine xs vs) term_var ]v ->
    [ ρ | v : T_exists_vars xs T1 T2 ]v.
Proof.
  unfold T_exists_vars; steps.
Admitted.

Lemma untangle_freshen:
forall Γ f template xs ys keys m,
  List.NoDup (xs ++ ys) ->
  wf template 0 ->
  wf f 0 ->
  List.Forall (fun key => [ key : T_key ]) keys ->
  ~ m ∈ fv template ->
  ~ m ∈ fv f ->
  (forall key, key ∈ keys -> m ∈ fv key -> False) ->
  (forall y, y ∈ ys -> y ∈ support Γ -> False) ->
  [Γ
  ⊨ T_exists T_trail
      (close 0
         (psubstitute template
            (List.combine xs (List.map (fun key : tree => app f (pp key (fvar m term_var))) keys))
            term_var) m) =
  T_exists_vars ys T_trail
    (psubstitute template (List.combine xs (List.map (fun y : nat => app f (fvar y term_var)) ys))
       term_var)].
Proof.
  unfold open_equivalent_types, equivalent_types;
    repeat step || list_utils || simp_red_top_level_hyp.

  - rewrite substitute_open2 in *; repeat step || list_utils; eauto with wf.
    rewrite open_close in *; steps; eauto using wfs_combine2 with wf.
    rewrite (subst_subst template) in *; repeat step || rewrite List.map_map in *.
    repeat t_substitutions.
    rewrite list_map_subst in *; steps; eauto.
    rewrite psubstitute_texists_vars;
      repeat step || rewrite substitute_trail || rewrite <- satisfies_same_support in *;
      eauto with fv;
      eauto using var_in_support.
    admit.
Search satisfies.
    

Require Import Coq.Init.Datatypes.
Require Import Coq.Lists.List.
Search (List.map _ (List.map _ _)).
    admit.
    admit.
    apply wf_subst; auto.
    apply wfs_combine.
    admit.

  
  
intros Γ f template xs ys keys m H.


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
