Require Import Equations.Equations.
Require Import Equations.Subterm.

Require Import Omega.

Require Import Coq.Strings.String.
Require Import Coq.Lists.List.

Require Import Termination.StarInversions.
Require Import Termination.StarRelation.
Require Import Termination.SmallStep.
Require Import Termination.Syntax.
Require Import Termination.Trees.
Require Import Termination.Tactics.
Require Import Termination.Equivalence.
Require Import Termination.OpenTOpen.

Require Import Termination.SizeLemmas.

Require Import Termination.WFLemmas.
Require Import Termination.TWFLemmas.
Require Import Termination.ErasedTermLemmas.

Require Import Termination.ReducibilityCandidate.
Require Import Termination.ReducibilityDefinition.
Require Import Termination.ReducibilityLemmas.
Require Import Termination.ReducibilityUnused.
Require Import Termination.ReducibilityMeasure.
Require Import Termination.ReducibilityRenaming.
Require Import Termination.ReducibilitySubst.
Require Import Termination.RedTactics.
Require Import Termination.RedTactics2.

Require Import Termination.AssocList.
Require Import Termination.Sets.
Require Import Termination.Freshness.
Require Import Termination.SwapHoles.
Require Import Termination.ListUtils.
Require Import Termination.TOpenTClose.

Require Import Termination.FVLemmas.

Opaque makeFresh.
Opaque Nat.eq_dec.
Opaque reducible_values.

Fixpoint no_type_lvar (t: tree) (k: nat) :=
  match t with
  | fvar _ type_var => True
  | lvar i type_var => i <> k

  | T_unit => True
  | T_bool => True
  | T_nat => True
  | T_prod T1 T2 => no_type_lvar T1 k /\ no_type_lvar T2 k
  | T_arrow T1 T2 => no_type_lvar T1 k /\ no_type_lvar T2 k
  | T_sum T1 T2 => no_type_lvar T1 k /\ no_type_lvar T2 k
  | T_refine T p => no_type_lvar T k
  | T_let t A B => no_type_lvar A k /\ no_type_lvar B k
  | T_singleton t => True
  | T_intersection T1 T2 => no_type_lvar T1 k /\ no_type_lvar T2 k
  | T_union T1 T2 => no_type_lvar T1 k /\ no_type_lvar T2 k
  | T_top => True
  | T_bot => True
  | T_equal t1 t2 => True
  | T_forall T1 T2 => no_type_lvar T1 k /\ no_type_lvar T2 k
  | T_exists T1 T2 => no_type_lvar T1 k /\ no_type_lvar T2 k
  | T_abs T => no_type_lvar T (S k)
  | T_rec n T0 Ts => no_type_lvar T0 k /\ no_type_lvar Ts (S k)

  | _ => False
  end.

Fixpoint strictly_positive (t: tree) (k: nat) :=
  match t with
  | fvar _ type_var => True
  | lvar i type_var => True

  | T_unit => True
  | T_bool => True
  | T_nat => True
  | T_prod T1 T2 => strictly_positive T1 k /\ strictly_positive T2 k
  | T_arrow T1 T2 => no_type_lvar T1 k /\ strictly_positive T2 k
  | T_sum T1 T2 => strictly_positive T1 k /\ strictly_positive T2 k
  | T_refine T p => strictly_positive T k
  | T_let t A B => strictly_positive A k /\ strictly_positive B k
  | T_singleton t => True
  | T_intersection T1 T2 => strictly_positive T1 k /\ strictly_positive T2 k
  | T_union T1 T2 => no_type_lvar T1 k /\ no_type_lvar T2 k (* !! TODO: This could be relaxed by letting one hole in either T1 or T2 *)
  | T_top => True
  | T_bot => True
  | T_equal t1 t2 => True
  | T_forall T1 T2 => no_type_lvar T1 k /\ strictly_positive T2 k
  | T_exists T1 T2 => no_type_lvar T1 k /\ no_type_lvar T2 k (* !! We cannot push foralls down exists *)
  | T_abs T => strictly_positive T (S k)
  | T_rec n T0 Ts => strictly_positive T0 k /\ strictly_positive Ts (S k) /\ (
                    (* if (S k) appears in Ts, then the recursive type variable of Ts must be positive*)
                      no_type_lvar Ts (S k) \/ strictly_positive Ts 0
                    )

  | _ => False
  end.

Lemma no_type_lvar_open:
  forall T k1 k2 rep,
    twf rep 0 ->
    no_type_lvar T k1 ->
    no_type_lvar (open k2 T rep) k1.
Proof.
  induction T; steps; eauto using twf_open with btwf omega.
Qed.

Lemma strictly_positive_open:
  forall T k1 k2 rep,
    twf rep 0 ->
    strictly_positive T k1 ->
    strictly_positive (open k2 T rep) k1.
Proof.
  induction T; steps;
    eauto using twf_open with btwf omega;
    eauto using no_type_lvar_open.
Qed.

Definition non_empty theta A := exists v, reducible_values theta v A.

Lemma instantiate_non_empty:
  forall theta (A: tree) (P: tree -> Prop),
    non_empty theta A ->
    (forall a, reducible_values theta a A -> P a) ->
    exists a, reducible_values theta a A /\ P a.
Proof.
  unfold non_empty; steps; eauto.
Qed.

Ltac t_instantiate_non_empty :=
  match goal with
  | H1: non_empty ?theta ?A, H2: forall a, reducible_values ?theta a ?A -> _ |- _ =>
    pose proof (instantiate_non_empty _ _ _ H1 H2)
  end.

Ltac apply_induction H :=
  match goal with
  | |- reducible_values _ _ (topen 0 ?T _) => apply H with (size T, index T)
  end.

(*
Lemma twf_positive:
  forall T k,
    is_erased_type T ->
    twf T k ->
    strictly_positive T k.
Proof.
  induction T; steps; try omega.
Qed.
*)

(*
Lemma strict_positive_monotone:
  forall T k1 k2,
    strictly_positive T k1 ->
    k1 <= k2 ->
    strictly_positive T k2.
Proof.
  induction T;
    repeat step;
    eauto with btwf omega.
Qed.
*)

(*
Lemma strictly_positive_swap:
  forall T i rep,
    twf rep 0 ->
    is_erased_type T ->
    strictly_positive rep 0 ->
    strictly_positive T (S i) ->
    strictly_positive (topen (S i) (swap_type_holes T i (S i)) rep) i.
Proof.
  induction T; repeat step || apply twf_swap;
    eauto using strict_positive_monotone with omega.
Qed.
*)

Lemma non_empty_extend:
  forall theta A x RC,
    non_empty theta A ->
    reducibility_candidate RC ->
    valid_interpretation theta ->
    ~(x ∈ pfv A type_var) ->
    non_empty ((x, RC) :: theta) A.
Proof.
  unfold non_empty; repeat step || exists v || apply reducible_unused2.
Qed.

Lemma twf_no_type_lvar:
  forall T k,
    is_erased_type T ->
    twf T k ->
    no_type_lvar T k.
Proof.
  induction T; steps; try omega.
Qed.

Lemma twf_positive:
  forall T k,
    is_erased_type T ->
    twf T k ->
    strictly_positive T k.
Proof.
  induction T; steps; try omega;
    eauto using twf_no_type_lvar.
Qed.

Lemma twf_positive2:
  forall T k,
    is_erased_type T ->
    twf T 0 ->
    strictly_positive T k.
Proof.
  eauto using twf_positive with btwf omega.
Qed.

Lemma no_type_lvar_in_topen:
  forall T i j R,
    is_erased_type T ->
    is_erased_type R ->
    twf R 0 ->
    no_type_lvar T i ->
    no_type_lvar (topen j T R) i.
Proof.
  induction T; repeat step || apply twf_no_type_lvar;
    eauto using twf_positive2; eauto with btwf omega.
Qed.

Lemma strictly_positive_topen:
  forall T i j R,
    is_erased_type T ->
    is_erased_type R ->
    twf R 0 ->
    strictly_positive T i ->
    strictly_positive (topen j T R) i.
Proof.
  induction T; steps;
    eauto using twf_positive2;
    eauto using no_type_lvar_in_topen.
Qed.

Lemma no_type_var_positive:
  forall T k,
    is_erased_type T ->
    no_type_lvar T k ->
    strictly_positive T k.
Proof.
  induction T; steps; try omega.
Qed.

Lemma no_type_lvar_topen:
  forall T k R,
    no_type_lvar T k ->
    is_erased_type T ->
    topen k T R = T.
Proof.
  induction T; repeat step || tequality || t_topen_none.
Qed.

Lemma strictly_positive_push_forall:
  forall measure T theta A B v,
    (size T, index T) = measure ->
    strictly_positive T 0 ->
    wf T 0 ->
    twf T 1 ->
    wf A 0 ->
    twf A 0 ->
    wf B 1 ->
    twf B 0 ->
    valid_interpretation theta ->
    non_empty theta A ->
    is_erased_type A ->
    is_erased_type B ->
    is_erased_type T ->
    (forall a,
      reducible_values theta a A ->
      reducible_values theta v (topen 0 T (open 0 B a))) ->
    reducible_values theta v (topen 0 T (T_forall A B)).
Proof.
  induction measure as [ PP HH ] using measure_induction; intros; t_instantiate_non_empty; destruct T;
    repeat match goal with
    | _ =>
      step ||
      simp_red ||
      t_topen_none ||
      t_instantiate_reducible ||
      find_reducible_value ||
      reducibility_choice ||
      t_deterministic_star ||
      (* t_reduces_to || *)
      ( progress unfold reduces_to in * ) ||
      find_smallstep_value ||
      apply strictly_positive_open ||
      apply left_lex ||
      apply_induction HH ||
      find_exists ||
      ( progress autorewrite with bsize in * ) ||
      (rewrite open_topen in * by (steps; eauto with btwf; eauto with bwf)) ||
      (rewrite no_type_lvar_topen in * by (repeat step || apply no_type_lvar_open || apply is_erased_type_open; eauto with btwf))
    end;
    try omega;
    eauto using reducible_values_closed;
    eauto with berased bwf btwf;
    eauto using no_type_var_positive;
    try solve [ apply twf_open; eauto with btwf ];
    t_closer.

  (** Polymorphic type **)
  - exists (makeFresh (
           support theta ::
           pfv A type_var ::
           pfv T type_var ::
           pfv B type_var ::
           pfv (topen 1 T (T_forall A B)) type_var :: nil));
      repeat step || finisher || t_instantiate_rc || find_smallstep_value;
        try solve [ repeat unfold closed_term, closed_value in * || step ].

    rewrite open_swap; steps; eauto with omega.
    apply_induction HH;
      repeat
        step ||
        apply left_lex ||
        (progress autorewrite with bsize in * ) ||
        apply strictly_positive_swap ||
        apply twf_topen ||
        apply is_erased_type_topen ||
        apply non_empty_extend ||
        t_deterministic_star ||
        apply wf_topen;
      try finisher;
      eauto with bwf btwf omega berased;
      eauto 2 using red_is_val with step_tactic.

    apply reducible_unused3 in H27; steps; try finisher.

    rewrite open_swap;
      repeat step || rewrite swap_holes_twice ||
             t_instantiate_reducible || t_instantiate_rc ||
             unfold reduces_to in * || t_deterministic_star ||
             simp_red || t_reducible_rename_one || t_fv_open ||
             t_listutils ||
             unshelve eauto using valid_interpretation_cons with btwf btwf2 ||
             unshelve eauto using valid_interpretation_cons, red_is_val;
      try finisher;
      eauto using fv_in_reducible_val.

  (** Recursive type at 0 **)
  - left.
      repeat step || simp_red ||
             t_instantiate_reducible || apply_induction HH || apply left_lex ||
             t_deterministic_star ||
             t_topen_none; eauto with omega.

  (** Recursive type at n+1 **)
  - right.
      exists n'0, v'0, (makeFresh (
                       support theta ::
                       pfv A type_var ::
                       pfv n'0 type_var ::
                       pfv (topen 0 T2 (T_forall A B)) type_var ::
                       pfv (topen 1 T3 (T_forall A B)) type_var ::
                       nil));
      repeat step || simp_red ||
             t_instantiate_reducible || apply_induction HH || apply left_lex ||
             t_deterministic_star ||
             t_topen_none;
        eauto with omega;
        try finisher.

      remember (makeFresh (
                       support theta ::
                       pfv A type_var ::
                       pfv n'0 type_var ::
                       pfv (topen 0 T2 (T_forall A B)) type_var ::
                       pfv (topen 1 T3 (T_forall A B)) type_var ::
                       nil)) as M.

      apply reducibility_subst_head2;
        repeat
          step || t_listutils ||
          apply is_erased_topen ||
          apply is_erased_type_topen ||
          apply twf_topen ||
          apply wf_topen;
        try finisher;
        eauto with btwf;
        eauto with bwf.

Set Nested Proofs Allowed.
Lemma topen_rec:
  forall k n T0 Ts R,
    twf n 0 ->
    topen k (T_rec n T0 Ts) R = T_rec n (topen k T0 R) (topen (S k) Ts R).
Proof.
  repeat step || tequality || rewrite topen_none; eauto with btwf omega.
Qed.

      rewrite open_swap;
        repeat step || apply twf_topen;
        eauto with omega;
        eauto with btwf.

      rewrite <- topen_rec; eauto with btwf.
      define M2 (makeFresh (
                     pfv (swap_type_holes T3 0 1) type_var ::
                     pfv (T_rec n'0 T2 T3) type_var ::
                     nil
                )).
      rewrite (topen_twice _ _ _ M2); steps; eauto with btwf; try finisher.

    apply_induction HH;
      repeat
        step ||
        apply left_lex ||
        (progress autorewrite with bsize in * ) ||
        apply strictly_positive_swap ||
        apply twf_topen ||
        apply is_erased_type_topen ||
        apply non_empty_extend ||
        t_deterministic_star ||
        apply wf_topen;
      try finisher;
      eauto with bwf btwf omega berased;
      eauto 2 using red_is_val with step_tactic;
      eauto using reducibility_is_candidate.

    + admit. (* use multiset measure *)
    +

Lemma strictly_positive_close:
  forall T k1 k2 rep,
    twf rep 0 ->
    strictly_positive T k1 ->
    strictly_positive (open k2 T rep) k1.
Proof.
  induction T; steps; eauto using twf_open with btwf omega.
Qed.

      remember (makeFresh (
                       support theta ::
                       pfv A type_var ::
                       pfv n'0 type_var ::
                       pfv (topen 0 T2 (T_forall A B)) type_var ::
                       pfv (topen 1 T3 (T_forall A B)) type_var ::
                       nil)) as M.
      

     (*
    topen 0 (topen 1 A R) (topen 0 B R)
*)
(*
*)
    (*
    assert (
      topen 0 (topen 1 A (topen 0 B R)) R
      topen 0 (t_close 0 (topen 1 A (topen 0 B X)) X) R
    ).
*)
Admitted.

Lemma strictly_positive_pull_forall:
  forall T theta A B v a,
    strictly_positive T 0 ->
    wf T 0 ->
    twf T 1 ->
    wf A 0 ->
    twf A 0 ->
    wf B 1 ->
    twf B 0 ->
    valid_interpretation theta ->
    reducible_values theta a A ->
    reducible_values theta v (topen 0 T (T_forall A B)) ->
    reducible_values theta v (topen 0 T (open 0 B a)).
Proof.
(*  induction T;
    repeat t_topen_none || step ||
      simp reducible_values in * ||
      (rewrite topen_none in * by t_rewrite);
    eauto 6 with berased; eauto 11. *)
Admitted.
