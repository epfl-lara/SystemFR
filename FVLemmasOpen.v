Require Import Coq.Strings.String.

Require Import Termination.Typing.
Require Import Termination.Syntax.
Require Import Termination.Tactics.
Require Import Termination.Freshness.
Require Import Termination.AssocList.
Require Import Termination.TermList.

Require Import Termination.Sets.
Require Import Termination.SetLemmas.

Require Import Termination.FVLemmas.
Require Import Termination.FVLemmasTyping.
Require Import Termination.FVLemmasLists.

Ltac pp :=
  repeat
    step || p_fv ||
    slow_instantiations ||
    fresh_instantiations1 ||
    unfold subset in *; eauto 1 with omega.

(*
Lemma defined_FV_open:
  forall tvars gamma A t T L,
    (forall x, ~(x ∈ L) -> has_type tvars ((x,A) :: gamma) (open 0 t (fvar x)) T) ->
    subset (fv t) (support gamma).
Proof.
  pp; eauto 2 with bfv.
Qed.

Hint Resolve defined_FV_open: bfv.
*)

(*
Lemma defined_FV_open2:
  forall gamma A t T L,
    (forall x, ~(x ∈ L) -> has_type ((x,A) :: gamma) (open 0 t (fvar x)) (open 0 T (fvar x))) ->
    subset (fv t) (support gamma).
Proof.
  pp; eauto 2 with bfv.
Qed.

Hint Resolve defined_FV_open2: bfv.
*)

(*
Lemma defined_FV_open3:
  forall gamma A t T L,
    (forall x, ~(x ∈ L) -> has_type ((x,A) :: gamma) t (open 0 T (fvar x))) ->
    subset (fv t) (support gamma).
Proof.
  pp; eauto 2 with bfv.
  instantiate_any; repeat pp.
Qed.

Hint Resolve defined_FV_open3: bfv.
*)

(*
Lemma defined_FV_open4:
  forall gamma A t T V L,
    (forall x y, ~(x ∈ L) ->
            ~(y ∈ L) ->
            ~(x = y) ->
            has_type ((y, open 0 V (fvar x)) :: (x,A) :: gamma) (open 0 t (fvar y)) T) ->
    subset (fv t) (support gamma).
Proof.
  pp; eauto 2 with bfv.
Qed.

Hint Resolve defined_FV_open4: bfv.
*)
(*
Lemma defined_FV_open_type:
  forall gamma A T L,
    (forall x, ~(x ∈ L) -> is_type ((x,A) :: gamma) (open 0 T (fvar x))) ->
    subset (fv T) (support gamma).
Proof.
  pp; eauto 2 with bfv.
Qed.

Hint Resolve defined_FV_open_type: bfv.

Lemma defined_FV_double_open:
  forall gamma A T L t,
    (forall x y,
        (x ∈ L -> False) ->
        (y ∈ L -> False) ->
        (x = y -> False) ->
        has_type
          ((x, open 0 T (fvar y)) :: (y, A) :: gamma)
          (open 0 (open 1 t (fvar y)) (fvar x))
          (open 0 T (succ (fvar y)))) ->
    subset (fv t) (support gamma).
Proof.
  pp; eauto 3 with bfv.
Qed.

Hint Resolve defined_FV_double_open: bfv.


Lemma fv_nils3_open:
  forall P gamma t U V L l,
    (forall x : nat, (x ∈ L -> False) -> has_type ((x, U) :: gamma) (open 0 t (fvar x)) (open 0 V (fvar x))) ->
    satisfies P gamma l ->
    fv (substitute t l) = nil.
Proof.
  repeat step; eauto 6 using subset_same, satisfies_same_support with bfv.
Qed.

Hint Resolve fv_nils3_open: bfv.

Lemma fv_nils_double_open:
  forall P gamma t L l A T,
    (forall x y,
        (x ∈ L -> False) ->
        (y ∈ L -> False) ->
        (x = y -> False) ->
        has_type
          ((x, open 0 T (fvar y)) :: (y, A) :: gamma)
          (open 0 (open 1 t (fvar y)) (fvar x))
          (open 0 T (succ (fvar y)))) ->
    satisfies P gamma l ->
    fv (substitute t l) = nil.
Proof.
  repeat step; eauto 6 using subset_same, satisfies_same_support with bfv.
Qed.

Hint Resolve fv_nils_double_open: bfv.
*)
