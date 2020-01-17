Require Import Coq.Lists.List.
Import ListNotations.

Require Export SystemFR.StarLemmas.

(*
Definition equivalent_terms t1 t2 :=
  is_erased_term t1 /\
  is_erased_term t2 /\
  forall t1' t2',
    lift (fun e1 e2 => e1 = t1 /\ e2 = t2) t1' t2' ->
    normalizing t1' <-> normalizing t2'.
*)

(* Two terms `t1` and `t2` are observationally equivalent if for any context,   *)
(* `C[t1]` is scbv_normalizing iff `C[t2]` is scbv_normalizing                            *)
Definition equivalent_terms t1 t2 :=
  is_erased_term t1 /\
  is_erased_term t2 /\
  wf t1 0 /\
  wf t2 0 /\
(*   pfv t1 term_var = nil /\
  pfv t2 term_var = nil /\ *)
  forall C,
    is_erased_term C ->
    wf C 1 ->
(*    pfv C term_var = nil -> *)
    scbv_normalizing (open 0 C t1) <-> scbv_normalizing (open 0 C t2).
