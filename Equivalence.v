Require Import Coq.Strings.String.

Require Export SystemFR.StarLemmas.
Require Export SystemFR.ErasedTermLemmas.

(* Two terms `t1` and `t2` are observationally equivalent if for any context,   *)
(* `C[t1]` is scbv_normalizing iff `C[t2]` is scbv_normalizing                  *)
Definition equivalent_terms t1 t2 :=
  is_erased_term t1 /\
  is_erased_term t2 /\
  wf t1 0 /\
  wf t2 0 /\
  pfv t1 term_var = nil /\
  pfv t2 term_var = nil /\
  forall C,
    is_erased_term C ->
    wf C 1 ->
    pfv C term_var = nil ->
      star scbv_step (open 0 C t1) ttrue <->
      star scbv_step (open 0 C t2) ttrue.

Ltac equivalence_instantiate C :=
  match goal with
  | H: equivalent_terms _ _ |- _ =>
    poseNew (Mark (H) "equivalence_instantiate");
    unshelve epose proof ((proj2 (proj2 (proj2 (proj2 (proj2 (proj2 H)))))) C _ _ _)
  end.

Lemma equivalent_terms_fv1:
  forall t1 t2,
    equivalent_terms t1 t2 ->
    pfv t1 term_var = nil.
Proof.
  unfold equivalent_terms; steps.
Qed.

Lemma equivalent_terms_fv2:
  forall t1 t2,
    equivalent_terms t1 t2 ->
    pfv t2 term_var = nil.
Proof.
  unfold equivalent_terms; steps.
Qed.

Hint Immediate equivalent_terms_fv1: fv.
Hint Immediate equivalent_terms_fv2: fv.

Lemma equivalent_terms_erased1:
  forall t1 t2,
    equivalent_terms t1 t2 ->
    is_erased_term t1.
Proof.
  unfold equivalent_terms; steps.
Qed.

Lemma equivalent_terms_erased2:
  forall t1 t2,
    equivalent_terms t1 t2 ->
    is_erased_term t2.
Proof.
  unfold equivalent_terms; steps.
Qed.

Hint Immediate equivalent_terms_erased1: erased.
Hint Immediate equivalent_terms_erased2: erased.

Lemma equivalent_terms_wf1:
  forall t1 t2 k,
    equivalent_terms t1 t2 ->
    wf t1 k.
Proof.
  unfold equivalent_terms; steps; eauto with wf.
Qed.

Lemma equivalent_terms_wf2:
  forall t1 t2 k,
    equivalent_terms t1 t2 ->
    wf t2 k.
Proof.
  unfold equivalent_terms; steps; eauto with wf.
Qed.

Hint Immediate equivalent_terms_wf1: wf.
Hint Immediate equivalent_terms_wf2: wf.

Lemma equivalent_terms_twf1:
  forall t1 t2 k,
    equivalent_terms t1 t2 ->
    twf t1 k.
Proof.
  unfold equivalent_terms; steps; eauto with twf.
Qed.

Lemma equivalent_terms_twf2:
  forall t1 t2 k,
    equivalent_terms t1 t2 ->
    twf t2 k.
Proof.
  unfold equivalent_terms; steps; eauto with twf.
Qed.

Hint Immediate equivalent_terms_twf1: twf.
Hint Immediate equivalent_terms_twf2: twf.
