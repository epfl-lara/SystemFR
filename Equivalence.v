From Stdlib Require Import String.

Require Export SystemFR.StarLemmas.
Require Export SystemFR.ErasedTermLemmas.

(* Two terms `t1` and `t2` are observationally equivalent if for any context,   *)
(* `C[t1]` reduces to true iff `C[t2]` reduces to true                          *)
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
      open 0 C t1 ~>* ttrue <->
      open 0 C t2 ~>* ttrue.

Notation "[ t1 ≡ t2 ]" := (equivalent_terms t1 t2) (t1 at level 60, t2 at level 60, at level 60).

Ltac equivalence_instantiate C :=
  match goal with
  | H: [ _ ≡ _ ] |- _ =>
    poseNew (Mark (H) "equivalence_instantiate");
    unshelve epose proof ((proj2 (proj2 (proj2 (proj2 (proj2 (proj2 H)))))) C _ _ _)
  end.

Lemma equivalent_terms_fv1:
  forall t1 t2,
    [ t1 ≡ t2 ] ->
    pfv t1 term_var = nil.
Proof.
  unfold equivalent_terms; steps.
Qed.

Lemma equivalent_terms_fv2:
  forall t1 t2,
    [ t1 ≡ t2 ] ->
    pfv t2 term_var = nil.
Proof.
  unfold equivalent_terms; steps.
Qed.

#[export]
Hint Immediate equivalent_terms_fv1: fv.
#[export]
Hint Immediate equivalent_terms_fv2: fv.

Lemma equivalent_terms_erased1:
  forall t1 t2,
    [ t1 ≡ t2 ] ->
    is_erased_term t1.
Proof.
  unfold equivalent_terms; steps.
Qed.

Lemma equivalent_terms_erased2:
  forall t1 t2,
    [ t1 ≡ t2 ] ->
    is_erased_term t2.
Proof.
  unfold equivalent_terms; steps.
Qed.

#[export]
Hint Immediate equivalent_terms_erased1: erased.
#[export]
Hint Immediate equivalent_terms_erased2: erased.

Lemma equivalent_terms_wf1:
  forall t1 t2 k,
    [ t1 ≡ t2 ] ->
    wf t1 k.
Proof.
  unfold equivalent_terms; steps; eauto with wf.
Qed.

Lemma equivalent_terms_wf2:
  forall t1 t2 k,
    [ t1 ≡ t2 ] ->
    wf t2 k.
Proof.
  unfold equivalent_terms; steps; eauto with wf.
Qed.

#[export]
Hint Immediate equivalent_terms_wf1: wf.
#[export]
Hint Immediate equivalent_terms_wf2: wf.

Lemma equivalent_terms_twf1:
  forall t1 t2 k,
    [ t1 ≡ t2 ] ->
    twf t1 k.
Proof.
  unfold equivalent_terms; steps; eauto with twf.
Qed.

Lemma equivalent_terms_twf2:
  forall t1 t2 k,
    [ t1 ≡ t2 ] ->
    twf t2 k.
Proof.
  unfold equivalent_terms; steps; eauto with twf.
Qed.

#[export]
Hint Immediate equivalent_terms_twf1: twf.
#[export]
Hint Immediate equivalent_terms_twf2: twf.
