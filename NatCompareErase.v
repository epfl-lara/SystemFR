Require Import Termination.Tactics.
Require Import Termination.Trees.
Require Import Termination.TypeErasure.
Require Import Termination.NatCompare.

Definition annotated_tlt (a: tree) (b: tree) :=
  app
    (rec (T_arrow T_nat T_nat) a
      (lambda T_nat (tmatch (lvar 0 term_var) tfalse ttrue))
      (lambda T_nat (tmatch (lvar 0 term_var) tfalse (app (app (lvar 2 term_var) uu) (lvar 0 term_var)))))
    b.

Lemma tlt_erase:
  forall a b, erase_term (annotated_tlt a b) = tlt (erase_term a) (erase_term b).
Proof.
  unfold tlt, annotated_tlt; steps.
Qed.
