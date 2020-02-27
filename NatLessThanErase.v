Require Export SystemFR.Tactics.
Require Export SystemFR.Trees.
Require Export SystemFR.TypeErasure.
Require Export SystemFR.NatLessThan.

(* Annotated version of `tlt_fix` in `NatCompare.v`. We use dummy type annotations *)
Definition annotated_tlt_fix :=
  tfix T_unit (
    lambda T_unit (lambda T_unit (
      tmatch (lvar 1 term_var)
        (tmatch (lvar 0 term_var)
          tfalse
          ttrue)
        (tmatch (lvar 1 term_var)
          tfalse
          (app (app (lvar 4 term_var) (lvar 1 term_var)) (lvar 0 term_var))
        )
    ))
  ).

Lemma tlt_fix_erase:
  erase_term annotated_tlt_fix = tlt_fix.
Proof.
  steps.
Qed.

Definition annotated_tlt a b := app (app annotated_tlt_fix a) b.

Lemma tlt_erase:
  forall a b, erase_term (annotated_tlt a b) = tlt (erase_term a) (erase_term b).
Proof.
  steps.
Qed.
