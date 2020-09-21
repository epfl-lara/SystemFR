Require Import Equations.Equations.
Require Import Coq.Classes.RelationClasses.

Require Import Psatz.

Require Export SystemFR.SizeLemmas.
Require Export SystemFR.NoTypeFVar.

Equations strictly_positive (T: tree) (vars: list nat): Prop
    by wf (type_nodes T) lt :=
  strictly_positive (fvar _ type_var) _ := True;
  strictly_positive (lvar _ _) _ := True;

  strictly_positive T_unit _ := True;
  strictly_positive T_bool _ := True;
  strictly_positive T_nat _ := True;
  strictly_positive T_top _ := True;
  strictly_positive T_bot _ := True;

  strictly_positive (T_equiv _ _) _ := True;

  strictly_positive (T_prod T1 T2) vars := strictly_positive T1 vars /\ strictly_positive T2 vars;
  strictly_positive (T_arrow T1 T2) vars := no_type_fvar T1 vars /\ strictly_positive T2 vars;
  strictly_positive (T_forall T1 T2) vars := no_type_fvar T1 vars /\ strictly_positive T2 vars;
  strictly_positive (T_sum T1 T2) vars := strictly_positive T1 vars /\ strictly_positive T2 vars;
  strictly_positive (T_refine T p) vars := strictly_positive T vars;
  strictly_positive (T_type_refine T1 T2) vars := no_type_fvar T1 vars /\ no_type_fvar T2 vars;
  strictly_positive (T_intersection T1 T2) _ :=
    strictly_positive T1 vars /\ strictly_positive T2 vars;

  (* could be relaxed *)
  strictly_positive (T_union T1 T2) vars :=
    no_type_fvar T1 vars /\ no_type_fvar T2 vars;
  strictly_positive (T_exists T1 T2) vars := no_type_fvar T1 vars /\ no_type_fvar T2 vars;

  strictly_positive (T_abs T) vars := strictly_positive T vars;
  strictly_positive (T_rec n T0 Ts) vars :=
    strictly_positive T0 vars /\ strictly_positive Ts vars /\ (
      (no_type_fvar T0 vars /\ no_type_fvar Ts vars) \/
      exists X,
        ~(X ∈ pfv Ts type_var) /\
        strictly_positive (topen 0 Ts (fvar X type_var)) (X :: nil)
    );

  strictly_positive _ vars := False.


Solve All Obligations with (repeat step || autorewrite with bsize in *; try lia; eauto with lia).

Fail Next Obligation.

(* see https://github.com/coq/coq/issues/3814 *)
Instance: subrelation eq Basics.impl.
Proof.
  steps.
Qed.

Instance: subrelation eq (Basics.flip Basics.impl).
Proof.
  steps.
Qed.

Ltac simp_spos_hyp :=
  match goal with
  | H: _ |- _ => rewrite_strat topdown hints strictly_positive in H
  end.

Ltac simp_spos_goal := rewrite_strat topdown hints strictly_positive.

Ltac simp_spos := simp_spos_hyp || simp_spos_goal.
