Require Import Equations.Equations.

Require Import Omega.

Require Import SystemFR.Sets.
Require Import SystemFR.Syntax.
Require Import SystemFR.SizeLemmas.
Require Import SystemFR.NoTypeFVar.
Require Import SystemFR.Tactics.

Equations strictly_positive (T: tree) (vars: list nat): Prop
    by wf (typeNodes T) lt :=
  strictly_positive (fvar _ type_var) _ := True;
  strictly_positive (lvar _ _) _ := True;

  strictly_positive T_unit _ := True;
  strictly_positive T_bool _ := True;
  strictly_positive T_nat _ := True;
  strictly_positive T_top _ := True;
  strictly_positive T_bot _ := True;

  strictly_positive (ite b T1 T2) vars := strictly_positive T1 vars /\ strictly_positive T2 vars;

  strictly_positive (T_equal _ _) _ := True;

  strictly_positive (T_prod T1 T2) vars := strictly_positive T1 vars /\ strictly_positive T2 vars;
  strictly_positive (T_arrow T1 T2) vars := no_type_fvar T1 vars /\ strictly_positive T2 vars;
  strictly_positive (T_forall T1 T2) vars := no_type_fvar T1 vars /\ strictly_positive T2 vars;
  strictly_positive (T_sum T1 T2) vars := strictly_positive T1 vars /\ strictly_positive T2 vars;
  strictly_positive (T_refine T p) vars := strictly_positive T vars;
  strictly_positive (T_type_refine T1 T2) vars := no_type_fvar T1 vars /\ no_type_fvar T2 vars;
  strictly_positive (T_let t T2) vars := strictly_positive T2 vars;
  strictly_positive (T_singleton _) _ := True;
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


Solve All Obligations with (repeat step || autorewrite with bsize in *; try omega; eauto with omega).

Fail Next Obligation.

Ltac simp_spos :=
  rewrite strictly_positive_equation_1 in * ||
  rewrite strictly_positive_equation_2 in * ||
  rewrite strictly_positive_equation_3 in * ||
  rewrite strictly_positive_equation_4 in * ||
  rewrite strictly_positive_equation_5 in * ||
  rewrite strictly_positive_equation_6 in * ||
  rewrite strictly_positive_equation_7 in * ||
  rewrite strictly_positive_equation_8 in * ||
  rewrite strictly_positive_equation_9 in * ||
  rewrite strictly_positive_equation_10 in * ||
  rewrite strictly_positive_equation_11 in * ||
  rewrite strictly_positive_equation_12 in * ||
  rewrite strictly_positive_equation_13 in * ||
  rewrite strictly_positive_equation_14 in * ||
  rewrite strictly_positive_equation_15 in * ||
  rewrite strictly_positive_equation_16 in * ||
  rewrite strictly_positive_equation_17 in * ||
  rewrite strictly_positive_equation_18 in * ||
  rewrite strictly_positive_equation_19 in * ||
  rewrite strictly_positive_equation_20 in * ||
  rewrite strictly_positive_equation_21 in * ||
  rewrite strictly_positive_equation_22 in * ||
  rewrite strictly_positive_equation_23 in * ||
  rewrite strictly_positive_equation_24 in * ||
  rewrite strictly_positive_equation_25 in * ||
  rewrite strictly_positive_equation_26 in * ||
  rewrite strictly_positive_equation_27 in * ||
  rewrite strictly_positive_equation_28 in * ||
  rewrite strictly_positive_equation_29 in * ||
  rewrite strictly_positive_equation_30 in * ||
  rewrite strictly_positive_equation_31 in * ||
  rewrite strictly_positive_equation_32 in * ||
  rewrite strictly_positive_equation_33 in * ||
  rewrite strictly_positive_equation_34 in * ||
  rewrite strictly_positive_equation_35 in * ||
  rewrite strictly_positive_equation_36 in * ||
  rewrite strictly_positive_equation_37 in * ||
  rewrite strictly_positive_equation_38 in * ||
  rewrite strictly_positive_equation_39 in * ||
  rewrite strictly_positive_equation_40 in * ||
  rewrite strictly_positive_equation_41 in * ||
  rewrite strictly_positive_equation_42 in * ||
  rewrite strictly_positive_equation_43 in * ||
  rewrite strictly_positive_equation_44 in * ||
  rewrite strictly_positive_equation_45 in * ||
  rewrite strictly_positive_equation_46 in * ||
  rewrite strictly_positive_equation_47 in * ||
  rewrite strictly_positive_equation_48 in * ||
  rewrite strictly_positive_equation_49 in * ||
  rewrite strictly_positive_equation_50 in * ||
  rewrite strictly_positive_equation_51 in * ||
  rewrite strictly_positive_equation_52 in * ||
  rewrite strictly_positive_equation_53 in * ||
  rewrite strictly_positive_equation_54 in * ||
  rewrite strictly_positive_equation_55 in * ||
  rewrite strictly_positive_equation_56 in * ||
  rewrite strictly_positive_equation_57 in * ||
  rewrite strictly_positive_equation_58 in * ||
  rewrite strictly_positive_equation_59 in * ||
  rewrite strictly_positive_equation_60.
