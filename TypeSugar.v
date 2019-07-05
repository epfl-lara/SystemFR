Require Import SystemFR.Trees.
Require Import SystemFR.SomeTerms.

Definition T_not T := T_arrow T T_bot.
Definition T_has_type t T := T_exists T (T_equal (lvar 0 term_var) t).
Definition T_complement T := T_type_refine T_top (T_not (T_has_type (lvar 0 term_var) T)).
Definition T_ITE T A B := T_union (T_type_refine A T) (T_type_refine B (T_not T)).
Definition T_ite t A B := T_union (T_refine A t) (T_refine B (negate t)).
Definition T_sum_match t A B := T_union (T_let (unfold_left t) A) (T_let (unfold_right t) B).
Definition T_nat_match t T0 Ts := T_union (T_type_refine T0 (T_equal t zero)) (T_let (notype_tpred t) Ts).
Definition T_image f T := T_type_refine T_top (T_exists T (T_equal (lvar 1 term_var) (app f (lvar 0 term_var)))).
