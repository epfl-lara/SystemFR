Require Export SystemFR.ShiftOpen.

Definition tsingleton t :=
  T_type_refine T_top (T_equiv (lvar 0 term_var) (shift 0 t 1)).

Definition type_application T1 T2 : tree :=
  T_type_refine T_top (
    T_exists T1 (
      T_exists T2 (
        T_equiv (app (lvar 1 term_var) (lvar 0 term_var)) (lvar 2 term_var)
      )
    )
  ).

Definition List : tree :=
  intersect
    (T_sum T_top T_top)
    (T_sum T_unit (T_prod T_top (lvar 0 type_var))).

Definition tnil := tleft uu.
Definition Nil := tsingleton tnil.

Definition Var x := tsingleton (fvar x term_var).

Definition tcons h t := tright (pp h t).
Definition Cons H T :=
  T_exists H (T_exists T (
    tsingleton (tcons (lvar 1 term_var) (lvar 0 term_var))
  )).

Definition Match T1 T2 T3 :=
  T_exists T1 (
    T_union
      (T_type_refine T2 (T_equiv (lvar 1 term_var) (tleft uu)))
      (T_exists T_top (
        (T_exists List (
          (T_type_refine
            (shift 0 T3 1)
            (T_equiv
               (lvar 3 term_var)
               (tright (pp (lvar 2 term_var) (lvar 1 term_var))))
          )
        ))
      ))
  ).
