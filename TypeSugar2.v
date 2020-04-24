Require Export SystemFR.ShiftOpen.

Definition tsingleton T t :=
  T_type_refine T (T_equiv (lvar 0 term_var) (shift 0 t 1)).

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
Definition Nil := tsingleton List tnil.

Definition Var x := tsingleton (fvar x term_var).

Definition tcons h t := tright (pp h t).
Definition Cons H T :=
  T_exists H (T_exists T (
    tsingleton List (tcons (lvar 1 term_var) (lvar 0 term_var))
  )).

Definition List_Match t T2 T3 :=
  T_union
    (T_type_refine T2 (T_equiv t tnil))
    (T_exists T_top (
      (T_exists List (
        (T_type_refine T3 (T_equiv t (tcons (lvar 2 term_var) (lvar 1 term_var))))
      ))
    )).

(*
default: T
def f: T = t[f]


def f'(fuel): T =
  if fuel == 0
  then default
  else t[f -> f'(fuel - 1)]

val f = f'(globalFuel)

*)

Parameter globalFuel: tree.

Definition fix_default t default fuel: tree :=
  app
    (notype_lambda (app (lvar 0 term_var) fuel))
    (notype_tfix (
      notype_lambda (              (* fuel *)
        tmatch (lvar 0 term_var)   (* fuel *)
          default
          (shift_open 0 t
            (app (lvar 2 term_var) (lvar 0 term_var))
          )
        )
      )
    ).

Lemma wf_fix_default:
  forall default t fuel,
    wf globalFuel 0 ->
    wf t 1 ->
    wf default 0 ->
    wf fuel 0 ->
    wf (fix_default t default fuel) 0.
Proof.
  unfold fix_default;
    repeat step;
    eauto using wf_shift_open2 with wf step_tactic.
Qed.

Lemma is_erased_list: is_erased_type List.
Proof. steps. Qed.

Hint Resolve is_erased_list: erased.

Lemma wf_list: forall k, wf List k.
Proof. steps; eauto with lia. Qed.

Hint Resolve wf_list: wf.

Lemma open_list: forall k rep, open k List rep = List.
Proof. steps. Qed.

Lemma subst_list: forall l tag, psubstitute List l tag = List.
Proof. steps. Qed.
