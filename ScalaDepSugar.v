Require Export SystemFR.ShiftOpen.

Definition T_singleton T t :=
  T_type_refine T (T_equiv (lvar 0 term_var) (shift 0 t 1)).

Lemma substitute_singleton:
  forall T t l tag,
    wfs l 0 ->
    psubstitute (T_singleton T t) l tag =
    T_singleton (psubstitute T l tag) (psubstitute t l tag).
Proof.
  unfold T_singleton; repeat step || rewrite substitute_shift.
Qed.

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
Definition Nil := T_singleton List tnil.

Definition Var x := T_singleton (fvar x term_var).

Definition tcons h t := tright (pp h t).
Definition Cons H T :=
  T_exists H (T_exists T (
    T_singleton List (tcons (lvar 1 term_var) (lvar 0 term_var))
  )).

Definition list_match t1 t2 t3 :=
  sum_match t1 t2
    (shift_open 1 (shift_open 0 t3 (pi2 (lvar 0 term_var))) (pi1 (lvar 0 term_var))).

Definition List_Match t T2 T3 :=
  T_union
    (T_type_refine T2 (T_equiv t tnil))
    (T_exists T_top (
      (T_exists List (
        (T_type_refine T3 (T_equiv t (tcons (lvar 2 term_var) (lvar 1 term_var))))
      ))
    )).

Lemma wf_list_match:
  forall t1 t2 t3,
    wf t1 0 ->
    wf t2 0 ->
    wf t3 2 ->
    wf (list_match t1 t2 t3) 0.
Proof.
  repeat step; eauto 3 with wf step_tactic.
Qed.

Lemma pfv_list_match:
  forall t1 t2 t3 tag,
    pfv t1 tag = nil ->
    pfv t2 tag = nil ->
    pfv t3 tag = nil ->
    pfv (list_match t1 t2 t3) tag = nil.
Proof.
  repeat step || list_utils; eauto with fv.
Qed.

Lemma pfv_list_match2:
  forall t1 t2 t3 tag,
    subset (pfv (list_match t1 t2 t3) tag) (pfv t1 tag ++ pfv t2 tag ++ pfv t3 tag).
Proof.
  repeat step || list_utils || sets; eauto with sets.
  eapply subset_transitive; eauto using pfv_shift_open2; repeat step || sets; eauto with sets.
  eapply subset_transitive; eauto using pfv_shift_open2; repeat step || sets; eauto with sets.
Qed.

Lemma is_erased_term_list_match:
  forall t1 t2 t3,
    is_erased_term t1 ->
    is_erased_term t2 ->
    is_erased_term t3 ->
    is_erased_term (list_match t1 t2 t3).
Proof.
  repeat step || apply is_erased_term_shift_open.
Qed.

Lemma substitute_list_match:
  forall t1 t2 t3 l tag,
    wfs l 0 ->
    psubstitute (list_match t1 t2 t3) l tag =
    list_match (psubstitute t1 l tag) (psubstitute t2 l tag) (psubstitute t3 l tag).
Proof.
  unfold list_match; repeat step || t_equality || rewrite substitute_shift_open.
Qed.

Lemma wf_List_Match:
  forall t1 T2 T3,
    wf t1 0 ->
    wf T2 0 ->
    wf T3 2 ->
    wf (List_Match t1 T2 T3) 0.
Proof.
  repeat step; eauto 3 with wf step_tactic.
Qed.

Lemma pfv_List_Match:
  forall t1 T2 T3 tag,
    pfv t1 tag = nil ->
    pfv T2 tag = nil ->
    pfv T3 tag = nil ->
    pfv (List_Match t1 T2 T3) tag = nil.
Proof.
  repeat step || list_utils; eauto with fv.
Qed.

Lemma is_erased_type_List_Match:
  forall t1 T2 T3,
    is_erased_term t1 ->
    is_erased_type T2 ->
    is_erased_type T3 ->
    is_erased_type (List_Match t1 T2 T3).
Proof.
  steps.
Qed.

Lemma substitute_List_Match:
  forall t1 t2 t3 l tag,
    wfs l 0 ->
    psubstitute (List_Match t1 t2 t3) l tag =
    List_Match (psubstitute t1 l tag) (psubstitute t2 l tag) (psubstitute t3 l tag).
Proof.
  unfold list_match; repeat step || t_equality || rewrite substitute_shift_open.
Qed.

(*
default: T
def f: T = t[f]


def f'(fuel): T =
  if fuel == 0
  then default
  else t[f -> f'(fuel - 1)]

val f = f'(globalFuel)

*)

Definition fix_default' t default fuel: tree :=
  app
    (notype_tfix ( (* unused and f *)
      notype_lambda (           (* fuel *)
        tmatch (lvar 0 term_var (* fuel *))
          default
          (shift_open 0 t
            (app (lvar 2 term_var (* f *)) (lvar 0 term_var (* new fuel *)))
          )
        )
      )
    )
    fuel
.

Parameter global_fuel: tree.
Parameter is_nat_global_fuel: is_nat_value global_fuel.

Definition fix_default t default := fix_default' t default global_fuel.

Lemma wf_fix_default:
  forall default t fuel,
    wf t 1 ->
    wf default 0 ->
    wf fuel 0 ->
    wf (fix_default' t default fuel) 0.
Proof.
  unfold fix_default;
    repeat step;
    eauto using wf_shift_open2 with wf step_tactic.
Qed.

Lemma subst_fix_default:
  forall t default fuel l tag,
    wfs l 0 ->
    psubstitute (fix_default' t default fuel) l tag =
    fix_default' (psubstitute t l tag) (psubstitute default l tag) (psubstitute fuel l tag).
Proof.
  unfold fix_default; repeat step || t_equality || rewrite substitute_shift_open in *.
Qed.

Lemma pfv_fix_default:
  forall t default fuel tag,
    pfv t tag = nil ->
    pfv default tag = nil ->
    pfv fuel tag = nil ->
    pfv (fix_default' t default fuel) tag = nil.
Proof.
  repeat step || list_utils || rewrite pfv_shift_open.
Qed.

Lemma pfv_fix_default2:
  forall t default fuel tag,
    subset
      (pfv (fix_default' t default fuel) tag)
      (pfv t tag ++ pfv default tag ++ pfv fuel tag).
Proof.
  repeat step || list_utils || apply subset_union2; eauto with sets.
  eapply subset_transitive; eauto using pfv_shift_open2; repeat step || sets; eauto with sets.
Qed.

Lemma is_erased_term_fix_default:
  forall t default fuel,
    is_erased_term t ->
    is_erased_term default ->
    is_erased_term fuel ->
    is_erased_term (fix_default' t default fuel).
Proof.
  repeat step || apply is_erased_term_shift_open.
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
