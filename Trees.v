Require Export SystemFR.Tactics.

Inductive fv_tag: Set := term_var | type_var.

Inductive op: Set := plus | minus | mul | div | eq | neq | lt | leq | gt | geq | Not | And | Or | Cup | Nop .

Ltac destruct_tag :=
  match goal with
  | tag: fv_tag |- _ => destruct tag
  end.

(* locally nameless representation *)
Inductive tree: Set :=
  (* term or type variable *)
  | fvar: nat -> fv_tag -> tree
  | lvar: nat -> fv_tag -> tree

  (* types *)
  | T_nat: tree
  | T_unit: tree
  | T_bool: tree
  | T_arrow: tree -> tree -> tree
  | T_prod: tree -> tree -> tree
  | T_sum: tree -> tree -> tree
  | T_refine: tree -> tree -> tree
  | T_type_refine: tree -> tree -> tree
  | T_intersection: tree -> tree -> tree
  | T_union: tree -> tree -> tree
  | T_top: tree
  | T_bot: tree
  | T_equiv: tree -> tree -> tree
  | T_forall: tree -> tree -> tree
  | T_exists: tree -> tree -> tree
  | T_abs: tree -> tree
  | T_rec: tree -> tree -> tree -> tree

  (* terms *)
  | err: tree -> tree
  | notype_err: tree

  | uu: tree

  | tsize: tree -> tree

  | lambda: tree -> tree -> tree
  | notype_lambda: tree -> tree
  | app: tree -> tree -> tree

  | forall_inst: tree -> tree -> tree

  | pp: tree -> tree -> tree
  | pi1: tree -> tree
  | pi2: tree -> tree

  | because: tree -> tree -> tree
  | get_refinement_witness: tree -> tree -> tree

  | ttrue: tree
  | tfalse: tree
  | ite: tree -> tree -> tree -> tree
  | boolean_recognizer: nat -> tree -> tree

  | zero: tree
  | succ: tree -> tree
  | tmatch: tree -> tree -> tree -> tree

  | unary_primitive : op -> tree -> tree
  | binary_primitive : op -> tree -> tree -> tree

  | tfix: tree -> tree -> tree
  | notype_tfix: tree -> tree

  | tlet: tree -> tree -> tree -> tree
  | notype_tlet: tree -> tree -> tree

  | type_abs: tree -> tree
  | type_inst: tree -> tree -> tree

  | tfold: tree -> tree -> tree
  | tunfold: tree -> tree
  | tunfold_in: tree -> tree -> tree
  | tunfold_pos_in: tree -> tree -> tree

  | tright: tree -> tree
  | tleft: tree -> tree
  | sum_match: tree -> tree -> tree -> tree

  | typecheck: tree -> tree -> tree

  | trefl: tree -> tree -> tree
.

(* types defined in terms out of the previous types *)
Definition intersect T0 Ts := T_forall T_nat (T_rec (lvar 0 term_var) T0 Ts).

Fixpoint is_annotated_term t :=
  match t with
  | fvar y term_var => True
  | lvar _ term_var => True
  | err T => is_annotated_type T

  | uu => True

  | tsize t => is_annotated_term t

  | lambda T t' => is_annotated_type T /\ is_annotated_term t'
  | app t1 t2 => is_annotated_term t1 /\ is_annotated_term t2

  | forall_inst t1 t2 => is_annotated_term t1 /\ is_annotated_term t2

  | type_abs t => is_annotated_term t
  | type_inst t T => is_annotated_term t /\ is_annotated_type T

  | pp t1 t2 => is_annotated_term t1 /\ is_annotated_term t2
  | pi1 t' => is_annotated_term t'
  | pi2 t' => is_annotated_term t'

  | because t1 t2 => is_annotated_term t1 /\ is_annotated_term t2
  | get_refinement_witness t1 t2 => is_annotated_term t1 /\ is_annotated_term t2

  | ttrue => True
  | tfalse => True
  | ite t1 t2 t3 => is_annotated_term t1 /\ is_annotated_term t2 /\ is_annotated_term t3
  | boolean_recognizer _ t => is_annotated_term t

  | zero => True
  | succ t' => is_annotated_term t'
  | tmatch t' t0 ts => is_annotated_term t' /\ is_annotated_term t0 /\ is_annotated_term ts

  | unary_primitive _ t => is_annotated_term t
  | binary_primitive _ t1 t2 => is_annotated_term t1 /\ is_annotated_term t2

  | tfix T t' => is_annotated_type T /\ is_annotated_term t'

  | notype_tlet t1 t2 => is_annotated_term t1 /\ is_annotated_term t2
  | tlet t1 A t2 => is_annotated_term t1 /\ is_annotated_type A /\ is_annotated_term t2
  | trefl t1 t2 => is_annotated_term t1 /\ is_annotated_term t2

  | tfold T t => is_annotated_type T /\ is_annotated_term t
  | tunfold t => is_annotated_term t
  | tunfold_in t1 t2 => is_annotated_term t1 /\ is_annotated_term t2
  | tunfold_pos_in t1 t2 => is_annotated_term t1 /\ is_annotated_term t2

  | tleft t => is_annotated_term t
  | tright t => is_annotated_term t
  | sum_match t tl tr => is_annotated_term t /\ is_annotated_term tl /\ is_annotated_term tr

  | typecheck t T => is_annotated_term t /\ is_annotated_type T

  | _ => False
  end
with is_annotated_type T :=
  match T with
  | fvar y type_var => True
  | lvar y type_var => True
  | T_unit => True
  | T_bool => True
  | T_nat => True
  | T_refine A p => is_annotated_type A /\ is_annotated_term p
  | T_type_refine A B => is_annotated_type A /\ is_annotated_type B
  | T_prod A B => is_annotated_type A /\ is_annotated_type B
  | T_arrow A B => is_annotated_type A /\ is_annotated_type B
  | T_sum A B => is_annotated_type A /\ is_annotated_type B
  | T_intersection A B => is_annotated_type A /\ is_annotated_type B
  | T_union A B => is_annotated_type A /\ is_annotated_type B
  | T_top => True
  | T_bot => True
  | T_equiv t1 t2 => is_annotated_term t1 /\ is_annotated_term t2
  | T_forall A B => is_annotated_type A /\ is_annotated_type B
  | T_exists A B => is_annotated_type A /\ is_annotated_type B
  | T_abs T => is_annotated_type T
  | T_rec n T0 Ts => is_annotated_term n /\ is_annotated_type T0 /\ is_annotated_type Ts
  | _ => False
  end
.


Fixpoint is_erased_term t :=
    match t with
  | fvar y term_var => True
  | lvar _ term_var => True
  | notype_err => True

  | uu => True

  | tsize t => is_erased_term t

  | notype_lambda t' => is_erased_term t'
  | app t1 t2 => is_erased_term t1 /\ is_erased_term t2

  | pp t1 t2 => is_erased_term t1 /\ is_erased_term t2
  | pi1 t' => is_erased_term t'
  | pi2 t' => is_erased_term t'

  | ttrue => True
  | tfalse => True
  | ite t1 t2 t3 => is_erased_term t1 /\ is_erased_term t2 /\ is_erased_term t3
  | boolean_recognizer _ t => is_erased_term t

  | zero => True
  | succ t' => is_erased_term t'
  | tmatch t' t0 ts => is_erased_term t' /\ is_erased_term t0 /\ is_erased_term ts

  | notype_tfix t' => is_erased_term t'

  | tleft t => is_erased_term t
  | tright t => is_erased_term t
  | sum_match t tl tr => is_erased_term t /\ is_erased_term tl /\ is_erased_term tr

  | _ => False
  end.

Fixpoint is_erased_type T :=
  match T with
  | fvar y type_var => True
  | lvar y type_var => True

  | T_unit => True
  | T_bool => True
  | T_nat => True
  | T_refine A p => is_erased_type A /\ is_erased_term p
  | T_type_refine A B => is_erased_type A /\ is_erased_type B
  | T_prod A B => is_erased_type A /\ is_erased_type B
  | T_arrow A B => is_erased_type A /\ is_erased_type B
  | T_sum A B => is_erased_type A /\ is_erased_type B
  | T_intersection A B => is_erased_type A /\ is_erased_type B
  | T_union A B => is_erased_type A /\ is_erased_type B
  | T_top => True
  | T_bot => True
  | T_equiv t1 t2 => is_erased_term t1 /\ is_erased_term t2
  | T_forall A B => is_erased_type A /\ is_erased_type B
  | T_exists A B => is_erased_type A /\ is_erased_type B
  | T_abs A => is_erased_type A
  | T_rec n T0 Ts => is_erased_term n /\ is_erased_type T0 /\ is_erased_type Ts
  | _ => False
  end.


Fixpoint tree_size t :=
  match t with
  | fvar _ _ => 0
  | lvar _ _ => 0
  | err t => 1 + tree_size t
  | notype_err => 0

  | uu => 0

  | tsize t => 1 + tree_size t

  | notype_lambda t' => 1 + tree_size t'
  | lambda T t' => 1 + tree_size T + tree_size t'
  | app t1 t2 => 1 + tree_size t1 + tree_size t2

  | forall_inst t1 t2 => 1 + tree_size t1 + tree_size t2

  | pp t1 t2 => 1 + tree_size t1 + tree_size t2
  | pi1 t' => 1 + tree_size t'
  | pi2 t' => 1 + tree_size t'

  | because t1 t2 => 1 + tree_size t1 + tree_size t2
  | get_refinement_witness t1 t2 => 1 + tree_size t1 + tree_size t2

  | ttrue => 0
  | tfalse => 0
  | ite t1 t2 t3 => 1 + tree_size t1 + tree_size t2 + tree_size t3
  | boolean_recognizer _ t => 1 + tree_size t

  | zero => 0
  | succ t' =>  1 + tree_size t'
  | tmatch t' t0 ts => 1 + tree_size t' + tree_size t0 + tree_size ts

  | unary_primitive _ t => 1 + tree_size t
  | binary_primitive _ t1 t2 => 1 + tree_size t1 + tree_size t2

  | tfix T t' => 1 + tree_size T + tree_size t'
  | notype_tfix t' => 1 + tree_size t'

  | notype_tlet t1 t2 => 1 + tree_size t1 + tree_size t2
  | tlet t1 A t2 => 1 + tree_size t1 + tree_size A + tree_size t2
  | trefl t1 t2 => 1 + tree_size t1 + tree_size t2

  | type_abs t => 1 + tree_size t
  | type_inst t T => 1 + tree_size t + tree_size T

  | tfold T t => 1 + tree_size T + tree_size t
  | tunfold t => 1 + tree_size t
  | tunfold_in t1 t2 => 1 + tree_size t1 + tree_size t2
  | tunfold_pos_in t1 t2 => 1 + tree_size t1 + tree_size t2

  | tright t => 1 + tree_size t
  | tleft t => 1 + tree_size t
  | sum_match t tl tr => 1 + tree_size t + tree_size tl + tree_size tr

  | typecheck t T => 1 + tree_size t + tree_size T

  | T_unit => 0
  | T_bool => 0
  | T_nat => 0
  | T_refine A p => 1 + tree_size A + tree_size p
  | T_type_refine A B => 1 + tree_size A + tree_size B
  | T_prod A B => 1 + tree_size A + tree_size B
  | T_arrow A B => 1 + tree_size A + tree_size B
  | T_sum A B => 1 + tree_size A + tree_size B
  | T_intersection A B => 1 + tree_size A + tree_size B
  | T_union A B => 1 + tree_size A + tree_size B
  | T_top => 0
  | T_bot => 0
  | T_equiv t1 t2 => 1 + tree_size t1 + tree_size t2
  | T_forall A B => 1 + tree_size A + tree_size B
  | T_exists A B => 1 + tree_size A + tree_size B
  | T_abs T => 1 + tree_size T
  | T_rec n T0 Ts => 1 + tree_size n + tree_size T0 + tree_size Ts
  end.

Fixpoint build_nat (n: nat): tree :=
  match n with
  | 0 => zero
  | S n => succ (build_nat n)
  end.

Lemma build_nat_inj:
  forall n1 n2,
    build_nat n1 = build_nat n2 ->
    n1 = n2.
Proof.
  induction n1; destruct n2; steps.
Qed.

Ltac build_nat_inj :=
  match goal with
  |H: build_nat ?n1 = build_nat ?n2 |- _ => apply build_nat_inj in H
  end.
