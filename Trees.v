Require Import Termination.Tactics.

Inductive fv_tag: Set := term_var | type_var.

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
  | T_refine: tree -> tree -> tree
  | T_let: tree -> tree -> tree -> tree
  | T_singleton: tree -> tree
  | T_intersection: tree -> tree -> tree
  | T_union: tree -> tree -> tree
  | T_top: tree
  | T_bot: tree
  | T_equal: tree -> tree -> tree
  | T_forall: tree -> tree -> tree
  | T_exists: tree -> tree -> tree

  (* terms *)
  | err: tree

  | uu: tree

  | lambda: tree -> tree -> tree
  | notype_lambda: tree -> tree
  | app: tree -> tree -> tree

  | pp: tree -> tree -> tree
  | pi1: tree -> tree
  | pi2: tree -> tree

  | ttrue: tree
  | tfalse: tree
  | ite: tree -> tree -> tree -> tree

  | zero: tree
  | succ: tree -> tree
  | rec: tree -> tree -> tree -> tree -> tree
  | notype_rec: tree -> tree -> tree -> tree
  | tmatch: tree -> tree -> tree -> tree

  | tlet: tree -> tree -> tree -> tree
  | notype_tlet: tree -> tree -> tree

  | trefl: tree
.

Definition term_fvar s := fvar s term_var.
Definition type_fvar s := fvar s type_var.

Hint Unfold term_fvar.
Hint Unfold type_fvar.

Fixpoint is_annotated_term t :=
  match t with
  | fvar y term_var => True
  | lvar _ term_var => True
  | err => True

  | uu => True

  | lambda T t' => is_annotated_type T /\ is_annotated_term t'
  | app t1 t2 => is_annotated_term t1 /\ is_annotated_term t2

  | pp t1 t2 => is_annotated_term t1 /\ is_annotated_term t2
  | pi1 t' => is_annotated_term t'
  | pi2 t' => is_annotated_term t'

  | ttrue => True
  | tfalse => True
  | ite t1 t2 t3 => is_annotated_term t1 /\ is_annotated_term t2 /\ is_annotated_term t3

  | zero => True
  | succ t' => is_annotated_term t'
  | rec T t' t0 ts =>
      is_annotated_type T /\ is_annotated_term t' /\
      is_annotated_term t0 /\ is_annotated_term ts
  | tmatch t' t0 ts => is_annotated_term t' /\ is_annotated_term t0 /\ is_annotated_term ts

  | tlet t1 A t2 => is_annotated_term t1 /\ is_annotated_type A /\ is_annotated_term t2
  | trefl => True
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
  | T_prod A B => is_annotated_type A /\ is_annotated_type B
  | T_arrow A B => is_annotated_type A /\ is_annotated_type B
  | T_let t A B => is_annotated_term t /\ is_annotated_type A /\ is_annotated_type B
  | T_singleton t => is_annotated_term t
  | T_intersection A B => is_annotated_type A /\ is_annotated_type B
  | T_union A B => is_annotated_type A /\ is_annotated_type B
  | T_top => True
  | T_bot => True
  | T_equal t1 t2 => is_annotated_term t1 /\ is_annotated_term t2
  | T_forall A B => is_annotated_type A /\ is_annotated_type B
  | T_exists A B => is_annotated_type A /\ is_annotated_type B
  | _ => False
  end
.


Fixpoint is_erased_term t :=
    match t with
  | fvar y term_var => True
  | lvar _ term_var => True
  | err => True

  | uu => True

  | notype_lambda t' => is_erased_term t'
  | app t1 t2 => is_erased_term t1 /\ is_erased_term t2

  | pp t1 t2 => is_erased_term t1 /\ is_erased_term t2
  | pi1 t' => is_erased_term t'
  | pi2 t' => is_erased_term t'

  | ttrue => True
  | tfalse => True
  | ite t1 t2 t3 => is_erased_term t1 /\ is_erased_term t2 /\ is_erased_term t3

  | zero => True
  | succ t' => is_erased_term t'
  | notype_rec t' t0 ts => is_erased_term t' /\ is_erased_term t0 /\ is_erased_term ts
  | tmatch t' t0 ts => is_erased_term t' /\ is_erased_term t0 /\ is_erased_term ts

  | notype_tlet t1 t2 => is_erased_term t1 /\ is_erased_term t2
  | trefl => True
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
  | T_prod A B => is_erased_type A /\ is_erased_type B
  | T_arrow A B => is_erased_type A /\ is_erased_type B
  | T_let t A B => is_erased_term t /\ is_erased_type A /\ is_erased_type B
  | T_singleton t => is_erased_term t
  | T_intersection A B => is_erased_type A /\ is_erased_type B
  | T_union A B => is_erased_type A /\ is_erased_type B
  | T_top => True
  | T_bot => True
  | T_equal t1 t2 => is_erased_term t1 /\ is_erased_term t2
  | T_forall A B => is_erased_type A /\ is_erased_type B
  | T_exists A B => is_erased_type A /\ is_erased_type B
  | _ => False
  end.


Definition term := { t: tree | is_annotated_term t }.
Definition type := { t: tree | is_erased_type t }.
Definition erased_term := { t: tree | is_erased_term t }.
Definition erased_type := { t: tree | is_erased_type t }.

Definition term_to_tree (t: term) := proj1_sig t.
Definition type_to_tree (t: type) := proj1_sig t.
Definition erased_term_to_tree (t: erased_term) := proj1_sig t.
Definition erased_type_to_tree (t: erased_type) := proj1_sig t.

Coercion term_to_tree: term >-> tree.
Coercion type_to_tree: type >-> tree.
Coercion erased_term_to_tree: erased_term >-> tree.
Coercion erased_type_to_tree: erased_type >-> tree.

Fixpoint tree_size t :=
  match t with
  | fvar _ _ => 0
  | lvar _ _ => 0
  | err => 0

  | uu => 0

  | notype_lambda t' => 1 + tree_size t'
  | lambda T t' => 1 + tree_size T + tree_size t'
  | app t1 t2 => 1 + tree_size t1 + tree_size t2

  | pp t1 t2 => 1 + tree_size t1 + tree_size t2
  | pi1 t' => 1 + tree_size t'
  | pi2 t' => 1 + tree_size t'

  | ttrue => 0
  | tfalse => 0
  | ite t1 t2 t3 => 1 + tree_size t1 + tree_size t2 + tree_size t3

  | zero => 0
  | succ t' =>  1 + tree_size t'
  | notype_rec t' t0 ts =>
      1 + tree_size t' +
      tree_size t0 + tree_size ts
  | rec T t' t0 ts =>
      1 + tree_size T + tree_size t' +
      tree_size t0 + tree_size ts
  | tmatch t' t0 ts => 1 + tree_size t' + tree_size t0 + tree_size ts

  | notype_tlet t1 t2 => 1 + tree_size t1 + tree_size t2
  | tlet t1 A t2 => 1 + tree_size t1 + tree_size A + tree_size t2
  | trefl => 0

  | T_unit => 0
  | T_bool => 0
  | T_nat => 0
  | T_refine A p => 1 + tree_size A + tree_size p
  | T_prod A B => 1 + tree_size A + tree_size B
  | T_arrow A B => 1 + tree_size A + tree_size B
  | T_let t A B => 1 + tree_size t + tree_size A + tree_size B
  | T_singleton t => 1 + tree_size t
  | T_intersection A B => 1 + tree_size A + tree_size B
  | T_union A B => 1 + tree_size A + tree_size B
  | T_top => 0
  | T_bot => 0
  | T_equal t1 t2 => 1 + tree_size t1 + tree_size t2
  | T_forall A B => 1 + tree_size A + tree_size B
  | T_exists A B => 1 + tree_size A + tree_size B
  end.


Ltac destruct_refinements :=
  match goal with
  | t: erased_term |- _ =>
    let pp := fresh "pp" in
    destruct t as [ t pp ]
  | t: erased_type |- _ =>
    let pp := fresh "pp" in
    destruct t as [ t pp ]
  | t: term |- _ =>
    let pp := fresh "pp" in
    destruct t as [ t pp ]
  | t: type |- _ =>
    let pp := fresh "pp" in
    destruct t as [ t pp ]
  end.

Ltac t_ref := repeat step || destruct_refinements.

Notation "[ t ]" := (exist _ t (ltac:( t_ref ) : is_annotated_term t)).
Notation "'#' t '#'" := (exist _ t (ltac:( t_ref ) : is_erased_term t)) (at level 1000).
