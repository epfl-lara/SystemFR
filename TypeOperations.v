Require Import Termination.Trees.

Inductive T_ite (b: tree): tree -> tree -> tree -> Prop :=
| IteUnit:
    T_ite b T_unit T_unit T_unit
| IteBool:
    T_ite b T_bool T_bool T_bool
| IteNat:
    T_ite b T_nat T_nat T_nat
| IteRefine:
    forall t1 t2 T1 T2 T,
      T_ite b T1 T2 T ->
      T_ite b (T_refine T1 t1) (T_refine T2 t2) (T_refine T (ite b t1 t2))
| IteProd:
    forall A1 A2 A B1 B2 B,
      T_ite b A1 A2 A ->
      T_ite b B1 B2 B ->
      T_ite b (T_prod A1 B1) (T_prod A2 B2) (T_prod A B)
| IteArrow:
    forall A1 A2 A B1 B2 B,
      T_ite b A1 A2 A ->
      T_ite b B1 B2 B ->
      T_ite b (T_arrow A1 B1) (T_arrow A2 B2) (T_arrow A B)
| IteSum:
    forall A1 A2 A B1 B2 B,
      T_ite b A1 A2 A ->
      T_ite b B1 B2 B ->
      T_ite b (T_sum A1 B1) (T_sum A2 B2) (T_sum A B)
| IteTLet:
    forall A1 A2 A B1 B2 B t1 t2,
      T_ite b A1 A2 A ->
      T_ite b B1 B2 B ->
      T_ite b (T_let t1 A1 B1) (T_let t2 A2 B2) (T_let (ite b t1 t2) A B)
| IteSingleton:
    forall t t',
      T_ite b (T_singleton t) (T_singleton t') (T_singleton (ite b t t'))
| IteIntersection:
    forall A1 A2 A B1 B2 B,
      T_ite b A1 A2 A ->
      T_ite b B1 B2 B ->
      T_ite b (T_intersection A1 B1) (T_intersection A2 B2) (T_intersection A B)
| IteUnion:
    forall A1 A2 A B1 B2 B,
      T_ite b A1 A2 A ->
      T_ite b B1 B2 B ->
      T_ite b (T_union A1 B1) (T_union A2 B2) (T_union A B)

| IteTop:
    T_ite b T_top T_top T_top
| IteBot:
    T_ite b T_bot T_bot T_bot

| IteEqual:
    forall u1 v1 u2 v2,
      T_ite b (T_equal u1 v1) (T_equal u2 v2) (T_equal (ite b u1 u2) (ite b v1 v2))

| IteForall:
    forall A1 A2 A B1 B2 B,
      T_ite b A1 A2 A ->
      T_ite b B1 B2 B ->
      T_ite b (T_forall A1 B1) (T_forall A2 B2) (T_forall A B)
| IteExists:
    forall A1 A2 A B1 B2 B,
      T_ite b A1 A2 A ->
      T_ite b B1 B2 B ->
      T_ite b (T_exists A1 B1) (T_exists A2 B2) (T_exists A B)
| IteAbs:
    forall T1 T2 T,
      T_ite b T1 T2 T ->
      T_ite b (T_abs T1) (T_abs T2) (T_abs T)
| IteTRec:
    forall n1 T01 Ts1 n2 T02 Ts2 T0 Ts,
      T_ite b T01 T02 T0 ->
      T_ite b Ts1 Ts2 Ts ->
      T_ite b (T_rec n1 T01 Ts1) (T_rec n2 T02 Ts2) (T_rec (ite b n1 n2) T0 Ts).
