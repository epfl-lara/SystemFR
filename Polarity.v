Require Import Equations.Equations.

Require Import Omega.


Require Export SystemFR.Syntax.
Require Export SystemFR.SizeLemmas.
Require Export SystemFR.NoTypeFVar.
Require Export SystemFR.AssocList.

Inductive polarity := Positive | Negative.

Definition invert_polarity (p: polarity) :=
  match p with
  | Negative => Positive
  | Positive => Negative
  end.

Definition invert_polarities (m: list (nat * polarity)) := map_values invert_polarity m.

Inductive has_polarities: tree -> list (nat * polarity) -> Prop :=
| PolFVar:
    forall X pols,
      ~((X, Negative) ∈ pols) ->
      has_polarities (fvar X type_var) pols
| PolLVar:
    forall X pols,
      has_polarities (lvar X type_var) pols
| PolNat:
    forall pols,
      has_polarities T_nat pols
| PolUnit:
    forall pols,
      has_polarities T_unit pols
| PolBool:
    forall pols,
      has_polarities T_bool pols
| PolTop:
    forall pols,
      has_polarities T_top pols
| PolBot:
    forall pols,
      has_polarities T_bot pols
| PolArrow:
    forall A B pols,
      has_polarities A (invert_polarities pols) ->
      has_polarities B pols ->
      has_polarities (T_arrow A B) pols
| PolProd:
    forall A B pols,
      has_polarities A pols ->
      has_polarities B pols ->
      has_polarities (T_prod A B) pols
| PolSum:
    forall A B pols,
      has_polarities A pols ->
      has_polarities B pols ->
      has_polarities (T_sum A B) pols
| PolRefine:
    forall T b pols,
      has_polarities T pols ->
      has_polarities (T_refine T b) pols
| PolTypeRefine:
    forall T1 T2 pols,
      has_polarities T1 pols ->
      has_polarities T2 pols ->
      has_polarities (T_type_refine T1 T2) pols
| PolEqual:
    forall t1 t2 pols,
      has_polarities (T_equiv t1 t2) pols
| PolIntersection:
    forall A B pols,
      has_polarities A pols ->
      has_polarities B pols ->
      has_polarities (T_intersection A B) pols
| PolUnion:
    forall A B pols,
      has_polarities A pols ->
      has_polarities B pols ->
      has_polarities (T_union A B) pols
| PolForall:
    forall A B pols,
      has_polarities A (invert_polarities pols) ->
      has_polarities B pols ->
      has_polarities (T_forall A B) pols
| PolExists:
    forall A B pols,
      has_polarities A pols ->
      has_polarities B pols ->
      has_polarities (T_exists A B) pols
| PolAbs:
    forall T pols,
      has_polarities T pols ->
      has_polarities (T_abs T) pols
| PolRec:
    forall n T0 Ts pols,
      has_polarities T0 pols ->
      (exists X,
          ~(X ∈ pfv Ts type_var) /\
          ~(X ∈ support pols) /\
          has_polarities (topen 0 Ts (fvar X type_var)) ((X, Positive) :: pols)) ->
      has_polarities (T_rec n T0 Ts) pols.

Hint Constructors has_polarities: b_polarity.
