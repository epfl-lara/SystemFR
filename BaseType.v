Require Import Coq.Lists.List.
Require Import Coq.Strings.String.

Require Import SystemFR.Trees.
Require Import SystemFR.Syntax.
Require Import SystemFR.Tactics.
Require Import SystemFR.Sets.

Inductive base_type: nat -> tree -> tree -> Prop :=
| BTNat: forall X, base_type X T_nat T_nat
| BTUnit: forall X, base_type X T_unit T_unit
| BTBool: forall X, base_type X T_bool T_bool
| BTSum:
    forall X A B A0 B0,
      base_type X A A0 ->
      base_type X B B0 ->
      base_type X (T_sum A B) (T_sum A0 B0)
| BTProd:
    forall X A B A0 B0,
      base_type X A A0 ->
      base_type X B B0 ->
      base_type X (T_prod A B) (T_prod A0 B0)
| BTId:
    forall X A,
      ~(X ∈ pfv A type_var) ->
      is_erased_type A ->
      base_type X A A
| BTApprox:
    forall X A,
      (* X ∈ pfv A type_var -> *)
      (* We use this rule only when X belongs to pfv A type_var, but this extra assumption is
         not needed for the BaseTypeLemmas proofs *)
      base_type X A T_top.

Hint Constructors base_type: c_base_type.
