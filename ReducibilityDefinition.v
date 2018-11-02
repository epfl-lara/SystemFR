Require Import Coq.Strings.String.

Require Import Termination.Syntax.
Require Import Termination.ListUtils.
Require Import Termination.Tactics.
Require Import Termination.AssocList.
Require Import Termination.WFLemmas.
Require Import Termination.TermProperties.
Require Import Termination.SmallStep.
Require Import Termination.TermList.
Require Import Termination.SizeLemmas.
Require Import Termination.Equivalence.
Require Import Termination.TypeForm.

Require Import Equations.Equations.

Require Import Omega.

Definition reduces_to (P: term -> Prop) (t: term) :=
  wf t 0 /\
  fv t = nil /\
  exists t',
    star small_step t t' /\
    P t'.

Equations (noind) reducible_values (v: term) (T: term): Prop :=
  reducible_values v T by rec (size T) lt :=

  reducible_values v T_type := False;

  reducible_values v T_unit := v = uu;
                                 
  reducible_values v T_bool := v = ttrue \/ v = tfalse;

  reducible_values v T_nat := is_nat_value v; 
    
  reducible_values v (T_arrow A B) :=
    (* exists _: type_form B, *)
      is_value v /\
      fv v = nil /\
      wf v 0 /\
      forall a (p: term_form a),
        reducible_values a A ->
        reduces_to (fun t => reducible_values t (open 0 B a)) (app v a);

  reducible_values v (T_prod A B) :=
     exists a b  (p: term_form a) (* (_: type_form B) *),
       v = pp a b /\
       reducible_values a A /\
       reducible_values b (open 0 B a);

  reducible_values v (T_refine T p) :=
    reducible_values v T /\
    wf p 1 /\
    star small_step (open 0 p v) ttrue;

  reducible_values v (T_let a A B) :=
    exists a'  (p: term_form a') (*_: type_form B *),
      is_value a' /\
      star small_step a a' /\
      reducible_values v (open 0 B a');

  reducible_values v (T_singleton t) :=
    is_value v /\
    fv v = nil /\
    wf v 0 /\
    star small_step t v;
         
  reducible_values v (T_intersection A B) :=
    reducible_values v A /\
    reducible_values v B;
         
  reducible_values v (T_union A B) :=
    reducible_values v A \/
    reducible_values v B;

  reducible_values v T_top :=
      is_value v /\ fv v = nil /\ wf v 0 ;

  reducible_values v T_bot := False;

  reducible_values v (T_equal t1 t2) :=
      v = trefl /\ equivalent t1 t2;

  reducible_values v (T_forall A B) :=
    (* exists _: type_form B, *)
      is_value v /\
      fv v = nil /\
      wf v 0 /\
      forall a (p: term_form a),
        reducible_values a A ->
        reducible_values v (open 0 B a);

  reducible_values v (T_exists A B) :=
    exists a  (p: term_form a) (* _: type_form B *),
      reducible_values a A /\
      reducible_values v (open 0 B a);

  reducible_values v T := False
.


Solve Obligations with (repeat step || autorewrite with bsize; omega).

Definition reducible (t: term) (T: term): Prop :=
  reduces_to (fun t => reducible_values t T) t.

Definition open_reducible (gamma: context) t T: Prop :=
  forall l, satisfies reducible_values gamma l ->
       reducible (substitute t l) (substitute T l).

Lemma reducibility_rewrite:
  forall t T,
    reduces_to (fun t => reducible_values t T) t =
    reducible t T.
Proof.
  reflexivity.
Qed.

Lemma obvious_reducible:
  forall t T,
    reducible t T ->
    exists t',
      star small_step t t' /\
      reducible_values t' T. 
Proof.
  unfold reducible, reduces_to; steps.
Qed.

Ltac simp_red :=
  repeat (
      rewrite reducible_values_equation_1 in * ||
      rewrite reducible_values_equation_2 in * ||
      rewrite reducible_values_equation_3 in * ||
      rewrite reducible_values_equation_4 in * ||
      rewrite reducible_values_equation_5 in * ||
      rewrite reducible_values_equation_6 in * ||
      rewrite reducible_values_equation_7 in * ||
      rewrite reducible_values_equation_8 in * ||
      rewrite reducible_values_equation_9 in * ||
      rewrite reducible_values_equation_10 in * ||
      rewrite reducible_values_equation_11 in * ||
      rewrite reducible_values_equation_12 in * ||
      rewrite reducible_values_equation_13 in * ||
      rewrite reducible_values_equation_14 in * ||
      rewrite reducible_values_equation_15 in * ||
      rewrite reducible_values_equation_16 in * ||
      rewrite reducible_values_equation_17 in * ||
      rewrite reducible_values_equation_18 in * ||
      rewrite reducible_values_equation_19 in * ||
      rewrite reducible_values_equation_20 in * ||
      rewrite reducible_values_equation_21 in * ||
      rewrite reducible_values_equation_22 in * ||
      rewrite reducible_values_equation_23 in * ||
      rewrite reducible_values_equation_24 in * ||
      rewrite reducible_values_equation_25 in * ||
      rewrite reducible_values_equation_26 in * ||
      rewrite reducible_values_equation_27 in * ||
      rewrite reducible_values_equation_28 in * ||
      rewrite reducible_values_equation_29 in * ||
      rewrite reducible_values_equation_30 in * ||
      rewrite reducible_values_equation_31 in * ||
      rewrite reducible_values_equation_32 in * ||
      rewrite reducible_values_equation_33 in * ||
      rewrite reducible_values_equation_34 in *
  ).


Ltac top_level_unfold :=
  match goal with
  | H: reducible _ _ |- _ => unfold reducible, reduces_to in H
  end.
