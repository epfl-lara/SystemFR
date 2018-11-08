Require Import Termination.ListUtils.
Require Import Termination.Sets.
Require Import Termination.AssocList.
Require Import Termination.Tactics.

Require Import Coq.Strings.String.
Require Import Coq.Lists.List.

Require Import PeanoNat.

(* locally nameless representation *)
Inductive term: Set :=
  (* term variable *)
  | fvar: nat -> term

  (* types *)
  | T_var: nat -> term
  | T_nat: term
  | T_unit: term
  | T_bool: term
  | T_arrow: term -> term -> term
  | T_prod: term -> term -> term
  | T_refine: term -> term -> term
  | T_let: term -> term -> term -> term
  | T_singleton: term -> term
  | T_intersection: term -> term -> term
  | T_union: term -> term -> term
  | T_top: term
  | T_bot: term
  | T_equal: term -> term -> term
  | T_forall: term -> term -> term
  | T_exists: term -> term -> term

  (* terms *)
  | lvar: nat -> term
  | err: term

  | uu: term

  | lambda: term -> term -> term
  | app: term -> term -> term

  | pp: term -> term -> term
  | pi1: term -> term
  | pi2: term -> term

  | ttrue: term
  | tfalse: term
  | ite: term -> term -> term -> term

  | zero: term
  | succ: term -> term
  | rec: term -> term -> term -> term -> term
  | tmatch: term -> term -> term -> term

  | tlet: term -> term -> term -> term

  | trefl: term
.


Fixpoint fv (t: term): set nat :=
  match t with
  | fvar y => singleton y
  | lvar _ => empty
  | err => empty

  | uu => empty

  | lambda T t' => fv T ++ fv t'
  | app t1 t2 => fv t1 ++ fv t2

  | pp t1 t2 => fv t1 ++ fv t2
  | pi1 t' => fv t'
  | pi2 t' => fv t'

  | ttrue => empty
  | tfalse => empty
  | ite t1 t2 t3 => fv t1 ++ fv t2 ++ fv t3

  | zero => empty
  | succ t' => fv t'
  | rec T t' t0 ts => fv T ++ fv t' ++ fv t0 ++ fv ts
  | tmatch t' t0 ts => fv t' ++ fv t0 ++ fv ts

  | tlet t1 A t2 => fv t1 ++ fv A ++  fv t2
  | trefl => empty

  | T_var y => nil
  | T_unit => nil
  | T_bool => nil
  | T_nat => nil
  | T_refine A p => fv A ++ fv p
  | T_prod A B => fv A ++ fv B
  | T_arrow A B => fv A ++ fv B
  | T_let t A B => fv t ++ fv A ++ fv B
  | T_singleton t => fv t
  | T_intersection A B => fv A ++ fv B
  | T_union A B => fv A ++ fv B
  | T_top => nil
  | T_bot => nil
  | T_equal t1 t2 => fv t1 ++ fv t2
  | T_forall A B => fv A ++ fv B
  | T_exists A B => fv A ++ fv B
  end.

Definition tvar_list := list nat.
Definition context: Type := list (nat * term).

Fixpoint fv_context gamma :=
  match gamma with
  | nil => nil
  | (x,T) :: gamma' => x :: fv T ++ fv_context gamma'
  end.

Lemma fv_context_append:
  forall gamma1 gamma2,
    fv_context (gamma1 ++ gamma2) = fv_context gamma1 ++ fv_context gamma2.
Proof.
  induction gamma1; repeat step || rewrite app_assoc_reverse.
Qed.

Hint Rewrite fv_context_append: blistutils.

Fixpoint fv_range (m: list (nat * term)) :=
  match m with
  | nil => empty
  | (x,t) :: m' => fv t ++ fv_range m'
  end.

Fixpoint closed_mapping (m: list (nat * term)): Prop :=
  match m with
  | nil => True
  | (x,t) :: m' => fv t = nil /\ closed_mapping m'
  end.

Fixpoint substitute t (l: list (nat * term)): term :=
  match t with
  | fvar x =>
    match lookup Nat.eq_dec l x with
    | None => t
    | Some e => e
    end

  (* substitution is only for term variables *)
  | T_var _ => t

  | lvar _ => t
  | err => t

  | uu => t

  | lambda T t' => lambda (substitute T l) (substitute t' l)
  | app t1 t2 => app (substitute t1 l) (substitute t2 l)

  | pp t1 t2 => pp (substitute t1 l) (substitute t2 l)
  | pi1 t' => pi1 (substitute t' l)
  | pi2 t' => pi2 (substitute t' l)

  | ttrue => t
  | tfalse => t
  | ite t1 t2 t3 => ite (substitute t1 l) (substitute t2 l) (substitute t3 l)

  | zero => t
  | succ t' => succ (substitute t' l)
  | rec T t' t1 t2 => rec (substitute T l) (substitute t' l) (substitute t1 l) (substitute t2 l)
  | tmatch t' t1 t2 => tmatch (substitute t' l) (substitute t1 l) (substitute t2 l)

  | tlet t1 T t2 => tlet (substitute t1 l) (substitute T l) (substitute t2 l)
  | trefl => t

  | T_unit => t
  | T_bool => t
  | T_nat => t
  | T_prod T1 T2 => T_prod (substitute T1 l) (substitute T2 l)
  | T_arrow T1 T2 => T_arrow (substitute T1 l) (substitute T2 l)
  | T_refine T p => T_refine (substitute T l) (substitute p l)
  | T_let t A B => T_let (substitute t l) (substitute A l) (substitute B l)
  | T_singleton t => T_singleton (substitute t l)
  | T_intersection T1 T2 => T_intersection (substitute T1 l) (substitute T2 l)
  | T_union T1 T2 => T_union (substitute T1 l) (substitute T2 l)
  | T_top => t
  | T_bot => t
  | T_equal t1 t2 => T_equal (substitute t1 l) (substitute t2 l)
  | T_forall T1 T2 => T_forall (substitute T1 l) (substitute T2 l)
  | T_exists T1 T2 => T_exists (substitute T1 l) (substitute T2 l)
  end.

Fixpoint substitute_context (gamma: context) (l: list (nat * term)): context :=
  match gamma with
  | nil => nil
  | (x,T) :: gamma' => (x, substitute T l) :: substitute_context gamma' l
  end.

Fixpoint open (k: nat) (t rep: term) :=
  match t with
  | fvar _ => t
  | lvar i => if (Nat.eq_dec k i) then rep else t
  | err => t

  | lambda T t' => lambda (open k T rep) (open (S k) t' rep)
  | app t1 t2 => app (open k t1 rep) (open k t2 rep)

  | uu => t

  | pp t1 t2 => pp (open k t1 rep) (open k t2 rep)
  | pi1 t => pi1 (open k t rep)
  | pi2 t => pi2 (open k t rep)

  | ttrue => t
  | tfalse => t
  | ite t1 t2 t3 => ite (open k t1 rep) (open k t2 rep) (open k t3 rep)

  | zero => t
  | succ t' => succ (open k t' rep)
  | rec T t' t1 t2 =>
    rec (open (S k) T rep)
        (open k t' rep)
        (open k t1 rep)
        (open (S (S k)) t2 rep)
  | tmatch t' t1 t2 =>
    tmatch
        (open k t' rep)
        (open k t1 rep)
        (open (S k) t2 rep)

  | tlet t1 T t2 =>
    tlet (open k t1 rep)
         (open k T rep)
         (open (S k) t2 rep)
  | trefl => t

  | T_var _ => t
  | T_unit => t
  | T_bool => t
  | T_nat => t
  | T_prod T1 T2 => T_prod (open k T1 rep) (open (S k) T2 rep)
  | T_arrow T1 T2 => T_arrow (open k T1 rep) (open (S k) T2 rep)
  | T_refine T p => T_refine (open k T rep) (open (S k) p rep)
  | T_let t A B => T_let (open k t rep) (open k A rep) (open (S k) B rep)
  | T_singleton t => T_singleton (open k t rep)
  | T_intersection T1 T2 => T_intersection (open k T1 rep) (open k T2 rep)
  | T_union T1 T2 => T_union (open k T1 rep) (open k T2 rep)
  | T_top => t
  | T_bot => t
  | T_equal t1 t2 => T_equal (open k t1 rep) (open k t2 rep)
  | T_forall T1 T2 => T_forall (open k T1 rep) (open (S k) T2 rep)
  | T_exists T1 T2 => T_exists (open k T1 rep) (open (S k) T2 rep)
  end.

Fixpoint wf t k :=
  match t with
  | fvar _ => True
  | lvar i => i < k
  | err => True

  | uu => True

  | lambda T t' => wf T k /\ wf t' (S k)
  | app t1 t2 => wf t1 k /\ wf t2 k

  | pp t1 t2 => wf t1 k /\ wf t2 k
  | pi1 t => wf t k
  | pi2 t => wf t k

  | ttrue => True
  | tfalse => True
  | ite t1 t2 t3 => wf t1 k /\ wf t2 k /\ wf t3 k

  | zero => True
  | succ t' => wf t' k
  | rec T t' t1 t2 =>
      wf T (S k) /\
      wf t' k /\
      wf t1 k /\
      wf t2 (S (S k))
  | tmatch t' t1 t2 =>
      wf t' k /\
      wf t1 k /\
      wf t2 (S k)

  | tlet t1 T t2 => wf t1 k /\ wf T k /\ wf t2 (S k)
  | trefl => True

  | T_var _ => True
  | T_unit => True
  | T_bool => True
  | T_nat => True
  | T_prod T1 T2 => wf T1 k /\ wf T2 (S k)
  | T_arrow T1 T2 => wf T1 k /\ wf T2 (S k)
  | T_refine T p => wf T k /\ wf p (S k)
  | T_let t A B => wf t k /\ wf A k /\ wf B (S k)
  | T_singleton t => wf t k
  | T_intersection T1 T2 => wf T1 k /\ wf T2 k
  | T_union T1 T2 => wf T1 k /\ wf T2 k
  | T_top => True
  | T_bot => True
  | T_equal t1 t2 => wf t1 k /\ wf t2 k
  | T_forall T1 T2 => wf T1 k /\ wf T2 (S k)
  | T_exists T1 T2 => wf T1 k /\ wf T2 (S k)
  end.

Fixpoint wfs (gamma: list (nat * term)) k :=
  match gamma with
  | nil => True
  | (x,A) :: gamma' => wf A k /\ wfs gamma' k
  end.

Ltac tequality :=
  match goal with
  | |- app _ _ = app _ _ => f_equal
  | |- pp _ _ = pp _ _ => f_equal
  | |- lambda _ _ = lambda _ _ => f_equal
  | |- pi1 _ = pi1 _ => f_equal
  | |- pi2 _ = pi2 _ => f_equal
  | |- succ _ = succ _ => f_equal
  | |- ite _ _ _ = ite _ _ _ => f_equal
  | |- rec _ _ _ _ = rec _ _ _ _ => f_equal
  | |- tmatch _ _ _ = tmatch _ _ _ => f_equal
  | |- tlet _ _ _ = tlet _ _ _ => f_equal

  | |- T_refine _ _ = T_refine _ _ => f_equal
  | |- T_prod _ _ = T_prod _ _ => f_equal
  | |- T_arrow _ _ = T_arrow _ _ => f_equal
  | |- T_let _ _ _ = T_let _ _ _ => f_equal
  | |- T_singleton _ = T_singleton _ => f_equal
  | |- T_intersection _ _ = T_intersection _ _ => f_equal
  | |- T_union _ _ = T_union _ _ => f_equal
  | |- T_equal _ _ = T_equal _ _ => f_equal
  | |- T_forall _ _ = T_forall _ _ => f_equal
  | |- T_exists _ _ = T_exists _ _ => f_equal
 end.

Lemma fold_open_arrow:
  forall T1 T2 rep,
    T_arrow (open 0 T1 rep) (open 1 T2 rep) = open 0 (T_arrow T1 T2) rep.
Proof.
  reflexivity.
Qed.

Lemma fold_open_refine:
  forall T p rep,
    T_refine (open 0 T rep) (open 1 p rep) = open 0 (T_refine T p) rep.
Proof.
  reflexivity.
Qed.
