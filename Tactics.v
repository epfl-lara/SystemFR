Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Omega.
Require Import Psatz.

Open Scope string.

Hint Extern 50 => omega: omega.
Hint Extern 50 => lia: lia.
Hint Extern 50 => cbn: cbn.
Hint Extern 50 => cbn; intuition auto: cbn_intuition.

Ltac destruct_and :=
  match goal with
  | H: _ /\ _ |- _ => destruct H
  end.

Ltac destruct_or :=
  match goal with
  | H: _ \/ _ |- _ => destruct H
  end.

Ltac success t := (t; fail) || (t; []).

Ltac light :=
  (intros) ||
  (intuition auto) ||
  (congruence) ||
  (subst) ||
  (cbn in *) ||
  (autounfold in *)
.

Ltac basic_rewrites :=
  (autorewrite with list in *; eauto; fail) ||
  (autorewrite with list in *; eauto; [ idtac ]) ||
  (autorewrite with core in *; eauto; fail) ||
  (autorewrite with core in *; eauto; [ idtac ]).

Ltac light2 := basic_rewrites || firstorder.

Ltac t_equality :=
  match goal with
  | |- ?F _ = ?F _ => is_constructor F; f_equal
  | |- ?F _ _ = ?F _ _ => is_constructor F; f_equal
  | |- ?F _ _ _ = ?F _ _ _ => is_constructor F; f_equal
  | |- ?F _ _ _ _ = ?F _ _ _ _ => is_constructor F; f_equal
  | |- ?F _ _ _ _ _ = ?F _ _ _ _ _ => is_constructor F; f_equal
  | |- ?F _ _ _ _ _ _ = ?F _ _ _ _ _ _ => is_constructor F; f_equal
  end.

(** Taken from Cpdt **)
(** Succeed iff [x] is in the list [ls], represented with left-associated nested tuples. *)
Ltac inList x ls :=
  match ls with
    | x => idtac
    | (_, x) => idtac
    | (?LS, _) => inList x LS
  end.

(** Taken from Cpdt **)
Ltac step_inversion predicates :=
  let invert H F :=
    inList F predicates;
      (inversion H; fail) ||
      (inversion H; [ idtac ]; clear H)
  in
  match goal with
    | [ H: ?F _ |- _ ] => invert H F
    | [ H: ?F _ _ |- _ ] => invert H F
    | [ H: ?F _ _ _ |- _ ] => invert H F
    | [ H: ?F _ _ _ _ |- _ ] => invert H F
    | [ H: ?F _ _ _ _ _ |- _ ] => invert H F
    | [ H: ?F _ _ _ _ _ _ |- _ ] => invert H F
  end.

Ltac containsExistential := match goal with
  | [ |- ?G ]  => has_evar G
  end.

Ltac noExistential := tryif containsExistential then fail else idtac.

Ltac removeDuplicateProps := match goal with
  | [ H1: ?P, H2: ?P |- _ ] =>
    match type of P with
    | Prop => idtac
    end;  clear H2
  end.

Ltac isThere P := match goal with
  | H: ?Q |- _ => unify P Q
(*  | |- ?Q => unify P Q *)
  end.

Ltac notThere P := tryif (isThere P) then fail else idtac.
Ltac not_var P := tryif (is_var P) then fail else idtac.
Ltac noUnify P Q := tryif (unify P Q) then fail else idtac.

Lemma strong_and:
  forall (A B: Prop), A -> (A -> B) -> (exists _: A, B).
Proof.
  eauto.
Qed.

Ltac step_gen := match goal with
  | _ => progress light
  | _ => apply strong_and
  | H: exists x, _ |- _ =>
    let x' := fresh x in
    destruct H as [ x' ]
  | [ p: ?A*?B |- _ ] => destruct p
  | [ H: (_,_) = (_,_) |- _ ] => inversion H; clear H
  | [ H: context[Nat.eq_dec ?U ?V] |- _ ] => destruct (Nat.eq_dec U V)
  | H: _ |- _ => injection H; clear H
  | |- NoDup _ => constructor
  | H: forall a, _ -> _ |- _ => pose proof (H _ eq_refl); clear H
  | H: forall a b, _ -> _ |- _ => pose proof (H _ _ eq_refl); clear H
  | H: forall a b c, _ -> _ |- _ => pose proof (H _ _ _ eq_refl); clear H
  | H: forall a b c d, _ -> _ |- _ => pose proof (H _ _ _ _ eq_refl); clear H
  | H: forall a b c d e, _ -> _ |- _ => pose proof (H _ _ _ _ _ eq_refl); clear H
  | [ |- context[match ?t with _ => _ end]] =>
      let matched := fresh "matched" in
      destruct t eqn:matched
  | [ H: context[match ?t with _ => _ end] |- _ ] =>
      let matched := fresh "matched" in
      destruct t eqn:matched
  | _ => removeDuplicateProps
  | H := _: ?T |- _ => noUnify T string; clearbody H
  | _ => noExistential; solve [ constructor ]
  | _ => noExistential; solve [ constructor; constructor ]
  end.

Ltac step := step_gen || step_inversion (List.Forall, List.In).
Ltac steps := repeat step.

Ltac termNotThere p :=
  let P := type of p in
    tryif (isThere P) then fail else idtac.

Ltac poseNew E := termNotThere E; pose proof E.

(* Marking contexts to avoid applying the same step twice *)
(* Used to ensure termination of some tactics *)
Inductive Marked {T}: T -> string -> Type :=
| Mark: forall t s, Marked t s
.

Ltac clear_marked :=
  repeat match goal with
         | H: Marked _ _ |- _ => clear H
         end.

Notation "'internal'" := (Marked _ _) (at level 50).

(* tactic to add hypotheses from existing ones *)
Ltac forall_starts_with F G :=
  match F with
  | forall _, ?R => forall_starts_with R G
  | ?P -> _ => unify P G
  end.

Ltac applyHyp H1 H2 :=
  (termNotThere (H1 H2); pose (H1 H2)) ||
  (termNotThere (H1 _ H2); pose (H1 _ H2)) ||
  (termNotThere (H1 _ _ H2); pose (H1 _ _ H2)) ||
  (termNotThere (H1 _ _ _ H2); pose (H1 _ _ _ H2)) ||
  (termNotThere (H1 _ _ _ _ H2); pose (H1 _ _ _ _ H2)) ||
  (termNotThere (H1 _ _ _ _ _ H2); pose (H1 _ _ _ _ _ H2)) ||
  (termNotThere (H1 _ _ _ _ _ _ H2); pose (H1 _ _ _ _ _ _ H2)) ||
  (termNotThere (H1 _ _ _ _ _ _ _ H2); pose (H1 _ _ _ _ _ _ _ H2)).

Ltac createHypothesis := match goal with
                         | [ H1: ?F, H2: ?P |- _ ] =>
                           poseNew (Mark (F,P,H2) "createHypothesis");
                           forall_starts_with F P;
                           applyHyp H1 H2
                         end.

Ltac createHypotheses := repeat createHypothesis.

Ltac define m t :=
  let M := fresh "M" in
  pose t as m;
  assert (t = m) as M; auto;
  pose (Mark M "remembering m").

Lemma idd: forall s: nat, exists s', s' = s.
Proof. eauto. Qed.


Ltac define2 m t :=
  let H := fresh "Heq" in
  destruct (idd t) as [ m H ].

Ltac define3 m t :=
  let M := fresh "M" in
  pose t as m;
  assert (m = t) as M; auto.

Hint Extern 50 => apply False_ind: exfalso.
(** Useful shorthands that work on any hypothesis in the the context *)

Ltac apply_any :=
  match goal with
  | H: _ |- _ => apply H
  end.

Ltac rewrite_any :=
  match goal with
  | H: _ |- _ => rewrite H in *
  end.

Ltac erewrite_any :=
  match goal with
  | H: _ |- _ => erewrite H in *
  end.

Ltac rewrite_back_any :=
  match goal with
  | H: _ |- _ => rewrite <- H in *
  end.

Ltac eapply_any :=
  match goal with
  | H: _ |- _ => eapply H
  end.

Ltac apply_anywhere f :=
  match goal with
  | H: _ |- _ => apply f in H
  end.

Ltac eapply_anywhere f :=
  match goal with
  | H: _ |- _ => eapply f in H
  end.

Ltac rewrite_anywhere f :=
  match goal with
  | H: _ |- _ => rewrite f in H
  end.

Ltac erewrite_anywhere f :=
  match goal with
  | H: _ |- _ => erewrite f in H
  end.

Ltac instantiate_any :=
  match goal with
  | H1: forall x, _ -> _, H2: _ |- _ =>
    poseNew (Mark (H1, H2) "instantiation");
    pose proof (H1 _ H2)
  | H1: forall x y, _ -> _, H2: _ |- _ =>
    poseNew (Mark (H1, H2) "instantiation");
    pose proof (H1 _ _ H2)
  | H1: forall x y z, _ -> _, H2: _ |- _ =>
    poseNew (Mark (H1, H2) "instantiation");
    pose proof (H1 _ _ _ H2)
  end.

Hint Extern 50 => apply_any: apply_any.
Hint Extern 50 => eapply_any: eapply_any.
Hint Extern 50 => congruence: bcongruence.
Hint Extern 50 => steps: step_tactic.

Ltac top_level_unfold F :=
  match goal with
  | H: ?f |- _ => unify f F; unfold F in H
  | H: ?f _ |- _ => unify f F; unfold F in H
  | H: ?f _ _ |- _ => unify f F; unfold F in H
  | H: ?f _ _ _ |- _ => unify f F; unfold F in H
  | H: ?f _ _ _ _ |- _ => unify f F; unfold F in H
  | H: ?f _ _ _ _ _ |- _ => unify f F; unfold F in H
  end.

Ltac inversion_solve :=
  match goal with
  | H: _ |- _ => solve [ inversion H; steps ]
  end.

Lemma rewrite_truth:
  forall (P: Prop), P -> (P <-> True).
Proof.
  steps.
Qed.

Ltac rewrite_truth l :=
  rewrite (rewrite_truth _ l) in * by (eauto using l).

Ltac force_invert P :=
  match goal with
  | H: ?F _ |- _ => unify F P; inversion H; clear H
  | H: ?F _ _ |- _ => unify F P; inversion H; clear H
  | H: ?F _ _ _ |- _ => unify F P; inversion H; clear H
  | H: ?F _ _ _ _ |- _ => unify F P; inversion H; clear H
  | H: ?F _ _ _ _ _ |- _ => unify F P; inversion H; clear H
  | H: ?F _ _ _ _ _ _ |- _ => unify F P; inversion H; clear H
  end.

Hint Rewrite Bool.andb_true_iff: bools.
Hint Rewrite Bool.andb_false_iff: bools.
Hint Rewrite Bool.orb_true_iff: bools.
Hint Rewrite Bool.orb_false_iff: bools.
Hint Rewrite Bool.negb_true_iff: bools.
Hint Rewrite Bool.negb_false_iff: bools.
Ltac bools :=
  autorewrite with bools in *.


Ltac options :=
unfold option_map in *.

Ltac invert_constructor_equalities :=
match goal with
| H: ?F _ = ?F _ |- _ => is_constructor F; inversion H; clear H
| H: ?F _ _ = ?F _ _ |- _ => is_constructor F; inversion H; clear H
| H: ?F _ _ _ = ?F _ _ _ |- _ => is_constructor F; inversion H; clear H
| H: ?F _ _ _ _ = ?F _ _ _ _ |- _ => is_constructor F; inversion H; clear H
| H: ?F _ _ _ _ _ = ?F _ _ _ _ _ |- _ => is_constructor F; inversion H; clear H
| H: ?F _ _ _ _ _ _ = ?F _ _ _ _ _ _ |- _ => is_constructor F; inversion H; clear H
end.

Ltac custom_light :=
  (intros) ||
  (subst).

Ltac destruct_match :=
match goal with
| [ |- context[match ?t with _ => _ end]] =>
let matched := fresh "matched" in
destruct t eqn:matched
| [ H: context[match ?t with _ => _ end] |- _ ] =>
let matched := fresh "matched" in
destruct t eqn:matched
end.



Ltac instantiate_eq_refl :=
match goal with
| H: _ |- _ => pose proof (proj1 (H _) eq_refl); clear H
| H: _ |- _ => pose proof (proj2 (H _) eq_refl); clear H
| H: _ |- _ => pose proof (H _ eq_refl); clear H
| H: _ |- _ => pose proof (H _ _ eq_refl ); clear H
| H: _ |- _ => pose proof (proj1 (H _ _ ) eq_refl); clear H
| H: _ |- _ => pose proof (proj2 (H _ _ ) eq_refl); clear H
| H: _ |- _ => pose proof (H _ _ _ eq_refl); clear H
| H: _ |- _ => pose proof (H _ _ _ _ eq_refl); clear H
| H: _ |- _ => pose proof (H _ _ _ _ _ eq_refl); clear H
| H: _ |- _ => pose proof (H _ _ _ _ _ _ eq_refl); clear H
end.
