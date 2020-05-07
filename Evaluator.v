Require Export SystemFR.Trees.
Require Export SystemFR.Syntax.
Require Export SystemFR.TypeErasure.
Require Export SystemFR.Freshness.
Require Export SystemFR.Notations.
Import Notations.UnTyped.
Require Export SystemFR.PrimitiveSize.
Require Export SystemFR.SmallStep.
Require Import Coq.Strings.String.
Open Scope bool_scope.


(* Helpers *)
Fixpoint isNat (t : tree) : bool :=
  match t with
    | zero => true
    | succ t1 => (isNat t1)
    | _ => false
end.
Fixpoint isValue (t: tree) : bool :=
  match t with
    (*| lvar _ _ => true
    | fvar _ _ => true *)
    | uu => true
    | ttrue => true
    | tfalse => true
    | pp e1 e2 => andb (isValue e1) (isValue e2)
    | tleft e1 => (isValue e1)
    | tright e1 => (isValue e1)
    | zero => true
    | succ e1 => (isValue e1)
    | notype_lambda _ => true
    | _ => false end.
Definition getPair t : {t': option (tree*tree) | forall t1 t2, t' = Some (t1, t2) <-> t = pp t1 t2}.
  Proof.
    exists ( match t with
    | pp e1 e2 => Some (e1,e2)
    | _ => None end).
    destruct t; steps.
  Defined.

  Definition getApp t : {t': option tree | forall t1, t' = Some t1 <-> t = notype_lambda t1}.
  Proof.
    exists (match t with
       | notype_lambda body => Some body
       | _ => None end).
    destruct t; steps.
  Defined.  

  Definition getLR t : {t': option tree | forall t1, t' = Some t1 <-> (t = tleft t1 \/ t = tright t1)}.
  Proof.
    exists (match t with
       | tleft t' => Some t'
       | tright t' => Some t'
       | _ => None end).
    destruct t; steps.
  Defined.    


(* Evaluator *)
Fixpoint ss_eval (t: tree) {struct t}: (option tree) :=
  match t with
    | ite ttrue t1 t2 => Some t1
    | ite tfalse t1 t2 => Some t2
    | ite t t1 t2 => option_map (fun e => ite e t1 t2) (ss_eval t)

    | pp e1 e2 => match (isValue e1) with
                   | true => option_map (pp e1) (ss_eval e2)
                   | false => option_map (fun e => pp e e2) (ss_eval e1) end

    | pi1 t => match getPair t with
              | exist _ None _  => option_map pi1 (ss_eval t)
              | exist _ (Some (e1, e2)) _ =>
                if (isValue e1) && (isValue e2)
                then Some e1
                else option_map pi1 (ss_eval t) end

    | pi2 t => match getPair t with
              | exist _ None _ => option_map pi2 (ss_eval t)
              | exist _ (Some (e1, e2)) _ =>
                if (isValue e1) && (isValue e2)
                then Some e2
                else option_map pi2 (ss_eval t) end
                                                                                                       
    | app t1 t2 => match (isValue t1) with
                    | true => match getApp t1 with
                             | exist _ None _ => option_map (app t1) (ss_eval t2) 
                             | exist _ (Some ts) _ =>
                               if (isValue t2)
                               then Some (open 0 ts t2)
                               else option_map (app t1) (ss_eval t2) end
                    | false => option_map (fun e => app e t2) (ss_eval t1) end
                    
    | notype_tfix ts => Some (open 0 (open 1 ts zero) (notype_tfix ts))

    | succ t => option_map succ (ss_eval t)
                          
    | tmatch t1 t0 ts => match t1 with
                       | zero => Some t0
                       | succ t2 =>
                         if (isValue t2)
                         then Some (open 0 ts t2)
                         else option_map (fun e => tmatch e t0 ts) (ss_eval t1)
                       | _ => option_map (fun e => tmatch e t0 ts) (ss_eval t1) end

    | sum_match t tl tr => if (isValue t) then match t with
                                   | tleft v => Some (open 0 tl v)
                                   | tright v => Some (open 0 tr v)
                                   | _ => None end
                          else option_map (fun e => sum_match e tl tr) (ss_eval t)
                            
    | tleft t => option_map tleft (ss_eval t)
    | tright t => option_map tright (ss_eval t)

    | tsize t => if (isValue t) then Some (build_nat (tsize_semantics t)) else (option_map tsize (ss_eval t))
    | boolean_recognizer r t => if (isValue t) then match r with
                                                   | 0 => Some (is_pair t)
                                                   | 1 => Some (is_succ t)
                                                   | 2 => Some (is_lambda t)
                                                   | _ => None end
                               else option_map (boolean_recognizer r) (ss_eval t)
    | _ => None
  end.

Fixpoint ss_eval_n (t : tree) (k: nat) : (option tree) :=
  match k with
    | 0 => Some t
    | S k' => match ss_eval t with
               | Some t' => ss_eval_n t' k'
               | None => Some t end
  end.

Definition eval (t: tree) (k: nat): (option tree) :=
  ss_eval_n (erase_term t) k.


(* Tactics *)
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
                                               
Ltac destruct_sig :=
match goal with
  | H: _ |- context[let _ := getPair ?t in _ ]  => let fresh := fresh "getPair" in destruct (getPair t) (* eqn:fresh *)
  | H: context[getPair ?t = _ ] |- _ => let fresh := fresh "getPair" in destruct (getPair t) (* eqn:fresh *)
  | H: context[_ = getPair ?t ] |- _ => let fresh := fresh "getPair" in destruct (getPair t) (* eqn:fresh *)
  | H: context[getApp ?t = _ ] |- _ => let fresh := fresh "getApp" in destruct (getApp t) (* eqn:fresh *)
  | H: context[_ = getApp ?t ] |- _ => let fresh := fresh "getApp" in destruct (getApp t) (* eqn:fresh *)
end. (* match on type of t = sig *)

Ltac destruct_ss_eval :=
  match goal with
    | H: context[ss_eval ?t] |- _ => destruct (ss_eval t) end.


(* Results *)
Lemma isValueCorrect : forall v, isValue v = true <-> cbv_value v.
Proof.
  split.
  - induction v; repeat step || bools; eauto with values.
  - induction 1; repeat step || bools.
Defined.
Lemma ss_eval_step : forall t t', ss_eval t = Some t' -> isValue t = true -> False.
Proof.
  induction t; repeat step || options.
Qed.
Ltac ss_eval_step :=
  match goal with
  |H: ss_eval ?t1 = Some ?t2 |- _ => poseNew (Mark (t1, t2) "ss_eval_step_h");
                                   pose proof  (ss_eval_step _ _ H) end.



Lemma ss_eval_correct2: forall t t',(pfv t term_var = nil) -> scbv_step t t' ->  ss_eval t = Some t'.
  intros.
  induction H0 ;
    repeat light || options || invert_constructor_equalities || ss_eval_step || destruct_sig || instantiate_eq_refl || list_utils || bools || rewrite <- isValueCorrect in * ||  eauto using ss_eval_step, fv_nil_top_level_var with smallstep values || destruct_match.
Qed.

Lemma ss_eval_correct1: forall t t', ss_eval t = Some t' -> (pfv t term_var = nil) -> scbv_step t t'.
Proof.
  induction t; intros ; repeat light ; destruct_ss_eval ; repeat light || options || bools || list_utils || instantiate_eq_refl || invert_constructor_equalities || rewrite isValueCorrect in * || destruct_sig || congruence ||  step_inversion cbv_value || destruct_match ; eauto using ss_eval_step, fv_nil_top_level_var with smallstep values . Qed.


(* Extraction *)
Require Extraction.

Extraction Language Ocaml.
Set Extraction AccessOpaque.


Extraction "evaluator.ml" eval. 
    
