Require Export SystemFR.Trees.
Require Export SystemFR.Syntax.
Require Export SystemFR.Freshness.
(* Require Import SystemFR.Notations. *)


Fixpoint isValue (t: tree) : bool :=
  match t with
    | lvar _ _ => true
    | fvar _ _ => true
    | uu => true
    | ttrue => true
    | tfalse => true
    | pp e1 e2 => andb (isValue e1) (isValue e2)
    | _ => false (* Lacks a looooot of terms *) end.

Fixpoint ss_eval (t: tree): (option tree) :=
  match t with
    | pi1 (pp e1 e2) => match (isValue e1, isValue e2) with
                         | (true, true) => Some e1
                         | (true, false) => option_map (fun e => pi1 (pp e1 e)) (ss_eval e2)
                         | (false, _) => option_map (fun e => pi1 (pp e e2)) (ss_eval e1)
                       end
    | pp e1 e2 => match (isValue e1) with
                   | true => option_map (pp e1) (ss_eval e2)
                   | false => option_map (fun e => pp e e2) (ss_eval e1) end
    | _ => None end.

Eval compute in (ss_eval (pp (pi1 (pp ttrue uu)) uu)).
Eval compute in (ss_eval (pi1 (pp ttrue uu))).

Search (_ -> option _).
