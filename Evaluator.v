Require Export SystemFR.Trees.
Require Export SystemFR.Syntax.
Require Export SystemFR.Freshness.


Fixpoint isValue (t: tree) : bool :=
  match t with
    | lvar _ _ => true
    | fvar _ _ => true
    | uu => true
    | tsize e => (isValue e)
    | pp e1 e2 => andb (isValue e1) (isValue e2)
    | _ => false (* Lacks a looooot of terms *) end.

Definition optionApp (t : tree -> tree) (v : option tree) : option tree :=
  match v with
    | None => None
    | Some v' => Some (t v') end.

Fixpoint eval (t: tree): (option tree) :=
  match t with
    | pi1 (pp e1 e2) => Some e1
    | pp e1 e2 => match (isValue e1) with
                   | true => optionApp (pp e1) (eval e2)
                   | false => optionApp (fun e => pp e e2) (eval e1) end
    | _ => None end.

Eval compute in (eval (pi1 (pp uu uu))).
