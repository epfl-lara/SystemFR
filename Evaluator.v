Require Export SystemFR.Trees.
Require Export SystemFR.Syntax.
Require Export SystemFR.Freshness.
Require Import SystemFR.Notations.

Fixpoint isValue (t: tree) : bool :=
  match t with
    | lvar _ _ => true
    | fvar _ _ => true
    | uu => true
    | ttrue => true
    | tfalse => true
    | pp e1 e2 => andb (isValue e1) (isValue e2)
    | tleft e1 => (isValue e1)
    | tright e1 => (isValue e1)
    | zero => true
    | succ e1 => (isValue e1)
    | _ => false (* Lacks a looooot of terms *) end.

Fixpoint isNat (t : tree) : bool :=
  match t with
    | zero => true
    | succ t1 => (isNat t1)
    | _ => false
end.
 
Fixpoint ss_eval (t: tree) {struct t}: (option tree) :=
  match t with
    | ite ttrue t1 t2 => Some t1
    | ite tfalse t1 t2 => Some t2
    | ite t t1 t2 => option_map (fun e => ite e t1 t2) (ss_eval t)

    | pp e1 e2 => match (isValue e1) with
                   | true => option_map (pp e1) (ss_eval e2)
                   | false => option_map (fun e => pp e e2) (ss_eval e1) end

    | pi1 (pp e1 _ ) => Some e1
    | pi1 t => option_map pi1 (ss_eval t)
    | pi2 (pp _ e2) => Some e2
    | pi2 t => option_map pi2 (ss_eval t)

    | app (lambda x t_body) t2 => match (isValue t2) with
                                  | true => Some (open 0 t_body t2)
                                  | false => option_map (app (lambda x t_body)) (ss_eval t2) end
    | app t1 t2 => match (isValue t1) with
                    | true => option_map (app t1) (ss_eval t2)
                    | false => option_map (fun e => app e t2) (ss_eval t1) end
    (* Fix ? *)
                    
    | tmatch zero t0 _ => Some t0
    | tmatch (succ ts) t0 t1 => match (isValue ts) with
                                | true => match (isNat ts) with
                                           | true => Some (open 0 t1 ts)
                                           | false => None end
                                | false => option_map (fun e => tmatch (succ e) t0 t1) (ss_eval ts) end

    | sum_match (tleft v) tl tr => match (isValue v) with
                                    | true => Some (open 0 tl v)
                                    | false => option_map (fun e => sum_match (tleft e) tl tr) (ss_eval v) end
    | sum_match (tright v) tl tr => match (isValue v) with
                                    | true => Some (open 0 tr v)
                                    | false => option_map (fun e => sum_match (tright e) tl tr) (ss_eval v) end

    | tleft t => option_map tleft (ss_eval t)
    | tright t => option_map tright (ss_eval t)
                           
    | _ => None end.


Fixpoint bs_eval (t: tree): (option tree) :=
  match t with
    | _ => None end.

Search (_ -> option _).
