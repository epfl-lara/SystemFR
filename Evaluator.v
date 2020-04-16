Require Export SystemFR.Trees.
Require Export SystemFR.Syntax.
Require Export SystemFR.Freshness.
Require Export SystemFR.Notations.
Import Notations.UnTyped.
Require Export SystemFR.PrimitiveSize.

Fixpoint isNat (t : tree) : bool :=
  match t with
    | zero => true
    | succ t1 => (isNat t1)
    | _ => false
end.
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
    | succ e1 => (isNat e1)
    | lambda _ _ => true
    | notype_lambda _ => true
    | err _ => true
    | notype_err => true
    | tfix _ _  => true
    | _ => false end.
 
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

    | lambda x t_body => Some (notype_lambda t_body) (* remove type annotation *)
    | app (notype_lambda t_body) t2 => match (isValue t2) with
                                  | true => Some (open 0 t_body t2)
                                  | false => option_map (app (notype_lambda t_body)) (ss_eval t2) end
    | app t1 t2 => match (isValue t2) with
                    | false => option_map (app t1) (ss_eval t2)
                    | true => option_map (fun e => app e t2) (ss_eval t1) end

    | notype_tfix t_body => Some (open 0 t_body (notype_tfix t_body))

    | notype_tlet t1 t_body => match isValue t1 with
                               | true => Some (open 0 t_body t1)
                               | false => option_map (fun e => notype_tlet e t_body) (ss_eval t1) end

    | succ t => option_map succ (ss_eval t)
    | tmatch zero t0 _ => Some t0
    | tmatch (succ ts) t0 t1 => match (isNat ts) with
                                | true => Some (open 0 t1 ts)
                                | false => option_map (fun e => tmatch (succ e) t0 t1) (ss_eval ts) end
    | tmatch ts t0 t1 => match (isValue ts) with
                          | true => None
                          | false => option_map (fun e => tmatch e t0 t1) (ss_eval ts) end

    | sum_match (tleft v) tl tr => match (isValue v) with
                                    | true => Some (open 0 tl v)
                                    | false => option_map (fun e => sum_match (tleft e) tl tr) (ss_eval v) end
    | sum_match (tright v) tl tr => match (isValue v) with
                                    | true => Some (open 0 tr v)
                                    | false => option_map (fun e => sum_match (tright e) tl tr) (ss_eval v) end

    | tleft t => option_map tleft (ss_eval t)
    | tright t => option_map tright (ss_eval t)

    | tsize t => Some (build_nat (tsize_semantics t))
    | _ => None
  end.

Fixpoint ss_eval_n (t : tree) (k: nat) : (option tree) :=
  match k with
    | 0 => Some t
    | S k' => match ss_eval t with
               | Some t' => ss_eval_n t' k'
               | None => None end
               end.


Definition example1 :=
[|
 let plus := (def_rec f x y => (
     match x with
      | 0 => y
      | s x' => s ((f x') y)
     end))
 in let fibo := (def_rec f n => (
        match n with
         | 0 => 1
         | s n' => (
             match n' with
              | 0 => 1
              | s n'' => (plus (f n')) (f n'')
             end)
        end))
    in
    (fibo (s (s (s (s 1)))))
 |].

Example fibo4 : (ss_eval_n example1 141) =  Some (succ (succ (succ (succ (succ (succ (succ (succ zero)))))))).
Proof. compute. reflexivity. Qed.

Definition example2 :=
[|
 let plus := (def_rec f x y => (
     match x with
      | 0 => y
      | s x' => s ((f x') y)
     end))
 in let fibo := (def_rec f n => (
        match n with
         | 0 => 1
         | s n' => (
             match n' with
              | 0 => 1
              | s n'' => (plus (f n')) (f n'')
             end)
        end))
    in
    (fibo (s (s (s (s (s 1))))))
 |].


Eval compute in ss_eval_n example2 254.
Example fibo5 : (ss_eval_n example2 254) =  Some (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ zero))))))))))))).
Proof. compute. reflexivity. Qed.
