Require Import Coq.Arith.PeanoNat.
Require Import Coq.Lists.List.

Require Import Termination.Syntax.
Require Import Termination.ListUtils.
Require Import Termination.Sets.
Require Import Termination.Tactics.
Require Import Termination.AssocList.
Require Import Termination.SmallStep.
Require Import Termination.TypeForm.

Open Scope list_scope.

Inductive has_type: context -> term -> term -> Prop :=
| HTVar: forall (gamma: context) x (T: term),
    is_context gamma ->
    lookup Nat.eq_dec gamma x = Some T ->
    has_type gamma (fvar x) T

| HTWeaken: forall gamma x T u U,
    has_type gamma u U ->
    is_type gamma T ->
    ~(x ∈ support gamma) ->
    has_type ((x,T) :: gamma) u U
             
| HTLambda:
    forall gamma t U V x,
      is_type gamma U ->
     (*  type_form V -> *)
      ~(x ∈ fv_context gamma) ->
      ~(x ∈ fv t) ->
      ~(x ∈ fv V) ->
      has_type ((x,U) :: gamma)
               (open 0 t (fvar x))
               (open 0 V (fvar x)) ->
      has_type gamma (lambda U t) (T_arrow U V)

| HTApp:
    forall gamma t1 t2 U V,
      has_type gamma t1 (T_arrow U V) ->
      has_type gamma t2 U ->
      has_type gamma (app t1 t2) (T_let t2 U V)

| HTPair:
    forall gamma A B t1 t2,
      has_type gamma t1 A ->
      has_type gamma t2 (T_let t1 A B) ->
      has_type gamma (pp t1 t2) (T_prod A B)

| HTPi1:
    forall gamma t A B,
      has_type gamma t (T_prod A B) ->
      has_type gamma (pi1 t) A

| HTPi2:
    forall gamma t A B,
      has_type gamma t (T_prod A B) ->
      has_type gamma (pi2 t) (T_let (pi1 t) A B)

| HTUnit:
    forall gamma,
      is_context gamma ->
      has_type gamma uu T_unit
               
| HTTrue:
    forall gamma,
      is_context gamma ->
      has_type gamma ttrue T_bool

| HTFalse:
    forall gamma,
      is_context gamma ->
      has_type gamma tfalse T_bool

| HTIte:
    forall gamma t1 t2 t3 T x,
      ~(x ∈ fv_context gamma) ->
      ~(x ∈ fv t1) ->
      ~(x ∈ fv t2) ->
      ~(x ∈ fv t3) ->
      ~(x ∈ fv T) ->
      has_type gamma t1 T_bool ->
      has_type ((x, T_equal t1 ttrue) :: gamma) t2 T ->
      has_type ((x, T_equal t1 tfalse) :: gamma) t3 T ->
      has_type gamma (ite t1 t2 t3) T

| HTErr:
    forall gamma T,
      is_type gamma T ->
      are_equal gamma tfalse ttrue ->
      has_type gamma err T_bot

| HTZero:
    forall gamma,
      is_context gamma ->
      has_type gamma zero T_nat

| HTSucc:
    forall gamma t,
      has_type gamma t T_nat ->
      has_type gamma (succ t) T_nat

| HTRec:
    forall gamma tn t0 ts T n y p,
     (* type_form T -> *)
      ~(n ∈ fv_context gamma) ->
      ~(y ∈ fv_context gamma) ->
      ~(p ∈ fv_context gamma) ->
      ~(n ∈ fv T) ->
      ~(n ∈ fv ts) ->
      ~(n ∈ fv t0) ->
      ~(n ∈ fv tn) ->
      ~(y ∈ fv T) ->
      ~(y ∈ fv ts) ->
      ~(y ∈ fv t0) ->
      ~(p ∈ fv T) ->
      ~(p ∈ fv ts) ->
      ~(p ∈ fv t0) ->
      ~(p ∈ fv tn) ->
      NoDup (n :: y :: p :: nil) ->
      has_type gamma tn T_nat ->
      has_type gamma t0 (open 0 T zero) ->
      is_type ((n,T_nat) :: gamma) (open 0 T (fvar n)) ->
      has_type (
        (p, T_equal (fvar y) (lambda T_unit (rec T (fvar n) t0 ts))) ::
        (y, T_arrow T_unit (open 0 T (fvar n))) ::
        (n, T_nat) ::
        gamma
      )
        (open 0 (open 1 ts (fvar n)) (fvar y))
        (open 0 T (succ (fvar n)))
      ->
      has_type gamma (rec T tn t0 ts) (T_let tn T_nat T)

| HTMatch:
    forall gamma tn t0 ts T n p,
      ~(p ∈ fv ts) ->
      ~(p ∈ fv t0) ->
      ~(p ∈ fv tn) ->
      ~(p ∈ fv T) ->
      ~(p ∈ fv_context gamma) ->
      ~(n ∈ fv tn) ->
      ~(n ∈ fv ts) ->
      ~(n ∈ fv T) ->
      ~(n ∈ fv_context gamma) ->
      ~(n = p) ->
      has_type gamma tn T_nat ->
      has_type ((p, T_equal tn zero) :: gamma) t0 T ->
      has_type (
        (p, T_equal tn (succ (fvar n))) ::
        (n, T_nat) ::
        gamma
      )
        (open 0 ts (fvar n))
        T
      ->
      has_type gamma (tmatch tn t0 ts) T

| HTRefine:
    forall gamma t A b x p,
      ~(p ∈ fv_context gamma) ->
      ~(p ∈ fv b) ->
      ~(p ∈ fv t) ->
      ~(p ∈ fv A) ->
      ~(x ∈ fv_context gamma) ->
      ~(x ∈ fv b) ->
      ~(x ∈ fv t) ->
      ~(x ∈ fv A) ->
      ~(x = p) ->
      has_type gamma t A ->
      has_type ((x,A) :: gamma) (open 0 b (fvar x)) T_bool ->
      are_equal ((p, T_equal (fvar x) t) :: (x,A) :: gamma) (open 0 b (fvar x)) ttrue ->
      has_type gamma t (T_refine A b) 
      
| HTSub:
    forall gamma t T1 T2,
      is_subtype gamma T1 T2 ->
      has_type gamma t T1 ->
      has_type gamma t T2

| HTLet:
    forall gamma t1 t2 x p A B,
      ~(x ∈ support gamma) ->
      ~(p ∈ support gamma) ->
      ~(x = p) ->
      ~(x ∈ fv t2) ->
      ~(p ∈ fv t2) ->
      ~(x ∈ fv B) ->
      ~(p ∈ fv B) ->
      has_type gamma t1 A ->
      has_type ((p,T_equal (fvar x) t1) :: (x,A) :: gamma) (open 0 t2 (fvar x)) B ->
      has_type gamma (tlet t1 A t2) B

| HTSingleton:
    forall gamma t1 t2 T,
      has_type gamma t1 T ->
      are_equal gamma t1 t2 ->
      has_type gamma t1 (T_singleton t2)

| HTIdentityElim:
    forall gamma t1 t2 T,
      has_type gamma t1 T ->
      are_equal gamma t1 t2 ->
      has_type gamma t2 T

| HTIntersection:
    forall gamma t T1 T2,
      has_type gamma t T1 ->
      has_type gamma t T2 ->
      has_type gamma t (T_intersection T1 T2)

| HTUnionElim:
    forall gamma t t' T1 T2 T z,
      ~(z ∈ support gamma) ->
      ~(z ∈ fv t') ->
      ~(z ∈ fv T) ->
      has_type gamma t (T_union T1 T2) ->
      has_type ((z,T1) :: gamma) (open 0 t' (fvar z)) T ->
      has_type ((z,T2) :: gamma) (open 0 t' (fvar z)) T -> 
      has_type gamma (tlet t (T_union T1 T2) t') T

| HTRefl:
    forall gamma t1 t2,
      are_equal gamma t1 t2 ->
      has_type gamma trefl (T_equal t1 t2)

| HTForall:
    forall gamma t A U V x,
     (*  type_form V -> *)
      ~(x ∈ support gamma) ->
      ~(x ∈ fv V) ->
      is_type gamma U ->
      has_type ((x,U) :: gamma) t (open 0 V (fvar x) )->
      has_type gamma t A ->
      has_type gamma t (T_forall U V)

| HTExistsElim:
    forall gamma p U V x y t T,
      ~(x ∈ support gamma) ->
      ~(y ∈ support gamma) ->
      ~(x = y) ->
      ~(x ∈ fv t) ->
      ~(y ∈ fv t) ->
      ~(x ∈ fv T) ->
      ~(y ∈ fv T) ->
      has_type gamma p (T_exists U V) ->
      has_type ((y, open 0 V (fvar x)) :: (x,U) :: gamma)
               (open 0 t (fvar y))
               T
      ->
      has_type gamma (tlet p (T_exists U V) t) T
               
with is_type: context -> term -> Prop :=
| ITUnit:
    forall gamma,
      is_context gamma ->
      is_type gamma T_unit

| ITBool:
    forall gamma,
      is_context gamma ->
      is_type gamma T_bool

| ITNat:
    forall gamma,
      is_context gamma ->
      is_type gamma T_nat
              
| ITProd:
    forall gamma T1 T2 x,
      ~(x ∈ support gamma) ->
      ~(x ∈ fv T2) ->
      is_type gamma T1 ->
      is_type ((x,T1) :: gamma) (open 0 T2 (fvar x)) ->
      is_type gamma (T_prod T1 T2)

| ITTerm:
    forall gamma T,
      has_type gamma T T_type ->
      is_type gamma T
              
| ITArrow:
    forall gamma T1 T2 x,
      ~(x ∈ support gamma) ->
      ~(x ∈ fv T2) ->
      is_type gamma T1 ->
      is_type ((x,T1) :: gamma) (open 0 T2 (fvar x)) ->
      is_type gamma (T_arrow T1 T2)

| ITRefine:
    forall gamma T p x,
      ~(x ∈ support gamma) ->
      ~(x ∈ fv p) ->
      is_type gamma T ->
      has_type ((x,T) :: gamma) (open 0 p (fvar x)) T_bool ->
      is_type gamma (T_refine T p)

| ITLet:
    forall gamma t1 A B x p,
      ~(x ∈ support gamma) ->
      ~(p ∈ support gamma) ->
      ~(x = p) ->
      ~(x ∈ fv B) ->
      ~(p ∈ fv B) ->
      is_type gamma A ->
      has_type gamma t1 A ->
      is_type ((p, T_equal (fvar x) t1) :: (x,A) :: gamma) (open 0 B (fvar x)) ->
      is_type gamma (T_let t1 A B)

| ITSingleton:
    forall gamma t,
      is_context gamma ->
      subset (fv t) (support gamma) ->
      wf t 0 ->
      is_type gamma (T_singleton t)

| ITIntersection:
    forall gamma T1 T2,
      is_type gamma T1 ->
      is_type gamma T2 ->
      is_type gamma (T_intersection T1 T2)

| ITUnion:
    forall gamma T1 T2,
      is_type gamma T1 ->
      is_type gamma T2 ->
      is_type gamma (T_union T1 T2)

| ITBot:
    forall gamma,
      is_context gamma ->
      is_type gamma T_bot

| ITTop:
    forall gamma,
      is_context gamma ->
      is_type gamma T_top

| ITEqual:
    forall gamma t1 t2,
      is_context gamma ->
      subset (fv t1) (support gamma) ->
      subset (fv t2) (support gamma) ->
      wf t1 0 ->
      wf t2 0 ->
      is_type gamma (T_equal t1 t2)

| ITForall:
    forall gamma T1 T2 x,
      ~(x ∈ support gamma) ->
      ~(x ∈ fv T2) ->      
      is_type gamma T1 ->
      is_type ((x,T1) :: gamma) (open 0 T2 (fvar x)) ->
      is_type gamma (T_forall T1 T2)

| ITExists:
    forall gamma T1 T2 x,
      ~(x ∈ support gamma) ->
      ~(x ∈ fv T2) ->      
      is_type gamma T1 ->
      is_type ((x,T1) :: gamma) (open 0 T2 (fvar x)) ->
      is_type gamma (T_exists T1 T2)

| ITType:
    forall gamma,
      is_context gamma ->
      is_type gamma T_type
      
with is_context: context -> Prop :=
| ICNil: is_context nil
| ICCons:
    forall x T gamma,
      is_context gamma ->
      ~(x ∈ support gamma) ->
      is_type gamma T ->
      is_context ((x,T) :: gamma)

with is_subtype: context -> term -> term -> Prop :=
| ISRefl:
    forall gamma A,
      is_type gamma A ->
      is_subtype gamma A A

| ISTrans:
    forall gamma T1 T2 T3,
      is_subtype gamma T1 T2 ->
      is_subtype gamma T2 T3 ->
      is_subtype gamma T1 T3
| ISArrow:
    forall gamma A1 A2 B1 B2 x,
     (* type_form B2 -> *)
      ~(x ∈ support gamma) ->
      ~(x ∈ fv A2) ->      
      ~(x ∈ fv B2) ->      
      is_subtype gamma B1 A1 ->
      is_type ((x,A1) :: gamma) (open 0 A2 (fvar x)) ->
      is_type ((x,B1) :: gamma) (open 0 B2 (fvar x)) ->
      is_subtype ((x,B1) :: gamma)
                 (open 0 A2 (fvar x)) 
                 (open 0 B2 (fvar x)) ->
      is_subtype gamma (T_arrow A1 A2) (T_arrow B1 B2)

| ISArrow2:
    forall gamma T A B x f,
     (* type_form B -> *)
      ~(x ∈ support gamma) ->
      ~(f ∈ support gamma) ->
      ~(x = f) ->
      ~(x ∈ fv B) ->      
      ~(f ∈ fv B) ->      
      is_type gamma A ->
      is_type gamma T ->
      has_type ((x,A) :: (f,T) :: gamma) (app (fvar f) (fvar x))
                                         (open 0 B (fvar x)) ->
      is_type ((x,A) :: gamma) (open 0 B (fvar x)) ->
      is_subtype gamma T (T_arrow A B)

| ISGeneric:
    forall gamma A B x,
      ~(x ∈ support gamma) ->
      is_type gamma A ->
      is_type gamma B ->
      has_type ((x,A) :: gamma) (fvar x) B ->
      is_subtype gamma A B
                
                 
| ISProd:
    forall gamma A1 A2 B1 B2 x,
     (* type_form B2 -> *)
      ~(x ∈ support gamma) ->
      ~(x ∈ fv A2) ->      
      ~(x ∈ fv B2) ->      
      is_subtype gamma A1 B1 ->
      is_type ((x,A1) :: gamma) (open 0 A2 (fvar x)) ->
      is_type ((x,B1) :: gamma) (open 0 B2 (fvar x)) ->
      is_subtype ((x,A1) :: gamma)
                 (open 0 A2 (fvar x)) 
                 (open 0 B2 (fvar x)) ->
      is_subtype gamma (T_prod A1 A2) (T_prod B1 B2)
                 
| ISProd2:
    forall gamma T A B x,
     (* type_form B -> *)
      ~(x ∈ support gamma) ->
      ~(x ∈ fv A) ->      
      ~(x ∈ fv B) ->      
      is_type gamma T ->
      is_type ((x,A) :: gamma) (open 0 B (fvar x)) ->
      has_type ((x,T) :: gamma) (pi1 (fvar x)) A ->
      has_type ((x,T) :: gamma) (pi2 (fvar x)) (T_let (pi1 (fvar x)) A B) ->
      is_subtype gamma T (T_prod A B)
            
| ISRefine:
    forall gamma A B p q x,
      ~(x ∈ support gamma) ->
      ~(x ∈ fv p) ->
      ~(x ∈ fv q) ->
      has_type ((x,A) :: gamma) (open 0 p (fvar x)) T_bool ->
      has_type ((x,B) :: gamma) (open 0 q (fvar x)) T_bool ->
      are_equal ((x, T_refine A p) :: gamma) (open 0 q (fvar x)) ttrue ->
      is_subtype gamma A B ->
      is_subtype gamma (T_refine A p) (T_refine B q)
                 
| ISRefine2:
    forall gamma A B p,
      is_subtype gamma A B ->
      is_type gamma (T_refine A p) ->
      is_subtype gamma (T_refine A p) B
                 
| ISRefine3:
    forall gamma A,
      is_type gamma A ->
      is_subtype gamma A (T_refine A ttrue)

| ISRefine4:
    forall gamma T A p x,
      ~(x ∈ support gamma) ->
      ~(x ∈ fv p) ->
      has_type ((x,A) :: gamma) (open 0 p (fvar x)) T_bool ->
      are_equal ((x, T) :: gamma) (open 0 p (fvar x)) ttrue ->  
      is_subtype gamma T A ->
      is_subtype gamma T (T_refine A p)

| ISRefine5:
    forall gamma T A b x p,
      ~(x ∈ support gamma) ->
      ~(p ∈ support gamma) ->
      ~(x = p) ->
      ~(x ∈ fv b) ->
      ~(x ∈ fv T) ->
      ~(p ∈ fv T) ->
      is_type gamma A ->
      has_type ((x,A) :: gamma) (open 0 b (fvar x)) T_bool ->
      has_type ((p, T_equal (open 0 b (fvar x)) ttrue) :: (x, A) :: gamma)
               (fvar x)
               T ->
      is_subtype gamma (T_refine A b) T

| ISSingleton:
    forall gamma t T,
      has_type gamma t T ->
      is_subtype gamma (T_singleton t) T

| ISLet:
    forall gamma t A B T x p,
      ~(x ∈ support gamma) ->
      ~(p ∈ support gamma) ->
      ~(x = p) ->
      ~(x ∈ fv B) ->
      ~(p ∈ fv B) ->
      ~(x ∈ fv T) ->
      ~(p ∈ fv T) ->
      is_type gamma A ->
      has_type gamma t A ->
      is_type gamma (open 0 B t) ->
      is_type ((p, T_equal (fvar x) t) :: (x,A) :: gamma) (open 0 B (fvar x)) ->
      is_subtype ((p, T_equal (fvar x) t) :: (x,A) :: gamma)
                 (open 0 B (fvar x)) T ->
      is_subtype gamma (T_let t A B) T
                 
| ISLetEqual:
    forall gamma t t' A B,
      are_equal gamma t t' ->
      is_type gamma A ->
      is_type gamma (T_let t A B) ->
      is_type gamma (T_let t' A B) ->
      is_subtype gamma (T_let t A B) (T_let t' A B)

| ISLetOpen:
    forall gamma v A B,
      is_value v ->
      has_type gamma v A ->
      is_type gamma (T_let v A B) ->
      is_type gamma (open 0 B v) ->
      is_subtype gamma (T_let v A B) (open 0 B v)

| ISLetOpen2:
    forall gamma v A B,
    (*  type_form B -> *)
      is_value v ->
      has_type gamma v A ->
      is_type gamma (T_let v A B) ->
      is_type gamma (open 0 B v) ->
      is_subtype gamma (open 0 B v) (T_let v A B)

| ISBot:
    forall gamma T,
      is_type gamma T ->
      is_subtype gamma T_bot T

| ISTop:
    forall gamma T,
      is_type gamma T ->
      is_subtype gamma T T_top

| ISIntersection1:
    forall gamma T1 T2,
      is_type gamma T1 ->
      is_type gamma T2 ->
      is_subtype gamma (T_intersection T1 T2) T1

| ISIntersection2:
    forall gamma T1 T2,
      is_type gamma T1 ->
      is_type gamma T2 ->
      is_subtype gamma (T_intersection T1 T2) T2

| ISUnion1:
    forall gamma T1 T2,
      is_type gamma T1 ->
      is_type gamma T2 ->
      is_subtype gamma T1 (T_union T1 T2)

| ISUnion2:
    forall gamma T1 T2,
      is_type gamma T1 ->
      is_type gamma T2 ->
      is_subtype gamma T2 (T_union T1 T2)

| ISForall:
    forall gamma t T1 T2 x,
      ~(x ∈ support gamma) ->
      ~(x ∈ fv T2) ->
      has_type gamma t T1 ->
      is_type ((x,T1) :: gamma) (open 0 T2 (fvar x)) ->
      is_subtype gamma (T_forall T1 T2) (T_let t T1 T2)

| ISExists:
    forall gamma t T1 T2 x,
      ~(x ∈ support gamma) ->
      ~(x ∈ fv T2) ->
      has_type gamma t T1 ->
      is_type ((x,T1) :: gamma) (open 0 T2 (fvar x)) ->
      is_subtype gamma (T_let t T1 T2) (T_exists T1 T2) 
                 
with are_equal: context -> term -> term -> Prop :=
| AERefl: forall gamma t,
    subset (fv t) (support gamma) ->
    wf t 0 ->
    is_context gamma ->
    are_equal gamma t t

| AEWeaken: forall gamma x T u v,
    are_equal gamma u v ->
    is_type gamma T ->
    ~(x ∈ support gamma) ->
    are_equal ((x,T) :: gamma) u v

| AETrans: forall gamma t1 t2 t3,
    are_equal gamma t1 t2 ->
    are_equal gamma t2 t3 ->
    are_equal gamma t1 t3

| AESym: forall gamma t1 t2,
    are_equal gamma t1 t2 ->
    are_equal gamma t2 t1

| AEStep: forall gamma t1 t2,
    subset (fv t1) (support gamma) ->
    wf t1 0 ->
    is_context gamma ->
    small_step t1 t2 ->
    are_equal gamma t1 t2

| AEPairExt: forall gamma t A B,
    has_type gamma t (T_prod A B) ->
    are_equal gamma t (pp (pi1 t) (pi2 t))

| AESing: forall gamma t1 t2,
    has_type gamma t1 (T_singleton t2) ->
    are_equal gamma t1 t2

| AEApp: forall gamma t1 t2 t1' t2',
    are_equal gamma t1 t2 ->
    are_equal gamma t1' t2' ->
    are_equal gamma (app t1 t1') (app t2 t2')

| AESucc: forall gamma u v,
    are_equal gamma u v ->
    are_equal gamma (succ u) (succ v)

| AESuccInj: forall gamma u v,
    are_equal gamma (succ u) (succ v) ->
    are_equal gamma u v

| AEPi1: forall gamma u v,
    are_equal gamma u v ->
    are_equal gamma (pi1 u) (pi1 v)

| AEPi2: forall gamma u v,
    are_equal gamma u v ->
    are_equal gamma (pi2 u) (pi2 v)

| AEPair: forall gamma u v u' v',
    are_equal gamma u v ->
    are_equal gamma u' v' ->
    are_equal gamma (pp u u') (pp v v')

| AEType: forall gamma p t1 t2,
    has_type gamma p (T_equal t1 t2) ->
    are_equal gamma t1 t2

| AEProof: forall gamma p t1 t2,
    has_type gamma p (T_equal t1 t2) ->
    are_equal gamma p trefl

| AEIte:
    forall gamma t1 t2 t3 t x,
      ~(x ∈ support gamma) ->
      ~(x ∈ fv t) ->
      ~(x ∈ fv t2) ->
      ~(x ∈ fv t3) ->
      has_type gamma t1 T_bool ->
      are_equal ((x, T_equal t1 ttrue) :: gamma) t2 t ->
      are_equal ((x, T_equal t1 tfalse) :: gamma) t3 t ->
      are_equal gamma (ite t1 t2 t3) t

| AEMatch:
    forall gamma tn t0 ts t n p,
      ~(p ∈ support gamma) ->
      ~(p ∈ fv tn) ->
      ~(p ∈ fv ts) ->
      ~(p ∈ fv t0) ->
      ~(p ∈ fv t) ->
      ~(n ∈ support gamma) ->
      ~(n ∈ fv tn) ->
      ~(n ∈ fv ts) ->
      ~(n ∈ fv t) ->
      ~(n = p) ->      
      has_type gamma tn T_nat ->
      are_equal ((p, T_equal tn zero) :: gamma) t0 t ->
      are_equal ((p, T_equal tn (succ (fvar n))) :: (n, T_nat) :: gamma)
                (open 0 ts (fvar n))
                t ->
      are_equal gamma (tmatch tn t0 ts) t

| AERec:    
    forall gamma T tn t0 ts t n p,
      ~(p ∈ support gamma) ->
      ~(p ∈ fv tn) ->
      ~(p ∈ fv ts) ->
      ~(p ∈ fv t0) ->
      ~(p ∈ fv t) ->
      ~(p ∈ fv T) ->
      ~(n ∈ support gamma) ->
      ~(n ∈ fv ts) ->
      ~(n ∈ fv tn) ->
      ~(n ∈ fv t0) ->
      ~(n ∈ fv t) ->
      ~(n ∈ fv T) ->
      ~(n = p) ->
      has_type gamma tn T_nat ->
      is_type ((n,T_nat) :: gamma) (open 0 T (fvar n)) ->
      are_equal ((p, T_equal tn zero) :: gamma) t0 t ->
      are_equal
        ((p, T_equal tn (succ (fvar n))) :: (n, T_nat) :: gamma)
        (open 0 (open 1 ts (fvar n)) (lambda T_unit (rec T (fvar n) t0 ts)))
        t ->
      are_equal gamma (rec T tn t0 ts) t

| AEWeakHyp:
    forall gamma1 gamma2 x T T' u v,
      ~(x ∈ support gamma2) ->
      is_subtype gamma2 T T' ->
      are_equal (gamma1 ++ (x,T') :: gamma2) u v ->
      are_equal (gamma1 ++ (x,T) :: gamma2) u v

| AESplitBool:
    forall gamma1 gamma2 b t t' x,
      ~(x ∈ fv_context gamma1) ->
      ~(x ∈ support gamma2) ->
      ~(x ∈ fv t) ->
      ~(x ∈ fv t') ->
      has_type gamma2 b T_bool ->
      are_equal (gamma1 ++ (x,T_equal b ttrue) :: gamma2) t t' ->
      are_equal (gamma1 ++ (x,T_equal b tfalse) :: gamma2) t t' ->
      are_equal (gamma1 ++ gamma2) t t'

| AESplitNat:
    forall gamma1 gamma2 n t t' x y,
      ~(x ∈ fv_context gamma1) ->
      ~(x ∈ support gamma2) ->
      ~(y ∈ fv_context gamma1) ->
      ~(y ∈ support gamma2) ->
      ~(x ∈ fv t) ->
      ~(x ∈ fv t') ->
      ~(y ∈ fv t) ->
      ~(y ∈ fv t') ->
      ~(x = y) ->
      has_type gamma2 n T_nat ->
      are_equal (gamma1 ++ (x,T_equal n zero) :: gamma2) t t' ->
      are_equal (gamma1 ++ (x,T_equal n (succ (fvar y))) :: (y, T_nat) :: gamma2) t t' ->
      are_equal (gamma1 ++ gamma2) t t'

| AEError:
    forall gamma e T,
      has_type gamma e T ->
      are_equal gamma err e ->
      are_equal gamma ttrue tfalse

| AESplitIte:
    forall gamma1 gamma2 b e1 e2 t t' e x y,
      ~(x ∈ fv_context gamma1) ->
      ~(x ∈ support gamma2) ->
      ~(y ∈ fv_context gamma1) ->
      ~(y ∈ support gamma2) ->
      ~(x ∈ fv t) ->
      ~(x ∈ fv t') ->
      ~(y ∈ fv t) ->
      ~(y ∈ fv t') ->
      ~(x = y) ->

      has_type gamma2 b T_bool ->
      is_context (gamma1 ++ ((x, T_equal (ite b e1 e2) e)  :: gamma2)) ->
      are_equal (gamma1 ++ (x, T_equal e1 e) :: (y, T_equal b ttrue) :: gamma2) t t' ->
      are_equal (gamma1 ++ (x, T_equal e2 e) :: (y, T_equal b tfalse) :: gamma2) t t' ->
      are_equal (gamma1 ++ ((x, T_equal (ite b e1 e2) e)  :: gamma2)) t t'

| AESplitMatch:
  forall gamma1 gamma2 n t t' e1 e2 e x y v,
    ~(x ∈ fv_context gamma1) ->
    ~(x ∈ support gamma2) ->
    ~(y ∈ fv_context gamma1) ->
    ~(y ∈ support gamma2) ->
    ~(v ∈ fv_context gamma1) ->
    ~(v ∈ support gamma2) ->
    ~(x ∈ fv t) ->
    ~(x ∈ fv t') ->
    ~(x ∈ fv n) ->
    ~(x ∈ fv e1) ->
    ~(x ∈ fv e2) ->
    ~(x ∈ fv e) ->
    ~(y ∈ fv t) ->
    ~(y ∈ fv t') ->
    ~(y ∈ fv n) ->
    ~(y ∈ fv e1) ->
    ~(y ∈ fv e2) ->
    ~(y ∈ fv e) ->
    ~(v ∈ fv t) ->
    ~(v ∈ fv t') ->
    ~(v ∈ fv n) ->
    ~(v ∈ fv e1) ->
    ~(v ∈ fv e2) ->
    ~(v ∈ fv e) ->
    NoDup (x :: y :: v :: nil) ->

    has_type gamma2 n T_nat ->
    is_context (gamma1 ++ ((x, T_equal (tmatch n e1 e2) e)  :: gamma2)) ->
    are_equal (gamma1 ++ (x, T_equal e1 e) :: (y, T_equal n zero) :: gamma2) t t' ->
    are_equal (gamma1 ++ (x, T_equal (open 0 e2 (fvar v)) e) ::
                         (y, T_equal n (succ (fvar v))) ::
                         (v, T_nat) ::
                         gamma2)
              t t' ->
    are_equal (gamma1 ++ ((x, T_equal (tmatch n e1 e2) e)  :: gamma2)) t t'

| AESplitRec:
  forall gamma1 gamma2 n t t' T e1 e2 e x y v,
    ~(x ∈ fv_context gamma1) ->
    ~(x ∈ support gamma2) ->
    ~(y ∈ fv_context gamma1) ->
    ~(y ∈ support gamma2) ->
    ~(v ∈ fv_context gamma1) ->
    ~(v ∈ support gamma2) ->
    ~(x ∈ fv t) ->
    ~(x ∈ fv t') ->
    ~(x ∈ fv n) ->
    ~(x ∈ fv e1) ->
    ~(x ∈ fv e2) ->
    ~(x ∈ fv e) ->
    ~(x ∈ fv T) ->
    ~(y ∈ fv t) ->
    ~(y ∈ fv t') ->
    ~(y ∈ fv n) ->
    ~(y ∈ fv e1) ->
    ~(y ∈ fv e2) ->
    ~(y ∈ fv e) ->
    ~(y ∈ fv T) ->
    ~(v ∈ fv t) ->
    ~(v ∈ fv t') ->
    ~(v ∈ fv n) ->
    ~(v ∈ fv e1) ->
    ~(v ∈ fv e2) ->
    ~(v ∈ fv e) ->
    ~(v ∈ fv T) ->
    NoDup (x :: y :: v :: nil) ->

    has_type gamma2 n T_nat ->
    is_context (gamma1 ++ ((x, T_equal (rec T n e1 e2) e)  :: gamma2)) -> 
    is_type gamma2 (open 0 T (fvar x)) ->
    are_equal (gamma1 ++ (x, T_equal e1 e) :: (y, T_equal n zero) :: gamma2) t t' ->
    are_equal (gamma1 ++ (x, T_equal
                               (open 0 (open 1 e2 (fvar v))
                                             (lambda T_unit (rec T (fvar v) e1 e2)))
                               e) ::
                          (y, T_equal n (succ (fvar v))) ::
                          (v, T_nat) ::
                          gamma2
              ) t t' ->
    are_equal (gamma1 ++ ((x, T_equal (rec T n e1 e2) e)  :: gamma2)) t t'
.


Scheme mut_has_type        := Induction for has_type    Sort Prop
  with mut_is_context      := Induction for is_context  Sort Prop
  with mut_is_type         := Induction for is_type     Sort Prop
  with mut_is_subtype      := Induction for is_subtype  Sort Prop
  with mut_are_equal       := Induction for are_equal   Sort Prop.

Combined Scheme mut_HT_IT_IC_IS_AE from
         mut_has_type, mut_is_type, mut_is_context, mut_is_subtype, mut_are_equal.
