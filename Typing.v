Require Import Coq.Arith.PeanoNat.
Require Import Coq.Lists.List.

Require Import SystemFR.Syntax.
Require Import SystemFR.ListUtils.
Require Import SystemFR.Sets.
Require Import SystemFR.Tactics.
Require Import SystemFR.AssocList.
Require Import SystemFR.SmallStep.
Require Import SystemFR.TypeErasure.
Require Import SystemFR.StrictPositivity.

Require Import SystemFR.Polarity.
Require Import SystemFR.NatUtils.
Require Import SystemFR.NatCompare.
Require Import SystemFR.LVarOperations.
Require Import SystemFR.NatCompareErase.
Require Import SystemFR.BaseType.
Require Import SystemFR.TypeOperations.

Open Scope list_scope.

Inductive has_type: list nat -> context -> tree -> tree -> Prop :=
| HTVar: forall tvars (gamma: context) x T,
    is_context tvars gamma ->
    lookup Nat.eq_dec gamma x = Some T ->
    has_type tvars gamma (term_fvar x) T

| HTWeaken: forall tvars gamma x T u U,
    has_type tvars gamma u U ->
    is_type tvars gamma T ->
    ~(x ∈ support gamma) ->
    ~(x ∈ tvars) ->
    has_type tvars ((x,T) :: gamma) u U

| HTLambda:
    forall tvars gamma t U V x,
      is_type tvars gamma U ->
      ~(x ∈ fv_context gamma) ->
      ~(x ∈ fv t) ->
      ~(x ∈ fv V) ->
      ~(x ∈ tvars) ->
      has_type tvars
               ((x,U) :: gamma)
               (open 0 t (term_fvar x))
               (open 0 V (term_fvar x)) ->
      has_type tvars gamma (lambda U t) (T_arrow U V)

| HTApp:
    forall tvars gamma t1 t2 U V,
      has_type tvars gamma t1 (T_arrow U V) ->
      has_type tvars gamma t2 U ->
      has_type tvars gamma (app t1 t2) (T_let t2 V)

| HTTypeLambda:
    forall tvars gamma t T X,
      ~(X ∈ pfv_context gamma term_var) ->
      ~(X ∈ pfv_context gamma type_var) ->
      ~(X ∈ pfv t term_var) ->
      ~(X ∈ pfv T term_var) ->
      ~(X ∈ pfv T type_var) ->
      ~(X ∈ tvars) ->
      has_type (X :: tvars)
               gamma
               (topen 0 t (type_fvar X))
               (topen 0 T (type_fvar X)) ->
      has_type tvars gamma (type_abs t) (T_abs T)

| HTTypeInst:
    forall tvars gamma t U V,
      has_type tvars gamma t (T_abs U) ->
      is_type tvars gamma V ->
      has_type tvars gamma (type_inst t V) (topen 0 U V)

| HTForallInst:
    forall tvars gamma t1 t2 U V,
      has_type tvars gamma t1 (T_forall U V) ->
      has_type tvars gamma t2 U ->
      has_type tvars gamma (forall_inst t1 t2) (T_let t2 V)

| HTTypeability:
    forall tvars gamma t T,
      has_type tvars gamma t T ->
      has_type tvars gamma (typecheck t T) (typeability t T)

| HTPair:
    forall tvars gamma A B t1 t2,
      has_type tvars gamma t1 A ->
      has_type tvars gamma t2 (T_let t1 B) ->
      has_type tvars gamma (pp t1 t2) (T_prod A B)

| HTPi1:
    forall tvars gamma t A B,
      has_type tvars gamma t (T_prod A B) ->
      has_type tvars gamma (pi1 t) A

| HTPi2:
    forall tvars gamma t A B,
      has_type tvars gamma t (T_prod A B) ->
      has_type tvars gamma (pi2 t) (T_let (pi1 t) B)

| HTBecause:
    forall tvars gamma A B t1 t2,
      has_type tvars gamma t1 A ->
      has_type tvars gamma t2 (T_let t1 B) ->
      has_type tvars gamma (because t1 t2) (T_type_refine A B)

| HTGetProofIn:
    forall tvars gamma t1 t2 A B T x,
      ~(x ∈ tvars) ->
      ~(x ∈ fv_context gamma) ->
      ~(x ∈ fv t1) ->
      ~(x ∈ fv t2) ->
      ~(x ∈ fv T) ->
      ~(x ∈ fv A) ->
      ~(x ∈ fv B) ->
      wf (erase_term t2) 0 ->
      has_type tvars gamma t1 (T_type_refine A B) ->
      has_type tvars ((x, T_let t1 B) :: gamma) (open 0 t2 (term_fvar x)) T ->
      has_type tvars gamma (get_refinement_witness t1 t2) T

| HTUnit:
    forall tvars gamma,
      is_context tvars gamma ->
      has_type tvars gamma uu T_unit

| HTTrue:
    forall tvars gamma,
      is_context tvars gamma ->
      has_type tvars gamma ttrue T_bool

| HTFalse:
    forall tvars gamma,
      is_context tvars gamma ->
      has_type tvars gamma tfalse T_bool

| HTIte:
    forall tvars gamma b t1 t2 T x,
      ~(x ∈ fv_context gamma) ->
      ~(x ∈ fv b) ->
      ~(x ∈ fv t1) ->
      ~(x ∈ fv t2) ->
      ~(x ∈ fv T) ->
      ~(x ∈ tvars) ->
      has_type tvars gamma b T_bool ->
      has_type tvars ((x, T_equal b ttrue) :: gamma) t1 T ->
      has_type tvars ((x, T_equal b tfalse) :: gamma) t2 T ->
      has_type tvars gamma (ite b t1 t2) T

| HTIte2:
    forall tvars gamma b t1 t2 T1 T2 T x,
      ~(x ∈ fv_context gamma) ->
      ~(x ∈ fv b) ->
      ~(x ∈ fv t1) ->
      ~(x ∈ fv t2) ->
      ~(x ∈ fv T1) ->
      ~(x ∈ fv T2) ->
      ~(x ∈ tvars) ->
      has_type tvars gamma b T_bool ->
      has_type tvars ((x, T_equal b ttrue) :: gamma) t1 T1 ->
      has_type tvars ((x, T_equal b tfalse) :: gamma) t2 T2 ->
      T_ite b T1 T2 T ->
      has_type tvars gamma (ite b t1 t2) T

| HTIsPair:
    forall tvars gamma t,
      has_type tvars gamma t T_top ->
      has_type tvars gamma (boolean_recognizer 0 t) T_bool

| HTIsSucc:
    forall tvars gamma t,
      has_type tvars gamma t T_top ->
      has_type tvars gamma (boolean_recognizer 1 t) T_bool

| HTIsLambda:
    forall tvars gamma t,
      has_type tvars gamma t T_top ->
      has_type tvars gamma (boolean_recognizer 2 t) T_bool

| HTErr:
    forall tvars gamma T,
      is_type tvars gamma T ->
      are_equal tvars gamma tfalse ttrue ->
      has_type tvars gamma (err T) T

| HTZero:
    forall tvars gamma,
      is_context tvars gamma ->
      has_type tvars gamma zero T_nat

| HTSucc:
    forall tvars gamma t,
      has_type tvars gamma t T_nat ->
      has_type tvars gamma (succ t) T_nat

| HTRec:
    forall tvars gamma tn t0 ts T n y p,
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
      ~(n ∈ tvars) ->
      ~(y ∈ tvars) ->
      ~(p ∈ tvars) ->
      NoDup (n :: y :: p :: nil) ->
      has_type tvars gamma tn T_nat ->
      has_type tvars gamma t0 (open 0 T zero) ->
      is_type tvars ((n,T_nat) :: gamma) (open 0 T (term_fvar n)) ->
      has_type tvars (
        (p, T_equal (term_fvar y) (lambda T_unit (rec T (term_fvar n) t0 ts))) ::
        (y, T_arrow T_unit (open 0 T (term_fvar n))) ::
        (n, T_nat) ::
        gamma
      )
        (open 0 (open 1 ts (term_fvar n)) (term_fvar y))
        (open 0 T (succ (term_fvar n)))
      ->
      has_type tvars gamma (rec T tn t0 ts) (T_let tn T)

| HTFix:
    forall tvars gamma ts T n y p,
      ~(n ∈ fv_context gamma) ->
      ~(y ∈ fv_context gamma) ->
      ~(p ∈ fv_context gamma) ->
      ~(n ∈ fv T) ->
      ~(n ∈ fv ts) ->
      ~(y ∈ fv T) ->
      ~(y ∈ fv ts) ->
      ~(p ∈ fv T) ->
      ~(p ∈ fv ts) ->
      ~(n ∈ tvars) ->
      ~(y ∈ tvars) ->
      ~(p ∈ tvars) ->
      NoDup (n :: y :: p :: nil) ->
      wf (erase_term ts) 1 ->
      is_context tvars gamma ->
      is_type tvars ((n,T_nat) :: gamma) (open 0 T (term_fvar n)) ->
      has_type tvars (
        (p, T_equal (term_fvar y) (lambda T_unit (tfix T ts))) ::
        (y, T_arrow T_unit (open 0 T (term_fvar n))) ::
        (n, T_nat) ::
        gamma
      )
        (open 0 (open 1 ts (succ (fvar n term_var))) (term_fvar y))
        (open 0 T (succ (term_fvar n)))
      ->
      has_type tvars
               ((y, T_top) :: gamma)
               (open 0 (open 1 ts zero) (fvar y term_var))
               (open 0 T zero)
      ->
      has_type tvars gamma (tfix T ts) (T_forall T_nat T)

| HTFixStrongInduct:
    forall tvars gamma ts T n y p,
      ~(n ∈ fv_context gamma) ->
      ~(y ∈ fv_context gamma) ->
      ~(p ∈ fv_context gamma) ->
      ~(n ∈ fv T) ->
      ~(n ∈ fv ts) ->
      ~(y ∈ fv T) ->
      ~(y ∈ fv ts) ->
      ~(p ∈ fv T) ->
      ~(p ∈ fv ts) ->
      ~(n ∈ tvars) ->
      ~(y ∈ tvars) ->
      ~(p ∈ tvars) ->
      NoDup (n :: y :: p :: nil) ->
      wf (erase_term ts) 1 ->
      is_context tvars gamma ->
      is_type tvars ((n,T_nat) :: gamma) (open 0 T (term_fvar n)) ->
      has_type tvars (
        (p, T_equal (term_fvar y) (lambda T_unit (tfix T ts))) ::
        (y,
          (T_forall
             (T_refine T_nat (annotated_tlt (lvar 0 term_var) (fvar n term_var)))
             (T_arrow T_unit (shift T)))) ::
        (n, T_nat) ::
        gamma
      )
        (open 0 (open 1 ts (fvar n term_var)) (term_fvar y))
        (open 0 T (term_fvar n))
      ->
      has_type tvars gamma (tfix T ts) (T_forall T_nat T)

| HTMatch:
    forall tvars gamma tn t0 ts T n p,
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
      ~(n ∈ tvars) ->
      ~(p ∈ tvars) ->
      has_type tvars gamma tn T_nat ->
      has_type tvars ((p, T_equal tn zero) :: gamma) t0 T ->
      has_type tvars (
        (p, T_equal tn (succ (term_fvar n))) ::
        (n, T_nat) ::
        gamma
      )
        (open 0 ts (term_fvar n))
        T
      ->
      has_type tvars gamma (tmatch tn t0 ts) T

| HTRefine:
    forall tvars gamma t A b x p,
      ~(p ∈ fv_context gamma) ->
      ~(p ∈ fv b) ->
      ~(p ∈ fv t) ->
      ~(p ∈ fv A) ->
      ~(x ∈ fv_context gamma) ->
      ~(x ∈ fv b) ->
      ~(x ∈ fv t) ->
      ~(x ∈ fv A) ->
      ~(x = p) ->
      ~(x ∈ tvars) ->
      ~(p ∈ tvars) ->
      has_type tvars gamma t A ->
      has_type tvars ((x,A) :: gamma) (open 0 b (term_fvar x)) T_bool ->
      are_equal tvars ((p, T_equal (term_fvar x) t) :: (x,A) :: gamma) (open 0 b (term_fvar x)) ttrue ->
      has_type tvars gamma t (T_refine A b)

| HTSub:
    forall tvars gamma t T1 T2,
      is_subtype tvars gamma T1 T2 ->
      has_type tvars gamma t T1 ->
      has_type tvars gamma t T2

| HTLet:
    forall tvars gamma t1 t2 x p A B,
      ~(x ∈ support gamma) ->
      ~(p ∈ support gamma) ->
      ~(x = p) ->
      ~(x ∈ fv t2) ->
      ~(p ∈ fv t2) ->
      ~(x ∈ fv B) ->
      ~(p ∈ fv B) ->
      ~(x ∈ tvars) ->
      ~(p ∈ tvars) ->
      has_type tvars gamma t1 A ->
      has_type tvars ((p,T_equal (term_fvar x) t1) :: (x,A) :: gamma) (open 0 t2 (term_fvar x)) B ->
      has_type tvars gamma (tlet t1 A t2) B

| HTLet2:
    forall tvars gamma t1 t2 x p A B,
      ~(x ∈ support gamma) ->
      ~(p ∈ support gamma) ->
      ~(x = p) ->
      ~(x ∈ fv t2) ->
      ~(p ∈ fv t2) ->
      ~(x ∈ fv B) ->
      ~(p ∈ fv B) ->
      ~(x ∈ tvars) ->
      ~(p ∈ tvars) ->
      has_type tvars gamma t1 A ->
      has_type tvars ((p,T_equal (term_fvar x) t1) :: (x,A) :: gamma) (open 0 t2 (term_fvar x)) (open 0 B (term_fvar x)) ->
      has_type tvars gamma (tlet t1 A t2) (T_let t1 B)

| HTSingleton:
    forall tvars gamma t1 t2 T,
      has_type tvars gamma t1 T ->
      are_equal tvars gamma t1 t2 ->
      has_type tvars gamma t1 (T_singleton t2)

| HTIdentityElim:
    forall tvars gamma t1 t2 T,
      has_type tvars gamma t1 T ->
      are_equal tvars gamma t1 t2 ->
      has_type tvars gamma t2 T

| HTIntersection:
    forall tvars gamma t T1 T2,
      has_type tvars gamma t T1 ->
      has_type tvars gamma t T2 ->
      has_type tvars gamma t (T_intersection T1 T2)

| HTUnionElim:
    forall tvars gamma t t' T1 T2 T z,
      ~(z ∈ support gamma) ->
      ~(z ∈ fv t') ->
      ~(z ∈ fv T) ->
      ~(z ∈ tvars) ->
      has_type tvars gamma t (T_union T1 T2) ->
      has_type tvars ((z,T1) :: gamma) (open 0 t' (term_fvar z)) T ->
      has_type tvars ((z,T2) :: gamma) (open 0 t' (term_fvar z)) T ->
      has_type tvars gamma (tlet t (T_union T1 T2) t') T

| HTRefl:
    forall tvars gamma t1 t2,
      are_equal tvars gamma t1 t2 ->
      has_type tvars gamma (trefl t1 t2) (T_equal t1 t2)

| HTForall:
    forall tvars gamma t A U V x,
      ~(x ∈ support gamma) ->
      ~(x ∈ fv V) ->
      ~(x ∈ tvars) ->
      is_type tvars gamma U ->
      has_type tvars ((x,U) :: gamma) t (open 0 V (term_fvar x) )->
      has_type tvars gamma t A ->
      has_type tvars gamma t (T_forall U V)

| HTExistsElim:
    forall tvars gamma p U V x y t T,
      ~(x ∈ support gamma) ->
      ~(y ∈ support gamma) ->
      ~(x = y) ->
      ~(x ∈ fv t) ->
      ~(y ∈ fv t) ->
      ~(x ∈ fv T) ->
      ~(y ∈ fv T) ->
      ~(x ∈ tvars) ->
      ~(y ∈ tvars) ->
      has_type tvars gamma p (T_exists U V) ->
      has_type tvars ((y, open 0 V (term_fvar x)) :: (x,U) :: gamma)
               (open 0 t (term_fvar y))
               T
      ->
      has_type tvars gamma (tlet p (T_exists U V) t) T

| HTUnfoldZ:
    forall tvars gamma t n T0 Ts,
      wf T0 0 ->
      wf Ts 0 ->
      twf T0 0 ->
      twf Ts 1 ->
      are_equal tvars gamma n zero ->
      has_type tvars gamma t (T_rec n T0 Ts) ->
      has_type tvars gamma (tunfold t) T0

| HTUnfoldS:
    forall tvars gamma t n T0 Ts,
      is_annotated_term n ->
      wf n 0 ->
      wf T0 0 ->
      wf Ts 0 ->
      twf T0 0 ->
      twf Ts 1 ->
      are_equal tvars gamma (spositive n) ttrue ->
      has_type tvars gamma t (T_rec n T0 Ts) ->
      has_type tvars gamma (tunfold t) (topen 0 Ts (T_rec (tpred n) T0 Ts))

| HTUnfoldIn:
    forall tvars gamma t1 t2 n T0 Ts pn p1 p2 y T,
      ~(p1 ∈ tvars) ->
      ~(p1 ∈ support gamma) ->
      ~(p1 ∈ fv t1) ->
      ~(p1 ∈ fv t2) ->
      ~(p1 ∈ fv n) ->
      ~(p1 ∈ fv T0) ->
      ~(p1 ∈ fv Ts) ->
      ~(p1 ∈ fv T) ->
      ~(p2 ∈ tvars) ->
      ~(p2 ∈ support gamma) ->
      ~(p2 ∈ fv t1) ->
      ~(p2 ∈ fv t2) ->
      ~(p2 ∈ fv n) ->
      ~(p2 ∈ fv T0) ->
      ~(p2 ∈ fv Ts) ->
      ~(p2 ∈ fv T) ->
      ~(pn ∈ tvars) ->
      ~(pn ∈ support gamma) ->
      ~(pn ∈ fv t1) ->
      ~(pn ∈ fv t2) ->
      ~(pn ∈ fv n) ->
      ~(pn ∈ fv T0) ->
      ~(pn ∈ fv Ts) ->
      ~(pn ∈ fv T) ->
      ~(y ∈ tvars) ->
      ~(y ∈ support gamma) ->
      ~(y ∈ fv t1) ->
      ~(y ∈ fv t2) ->
      ~(y ∈ fv n) ->
      ~(y ∈ fv T0) ->
      ~(y ∈ fv Ts) ->
      ~(y ∈ fv T) ->
      NoDup (p1 :: p2 :: pn :: y :: nil) ->
      is_annotated_term n ->
      is_annotated_type T0 ->
      is_annotated_type Ts ->
      wf n 0 ->
      wf T0 0 ->
      wf Ts 0 ->
      twf T0 0 ->
      twf Ts 1 ->
      wf t2 0 ->
      has_type tvars gamma t1 (T_rec n T0 Ts) ->
      has_type tvars
               ((p2, T_equal n zero) :: (p1, T_equal t1 (tfold (T_rec n T0 Ts) (fvar y term_var))) :: (y, T0) :: gamma)
               (open 0 t2 (fvar y term_var)) T ->
      has_type tvars
               ((p2, T_equal n (succ (fvar pn term_var))) ::
                (p1, T_equal t1 (tfold (T_rec n T0 Ts) (fvar y term_var))) ::
                (y, topen 0 Ts (T_rec (fvar pn term_var) T0 Ts)) ::
                (pn, T_nat) :: gamma)
               (open 0 t2 (fvar y term_var)) T ->
      has_type tvars gamma (tunfold_in t1 t2) T

| HTFold:
    forall tvars gamma t n pn T0 Ts p,
      ~(p ∈ tvars) ->
      ~(p ∈ support gamma) ->
      ~(p ∈ fv t) ->
      ~(p ∈ fv n) ->
      ~(p ∈ fv T0) ->
      ~(p ∈ fv Ts) ->
      ~(pn ∈ tvars) ->
      ~(pn ∈ support gamma) ->
      ~(pn ∈ fv t) ->
      ~(pn ∈ fv n) ->
      ~(pn ∈ fv T0) ->
      ~(pn ∈ fv Ts) ->
      ~(p = pn) ->
      wf n 0 ->
      twf n 0 ->
      wf T0 0 ->
      twf T0 0 ->
      wf Ts 0 ->
      twf Ts 1 ->
      subset (fv n) (support gamma) ->
      subset (fv T0) (support gamma) ->
      subset (fv Ts) (support gamma) ->
      is_annotated_term n ->
      is_annotated_type T0 ->
      is_annotated_type Ts ->
      has_type tvars gamma n T_nat ->
      has_type tvars ((p, T_equal n zero) :: gamma) t T0 ->
      has_type tvars
               ((p, T_equal n (succ (fvar pn term_var))) :: (pn, T_nat) :: gamma)
               t
               (topen 0 Ts (T_rec (fvar pn term_var) T0 Ts)) ->
      has_type tvars gamma (tfold (T_rec n T0 Ts) t) (T_rec n T0 Ts)

| HTUnfoldGen:
    forall tvars gamma t T0 Ts X,
      wf T0 0 ->
      wf Ts 0 ->
      twf T0 0 ->
      twf Ts 1 ->
      ~(X ∈ pfv Ts type_var) ->
      strictly_positive (topen 0 Ts (fvar X type_var)) (X :: nil) ->
      has_type tvars gamma t (intersect T0 Ts) ->
      has_type tvars gamma (tunfold t) (topen 0 Ts (intersect T0 Ts))

| HTUnfoldGenIn:
    forall tvars gamma t1 t2 T0 Ts p y T X,
      ~(p ∈ tvars) ->
      ~(p ∈ support gamma) ->
      ~(p ∈ fv t1) ->
      ~(p ∈ fv t2) ->
      ~(p ∈ fv T0) ->
      ~(p ∈ fv Ts) ->
      ~(p ∈ fv T) ->
      ~(y ∈ tvars) ->
      ~(y ∈ support gamma) ->
      ~(y ∈ fv t1) ->
      ~(y ∈ fv t2) ->
      ~(y ∈ fv T0) ->
      ~(y ∈ fv Ts) ->
      ~(y ∈ fv T) ->
      ~(X ∈ pfv Ts type_var) ->
      strictly_positive (topen 0 Ts (fvar X type_var)) (X :: nil) ->
      is_annotated_type T0 ->
      is_annotated_type Ts ->
      ~(p = y) ->
      wf T0 0 ->
      wf Ts 0 ->
      twf T0 0 ->
      twf Ts 1 ->
      wf t2 0 ->
      has_type tvars gamma t1 (intersect T0 Ts) ->
      has_type tvars
               ((p, T_equal t1 (tfold  (intersect T0 Ts) (fvar y term_var))) ::
                (y, topen 0 Ts (intersect T0 Ts)) ::
                gamma)
               (open 0 t2 (fvar y term_var)) T ->
      has_type tvars gamma (tunfold_in t1 t2) T

| HTFoldGen:
    forall tvars gamma t T0 Ts X,
      wf T0 0 ->
      twf T0 0 ->
      wf Ts 0 ->
      twf Ts 1 ->
      subset (fv T0) (support gamma) ->
      subset (fv Ts) (support gamma) ->
      is_annotated_type T0 ->
      is_annotated_type Ts ->
      ~(X ∈ pfv Ts type_var) ->
      is_subtype tvars gamma (topen 0 Ts (T_rec zero T0 Ts)) T0 ->
      strictly_positive (topen 0 Ts (fvar X type_var)) (X :: nil) ->
      has_type tvars gamma t (topen 0 Ts (intersect T0 Ts)) ->
      has_type tvars gamma (tfold (intersect T0 Ts) t) (intersect T0 Ts)

| HTFoldGen2:
    forall tvars gamma t T0 Ts X,
      wf Ts 0 ->
      twf Ts 1 ->
      subset (fv Ts) (support gamma) ->
      base_type X (topen 0 Ts (fvar X type_var)) T0 ->
      is_annotated_type Ts ->
      ~(X ∈ pfv Ts type_var) ->
      strictly_positive (topen 0 Ts (fvar X type_var)) (X :: nil) ->
      has_type tvars gamma t (topen 0 Ts (intersect T0 Ts)) ->
      has_type tvars gamma (tfold (intersect T0 Ts) t) (intersect T0 Ts)

| HTLeft:
    forall tvars gamma t A B,
      has_type tvars gamma t A ->
      is_type tvars gamma B ->
      has_type tvars gamma (tleft t) (T_sum A B)

| HTRight:
    forall tvars gamma t A B,
      has_type tvars gamma t B ->
      is_type tvars gamma A ->
      has_type tvars gamma (tright t) (T_sum A B)

| HTSumMatch:
    forall tvars gamma t tl tr A B T y p,
      ~(p ∈ fv tl) ->
      ~(p ∈ fv tr) ->
      ~(p ∈ fv t) ->
      ~(p ∈ fv T) ->
      ~(p ∈ fv A) ->
      ~(p ∈ fv B) ->
      ~(p ∈ fv_context gamma) ->
      ~(y ∈ fv tl) ->
      ~(y ∈ fv tr) ->
      ~(y ∈ fv t) ->
      ~(y ∈ fv T) ->
      ~(y ∈ fv A) ->
      ~(y ∈ fv B) ->
      ~(y ∈ fv_context gamma) ->
      ~(y = p) ->
      ~(y ∈ tvars) ->
      ~(p ∈ tvars) ->
      is_type tvars ((y,T_sum A B) :: gamma) (open 0 T (fvar y term_var)) ->
      has_type tvars gamma t (T_sum A B) ->
      has_type
        tvars ((p, T_equal t (tleft (fvar y term_var))) :: (y, A) :: gamma)
        (open 0 tl (fvar y term_var))
        (open 0 T (tleft (fvar y term_var)))
      ->
      has_type
        tvars ((p, T_equal t (tright (fvar y term_var))) :: (y, B) :: gamma)
        (open 0 tr (fvar y term_var))
        (open 0 T (tright (fvar y term_var)))
      ->
      has_type tvars gamma (sum_match t tl tr) (T_let t T)

| HTSize:
    forall tvars gamma t A,
      has_type tvars gamma t A ->
      has_type tvars gamma (tsize t) T_nat

with is_type: tvar_list -> context -> tree -> Prop :=
| ITUnit:
    forall tvars gamma,
      is_context tvars gamma ->
      is_type tvars gamma T_unit

| ITBool:
    forall tvars gamma,
      is_context tvars gamma ->
      is_type tvars gamma T_bool

| ITNat:
    forall tvars gamma,
      is_context tvars gamma ->
      is_type tvars gamma T_nat

| ITProd:
    forall tvars gamma T1 T2 x,
      ~(x ∈ support gamma) ->
      ~(x ∈ fv T2) ->
      is_type tvars gamma T1 ->
      is_type tvars ((x,T1) :: gamma) (open 0 T2 (term_fvar x)) ->
      is_type tvars gamma (T_prod T1 T2)

| ITArrow:
    forall tvars gamma T1 T2 x,
      ~(x ∈ support gamma) ->
      ~(x ∈ fv T2) ->
      is_type tvars gamma T1 ->
      is_type tvars ((x,T1) :: gamma) (open 0 T2 (term_fvar x)) ->
      is_type tvars gamma (T_arrow T1 T2)

| ITRefine:
    forall tvars gamma T p x,
      ~(x ∈ support gamma) ->
      ~(x ∈ fv p) ->
      is_type tvars gamma T ->
      has_type tvars ((x,T) :: gamma) (open 0 p (term_fvar x)) T_bool ->
      is_type tvars gamma (T_refine T p)

| ITLet:
    forall tvars gamma t1 A B x p,
      ~(x ∈ support gamma) ->
      ~(p ∈ support gamma) ->
      ~(x = p) ->
      ~(x ∈ fv B) ->
      ~(p ∈ fv B) ->
      ~(x ∈ tvars) ->
      ~(p ∈ tvars) ->
      is_type tvars gamma A ->
      has_type tvars gamma t1 A ->
      is_type tvars ((p, T_equal (term_fvar x) t1) :: (x,A) :: gamma) (open 0 B (term_fvar x)) ->
      is_type tvars gamma (T_let t1 B)

| ITSingleton:
    forall tvars gamma t,
      is_context tvars gamma ->
      subset (fv t) (support gamma) ->
      wf t 0 ->
      twf t 0 ->
      is_annotated_term t ->
      is_type tvars gamma (T_singleton t)

| ITIntersection:
    forall tvars gamma T1 T2,
      is_type tvars gamma T1 ->
      is_type tvars gamma T2 ->
      is_type tvars gamma (T_intersection T1 T2)

| ITUnion:
    forall tvars gamma T1 T2,
      is_type tvars gamma T1 ->
      is_type tvars gamma T2 ->
      is_type tvars gamma (T_union T1 T2)

| ITBot:
    forall tvars gamma,
      is_context tvars gamma ->
      is_type tvars gamma T_bot

| ITTop:
    forall tvars gamma,
      is_context tvars gamma ->
      is_type tvars gamma T_top

| ITEqual:
    forall tvars gamma t1 t2,
      is_context tvars gamma ->
      subset (fv t1) (support gamma) ->
      subset (fv t2) (support gamma) ->
      wf t1 0 ->
      wf t2 0 ->
      twf t1 0 ->
      twf t2 0 ->
      is_annotated_term t1 ->
      is_annotated_term t2 ->
      is_type tvars gamma (T_equal t1 t2)

| ITForall:
    forall tvars gamma T1 T2 x,
      ~(x ∈ support gamma) ->
      ~(x ∈ fv T2) ->
      ~(x ∈ tvars) ->
      is_type tvars gamma T1 ->
      is_type tvars ((x,T1) :: gamma) (open 0 T2 (term_fvar x)) ->
      is_type tvars gamma (T_forall T1 T2)

| ITExists:
    forall tvars gamma T1 T2 x,
      ~(x ∈ support gamma) ->
      ~(x ∈ fv T2) ->
      ~(x ∈ tvars) ->
      is_type tvars gamma T1 ->
      is_type tvars ((x,T1) :: gamma) (open 0 T2 (term_fvar x)) ->
      is_type tvars gamma (T_exists T1 T2)

| ITAbs:
    forall tvars gamma T X,
      ~(X ∈ fv_context gamma) ->
      ~(X ∈ fv T) ->
      ~(X ∈ tvars) ->
      is_type (X :: tvars) gamma (topen 0 T (type_fvar X)) ->
      is_type tvars gamma (T_abs T)

| ITVar:
    forall tvars gamma X,
      X ∈ tvars ->
      is_context tvars gamma ->
      is_type tvars gamma (type_fvar X)


| ITRec:
    forall tvars gamma n T0 Ts X,
      ~(X ∈ support gamma) ->
      ~(X ∈ pfv T0 type_var) ->
      ~(X ∈ pfv Ts type_var) ->
      ~(X ∈ tvars) ->
      is_annotated_type T0 ->
      is_annotated_type Ts ->
      has_type tvars gamma n T_nat ->
      is_type tvars gamma T0 ->
      is_type (X :: tvars) gamma (topen 0 Ts (fvar X type_var)) ->
      is_type tvars gamma (T_rec n T0 Ts)

with is_context: tvar_list -> context -> Prop :=
| ICNil: forall tvars, is_context tvars nil
| ICCons:
    forall tvars x T gamma,
      is_context tvars gamma ->
      ~(x ∈ support gamma) ->
      ~(x ∈ tvars) ->
      is_type tvars gamma T ->
      is_context tvars ((x,T) :: gamma)

with is_subtype: tvar_list -> context -> tree -> tree -> Prop :=
| ISRefl:
    forall tvars gamma A,
      is_type tvars gamma A ->
      is_subtype tvars gamma A A

| ISTrans:
    forall tvars gamma T1 T2 T3,
      is_subtype tvars gamma T1 T2 ->
      is_subtype tvars gamma T2 T3 ->
      is_subtype tvars gamma T1 T3
| ISArrow:
    forall tvars gamma A1 A2 B1 B2 x,
      ~(x ∈ support gamma) ->
      ~(x ∈ fv A2) ->
      ~(x ∈ fv B2) ->
      ~(x ∈ tvars) ->
      is_subtype tvars gamma B1 A1 ->
      is_type tvars ((x,A1) :: gamma) (open 0 A2 (term_fvar x)) ->
      is_type tvars ((x,B1) :: gamma) (open 0 B2 (term_fvar x)) ->
      is_subtype tvars
                 ((x,B1) :: gamma)
                 (open 0 A2 (term_fvar x))
                 (open 0 B2 (term_fvar x)) ->
      is_subtype tvars gamma (T_arrow A1 A2) (T_arrow B1 B2)

| ISArrow2:
    forall tvars gamma T A B x f,
      ~(x ∈ support gamma) ->
      ~(f ∈ support gamma) ->
      ~(x = f) ->
      ~(x ∈ fv B) ->
      ~(f ∈ fv B) ->
      ~(x ∈ tvars) ->
      ~(f ∈ tvars) ->
      is_type tvars gamma A ->
      is_type tvars gamma T ->
      has_type tvars ((x,A) :: (f,T) :: gamma) (app (term_fvar f) (term_fvar x))
                                         (open 0 B (term_fvar x)) ->
      is_type tvars ((x,A) :: gamma) (open 0 B (term_fvar x)) ->
      is_subtype tvars gamma T (T_arrow A B)

| ISGeneric:
    forall tvars gamma A B x,
      ~(x ∈ support gamma) ->
      is_type tvars gamma A ->
      is_type tvars gamma B ->
      has_type tvars ((x,A) :: gamma) (term_fvar x) B ->
      is_subtype tvars gamma A B


| ISProd:
    forall tvars gamma A1 A2 B1 B2 x,
      ~(x ∈ support gamma) ->
      ~(x ∈ fv A2) ->
      ~(x ∈ fv B2) ->
      ~(x ∈ tvars) ->
      is_subtype tvars gamma A1 B1 ->
      is_type tvars ((x,A1) :: gamma) (open 0 A2 (term_fvar x)) ->
      is_type tvars ((x,B1) :: gamma) (open 0 B2 (term_fvar x)) ->
      is_subtype tvars
                 ((x,A1) :: gamma)
                 (open 0 A2 (term_fvar x))
                 (open 0 B2 (term_fvar x)) ->
      is_subtype tvars gamma (T_prod A1 A2) (T_prod B1 B2)

| ISProd2:
    forall tvars gamma T A B x,
      ~(x ∈ support gamma) ->
      ~(x ∈ fv A) ->
      ~(x ∈ fv B) ->
      ~(x ∈ tvars) ->
      is_type tvars gamma T ->
      is_type tvars ((x,A) :: gamma) (open 0 B (term_fvar x)) ->
      has_type tvars ((x,T) :: gamma) (pi1 (term_fvar x)) A ->
      has_type tvars ((x,T) :: gamma) (pi2 (term_fvar x)) (T_let (pi1 (term_fvar x)) B) ->
      is_subtype tvars gamma T (T_prod A B)

| ISRefine:
    forall tvars gamma A B p q x,
      ~(x ∈ support gamma) ->
      ~(x ∈ fv p) ->
      ~(x ∈ fv q) ->
      ~(x ∈ tvars) ->
      has_type tvars ((x,A) :: gamma) (open 0 p (term_fvar x)) T_bool ->
      has_type tvars ((x,B) :: gamma) (open 0 q (term_fvar x)) T_bool ->
      are_equal tvars ((x, T_refine A p) :: gamma) (open 0 q (term_fvar x)) ttrue ->
      is_subtype tvars gamma A B ->
      is_subtype tvars gamma (T_refine A p) (T_refine B q)

| ISRefine2:
    forall tvars gamma A B p,
      is_subtype tvars gamma A B ->
      is_type tvars gamma (T_refine A p) ->
      is_subtype tvars gamma (T_refine A p) B

| ISRefine3:
    forall tvars gamma A,
      is_type tvars gamma A ->
      is_subtype tvars gamma A (T_refine A ttrue)

| ISRefine4:
    forall tvars gamma T A p x,
      ~(x ∈ support gamma) ->
      ~(x ∈ fv p) ->
      ~(x ∈ tvars) ->
      has_type tvars ((x,A) :: gamma) (open 0 p (term_fvar x)) T_bool ->
      are_equal tvars ((x, T) :: gamma) (open 0 p (term_fvar x)) ttrue ->
      is_subtype tvars gamma T A ->
      is_subtype tvars gamma T (T_refine A p)

| ISRefine5:
    forall tvars gamma T A b x p,
      ~(x ∈ support gamma) ->
      ~(p ∈ support gamma) ->
      ~(x = p) ->
      ~(x ∈ fv b) ->
      ~(x ∈ fv T) ->
      ~(p ∈ fv T) ->
      ~(x ∈ tvars) ->
      ~(p ∈ tvars) ->
      is_type tvars gamma A ->
      has_type tvars ((x,A) :: gamma) (open 0 b (term_fvar x)) T_bool ->
      has_type tvars ((p, T_equal (open 0 b (term_fvar x)) ttrue) :: (x, A) :: gamma)
               (term_fvar x)
               T ->
      is_subtype tvars gamma (T_refine A b) T

| ISSingleton:
    forall tvars gamma t T,
      has_type tvars gamma t T ->
      is_subtype tvars gamma (T_singleton t) T

| ISLet:
    forall tvars gamma t A B T x p,
      ~(x ∈ support gamma) ->
      ~(p ∈ support gamma) ->
      ~(x = p) ->
      ~(x ∈ fv B) ->
      ~(p ∈ fv B) ->
      ~(x ∈ fv T) ->
      ~(p ∈ fv T) ->
      is_type tvars gamma A ->
      has_type tvars gamma t A ->
      is_type tvars gamma (open 0 B t) ->
      is_type tvars ((p, T_equal (term_fvar x) t) :: (x,A) :: gamma) (open 0 B (term_fvar x)) ->
      is_subtype tvars
                 ((p, T_equal (term_fvar x) t) :: (x,A) :: gamma)
                 (open 0 B (term_fvar x)) T ->
      is_subtype tvars gamma (T_let t B) T

| ISLetEqual:
    forall tvars gamma t t' A B,
      are_equal tvars gamma t t' ->
      is_type tvars gamma A ->
      is_type tvars gamma (T_let t B) ->
      is_type tvars gamma (T_let t' B) ->
      is_subtype tvars gamma (T_let t B) (T_let t' B)

| ISLetOpen:
    forall tvars gamma v A B,
      is_value (erase_term v) ->
      has_type tvars gamma v A ->
      is_type tvars gamma (T_let v B) ->
      is_type tvars gamma (open 0 B v) ->
      is_subtype tvars gamma (T_let v B) (open 0 B v)

| ISLetOpen2:
    forall tvars gamma v A B,
      is_value (erase_term v) ->
      has_type tvars gamma v A ->
      is_type tvars gamma (T_let v B) ->
      is_type tvars gamma (open 0 B v) ->
      is_subtype tvars gamma (open 0 B v) (T_let v B)

| ISBot:
    forall tvars gamma T,
      is_type tvars gamma T ->
      is_subtype tvars gamma T_bot T

| ISTop:
    forall tvars gamma T,
      is_type tvars gamma T ->
      is_subtype tvars gamma T T_top

| ISIntersection1:
    forall tvars gamma T1 T2,
      is_type tvars gamma T1 ->
      is_type tvars gamma T2 ->
      is_subtype tvars gamma (T_intersection T1 T2) T1

| ISIntersection2:
    forall tvars gamma T1 T2,
      is_type tvars gamma T1 ->
      is_type tvars gamma T2 ->
      is_subtype tvars gamma (T_intersection T1 T2) T2

| ISUnion1:
    forall tvars gamma T1 T2,
      is_type tvars gamma T1 ->
      is_type tvars gamma T2 ->
      is_subtype tvars gamma T1 (T_union T1 T2)

| ISUnion2:
    forall tvars gamma T1 T2,
      is_type tvars gamma T1 ->
      is_type tvars gamma T2 ->
      is_subtype tvars gamma T2 (T_union T1 T2)

| ISForall:
    forall tvars gamma t T1 T2 x,
      ~(x ∈ support gamma) ->
      ~(x ∈ fv T2) ->
      ~(x ∈ tvars) ->
      has_type tvars gamma t T1 ->
      is_type tvars ((x,T1) :: gamma) (open 0 T2 (term_fvar x)) ->
      is_subtype tvars gamma (T_forall T1 T2) (T_let t T2)

| ISExists:
    forall tvars gamma t T1 T2 x,
      ~(x ∈ support gamma) ->
      ~(x ∈ fv T2) ->
      ~(x ∈ tvars) ->
      has_type tvars gamma t T1 ->
      is_type tvars ((x,T1) :: gamma) (open 0 T2 (term_fvar x)) ->
      is_subtype tvars gamma (T_let t T2) (T_exists T1 T2)

| ISRec:
    forall tvars gamma n1 n2 T0 Ts,
      wf T0 0 ->
      wf Ts 0 ->
      twf T0 0 ->
      twf Ts 1 ->
      subset (fv T0) (support gamma) ->
      subset (fv Ts) (support gamma) ->
      is_annotated_type T0 ->
      is_annotated_type Ts ->
      are_equal tvars gamma n1 n2 ->
      is_subtype tvars gamma (T_rec n1 T0 Ts) (T_rec n2 T0 Ts)

| ISRecPos:
    forall X tvars gamma n1 n2 T0 Ts,
      wf T0 0 ->
      wf Ts 0 ->
      twf T0 0 ->
      twf Ts 1 ->
      subset (fv T0) (support gamma) ->
      subset (fv Ts) (support gamma) ->
      is_annotated_type T0 ->
      is_annotated_type Ts ->
      ~(X ∈ pfv T0 type_var) ->
      ~(X ∈ pfv Ts type_var) ->
      ~(X ∈ tvars) ->
      has_polarities (topen 0 Ts (fvar X type_var)) ((X, Positive) :: nil) ->
      are_equal tvars gamma (annotated_tlt n1 (succ n2)) ttrue ->
      has_type tvars gamma n1 T_nat ->
      is_subtype tvars gamma (topen 0 Ts (T_rec zero T0 Ts)) T0 ->
      is_subtype tvars gamma (T_rec n2 T0 Ts) (T_rec n1 T0 Ts)

with are_equal: tvar_list -> context -> tree -> tree -> Prop :=
| AERefl: forall tvars gamma t,
    subset (fv t) (support gamma) ->
    wf t 0 ->
    twf t 0 ->
    is_annotated_term t ->
    is_context tvars gamma ->
    are_equal tvars gamma t t

| AEWeaken: forall tvars gamma x T u v,
    are_equal tvars gamma u v ->
    is_type tvars gamma T ->
    ~(x ∈ support gamma) ->
    are_equal tvars ((x,T) :: gamma) u v

| AETrans: forall tvars gamma t1 t2 t3,
    are_equal tvars gamma t1 t2 ->
    are_equal tvars gamma t2 t3 ->
    are_equal tvars gamma t1 t3

| AESym: forall tvars gamma t1 t2,
    are_equal tvars gamma t1 t2 ->
    are_equal tvars gamma t2 t1

| AEStep: forall tvars gamma t1 t2,
    subset (fv t1) (support gamma) ->
    subset (fv t2) (support gamma) ->
    wf t1 0 ->
    wf t2 0 ->
    twf t1 0 ->
    twf t2 0 ->
    is_annotated_term t1 ->
    is_annotated_term t2 ->
    is_context tvars gamma ->
    small_step (erase_term t1) (erase_term t2) ->
    are_equal tvars gamma t1 t2

| AEPairExt: forall tvars gamma t A B,
    has_type tvars gamma t (T_prod A B) ->
    are_equal tvars gamma t (pp (pi1 t) (pi2 t))

| AESing: forall tvars gamma t1 t2,
    has_type tvars gamma t1 (T_singleton t2) ->
    are_equal tvars gamma t1 t2

| AEApp: forall tvars gamma t1 t2 t1' t2',
    are_equal tvars gamma t1 t2 ->
    are_equal tvars gamma t1' t2' ->
    are_equal tvars gamma (app t1 t1') (app t2 t2')

| AESucc: forall tvars gamma u v,
    are_equal tvars gamma u v ->
    are_equal tvars gamma (succ u) (succ v)

| AESuccInj: forall tvars gamma u v,
    are_equal tvars gamma (succ u) (succ v) ->
    are_equal tvars gamma u v

| AEPi1: forall tvars gamma u v,
    are_equal tvars gamma u v ->
    are_equal tvars gamma (pi1 u) (pi1 v)

| AEPi2: forall tvars gamma u v,
    are_equal tvars gamma u v ->
    are_equal tvars gamma (pi2 u) (pi2 v)

| AEPair: forall tvars gamma u v u' v',
    are_equal tvars gamma u v ->
    are_equal tvars gamma u' v' ->
    are_equal tvars gamma (pp u u') (pp v v')

| AEFold: forall tvars gamma u v T1 T2,
    wf T1 0 ->
    wf T2 0 ->
    twf T1 0 ->
    twf T2 0 ->
    subset (fv T1) (support gamma) ->
    subset (fv T2) (support gamma) ->
    is_annotated_type T1 ->
    is_annotated_type T2 ->
    are_equal tvars gamma u v ->
    are_equal tvars gamma (tfold T1 u) (tfold T2 v)

| AEUnfold: forall tvars gamma u v,
    are_equal tvars gamma u v ->
    are_equal tvars gamma (tunfold u) (tunfold v)

| AEType: forall tvars gamma p t1 t2,
    has_type tvars gamma p (T_equal t1 t2) ->
    are_equal tvars gamma t1 t2

| AEProof: forall tvars gamma p t1 t2 t3 t4,
    wf t3 0 ->
    wf t4 0 ->
    twf t3 0 ->
    twf t4 0 ->
    subset (fv t3) (support gamma) ->
    subset (fv t4) (support gamma) ->
    is_annotated_term t3 ->
    is_annotated_term t4 ->
    has_type tvars gamma p (T_equal t1 t2) ->
    are_equal tvars gamma p (trefl t3 t4)

| AEIte:
    forall tvars gamma t1 t2 t3 t x,
      ~(x ∈ support gamma) ->
      ~(x ∈ fv t) ->
      ~(x ∈ fv t2) ->
      ~(x ∈ fv t3) ->
      ~(x ∈ tvars) ->
      has_type tvars gamma t1 T_bool ->
      are_equal tvars ((x, T_equal t1 ttrue) :: gamma) t2 t ->
      are_equal tvars ((x, T_equal t1 tfalse) :: gamma) t3 t ->
      are_equal tvars gamma (ite t1 t2 t3) t

| AEMatch:
    forall tvars gamma tn t0 ts t n p,
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
      ~(p ∈ tvars) ->
      ~(n ∈ tvars) ->
      has_type tvars gamma tn T_nat ->
      are_equal tvars ((p, T_equal tn zero) :: gamma) t0 t ->
      are_equal tvars ((p, T_equal tn (succ (term_fvar n))) :: (n, T_nat) :: gamma)
                (open 0 ts (term_fvar n))
                t ->
      are_equal tvars gamma (tmatch tn t0 ts) t

| AERec:
    forall tvars gamma T tn t0 ts t n p,
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
      ~(n ∈ tvars) ->
      ~(p ∈ tvars) ->
      is_annotated_term ts ->
      has_type tvars gamma tn T_nat ->
      is_type tvars ((n,T_nat) :: gamma) (open 0 T (term_fvar n)) ->
      are_equal tvars ((p, T_equal tn zero) :: gamma) t0 t ->
      are_equal tvars
        ((p, T_equal tn (succ (term_fvar n))) :: (n, T_nat) :: gamma)
        (open 0 (open 1 ts (term_fvar n)) (lambda T_unit (rec T (term_fvar n) t0 ts)))
        t ->
      are_equal tvars gamma (rec T tn t0 ts) t

| AEWeakHyp:
    forall tvars gamma1 gamma2 x T T' u v,
      ~(x ∈ support gamma2) ->
      is_subtype tvars gamma2 T T' ->
      are_equal tvars (gamma1 ++ (x,T') :: gamma2) u v ->
      are_equal tvars (gamma1 ++ (x,T) :: gamma2) u v

| AESplitBool:
    forall tvars gamma1 gamma2 b t t' x,
      ~(x ∈ fv_context gamma1) ->
      ~(x ∈ support gamma2) ->
      ~(x ∈ fv t) ->
      ~(x ∈ fv t') ->
      ~(x ∈ tvars) ->
      has_type tvars gamma2 b T_bool ->
      are_equal tvars (gamma1 ++ (x,T_equal b ttrue) :: gamma2) t t' ->
      are_equal tvars (gamma1 ++ (x,T_equal b tfalse) :: gamma2) t t' ->
      are_equal tvars (gamma1 ++ gamma2) t t'

| AESplitNat:
    forall tvars gamma1 gamma2 n t t' x y,
      ~(x ∈ fv_context gamma1) ->
      ~(x ∈ support gamma2) ->
      ~(y ∈ fv_context gamma1) ->
      ~(y ∈ support gamma2) ->
      ~(x ∈ fv t) ->
      ~(x ∈ fv t') ->
      ~(y ∈ fv t) ->
      ~(y ∈ fv t') ->
      ~(x = y) ->
      ~(x ∈ tvars) ->
      ~(y ∈ tvars) ->
      has_type tvars gamma2 n T_nat ->
      are_equal tvars (gamma1 ++ (x,T_equal n zero) :: gamma2) t t' ->
      are_equal tvars (gamma1 ++ (x,T_equal n (succ (term_fvar y))) :: (y, T_nat) :: gamma2) t t' ->
      are_equal tvars (gamma1 ++ gamma2) t t'

| AEError:
    forall tvars gamma e T1 T2,
      has_type tvars gamma e T1 ->
      are_equal tvars gamma (err T2) e ->
      are_equal tvars gamma ttrue tfalse

| AESplitIte:
    forall tvars gamma1 gamma2 b e1 e2 t t' e x y,
      ~(x ∈ fv_context gamma1) ->
      ~(x ∈ support gamma2) ->
      ~(y ∈ fv_context gamma1) ->
      ~(y ∈ support gamma2) ->
      ~(x ∈ fv t) ->
      ~(x ∈ fv t') ->
      ~(y ∈ fv t) ->
      ~(y ∈ fv t') ->
      ~(x = y) ->
      ~(x ∈ tvars) ->
      ~(y ∈ tvars) ->

      has_type tvars gamma2 b T_bool ->
      is_context tvars (gamma1 ++ ((x, T_equal (ite b e1 e2) e)  :: gamma2)) ->
      are_equal tvars (gamma1 ++ (x, T_equal e1 e) :: (y, T_equal b ttrue) :: gamma2) t t' ->
      are_equal tvars (gamma1 ++ (x, T_equal e2 e) :: (y, T_equal b tfalse) :: gamma2) t t' ->
      are_equal tvars (gamma1 ++ ((x, T_equal (ite b e1 e2) e)  :: gamma2)) t t'

| AESplitMatch:
  forall tvars gamma1 gamma2 n t t' e1 e2 e x y v,
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
    ~(x ∈ tvars) ->
    ~(y ∈ tvars) ->
    ~(v ∈ tvars) ->
    is_annotated_term e2 ->
    NoDup (x :: y :: v :: nil) ->

    has_type tvars gamma2 n T_nat ->
    is_context tvars (gamma1 ++ ((x, T_equal (tmatch n e1 e2) e)  :: gamma2)) ->
    are_equal tvars (gamma1 ++ (x, T_equal e1 e) :: (y, T_equal n zero) :: gamma2) t t' ->
    are_equal tvars (gamma1 ++ (x, T_equal (open 0 e2 (term_fvar v)) e) ::
                         (y, T_equal n (succ (term_fvar v))) ::
                         (v, T_nat) ::
                         gamma2)
              t t' ->
    are_equal tvars (gamma1 ++ ((x, T_equal (tmatch n e1 e2) e)  :: gamma2)) t t'

| AESplitRec:
  forall tvars gamma1 gamma2 n t t' T e1 e2 e x y v,
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
    ~(x ∈ tvars) ->
    ~(y ∈ tvars) ->
    ~(v ∈ tvars) ->
    is_annotated_term e2 ->
    NoDup (x :: y :: v :: nil) ->

    has_type tvars gamma2 n T_nat ->
    is_context tvars (gamma1 ++ ((x, T_equal (rec T n e1 e2) e)  :: gamma2)) ->
    is_type tvars gamma2 (open 0 T (term_fvar x)) ->
    are_equal tvars (gamma1 ++ (x, T_equal e1 e) :: (y, T_equal n zero) :: gamma2) t t' ->
    are_equal tvars (gamma1 ++ (x, T_equal
                               (open 0 (open 1 e2 (term_fvar v))
                                             (lambda T_unit (rec T (term_fvar v) e1 e2)))
                               e) ::
                          (y, T_equal n (succ (term_fvar v))) ::
                          (v, T_nat) ::
                          gamma2
              ) t t' ->
    are_equal tvars (gamma1 ++ ((x, T_equal (rec T n e1 e2) e)  :: gamma2)) t t'
.

Scheme mut_has_type        := Induction for has_type    Sort Prop
  with mut_is_context      := Induction for is_context  Sort Prop
  with mut_is_type         := Induction for is_type     Sort Prop
  with mut_is_subtype      := Induction for is_subtype  Sort Prop
  with mut_are_equal       := Induction for are_equal   Sort Prop.

Combined Scheme mut_HT_IT_IC_IS_AE from
         mut_has_type, mut_is_type, mut_is_context, mut_is_subtype, mut_are_equal.

Ltac t_invert_context :=
  match goal with
  | H: is_context (_ :: _) |- _ => inversion H; clear H
  end.
