Require Export SystemFR.ErasedRec.

(*

| HTUnfoldZ:
    forall tvars gamma t n T0 Ts,
      wf T0 0 ->
      wf Ts 0 ->
      twf T0 0 ->
      twf Ts 1 ->
      are_equal tvars gamma n zero ->
      annotated_reducible tvars gamma t (T_rec n T0 Ts) ->
      annotated_reducible tvars gamma (tunfold t) T0

| HTUnfoldS:
    forall tvars gamma t n T0 Ts,
      is_annotated_term n ->
      wf n 0 ->
      wf T0 0 ->
      wf Ts 0 ->
      twf T0 0 ->
      twf Ts 1 ->
      are_equal tvars gamma (spositive n) ttrue ->
      annotated_reducible tvars gamma t (T_rec n T0 Ts) ->
      annotated_reducible tvars gamma (tunfold t) (topen 0 Ts (T_rec (tpred n) T0 Ts))

| HTUnfoldIn:
    forall tvars gamma t1 t2 n T0 Ts p1 p2 y T,
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
      ~(y ∈ tvars) ->
      ~(y ∈ support gamma) ->
      ~(y ∈ fv t1) ->
      ~(y ∈ fv t2) ->
      ~(y ∈ fv n) ->
      ~(y ∈ fv T0) ->
      ~(y ∈ fv Ts) ->
      ~(y ∈ fv T) ->
      NoDup (p1 :: p2 :: y :: nil) ->
      is_annotated_term n ->
      is_annotated_type T0 ->
      is_annotated_type Ts ->
      wf n 0 ->
      wf T0 0 ->
      wf Ts 0 ->
      twf T0 0 ->
      twf Ts 1 ->
      wf t2 0 ->
      annotated_reducible tvars gamma t1 (T_rec n T0 Ts) ->
      annotated_reducible tvars
               ((p2, T_equiv n zero) ::
                (p1, T_equiv t1 (tfold (T_rec n T0 Ts) (fvar y term_var))) ::
                (y, T0) :: gamma)
               (open 0 t2 (fvar y term_var)) T ->
      annotated_reducible tvars
               ((p1, T_equiv t1 (tfold (T_rec n T0 Ts) (fvar y term_var))) ::
                (y, topen 0 Ts (T_rec (tpred n) T0 Ts)) ::
                gamma)
               (open 0 t2 (fvar y term_var)) T ->
      annotated_reducible tvars gamma (tunfold_in t1 t2) T

| HTUnfoldPosIn:
    forall tvars gamma t1 t2 n T0 Ts p1 y T,
      ~(p1 ∈ tvars) ->
      ~(p1 ∈ support gamma) ->
      ~(p1 ∈ fv t1) ->
      ~(p1 ∈ fv t2) ->
      ~(p1 ∈ fv n) ->
      ~(p1 ∈ fv T0) ->
      ~(p1 ∈ fv Ts) ->
      ~(p1 ∈ fv T) ->
      ~(y ∈ tvars) ->
      ~(y ∈ support gamma) ->
      ~(y ∈ fv t1) ->
      ~(y ∈ fv t2) ->
      ~(y ∈ fv n) ->
      ~(y ∈ fv T0) ->
      ~(y ∈ fv Ts) ->
      ~(y ∈ fv T) ->
      NoDup (p1 :: y :: nil) ->
      is_annotated_term n ->
      is_annotated_type T0 ->
      is_annotated_type Ts ->
      wf n 0 ->
      wf T0 0 ->
      wf Ts 0 ->
      twf T0 0 ->
      twf Ts 1 ->
      wf t2 0 ->
      annotated_reducible tvars gamma t1 (T_rec n T0 Ts) ->
      are_equal tvars gamma (annotated_tlt zero n) ttrue ->
      annotated_reducible tvars
               ((p1, T_equiv t1 (tfold (T_rec n T0 Ts) (fvar y term_var))) ::
                (y, topen 0 Ts (T_rec (tpred n) T0 Ts)) ::
                gamma)
               (open 0 t2 (fvar y term_var)) T ->
      annotated_reducible tvars gamma (tunfold_pos_in t1 t2) T

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
      annotated_reducible tvars gamma n T_nat ->
      annotated_reducible tvars ((p, T_equiv n zero) :: gamma) t T0 ->
      annotated_reducible tvars
               ((p, T_equiv n (succ (fvar pn term_var))) :: (pn, T_nat) :: gamma)
               t
               (topen 0 Ts (T_rec (fvar pn term_var) T0 Ts)) ->
      annotated_reducible tvars gamma (tfold (T_rec n T0 Ts) t) (T_rec n T0 Ts)
*)
