Inductive star {T} (R: T -> T -> Prop): T -> T -> Prop :=
| Refl: forall t,
    star R t t
| Trans: forall t1 t2 t3,
    R t1 t2 ->
    star R t2 t3 ->
    star R t1 t3.

Hint Resolve Refl: smallstep.
Hint Resolve Trans: smallstep.
