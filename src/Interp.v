From FpyCert Require Import Syntax.


Definition SemTy := Value -> Prop.

Definition term_has_semtype (env : list Value) (t : Term) (ty : SemTy) : Prop :=
    forall fuel r, eval fuel env t = Some r ->
        exists v, r = Some v /\ ty v.