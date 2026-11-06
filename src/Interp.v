From FpyCert Require Import Syntax.


Definition SemTy := Value -> Prop.

Definition interp_unit (v : Value) : Prop :=
    v = v_unit.

Definition interp_bool (v : Value) : Prop :=
    exists b, v = v_bool b.

Definition interp_int32 (v : Value) : Prop :=
    exists z, v = v_int32 z.

Definition interp_singleton (base : SemTy) (s : Value) (v : Value) : Prop :=
    base v /\ s = v.

Definition interp_or (a b : SemTy) (v : Value) : Prop :=
    a v \/ b v.

Definition interp_top (v : Value) : Prop := True.

Definition interp_bot (v : Value) : Prop := False.


Fixpoint interp (T : Ty) : SemTy :=
    match T with
    | T_Unit => interp_unit
    | T_Bool => interp_bool
    | T_Int32 => interp_int32
    | T_Singleton base s => interp_singleton (interp base) s
    | T_Or a b => interp_or (interp a) (interp b)
    | T_Top => interp_top
    | T_Bot => interp_bot
    end.

Definition term_has_semtype (env : list Value) (t : Term) (ty : SemTy) : Prop :=
    forall fuel r, eval fuel env t = Some r ->
        exists v, r = Some v /\ ty v.


