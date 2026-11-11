From Stdlib Require Import ZArith.
From FpyCert Require Import Syntax Evaluate State Integers SyntacticTyping.

Definition SemTy := Value -> Prop.

Definition interp_unit (v : Value) : Prop :=
    v = v_unit.

Definition interp_bool (v : Value) : Prop :=
    exists b, v = v_bool b.

Definition interp_int32 (v : Value) : Prop :=
    exists z, in_int32_bounds z = true /\ v = v_int z.

Definition interp_singleton (base : SemTy) (s : Value) (v : Value) : Prop :=
    base v /\ s = v.

Definition interp_or (a b : SemTy) (v : Value) : Prop :=
    a v \/ b v.

Definition interp_top (v : Value) : Prop := True.

Definition interp_bot (v : Value) : Prop := False.


Fixpoint syn_to_sem_ty (T : Ty) : SemTy :=
    match T with
    | T_Unit => interp_unit
    | T_Bool => interp_bool
    | T_Int => interp_int32
    | T_Top => interp_top
    | T_Bot => interp_bot
    | T_Or a b => interp_or (syn_to_sem_ty a) (syn_to_sem_ty b)
    | T_Singleton base value => interp_singleton (syn_to_sem_ty base) value
    end.

(* If t finishes with value v, then v has type ty*)
Definition sem_typed_after_evaluation (t : Term) (env : tlm_env) (ty : SemTy) : Prop :=
    forall fuel v, eval_term fuel t env = Done v -> ty v.

Definition env_matches_ctx (env : tlm_env) (ctx : tlm_ctx) : Prop :=
    forall z v syn_ty,
    (ctx z) = Some syn_ty ->
    (env z) = Some v ->
    (syn_to_sem_ty syn_ty) v.

Definition sem_typed (ctx : tlm_ctx) (t : Term) (ty : Ty) : Prop :=
    forall env,
    env_matches_ctx env ctx ->
    sem_typed_after_evaluation t env (syn_to_sem_ty ty).

Definition sem_subtype (a b : Ty) : Prop :=
    forall v, (syn_to_sem_ty a) v -> (syn_to_sem_ty b) v.