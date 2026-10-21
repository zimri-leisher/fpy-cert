From FpyCert Require Import syntax.
From Stdlib Require Import String.
Open Scope string_scope.

Inductive ty : Type :=
    | F64 : ty
    | I64 : ty.

Definition context := string -> option ty.

Definition is_subtype (t1 t2 : ty) : bool.
Admitted.

Definition common_type (t1 t2 : ty) : option ty :=
    if is_subtype t1 t2 then Some t2 else
    if is_subtype t2 t1 then Some t1 else
    None.
    
    

Inductive has_type : context -> expr -> ty -> Prop :=
    | T_I64 : forall Gamma x,
        has_type Gamma (IntLiteral x) I64
    | T_F64 : forall Gamma x,
        has_type Gamma (FloatLiteral x) F64
    | T_Plus : forall Gamma x y t1 t2 t3,
        has_type Gamma x t1 ->
        has_type Gamma y t2 ->
        Some t3 = common_type t1 t2 ->
        has_type Gamma (Plus x y) t3.
        