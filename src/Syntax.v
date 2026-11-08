From Stdlib Require Import ZArith.
From Vellvm Require Import Floats Integers.

Variant Value : Set :=
    | v_unit : Value
    | v_bool : bool -> Value
    | v_int : Z -> Value
    | v_f64 : float -> Value
    | v_i64 : @bit_int 64 -> Value
    .

Variant BinOp : Set :=
    | BinOp_Add
    .

Inductive Term : Set :=
    | t_value : Value -> Term
    | t_bin_op : BinOp -> Term -> Term -> Term
    | t_tlm_ident : Z -> Term
    .

Inductive Ty : Set :=
    | T_Unit : Ty
    | T_Bool : Ty
    | T_Int : Ty
    | T_F64 : Ty
    | T_I64 : Ty
    | T_Singleton : Ty -> Value -> Ty
    | T_Or : Ty -> Ty -> Ty
    | T_Top : Ty
    | T_Bot : Ty
    .

Fixpoint base_ty (t : Ty) : Ty :=
    match t with
    | T_Singleton b _ => base_ty b
    | _ => t
    end.