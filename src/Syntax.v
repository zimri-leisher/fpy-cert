From Stdlib Require Import ZArith.

Inductive Value : Type :=
    | v_unit : Value
    | v_bool : bool -> Value
    | v_int : Z -> Value
    .

Variant BinOp : Set :=
    | BinOp_Add
    .

Inductive Term : Type :=
    | t_value : Value -> Term
    | t_bin_op : BinOp -> Term -> Term -> Term
    | t_tlm_ident : Z -> Term
    .

Inductive Ty : Set :=
    | T_Unit : Ty
    | T_Bool : Ty
    | T_Int : Ty
    | T_Singleton : Ty -> Value -> Ty
    | T_Or : Ty -> Ty -> Ty
    | T_Top : Ty
    | T_Bot : Ty
    .

