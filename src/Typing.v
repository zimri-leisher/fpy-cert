From FpyCert Require Import Syntax.
From Stdlib Require Import String ZArith Bool Lia List.
From ExtLib Require Import Structures.Monad Data.Monads.OptionMonad.
From Vellvm.Numeric Require Import Integers.
Import MonadNotation.
Open Scope string_scope.
Import ListNotations.

Inductive signedness : Type := Signed | Unsigned.
Inductive int_width : Type := IW8 | IW16 | IW32 | IW64.
Inductive float_width : Type := FW32 | FW64.

Variant typ : Type :=
    | TInt (s : signedness) (w : int_width)
    | TFloat (w : float_width)
    | TBool.

Definition type_bits (t : typ) : positive :=
    match t with
    | TInt _ w => 
        match w with IW8 => 8 | IW16 => 16 | IW32 => 32 | IW64 => 64 end
    | TFloat w => 
        match w with FW32 => 32 | FW64 => 64 end
    | TBool => 1
    end.

Notation Bool := (TBool).
Notation I8 := (TInt Signed IW8).
Notation I16 := (TInt Signed IW16).
Notation I32 := (TInt Signed IW32).
Notation I64 := (TInt Signed IW64).
Notation U8 := (TInt Unsigned IW8).
Notation U16 := (TInt Unsigned IW16).
Notation U32 := (TInt Unsigned IW32).
Notation U64 := (TInt Unsigned IW64).
Notation F32 := (TFloat FW32).
Notation F64 := (TFloat FW64).

Definition int_types : list typ := [I8; I16; I32; I64; U8; U16; U32; U64].

Definition float_types : list typ := [F32; F64].

Definition context := string -> option typ.

Open Scope Z_scope.
Open Scope monad_scope.

Coercion Zpos : positive >-> Z.

Definition int_min (s : signedness) (bits : positive) : Z :=
    match s with
        | Unsigned => 0
        | Signed => -(2 ^ (bits - 1))
    end.

Definition int_max (s : signedness) (bits : positive) : Z :=
    match s with
        | Unsigned => 2 ^ bits - 1
        | Signed => 2 ^ (bits - 1) - 1
    end.

Definition is_subtype (t1 t2 : typ) : bool :=
    match t1, t2 with
        | TInt s1 w1, TInt s2 w2 => 
            ((int_min s1 (type_bits t1)) >=? (int_min s2 (type_bits t2))) && 
            ((int_max s1 (type_bits t1)) <=? (int_max s2 (type_bits t2)))
        | TFloat w1, TFloat w2 => type_bits t1 <=? type_bits t2
        | TBool, TBool => true
        | _, _ => false
    end.

Definition fact_is_subtype_is_reflexive : Prop := 
    forall t, is_subtype t t = true.

Definition fact_is_subtype_is_transitive : Prop :=
    forall t1 t2 t3, 
        is_subtype t1 t2 = true -> 
        is_subtype t2 t3 = true -> 
        is_subtype t1 t3 = true.

Definition fact_is_subtype_is_antisymmetric : Prop :=
    forall t1 t2,
        is_subtype t1 t2 = true ->
        is_subtype t2 t1 = true ->
        t1 = t2.

(*
How could I state the real desired property of a subtype reln, which
is that if t1 <: t2, we can put a value of t1 in for wherever t2 is,
and the program won't get stuck?
*)

Definition common_type (t1 t2 : typ) : option typ :=
    match t1, t2 with
        | TInt _ _, TInt _ _ => 
            find (fun t => is_subtype t1 t && is_subtype t2 t) int_types
        | TFloat _, TFloat _ =>
            find (fun t => is_subtype t1 t && is_subtype t2 t) float_types
        | TBool, TBool => Some TBool
        | _, _ => None
    end.

(*
Also want to show that common type gives the "least supertype"
So what is least subtype? i8, u8, what is the least supertype? the subtype with the fewest bits?
What happens if the type doesn't have a static size? Maybe we just assume it's the bits for now
*)

Definition fact_common_type_always_smallest_bits_supertype : Prop :=
    forall t1 t2 t3,
        common_type t1 t2 = Some t3 ->
        ~ exists t4, (
            is_subtype t1 t4 = true /\
            is_subtype t2 t4 = true
        ) /\ type_bits t4 <? type_bits t3 = true.


Definition fact_common_type_always_supertype : Prop :=
    forall t1 t2 t3,
        common_type t1 t2 = Some t3 ->
        is_subtype t1 t3 = true /\
        is_subtype t2 t3 = true.


Definition fact_no_common_type_means_no_supertype : Prop :=
    forall t1 t2,
        common_type t1 t2 = None ->
        ~ exists t3, is_subtype t1 t3 = true /\ is_subtype t2 t3 = true.

(* TODO is symmetric the right word for this? *)
Definition fact_common_type_symmetric : Prop :=
    forall t1 t2,
        common_type t1 t2 = common_type t2 t1.

(* 
Variant value : Set :=
    | VInt (s : signedness) (w : int_width) (x: @bit_int (type_bits w))
    | VF32 (x : Floats.float32)
    | VF64 (x : Floats.float)
    | VBool (x : bool).
*)


Fixpoint type_of (c : context) (e : expr) : option typ :=
    match e with
    | IntLiteral x => Some I64
    | FloatLiteral y => Some F64
    | Plus a b => 
        ty_a <- type_of c a ;;
        ty_b <- type_of c b ;;
        common_type ty_a ty_b
    end.


Inductive has_type : context -> expr -> typ -> Prop :=
    | T_I64 : forall Gamma x,
        has_type Gamma (IntLiteral x) I64
    | T_F64 : forall Gamma x,
        has_type Gamma (FloatLiteral x) F64
    | T_Plus : forall Gamma x y t1 t2 t3,
        has_type Gamma x t1 ->
        has_type Gamma y t2 ->
        Some t3 = common_type t1 t2 ->
        has_type Gamma (Plus x y) t3.


