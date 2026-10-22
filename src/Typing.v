From FpyCert Require Import syntax.
From Stdlib Require Import String ZArith Bool Lia List.
Open Scope string_scope.
Import ListNotations.

Inductive signedness : Type := Signed | Unsigned.
Inductive int_width : Type := IW8 | IW16 | IW32 | IW64.
Inductive float_width : Type := FW32 | FW64.

Inductive ty : Type :=
    | TInt (s : signedness) (w : int_width)
    | TFloat (w : float_width)
    | TBool.

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

Definition int_types : list ty := [I8; I16; I32; I64; U8; U16; U32; U64].

Definition float_types : list ty := [F32; F64].

Definition context := string -> option ty.

Open Scope Z_scope.

Definition int_bits (w : int_width) : Z :=
    match w with IW8 => 8 | IW16 => 16 | IW32 => 32 | IW64 => 64 end.

Definition int_min (s : signedness) (bits : Z) : Z :=
    match s with
        | Unsigned => 0
        | Signed => -(2 ^ (bits - 1))
    end.

Definition int_max (s : signedness) (bits : Z) : Z :=
    match s with
        | Unsigned => 2 ^ bits - 1
        | Signed => 2 ^ (bits - 1) - 1
    end.

Definition float_bits (w : float_width) : Z :=
    match w with FW32 => 32 | FW64 => 64 end.

Definition is_subtype (t1 t2 : ty) : bool :=
    match t1, t2 with
        | TInt s1 w1, TInt s2 w2 => 
            ((int_min s1 (int_bits w1)) >=? (int_min s2 (int_bits w2))) && 
            ((int_max s1 (int_bits w1)) <=? (int_max s2 (int_bits w2)))
        | TFloat w1, TFloat w2 => float_bits w1 <=? float_bits w2
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

Definition common_type (t1 t2 : ty) : option ty :=
    match t1, t2 with
        | TInt _ _, TInt _ _ => 
            find (fun t => is_subtype t1 t && is_subtype t2 t) int_types
        | TFloat _, TFloat _ =>
            find (fun t => is_subtype t1 t && is_subtype t2 t) float_types
        | TBool, TBool => Some TBool
        | _, _ => None
    end.

Definition fact_common_type_always_supertype : Prop :=
    forall t1 t2 t3,
        common_type t1 t2 = Some t3 ->
        is_subtype t1 t3 = true /\
        is_subtype t2 t3 = true.


Definition fact_no_common_type_means_no_supertype : Prop :=
    forall t1 t2,
        common_type t1 t2 = None ->
        ~ exists t3, is_subtype t1 t3 = true /\ is_subtype t2 t3 = true.


Definition 



Definition ll_float  := Floats.float32.
Definition ll_double := Floats.float.

    
    

Fixpoint has_type2 (c : context) (e : expr) (t : ty) : bool :=
    match e with
    | IntLiteral x => t = I64
    | FloatLiteral y => t = F64
    | Plus a b => let ct := common_type 

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
        