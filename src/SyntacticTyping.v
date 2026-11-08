From FpyCert Require Import Syntax State.


Inductive syn_typed (ctx : tlm_ctx) : Term -> Ty -> Prop :=
    | ST_Unit :
        syn_typed ctx (t_value v_unit) T_Unit
    | ST_Bool :
        forall b, syn_typed ctx (t_value (v_bool b)) T_Bool
    | ST_Int :
        forall z, syn_typed ctx (t_value (v_int z)) T_Int
    | ST_TlmIdent :
        forall i t,
        ctx i = Some t ->
        syn_typed ctx (t_tlm_ident i) t
    | ST_Selfify :
        forall v base,
        syn_typed ctx (t_value v) base ->
        syn_typed ctx (t_value v) (T_Singleton base v)
    | ST_BinOp :
        forall 
    .

(* Inductive signedness : Type := Signed | Unsigned.
Inductive int_width : Type := IW8 | IW16 | IW32 | IW64.
Inductive float_width : Type := FW32 | FW64.

Variant typ : Type :=
    | T_Int (s : signedness) (w : int_width)
    | T_Float (w : float_width)
    | T_Unit
    | T_True
    | T_False
    | T_Top
    | T_Bot
    | T_Or (a b : typ)
    | T_And (a b : typ)
    | T_Singleton (a : typ) (v : value).

Definition type_bits (t : typ) : positive :=
    match t with
    | T_Int _ w => 
        match w with IW8 => 8 | IW16 => 16 | IW32 => 32 | IW64 => 64 end
    | T_Float w => 
        match w with FW32 => 32 | FW64 => 64 end
    | T_Bool => 1
    end.

Notation Bool := (T_Bool).
Notation I8 := (T_Int Signed IW8).
Notation I16 := (T_Int Signed IW16).
Notation I32 := (T_Int Signed IW32).
Notation I64 := (T_Int Signed IW64).
Notation U8 := (T_Int Unsigned IW8).
Notation U16 := (T_Int Unsigned IW16).
Notation U32 := (T_Int Unsigned IW32).
Notation U64 := (T_Int Unsigned IW64).
Notation F32 := (T_Float FW32).
Notation F64 := (T_Float FW64).

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

Definition check_subtype (t1 t2 : typ) : bool :=
    match t1, t2 with
        | T_Int s1 w1, T_Int s2 w2 => 
            ((int_min s1 (type_bits t1)) >=? (int_min s2 (type_bits t2))) && 
            ((int_max s1 (type_bits t1)) <=? (int_max s2 (type_bits t2)))
        | T_Float w1, T_Float w2 => type_bits t1 <=? type_bits t2
        | T_Bool, T_Bool => true
        | _, _ => false
    end.

Definition common_type (t1 t2 : typ) : option typ :=
    match t1, t2 with
        | T_Int _ _, T_Int _ _ => 
            find (fun t => is_subtype t1 t && is_subtype t2 t) int_types
        | T_Float _, T_Float _ =>
            find (fun t => is_subtype t1 t && is_subtype t2 t) float_types
        | T_Bool, T_Bool => Some T_Bool
        | _, _ => None
    end.


Variant value : Set :=
    | VInt (s : signedness) (w : int_width) (x: @bit_int (type_bits w))
    | VF32 (x : Floats.float32)
    | VF64 (x : Floats.float)
    | VTrue
    | VFalse
    | VUnit
    .



Fixpoint type_of (c : context) (e : expr) : option typ :=
    match e with
    | IntLiteral x => Some I64
    (* | FloatLiteral y => Some F64 *)
    | Plus a b => 
        ty_a <- type_of c a ;;
        ty_b <- type_of c b ;;
        common_type ty_a ty_b
    end.


Definition firstorder_val (v : value) : Prop :=
    v = VUnit \/ v = VTrue \/ v = VFalse


Inductive is_subtype : context -> typ -> typ -> Prop :=
    | S_Refl : forall Gamma a,
        is_subtype Gamma a a
    | S_Trans : forall Gamma a b c,
        is_subtype Gamma a b \/ is_subtype Gamma b c ->
        is_subtype Gamma a c
    | S_Top : forall Gamma a,
        is_subtype Gamma a T_Top
    | S_Bot : forall Gamma a,
        is_subtype Gamma T_Bot a
    | S_OrLeft : forall Gamma a b,
        is_subtype Gamma a (T_Or a b)
    | S_OrRight : forall Gamma a b,
        is_subtype Gamma b (T_Or a b)
    | S_Or : forall Gamma a b c,
        is_subtype Gamma a c /\ is_subtype Gamma b c ->
        is_subtype Gamma (T_Or a b) c
    | S_AndLeft : forall Gamma a b,
        is_subtype Gamma (T_And a b) a
    | S_AndRight : forall Gamma a b,
        is_subtype Gamma (T_And a b) b
    | S_And : forall Gamma a b c,
        is_subtype Gamma c a /\ is_subtype Gamma c b ->
        is_subtype c (T_And a b)
    | S_SingletonBase : forall Gamma a v,
        is_subtype Gamma (T_Singleton a v) a
    | S_Singleton : forall Gamma a b v,
        is_subtype Gamma a b -> 
        is_subtype Gamma (T_Singleton a v) (T_Singleton b v)
    .


Variant op_compat : op -> typ -> Prop :=
    | OC_AddInt :
        forall s w,
        op_compat Op_Add (T_Int s w)
    | OC_AddFloat :
        forall w,
        op_compat Op_Add (T_Float w)
    .

Definition result_type (o: op) (t: typ) : typ :=
    F64.

Inductive has_type : context -> expr -> typ -> Prop :=
    | HT_Unit : forall Gamma,
        has_type Gamma E_Unit T_Unit
    | HT_True : forall Gamma,
        has_type Gamma E_True T_True
    | HT_False : forall Gamma,
        has_type Gamma E_False T_False
    | HT_I64 : forall Gamma x,
        has_type Gamma (IntLiteral x) I64
    | HT_Sub : forall Gamma v a b,
        has_type Gamma v a /\ is_subtype Gamma a b ->
        has_type Gamma v b
    | HT_Self : forall Gamma v a,
        firstorder a -> has_type v (T_Singleton a v)
    (* | HT_F64 : forall Gamma x,
        has_type Gamma (FloatLiteral x) F64 *)
    | HT_BinOp : forall v1 v2 a op,
        has_type Gamma v1 a /\ has_type v2 a /\ op_compat op a ->
        has_type Gamma  *)



