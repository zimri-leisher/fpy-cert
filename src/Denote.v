From Stdlib Require Import ZArith String.
From FpyCert Require Import Syntax State.
From ITree Require Import ITree Events.State.
From Vellvm Require Import Floats Integers.
Import ITree.Basics.Basics.Monads.

Import ITreeNotations.
Local Open Scope itree_scope.
Local Open Scope Z_scope.
Local Open Scope string_scope.

Variant PanicE : Type -> Type :=
    | Overflow : PanicE void
    | TlmNotFound : Z -> PanicE void
    .

Variant HostE : Type -> Type :=
    | GetTlm : Z -> HostE Value
    .

Variant IllFormedE : Type -> Type :=
    | TypeError : string -> IllFormedE void
    .

Definition BaseE := (PanicE +' IllFormedE) +' HostE.

Definition FinalE := PanicE +' IllFormedE.

Definition BaseTree : Type := itree BaseE Value.

Definition FinalTree : Type := itree FinalE (tlm_env * Value).

Definition int_to_i64 (z : Z) : @bit_int 64 :=
    @repr 64 z.

Variant OpResult :=
    | OpOk (v : Value)
    | OpOverflow
    | OpIllTyped
    .

Definition eval_bin_op (op : BinOp) (v1 v2 : Value) : OpResult :=
    match op, v1, v2 with
    | BinOp_Add, v_int z1, v_int z2 => 
        OpOk (v_int (z1 + z2))
    | BinOp_Add, v_f64 f1, v_f64 f2 =>
        OpOk (v_f64 (Float.add f1 f2))
    | _, _, _ => OpIllTyped
    end.

Definition denote_bin_op (op : BinOp) (v1 v2 : Value) : BaseTree :=
    match eval_bin_op op v1 v2 with
    | OpOk v => Ret v
    | OpOverflow => x <- trigger Overflow ;; match x : void with end
    | OpIllTyped => x <- trigger (TypeError "ill typed") ;; match x : void with end
    end.

Fixpoint denote_term (o : Term) : BaseTree :=
    match o with
    | t_value v => Ret v
    | t_bin_op op t1 t2 =>
        lhs <- denote_term t1 ;;
        rhs <- denote_term t2 ;;
        denote_bin_op op lhs rhs
    | t_tlm_ident i =>
        trigger (GetTlm i)
    end.


Definition handler_host : HostE ~> stateT tlm_env (itree FinalE) :=
    fun _ e env =>
        match e with
        | GetTlm z =>
            match env z with
            | Some v => Ret (env, v)
            | None => vis (TlmNotFound z) (fun x : void => match x with end)
            end
        end.


Definition handler_base : BaseE ~> stateT tlm_env (itree FinalE) :=
    case_ pure_state handler_host.

Definition handle_base_events (t : BaseTree) (env : tlm_env) : FinalTree :=
    interp_state handler_base t env.

