From Stdlib Require Import ZArith.
From FpyCert Require Import Syntax State.
From ITree Require Import ITree Events.State.
Import ITree.Basics.Basics.Monads.

Import ITreeNotations.
Local Open Scope itree_scope.
Local Open Scope Z_scope.

Variant PanicE : Type -> Type :=
    | Overflow : PanicE void
    | TlmNotFound : Z -> PanicE void
    .

Variant HostE : Type -> Type :=
    | GetTlm : Z -> HostE Value
    .

Definition BaseE := PanicE +' HostE.

Definition FinalE := PanicE.

Definition BaseTree : Type := itree BaseE Value.

Definition FinalTree : Type := itree FinalE (tlm_env * Value).

Definition eval_bin_op (op: BinOp) (v1 v2: Value) : BaseTree :=
    match op, v1, v2 with
    | BinOp_Add, v_int z1, v_int z2 => 
        let res := z1 + z2 in
        Ret (v_int res)
    | _, _, _ => Ret (v_int 0)
    end.


Fixpoint denote_term (o : Term) : BaseTree :=
    match o with
    | t_value v => Ret v
    | t_bin_op op t1 t2 =>
        lhs <- denote_term t1 ;;
        rhs <- denote_term t2 ;;
        eval_bin_op op lhs rhs
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

