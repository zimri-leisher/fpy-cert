From Stdlib Require Import ZArith.
From FpyCert Require Import Syntax.
From ITree Require Import ITree.

Import ITreeNotations.
Local Open Scope itree_scope.
Local Open Scope Z_scope.


Variant FpyEvent : Type -> Type :=
    | Overflow : FpyEvent void
    | GetTlm : Z -> FpyEvent Value
    | TlmNotFound : Z -> FpyEvent void
    .

Definition FpyTree : Type := itree FpyEvent Value.


Definition eval_bin_op (op: BinOp) (v1 v2: Value) : FpyTree :=
    match op, v1, v2 with
    | BinOp_Add, v_int32 z1, v_int32 z2 => 
        let res := z1 + z2 in
        if ((res >? 2 ^ 31 - 1) || (res <? - 2 ^ 31))%bool then
            Vis Overflow (fun x : void => match x with end)
        else
            Ret (v_int32 res)
    | _, _, _ => Ret (v_int32 0)
    end.


Fixpoint denote_term (o : Term) : FpyTree :=
    match o with
    | t_unit => Ret v_unit
    | t_bool b => Ret (v_bool b)
    | t_int32 z => Ret (v_int32 z)
    | t_bin_op op t1 t2 =>
        lhs <- denote_term t1 ;;
        rhs <- denote_term t2 ;;
        eval_bin_op op lhs rhs
    | t_tlm_ident i =>
        trigger (GetTlm i)
    end.


Definition tlm_env := Z -> option Value.


Definition handle_fpy_event : forall T, FpyEvent T -> tlm_env -> itree FpyEvent (tlm_env * T) :=
    fun _ e env =>
        match e with
        | GetTlm z =>
            match env z with
            | Some v => Ret (env, v)
            | None => Vis (TlmNotFound z) (fun x : void => match x with end)
            end
        | e' => Vis e' (fun x => Ret (env, x))
        end.