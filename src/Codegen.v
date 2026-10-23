From Stdlib Require Import ZArith String List.
From ExtLib Require Import Structures.Maps.

From ITree Require Import ITree.

From Vellvm Require Import Syntax Utils Params Semantics Interfaces.Memory ParamsV IPtrInfinite.
From FpyCert Require Import LLVMBuilder Syntax.
From ExtLib Require Import Structures.Monads Data.Monads.StateMonad.
Import ListNotations MonadNotation.
Open Scope string_scope. Open Scope monad_scope.



Record cg_state := mk_cg_state { cg_next : Z; cg_reversed_code : code dtyp}.

(* monad state to hold codegen info *)
Definition CG := state cg_state.

Definition fresh_raw_id : CG raw_id :=
    s <- get ;; put (mk_cg_state (cg_next s + 1) (cg_reversed_code s)) ;; ret (Anon (cg_next s)).

Definition emit_llvm_exp_as_temp_var (e : llexpr) : CG (llexpr) :=
    x <- fresh_raw_id ;; 
    state <- get ;;
    put (mk_cg_state (cg_next state) (LL.assign x (INSTR_Op e) :: cg_reversed_code state)) ;;
    ret (LL.local x).

Fixpoint emit_exp (e : expr) : CG (llexpr) :=
    match e with
    | IntLiteral x => ret (LL.int_lit (Z.of_num_int x))
    | Plus e1 e2 => 
        lhs <- emit_exp e1 ;;
        rhs <- emit_exp e2 ;;
        emit_llvm_exp_as_temp_var (LL.add LL.i64 lhs rhs)
    end.

Definition ex1 : expr := (Plus (Plus (lit 2) (lit 3)) (lit 4)).

Definition emit_main_block (e : expr) : LLVMAst.block dtyp :=
    let '(v, s) := runState (emit_exp e) (mk_cg_state 0 []) in
    LL.block (Name "entry") (rev (cg_reversed_code s)) (LL.ret LL.i64 v).

Definition ex1_main := (emit_main_block (ex1)).

Compute show ex1_main.

Definition emit_program (block : LLVMAst.block dtyp) : mcfg dtyp :=
    LL.program [LL.fn "main" [] block []].

Definition ex1_prog := emit_program ex1_main.

Compute show ex1_prog.
