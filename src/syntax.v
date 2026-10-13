From Stdlib Require Import ZArith String List.
From ExtLib Require Import Structures.Maps.

From ITree Require Import ITree.

From Vellvm Require Import Syntax Utils Params Semantics Interfaces.Memory ParamsV IPtrInfinite.

Import ListNotations.
Open Scope string_scope.

#[local] Instance Pa : Params := @ParamsV IPZ IPZTheory.


Definition int_syntax := Number.signed_int.

Inductive expr : Set :=
| IntLiteral (x:int_syntax)
| Plus (v1:expr) (v2:expr)
.

Variant fpye_event : Type -> Type :=
| Overflow : fpye_event void.


Fixpoint denote_expr (e:expr) : itree fpye_event Z :=
    match e with
    | IntLiteral x => Ret (Z.of_num_int x)
    | Plus lhs rhs =>
    lhs_val <- denote_expr lhs ;;
    rhs_val <- denote_expr rhs ;;
    let result := lhs_val + rhs_val in
    (* Okay, now I want to check if the result is representable in I64*)
    if Z.leb (- 2 ^ 63) result && Z.leb result ((2 ^ 63) - 1) then
        Ret result
    else
        (* This magic allows us to avoid giving a value to v??*)
        v <- trigger Overflow ;; match v : void with end
end.



Definition lit (z : Z) : expr := IntLiteral (Z.to_num_int z).

Definition ex1 : expr := Plus (lit 2) (lit (2 ^ 63)).

Compute denote_expr ex1.

Definition llvm_i64 : dtyp := DTYPE_I 64.

Definition llvm_int_lit (z : Z) : exp dtyp := EXP_Integer (Z.to_num_int z).

Definition test_add_instr : instr dtyp :=
    INSTR_Op (OP_IBinop (LLVMAst.Add false false) llvm_i64 (llvm_int_lit 2) (llvm_int_lit 3)).

Definition entry : block dtyp :=
    {|
        blk_id := Name "entry";
        blk_phis := [];
        blk_code := [(IId (Name "sum"), test_add_instr, [])];
        blk_term := (IVoid 0, TERM_Ret (llvm_i64, EXP_Ident (ID_Local (Name "sum"))), []);
        blk_comments := None;
    |}.

Definition main_def : definition dtyp (block dtyp * list (block dtyp)) :=
    {|
        df_prototype :=
        {|
            dc_name := Name "main";
            dc_type := (DTYPE_Pointer : dtyp);
            dc_param_attrs := ([], []);
            dc_attrs := [];
            dc_annotations := [];
        |};
        df_args := [];
        df_instrs := (entry, [])
    |}.

Definition prog : mcfg dtyp :=
    mcfg_of_modul (modul_of_toplevel_entities [TLE_Definition main_def]).

Definition prog_den : MCFGtop dvalue :=
    denote_vellvm llvm_i64 (Name "main") [] prog.

Definition prog_result : MCFGbot (Res dvalue) :=
    interp_mcfg prog_den
        (initial_state, ((Build_stack_frame Maps.empty None None, []), Maps.empty)).

Variant outcome {E : Type -> Type} {R : Type} :=
| Done (r: R)
| OutOfFuel
| Event (X : Type) (e : E X).
Arguments outcome : clear implicits.

Fixpoint run {E R} (n : nat) (t : itree E R) : outcome E R :=
    match n with
    | O => OutOfFuel
    | S n => match observe t with
        | RetF r => Done r
        | TauF t' => run n t'
        | VisF X e _ => Event X e
        end
    end.

Definition result_value (o : outcome MCFGEbot (Res dvalue)) : outcome MCFGEbot dvalue :=
    match o with
    | Done r => Done (snd r)
    | OutOfFuel => OutOfFuel
    | Event X e => Event X e
    end.

Compute result_value (run 1000 prog_result).



