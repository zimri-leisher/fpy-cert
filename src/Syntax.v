From Stdlib Require Import ZArith.

Inductive Value : Type :=
    | v_unit : Value
    | v_bool : bool -> Value
    | v_int32 : Z -> Value
    .

Inductive Ty : Set :=
    | T_Unit : Ty
    | T_Bool : Ty
    | T_Int32 : Ty
    | T_Singleton : Ty -> Value -> Ty
    | T_Or : Ty -> Ty -> Ty
    | T_Top : Ty
    | T_Bot : Ty
    .

Variant BinOp : Set :=
    | BinOp_Add
    .

Inductive Term : Type :=
    | t_unit : Term
    | t_bool : bool -> Term
    | t_int32 : Z -> Term
    | t_app : Term -> Term -> Term
    | t_bin_op : BinOp -> Term -> Term -> Term
    .




(* 

Variant fpye_event : Type -> Type :=
| Overflow : fpye_event void.


(* 
Definition lit (z : Z) : expr := IntLiteral (Z.to_num_int z).

Definition ex1 : expr := Plus (lit 2) (lit 3). *)



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



Compute run 100 (denote_expr ex1).

Definition llvm_i64 : dtyp := DTYPE_I 64.

Definition llvm_int_lit (z : Z) : exp dtyp := EXP_Integer (Z.to_num_int z).

Fixpoint emit_exp (e: expr) : exp dtyp :=
    match e with
    | IntLiteral x => llvm_int_lit (Z.of_num_int x)
    | Plus e1 e2 => OP_IBinop (LLVMAst.Add false false) llvm_i64 (emit_exp e1) (emit_exp e2)
    end.

Compute emit_exp ex1.

Definition test_add_instr : instr dtyp :=
    INSTR_Op (OP_IBinop (LLVMAst.Add false false) llvm_i64 (llvm_int_lit 2) (llvm_int_lit 3)).

Definition build_program_from_instr (i: instr dtyp) (return_type: dtyp) : mcfg dtyp :=
    let entry: block dtyp := {|
        blk_id := Name "entry";
        blk_phis := [];
        blk_code := [(IId (Name "value"), i, [])];
        blk_term := (IVoid 0, TERM_Ret (return_type, EXP_Ident (ID_Local (Name "value"))), []);
        blk_comments := None;
    |} in
    let main: definition dtyp (block dtyp * list (block dtyp)) :=
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
    |} in
    mcfg_of_modul (modul_of_toplevel_entities [TLE_Definition main]). *)

(*
Definition prog_den : MCFGtop dvalue :=
    denote_vellvm llvm_i64 (Name "main") [] prog.

Definition prog_result : MCFGbot (Res dvalue) :=
    interp_mcfg prog_den
        (initial_state, ((Build_stack_frame Maps.empty None None, []), Maps.empty)).

Compute result_value (run 1000 prog_result).

*)


