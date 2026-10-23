From Stdlib Require Import ZArith String List.
From ExtLib Require Import Structures.Monads Data.Monads.StateMonad.
From Vellvm Require Import Syntax Utils.
Import ListNotations MonadNotation.
Open Scope string_scope. Open Scope monad_scope.

Notation llexpr := (exp dtyp).

Module LL.

Definition i64 : dtyp := DTYPE_I 64.
Definition i1 : dtyp := DTYPE_I 1.
Definition int_lit (z : Z) : llexpr := EXP_Integer (Z.to_num_int z).
Definition local (x : raw_id) : llexpr := EXP_Ident (ID_Local x).
Definition add (t : dtyp) (a b : llexpr) : llexpr := OP_IBinop (LLVMAst.Add false false) t a b.
Definition assign (x : raw_id) (i : instr dtyp) : instr_id * instr dtyp * list (metadata dtyp) := (IId x, i, []).
Definition ret (t : dtyp) (e : llexpr) : terminator dtyp := TERM_Ret (t, e).
Definition br_if (c : llexpr) (bt bf : block_id) : terminator dtyp := TERM_Br (i1, c) bt bf.
Definition block (name : block_id) (c : code dtyp) (t : terminator dtyp) : LLVMAst.block dtyp :=
    {|
        blk_id := name;
        blk_phis := [];
        blk_code := c;
        blk_term := (IVoid 0, t, []);
        blk_comments := None;
    |}.

Definition fn (name : string) (args : list raw_id) (entry : LLVMAst.block dtyp) (rest : list (LLVMAst.block dtyp))
    : definition dtyp (LLVMAst.block dtyp * list (LLVMAst.block dtyp)) :=
    {|
        df_prototype := {|
            dc_name := Name name;
            dc_type := (DTYPE_Pointer : dtyp);
            dc_param_attrs := ([], []);
            dc_attrs := [];
            dc_annotations := [];
        |};
        df_args := args;
        df_instrs := (entry, rest);
    |}.
Definition program fns : mcfg dtyp := mcfg_of_modul (modul_of_toplevel_entities (map TLE_Definition fns)).

End LL.
