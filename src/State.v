From Stdlib Require Import ZArith List.
From FpyCert Require Import Syntax.

Import ListNotations.
Definition tlm_env := Z -> option Value.
Definition tlm_ctx := Z -> option Ty.

Definition env_of (l : list (Z * Value)) : tlm_env :=
    fun z => option_map snd (find (fun p => (fst p =? z)%Z) l).

Definition ctx_of (l : list (Z * Ty)) : tlm_ctx :=
    fun z => option_map snd (find (fun p => (fst p =? z)%Z) l).