From Stdlib Require Import ZArith.
From FpyCert Require Import Syntax.
Definition tlm_env := Z -> option Value.
Definition tlm_ctx := Z -> option Ty.