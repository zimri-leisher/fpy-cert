From Stdlib Require Import ZArith.

Definition int_syntax := Number.signed_int.

Inductive expr : Set :=
| IntLiteral (x:int_syntax)
| Plus (v1:expr) (v2:expr)
.



Fixpoint denote_expr (e:expr) : Z :=
    match e with
    | IntLiteral x => Z.of_num_int x
    | Plus v1 v2 => Z.add (denote_expr v1) (denote_expr v2)
end.

