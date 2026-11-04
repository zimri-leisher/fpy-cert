From Stdlib Require Import ZArith Bool.
From ITree Require Import ITree.
From FpyCert Require Import Syntax.

Import ITreeNotations.
Open Scope itree_scope.
Open Scope Z_scope.

(* Fixpoint denote_expr (e:expr) : itree fpye_event Z :=
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
end. *)

