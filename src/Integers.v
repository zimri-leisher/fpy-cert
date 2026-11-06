From Stdlib Require Import ZArith.

Local Open Scope Z_scope.

Definition in_int32_bounds (z : Z) : bool :=
    ((-2^31 <=? z) && (z <=? 2^31 - 1))%bool.