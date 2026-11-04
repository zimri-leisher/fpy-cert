(** Facts about the definitions in [Typing].

    This file states the properties we want of [is_subtype] and
    [common_type] as named [Prop]s (e.g. [fact_is_subtype_is_reflexive])
    and proves them. Some are not proved yet. *)

From FpyCert Require Import Typing.
From Stdlib Require Import ZArith.

Open Scope Z_scope.

(* Definition fact_is_subtype_is_reflexive : Prop :=
    forall t, is_subtype t t = true.

Definition fact_is_subtype_is_transitive : Prop :=
    forall t1 t2 t3,
        is_subtype t1 t2 = true ->
        is_subtype t2 t3 = true ->
        is_subtype t1 t3 = true.

Definition fact_is_subtype_is_antisymmetric : Prop :=
    forall t1 t2,
        is_subtype t1 t2 = true ->
        is_subtype t2 t1 = true ->
        t1 = t2.

(*
How could I state the real desired property of a subtype reln, which
is that if t1 <: t2, we can put a value of t1 in for wherever t2 is,
and the program won't get stuck?
*)

(*
Also want to show that common type gives the "least supertype"
So what is least subtype? i8, u8, what is the least supertype? the subtype with the fewest bits?
What happens if the type doesn't have a static size? Maybe we just assume it's the bits for now
*)

Definition fact_common_type_always_smallest_bits_supertype : Prop :=
    forall t1 t2 t3,
        common_type t1 t2 = Some t3 ->
        ~ exists t4, (
            is_subtype t1 t4 = true /\
            is_subtype t2 t4 = true
        ) /\ type_bits t4 <? type_bits t3 = true.

Definition fact_common_type_always_supertype : Prop :=
    forall t1 t2 t3,
        common_type t1 t2 = Some t3 ->
        is_subtype t1 t3 = true /\
        is_subtype t2 t3 = true.

Definition fact_no_common_type_means_no_supertype : Prop :=
    forall t1 t2,
        common_type t1 t2 = None ->
        ~ exists t3, is_subtype t1 t3 = true /\ is_subtype t2 t3 = true.

(* TODO is symmetric the right word for this? *)
Definition fact_common_type_symmetric : Prop :=
    forall t1 t2,
        common_type t1 t2 = common_type t2 t1.

(** [is_subtype] is reflexive: every type is a subtype of itself.

    For [T_Int], both range bounds are compared against themselves; for
    [T_Float], the bit width is compared against itself; for [T_Bool], the
    result is [true] by definition. *)
Theorem is_subtype_is_reflexive : fact_is_subtype_is_reflexive.
Proof.
  unfold fact_is_subtype_is_reflexive.
  intros [s w | w | ]; unfold is_subtype.
  - (* T_Int s w *)
    rewrite Z.geb_leb, !Z.leb_refl.
    reflexivity.
  - (* T_Float w *)
    apply Z.leb_refl.
  - (* T_Bool *)
    reflexivity.
Qed. *)
