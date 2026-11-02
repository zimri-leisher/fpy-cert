(** Facts about the definitions in [Typing].

    [Typing] states the properties it wants of [is_subtype] and
    [common_type] as named [Prop]s (e.g. [fact_is_subtype_is_reflexive]);
    this file proves them. *)

From FpyCert Require Import Typing.
From Stdlib Require Import ZArith.

Open Scope Z_scope.

(** [is_subtype] is reflexive: every type is a subtype of itself.

    For [TInt], both range bounds are compared against themselves; for
    [TFloat], the bit width is compared against itself; for [TBool], the
    result is [true] by definition. *)
Theorem is_subtype_is_reflexive : fact_is_subtype_is_reflexive.
Proof.
  unfold fact_is_subtype_is_reflexive.
  intros [s w | w | ]; unfold is_subtype.
  - (* TInt s w *)
    rewrite Z.geb_leb, !Z.leb_refl.
    reflexivity.
  - (* TFloat w *)
    apply Z.leb_refl.
  - (* TBool *)
    reflexivity.
Qed.
