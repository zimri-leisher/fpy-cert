(** Bits of 64-bit words, for the bit-packed sieves of attempt 8.

    [bitsum v k] counts the set bits of [v] among positions [0 .. k-1]; [popc] in the program
    computes [bitsum v 64] by clearing the lowest set bit until the word is zero ([bitsum_clear_low]),
    and [ctz] computes the index of the lowest set bit as the popcount of [(v xor (v - 1)) >> 1]
    ([xor_pred_shift]). Words loaded from memory are [bytes8] of their bytes ([testbit_bytes8]). *)

From Stdlib Require Import ZArith Lia Bool.
Open Scope Z_scope.

(** * Counting set bits *)

Fixpoint bitsum (v : Z) (k : nat) : Z :=
  match k with O => 0 | S k' => bitsum v k' + (if Z.testbit v (Z.of_nat k') then 1 else 0) end.

Lemma bitsum_ext : forall v w k, (forall i, 0 <= i < Z.of_nat k -> Z.testbit v i = Z.testbit w i) -> bitsum v k = bitsum w k.
Proof.
  intros v w k. induction k as [| k IH]; intros H; [reflexivity |]. cbn [bitsum].
  rewrite IH by (intros i Hi; apply H; lia). rewrite (H (Z.of_nat k)) by lia. reflexivity.
Qed.

Lemma bitsum_bounds : forall v k, 0 <= bitsum v k <= Z.of_nat k.
Proof. intros v k. induction k as [| k IH]; cbn [bitsum]; [lia |]. destruct (Z.testbit v (Z.of_nat k)); lia. Qed.

Lemma bitsum_0 : forall k, bitsum 0 k = 0.
Proof. intros k. induction k as [| k IH]; cbn [bitsum]; [reflexivity |]. rewrite Z.testbit_0_l, IH. reflexivity. Qed.

(** Clearing one set bit removes one from the count. *)
Lemma bitsum_clear_one : forall v w k t, 0 <= t < Z.of_nat k -> Z.testbit v t = true -> Z.testbit w t = false ->
  (forall i, 0 <= i < Z.of_nat k -> i <> t -> Z.testbit w i = Z.testbit v i) -> bitsum w k = bitsum v k - 1.
Proof.
  intros v w k. induction k as [| k IH]; intros t Ht Hv Hw Hrest; [lia |]. cbn [bitsum].
  destruct (Z.eq_dec t (Z.of_nat k)) as [-> | Hne].
  - rewrite Hv, Hw. rewrite (bitsum_ext w v k) by (intros i Hi; apply Hrest; lia). lia.
  - rewrite (IH t) by (first [lia | assumption | (intros i Hi Hit; apply Hrest; lia)]).
    rewrite (Hrest (Z.of_nat k)) by lia. lia.
Qed.

(** The low [t] ones. *)
Lemma bitsum_ones_min : forall t k, 0 <= t -> bitsum (Z.ones t) k = Z.min t (Z.of_nat k).
Proof.
  intros t k Ht. induction k as [| k IH]; cbn [bitsum]; [lia |].
  rewrite IH, Z.testbit_ones by lia.
  replace (0 <=? Z.of_nat k) with true by (symmetry; apply Z.leb_le; lia).
  destruct (Z.ltb_spec (Z.of_nat k) t); cbn; lia.
Qed.

Lemma bitsum_ones : forall t k, 0 <= t <= Z.of_nat k -> bitsum (Z.ones t) k = t.
Proof. intros t k Ht. rewrite bitsum_ones_min by lia. lia. Qed.

(** * The lowest set bit *)

(** [low_bit x t]: bit [t] of [x] is the lowest set bit. *)
Definition low_bit (x t : Z) : Prop := 0 <= t /\ Z.testbit x t = true /\ (forall i, 0 <= i < t -> Z.testbit x i = false).

Lemma low_bit_exists : forall x, 0 < x -> exists t, low_bit x t.
Proof.
  intros x Hx. remember (Z.to_nat x) as k eqn:Hk. revert x Hx Hk.
  induction k as [k IH] using (well_founded_induction lt_wf). intros x Hx Hk.
  destruct (Z.even x) eqn:Hev.
  - (* x = 2 y *)
    pose proof (Z.even_spec x) as [He _]. specialize (He Hev). destruct He as [y Hy].
    destruct (IH (Z.to_nat y) ltac:(lia) y ltac:(lia) eq_refl) as [t [Ht0 [Ht Hlow]]].
    exists (t + 1). split; [lia | split].
    + replace (t + 1) with (Z.succ t) by lia. rewrite Hy, Z.testbit_even_succ by lia. exact Ht.
    + intros i Hi. rewrite Hy. destruct (Z.eq_dec i 0) as [-> | Hne].
      * apply Z.testbit_even_0.
      * replace i with (Z.succ (i - 1)) by lia. rewrite Z.testbit_even_succ by lia. apply Hlow. lia.
  - exists 0. split; [lia | split; [| intros i Hi; lia]].
    rewrite Z.bit0_odd. rewrite <- Z.negb_even, Hev. reflexivity.
Qed.

Lemma low_bit_unique : forall x t t', low_bit x t -> low_bit x t' -> t = t'.
Proof.
  intros x t t' [H0 [H1 H2]] [H0' [H1' H2']].
  destruct (Z.lt_trichotomy t t') as [Hlt | [Heq | Hgt]]; [| exact Heq |].
  - rewrite (H2' t) in H1 by lia. discriminate.
  - rewrite (H2 t') in H1' by lia. discriminate.
Qed.

(** The bits of [x - 1]: ones below the lowest set bit [t], zero at [t], those of [x] above. *)
Lemma testbit_pred : forall x t, 0 < x -> low_bit x t -> forall i, 0 <= i ->
  Z.testbit (x - 1) i = if i <? t then true else if i =? t then false else Z.testbit x i.
Proof.
  intros x t Hx Hlow. destruct Hlow as [Ht0 Hlow]. revert x Hx Hlow.
  pattern t. apply natlike_ind; [| | exact Ht0]; clear t Ht0.
  - (* t = 0: x odd *)
    intros x Hx [Hb _] i Hi.
    assert (Hodd : x = 2 * (x / 2) + 1).
    { rewrite Z.bit0_odd in Hb. apply Z.odd_spec in Hb. destruct Hb as [m Hm]. rewrite Hm.
      replace ((2 * m + 1) / 2) with m by (apply Z.div_unique_pos with 1; lia). reflexivity. }
    destruct (Z.eq_dec i 0) as [-> | Hne].
    + cbn. replace (x - 1) with (2 * (x / 2)) by lia. apply Z.testbit_even_0.
    + replace (0 <=? i) with true by (symmetry; apply Z.leb_le; lia).
      replace (i <? 0) with false by (symmetry; apply Z.ltb_ge; lia).
      replace (i =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
      replace (x - 1) with (2 * (x / 2)) by lia. rewrite Hodd at 2.
      replace i with (Z.succ (i - 1)) by lia. rewrite Z.testbit_even_succ, Z.testbit_odd_succ by lia. reflexivity.
  - (* t + 1: x = 2 y with the lowest bit of y at t *)
    intros t Ht IH x Hx [Hb Hlowx] i Hi.
    assert (Hev : x = 2 * (x / 2)).
    { pose proof (Hlowx 0 ltac:(lia)) as H0. rewrite Z.bit0_odd in H0.
      rewrite <- Z.negb_even in H0. apply negb_false_iff in H0. apply Z.even_spec in H0. destruct H0 as [m Hm].
      rewrite Hm. replace (2 * m / 2) with m by (apply Z.div_unique_pos with 0; lia). reflexivity. }
    set (y := x / 2) in *.
    assert (Hy : 0 < y) by lia.
    assert (Hby : Z.testbit y t = true) by (rewrite Hev in Hb; rewrite Z.testbit_even_succ in Hb by lia; exact Hb).
    assert (Hlowy : forall j, 0 <= j < t -> Z.testbit y j = false).
    { intros j Hj. pose proof (Hlowx (Z.succ j) ltac:(lia)) as Hj'. rewrite Hev in Hj'. rewrite Z.testbit_even_succ in Hj' by lia. exact Hj'. }
    replace (x - 1) with (2 * (y - 1) + 1) by lia.
    destruct (Z.eq_dec i 0) as [-> | Hne].
    + rewrite Z.testbit_odd_0. replace (0 <? Z.succ t) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
    + replace i with (Z.succ (i - 1)) at 1 by lia. rewrite Z.testbit_odd_succ by lia.
      rewrite (IH y Hy (conj Hby Hlowy) (i - 1)) by lia.
      assert (E : Z.testbit x i = Z.testbit y (i - 1)).
      { rewrite Hev. replace i with (Z.succ (i - 1)) at 1 by lia. rewrite Z.testbit_even_succ by lia. reflexivity. }
      rewrite E.
      replace (i - 1 <? t) with (i <? Z.succ t) by (apply Bool.eq_iff_eq_true; rewrite !Z.ltb_lt; lia).
      replace (i - 1 =? t) with (i =? Z.succ t) by (apply Bool.eq_iff_eq_true; rewrite !Z.eqb_eq; lia).
      reflexivity.
Qed.

(** [x land (x - 1)] clears the lowest set bit. *)
Lemma testbit_land_pred : forall x t, 0 < x -> low_bit x t -> forall i, 0 <= i ->
  Z.testbit (Z.land x (x - 1)) i = Z.testbit x i && negb (i =? t).
Proof.
  intros x t Hx Hlow i Hi. rewrite Z.land_spec, (testbit_pred x t Hx Hlow i Hi).
  destruct Hlow as [Ht0 [Hb Hl]].
  destruct (Z.ltb_spec i t) as [Hlt | Hge].
  - rewrite (Hl i) by lia. reflexivity.
  - destruct (Z.eqb_spec i t) as [-> | Hne]; [rewrite Hb; reflexivity |]. destruct (Z.testbit x i); reflexivity.
Qed.

(** [(x xor (x - 1)) >> 1] is [2^t - 1]. *)
Lemma xor_pred_shift : forall x t, 0 < x -> low_bit x t -> Z.shiftr (Z.lxor x (x - 1)) 1 = Z.ones t.
Proof.
  intros x t Hx Hlow. apply Z.bits_inj'. intros i Hi.
  rewrite Z.shiftr_spec, Z.lxor_spec, (testbit_pred x t Hx Hlow (i + 1)) by lia.
  destruct Hlow as [Ht0 [Hb Hl]]. rewrite Z.testbit_ones by lia.
  replace (0 <=? i) with true by (symmetry; apply Z.leb_le; lia).
  destruct (Z.ltb_spec (i + 1) t) as [Hlt | Hge].
  - rewrite (Hl (i + 1)) by lia. replace (i <? t) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
  - destruct (Z.eqb_spec (i + 1) t) as [Heq | Hne].
    + subst t. rewrite Hb. replace (i <? i + 1) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
    + replace (i <? t) with false by (symmetry; apply Z.ltb_ge; lia). destruct (Z.testbit x (i + 1)); reflexivity.
Qed.

(** The lowest set bit of a word is below 64. *)
Lemma low_bit_lt64 : forall x t, 0 <= x < 2 ^ 64 -> low_bit x t -> t < 64.
Proof.
  intros x t Hx [Ht0 [Hb _]]. destruct (Z_lt_le_dec t 64) as [H | H]; [exact H |].
  rewrite Z.bits_above_log2 in Hb; [discriminate | lia |].
  assert (Z.log2 x < 64) by (destruct (Z.eq_dec x 0) as [-> | Hne]; [cbn; lia | apply Z.log2_lt_pow2; lia]). lia.
Qed.

(** Clearing the lowest bit of a nonzero word. *)
Lemma bitsum_clear_low : forall x, 0 < x < 2 ^ 64 -> bitsum (Z.land x (x - 1)) 64 = bitsum x 64 - 1.
Proof.
  intros x Hx. destruct (low_bit_exists x ltac:(lia)) as [t Hlow].
  pose proof (low_bit_lt64 x t ltac:(lia) Hlow) as Ht64.
  apply (bitsum_clear_one x (Z.land x (x - 1)) 64 t).
  - destruct Hlow; lia.
  - destruct Hlow as [_ [Hb _]]. exact Hb.
  - rewrite (testbit_land_pred x t) by (first [lia | exact Hlow | (destruct Hlow; lia)]). rewrite Z.eqb_refl, andb_false_r. reflexivity.
  - intros i Hi Hne. rewrite (testbit_land_pred x t) by (first [lia | exact Hlow]).
    replace (i =? t) with false by (symmetry; apply Z.eqb_neq; exact Hne). apply andb_true_r.
Qed.

(** The index of the lowest set bit, as the program computes it. *)
Lemma ctz_spec : forall x t, 0 < x < 2 ^ 64 -> low_bit x t -> bitsum (Z.shiftr (Z.lxor x (x - 1)) 1) 64 = t.
Proof.
  intros x t Hx Hlow. rewrite (xor_pred_shift x t) by (first [lia | exact Hlow]).
  apply bitsum_ones. pose proof (low_bit_lt64 x t ltac:(lia) Hlow). destruct Hlow. lia.
Qed.

(** * Words made of bytes *)

Definition bytes8 (z0 z1 z2 z3 z4 z5 z6 z7 : Z) : Z :=
  z0 + 256 * (z1 + 256 * (z2 + 256 * (z3 + 256 * (z4 + 256 * (z5 + 256 * (z6 + 256 * z7)))))).

Lemma testbit_byte_cons : forall b r i, 0 <= b < 256 -> 0 <= r -> 0 <= i ->
  Z.testbit (b + 256 * r) i = if i <? 8 then Z.testbit b i else Z.testbit r (i - 8).
Proof.
  intros b r i Hb Hr Hi. destruct (Z.ltb_spec i 8) as [Hlt | Hge].
  - rewrite <- (Z.mod_pow2_bits_low (b + 256 * r) 8 i) by lia.
    replace ((b + 256 * r) mod 2 ^ 8) with b; [reflexivity |].
    apply (Z.mod_unique_pos (b + 256 * r) (2 ^ 8) r b); change (2 ^ 8) with 256; lia.
  - replace i with (i - 8 + 8) at 1 by lia. rewrite <- (Z.div_pow2_bits (b + 256 * r) 8 (i - 8)) by lia.
    replace ((b + 256 * r) / 2 ^ 8) with r; [reflexivity |].
    apply (Z.div_unique_pos (b + 256 * r) (2 ^ 8) r b); change (2 ^ 8) with 256; lia.
Qed.

(** Bit [8 j + k] of a word is bit [k] of its byte [j]. *)
Lemma testbit_bytes8 : forall z0 z1 z2 z3 z4 z5 z6 z7 i,
  0 <= z0 < 256 -> 0 <= z1 < 256 -> 0 <= z2 < 256 -> 0 <= z3 < 256 -> 0 <= z4 < 256 -> 0 <= z5 < 256 -> 0 <= z6 < 256 -> 0 <= z7 < 256 ->
  0 <= i < 64 ->
  Z.testbit (bytes8 z0 z1 z2 z3 z4 z5 z6 z7) i =
  Z.testbit (match i / 8 with 0 => z0 | 1 => z1 | 2 => z2 | 3 => z3 | 4 => z4 | 5 => z5 | 6 => z6 | _ => z7 end) (i mod 8).
Proof.
  intros. unfold bytes8.
  assert (B6 : 0 <= z6 + 256 * z7) by lia. assert (B5 : 0 <= z5 + 256 * (z6 + 256 * z7)) by lia.
  assert (B4 : 0 <= z4 + 256 * (z5 + 256 * (z6 + 256 * z7))) by lia.
  assert (B3 : 0 <= z3 + 256 * (z4 + 256 * (z5 + 256 * (z6 + 256 * z7)))) by lia.
  assert (B2 : 0 <= z2 + 256 * (z3 + 256 * (z4 + 256 * (z5 + 256 * (z6 + 256 * z7))))) by lia.
  assert (B1 : 0 <= z1 + 256 * (z2 + 256 * (z3 + 256 * (z4 + 256 * (z5 + 256 * (z6 + 256 * z7)))))) by lia.
  assert (Hj : i / 8 = 0 \/ i / 8 = 1 \/ i / 8 = 2 \/ i / 8 = 3 \/ i / 8 = 4 \/ i / 8 = 5 \/ i / 8 = 6 \/ i / 8 = 7)
    by (pose proof (Z.div_pos i 8); pose proof (Z.div_lt_upper_bound i 8 8); lia).
  pose proof (Z.div_mod i 8 ltac:(lia)) as Hdm. pose proof (Z.mod_pos_bound i 8 ltac:(lia)) as Hmb.
  destruct Hj as [E | [E | [E | [E | [E | [E | [E | E]]]]]]]; rewrite E;
  repeat (rewrite testbit_byte_cons by lia;
          match goal with |- context [if ?c then _ else _] => destruct c eqn:?Ec end;
          [ first [ f_equal; lia | (apply Z.ltb_lt in Ec; lia) ] | apply Z.ltb_ge in Ec ]);
  try (f_equal; lia).
Qed.

(** * Bounds of bitwise results *)

Lemma lt_pow2_bits : forall v k, 0 <= v -> 0 <= k -> (forall i, k <= i -> Z.testbit v i = false) -> v < 2 ^ k.
Proof.
  intros v k Hv Hk H. destruct (Z.eq_dec v 0) as [-> | Hne]; [apply Z.pow_pos_nonneg; lia |].
  pose proof (Z.bit_log2 v ltac:(lia)) as Hb.
  destruct (Z_lt_le_dec (Z.log2 v) k) as [Hlt | Hge]; [apply Z.log2_lt_pow2; lia |].
  rewrite (H (Z.log2 v) Hge) in Hb. discriminate.
Qed.

Lemma testbit_high_false : forall v k i, 0 <= v < 2 ^ k -> k <= i -> Z.testbit v i = false.
Proof.
  intros v k i Hv Hi. destruct (Z.eq_dec v 0) as [-> | Hne]; [apply Z.testbit_0_l |].
  apply Z.bits_above_log2; [lia |]. apply Z.lt_le_trans with k; [| exact Hi].
  apply Z.log2_lt_pow2; lia.
Qed.

Lemma land_bound : forall a b k, 0 <= a < 2 ^ k -> 0 <= b -> 0 <= Z.land a b < 2 ^ k.
Proof.
  intros a b k Ha Hb. assert (0 <= k) by (destruct (Z_lt_le_dec k 0) as [H | H]; [rewrite Z.pow_neg_r in Ha by exact H; lia | exact H]).
  split; [apply Z.land_nonneg; lia |]. apply lt_pow2_bits; [apply Z.land_nonneg; lia | lia |].
  intros i Hi. rewrite Z.land_spec, (testbit_high_false a k i) by lia. reflexivity.
Qed.

Lemma lor_bound : forall a b k, 0 <= a < 2 ^ k -> 0 <= b < 2 ^ k -> 0 <= Z.lor a b < 2 ^ k.
Proof.
  intros a b k Ha Hb. assert (0 <= k) by (destruct (Z_lt_le_dec k 0) as [H | H]; [rewrite Z.pow_neg_r in Ha by exact H; lia | exact H]).
  split; [apply Z.lor_nonneg; lia |]. apply lt_pow2_bits; [apply Z.lor_nonneg; lia | lia |].
  intros i Hi. rewrite Z.lor_spec, (testbit_high_false a k i), (testbit_high_false b k i) by lia. reflexivity.
Qed.

Lemma lxor_bound : forall a b k, 0 <= a < 2 ^ k -> 0 <= b < 2 ^ k -> 0 <= Z.lxor a b < 2 ^ k.
Proof.
  intros a b k Ha Hb. assert (0 <= k) by (destruct (Z_lt_le_dec k 0) as [H | H]; [rewrite Z.pow_neg_r in Ha by exact H; lia | exact H]).
  split; [apply Z.lxor_nonneg; lia |]. apply lt_pow2_bits; [apply Z.lxor_nonneg; lia | lia |].
  intros i Hi. rewrite Z.lxor_spec, (testbit_high_false a k i), (testbit_high_false b k i) by lia. reflexivity.
Qed.

Lemma land_le_l : forall a b, 0 <= a -> 0 <= b -> Z.land a b <= a.
Proof.
  intros a b Ha Hb. assert (E : a = Z.land a b + Z.ldiff a b).
  { rewrite Z.add_nocarry_lxor.
    - apply Z.bits_inj'. intros i Hi. rewrite Z.lxor_spec, Z.land_spec, Z.ldiff_spec.
      destruct (Z.testbit a i), (Z.testbit b i); reflexivity.
    - apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.land_spec, Z.ldiff_spec, Z.testbit_0_l.
      destruct (Z.testbit a i), (Z.testbit b i); reflexivity. }
  assert (0 <= Z.ldiff a b) by (apply Z.ldiff_nonneg; lia). lia.
Qed.
