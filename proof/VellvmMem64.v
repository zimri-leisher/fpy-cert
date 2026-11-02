(** 64-bit loads and stores on the byte arrays of [VellvmMem].

    Vellvm's memory stores an [i64] as eight concrete little-endian bytes
    ([BYTE_I], the same representation as eight [i8] stores) and reads eight
    bytes back as their little-endian combination, so a program may fill
    eight cells with one [store i64] and read eight flags with one
    [load i64]. This file provides the handler lemmas ([mem_store64],
    [mem_load64]), the [runX]-level instruction lemmas, the arithmetic of the
    byte decomposition ([byte_k], [bytes8]) and the tactic clauses. *)

From Stdlib Require Import ZArith NArith String List Lia Bool.
From ExtLib Require Import Structures.Maps Structures.Monads.
From ITree Require Import ITree ITreeFacts.
From Vellvm Require Import Syntax Utils Params Semantics Interfaces.Memory ParamsV IPtrInfinite.
From Vellvm Require Import Implementations.Memory Semantics.Libraries.
From FpyCert Require Import LLVMBuilder VellvmRun VellvmMem.
Import ListNotations ITreeNotations.
Open Scope string_scope. Open Scope itree_scope. Open Scope Z_scope.
Unset Implicit Arguments.

Notation "t1 ≈ t2" := (eutt eq t1 t2) (at level 70, only parsing).

#[local] Instance Pa : Params := @ParamsV IPZ IPZTheory.

Opaque Integers.repr Integers.unsigned Integers.signed Integers.mul Integers.add Integers.eq Integers.ltu
  Integers.zero Integers.one.

(** * The bytes of a 64-bit value *)

(** The [k]-th byte (little-endian). *)
Definition byte_k (v k : Z) : Z := (v / 2 ^ (8 * k)) mod 256.

Lemma byte_k_bounds : forall v k, 0 <= byte_k v k < 256.
Proof. intros. unfold byte_k. apply Z.mod_pos_bound. lia. Qed.

(** How the serializer extracts byte [idx]. *)
Lemma extract_byte_repr64 : forall v (idx : N), 0 <= v < two64 -> (idx < 8)%N ->
  extract_byte_vint (@Integers.repr 64 v) idx = byte_k v (Z.of_N idx).
Proof.
  intros * Hv Hidx. unfold two64 in Hv. unfold extract_byte_vint, byte_k. cbn [VellvmIntegers.unsigned VellvmIntegers.modu VellvmIntegers.shru VellvmIntegers.repr VellvmIntegers.VInt_Bounded]. unfold Integers.modu, Integers.shru.
  assert (Hp : 0 < 2 ^ (8 * Z.of_N idx)) by (apply Z.pow_pos_nonneg; lia).
  assert (Hq : 0 <= v / 2 ^ (8 * Z.of_N idx) <= v).
  { split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; [lia | nia]]. }
  pose proof (Z.mod_pos_bound (v / 2 ^ (8 * Z.of_N idx)) 256 ltac:(lia)) as Hm.
  rewrite (unsigned_repr64 v) by (unfold two64; lia).
  rewrite (unsigned_repr64 (Z.of_N idx * 8)) by (unfold two64; lia).
  rewrite Z.shiftr_div_pow2 by lia. replace (Z.of_N idx * 8) with (8 * Z.of_N idx) by lia.
  rewrite (unsigned_repr64 (v / 2 ^ (8 * Z.of_N idx))) by (unfold two64; lia).
  rewrite (unsigned_repr64 256) by (unfold two64; lia).
  rewrite unsigned_repr64 by (unfold two64; lia).
  reflexivity.
Qed.
Opaque Integers.modu Integers.shru Integers.sub Integers.divu.

(** The serialization of [DVALUE_I 64 (repr v)]. *)
Lemma bytes_of_i64 : forall v, 0 <= v < two64 ->
  dvalue_to_memory_bytes (DTYPE_I 64) (DVALUE_Base (DVALUE_I 64 (Integers.repr v))) None
  = raise_ret [BYTE_I (Integers.repr (byte_k v 0)); BYTE_I (Integers.repr (byte_k v 1));
               BYTE_I (Integers.repr (byte_k v 2)); BYTE_I (Integers.repr (byte_k v 3));
               BYTE_I (Integers.repr (byte_k v 4)); BYTE_I (Integers.repr (byte_k v 5));
               BYTE_I (Integers.repr (byte_k v 6)); BYTE_I (Integers.repr (byte_k v 7))].
Proof.
  intros. unfold dvalue_to_memory_bytes. cbn -[extract_byte_vint].
  rewrite !extract_byte_repr64 by lia. reflexivity.
Qed.

(** [bytes8] (from [VellvmRun]) undoes the decomposition. *)
Lemma div_step256 : forall v e e', 0 <= v -> 0 <= e -> e' = e + 8 ->
  v / 2 ^ e = (v / 2 ^ e) mod 256 + 256 * (v / 2 ^ e').
Proof.
  intros * Hv He ->. rewrite Z.pow_add_r by lia. rewrite <- Z.div_div by (try apply Z.pow_pos_nonneg; lia).
  rewrite (Z.div_mod (v / 2 ^ e) 256) at 1 by lia. replace (2 ^ 8) with 256 by reflexivity. lia.
Qed.

Lemma bytes8_byte_k : forall v, 0 <= v < two64 ->
  bytes8 (byte_k v 0) (byte_k v 1) (byte_k v 2) (byte_k v 3) (byte_k v 4) (byte_k v 5) (byte_k v 6) (byte_k v 7) = v.
Proof.
  intros v Hv. unfold two64 in Hv. unfold bytes8, byte_k.
  replace (8 * 0) with 0 by lia. replace (8 * 1) with 8 by lia. replace (8 * 2) with 16 by lia.
  replace (8 * 3) with 24 by lia. replace (8 * 4) with 32 by lia. replace (8 * 5) with 40 by lia.
  replace (8 * 6) with 48 by lia. replace (8 * 7) with 56 by lia.
  rewrite Z.pow_0_r, Z.div_1_r.
  pose proof (div_step256 v 0 8 ltac:(lia) ltac:(lia) ltac:(reflexivity)) as E0. rewrite Z.pow_0_r, Z.div_1_r in E0.
  pose proof (div_step256 v 8 16 ltac:(lia) ltac:(lia) ltac:(reflexivity)) as E1.
  pose proof (div_step256 v 16 24 ltac:(lia) ltac:(lia) ltac:(reflexivity)) as E2.
  pose proof (div_step256 v 24 32 ltac:(lia) ltac:(lia) ltac:(reflexivity)) as E3.
  pose proof (div_step256 v 32 40 ltac:(lia) ltac:(lia) ltac:(reflexivity)) as E4.
  pose proof (div_step256 v 40 48 ltac:(lia) ltac:(lia) ltac:(reflexivity)) as E5.
  pose proof (div_step256 v 48 56 ltac:(lia) ltac:(lia) ltac:(reflexivity)) as E6.
  pose proof (div_step256 v 56 64 ltac:(lia) ltac:(lia) ltac:(reflexivity)) as E7.
  assert (E8 : v / 2 ^ 64 = 0) by (apply Z.div_small; lia).
  lia.
Qed.

(** Counting eight 0/1 flags packed in one value: [(w * 0x0101010101010101) >> 56]. *)
Lemma bytesum8 : forall z0 z1 z2 z3 z4 z5 z6 z7,
  0 <= z0 <= 1 -> 0 <= z1 <= 1 -> 0 <= z2 <= 1 -> 0 <= z3 <= 1 -> 0 <= z4 <= 1 -> 0 <= z5 <= 1 -> 0 <= z6 <= 1 -> 0 <= z7 <= 1 ->
  Integers.shru (@Integers.repr 64 (bytes8 z0 z1 z2 z3 z4 z5 z6 z7 * 72340172838076673)) (Integers.repr 56)
  = Integers.repr (z0 + z1 + z2 + z3 + z4 + z5 + z6 + z7).
Proof.
  intros. rewrite shru_repr64 by lia. f_equal.
  repeat match goal with H : 0 <= ?z <= 1 |- _ => let E := fresh in assert (E : z = 0 \/ z = 1) by lia; clear H; destruct E as [-> | ->] end;
  vm_compute; reflexivity.
Qed.

(** * The handler *)

(** The memory after storing the bytes of [v] at [a .. a + 7] (in the order
    the handler writes them). *)
Definition store64_mem (a : Z) (q : N) (v : Z) (mem : memory) : memory :=
  IM.add (a + 7) (BYTE_I (Integers.repr (byte_k v 7)), Some q)
  (IM.add (a + 6) (BYTE_I (Integers.repr (byte_k v 6)), Some q)
  (IM.add (a + 5) (BYTE_I (Integers.repr (byte_k v 5)), Some q)
  (IM.add (a + 4) (BYTE_I (Integers.repr (byte_k v 4)), Some q)
  (IM.add (a + 3) (BYTE_I (Integers.repr (byte_k v 3)), Some q)
  (IM.add (a + 2) (BYTE_I (Integers.repr (byte_k v 2)), Some q)
  (IM.add (a + 1) (BYTE_I (Integers.repr (byte_k v 1)), Some q)
  (IM.add (a + 0) (BYTE_I (Integers.repr (byte_k v 0)), Some q) mem))))))).

Ltac store_round H :=
  unfold set_byte_raw_mem;
  repeat (rewrite IntMaps.IP.F.add_neq_o by lia);
  first [rewrite H | (change (@IM.find byte) with (@IM.find (memory_byte * option N)); rewrite H)];
  cbn -[extract_byte_vint IM.find IM.add]; rewrite N.eqb_refl; cbn -[extract_byte_vint IM.find IM.add].

Lemma mem_store64 : forall mem fs heap p (a : Z) (q : N) v b0 b1 b2 b3 b4 b5 b6 b7,
  0 <= v < two64 ->
  IM.find (a + 0) mem = Some (b0, Some q) -> IM.find (a + 1) mem = Some (b1, Some q) ->
  IM.find (a + 2) mem = Some (b2, Some q) -> IM.find (a + 3) mem = Some (b3, Some q) ->
  IM.find (a + 4) mem = Some (b4, Some q) -> IM.find (a + 5) mem = Some (b5, Some q) ->
  IM.find (a + 6) mem = Some (b6, Some q) -> IM.find (a + 7) mem = Some (b7, Some q) ->
  (handle_memory memM_interp (Store (DTYPE_I 64) (DVALUE_Base (DVALUE_Pointer (a, Some [q]))) (DVALUE_Base (DVALUE_I 64 (Integers.repr v))))
     (mkState (mkMemoryStack mem fs heap) p) : itree MCFGEbot _)
    ≈ Ret (mkState (mkMemoryStack (store64_mem a q v mem) fs heap) p, tt).
Proof.
  intros * Hv H0 H1 H2 H3 H4 H5 H6 H7.
  unfold handle_memory. cbn -[extract_byte_vint IM.find IM.add]. unfold read_byte_raw_mem.
  store_round H0. store_round H1. store_round H2. store_round H3.
  store_round H4. store_round H5. store_round H6. store_round H7.
  unfold set_byte_raw_mem. rewrite !extract_byte_repr64 by lia. unfold store64_mem. reflexivity.
Qed.

(** Deserializing eight bytes as an [i64]. *)
Lemma bytes_to_i64 : forall z0 z1 z2 z3 z4 z5 z6 z7,
  0 <= z0 < 256 -> 0 <= z1 < 256 -> 0 <= z2 < 256 -> 0 <= z3 < 256 ->
  0 <= z4 < 256 -> 0 <= z5 < 256 -> 0 <= z6 < 256 -> 0 <= z7 < 256 ->
  memory_bytes_to_dvalue
    [BYTE_I (@Integers.repr 8 z0); BYTE_I (Integers.repr z1); BYTE_I (Integers.repr z2); BYTE_I (Integers.repr z3);
     BYTE_I (Integers.repr z4); BYTE_I (Integers.repr z5); BYTE_I (Integers.repr z6); BYTE_I (Integers.repr z7)] (DTYPE_I 64)
  = raise_ret (DVALUE_Base (DVALUE_I 64 (Integers.repr (bytes8 z0 z1 z2 z3 z4 z5 z6 z7)))).
Proof.
  intros. cbn -[Z.shiftl]. rewrite !unsigned_repr8 by lia. rewrite !Z.shiftl_mul_pow2 by lia.
  change (2 ^ 8) with 256. unfold bytes8. do 4 f_equal. lia.
Qed.

Section Load64Sec.
  Variables (mem : memory) (fs : Framestack) (heap : Heap) (p : provenance) (a : Z) (q : N) (z0 z1 z2 z3 z4 z5 z6 z7 : Z).
  Hypotheses (H0 : IM.find (a + 0) mem = Some (BYTE_I (Integers.repr z0), Some q))
             (H1 : IM.find (a + 1) mem = Some (BYTE_I (Integers.repr z1), Some q))
             (H2 : IM.find (a + 2) mem = Some (BYTE_I (Integers.repr z2), Some q))
             (H3 : IM.find (a + 3) mem = Some (BYTE_I (Integers.repr z3), Some q))
             (H4 : IM.find (a + 4) mem = Some (BYTE_I (Integers.repr z4), Some q))
             (H5 : IM.find (a + 5) mem = Some (BYTE_I (Integers.repr z5), Some q))
             (H6 : IM.find (a + 6) mem = Some (BYTE_I (Integers.repr z6), Some q))
             (H7 : IM.find (a + 7) mem = Some (BYTE_I (Integers.repr z7), Some q)).
  Hypotheses (B0 : 0 <= z0 < 256) (B1 : 0 <= z1 < 256) (B2 : 0 <= z2 < 256) (B3 : 0 <= z3 < 256)
             (B4 : 0 <= z4 < 256) (B5 : 0 <= z5 < 256) (B6 : 0 <= z6 < 256) (B7 : 0 <= z7 < 256).

  Ltac load_round H :=
    first [rewrite H | (change (@IM.find byte) with (@IM.find (memory_byte * option N)); rewrite H)];
    cbn -[memory_bytes_to_dvalue IM.find IM.add]; rewrite N.eqb_refl; cbn -[memory_bytes_to_dvalue IM.find IM.add].

  Lemma mem_load64 :
    (handle_memory memM_interp (Load (DTYPE_I 64) (DVALUE_Base (DVALUE_Pointer (a, Some [q])))) (mkState (mkMemoryStack mem fs heap) p)
       : itree MCFGEbot _)
      ≈ Ret (mkState (mkMemoryStack mem fs heap) p, DVALUE_Base (DVALUE_I 64 (Integers.repr (bytes8 z0 z1 z2 z3 z4 z5 z6 z7)))).
  Proof.
    unfold handle_memory, handle_memoryM, read_dvalue, read_bytes.
    change (store_size_dtyp (DTYPE_I 64)) with 8%N. change (@read_byte _ _) with (@Read_byte Pa).
    cbn -[memory_bytes_to_dvalue IM.find IM.add]. unfold read_byte_raw_mem.
    load_round H0. load_round H1. load_round H2. load_round H3. load_round H4. load_round H5. load_round H6. load_round H7.
    rewrite bytes_to_i64 by assumption. cbn. reflexivity.
  Qed.
End Load64Sec.

(** * Arrays of 64-bit values *)

(** [arr64 mem addr q lo hi f]: elements [lo, hi) of the [i64] array at
    [addr] hold the values [f lo], ..., [f (hi - 1)] (each below 2^64),
    element [i] occupying the bytes [addr + 8 i + k]. *)
Definition arr64 (mem : memory) (addr : Z) (q : N) (lo hi : Z) (f : Z -> Z) : Prop :=
  forall i, lo <= i < hi ->
    (0 <= f i < two64) /\
    (forall k, 0 <= k < 8 -> IM.find (addr + 8 * i + k) mem = Some (BYTE_I (Integers.repr (byte_k (f i) k)), Some q)).

(** Updating element [i] of an array function. *)
Definition upd64 (f : Z -> Z) (i v : Z) : Z -> Z := fun j => if j =? i then v else f j.

Lemma arr64_cell : forall mem addr q lo hi f, arr64 mem addr q lo hi f ->
  forall i k, lo <= i < hi -> 0 <= k < 8 -> IM.find (addr + 8 * i + k) mem = Some (BYTE_I (Integers.repr (byte_k (f i) k)), Some q).
Proof. intros * Ha * Hi Hk. apply (proj2 (Ha i Hi) k Hk). Qed.

Lemma arr64_val : forall mem addr q lo hi f, arr64 mem addr q lo hi f -> forall i, lo <= i < hi -> 0 <= f i < two64.
Proof. intros * Ha * Hi. apply (proj1 (Ha i Hi)). Qed.

Lemma arr64_sub : forall mem addr q lo hi lo' hi' f, lo <= lo' -> hi' <= hi -> arr64 mem addr q lo hi f -> arr64 mem addr q lo' hi' f.
Proof. intros * ? ? Ha i Hi. apply Ha. lia. Qed.

(** Storing element [hi] extends the array. *)
Lemma arr64_store_extend : forall mem addr q lo hi f v, 0 <= v < two64 ->
  arr64 mem addr q lo hi f -> arr64 (store64_mem (addr + 8 * hi) q v mem) addr q lo (hi + 1) (upd64 f hi v).
Proof.
  intros * Hv Ha i Hi. unfold upd64. destruct (Z.eqb_spec i hi) as [-> | Hne].
  - split; [exact Hv |]. intros k Hk. unfold store64_mem.
    assert (k = 0 \/ k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7) as H by lia.
    repeat (destruct H as [-> | H]; [repeat (rewrite IntMaps.IP.F.add_neq_o by lia); rewrite IntMaps.IP.F.add_eq_o by lia; reflexivity |]).
    subst. repeat (rewrite IntMaps.IP.F.add_neq_o by lia). rewrite IntMaps.IP.F.add_eq_o by lia. reflexivity.
  - destruct (Ha i ltac:(lia)) as [Hb Hc]. split; [exact Hb |]. intros k Hk.
    unfold store64_mem. repeat (rewrite IntMaps.IP.F.add_neq_o by lia). apply Hc. exact Hk.
Qed.

(** The address given as the handler computes it. *)
Lemma arr64_store_extend' : forall mem addr q lo hi f v a, a = addr + 8 * hi -> 0 <= v < two64 ->
  arr64 mem addr q lo hi f -> arr64 (store64_mem a q v mem) addr q lo (hi + 1) (upd64 f hi v).
Proof. intros * -> Hv Ha. apply arr64_store_extend; assumption. Qed.

Lemma arr64_ext : forall mem addr q lo hi f g, (forall i, lo <= i < hi -> f i = g i) -> arr64 mem addr q lo hi f -> arr64 mem addr q lo hi g.
Proof. intros * Hfg Ha i Hi. destruct (Ha i Hi) as [Hb Hc]. rewrite Hfg in Hb, Hc by exact Hi. split; assumption. Qed.

(** Stores elsewhere. *)
Lemma arr64_store_other : forall mem addr q lo hi f k (b : byte), (k < addr + 8 * lo \/ addr + 8 * hi <= k) ->
  arr64 mem addr q lo hi f -> arr64 (IM.add k b mem) addr q lo hi f.
Proof.
  intros * Hk Ha i Hi. destruct (Ha i Hi) as [Hb Hc]. split; [exact Hb |]. intros j Hj.
  rewrite IntMaps.IP.F.add_neq_o by lia. apply Hc. exact Hj.
Qed.

Lemma arr64_store64_other : forall mem addr q lo hi f a q' v, (a + 8 <= addr + 8 * lo \/ addr + 8 * hi <= a) ->
  arr64 mem addr q lo hi f -> arr64 (store64_mem a q' v mem) addr q lo hi f.
Proof.
  intros * Hd Ha i Hi. destruct (Ha i Hi) as [Hb Hc]. split; [exact Hb |]. intros j Hj.
  unfold store64_mem. repeat (rewrite IntMaps.IP.F.add_neq_o by lia). apply Hc. exact Hj.
Qed.

Lemma arr64_alloc_other : forall L addr2 q2 mem addr q lo hi f,
  addr + 8 * hi <= addr2 -> arr64 mem addr q lo hi f -> arr64 (alloc_mem L addr2 q2 mem) addr q lo hi f.
Proof.
  intros * Hd Ha i Hi. destruct (Ha i Hi) as [Hb Hc]. split; [exact Hb |]. intros j Hj.
  rewrite find_alloc_mem_other by lia. apply Hc. exact Hj.
Qed.

(** The address of element [i]: [getelementptr i64, ptr %a, i64 %i]. *)
Lemma gep64 : forall (a : Z) (pr : prov) i, 0 <= i < 1152921504606846976 ->
  eval_gep (DTYPE_I 64) (DVALUE_Base (DVALUE_Pointer (a, pr))) [DVALUE_Base (DVALUE_I 64 (Integers.repr i))]
  = raise_ret (DVALUE_Base (DVALUE_Pointer (a + 8 * i, pr))).
Proof.
  intros. cbn. rewrite signed_repr64 by (unfold two63; lia). destruct i; reflexivity.
Qed.

(** * The instructions *)

Section Runner64.
  Variable fundefs : IntMap function_denotation.

  Lemma runX_exp_gep64 : forall ea ei addr q i s,
    runX fundefs (denote_exp' (Some (DTYPE_Pointer : dtyp)) ea) s ≈ Ret (s, inr (DVALUE_Base (DVALUE_Pointer (addr, Some [q])))) ->
    runX fundefs (denote_exp' (Some LL.i64) ei) s ≈ Ret (s, inr (dvZ i)) ->
    0 <= i < 1152921504606846976 ->
    runX fundefs (denote_exp' None (OP_GetElementPtr (DTYPE_I 64 : dtyp) (DTYPE_Pointer : dtyp, ea) [(LL.i64, ei)])) s
      ≈ Ret (s, inr (DVALUE_Base (DVALUE_Pointer (addr + 8 * i, Some [q])))).
  Proof.
    intros. unfold denote_exp' in *. cbn. unfold withCall in *.
    rewrite translate_bind. eapply runX_bind_step; [exact H |].
    rewrite translate_bind. eapply runX_bind_step.
    { rewrite translate_bind. eapply runX_bind_step; [exact H0 |].
      try (rewrite translate_bind; eapply runX_bind_step; [rewrite translate_ret; apply runX_ret |]).
      cbn. rewrite translate_ret. apply runX_ret. }
    unfold dvZ. rewrite gep64 by exact H1. cbn. rewrite translate_ret. apply runX_ret.
  Qed.

  (** [store i64 v, ptr p] where [v] evaluates to [dvZ z]. *)
  Lemma runX_instr_store64 : forall k ev ep anns md va addr q z b0 b1 b2 b3 b4 b5 b6 b7 mem fs heap p env exc loc stk g,
    runX fundefs (denote_exp' (Some LL.i64) ev) (ST (mkState (mkMemoryStack mem fs heap) p) env exc loc stk g)
      ≈ Ret (ST (mkState (mkMemoryStack mem fs heap) p) env exc loc stk g, inr (dvZ z)) ->
    runX fundefs (denote_exp' (Some (DTYPE_Pointer : dtyp)) ep) (ST (mkState (mkMemoryStack mem fs heap) p) env exc loc stk g)
      ≈ Ret (ST (mkState (mkMemoryStack mem fs heap) p) env exc loc stk g, inr (DVALUE_Base (DVALUE_Pointer (addr, Some [q])))) ->
    0 <= z < two64 ->
    IM.find (addr + 0) mem = Some (b0, Some q) -> IM.find (addr + 1) mem = Some (b1, Some q) ->
    IM.find (addr + 2) mem = Some (b2, Some q) -> IM.find (addr + 3) mem = Some (b3, Some q) ->
    IM.find (addr + 4) mem = Some (b4, Some q) -> IM.find (addr + 5) mem = Some (b5, Some q) ->
    IM.find (addr + 6) mem = Some (b6, Some q) -> IM.find (addr + 7) mem = Some (b7, Some q) ->
    runX fundefs (denote_instr (IVoid k, INSTR_Store (LL.i64, ev) (DTYPE_Pointer : dtyp, ep) anns, md) va)
      (ST (mkState (mkMemoryStack mem fs heap) p) env exc loc stk g)
      ≈ Ret (ST (mkState (mkMemoryStack (store64_mem addr q z mem) fs heap) p) env exc loc stk g, inr tt).
  Proof.
    intros. cbn. eapply runX_bind_step; [exact H |]. eapply runX_bind_step; [exact H0 |]. cbn.
    eapply runX_bind_step.
    { apply runX_of_runF_trigger; [reflexivity |]. eapply runF_mem_eq. eapply mem_store64; eassumption. }
    apply runX_ret.
  Qed.
End Runner64.

Section Load64.
  Variable fundefs : IntMap function_denotation.
  Variables (x : raw_id) (ep : llexpr) (anns : list (annotation dtyp)) (md : list (metadata dtyp)) (va : option ptr)
            (addr : Z) (q : N) (z0 z1 z2 z3 z4 z5 z6 z7 : Z) (mem : memory) (fs : Framestack) (heap : Heap) (p : provenance)
            (env : local_env) (exc : option dvalue) (loc : option string) (stk : stack) (g : global_env).
  Hypothesis Hp : runX fundefs (denote_exp' (Some (DTYPE_Pointer : dtyp)) ep) (ST (mkState (mkMemoryStack mem fs heap) p) env exc loc stk g)
      ≈ Ret (ST (mkState (mkMemoryStack mem fs heap) p) env exc loc stk g, inr (DVALUE_Base (DVALUE_Pointer (addr, Some [q])))).
  Hypotheses (H0 : IM.find (addr + 0) mem = Some (BYTE_I (Integers.repr z0), Some q))
             (H1 : IM.find (addr + 1) mem = Some (BYTE_I (Integers.repr z1), Some q))
             (H2 : IM.find (addr + 2) mem = Some (BYTE_I (Integers.repr z2), Some q))
             (H3 : IM.find (addr + 3) mem = Some (BYTE_I (Integers.repr z3), Some q))
             (H4 : IM.find (addr + 4) mem = Some (BYTE_I (Integers.repr z4), Some q))
             (H5 : IM.find (addr + 5) mem = Some (BYTE_I (Integers.repr z5), Some q))
             (H6 : IM.find (addr + 6) mem = Some (BYTE_I (Integers.repr z6), Some q))
             (H7 : IM.find (addr + 7) mem = Some (BYTE_I (Integers.repr z7), Some q)).
  Hypotheses (B0 : 0 <= z0 < 256) (B1 : 0 <= z1 < 256) (B2 : 0 <= z2 < 256) (B3 : 0 <= z3 < 256)
             (B4 : 0 <= z4 < 256) (B5 : 0 <= z5 < 256) (B6 : 0 <= z6 < 256) (B7 : 0 <= z7 < 256).
  (** [x = load i64, ptr p]: the eight flags as one value. *)
  Lemma runX_instr_load64 :
    runX fundefs (denote_instr (IId x, INSTR_Load LL.i64 (DTYPE_Pointer : dtyp, ep) anns, md) va)
      (ST (mkState (mkMemoryStack mem fs heap) p) env exc loc stk g)
      ≈ Ret (ST (mkState (mkMemoryStack mem fs heap) p) (Maps.add x (dvZ (bytes8 z0 z1 z2 z3 z4 z5 z6 z7)) env) exc loc stk g, inr tt).
  Proof.
    cbn. eapply runX_bind_step; [exact Hp |].
    eapply runX_bind_step.
    { apply runX_of_runF_trigger; [reflexivity |]. eapply runF_mem_eq. eapply mem_load64; eassumption. }
    apply runX_lwrite.
  Qed.
End Load64.

Section Load64Val.
  Variable fundefs : IntMap function_denotation.
  Variables (x : raw_id) (ep : llexpr) (anns : list (annotation dtyp)) (md : list (metadata dtyp)) (va : option ptr)
            (addr : Z) (q : N) (v : Z) (mem : memory) (fs : Framestack) (heap : Heap) (p : provenance)
            (env : local_env) (exc : option dvalue) (loc : option string) (stk : stack) (g : global_env).
  Hypothesis Hp : runX fundefs (denote_exp' (Some (DTYPE_Pointer : dtyp)) ep) (ST (mkState (mkMemoryStack mem fs heap) p) env exc loc stk g)
      ≈ Ret (ST (mkState (mkMemoryStack mem fs heap) p) env exc loc stk g, inr (DVALUE_Base (DVALUE_Pointer (addr, Some [q])))).
  Hypotheses (H0 : IM.find (addr + 0) mem = Some (BYTE_I (Integers.repr (byte_k v 0)), Some q))
             (H1 : IM.find (addr + 1) mem = Some (BYTE_I (Integers.repr (byte_k v 1)), Some q))
             (H2 : IM.find (addr + 2) mem = Some (BYTE_I (Integers.repr (byte_k v 2)), Some q))
             (H3 : IM.find (addr + 3) mem = Some (BYTE_I (Integers.repr (byte_k v 3)), Some q))
             (H4 : IM.find (addr + 4) mem = Some (BYTE_I (Integers.repr (byte_k v 4)), Some q))
             (H5 : IM.find (addr + 5) mem = Some (BYTE_I (Integers.repr (byte_k v 5)), Some q))
             (H6 : IM.find (addr + 6) mem = Some (BYTE_I (Integers.repr (byte_k v 6)), Some q))
             (H7 : IM.find (addr + 7) mem = Some (BYTE_I (Integers.repr (byte_k v 7)), Some q)).
  Hypothesis Hv : 0 <= v < two64.
  (** [x = load i64, ptr p] of a stored 64-bit value. *)
  Lemma runX_instr_load64_val :
    runX fundefs (denote_instr (IId x, INSTR_Load LL.i64 (DTYPE_Pointer : dtyp, ep) anns, md) va)
      (ST (mkState (mkMemoryStack mem fs heap) p) env exc loc stk g)
      ≈ Ret (ST (mkState (mkMemoryStack mem fs heap) p) (Maps.add x (dvZ v) env) exc loc stk g, inr tt).
  Proof.
    rewrite <- (bytes8_byte_k v Hv).
    apply (runX_instr_load64 fundefs x ep anns md va addr q (byte_k v 0) (byte_k v 1) (byte_k v 2) (byte_k v 3)
             (byte_k v 4) (byte_k v 5) (byte_k v 6) (byte_k v 7) mem fs heap p env exc loc stk g Hp H0 H1 H2 H3 H4 H5 H6 H7);
      apply byte_k_bounds.
  Qed.
End Load64Val.

(** * Tactics *)

(* The eight memory facts of a 64-bit access ([IM.find (addr + k) mem = Some (_, Some _)]),
   the byte bounds of a 64-bit load of flags, and the value bound of a 64-bit
   load of a stored value; programs redefine them with [::=]. *)
Ltac mem_fact64 := fail "mem_fact64: provide the memory fact (redefine it with Ltac mem_fact64 ::= ...)".
Ltac byte_bounds := fail "byte_bounds: provide the byte bound (redefine it with Ltac byte_bounds ::= ...)".
Ltac val_bounds := bounds.

Ltac run_exp ::=
  lazymatch goal with
  | |- eutt eq (runX _ (denote_exp' _ (EXP_Integer _)) _) _ => apply runX_exp_lit_sz
  | |- eutt eq (runX _ (denote_exp' _ (EXP_Ident (ID_Local _))) _) _ =>
      apply runX_exp_local; simpl_lookup; first [reflexivity | eassumption]
  | |- eutt eq (runX _ (denote_exp' _ (EXP_Ident (ID_Global _))) _) _ =>
      apply runX_exp_global; simpl_lookup; first [reflexivity | eassumption]
  | |- eutt eq (runX _ (denote_exp' _ (OP_IBinop _ _ _ _)) _) _ => eapply runX_exp_ibinop; [run_exp | run_exp | eval_op]
  | |- eutt eq (runX _ (denote_exp' _ (OP_ICmp _ _ _ _ _)) _) _ => eapply runX_exp_icmp; [run_exp | run_exp | eval_op]
  | |- eutt eq (runX _ (denote_exp' _ (OP_GetElementPtr (DTYPE_Base (DTYPE_I 8)) _ _)) _) _ => eapply runX_exp_gep; [run_exp | run_exp | bounds]
  | |- eutt eq (runX _ (denote_exp' _ (OP_GetElementPtr (DTYPE_Base (DTYPE_I 64)) _ _)) _) _ => eapply runX_exp_gep64; [run_exp | run_exp | bounds]
  | |- eutt eq (runX _ (denote_exp' _ (OP_Conversion _ _ _ _)) _) _ => eapply runX_exp_zext8k; [run_exp | bounds]
  end.

Ltac run_instr ::=
  lazymatch goal with
  | |- eutt eq (runX _ (denote_instr (_, INSTR_Op _, _) _) _) _ => eapply runX_instr_op; run_exp
  | |- eutt eq (runX _ (denote_instr (_, INSTR_Call _ _ _ _, _) _) _) _ =>
      eapply runX_instr_call_n; [reflexivity | run_args | simpl_lookup; eassumption | eassumption | run_callee]
  | |- eutt eq (runX _ (denote_instr (_, INSTR_Load (DTYPE_Base (DTYPE_I 8)) _ _, _) _) _) _ =>
      eapply runX_instr_load8; [run_exp | mem_fact]
  | |- eutt eq (runX _ (denote_instr (_, INSTR_Load (DTYPE_Base (DTYPE_I 64)) _ _, _) _) _) _ =>
      first [ eapply runX_instr_load64_val;
              [run_exp | mem_fact64 | mem_fact64 | mem_fact64 | mem_fact64 | mem_fact64 | mem_fact64 | mem_fact64 | mem_fact64 | val_bounds]
            | eapply runX_instr_load64;
              [run_exp | mem_fact64 | mem_fact64 | mem_fact64 | mem_fact64 | mem_fact64 | mem_fact64 | mem_fact64 | mem_fact64
               | byte_bounds | byte_bounds | byte_bounds | byte_bounds | byte_bounds | byte_bounds | byte_bounds | byte_bounds] ]
  | |- eutt eq (runX _ (denote_instr (_, INSTR_Store (DTYPE_Base (DTYPE_I 8), _) _ _, _) _) _) _ =>
      eapply runX_instr_store8; [run_exp | run_exp | mem_fact]
  | |- eutt eq (runX _ (denote_instr (_, INSTR_Store (DTYPE_Base (DTYPE_I 64), _) _ _, _) _) _) _ =>
      eapply runX_instr_store64;
      [run_exp | run_exp | bounds | mem_fact64 | mem_fact64 | mem_fact64 | mem_fact64 | mem_fact64 | mem_fact64 | mem_fact64 | mem_fact64]
  | |- eutt eq (runX _ (denote_instr (IId ?x, INSTR_Alloca _ _, _) _) _) _ =>
      match goal with H : eutt eq (runX _ (denote_instr (IId x, INSTR_Alloca _ _, _) _) _) _ |- _ => exact H end
  end.
