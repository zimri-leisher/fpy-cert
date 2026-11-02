(** More instructions for the symbolic execution of [VellvmRun], [VellvmMem], [VellvmMem64]:
    bitwise operators and shifts (i64, i8, i1), [select], zero extension from i1 and i32,
    truncation to i32, [getelementptr] on [i32] arrays, and 32-bit loads and stores. *)

From Stdlib Require Import ZArith NArith String List Lia Bool.
From ExtLib Require Import Structures.Maps Structures.Monads.
From ITree Require Import ITree ITreeFacts.
From Vellvm Require Import Syntax Utils Params Semantics Interfaces.Memory ParamsV IPtrInfinite.
From Vellvm Require Import Implementations.Memory Semantics.Libraries.
From FpyCert Require Import LLVMBuilder VellvmRun VellvmMem VellvmMem64.
Import ListNotations ITreeNotations.
Open Scope string_scope. Open Scope itree_scope. Open Scope Z_scope.
Unset Implicit Arguments.

Notation "t1 ≈ t2" := (eutt eq t1 t2) (at level 70, only parsing).

#[local] Instance Pa : Params := @ParamsV IPZ IPZTheory.

(** * Values *)

(** An [i1] (a comparison result) and an [i32] value. *)
Definition dv1 (c : bool) : dvalue := DVALUE_Base (if c then DVALUE_I 1 Integers.one else DVALUE_I 1 Integers.zero).
Definition dv32 (z : Z) : dvalue := DVALUE_Base (DVALUE_I 32 (Integers.repr z)).
Definition two32 : Z := 4294967296.

Lemma unsigned_repr32 : forall z, 0 <= z < two32 -> Integers.unsigned (@Integers.repr 32 z) = z.
Proof. intros. apply Integers.unsigned_repr. unfold Integers.max_unsigned. replace (@Integers.modulus 32) with two32 by (vm_compute; reflexivity). lia. Qed.

Lemma modulus8 : @Integers.modulus 8 = 256.
Proof. vm_compute. reflexivity. Qed.
Lemma modulus32 : @Integers.modulus 32 = two32.
Proof. vm_compute. reflexivity. Qed.

(** * The evaluators *)

Section Evaluators.
  Let d64 (x : @Integers.bit_int 64) : dvalue := DVALUE_Base (DVALUE_I 64 x).
  Let d8 (x : @Integers.bit_int 8) : dvalue := DVALUE_Base (DVALUE_I 8 x).

  Lemma eval_iop_and64 : forall a b, eval_iop LLVMAst.And (d64 a) (d64 b) = raise_ret (d64 (Integers.and a b)).
  Proof. reflexivity. Qed.
  Lemma eval_iop_or64 : forall a b, eval_iop (LLVMAst.Or false) (d64 a) (d64 b) = raise_ret (d64 (Integers.or a b)).
  Proof. reflexivity. Qed.
  Lemma eval_iop_xor64 : forall a b, eval_iop LLVMAst.Xor (d64 a) (d64 b) = raise_ret (d64 (Integers.xor a b)).
  Proof. reflexivity. Qed.
  Lemma eval_iop_shl64 : forall a b, Integers.unsigned b < 64 ->
    eval_iop (LLVMAst.Shl false false) (d64 a) (d64 b) = raise_ret (d64 (Integers.shl a b)).
  Proof.
    intros a b H. cbn. destruct (Integers.unsigned b >=? 64) eqn:E; [apply Z.geb_le in E; lia |]. reflexivity.
  Qed.
  Lemma eval_iop_and8 : forall a b, eval_iop LLVMAst.And (d8 a) (d8 b) = raise_ret (d8 (Integers.and a b)).
  Proof. reflexivity. Qed.
  Lemma eval_iop_and1 : forall c1 c2, eval_iop LLVMAst.And (dv1 c1) (dv1 c2) = raise_ret (dv1 (c1 && c2)).
  Proof. intros [|] [|]; reflexivity. Qed.
  (* the same, in the unfolded form in which comparison results appear *)
  Lemma eval_iop_and1' : forall c1 c2 : bool,
    eval_iop LLVMAst.And (DVALUE_Base (if c1 then DVALUE_I 1 Integers.one else DVALUE_I 1 Integers.zero))
                         (DVALUE_Base (if c2 then DVALUE_I 1 Integers.one else DVALUE_I 1 Integers.zero))
    = raise_ret (DVALUE_Base (if c1 && c2 then DVALUE_I 1 Integers.one else DVALUE_I 1 Integers.zero)).
  Proof. intros [|] [|]; reflexivity. Qed.
  Lemma eval_icmp_ule : forall a b, eval_icmp false LLVMAst.Ule (d64 a) (d64 b)
    = raise_ret (DVALUE_Base (if negb (Integers.ltu b a) then DVALUE_I 1 Integers.one else DVALUE_I 1 Integers.zero)).
  Proof. reflexivity. Qed.
  Lemma eval_icmp_uge : forall a b, eval_icmp false LLVMAst.Uge (d64 a) (d64 b)
    = raise_ret (DVALUE_Base (if negb (Integers.ltu a b) then DVALUE_I 1 Integers.one else DVALUE_I 1 Integers.zero)).
  Proof. reflexivity. Qed.
  Lemma eval_icmp_ne : forall a b, eval_icmp false LLVMAst.Ne (d64 a) (d64 b)
    = raise_ret (DVALUE_Base (if negb (Integers.eq a b) then DVALUE_I 1 Integers.one else DVALUE_I 1 Integers.zero)).
  Proof. reflexivity. Qed.
End Evaluators.

(** The integer operations on in-range values, as [Z] operations. *)
Lemma and_repr64 : forall a b, 0 <= a < two64 -> 0 <= b < two64 ->
  Integers.and (@Integers.repr 64 a) (Integers.repr b) = Integers.repr (Z.land a b).
Proof. intros. unfold Integers.and. rewrite !unsigned_repr64 by assumption. reflexivity. Qed.
Lemma or_repr64 : forall a b, 0 <= a < two64 -> 0 <= b < two64 ->
  Integers.or (@Integers.repr 64 a) (Integers.repr b) = Integers.repr (Z.lor a b).
Proof. intros. unfold Integers.or. rewrite !unsigned_repr64 by assumption. reflexivity. Qed.
Lemma xor_repr64 : forall a b, 0 <= a < two64 -> 0 <= b < two64 ->
  Integers.xor (@Integers.repr 64 a) (Integers.repr b) = Integers.repr (Z.lxor a b).
Proof. intros. unfold Integers.xor. rewrite !unsigned_repr64 by assumption. reflexivity. Qed.
Lemma shl_repr64 : forall a k, 0 <= a < two64 -> 0 <= k < 64 ->
  Integers.shl (@Integers.repr 64 a) (Integers.repr k) = Integers.repr (a * 2 ^ k).
Proof.
  intros. unfold Integers.shl. rewrite !unsigned_repr64 by (unfold two64 in *; lia).
  rewrite Z.shiftl_mul_pow2 by lia. reflexivity.
Qed.
Lemma and_repr8 : forall a b, 0 <= a < 256 -> 0 <= b < 256 ->
  Integers.and (@Integers.repr 8 a) (Integers.repr b) = Integers.repr (Z.land a b).
Proof. intros. unfold Integers.and. rewrite !unsigned_repr8 by assumption. reflexivity. Qed.

(** [select], conversions and [getelementptr i32]. *)
Lemma eval_select_dv1 : forall (c : bool) t v1 v2, eval_select (dv1 c) t v1 v2 = raise_ret (if c then v1 else v2).
Proof. intros [|] t v1 v2; reflexivity. Qed.

Lemma zext1 : forall c : bool,
  convert_pure (Zext false) (DTYPE_I 1) (dv1 c) (DTYPE_I 64) = raise_ret (dvZ (if c then 1 else 0)).
Proof. intros [|]; reflexivity. Qed.

Lemma zext32 : forall z, 0 <= z < two32 ->
  convert_pure (Zext false) (DTYPE_I 32) (dv32 z) (DTYPE_I 64) = raise_ret (dvZ z).
Proof.
  intros z Hz. cbn. unfold dvZ. rewrite Integers.Z_mod_modulus_eq, modulus32, Z.mod_small by exact Hz. reflexivity.
Qed.

Lemma trunc32 : forall z, 0 <= z < two64 ->
  convert_pure (Trunc false false) (DTYPE_I 64) (dvZ z) (DTYPE_I 32) = raise_ret (dv32 (z mod two32)).
Proof.
  intros z Hz. cbn. unfold dv32. rewrite Integers.Z_mod_modulus_eq, modulus_64, Z.mod_small by exact Hz.
  do 3 f_equal. apply Integers.eqm_samerepr. unfold Integers.eqm. rewrite modulus32. apply Zbits.eqmod_mod.
Qed.

Lemma gep32 : forall (a : Z) (pr : prov) i, 0 <= i < 2305843009213693952 ->
  eval_gep (DTYPE_I 32) (DVALUE_Base (DVALUE_Pointer (a, pr))) [DVALUE_Base (DVALUE_I 64 (Integers.repr i))]
  = raise_ret (DVALUE_Base (DVALUE_Pointer (a + 4 * i, pr))).
Proof. intros. cbn. rewrite signed_repr64 by (unfold two63; lia). destruct i; reflexivity. Qed.

(** * 32-bit memory *)

Opaque Integers.repr Integers.unsigned Integers.signed Integers.mul Integers.add Integers.eq Integers.ltu
  Integers.zero Integers.one.

Lemma extract_byte_repr32 : forall v (idx : N), 0 <= v < two32 -> (idx < 4)%N ->
  extract_byte_vint (@Integers.repr 32 v) idx = byte_k v (Z.of_N idx).
Proof.
  intros * Hv Hidx. unfold two32 in Hv. unfold extract_byte_vint, byte_k.
  cbn [VellvmIntegers.unsigned VellvmIntegers.modu VellvmIntegers.shru VellvmIntegers.repr VellvmIntegers.VInt_Bounded].
  unfold Integers.modu, Integers.shru.
  assert (Hp : 0 < 2 ^ (8 * Z.of_N idx)) by (apply Z.pow_pos_nonneg; lia).
  assert (Hq : 0 <= v / 2 ^ (8 * Z.of_N idx) <= v).
  { split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; [lia | nia]]. }
  pose proof (Z.mod_pos_bound (v / 2 ^ (8 * Z.of_N idx)) 256 ltac:(lia)) as Hm.
  rewrite (unsigned_repr32 v) by (unfold two32; lia).
  rewrite (unsigned_repr32 (Z.of_N idx * 8)) by (unfold two32; lia).
  rewrite Z.shiftr_div_pow2 by lia. replace (Z.of_N idx * 8) with (8 * Z.of_N idx) by lia.
  rewrite (unsigned_repr32 (v / 2 ^ (8 * Z.of_N idx))) by (unfold two32; lia).
  rewrite (unsigned_repr32 256) by (unfold two32; lia).
  rewrite unsigned_repr32 by (unfold two32; lia).
  reflexivity.
Qed.
Opaque Integers.modu Integers.shru Integers.sub Integers.divu.

(** The memory after storing the four bytes of [v] at [a .. a + 3]. *)
Definition store32_mem (a : Z) (q : N) (v : Z) (mem : memory) : memory :=
  IM.add (a + 3) (BYTE_I (Integers.repr (byte_k v 3)), Some q)
  (IM.add (a + 2) (BYTE_I (Integers.repr (byte_k v 2)), Some q)
  (IM.add (a + 1) (BYTE_I (Integers.repr (byte_k v 1)), Some q)
  (IM.add (a + 0) (BYTE_I (Integers.repr (byte_k v 0)), Some q) mem))).

Lemma mem_store32 : forall mem fs heap p (a : Z) (q : N) v b0 b1 b2 b3,
  0 <= v < two32 ->
  IM.find (a + 0) mem = Some (b0, Some q) -> IM.find (a + 1) mem = Some (b1, Some q) ->
  IM.find (a + 2) mem = Some (b2, Some q) -> IM.find (a + 3) mem = Some (b3, Some q) ->
  (handle_memory memM_interp (Store (DTYPE_I 32) (DVALUE_Base (DVALUE_Pointer (a, Some [q]))) (DVALUE_Base (DVALUE_I 32 (Integers.repr v))))
     (mkState (mkMemoryStack mem fs heap) p) : itree MCFGEbot _)
    ≈ Ret (mkState (mkMemoryStack (store32_mem a q v mem) fs heap) p, tt).
Proof.
  intros * Hv H0 H1 H2 H3.
  unfold handle_memory. cbn -[extract_byte_vint IM.find IM.add]. unfold read_byte_raw_mem.
  store_round H0. store_round H1. store_round H2. store_round H3.
  unfold set_byte_raw_mem. rewrite !extract_byte_repr32 by lia. unfold store32_mem. reflexivity.
Qed.

(** Four bytes, little-endian. *)
Definition bytes4 (z0 z1 z2 z3 : Z) : Z := z0 + 256 * (z1 + 256 * (z2 + 256 * z3)).

Lemma bytes_to_i32 : forall z0 z1 z2 z3,
  0 <= z0 < 256 -> 0 <= z1 < 256 -> 0 <= z2 < 256 -> 0 <= z3 < 256 ->
  memory_bytes_to_dvalue [BYTE_I (@Integers.repr 8 z0); BYTE_I (Integers.repr z1); BYTE_I (Integers.repr z2); BYTE_I (Integers.repr z3)] (DTYPE_I 32)
  = raise_ret (DVALUE_Base (DVALUE_I 32 (Integers.repr (bytes4 z0 z1 z2 z3)))).
Proof.
  intros. cbn -[Z.shiftl]. rewrite !unsigned_repr8 by lia. rewrite !Z.shiftl_mul_pow2 by lia.
  change (2 ^ 8) with 256. unfold bytes4. do 4 f_equal. lia.
Qed.

Lemma bytes4_byte_k : forall v, 0 <= v < two32 -> bytes4 (byte_k v 0) (byte_k v 1) (byte_k v 2) (byte_k v 3) = v.
Proof.
  intros v Hv. unfold two32 in Hv. unfold bytes4, byte_k.
  replace (8 * 0) with 0 by lia. replace (8 * 1) with 8 by lia. replace (8 * 2) with 16 by lia. replace (8 * 3) with 24 by lia.
  rewrite Z.pow_0_r, Z.div_1_r.
  pose proof (div_step256 v 0 8 ltac:(lia) ltac:(lia) ltac:(reflexivity)) as E0. rewrite Z.pow_0_r, Z.div_1_r in E0.
  pose proof (div_step256 v 8 16 ltac:(lia) ltac:(lia) ltac:(reflexivity)) as E1.
  pose proof (div_step256 v 16 24 ltac:(lia) ltac:(lia) ltac:(reflexivity)) as E2.
  pose proof (div_step256 v 24 32 ltac:(lia) ltac:(lia) ltac:(reflexivity)) as E3.
  assert (E4 : v / 2 ^ 32 = 0) by (apply Z.div_small; lia).
  lia.
Qed.

Section Load32Sec.
  Variables (mem : memory) (fs : Framestack) (heap : Heap) (p : provenance) (a : Z) (q : N) (z0 z1 z2 z3 : Z).
  Hypotheses (H0 : IM.find (a + 0) mem = Some (BYTE_I (Integers.repr z0), Some q))
             (H1 : IM.find (a + 1) mem = Some (BYTE_I (Integers.repr z1), Some q))
             (H2 : IM.find (a + 2) mem = Some (BYTE_I (Integers.repr z2), Some q))
             (H3 : IM.find (a + 3) mem = Some (BYTE_I (Integers.repr z3), Some q)).
  Hypotheses (B0 : 0 <= z0 < 256) (B1 : 0 <= z1 < 256) (B2 : 0 <= z2 < 256) (B3 : 0 <= z3 < 256).

  Ltac load_round H :=
    first [rewrite H | (change (@IM.find byte) with (@IM.find (memory_byte * option N)); rewrite H)];
    cbn -[memory_bytes_to_dvalue IM.find IM.add]; rewrite N.eqb_refl; cbn -[memory_bytes_to_dvalue IM.find IM.add].

  Lemma mem_load32 :
    (handle_memory memM_interp (Load (DTYPE_I 32) (DVALUE_Base (DVALUE_Pointer (a, Some [q])))) (mkState (mkMemoryStack mem fs heap) p)
       : itree MCFGEbot _)
      ≈ Ret (mkState (mkMemoryStack mem fs heap) p, DVALUE_Base (DVALUE_I 32 (Integers.repr (bytes4 z0 z1 z2 z3)))).
  Proof.
    unfold handle_memory, handle_memoryM, read_dvalue, read_bytes.
    change (store_size_dtyp (DTYPE_I 32)) with 4%N. change (@read_byte _ _) with (@Read_byte Pa).
    cbn -[memory_bytes_to_dvalue IM.find IM.add]. unfold read_byte_raw_mem.
    load_round H0. load_round H1. load_round H2. load_round H3.
    rewrite bytes_to_i32 by assumption. cbn. reflexivity.
  Qed.
End Load32Sec.

Lemma shru_repr64' : forall a k, 0 <= a < two64 -> 0 <= k < 64 ->
  Integers.shru (@Integers.repr 64 a) (Integers.repr k) = Integers.repr (a / 2 ^ k).
Proof. intros. rewrite shru_repr64 by lia. rewrite Z.mod_small by lia. reflexivity. Qed.

(** * The runners *)

Section RunnerOps.
  Variable fundefs : IntMap function_denotation.
  Notation runX := (runX fundefs).

  (** A binary operator at any integer type. *)
  Lemma runX_exp_ibinop_t : forall (t : dtyp) iop ea eb va vb vr s,
    runX (denote_exp' (Some t) ea) s ≈ Ret (s, inr va) ->
    runX (denote_exp' (Some t) eb) s ≈ Ret (s, inr vb) ->
    eval_iop iop va vb = raise_ret vr ->
    runX (denote_exp' None (OP_IBinop iop t ea eb)) s ≈ Ret (s, inr vr).
  Proof.
    intros. unfold denote_exp' in *. cbn. unfold withCall in *.
    rewrite translate_bind. eapply runX_bind_step; [exact H |].
    rewrite translate_bind. eapply runX_bind_step; [exact H0 |].
    rewrite H1. cbn. rewrite translate_ret. apply runX_ret.
  Qed.

  (** [select i1 c, i64 a, i64 b]. *)
  Lemma runX_exp_select : forall ec e1 e2 (c : bool) v1 v2 s,
    runX (denote_exp' (Some (DTYPE_I 1 : dtyp)) ec) s
      ≈ Ret (s, inr (DVALUE_Base (if c then DVALUE_I 1 Integers.one else DVALUE_I 1 Integers.zero))) ->
    runX (denote_exp' (Some LL.i64) e1) s ≈ Ret (s, inr v1) ->
    runX (denote_exp' (Some LL.i64) e2) s ≈ Ret (s, inr v2) ->
    runX (denote_exp' None (OP_Select ((DTYPE_I 1 : dtyp), ec) (LL.i64, e1) (LL.i64, e2))) s ≈ Ret (s, inr (if c then v1 else v2)).
  Proof.
    intros. unfold denote_exp' in *. cbn -[eval_select]. unfold withCall in *.
    rewrite translate_bind. eapply runX_bind_step; [exact H |].
    rewrite translate_bind. eapply runX_bind_step; [exact H0 |].
    rewrite translate_bind. eapply runX_bind_step; [exact H1 |].
    change (DVALUE_Base (if c then DVALUE_I 1 Integers.one else DVALUE_I 1 Integers.zero)) with (dv1 c).
    rewrite eval_select_dv1. cbn. rewrite translate_ret. apply runX_ret.
  Qed.

  (** Conversions: [zext i1/i32 to i64], [trunc i64 to i32]. *)
  Lemma runX_exp_zext1 : forall e (c : bool) s,
    runX (denote_exp' (Some (DTYPE_I 1 : dtyp)) e) s
      ≈ Ret (s, inr (DVALUE_Base (if c then DVALUE_I 1 Integers.one else DVALUE_I 1 Integers.zero))) ->
    runX (denote_exp' None (OP_Conversion (CONV_Pure (Zext false)) (DTYPE_I 1 : dtyp) e LL.i64)) s
      ≈ Ret (s, inr (dvZ (if c then 1 else 0))).
  Proof.
    intros. unfold denote_exp' in *. cbn. unfold withCall in *.
    rewrite translate_bind. eapply runX_bind_step; [exact H |].
    destruct c; cbn; rewrite translate_ret; apply runX_ret.
  Qed.

  Lemma runX_exp_zext32 : forall e z s,
    runX (denote_exp' (Some (DTYPE_I 32 : dtyp)) e) s ≈ Ret (s, inr (dv32 z)) -> 0 <= z < two32 ->
    runX (denote_exp' None (OP_Conversion (CONV_Pure (Zext false)) (DTYPE_I 32 : dtyp) e LL.i64)) s ≈ Ret (s, inr (dvZ z)).
  Proof.
    intros e z s H Hz. unfold denote_exp' in *. cbn. unfold withCall in *.
    rewrite translate_bind. eapply runX_bind_step; [exact H |].
    change (convert (CONV_Pure (Zext false)) (DTYPE_I 32) (dv32 z) (DTYPE_I 64))
      with (lift (convert_pure (Zext false) (DTYPE_I 32) (dv32 z) (DTYPE_I 64)) : itree _ dvalue).
    rewrite zext32 by exact Hz. cbn. rewrite translate_ret. apply runX_ret.
  Qed.

  Lemma runX_exp_trunc32 : forall e z s,
    runX (denote_exp' (Some LL.i64) e) s ≈ Ret (s, inr (dvZ z)) -> 0 <= z < two64 ->
    runX (denote_exp' None (OP_Conversion (CONV_Pure (Trunc false false)) LL.i64 e (DTYPE_I 32 : dtyp))) s
      ≈ Ret (s, inr (dv32 (z mod two32))).
  Proof.
    intros e z s H Hz. unfold denote_exp' in *. cbn. unfold withCall in *.
    rewrite translate_bind. eapply runX_bind_step; [exact H |].
    change (convert (CONV_Pure (Trunc false false)) (DTYPE_I 64) (dvZ z) (DTYPE_I 32))
      with (lift (convert_pure (Trunc false false) (DTYPE_I 64) (dvZ z) (DTYPE_I 32)) : itree _ dvalue).
    rewrite trunc32 by exact Hz. cbn. rewrite translate_ret. apply runX_ret.
  Qed.

  (** [getelementptr i32, ptr %a, i64 %i]. *)
  Lemma runX_exp_gep32 : forall ea ei addr q i s,
    runX (denote_exp' (Some (DTYPE_Pointer : dtyp)) ea) s ≈ Ret (s, inr (DVALUE_Base (DVALUE_Pointer (addr, Some [q])))) ->
    runX (denote_exp' (Some LL.i64) ei) s ≈ Ret (s, inr (dvZ i)) ->
    0 <= i < 2305843009213693952 ->
    runX (denote_exp' None (OP_GetElementPtr (DTYPE_I 32 : dtyp) (DTYPE_Pointer : dtyp, ea) [(LL.i64, ei)])) s
      ≈ Ret (s, inr (DVALUE_Base (DVALUE_Pointer (addr + 4 * i, Some [q])))).
  Proof.
    intros. unfold denote_exp' in *. cbn. unfold withCall in *.
    rewrite translate_bind. eapply runX_bind_step; [exact H |].
    rewrite translate_bind. eapply runX_bind_step.
    { rewrite translate_bind. eapply runX_bind_step; [exact H0 |].
      try (rewrite translate_bind; eapply runX_bind_step; [rewrite translate_ret; apply runX_ret |]).
      cbn. rewrite translate_ret. apply runX_ret. }
    unfold dvZ. rewrite gep32 by exact H1. cbn. rewrite translate_ret. apply runX_ret.
  Qed.

  (** [store i32 v, ptr p]. *)
  Lemma runX_instr_store32 : forall k ev ep anns md va addr q z b0 b1 b2 b3 mem fs heap p env exc loc stk g,
    runX (denote_exp' (Some (DTYPE_I 32 : dtyp)) ev) (ST (mkState (mkMemoryStack mem fs heap) p) env exc loc stk g)
      ≈ Ret (ST (mkState (mkMemoryStack mem fs heap) p) env exc loc stk g, inr (dv32 z)) ->
    runX (denote_exp' (Some (DTYPE_Pointer : dtyp)) ep) (ST (mkState (mkMemoryStack mem fs heap) p) env exc loc stk g)
      ≈ Ret (ST (mkState (mkMemoryStack mem fs heap) p) env exc loc stk g, inr (DVALUE_Base (DVALUE_Pointer (addr, Some [q])))) ->
    0 <= z < two32 ->
    IM.find (addr + 0) mem = Some (b0, Some q) -> IM.find (addr + 1) mem = Some (b1, Some q) ->
    IM.find (addr + 2) mem = Some (b2, Some q) -> IM.find (addr + 3) mem = Some (b3, Some q) ->
    runX (denote_instr (IVoid k, INSTR_Store ((DTYPE_I 32 : dtyp), ev) (DTYPE_Pointer : dtyp, ep) anns, md) va)
      (ST (mkState (mkMemoryStack mem fs heap) p) env exc loc stk g)
      ≈ Ret (ST (mkState (mkMemoryStack (store32_mem addr q z mem) fs heap) p) env exc loc stk g, inr tt).
  Proof.
    intros. cbn. eapply runX_bind_step; [exact H |]. eapply runX_bind_step; [exact H0 |]. cbn.
    eapply runX_bind_step.
    { apply runX_of_runF_trigger; [reflexivity |]. eapply runF_mem_eq. eapply mem_store32; eassumption. }
    apply runX_ret.
  Qed.
End RunnerOps.

Section Load32.
  Variable fundefs : IntMap function_denotation.
  Variables (x : raw_id) (ep : llexpr) (anns : list (annotation dtyp)) (md : list (metadata dtyp)) (va : option ptr)
            (addr : Z) (q : N) (z0 z1 z2 z3 : Z) (mem : memory) (fs : Framestack) (heap : Heap) (p : provenance)
            (env : local_env) (exc : option dvalue) (loc : option string) (stk : stack) (g : global_env).
  Hypothesis Hp : runX fundefs (denote_exp' (Some (DTYPE_Pointer : dtyp)) ep) (ST (mkState (mkMemoryStack mem fs heap) p) env exc loc stk g)
      ≈ Ret (ST (mkState (mkMemoryStack mem fs heap) p) env exc loc stk g, inr (DVALUE_Base (DVALUE_Pointer (addr, Some [q])))).
  Hypotheses (H0 : IM.find (addr + 0) mem = Some (BYTE_I (Integers.repr z0), Some q))
             (H1 : IM.find (addr + 1) mem = Some (BYTE_I (Integers.repr z1), Some q))
             (H2 : IM.find (addr + 2) mem = Some (BYTE_I (Integers.repr z2), Some q))
             (H3 : IM.find (addr + 3) mem = Some (BYTE_I (Integers.repr z3), Some q)).
  Hypotheses (B0 : 0 <= z0 < 256) (B1 : 0 <= z1 < 256) (B2 : 0 <= z2 < 256) (B3 : 0 <= z3 < 256).
  (** [x = load i32, ptr p]. *)
  Lemma runX_instr_load32 :
    runX fundefs (denote_instr (IId x, INSTR_Load (DTYPE_I 32 : dtyp) (DTYPE_Pointer : dtyp, ep) anns, md) va)
      (ST (mkState (mkMemoryStack mem fs heap) p) env exc loc stk g)
      ≈ Ret (ST (mkState (mkMemoryStack mem fs heap) p) (Maps.add x (dv32 (bytes4 z0 z1 z2 z3)) env) exc loc stk g, inr tt).
  Proof.
    cbn. eapply runX_bind_step; [exact Hp |].
    eapply runX_bind_step.
    { apply runX_of_runF_trigger; [reflexivity |]. eapply runF_mem_eq. eapply mem_load32; eassumption. }
    apply runX_lwrite.
  Qed.
End Load32.

(** * Tactics

    The clauses of [VellvmRun], [VellvmMem], [VellvmMem64] plus the new forms. Hooks a program
    proof provides: [mem_fact] (byte cells), [mem_fact64], [mem_fact32] (the cells of an access),
    [byte_bounds] (a loaded byte value is below 256), [val_bounds] (an [i64] element), [val32_bounds]. *)

Ltac mem_fact32 := fail "mem_fact32: provide the memory fact (redefine it with Ltac mem_fact32 ::= ...)".
Ltac val32_bounds := fail "val32_bounds: provide the bound (redefine it with Ltac val32_bounds ::= ...)".

Ltac bounds ::= unfold two64, two63, two32, bytes8, bytes4 in *; first [lia | nia].

(* Comparison results are normalized to [Z] comparisons ([a <=? b], [negb (a =? b)]). *)
Ltac eval_op ::=
  unfold dvZ;
  first [ rewrite eval_iop_mul; rewrite mul_repr64 by bounds
        | rewrite eval_iop_add; rewrite add_repr64 by bounds
        | rewrite eval_iop_sub; rewrite sub_repr64 by bounds
        | rewrite eval_iop_urem by (rewrite unsigned_repr64 by bounds; lia); rewrite modu_repr64 by bounds
        | rewrite eval_iop_udiv by (rewrite unsigned_repr64 by bounds; lia); rewrite divu_repr64 by bounds
        | rewrite eval_iop_and64; rewrite and_repr64 by bounds
        | rewrite eval_iop_or64; rewrite or_repr64 by bounds
        | rewrite eval_iop_xor64; rewrite xor_repr64 by bounds
        | rewrite eval_iop_shl64 by (rewrite unsigned_repr64 by bounds; lia); rewrite shl_repr64 by bounds
        | rewrite eval_iop_lshr by (rewrite unsigned_repr64 by bounds; lia); rewrite shru_repr64' by bounds
        | eval_op_extra
        | rewrite eval_icmp_ult; rewrite ltu_repr64 by bounds
        | rewrite eval_icmp_ugt; rewrite ltu_repr64 by bounds
        | rewrite eval_icmp_ule; rewrite ltu_repr64 by bounds; rewrite <- Z.leb_antisym
        | rewrite eval_icmp_uge; rewrite ltu_repr64 by bounds; rewrite <- Z.leb_antisym
        | rewrite eval_icmp_eq; rewrite eq_repr64 by bounds
        | rewrite eval_icmp_ne; rewrite eq_repr64 by bounds ];
  reflexivity.

Ltac eval_op8 := unfold dv8; rewrite eval_iop_and8; rewrite and_repr8 by (first [byte_bounds | bounds]); reflexivity.
Ltac eval_op1 := rewrite eval_iop_and1'; reflexivity.

Ltac run_exp ::=
  lazymatch goal with
  | |- eutt eq (runX _ (denote_exp' _ (EXP_Integer _)) _) _ => apply runX_exp_lit_sz
  | |- eutt eq (runX _ (denote_exp' _ (EXP_Ident (ID_Local _))) _) _ =>
      apply runX_exp_local; simpl_lookup; first [reflexivity | eassumption]
  | |- eutt eq (runX _ (denote_exp' _ (EXP_Ident (ID_Global _))) _) _ =>
      apply runX_exp_global; simpl_lookup; first [reflexivity | eassumption]
  | |- eutt eq (runX _ (denote_exp' _ (OP_IBinop _ (DTYPE_Base (DTYPE_I 64)) _ _)) _) _ =>
      eapply runX_exp_ibinop; [run_exp | run_exp | eval_op]
  | |- eutt eq (runX _ (denote_exp' _ (OP_IBinop _ (DTYPE_Base (DTYPE_I 8)) _ _)) _) _ =>
      eapply runX_exp_ibinop_t; [run_exp | run_exp | eval_op8]
  | |- eutt eq (runX _ (denote_exp' _ (OP_IBinop _ (DTYPE_Base (DTYPE_I 1)) _ _)) _) _ =>
      eapply runX_exp_ibinop_t; [run_exp | run_exp | eval_op1]
  | |- eutt eq (runX _ (denote_exp' _ (OP_ICmp _ _ _ _ _)) _) _ => eapply runX_exp_icmp; [run_exp | run_exp | eval_op]
  | |- eutt eq (runX _ (denote_exp' _ (OP_Select _ _ _)) _) _ => eapply runX_exp_select; [run_exp | run_exp | run_exp]
  | |- eutt eq (runX _ (denote_exp' _ (OP_GetElementPtr (DTYPE_Base (DTYPE_I 8)) _ _)) _) _ => eapply runX_exp_gep; [run_exp | run_exp | bounds]
  | |- eutt eq (runX _ (denote_exp' _ (OP_GetElementPtr (DTYPE_Base (DTYPE_I 32)) _ _)) _) _ => eapply runX_exp_gep32; [run_exp | run_exp | bounds]
  | |- eutt eq (runX _ (denote_exp' _ (OP_GetElementPtr (DTYPE_Base (DTYPE_I 64)) _ _)) _) _ => eapply runX_exp_gep64; [run_exp | run_exp | bounds]
  | |- eutt eq (runX _ (denote_exp' _ (OP_Conversion (CONV_Pure (Zext _)) (DTYPE_Base (DTYPE_I 1)) _ _)) _) _ =>
      eapply runX_exp_zext1; run_exp
  | |- eutt eq (runX _ (denote_exp' _ (OP_Conversion (CONV_Pure (Zext _)) (DTYPE_Base (DTYPE_I 32)) _ _)) _) _ =>
      eapply runX_exp_zext32; [run_exp | first [val32_bounds | bounds]]
  | |- eutt eq (runX _ (denote_exp' _ (OP_Conversion (CONV_Pure (Zext _)) _ _ _)) _) _ =>
      eapply runX_exp_zext8k; [run_exp | first [byte_bounds | bounds]]
  | |- eutt eq (runX _ (denote_exp' _ (OP_Conversion (CONV_Pure (Trunc _ _)) _ _ _)) _) _ =>
      eapply runX_exp_trunc32; [run_exp | bounds]
  end.

Ltac run_instr ::=
  lazymatch goal with
  | |- eutt eq (runX _ (denote_instr (_, INSTR_Op _, _) _) _) _ => eapply runX_instr_op; run_exp
  | |- eutt eq (runX _ (denote_instr (_, INSTR_Call _ _ _ _, _) _) _) _ =>
      eapply runX_instr_call_n; [reflexivity | run_args | simpl_lookup; eassumption | eassumption | run_callee]
  | |- eutt eq (runX _ (denote_instr (_, INSTR_Load (DTYPE_Base (DTYPE_I 8)) _ _, _) _) _) _ =>
      eapply runX_instr_load8; [run_exp | mem_fact]
  | |- eutt eq (runX _ (denote_instr (_, INSTR_Load (DTYPE_Base (DTYPE_I 32)) _ _, _) _) _) _ =>
      eapply runX_instr_load32; [run_exp | mem_fact32 | mem_fact32 | mem_fact32 | mem_fact32
                                 | byte_bounds | byte_bounds | byte_bounds | byte_bounds]
  | |- eutt eq (runX _ (denote_instr (_, INSTR_Load (DTYPE_Base (DTYPE_I 64)) _ _, _) _) _) _ =>
      first [ eapply runX_instr_load64_val;
              [run_exp | mem_fact64 | mem_fact64 | mem_fact64 | mem_fact64 | mem_fact64 | mem_fact64 | mem_fact64 | mem_fact64 | val_bounds]
            | eapply runX_instr_load64;
              [run_exp | mem_fact64 | mem_fact64 | mem_fact64 | mem_fact64 | mem_fact64 | mem_fact64 | mem_fact64 | mem_fact64
               | byte_bounds | byte_bounds | byte_bounds | byte_bounds | byte_bounds | byte_bounds | byte_bounds | byte_bounds] ]
  | |- eutt eq (runX _ (denote_instr (_, INSTR_Store (DTYPE_Base (DTYPE_I 8), _) _ _, _) _) _) _ =>
      eapply runX_instr_store8; [run_exp | run_exp | mem_fact]
  | |- eutt eq (runX _ (denote_instr (_, INSTR_Store (DTYPE_Base (DTYPE_I 32), _) _ _, _) _) _) _ =>
      eapply runX_instr_store32; [run_exp | run_exp | bounds | mem_fact32 | mem_fact32 | mem_fact32 | mem_fact32]
  | |- eutt eq (runX _ (denote_instr (_, INSTR_Store (DTYPE_Base (DTYPE_I 64), _) _ _, _) _) _) _ =>
      eapply runX_instr_store64;
      [run_exp | run_exp | bounds | mem_fact64 | mem_fact64 | mem_fact64 | mem_fact64 | mem_fact64 | mem_fact64 | mem_fact64 | mem_fact64]
  | |- eutt eq (runX _ (denote_instr (IId ?x, INSTR_Alloca _ _, _) _) _) _ =>
      match goal with H : eutt eq (runX _ (denote_instr (IId x, INSTR_Alloca _ _, _) _) _) _ |- _ => exact H end
  end.

Transparent Integers.repr Integers.unsigned Integers.signed Integers.mul Integers.add Integers.eq Integers.ltu
  Integers.zero Integers.one Integers.modu Integers.shru Integers.sub Integers.divu.
