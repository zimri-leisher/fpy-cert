(** Symbolic reasoning about memory in Vellvm's reference interpreter
    ([Implementations.Memory], the byte-map model with provenance), for
    programs that allocate a byte array with [alloca i8, i64 %n] and access
    it with [getelementptr i8], [load i8] and [store i8].

    Memory is a map from addresses to bytes tagged with an allocation id;
    a pointer is an address and a provenance; accesses are allowed when the
    provenance covers the id. A fresh allocation of [L] bytes gets a fresh
    id [q] (the bumped provenance counter) and the pointer provenance
    [Some [q]].

    The lemmas come in three layers: the memory handler ([mem_*]), the
    pure evaluators ([gep8], [zext8]), and [runX]-level lemmas for the
    instructions and expressions, plugged into the tactics of [VellvmRun]. *)

From Stdlib Require Import ZArith NArith String List Lia Bool Morphisms.
From ExtLib Require Import Structures.Maps Structures.Monads.
From ITree Require Import ITree ITreeFacts Events.StateFacts.
From Vellvm Require Import Syntax Utils Params Semantics Interfaces.Memory ParamsV IPtrInfinite.
From Vellvm Require Import Implementations.Memory Semantics.Libraries.
From FpyCert Require Import LLVMBuilder VellvmRun.
Import ListNotations ITreeNotations.
Open Scope string_scope. Open Scope itree_scope. Open Scope Z_scope.
Unset Implicit Arguments.

Notation "t1 ≈ t2" := (eutt eq t1 t2) (at level 70, only parsing).

#[local] Instance Pa : Params := @ParamsV IPZ IPZTheory.

Opaque Integers.repr Integers.unsigned Integers.signed Integers.mul Integers.add Integers.eq Integers.ltu
  Integers.zero Integers.one.

(** * Pointers, provenance, bytes *)

(** The pointer to cell [i] of the array allocated with id [q] at [addr]. *)
Definition cell (addr : Z) (q : N) (i : Z) : dvalue := DVALUE_Base (DVALUE_Pointer (addr + i, Some [q])).

(** An [i8] value. *)
Definition dv8 (z : Z) : dvalue := DVALUE_Base (DVALUE_I 8 (Integers.repr z)).

Lemma access_own : forall q : N, access_allowed (allocation_id_to_prov (Some q)) (Some q) = true.
Proof. intros. cbn. rewrite N.eqb_refl. reflexivity. Qed.

(** How an [i8] is serialized: as itself. *)
Lemma byte_of_i8 : forall v : @Integers.bit_int 8,
  Integers.repr (Integers.unsigned (Integers.modu (Integers.shru v (Integers.repr 0)) (Integers.repr 256))) = v.
Proof.
  intros. replace (@Integers.repr 8 0) with (@Integers.zero 8) by reflexivity.
  rewrite Integers.shru_zero. unfold Integers.modu.
  replace (Integers.unsigned (@Integers.repr 8 256)) with 0 by (vm_compute; reflexivity).
  rewrite Zmod_0_r, Integers.repr_unsigned, Integers.repr_unsigned. reflexivity.
Qed.
Opaque Integers.modu Integers.shru.

Lemma unsigned_repr8 : forall z, 0 <= z < 256 -> Integers.unsigned (@Integers.repr 8 z) = z.
Proof. intros. apply Integers.unsigned_repr. unfold Integers.max_unsigned. replace (@Integers.modulus 8) with 256 by (vm_compute; reflexivity). lia. Qed.

Lemma signed_repr64 : forall z, 0 <= z < two63 -> Integers.signed (@Integers.repr 64 z) = z.
Proof.
  intros. apply Integers.signed_repr.
  replace (@Integers.min_signed 64) with (- two63) by (vm_compute; reflexivity).
  replace (@Integers.max_signed 64) with (two63 - 1) by (vm_compute; reflexivity). lia.
Qed.

(** Sizes of the types involved, as [vm_compute] sees them. *)
Lemma store_size_i8 : store_size_dtyp (DTYPE_I 8) = 1%N.
Proof. vm_compute. reflexivity. Qed.
Lemma alloc_size_b8 : alloc_size_dtyp (DTYPE_B 8) = 1%N.
Proof. vm_compute. reflexivity. Qed.
Lemma dtyp_eqb_i8_void : dtyp_eqb (DTYPE_I 8) DTYPE_Void = false.
Proof. vm_compute. reflexivity. Qed.

(** * The memory handler *)

(** Popping a frame frees its allocations. *)
Lemma mem_pop_frame : forall mem fs f heap p,
  (handle_memory memM_interp MemPop (mkState (mkMemoryStack mem (Snoc fs f) heap) p) : itree MCFGEbot _)
    ≈ Ret (mkState (mkMemoryStack (free_frame_memory f mem) fs heap) p, tt).
Proof. intros. unfold handle_memory. cbn. reflexivity. Qed.

(** Storing an [i8] at an allocated address with the right provenance. *)
Lemma mem_store8 : forall mem fs heap p (a : Z) (q : N) (v : @Integers.bit_int 8) b0,
  IM.find a mem = Some (b0, Some q) ->
  (handle_memory memM_interp (Store (DTYPE_I 8) (DVALUE_Base (DVALUE_Pointer (a, Some [q]))) (DVALUE_Base (DVALUE_I 8 v)))
     (mkState (mkMemoryStack mem fs heap) p) : itree MCFGEbot _)
    ≈ Ret (mkState (mkMemoryStack (IM.add a (BYTE_I v, Some q) mem) fs heap) p, tt).
Proof.
  intros. unfold handle_memory. cbn. unfold read_byte_raw_mem. replace (a + 0) with a by lia.
  change (@IM.find byte) with (@IM.find (memory_byte * option N)). rewrite H. cbn.
  rewrite N.eqb_refl. cbn. rewrite byte_of_i8. reflexivity.
Qed.

(** * The pure evaluators *)

Lemma gep8 : forall (a : Z) (pr : prov) i, 0 <= i < two63 ->
  eval_gep (DTYPE_I 8) (DVALUE_Base (DVALUE_Pointer (a, pr))) [DVALUE_Base (DVALUE_I 64 (Integers.repr i))]
  = raise_ret (DVALUE_Base (DVALUE_Pointer (a + i, pr))).
Proof.
  intros. cbn. rewrite signed_repr64 by exact H. destruct i; reflexivity.
Qed.

Lemma zext8 : forall x : @Integers.bit_int 8,
  convert_pure (Zext false) (DTYPE_I 8) (DVALUE_Base (DVALUE_I 8 x)) (DTYPE_I 64)
  = raise_ret (DVALUE_Base (DVALUE_I 64 (Integers.repr (Integers.unsigned x)))).
Proof. reflexivity. Qed.

(** * Allocation *)

(** The bytes and the memory of a fresh allocation of [L] bytes with id [q] at
    address [addr], exactly as the handler builds them. *)
Definition alloc_bytes (L : N) (q : N) : list byte :=
  map_acc (fun b => (b, Some q)) (concat_acc (repeatN L [poison_memory_byte])).
Definition alloc_mem (L : N) (addr : Z) (q : N) (mem : memory) : memory :=
  add_all_index_acc (alloc_bytes L q) addr mem.

Lemma repeatN_eq : forall {X} (n : N) (x : X), repeatN n x = repeat x (N.to_nat n).
Proof.
  intros X n x. unfold repeatN. induction n using N.peano_ind.
  - reflexivity.
  - rewrite N.recursion_succ by (repeat intro; subst; reflexivity). rewrite N2Nat.inj_succ. cbn. f_equal. exact IHn.
Qed.

Lemma concat_repeat_single : forall {X} (x : X) n, concat (repeat [x] n) = repeat x n.
Proof. intros. induction n; cbn; [reflexivity | f_equal; exact IHn]. Qed.

Lemma alloc_bytes_eq : forall L q, alloc_bytes L q = repeat (poison_memory_byte, Some q) (N.to_nat L).
Proof.
  intros. unfold alloc_bytes. rewrite map_acc_eq, concat_acc_eq, repeatN_eq, concat_repeat_single, map_repeat.
  reflexivity.
Qed.

Lemma length_h_eq : forall {X} (l : list X) acc, N.length_h l acc = (N.of_nat (length l) + acc)%N.
Proof. intros X l. induction l; intros; cbn [N.length_h length]; [lia | rewrite IHl, Nat2N.inj_succ; lia]. Qed.

Lemma N_length_eq : forall {X} (l : list X), N.length l = N.of_nat (length l).
Proof. intros. unfold N.length. rewrite length_h_eq. lia. Qed.

Lemma list_nth_z_repeat : forall {X} (x : X) n i, 0 <= i < Z.of_nat n -> list_nth_z (repeat x n) i = Some x.
Proof.
  intros X x n. induction n; intros i Hi; cbn in *; [lia |].
  destruct (zeq i 0); [reflexivity |]. apply IHn. lia.
Qed.

(** What a load at cell [i] of a fresh allocation finds: a poison byte with
    the allocation's id. *)
Lemma find_alloc_mem : forall L addr q mem i, 0 <= i < Z.of_N L ->
  IM.find (addr + i) (alloc_mem L addr q mem) = Some (poison_memory_byte, Some q).
Proof.
  intros. unfold alloc_mem.
  pose proof (add_all_index_acc_eq (alloc_bytes L q) addr mem (addr + i)) as E. unfold lookup in E. rewrite E.
  change (@IM.find byte) with (@IM.find (memory_byte * option N)).
  rewrite alloc_bytes_eq.
  apply (lookup_add_all_index_in (repeat (poison_memory_byte, Some q) (N.to_nat L)) (addr + i) addr).
  - rewrite Zlength_correct, repeat_length. lia.
  - replace (addr + i - addr) with i by lia. apply list_nth_z_repeat. lia.
Qed.

Lemma find_alloc_mem_other : forall L addr q mem k, (k < addr \/ addr + Z.of_N L <= k) ->
  IM.find k (alloc_mem L addr q mem) = IM.find k mem.
Proof.
  intros. unfold alloc_mem.
  pose proof (add_all_index_acc_eq (alloc_bytes L q) addr mem k) as E. unfold lookup in E. rewrite E.
  rewrite alloc_bytes_eq.
  apply (lookup_add_all_index_out (repeat (poison_memory_byte, Some q) (N.to_nat L)) k addr).
  rewrite Zlength_correct, repeat_length. lia.
Qed.

(** Pieces of the allocation handler on symbolic sizes. *)
Lemma len_alloc : forall L, N.length (concat_acc (repeatN L [poison_memory_byte])) = L.
Proof. intros. rewrite N_length_eq, concat_acc_eq, repeatN_eq, concat_repeat_single, repeat_length. lia. Qed.

Lemma map_monad_EOU_ret : forall {A B} (g : A -> B) (l : list A),
  map_monad (fun a => raise_ret (g a)) l = raise_ret (map g l).
Proof. intros. induction l; cbn; [reflexivity | rewrite IHl; reflexivity]. Qed.

Lemma map_monad_acc_EOU_ret : forall {A B} (f : A -> EOU B) (g : A -> B) (l : list A),
  (forall a, f a = raise_ret (g a)) -> map_monad_acc f l = raise_ret (map g l).
Proof.
  intros A B f g l Hf. unfold map_monad_acc.
  enough (forall acc, (fix loop (acc : list B) (l : list A) : EOU (list B) :=
                         match l with
                         | [] => @ret EOU _ _ (rev_append acc [])
                         | a :: l' => @bind EOU _ _ _ (f a) (fun b => loop (b :: acc) l')
                         end) acc l
                      = raise_ret (rev_append acc (map g l))) as E by apply E.
  induction l; intros acc; cbn.
  - reflexivity.
  - rewrite Hf. cbn. rewrite IHl. reflexivity.
Qed.

Lemma ptr_byte_offset_eq : forall (addr : Z) (pr : prov) (ix : Z),
  ptr_byte_offset (addr, pr) ix = raise_ret (addr + ix, pr).
Proof. intros. unfold ptr_byte_offset. rewrite alloc_size_b8. cbn; repeat f_equal; destruct ix; reflexivity. Qed.

Lemma fold_add_to_frame_Snoc : forall ks m s f h,
  fold_left (fun ms k => add_to_frame ms k) ks (mkMemoryStack m (Snoc s f) h)
  = mkMemoryStack m (Snoc s (rev ks ++ f)%list) h.
Proof.
  intros ks. induction ks as [| k ks IH]; intros; cbn [fold_left]; [reflexivity |].
  cbn [add_to_frame]. rewrite IH. cbn [rev]. rewrite <- app_assoc. reflexivity.
Qed.

Lemma add_all_to_frame_Snoc : forall ks m s f h,
  add_all_to_frame ks (mkMemoryStack m (Snoc s f) h) = mkMemoryStack m (Snoc s (rev ks ++ f)%list) h.
Proof. intros. apply fold_add_to_frame_Snoc. Qed.

(** Allocating [L] bytes: a fresh id, poison contents, pointers registered in
    the current frame (in some order). *)
Lemma mem_alloca8 : forall (L : N) mem fs f heap p,
  exists f',
  (handle_memory memM_interp (Alloca (DTYPE_I 8) L None) (mkState (mkMemoryStack mem (Snoc fs f) heap) p) : itree MCFGEbot _)
    ≈ Ret (mkState (mkMemoryStack (alloc_mem L (next_key_with_alignment mem 8) (N.succ p) mem) (Snoc fs f') heap) (N.succ p),
           DVALUE_Base (DVALUE_Pointer (next_key_with_alignment mem 8, Some [N.succ p]))).
Proof.
  intros. eexists. unfold handle_memory, handle_memoryM. cbv beta iota.
  unfold allocate_dtyp. rewrite dtyp_eqb_i8_void. cbv iota.
  unfold allocate_bytes. cbn [generate_poison_bytes generate_num_poison_bytes generate_num_poison_bytes_h store_size_dtyp].
  cbn. setoid_rewrite Eqit.bind_ret_l. cbn.
  unfold intptr_seq. rewrite seq_map_monad_acc_eq, N_to_nat_safe_eq, len_alloc.
  rewrite (map_monad_EOU_ret (fun n => Z.of_N n)).
  rewrite (map_monad_acc_EOU_ret _ (fun ix => (next_key_with_alignment mem 8 + ix, Some [N.succ p])))
    by (intros; apply ptr_byte_offset_eq).
  cbn. rewrite add_all_to_frame_Snoc. reflexivity.
Qed.

(** * Loads *)

(** Deserializing one byte as an [i8]. *)
Lemma bytes_i8 : forall v : @Integers.bit_int 8,
  memory_bytes_to_dvalue [BYTE_I v] (DTYPE_I 8) = raise_ret (DVALUE_Base (DVALUE_I 8 v)).
Proof. intros. cbn. rewrite Z.add_0_r, Integers.repr_unsigned. reflexivity. Qed.

(* [cbn] does not terminate on the class-method projection [read_byte];
   rewrite it to the implementation first. *)
Lemma read_byte_eq : @read_byte Pa MemoryModelPrimitivesV = @Read_byte Pa.
Proof. reflexivity. Qed.

(** Loading an [i8] from an allocated address with the right provenance.

    Stated in a section: with the variables as binders of the lemma, the
    elaborator exhausts memory on the first [intro] (it unifies the memory
    state type in its projection and record spellings under [itree]). The
    same applies to [runX_instr_load8] below. *)
Section LoadSec.
  Variables (mem : memory) (fs : Framestack) (heap : Heap) (p : provenance) (a : Z) (q : N) (v : @Integers.bit_int 8).
  Hypothesis H : IM.find a mem = Some (BYTE_I v, Some q).
  Lemma mem_load8 :
    (handle_memory memM_interp (Load (DTYPE_I 8) (DVALUE_Base (DVALUE_Pointer (a, Some [q])))) (mkState (mkMemoryStack mem fs heap) p)
       : itree MCFGEbot _)
      ≈ Ret (mkState (mkMemoryStack mem fs heap) p, DVALUE_Base (DVALUE_I 8 v)).
  Proof.
    unfold handle_memory, handle_memoryM, read_dvalue, read_bytes.
    change (store_size_dtyp (DTYPE_I 8)) with 1%N. change (@read_byte _ _) with (@Read_byte Pa).
    cbn -[memory_bytes_to_dvalue]. unfold read_byte_raw_mem. replace (a + 0) with a by lia.
    first [rewrite H | (change (@IM.find byte) with (@IM.find (memory_byte * option N)); rewrite H)].
    cbn -[memory_bytes_to_dvalue]. rewrite N.eqb_refl. cbn -[memory_bytes_to_dvalue]. rewrite bytes_i8. cbn. reflexivity.
  Qed.
End LoadSec.

(** * Expressions: [getelementptr] and [zext] *)

Section RunnerMem.
  Variable fundefs : IntMap function_denotation.

  (** [getelementptr i8, ptr %a, i64 %i] on the array pointer: cell [i]. *)
  Lemma runX_exp_gep : forall ea ei addr q i s,
    runX fundefs (denote_exp' (Some (DTYPE_Pointer : dtyp)) ea) s ≈ Ret (s, inr (DVALUE_Base (DVALUE_Pointer (addr, Some [q])))) ->
    runX fundefs (denote_exp' (Some LL.i64) ei) s ≈ Ret (s, inr (dvZ i)) ->
    0 <= i < two63 ->
    runX fundefs (denote_exp' None (OP_GetElementPtr (DTYPE_I 8 : dtyp) (DTYPE_Pointer : dtyp, ea) [(LL.i64, ei)])) s
      ≈ Ret (s, inr (cell addr q i)).
  Proof.
    intros. unfold denote_exp' in *. cbn. unfold withCall in *.
    rewrite translate_bind. eapply runX_bind_step; [exact H |].
    rewrite translate_bind. eapply runX_bind_step.
    { rewrite translate_bind. eapply runX_bind_step; [exact H0 |].
      try (rewrite translate_bind; eapply runX_bind_step; [rewrite translate_ret; apply runX_ret |]).
      cbn. rewrite translate_ret. apply runX_ret. }
    unfold dvZ. rewrite gep8 by exact H1. cbn. rewrite translate_ret. apply runX_ret.
  Qed.

  (** [zext i8 %b to i64]. *)
  Lemma runX_exp_zext8 : forall e x s,
    runX fundefs (denote_exp' (Some (DTYPE_I 8 : dtyp)) e) s ≈ Ret (s, inr (DVALUE_Base (DVALUE_I 8 x))) ->
    runX fundefs (denote_exp' None (OP_Conversion (CONV_Pure (Zext false)) (DTYPE_I 8 : dtyp) e LL.i64)) s
      ≈ Ret (s, inr (dvZ (Integers.unsigned x))).
  Proof.
    intros. unfold denote_exp' in *. cbn. unfold withCall in *.
    rewrite translate_bind. eapply runX_bind_step; [exact H |].
    cbn. rewrite translate_ret. apply runX_ret.
  Qed.

  (** Integer literals at any width. *)
  Lemma runX_exp_lit_sz : forall sz z s,
    runX fundefs (denote_exp' (Some (DTYPE_I sz : dtyp)) (P.lit z)) s ≈ Ret (s, inr (DVALUE_Base (DVALUE_I sz (Integers.repr z)))).
  Proof.
    intros. unfold denote_exp', P.lit, LL.int_lit. cbn. rewrite DecimalZ.of_to.
    unfold withCall. rewrite translate_ret. apply runX_ret.
  Qed.

  (** [zext] of a small constant. *)
  Lemma runX_exp_zext8k : forall e k s,
    runX fundefs (denote_exp' (Some (DTYPE_I 8 : dtyp)) e) s ≈ Ret (s, inr (dv8 k)) ->
    0 <= k < 256 ->
    runX fundefs (denote_exp' None (OP_Conversion (CONV_Pure (Zext false)) (DTYPE_I 8 : dtyp) e LL.i64)) s
      ≈ Ret (s, inr (dvZ k)).
  Proof. intros. unfold dvZ. rewrite <- (unsigned_repr8 k H0). apply runX_exp_zext8. exact H. Qed.

  (** [store i8 %v, ptr %p] at an allocated cell with the right provenance. *)
  Lemma runX_instr_store8 : forall k ev ep anns md va addr q z b0 mem fs heap p env exc loc stk g,
    runX fundefs (denote_exp' (Some (DTYPE_I 8 : dtyp)) ev) (ST (mkState (mkMemoryStack mem fs heap) p) env exc loc stk g)
      ≈ Ret (ST (mkState (mkMemoryStack mem fs heap) p) env exc loc stk g, inr (dv8 z)) ->
    runX fundefs (denote_exp' (Some (DTYPE_Pointer : dtyp)) ep) (ST (mkState (mkMemoryStack mem fs heap) p) env exc loc stk g)
      ≈ Ret (ST (mkState (mkMemoryStack mem fs heap) p) env exc loc stk g, inr (DVALUE_Base (DVALUE_Pointer (addr, Some [q])))) ->
    IM.find addr mem = Some (b0, Some q) ->
    runX fundefs (denote_instr (IVoid k, INSTR_Store (DTYPE_I 8 : dtyp, ev) (DTYPE_Pointer : dtyp, ep) anns, md) va)
      (ST (mkState (mkMemoryStack mem fs heap) p) env exc loc stk g)
      ≈ Ret (ST (mkState (mkMemoryStack (IM.add addr (BYTE_I (Integers.repr z), Some q) mem) fs heap) p) env exc loc stk g, inr tt).
  Proof.
    intros. cbn. eapply runX_bind_step; [exact H |]. eapply runX_bind_step; [exact H0 |]. cbn.
    eapply runX_bind_step.
    { apply runX_of_runF_trigger; [reflexivity |]. eapply runF_mem_eq. eapply mem_store8. exact H1. }
    apply runX_ret.
  Qed.

  (** [%a = alloca i8, i64 %L]. *)
  Lemma runX_instr_alloca8 : forall x eL md va L mem fs f heap p env exc loc stk g,
    runX fundefs (denote_exp' (Some LL.i64) eL) (ST (mkState (mkMemoryStack mem (Snoc fs f) heap) p) env exc loc stk g)
      ≈ Ret (ST (mkState (mkMemoryStack mem (Snoc fs f) heap) p) env exc loc stk g, inr (dvZ L)) ->
    0 <= L < two64 ->
    exists f',
    runX fundefs (denote_instr (IId x, INSTR_Alloca (DTYPE_I 8 : dtyp) [ANN_num_elements (LL.i64, eL)], md) va)
      (ST (mkState (mkMemoryStack mem (Snoc fs f) heap) p) env exc loc stk g)
      ≈ Ret (ST (mkState (mkMemoryStack (alloc_mem (Z.to_N L) (next_key_with_alignment mem 8) (N.succ p) mem) (Snoc fs f') heap) (N.succ p))
                (Maps.add x (DVALUE_Base (DVALUE_Pointer (next_key_with_alignment mem 8, Some [N.succ p]))) env) exc loc stk g, inr tt).
  Proof.
    intros. destruct (mem_alloca8 (Z.to_N L) mem fs f heap p) as [f' Ha]. exists f'.
    cbn. eapply runX_bind_step.
    { eapply runX_bind_step; [exact H |]. eapply runX_bind_step; [apply runX_ret |]. cbn.
      eapply runX_bind_step.
      { apply runX_of_runF_trigger; [reflexivity |]. eapply runF_mem_eq.
        rewrite unsigned_repr64 by (unfold two64 in *; lia). exact Ha. }
      apply runX_lwrite. }
    apply runX_ret.
  Qed.

  (** ** Calls with any number of arguments *)

  Lemma runX_map_monad_exps : forall (args : list (dtyp * llexpr)) vs s,
    Forall2 (fun '(t, e) v => runX fundefs (denote_exp' (Some t) e) s ≈ Ret (s, inr v)) args vs ->
    runX fundefs (map_monad (fun '(t, op) => denote_exp' (Some t) op) args) s ≈ Ret (s, inr vs).
  Proof.
    intros args vs s H. induction H as [| [t e] v args vs He _ IH].
    - apply runX_ret.
    - change (map_monad (fun '(t, op) => denote_exp' (Some t) op) ((t, e) :: args))
        with (ITree.bind (denote_exp' (Some t) e)
                (fun v => ITree.bind (map_monad (fun '(t, op) => denote_exp' (Some t) op) args) (fun vs => Ret (v :: vs)))).
      eapply runX_bind_step; [exact He |]. eapply runX_bind_step; [exact IH |]. apply runX_ret.
  Qed.

  (** [x = call i64 @f(args)] to an internal function that returns normally
      ([VellvmRun.runX_instr_call] is the one-argument case). *)
  Lemma runX_instr_call_n : forall x f args vs vap md fv fden S m' env' exc' loc' stk' g' rv,
    intrinsic_exp (P.global f) = None ->
    Forall2 (fun '(t, e) v => runX fundefs (denote_exp' (Some t) e) S ≈ Ret (S, inr v)) (map fst args) vs ->
    Maps.lookup (Name f) (snd (snd S)) = Some fv ->
    lookup_defn fv fundefs = Some fden ->
    runF fundefs (fden vs) S ≈ Ret ((m', ((Build_stack_frame env' exc' loc', stk'), g')), inr rv) ->
    runX fundefs (denote_instr (IId x, INSTR_Call (LL.i64, P.global f) args [] [], md) vap) S
      ≈ Ret ((m', ((Build_stack_frame (Maps.add x rv env') exc' loc', stk'), g')), inr tt).
  Proof.
    intros * Hintr Hargs Hg Hdef Hcall. destruct S as [m [ls g]]. cbn in Hg.
    Opaque intrinsic_exp. cbn. cbn in Hintr. rewrite Hintr. Transparent intrinsic_exp.
    eapply runX_bind_step; [apply runX_map_monad_exps; exact Hargs |].
    eapply runX_bind_step.
    { eapply runX_bind_step; [apply runX_exp_global; exact Hg |].
      eapply runX_bind_step.
      { rewrite (runX_call _ _ _ _ _ _ Hdef). rewrite Hcall, Eqit.bind_ret_l. reflexivity. }
      cbn. apply runX_ret. }
    apply runX_lwrite.
  Qed.
End RunnerMem.

(** [x = load i8, ptr %p] (see [mem_load8] for the section). *)
Section Load.
  Variable fundefs : IntMap function_denotation.
  Variables (x : raw_id) (ep : llexpr) (anns : list (annotation dtyp)) (md : list (metadata dtyp)) (va : option ptr)
            (addr : Z) (q : N) (v : @Integers.bit_int 8) (mem : memory) (fs : Framestack) (heap : Heap) (p : provenance)
            (env : local_env) (exc : option dvalue) (loc : option string) (stk : stack) (g : global_env).
  Hypothesis Hp : runX fundefs (denote_exp' (Some (DTYPE_Pointer : dtyp)) ep) (ST (mkState (mkMemoryStack mem fs heap) p) env exc loc stk g)
      ≈ Ret (ST (mkState (mkMemoryStack mem fs heap) p) env exc loc stk g, inr (DVALUE_Base (DVALUE_Pointer (addr, Some [q])))).
  Hypothesis Hm : IM.find addr mem = Some (BYTE_I v, Some q).
  Lemma runX_instr_load8 :
    runX fundefs (denote_instr (IId x, INSTR_Load (DTYPE_I 8 : dtyp) (DTYPE_Pointer : dtyp, ep) anns, md) va)
      (ST (mkState (mkMemoryStack mem fs heap) p) env exc loc stk g)
      ≈ Ret (ST (mkState (mkMemoryStack mem fs heap) p) (Maps.add x (DVALUE_Base (DVALUE_I 8 v)) env) exc loc stk g, inr tt).
  Proof.
    cbn. eapply runX_bind_step; [exact Hp |].
    eapply runX_bind_step.
    { apply runX_of_runF_trigger; [reflexivity |]. eapply runF_mem_eq. eapply mem_load8. exact Hm. }
    apply runX_lwrite.
  Qed.
End Load.

(** * A whole function call whose body allocates

    Like [runF_function_ex] ([VellvmRun]), but the body may allocate: it
    ends with memory [mem'] and the frame [Snoc fs f'] of its allocations,
    which the pop frees. *)
Lemma runF_function_mem : forall fundefs df args bs mem fs heap p fr stk g v,
  combine_lists_varargs (df_args df) args = raise_ret (bs, []) ->
  (forall varg, exists mem' f' env' p',
    runX fundefs (denote_cfg_map (ocfg_map (blks (df_instrs df))) (df_instrs df) (Some varg))
      (ST (mkState (mkMemoryStack mem (Snoc fs []) heap) (next_provenance p))
          (fold_right (fun '(x, dv) => Maps.add x dv) Maps.empty bs) None (Some "") (fr :: stk) g)
      ≈ Ret (ST (mkState (mkMemoryStack mem' (Snoc fs f') heap) p') env' None (Some "") (fr :: stk) g, inr v)) ->
  exists mem'' p',
    runF fundefs (denote_function df args) (mkState (mkMemoryStack mem fs heap) p, ((fr, stk), g))
      ≈ Ret ((mkState (mkMemoryStack mem'' fs heap) p', ((fr, stk), g)), inr v).
Proof.
  intros * Hargs Hbody.
  destruct (alloca_empty_eq mem (Snoc fs []) heap p) as [varg Halloca].
  destruct (Hbody varg) as [mem' [f' [env' [p' Hb]]]].
  exists (free_frame_memory f' mem'), p'.
  unfold denote_function, push_call_frame, pop_call_frame. rewrite Hargs.
  Opaque denote_cfg_map ocfg_map run_exc runF runX.
  cbn.
  Transparent denote_cfg_map ocfg_map run_exc runF runX.
  eapply runF_bind_step.
  { eapply runF_bind_step; [apply runF_ret |]. cbn.
    eapply runF_bind_step; [apply runF_ret |]. cbn.
    eapply runF_bind_step; [eapply runF_mem_eq; apply mem_push_eq |].
    eapply runF_bind_step; [apply runF_stack_push |].
    eapply runF_bind_step; [eapply runF_mem_eq; exact Halloca |].
    eapply runF_bind_step; [eapply runF_mem_eq; apply store_empty_eq |].
    apply runF_ret. }
  eapply runF_bind_step; [exact Hb |].
  eapply runF_bind_step.
  { eapply runF_bind_step; [apply runF_stack_pop |]. eapply runF_mem_eq. apply mem_pop_frame. }
  apply runF_ret.
Qed.

(** A call whose body only stores (no allocations): the caller learns a
    property [P] of the memory the callee leaves. *)
Lemma runF_function_prop : forall fundefs df args bs mem fs heap p fr stk g v (P : memory -> Prop),
  combine_lists_varargs (df_args df) args = raise_ret (bs, []) ->
  (forall varg, exists mem' env' p',
    P mem' /\
    runX fundefs (denote_cfg_map (ocfg_map (blks (df_instrs df))) (df_instrs df) (Some varg))
      (ST (mkState (mkMemoryStack mem (Snoc fs []) heap) (next_provenance p))
          (fold_right (fun '(x, dv) => Maps.add x dv) Maps.empty bs) None (Some "") (fr :: stk) g)
      ≈ Ret (ST (mkState (mkMemoryStack mem' (Snoc fs []) heap) p') env' None (Some "") (fr :: stk) g, inr v)) ->
  exists mem' p',
    P mem' /\
    runF fundefs (denote_function df args) (mkState (mkMemoryStack mem fs heap) p, ((fr, stk), g))
      ≈ Ret ((mkState (mkMemoryStack mem' fs heap) p', ((fr, stk), g)), inr v).
Proof.
  intros * Hargs Hbody.
  destruct (alloca_empty_eq mem (Snoc fs []) heap p) as [varg Halloca].
  destruct (Hbody varg) as [mem' [env' [p' [HP Hb]]]].
  exists mem', p'. split; [exact HP |].
  unfold denote_function, push_call_frame, pop_call_frame. rewrite Hargs.
  Opaque denote_cfg_map ocfg_map run_exc runF runX.
  cbn.
  Transparent denote_cfg_map ocfg_map run_exc runF runX.
  eapply runF_bind_step.
  { eapply runF_bind_step; [apply runF_ret |]. cbn.
    eapply runF_bind_step; [apply runF_ret |]. cbn.
    eapply runF_bind_step; [eapply runF_mem_eq; apply mem_push_eq |].
    eapply runF_bind_step; [apply runF_stack_push |].
    eapply runF_bind_step; [eapply runF_mem_eq; exact Halloca |].
    eapply runF_bind_step; [eapply runF_mem_eq; apply store_empty_eq |].
    apply runF_ret. }
  eapply runF_bind_step; [exact Hb |].
  eapply runF_bind_step.
  { eapply runF_bind_step; [apply runF_stack_pop |]. eapply runF_mem_eq. apply mem_pop_eq. }
  apply runF_ret.
Qed.

(** * Tactics

    Memory-aware versions of [VellvmRun]'s [run_exp] and [run_instr]. Loads
    and stores need a fact about the memory ([IM.find addr mem = Some (...)]),
    which the program-specific proof supplies by redefining [mem_fact]
    ([Ltac mem_fact ::= ...]). An [alloca] is run beforehand with
    [runX_instr_alloca8] (its result is existential) and picked up from the
    context. *)

Ltac mem_fact := fail "mem_fact: provide the memory fact (redefine it with Ltac mem_fact ::= ...)".

Ltac run_exp ::=
  lazymatch goal with
  | |- eutt eq (runX _ (denote_exp' _ (EXP_Integer _)) _) _ => apply runX_exp_lit_sz
  | |- eutt eq (runX _ (denote_exp' _ (EXP_Ident (ID_Local _))) _) _ =>
      apply runX_exp_local; simpl_lookup; first [reflexivity | eassumption]
  | |- eutt eq (runX _ (denote_exp' _ (EXP_Ident (ID_Global _))) _) _ =>
      apply runX_exp_global; simpl_lookup; first [reflexivity | eassumption]
  | |- eutt eq (runX _ (denote_exp' _ (OP_IBinop _ _ _ _)) _) _ => eapply runX_exp_ibinop; [run_exp | run_exp | eval_op]
  | |- eutt eq (runX _ (denote_exp' _ (OP_ICmp _ _ _ _ _)) _) _ => eapply runX_exp_icmp; [run_exp | run_exp | eval_op]
  | |- eutt eq (runX _ (denote_exp' _ (OP_GetElementPtr _ _ _)) _) _ => eapply runX_exp_gep; [run_exp | run_exp | bounds]
  | |- eutt eq (runX _ (denote_exp' _ (OP_Conversion _ _ _ _)) _) _ => eapply runX_exp_zext8k; [run_exp | bounds]
  end.

(** The arguments of a call, one [run_exp] each. *)
Ltac run_args := cbn [map fst]; repeat (eapply Forall2_cons; [cbv beta iota; run_exp |]); apply Forall2_nil.

Ltac run_instr ::=
  lazymatch goal with
  | |- eutt eq (runX _ (denote_instr (_, INSTR_Op _, _) _) _) _ => eapply runX_instr_op; run_exp
  | |- eutt eq (runX _ (denote_instr (_, INSTR_Call _ _ _ _, _) _) _) _ =>
      eapply runX_instr_call_n; [reflexivity | run_args | simpl_lookup; eassumption | eassumption | run_callee]
  | |- eutt eq (runX _ (denote_instr (_, INSTR_Load _ _ _, _) _) _) _ =>
      eapply runX_instr_load8; [run_exp | mem_fact]
  | |- eutt eq (runX _ (denote_instr (_, INSTR_Store _ _ _, _) _) _) _ =>
      eapply runX_instr_store8; [run_exp | run_exp | mem_fact]
  | |- eutt eq (runX _ (denote_instr (IId ?x, INSTR_Alloca _ _, _) _) _) _ =>
      match goal with H : eutt eq (runX _ (denote_instr (IId x, INSTR_Alloca _ _, _) _) _) _ |- _ => exact H end
  end.

(** * Fresh addresses

    The address of the next allocation, [next_key_with_alignment mem 8], is
    nonnegative and above every address of [mem]: a new array is disjoint
    from the existing ones. *)

Lemma next_key_nonneg : forall (mem : memory), 0 <= next_key_with_alignment mem 8.
Proof. intros. unfold next_key_with_alignment. destruct (IntMaps.IM_greatest_key mem); lia. Qed.

Lemma fresh_key : forall (mem : memory) k v, 0 <= k -> IM.find k mem = Some v -> k < next_key_with_alignment mem 8.
Proof.
  intros * Hk Hf.
  assert (Hin : IM.In k mem) by (apply IntMaps.IP.F.in_find_iff; rewrite Hf; discriminate).
  pose proof (IntMaps.next_key_correct mem k Hin) as Hnk.
  unfold IntMaps.next_key in Hnk. unfold next_key_with_alignment.
  destruct (IntMaps.IM_greatest_key mem) as [gk |]; [| lia].
  unfold Memory.pad_to. rewrite N2Z.inj_add, N2Z.inj_add, Z2N.id by lia.
  pose proof (N2Z.is_nonneg (Memory.pad_amount 8 (1 + Z.to_N gk))). replace (Z.of_N 1) with 1 by reflexivity. lia.
Qed.
