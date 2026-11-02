(** Symbolic execution of Vellvm programs through the reference interpreter.

    Nothing in this file is specific to a program. It provides:
    - [run]/[run_check]: a fuel-bounded stepper for itrees, and the reflection
      lemmas that turn a computed run into an [eutt] fact;
    - [runF]/[runX]: the whole interpretation stack applied to the denotation
      of a function body, with one lemma per syntactic construct
      (expressions, instructions, terminators, phi nodes, blocks, CFG steps,
      calls to internal functions);
    - [runF_function]: a call to a function, in terms of a run of its body;
    - [runM_*]: the top-level tree ([denote_vellvm]) once calls are resolved;
    - tactics ([run_block], [ocfg_jump], ...) that execute a basic block
      automatically. Loops are handled by induction in program-specific
      proofs; [NthPrimeProof] shows the pattern.

    Conventions: 64-bit integer values are written [dvZ z], 1-bit booleans
    [dvB c], and the fused interpreter state [ST mem env exc loc stk g]. *)

From Stdlib Require Import ZArith String List Lia Bool Morphisms.
From Stdlib Require Import Numbers.DecimalZ.
From ExtLib Require Import Structures.Maps Structures.Monads.
From ITree Require Import ITree ITreeFacts Events.StateFacts Interp.RecursionFacts.
From Paco Require Import paco.
From Vellvm Require Import Syntax Utils Params Semantics Interfaces.Memory ParamsV IPtrInfinite Theory.Equational.
From Vellvm Require Import Implementations.Memory Semantics.Libraries.
From FpyCert Require Import LLVMBuilder.
Import ListNotations ITreeNotations.
Open Scope string_scope. Open Scope itree_scope. Open Scope signature_scope.
Open Scope Z_scope.
Unset Implicit Arguments.

(* ITree declares [≈] both for [eutt eq] (in [type_scope]) and for [eq1] (in
   [monad_scope]); under an [exists] binder the latter would be picked. Make
   [eutt eq] the interpretation everywhere. *)
Notation "t1 ≈ t2" := (eutt eq t1 t2) (at level 70, only parsing).

#[local] Instance Pa : Params := @ParamsV IPZ IPZTheory.

(** * Values and states *)

Definition dvZ (z : Z) : dvalue := DVALUE_Base (DVALUE_I 64 (Integers.repr z)).
Definition dvB (c : bool) : dvalue := DVALUE_Base (if c then DVALUE_I 1 Integers.one else DVALUE_I 1 Integers.zero).

(** The fused interpreter state: memory; current frame (locals, exception
    handler, location); call stack; globals. *)
Notation ST mm env exc loc stk g := ((mm, ((Build_stack_frame env exc loc, stk), g)) : FusedS).

(** * Running an itree for a bounded number of steps *)

(* The event of a [Vis] node is deliberately not kept: storing it would make
   [Compute] normalize the whole memory model. *)
Inductive outcome (R : Type) : Type :=
| Done (r : R)
| OutOfFuel
| Event.
Arguments Done {R}.
Arguments OutOfFuel {R}.
Arguments Event {R}.

Fixpoint run {E R} (fuel : nat) (t : itree E R) : outcome R :=
  match fuel with
  | O => OutOfFuel
  | S fuel =>
    match observe t with
    | RetF r => Done r
    | TauF t => run fuel t
    | VisF _ _ _ => Event
    end
  end.

(** The interpreted tree of a program with an [i64 @main()] entry point, as
    Vellvm's [interpreter_gen] builds it. *)
Definition interp_prog (p : mcfg dtyp) :=
  interp_mcfg (denote_vellvm LL.i64 (Name "main") [] p)
    (initial_state, ((Build_stack_frame Maps.empty None None, []), Maps.empty)).

(** Builder helpers at [dtyp], used to restate the program's blocks. *)

Module P.

Definition global (x : string) : llexpr := EXP_Ident (ID_Global (Name x)).
Definition lbl (x : string) : block_id := Name x.
Definition var (x : string) : llexpr := LL.local (Name x).
Definition lit := LL.int_lit.

Definition mul (a b : llexpr) : llexpr := OP_IBinop (LLVMAst.Mul false false) LL.i64 a b.
Definition urem (a b : llexpr) : llexpr := OP_IBinop LLVMAst.URem LL.i64 a b.
(* [Eq] alone would resolve to the [comparison] constructor from Stdlib. *)
Definition icmp (c : LLVMAst.icmp) (a b : llexpr) : llexpr := OP_ICmp false c LL.i64 a b.

Definition set (x : string) (e : llexpr) := LL.assign (Name x) (INSTR_Op e).
Definition call (x : string) (f : string) (arg : llexpr) :=
  LL.assign (Name x) (INSTR_Call (LL.i64, global f) [((LL.i64, arg), [])] [] []).

Definition phi (x : string) (args : list (string * llexpr)) : local_id * LLVMAst.phi dtyp * list (metadata dtyp) :=
  (Name x, Phi LL.i64 (map (fun '(b, e) => (lbl b, e)) args), []).

Definition br (b : string) : terminator dtyp := TERM_Br_1 (lbl b).
Definition br_if (c : llexpr) (bt bf : string) : terminator dtyp := LL.br_if c (lbl bt) (lbl bf).
Definition ret (e : llexpr) : terminator dtyp := LL.ret LL.i64 e.

Definition block (name : string) (phis : list (local_id * LLVMAst.phi dtyp * list (metadata dtyp)))
    (c : code dtyp) (t : terminator dtyp) : LLVMAst.block dtyp :=
  {|
    blk_id := lbl name;
    blk_phis := phis;
    blk_code := c;
    blk_term := (IVoid 0, t, []);
    blk_comments := None;
  |}.

End P.

(** * Reflection: a terminating run of the stepper is an [eutt] fact *)

Lemma run_sound : forall {E R} (n : nat) (t : itree E R) (r : R),
  run n t = Done r -> t ≈ Ret r.
Proof.
  induction n as [| n IH]; intros t r H; cbn in H; [discriminate |].
  destruct (observe t) eqn:Ht.
  - inversion H; subst. rewrite (itree_eta t), Ht. reflexivity.
  - rewrite (itree_eta t), Ht, tau_eutt. apply IH, H.
  - discriminate.
Qed.

Lemma of_to_num_int : forall z, Z.of_num_int (Z.to_num_int z) = z.
Proof. intros z. unfold Z.to_num_int. apply DecimalZ.of_to. Qed.

(** * Structural lemmas for [run_exc]

    [run_exc] (Vellvm's frame-local exception catcher) is a copy of ITree's
    [throw_prefix]; these are the corresponding lemmas. *)

Lemma run_exc_ret : forall A (a : A), run_exc (Ret a) ≅ Ret (inr a).
Proof. intros. unfold run_exc. rewrite unfold_iter. cbn. rewrite Eqit.bind_ret_l. reflexivity. Qed.

Lemma run_exc_tau : forall A (t : CFGtop A), run_exc (Tau t) ≅ Tau (run_exc t).
Proof. intros. unfold run_exc. rewrite unfold_iter at 1. cbn. rewrite Eqit.bind_ret_l. reflexivity. Qed.

Lemma run_exc_exc : forall A X (e : CFGEtop X) x (k : X -> CFGtop A),
  exc_of_event e = Some x -> run_exc (Vis e k) ≅ Ret (inl x).
Proof. intros. unfold run_exc. rewrite unfold_iter. cbn. rewrite H. rewrite Eqit.bind_ret_l. reflexivity. Qed.

Lemma run_exc_ev : forall A X (e : CFGEtop X) (k : X -> CFGtop A),
  exc_of_event e = None -> run_exc (Vis e k) ≅ Vis e (fun y => Tau (run_exc (k y))).
Proof.
  intros. unfold run_exc. rewrite unfold_iter at 1. cbn. rewrite H. rewrite Eqit.bind_vis.
  apply eqit_Vis. intros. rewrite Eqit.bind_ret_l. reflexivity.
Qed.

#[global] Instance run_exc_eqit {A b} : Proper (eqit eq b b ==> eqit eq b b) (@run_exc _ A).
Proof.
  intros t1 t2 Ht. revert t1 t2 Ht. ginit. gcofix CIH. intros.
  unfold run_exc. setoid_rewrite unfold_iter.
  punfold Ht. red in Ht.
  remember (observe t1) as ot1 eqn:E1; remember (observe t2) as ot2 eqn:E2; clear E1 E2.
  hinduction Ht before r; intros; subst; eauto; try inv CHECK.
  - cbn. repeat rewrite Eqit.bind_ret_l. gfinal; right. pfold; constructor; auto.
  - cbn. repeat rewrite Eqit.bind_ret_l. gstep; constructor. gfinal. left. pclearbot. eapply CIH. auto.
  - cbn. destruct (exc_of_event e) eqn:He.
    + repeat rewrite Eqit.bind_ret_l. gfinal; right. pfold; constructor; auto.
    + repeat rewrite Eqit.bind_vis. gstep. constructor. intros. red.
      repeat rewrite Eqit.bind_ret_l. gstep. constructor. gfinal. left.
      eapply CIH. specialize (REL v). red in REL. destruct REL as [REL | REL]; [exact REL | contradiction].
  - cbn. rewrite Eqit.bind_ret_l. rewrite tau_euttge. rewrite unfold_iter. eapply IHHt; eauto.
  - cbn. rewrite Eqit.bind_ret_l. rewrite tau_euttge. rewrite unfold_iter. eapply IHHt; eauto.
Qed.

Lemma run_exc_bind : forall A B (t : CFGtop A) (k : A -> CFGtop B),
  run_exc (ITree.bind t k)
    ≅ ITree.bind (run_exc t) (fun r => match r with inl x => Ret (inl x) | inr a => run_exc (k a) end).
Proof.
  intros A B. ginit. gcofix CIH. intros.
  destruct (observe t) eqn:Heq; symmetry in Heq; apply simpobs in Heq.
  - rewrite Heq. rewrite run_exc_ret. repeat rewrite Eqit.bind_ret_l.
    gfinal; right. apply paco2_mon with (r := bot2); intros; try contradiction.
    enough (run_exc (k r0) ≅ run_exc (k r0)); auto; try reflexivity.
  - rewrite Heq. rewrite run_exc_tau. repeat rewrite Eqit.bind_tau. rewrite run_exc_tau.
    gstep. constructor. gfinal; eauto.
  - destruct (exc_of_event e) eqn:He.
    + rewrite Heq. rewrite Eqit.bind_vis. erewrite run_exc_exc by exact He. erewrite run_exc_exc by exact He.
      rewrite Eqit.bind_ret_l. gstep; constructor; auto.
    + rewrite Heq. rewrite Eqit.bind_vis. erewrite run_exc_ev by exact He. erewrite run_exc_ev by exact He.
      rewrite Eqit.bind_vis. gstep. constructor. intros. red. rewrite Eqit.bind_tau. gstep. constructor.
      gfinal. eauto.
Qed.

Lemma run_exc_trigger : forall X (e : CFGEtop X), exc_of_event e = None ->
  run_exc (ITree.trigger e) ≈ ITree.bind (ITree.trigger e) (fun x => Ret (inr x)).
Proof.
  intros. unfold ITree.trigger at 1. rewrite run_exc_ev by auto.
  rewrite Eqit.bind_trigger. apply eqit_Vis. intros. rewrite run_exc_ret, tau_eutt. reflexivity.
Qed.

(** * 64-bit integer facts *)

Definition two64 : Z := 18446744073709551616.

Lemma modulus_64 : @Integers.modulus 64 = two64.
Proof. reflexivity. Qed.

Lemma unsigned_repr64 : forall z, 0 <= z < two64 -> Integers.unsigned (@Integers.repr 64 z) = z.
Proof. intros. apply Integers.unsigned_repr. unfold Integers.max_unsigned. rewrite modulus_64. lia. Qed.

Lemma unsigned_range64 : forall x : @Integers.bit_int 64, 0 <= Integers.unsigned x < two64.
Proof. intros. rewrite <- modulus_64. apply Integers.unsigned_range. Qed.

Lemma eq_repr64 : forall a b, 0 <= a < two64 -> 0 <= b < two64 ->
  Integers.eq (@Integers.repr 64 a) (Integers.repr b) = (a =? b).
Proof.
  intros. unfold Integers.eq. rewrite !unsigned_repr64 by auto.
  destruct (zeq a b) as [-> | Hne]; symmetry; [apply Z.eqb_eq; auto | apply Z.eqb_neq; auto].
Qed.

Lemma ltu_repr64 : forall a b, 0 <= a < two64 -> 0 <= b < two64 ->
  Integers.ltu (@Integers.repr 64 a) (Integers.repr b) = (a <? b).
Proof.
  intros. unfold Integers.ltu. rewrite !unsigned_repr64 by auto.
  destruct (zlt a b) as [Hlt | Hge]; symmetry; [apply Z.ltb_lt; auto | apply Z.ltb_ge; lia].
Qed.

Lemma mul_repr64 : forall a b, 0 <= a < two64 -> 0 <= b < two64 ->
  Integers.mul (@Integers.repr 64 a) (Integers.repr b) = Integers.repr (a * b).
Proof. intros. unfold Integers.mul. rewrite !unsigned_repr64 by auto. reflexivity. Qed.

Lemma add_repr64 : forall a b, 0 <= a < two64 -> 0 <= b < two64 ->
  Integers.add (@Integers.repr 64 a) (Integers.repr b) = Integers.repr (a + b).
Proof. intros. unfold Integers.add. rewrite !unsigned_repr64 by auto. reflexivity. Qed.

Lemma modu_repr64 : forall a b, 0 <= a < two64 -> 0 <= b < two64 ->
  Integers.modu (@Integers.repr 64 a) (Integers.repr b) = Integers.repr (a mod b).
Proof. intros. unfold Integers.modu. rewrite !unsigned_repr64 by auto. reflexivity. Qed.

Lemma sub_repr64 : forall a b, 0 <= b <= a -> a < two64 ->
  Integers.sub (@Integers.repr 64 a) (Integers.repr b) = Integers.repr (a - b).
Proof. intros. unfold Integers.sub. rewrite !unsigned_repr64 by lia. reflexivity. Qed.

Lemma divu_repr64 : forall a b, 0 <= a < two64 -> 0 <= b < two64 ->
  Integers.divu (@Integers.repr 64 a) (Integers.repr b) = Integers.repr (a / b).
Proof. intros. unfold Integers.divu. rewrite !unsigned_repr64 by auto. reflexivity. Qed.

Lemma modulus64 : @Integers.modulus 64 = two64.
Proof. vm_compute. reflexivity. Qed.

(** A logical shift right of any value: the value is first reduced modulo
    2^64 (so that the lemma also applies to a product that overflowed). *)
Lemma shru_repr64 : forall a k, 0 <= k < 64 ->
  Integers.shru (@Integers.repr 64 a) (Integers.repr k) = Integers.repr ((a mod two64) / 2 ^ k).
Proof.
  intros. unfold Integers.shru. rewrite (Integers.unsigned_repr_eq a), modulus64, (unsigned_repr64 k) by (unfold two64; lia).
  rewrite Z.shiftr_div_pow2 by lia. reflexivity.
Qed.

(** Eight bytes, little-endian, as a 64-bit value. *)
Definition bytes8 (z0 z1 z2 z3 z4 z5 z6 z7 : Z) : Z :=
  z0 + 256 * (z1 + 256 * (z2 + 256 * (z3 + 256 * (z4 + 256 * (z5 + 256 * (z6 + 256 * z7)))))).
Arguments bytes8 : simpl never.

Lemma eq_bool_one : forall c : bool,
  Integers.eq (if c then @Integers.one 1 else Integers.zero) Integers.one = c.
Proof.
  destruct c; [apply Integers.eq_true |].
  apply Integers.eq_false. intro H. apply (f_equal Integers.unsigned) in H.
  rewrite Integers.unsigned_zero, Integers.unsigned_one in H. discriminate.
Qed.

Opaque Integers.repr Integers.unsigned Integers.mul Integers.add Integers.sub Integers.modu Integers.divu Integers.shru
  Integers.eq Integers.ltu Integers.zero Integers.one.

(** 2^63: a convenient bound for program proofs (values below it never
    overflow when added, and their products fit when one of them is small). *)
Definition two63 : Z := 9223372036854775808.

(** Shapes of the integer evaluators on 64-bit operands. *)
Section Evaluators.
  Variables a b : @Integers.bit_int 64.
  Let dv (x : @Integers.bit_int 64) : dvalue := DVALUE_Base (DVALUE_I 64 x).

  Lemma eval_iop_mul : eval_iop (LLVMAst.Mul false false) (dv a) (dv b) = raise_ret (dv (Integers.mul a b)).
  Proof. reflexivity. Qed.

  Lemma eval_iop_add : eval_iop (LLVMAst.Add false false) (dv a) (dv b) = raise_ret (dv (Integers.add a b)).
  Proof. reflexivity. Qed.

  Lemma eval_iop_sub : eval_iop (LLVMAst.Sub false false) (dv a) (dv b) = raise_ret (dv (Integers.sub a b)).
  Proof. reflexivity. Qed.

  Lemma eval_iop_lshr : Integers.unsigned b < 64 ->
    eval_iop (LLVMAst.LShr false) (dv a) (dv b) = raise_ret (dv (Integers.shru a b)).
  Proof.
    intros H. cbn. destruct (Integers.unsigned b >=? 64) eqn:E; [apply Z.geb_le in E; lia | reflexivity].
  Qed.

  Lemma eval_iop_udiv : Integers.unsigned b <> 0 ->
    eval_iop (LLVMAst.UDiv false) (dv a) (dv b) = raise_ret (dv (Integers.divu a b)).
  Proof.
    intros H. cbn. destruct (Integers.unsigned b =? 0) eqn:E; [apply Z.eqb_eq in E; contradiction | reflexivity].
  Qed.

  Lemma eval_iop_urem : Integers.unsigned b <> 0 ->
    eval_iop LLVMAst.URem (dv a) (dv b) = raise_ret (dv (Integers.modu a b)).
  Proof.
    intros H. cbn. destruct (Integers.unsigned b =? 0) eqn:E; [apply Z.eqb_eq in E; contradiction | reflexivity].
  Qed.

  Lemma eval_icmp_ult : eval_icmp false LLVMAst.Ult (dv a) (dv b)
    = raise_ret (DVALUE_Base (if Integers.ltu a b then DVALUE_I 1 Integers.one else DVALUE_I 1 Integers.zero)).
  Proof. reflexivity. Qed.

  Lemma eval_icmp_ugt : eval_icmp false LLVMAst.Ugt (dv a) (dv b)
    = raise_ret (DVALUE_Base (if Integers.ltu b a then DVALUE_I 1 Integers.one else DVALUE_I 1 Integers.zero)).
  Proof. reflexivity. Qed.

  Lemma eval_icmp_eq : eval_icmp false LLVMAst.Eq (dv a) (dv b)
    = raise_ret (DVALUE_Base (if Integers.eq a b then DVALUE_I 1 Integers.one else DVALUE_I 1 Integers.zero)).
  Proof. reflexivity. Qed.
End Evaluators.

(** * Running CFG-level itrees through the whole interpretation stack *)

(** The body of [denote_mcfg]'s [mrec]: resolve a call against the function map. *)
Definition mcfg_ctx (fundefs : IntMap function_denotation) : CallE ~> CFGtop :=
  fun T call =>
    match call with
    | Call dt fv args =>
        match lookup_defn fv fundefs with
        | Some f_den => f_den args
        | None => inr <$> external_call dt fv args
        end
    end.

Lemma denote_mcfg_mrec : forall fundefs dt f args,
  denote_mcfg fundefs dt f args = mrec (mcfg_ctx fundefs) (Call dt f args).
Proof. reflexivity. Qed.

Section Runner.
  Variable fundefs : IntMap function_denotation.

  (** [runF t s]: interpret the CFG-level tree [t] (calls resolved through
      [fundefs]) from the fused state [s]. *)
  Definition runF {R} (t : CFGtop R) (s : FusedS) : MCFGbot (Res R) :=
    interp_mcfg (interp_mrec (mcfg_ctx fundefs) t) s.

  #[global] Instance runF_eutt {R} : Proper (eutt eq ==> eq ==> eutt eq) (@runF R).
  Proof.
    repeat intro; subst. unfold runF, interp_mcfg, interp_intrinsics.
    eapply eutt_interp_state_eq; [| reflexivity].
    eapply eutt_interp'. eapply Proper_interp_mrec; [intros ? ?; reflexivity | exact H].
  Qed.

  Lemma runF_ret : forall {R} (x : R) s, runF (Ret x) s ≈ Ret (s, x).
  Proof.
    intros. unfold runF, interp_mcfg, interp_intrinsics.
    rewrite unfold_interp_mrec; cbn.
    rewrite interp_ret, interp_state_ret. reflexivity.
  Qed.

  Lemma runF_tau : forall {R} (t : CFGtop R) s, runF (Tau t) s ≈ runF t s.
  Proof.
    intros. unfold runF, interp_mcfg, interp_intrinsics.
    rewrite unfold_interp_mrec at 1; cbn.
    rewrite interp_tau, interp_state_tau, tau_eutt. reflexivity.
  Qed.

  Lemma runF_bind : forall {R S} (t : CFGtop R) (k : R -> CFGtop S) s,
    runF (ITree.bind t k) s ≈ ITree.bind (runF t s) (fun sx => runF (k (snd sx)) (fst sx)).
  Proof.
    intros. unfold runF, interp_mcfg, interp_intrinsics.
    rewrite interp_mrec_bind, interp_bind, interp_state_bind. reflexivity.
  Qed.

  Ltac norm := repeat (first [rewrite Eqit.bind_ret_l | rewrite Eqit.bind_bind | rewrite tau_eutt]; cbn).

  (* Run a non-call event through all the interpretation layers down to the
     fused handler. *)
  Ltac runF_event :=
    unfold runF, interp_mcfg, interp_intrinsics;
    rewrite interp_mrec_trigger; cbn;
    rewrite interp_trigger; cbn; unfold F_trigger, E_trigger;
    rewrite interp_state_trigger; cbn.

  Lemma runF_lread : forall x v m env exc loc stk g,
    Maps.lookup x env = Some v ->
    runF (lread x) (m, ((Build_stack_frame env exc loc, stk), g))
      ≈ Ret ((m, ((Build_stack_frame env exc loc, stk), g)), v).
  Proof. intros. unfold lread. runF_event. cbn in H. rewrite H. norm. reflexivity. Qed.

  Lemma runF_lwrite : forall x v m env exc loc stk g,
    runF (lwrite x v) (m, ((Build_stack_frame env exc loc, stk), g))
      ≈ Ret ((m, ((Build_stack_frame (Maps.add x v env) exc loc, stk), g)), tt).
  Proof. intros. unfold lwrite. runF_event. norm. reflexivity. Qed.

  Lemma runF_gread : forall x v m ls g,
    Maps.lookup x g = Some v ->
    runF (gread x) (m, (ls, g)) ≈ Ret ((m, (ls, g)), v).
  Proof. intros. unfold gread. runF_event. cbn in H. rewrite H. norm. reflexivity. Qed.

  Lemma runF_stack_push : forall args m fr stk g,
    runF (stack_push args) (m, ((fr, stk), g))
      ≈ Ret ((m, ((Build_stack_frame (fold_right (fun '(x, dv) => Maps.add x dv) Maps.empty args) None (Some ""), fr :: stk), g)), tt).
  Proof. intros. unfold stack_push. runF_event. norm. reflexivity. Qed.

  Lemma runF_stack_pop : forall m fr fr' stk g,
    runF stack_pop (m, ((fr, fr' :: stk), g)) ≈ Ret ((m, ((fr', stk), g)), tt).
  Proof. intros. unfold stack_pop. runF_event. norm. reflexivity. Qed.

  Lemma runF_mem : forall X (e : MemoryE X) m rest,
    runF (trigger e) (m, rest)
      ≈ ITree.bind (handle_memory memM_interp e m) (fun mr => Ret ((fst mr, rest), snd mr)).
  Proof. intros. runF_event. apply eutt_eq_bind. intros [? ?]. reflexivity. Qed.

  Lemma runF_call : forall dt fv args fden s,
    lookup_defn fv fundefs = Some fden ->
    runF (call dt fv args) s ≈ runF (fden args) s.
  Proof.
    intros. unfold runF, interp_mcfg, interp_intrinsics, call.
    Opaque lookup_defn.
    rewrite interp_mrec_trigger. cbn. unfold mrec. cbn. rewrite H. reflexivity.
    Transparent lookup_defn.
  Qed.

  (** ** Inside a function body: running under [run_exc] *)

  Definition runX {A} (t : CFGtop A) (s : FusedS) : MCFGbot (Res (exc + A)) := runF (run_exc t) s.

  #[global] Instance runX_eutt {A} : Proper (eutt eq ==> eq ==> eutt eq) (@runX A).
  Proof. repeat intro; subst. unfold runX. rewrite H. reflexivity. Qed.

  Lemma runX_ret : forall A (a : A) s, runX (Ret a) s ≈ Ret (s, inr a).
  Proof. intros; unfold runX; rewrite run_exc_ret; apply runF_ret. Qed.

  Lemma runX_tau : forall A (t : CFGtop A) s, runX (Tau t) s ≈ runX t s.
  Proof. intros; unfold runX; rewrite run_exc_tau; apply runF_tau. Qed.

  Lemma runX_bind : forall A B (t : CFGtop A) (k : A -> CFGtop B) s,
    runX (ITree.bind t k) s
      ≈ ITree.bind (runX t s) (fun sr => match snd sr with
                                        | inl x => Ret (fst sr, inl x)
                                        | inr a => runX (k a) (fst sr)
                                        end).
  Proof.
    intros; unfold runX. rewrite run_exc_bind. rewrite runF_bind.
    apply eutt_eq_bind; intros [s' [x | a]]; cbn.
    - apply runF_ret.
    - reflexivity.
  Qed.

  Lemma runX_bind_ok : forall A B (t : CFGtop A) (k : A -> CFGtop B) s s' a,
    runX t s ≈ Ret (s', inr a) -> runX (ITree.bind t k) s ≈ runX (k a) s'.
  Proof. intros. rewrite runX_bind, H, Eqit.bind_ret_l. reflexivity. Qed.

  (** The workhorse for symbolic execution: run the first part, continue with
      the rest. *)
  Lemma runX_bind_step : forall A B (t : CFGtop A) (k : A -> CFGtop B) s s' a r,
    runX t s ≈ Ret (s', inr a) -> runX (k a) s' ≈ r -> runX (ITree.bind t k) s ≈ r.
  Proof. intros. rewrite (runX_bind_ok _ _ _ _ _ _ _ H). exact H0. Qed.

  Lemma runX_of_runF_trigger : forall X (e : CFGEtop X) s s' v,
    exc_of_event e = None ->
    runF (ITree.trigger e) s ≈ Ret (s', v) ->
    runX (ITree.trigger e) s ≈ Ret (s', inr v).
  Proof.
    intros. unfold runX. rewrite run_exc_trigger by auto. rewrite runF_bind, H0, Eqit.bind_ret_l. cbn.
    apply runF_ret.
  Qed.

  Lemma runX_trigger_bind : forall X (e : CFGEtop X) s,
    exc_of_event e = None ->
    runX (ITree.trigger e) s ≈ ITree.bind (runF (ITree.trigger e) s) (fun sx => Ret (fst sx, inr (snd sx))).
  Proof.
    intros. unfold runX. rewrite run_exc_trigger by auto. rewrite runF_bind.
    apply eutt_eq_bind. intros [s' v]. cbn. apply runF_ret.
  Qed.

  Lemma runX_lwrite : forall x v m env exc loc stk g,
    runX (lwrite x v) (m, ((Build_stack_frame env exc loc, stk), g))
      ≈ Ret ((m, ((Build_stack_frame (Maps.add x v env) exc loc, stk), g)), inr tt).
  Proof. intros. apply runX_of_runF_trigger; [reflexivity | apply runF_lwrite]. Qed.

  Lemma runX_call : forall dt fv args fden s,
    lookup_defn fv fundefs = Some fden ->
    runX (call dt fv args) s ≈ ITree.bind (runF (fden args) s) (fun sx => Ret (fst sx, inr (snd sx))).
  Proof.
    intros. etransitivity; [apply runX_trigger_bind; reflexivity |].
    eapply eutt_clo_bind; [exact (runF_call dt fv args fden s H) | intros ? ? ->; reflexivity].
  Qed.

  (** ** Expressions *)

  Lemma runX_exp_local : forall t x v m env exc loc stk g,
    Maps.lookup x env = Some v ->
    runX (denote_exp' t (EXP_Ident (ID_Local x))) (m, ((Build_stack_frame env exc loc, stk), g))
      ≈ Ret ((m, ((Build_stack_frame env exc loc, stk), g)), inr v).
  Proof.
    intros. unfold denote_exp'; cbn. unfold withCall, lread. rewrite translate_trigger.
    apply runX_of_runF_trigger; [reflexivity |].
    runF_event. cbn in H. rewrite H. norm. reflexivity.
  Qed.

  Lemma runX_exp_global : forall t x v m ls g,
    Maps.lookup x g = Some v ->
    runX (denote_exp' t (EXP_Ident (ID_Global x))) (m, (ls, g)) ≈ Ret ((m, (ls, g)), inr v).
  Proof.
    intros. unfold denote_exp'; cbn. unfold withCall, gread. rewrite translate_trigger.
    apply runX_of_runF_trigger; [reflexivity |].
    runF_event. cbn in H. rewrite H. norm. reflexivity.
  Qed.

  Lemma runX_exp_lit : forall z s,
    runX (denote_exp' (Some LL.i64) (P.lit z)) s ≈ Ret (s, inr (DVALUE_Base (DVALUE_I 64 (Integers.repr z)))).
  Proof.
    intros. unfold denote_exp', P.lit, LL.int_lit. cbn. rewrite DecimalZ.of_to.
    unfold withCall. rewrite translate_ret. apply runX_ret.
  Qed.

  Lemma runX_exp_ibinop : forall iop ea eb va vb vr s,
    runX (denote_exp' (Some LL.i64) ea) s ≈ Ret (s, inr va) ->
    runX (denote_exp' (Some LL.i64) eb) s ≈ Ret (s, inr vb) ->
    eval_iop iop va vb = raise_ret vr ->
    runX (denote_exp' None (OP_IBinop iop LL.i64 ea eb)) s ≈ Ret (s, inr vr).
  Proof.
    intros. unfold denote_exp' in *. cbn. unfold withCall in *.
    rewrite translate_bind. eapply runX_bind_step; [exact H |].
    rewrite translate_bind. eapply runX_bind_step; [exact H0 |].
    rewrite H1. cbn. rewrite translate_ret. apply runX_ret.
  Qed.

  Lemma runX_exp_icmp : forall cmp ea eb va vb vr s,
    runX (denote_exp' (Some LL.i64) ea) s ≈ Ret (s, inr va) ->
    runX (denote_exp' (Some LL.i64) eb) s ≈ Ret (s, inr vb) ->
    eval_icmp false cmp va vb = raise_ret vr ->
    runX (denote_exp' None (OP_ICmp false cmp LL.i64 ea eb)) s ≈ Ret (s, inr vr).
  Proof.
    intros. unfold denote_exp' in *. cbn. unfold withCall in *.
    rewrite translate_bind. eapply runX_bind_step; [exact H |].
    rewrite translate_bind. eapply runX_bind_step; [exact H0 |].
    rewrite H1. cbn. rewrite translate_ret. apply runX_ret.
  Qed.

  (** ** Instructions *)

  Lemma runX_instr_op : forall x e v md va m env exc loc stk g,
    runX (denote_exp' None e) (m, ((Build_stack_frame env exc loc, stk), g))
      ≈ Ret ((m, ((Build_stack_frame env exc loc, stk), g)), inr v) ->
    runX (denote_instr (IId x, INSTR_Op e, md) va) (m, ((Build_stack_frame env exc loc, stk), g))
      ≈ Ret ((m, ((Build_stack_frame (Maps.add x v env) exc loc, stk), g)), inr tt).
  Proof.
    intros. cbn. eapply runX_bind_step; [exact H |].
    eapply runX_bind_step; [apply runX_lwrite |]. apply runX_ret.
  Qed.

  (** A call [x = call i64 @f(i64 arg)] to an internal function that returns
      normally. The callee may change the memory, the frame and the globals;
      the result is written into the caller's frame. *)
  Lemma runX_instr_call : forall x f arg va vap md fv fden S m' env' exc' loc' stk' g' rv,
    intrinsic_exp (P.global f) = None ->
    runX (denote_exp' (Some LL.i64) arg) S ≈ Ret (S, inr va) ->
    Maps.lookup (Name f) (snd (snd S)) = Some fv ->
    lookup_defn fv fundefs = Some fden ->
    runF (fden [va]) S ≈ Ret ((m', ((Build_stack_frame env' exc' loc', stk'), g')), inr rv) ->
    runX (denote_instr (IId x, INSTR_Call (LL.i64, P.global f) [((LL.i64, arg), [])] [] [], md) vap) S
      ≈ Ret ((m', ((Build_stack_frame (Maps.add x rv env') exc' loc', stk'), g')), inr tt).
  Proof.
    intros * Hintr Harg Hg Hdef Hcall. destruct S as [m [ls g]]. cbn in Hg.
    Opaque intrinsic_exp. cbn. cbn in Hintr. rewrite Hintr. Transparent intrinsic_exp.
    eapply runX_bind_step.
    { eapply runX_bind_step; [exact Harg |]. eapply runX_bind_step; [apply runX_ret |]. apply runX_ret. }
    eapply runX_bind_step.
    { eapply runX_bind_step; [apply runX_exp_global; exact Hg |].
      eapply runX_bind_step.
      { rewrite (runX_call _ _ _ _ _ Hdef). rewrite Hcall, Eqit.bind_ret_l. reflexivity. }
      cbn. apply runX_ret. }
    apply runX_lwrite.
  Qed.

  (** ** Terminators *)

  Lemma runX_term_ret : forall e v md iid s,
    runX (denote_exp' (Some LL.i64) e) s ≈ Ret (s, inr v) ->
    runX (denote_terminator (iid, TERM_Ret (LL.i64, e), md)) s ≈ Ret (s, inr (inr v)).
  Proof. intros. cbn. eapply runX_bind_step; [exact H |]. apply runX_ret. Qed.

  Lemma runX_term_br : forall e (c : bool) bt bf md iid s,
    runX (denote_exp' (Some LL.i1) e) s
      ≈ Ret (s, inr (DVALUE_Base (if c then DVALUE_I 1 Integers.one else DVALUE_I 1 Integers.zero))) ->
    runX (denote_terminator (iid, TERM_Br (LL.i1, e) bt bf, md)) s ≈ Ret (s, inr (inl (if c then bt else bf))).
  Proof.
    intros. cbn. eapply runX_bind_step; [exact H |]. cbn.
    destruct c; cbn.
    - rewrite Integers.eq_true. apply runX_ret.
    - pose proof (eq_bool_one false) as E. cbn in E. rewrite E. apply runX_ret.
  Qed.

  Lemma runX_term_br1 : forall b md iid s,
    runX (denote_terminator (iid, TERM_Br_1 b, md)) s ≈ Ret (s, inr (inl b)).
  Proof. intros. cbn. apply runX_ret. Qed.

  (** ** Phi nodes *)

  Lemma runX_phi : forall bid id t args md e v s,
    assoc bid args = Some e ->
    runX (denote_exp' (Some t) e) s ≈ Ret (s, inr v) ->
    runX (denote_phi bid (id, Phi t args, md)) s ≈ Ret (s, inr (id, v)).
  Proof. intros. cbn. rewrite H. eapply runX_bind_step; [exact H0 |]. apply runX_ret. Qed.

  Lemma runX_phis_nil : forall bid s, runX (denote_phis bid []) s ≈ Ret (s, inr tt).
  Proof.
    intros. unfold denote_phis. cbn.
    eapply runX_bind_step; [apply runX_ret |]. cbn. eapply runX_bind_step; [apply runX_ret |]. apply runX_ret.
  Qed.

  Lemma runX_phis_1 : forall bid p id v m env exc loc stk g,
    runX (denote_phi bid p) (m, ((Build_stack_frame env exc loc, stk), g))
      ≈ Ret ((m, ((Build_stack_frame env exc loc, stk), g)), inr (id, v)) ->
    runX (denote_phis bid [p]) (m, ((Build_stack_frame env exc loc, stk), g))
      ≈ Ret ((m, ((Build_stack_frame (Maps.add id v env) exc loc, stk), g)), inr tt).
  Proof.
    intros. unfold denote_phis. cbn.
    eapply runX_bind_step.
    { eapply runX_bind_step; [exact H |]. eapply runX_bind_step; [apply runX_ret |]. apply runX_ret. }
    cbn. eapply runX_bind_step.
    { eapply runX_bind_step; [apply runX_lwrite |]. eapply runX_bind_step; [apply runX_ret |]. apply runX_ret. }
    apply runX_ret.
  Qed.

  Lemma runX_phis_2 : forall bid p1 p2 id1 v1 id2 v2 m env exc loc stk g,
    runX (denote_phi bid p1) (m, ((Build_stack_frame env exc loc, stk), g))
      ≈ Ret ((m, ((Build_stack_frame env exc loc, stk), g)), inr (id1, v1)) ->
    runX (denote_phi bid p2) (m, ((Build_stack_frame env exc loc, stk), g))
      ≈ Ret ((m, ((Build_stack_frame env exc loc, stk), g)), inr (id2, v2)) ->
    runX (denote_phis bid [p1; p2]) (m, ((Build_stack_frame env exc loc, stk), g))
      ≈ Ret ((m, ((Build_stack_frame (Maps.add id2 v2 (Maps.add id1 v1 env)) exc loc, stk), g)), inr tt).
  Proof.
    intros. unfold denote_phis. cbn.
    eapply runX_bind_step.
    { eapply runX_bind_step; [exact H |].
      eapply runX_bind_step.
      { eapply runX_bind_step; [exact H0 |]. eapply runX_bind_step; [apply runX_ret |]. apply runX_ret. }
      apply runX_ret. }
    cbn. eapply runX_bind_step.
    { eapply runX_bind_step; [apply runX_lwrite |].
      eapply runX_bind_step.
      { eapply runX_bind_step; [apply runX_lwrite |]. eapply runX_bind_step; [apply runX_ret |]. apply runX_ret. }
      apply runX_ret. }
    apply runX_ret.
  Qed.

  (** ** Code, blocks, and the control-flow graph *)

  Lemma runX_code_nil : forall va s, runX (denote_code [] va) s ≈ Ret (s, inr tt).
  Proof. intros. cbn. apply runX_ret. Qed.

  Lemma runX_code_cons : forall i c va s s' s'',
    runX (denote_instr i va) s ≈ Ret (s', inr tt) ->
    runX (denote_code c va) s' ≈ Ret (s'', inr tt) ->
    runX (denote_code (i :: c) va) s ≈ Ret (s'', inr tt).
  Proof. intros. cbn. eapply runX_bind_step; [exact H |]. exact H0. Qed.

  Lemma runX_block : forall b from va s1 s2 s3 r,
    runX (denote_phis from (blk_phis b)) s1 ≈ Ret (s2, inr tt) ->
    runX (denote_code (blk_code b) va) s2 ≈ Ret (s3, inr tt) ->
    runX (denote_terminator (blk_term b)) s3 ≈ Ret (s3, inr r) ->
    runX (denote_block b from va) s1 ≈ Ret (s3, inr r).
  Proof.
    intros. unfold denote_block. eapply runX_bind_step; [exact H |]. eapply runX_bind_step; [exact H0 |]. exact H1.
  Qed.

  (** Unfolding one iteration of the CFG loop. This is [denote_ocfg_unfold_in]
      from Vellvm's theory, but keyed on the block map's [RM.find] (which
      computes on concrete programs) rather than on [find_block] (whose
      decidable equality on block names is opaque). *)
  Lemma denote_ocfg_unfold_find : forall va bks from src bk,
    RM.find src (ocfg_map bks) = Some bk ->
    denote_ocfg bks va (from, src)
      ≈ vob <- denote_block bk from va ;;
        match vob with
        | inr v => Ret (inr v)
        | inl tgt => denote_ocfg bks va (src, tgt)
        end.
  Proof.
    intros * GET. unfold denote_ocfg, denote_ocfg_map at 1.
    rewrite unfold_iter.
    Opaque denote_block.
    cbn. rewrite GET. rewrite Eqit.bind_bind.
    apply eutt_eq_bind. intros [tgt | v]; rewrite Eqit.bind_ret_l; cbn.
    - rewrite tau_eutt. reflexivity.
    - reflexivity.
    Transparent denote_block.
  Qed.

  (** One step of the CFG loop: run the current block, then either return or
      jump to the next block. *)
  Lemma runX_ocfg_step : forall bks va from src bk s s' r,
    RM.find src (ocfg_map bks) = Some bk ->
    runX (denote_block bk from va) s ≈ Ret (s', inr r) ->
    runX (denote_ocfg bks va (from, src)) s
      ≈ match r with
        | inr v => Ret (s', inr (inr v))
        | inl tgt => runX (denote_ocfg bks va (src, tgt)) s'
        end.
  Proof.
    intros. rewrite denote_ocfg_unfold_find by exact H.
    rewrite runX_bind, H0, Eqit.bind_ret_l. cbn. destruct r; [reflexivity | apply runX_ret].
  Qed.

  (** The body of a function as run by [denote_function]. *)
  Lemma runX_cfg : forall f va s s' v,
    runX (denote_ocfg (blks f) va (init f, init f)) s ≈ Ret (s', inr (inr v)) ->
    runX (denote_cfg_map (ocfg_map (blks f)) f va) s ≈ Ret (s', inr v).
  Proof.
    intros. unfold denote_cfg_map. change (denote_ocfg_map (ocfg_map (blks f))) with (denote_ocfg (blks f)).
    eapply runX_bind_step; [exact H |]. apply runX_ret.
  Qed.

  (** Phi nodes in general: all are evaluated in the initial environment,
      then all are written, in order. *)
  Lemma runX_map_monad_phi : forall bid ps ivs s,
    Forall2 (fun p iv => runX (denote_phi bid p) s ≈ Ret (s, inr iv)) ps ivs ->
    runX (map_monad (denote_phi bid) ps) s ≈ Ret (s, inr ivs).
  Proof.
    intros bid ps ivs s H. induction H as [| p iv ps ivs Hp _ IH].
    - apply runX_ret.
    - change (map_monad (denote_phi bid) (p :: ps))
        with (ITree.bind (denote_phi bid p)
                (fun v => ITree.bind (map_monad (denote_phi bid) ps) (fun vs => Ret (v :: vs)))).
      eapply runX_bind_step; [exact Hp |]. eapply runX_bind_step; [exact IH |]. apply runX_ret.
  Qed.

  Lemma runX_map_monad_lwrite : forall ivs m env exc loc stk g,
    runX (map_monad (fun '(id, dv) => lwrite id dv) ivs : CFGtop (list unit)) (ST m env exc loc stk g)
      ≈ Ret (ST m (fold_left (fun e '(id, v) => Maps.add id v e) ivs env) exc loc stk g, inr (map (fun _ => tt) ivs)).
  Proof.
    induction ivs as [| [id v] ivs IH]; intros.
    - apply runX_ret.
    - change (map_monad (fun '(id, dv) => lwrite id dv) ((id, v) :: ivs) : CFGtop (list unit))
        with (ITree.bind (lwrite id v)
                (fun u => ITree.bind (map_monad (fun '(id, dv) => lwrite id dv) ivs : CFGtop (list unit))
                            (fun us => Ret (u :: us)))).
      eapply runX_bind_step; [apply runX_lwrite |]. eapply runX_bind_step; [apply IH |]. apply runX_ret.
  Qed.

  Lemma runX_phis : forall bid ps ivs m env env' exc loc stk g,
    Forall2 (fun p iv => runX (denote_phi bid p) (ST m env exc loc stk g) ≈ Ret (ST m env exc loc stk g, inr iv)) ps ivs ->
    env' = fold_left (fun e '(id, v) => Maps.add id v e) ivs env ->
    runX (denote_phis bid ps) (ST m env exc loc stk g) ≈ Ret (ST m env' exc loc stk g, inr tt).
  Proof.
    intros * H ->.
    change (denote_phis bid ps)
      with (ITree.bind (map_monad (denote_phi bid) ps)
              (fun dvs => ITree.bind (map_monad (fun '(id, dv) => lwrite id dv) dvs : CFGtop (list unit))
                            (fun _ => Ret tt))).
    eapply runX_bind_step; [apply runX_map_monad_phi; exact H |].
    eapply runX_bind_step; [apply runX_map_monad_lwrite |]. apply runX_ret.
  Qed.
  (** The same, with the block list and the entry block given by name (so that
      the goal is in the form the [find_blocks] hints expect). *)
  Lemma runX_cfg_named : forall f bks entry va s s' v,
    bks = blks f -> entry = init f ->
    runX (denote_ocfg bks va (entry, entry)) s ≈ Ret (s', inr (inr v)) ->
    runX (denote_cfg_map (ocfg_map (blks f)) f va) s ≈ Ret (s', inr v).
  Proof. intros * -> ->. apply runX_cfg. Qed.
End Runner.

(** * Helpers for the program-specific proofs *)

Lemma find_add_eq : forall (V : Type) k (v : V) (m : rmap V), RM.find k (RM.add k v m) = Some v.
Proof. intros. apply RMF.F.add_eq_o. reflexivity. Qed.

Lemma find_add_neq : forall (V : Type) k k' (v : V) (m : rmap V), k' <> k -> RM.find k (RM.add k' v m) = RM.find k m.
Proof. intros. apply RMF.F.add_neq_o. exact H. Qed.

(* Resolve a lookup in an environment built from [Maps.add]s with concrete keys. *)
Ltac simpl_lookup :=
  cbn [Maps.lookup Maps.add Maps.empty Map_rmap fold_right] in *;
  repeat first [ rewrite find_add_eq | rewrite find_add_neq by discriminate ].

Lemma runF_bind_step : forall fundefs R S (t : CFGtop R) (k : R -> CFGtop S) s s' a r,
  runF fundefs t s ≈ Ret (s', a) -> runF fundefs (k a) s' ≈ r -> runF fundefs (ITree.bind t k) s ≈ r.
Proof. intros. rewrite runF_bind, H, Eqit.bind_ret_l. cbn. exact H0. Qed.

Lemma runF_mem_eq : forall fundefs X (e : MemoryE X) m m' v rest,
  (handle_memory memM_interp e m : itree MCFGEbot (state * X)) ≈ Ret (m', v) ->
  runF fundefs (trigger e) (m, rest) ≈ Ret ((m', rest), v).
Proof. intros. rewrite runF_mem, H, Eqit.bind_ret_l. reflexivity. Qed.

Ltac mem_compute := unfold handle_memory; cbn; repeat (rewrite Eqit.bind_ret_l; cbn); reflexivity.

Lemma runX_ocfg_jump : forall fundefs bks va from src bk s s' tgt,
  RM.find src (ocfg_map bks) = Some bk ->
  runX fundefs (denote_block bk from va) s ≈ Ret (s', inr (inl tgt)) ->
  runX fundefs (denote_ocfg bks va (from, src)) s ≈ runX fundefs (denote_ocfg bks va (src, tgt)) s'.
Proof. intros. exact (runX_ocfg_step fundefs bks va from src bk s s' (inl tgt) H H0). Qed.

Lemma runX_ocfg_ret : forall fundefs bks va from src bk s s' v,
  RM.find src (ocfg_map bks) = Some bk ->
  runX fundefs (denote_block bk from va) s ≈ Ret (s', inr (inr v)) ->
  runX fundefs (denote_ocfg bks va (from, src)) s ≈ Ret (s', inr (inr v)).
Proof. intros. exact (runX_ocfg_step fundefs bks va from src bk s s' (inr v) H H0). Qed.

(** ** The memory operations performed by a call

    Every call pushes a memory frame, allocates a zero-byte varargs block,
    stores zero bytes into it, and pops the frame on return. The memory is
    left unchanged except for the provenance counter. *)

Lemma mem_push_eq : forall mem fs heap p,
  (handle_memory memM_interp MemPush (mkState (mkMemoryStack mem fs heap) p) : itree MCFGEbot _)
    ≈ Ret (mkState (mkMemoryStack mem (Snoc fs []) heap) p, tt).
Proof. reflexivity. Qed.

Lemma mem_pop_eq : forall mem fs heap p,
  (handle_memory memM_interp MemPop (mkState (mkMemoryStack mem (Snoc fs []) heap) p) : itree MCFGEbot _)
    ≈ Ret (mkState (mkMemoryStack mem fs heap) p, tt).
Proof. reflexivity. Qed.

Lemma alloca_empty_eq : forall mem fs heap p, exists ptr,
  (handle_memory memM_interp (Alloca (DTYPE_Struct true []) 1 None) (mkState (mkMemoryStack mem fs heap) p) : itree MCFGEbot _)
    ≈ Ret (mkState (mkMemoryStack mem fs heap) (next_provenance p), DVALUE_Base (DVALUE_Pointer ptr)).
Proof. intros. eexists. mem_compute. Qed.

Lemma store_empty_eq : forall σ ptr,
  (handle_memory memM_interp (Store (DTYPE_Struct true []) (DVALUE_Base (DVALUE_Pointer ptr)) (DVALUE_Struct true [])) σ : itree MCFGEbot _)
    ≈ Ret (σ, tt).
Proof. intros. first [reflexivity | mem_compute]. Qed.

(** ** A whole function call

    [denote_function df args] pushes a frame (a memory frame; a stack frame
    binding [df_args df] to [args]; an empty varargs allocation), runs the
    body under [run_exc], and pops the frame. The body is given for the
    varargs pointer [varg] that the allocation returned, and may only change
    the memory's provenance counter. *)

Lemma runF_function_core : forall fundefs df args bs mem fs heap p p' fr stk g env' v varg,
  combine_lists_varargs (df_args df) args = raise_ret (bs, []) ->
  (handle_memory memM_interp (Alloca (DTYPE_Struct true []) 1 None) (mkState (mkMemoryStack mem (Snoc fs []) heap) p)
     : itree MCFGEbot _)
    ≈ Ret (mkState (mkMemoryStack mem (Snoc fs []) heap) (next_provenance p), DVALUE_Base (DVALUE_Pointer varg)) ->
  runX fundefs (denote_cfg_map (ocfg_map (blks (df_instrs df))) (df_instrs df) (Some varg))
    (ST (mkState (mkMemoryStack mem (Snoc fs []) heap) (next_provenance p))
        (fold_right (fun '(x, dv) => Maps.add x dv) Maps.empty bs) None (Some "") (fr :: stk) g)
    ≈ Ret (ST (mkState (mkMemoryStack mem (Snoc fs []) heap) p') env' None (Some "") (fr :: stk) g, inr v) ->
  runF fundefs (denote_function df args) (mkState (mkMemoryStack mem fs heap) p, ((fr, stk), g))
    ≈ Ret ((mkState (mkMemoryStack mem fs heap) p', ((fr, stk), g)), inr v).
Proof.
  intros * Hargs Halloca Hbody.
  unfold denote_function, push_call_frame, pop_call_frame. rewrite Hargs.
  Opaque denote_cfg_map ocfg_map run_exc runF runX.
  cbn.
  Transparent denote_cfg_map ocfg_map run_exc runF runX.
  (* push the frame *)
  eapply runF_bind_step.
  { eapply runF_bind_step; [apply runF_ret |]. cbn.
    eapply runF_bind_step; [apply runF_ret |]. cbn.
    eapply runF_bind_step; [eapply runF_mem_eq; apply mem_push_eq |].
    eapply runF_bind_step; [apply runF_stack_push |].
    eapply runF_bind_step; [eapply runF_mem_eq; exact Halloca |].
    eapply runF_bind_step; [eapply runF_mem_eq; apply store_empty_eq |].
    apply runF_ret. }
  (* run the body *)
  eapply runF_bind_step; [exact Hbody |].
  (* pop the frame *)
  eapply runF_bind_step.
  { eapply runF_bind_step; [apply runF_stack_pop |]. eapply runF_mem_eq. apply mem_pop_eq. }
  apply runF_ret.
Qed.

(** The two forms used in practice: the final provenance counter is known, or
    it is existential (the body made calls). *)
Lemma runF_function : forall fundefs df args bs mem fs heap p p' fr stk g v,
  combine_lists_varargs (df_args df) args = raise_ret (bs, []) ->
  (forall varg, exists env',
    runX fundefs (denote_cfg_map (ocfg_map (blks (df_instrs df))) (df_instrs df) (Some varg))
      (ST (mkState (mkMemoryStack mem (Snoc fs []) heap) (next_provenance p))
          (fold_right (fun '(x, dv) => Maps.add x dv) Maps.empty bs) None (Some "") (fr :: stk) g)
      ≈ Ret (ST (mkState (mkMemoryStack mem (Snoc fs []) heap) p') env' None (Some "") (fr :: stk) g, inr v)) ->
  runF fundefs (denote_function df args) (mkState (mkMemoryStack mem fs heap) p, ((fr, stk), g))
    ≈ Ret ((mkState (mkMemoryStack mem fs heap) p', ((fr, stk), g)), inr v).
Proof.
  intros * Hargs Hbody.
  destruct (alloca_empty_eq mem (Snoc fs []) heap p) as [varg Halloca].
  destruct (Hbody varg) as [env' Hb].
  exact (runF_function_core fundefs df args bs mem fs heap p p' fr stk g env' v varg Hargs Halloca Hb).
Qed.

Lemma runF_function_ex : forall fundefs df args bs mem fs heap p fr stk g v,
  combine_lists_varargs (df_args df) args = raise_ret (bs, []) ->
  (forall varg, exists env' p',
    runX fundefs (denote_cfg_map (ocfg_map (blks (df_instrs df))) (df_instrs df) (Some varg))
      (ST (mkState (mkMemoryStack mem (Snoc fs []) heap) (next_provenance p))
          (fold_right (fun '(x, dv) => Maps.add x dv) Maps.empty bs) None (Some "") (fr :: stk) g)
      ≈ Ret (ST (mkState (mkMemoryStack mem (Snoc fs []) heap) p') env' None (Some "") (fr :: stk) g, inr v)) ->
  exists p', runF fundefs (denote_function df args) (mkState (mkMemoryStack mem fs heap) p, ((fr, stk), g))
    ≈ Ret ((mkState (mkMemoryStack mem fs heap) p', ((fr, stk), g)), inr v).
Proof.
  intros * Hargs Hbody.
  destruct (alloca_empty_eq mem (Snoc fs []) heap p) as [varg Halloca].
  destruct (Hbody varg) as [env' [p' Hb]]. exists p'.
  exact (runF_function_core fundefs df args bs mem fs heap p p' fr stk g env' v varg Hargs Halloca Hb).
Qed.

(** A function definition as [denote_function] takes it. *)
Definition cfg_def (d : definition dtyp (LLVMAst.block dtyp * list (LLVMAst.block dtyp))) : definition dtyp (cfg dtyp) :=
  {| df_prototype := df_prototype d; df_args := df_args d; df_instrs := cfg_of_definition d |}.

(** * The top-level tree *)

(** ** Running top-level trees (no calls left to resolve) *)

#[global] Instance interp_mcfg_eutt {R} : Proper (eutt eq ==> eq ==> eutt eq) (@interp_mcfg _ R).
Proof.
  repeat intro; subst. unfold interp_mcfg, interp_intrinsics.
  eapply eutt_interp_state_eq; [| reflexivity]. eapply eutt_interp'. exact H.
Qed.

Lemma runM_ret : forall {R} (x : R) s, interp_mcfg (Ret x) s ≈ Ret (s, x).
Proof. intros. unfold interp_mcfg, interp_intrinsics. rewrite interp_ret, interp_state_ret. reflexivity. Qed.

Lemma runM_bind : forall {R S} (t : MCFGtop R) (k : R -> MCFGtop S) s,
  interp_mcfg (ITree.bind t k) s ≈ ITree.bind (interp_mcfg t s) (fun sx => interp_mcfg (k (snd sx)) (fst sx)).
Proof. intros. unfold interp_mcfg, interp_intrinsics. rewrite interp_bind, interp_state_bind. reflexivity. Qed.

Lemma runM_bind_step : forall R S (t : MCFGtop R) (k : R -> MCFGtop S) s s' a r,
  interp_mcfg t s ≈ Ret (s', a) -> interp_mcfg (k a) s' ≈ r -> interp_mcfg (ITree.bind t k) s ≈ r.
Proof. intros. rewrite runM_bind, H, Eqit.bind_ret_l. cbn. exact H0. Qed.

Lemma runM_gread : forall x v m ls g,
  Maps.lookup x g = Some v -> interp_mcfg (gread x) (m, (ls, g)) ≈ Ret ((m, (ls, g)), v).
Proof.
  intros. unfold interp_mcfg, interp_intrinsics, gread.
  rewrite interp_trigger. cbn. unfold F_trigger. rewrite interp_state_trigger. cbn.
  cbn in H. rewrite H. repeat (first [rewrite Eqit.bind_ret_l | rewrite Eqit.bind_bind | rewrite tau_eutt]; cbn).
  reflexivity.
Qed.

Lemma runM_address : forall df p m ls g,
  Maps.lookup (dc_name (df_prototype df)) g = Some (DVALUE_Base (DVALUE_Pointer p)) ->
  interp_mcfg (address_one_function df) (m, (ls, g)) ≈ Ret ((m, (ls, g)), (ptr_to_int p, denote_function df)).
Proof.
  intros. unfold address_one_function. eapply runM_bind_step; [apply runM_gread; exact H |]. apply runM_ret.
Qed.

Lemma runM_denote_mcfg : forall fundefs dt fv args s,
  interp_mcfg (denote_mcfg fundefs dt fv args) s = runF fundefs (mcfg_ctx fundefs _ (Call dt fv args)) s.
Proof. reflexivity. Qed.

(** ** Reflection through a boolean check

    Normalizing a whole interpreter state with [vm_compute] does not
    terminate in reasonable time, so runs are certified through a boolean
    check on the final state. *)

Definition run_check {E R} (n : nat) (t : itree E R) (f : R -> bool) : bool :=
  match run n t with Done r => f r | _ => false end.

Lemma run_check_sound : forall {E R} n (t : itree E R) f,
  run_check n t f = true -> exists r, t ≈ Ret r /\ f r = true.
Proof.
  intros * H. unfold run_check in H. destruct (run n t) eqn:Hrun; [| discriminate | discriminate].
  exists r. split; [apply (run_sound n); exact Hrun | exact H].
Qed.

Definition ptr_of_dv (dv : option dvalue) : option ptr :=
  match dv with Some (DVALUE_Base (DVALUE_Pointer p)) => Some p | _ => None end.

Lemma ptr_of_dv_inv : forall o p, ptr_of_dv o = Some p -> o = Some (DVALUE_Base (DVALUE_Pointer p)).
Proof.
  intros o p H. destruct o as [d |]; [| discriminate]. destruct d as [b | |]; try discriminate.
  destruct b; try discriminate. cbn in H. inversion H. reflexivity.
Qed.


(** ** The function map *)

Lemma lookup_defn_1 : forall (a b c : ptr) (f1 f2 f3 : function_denotation),
  lookup_defn (DVALUE_Base (DVALUE_Pointer a)) (IP.of_list [(ptr_to_int a, f1); (ptr_to_int b, f2); (ptr_to_int c, f3)]) = Some f1.
Proof.
  intros. unfold lookup_defn, lookup, IP.of_list. cbn [fold_right]. unfold IP.uncurry. cbn [fst snd].
  rewrite IP.F.add_eq_o; reflexivity.
Qed.

Lemma lookup_defn_2 : forall (a b c : ptr) (f1 f2 f3 : function_denotation),
  ptr_to_int a <> ptr_to_int b ->
  lookup_defn (DVALUE_Base (DVALUE_Pointer b)) (IP.of_list [(ptr_to_int a, f1); (ptr_to_int b, f2); (ptr_to_int c, f3)]) = Some f2.
Proof.
  intros. unfold lookup_defn, lookup, IP.of_list. cbn [fold_right]. unfold IP.uncurry. cbn [fst snd].
  rewrite IP.F.add_neq_o by exact H. rewrite IP.F.add_eq_o; reflexivity.
Qed.

Lemma lookup_defn_3 : forall (a b c : ptr) (f1 f2 f3 : function_denotation),
  ptr_to_int a <> ptr_to_int c -> ptr_to_int b <> ptr_to_int c ->
  lookup_defn (DVALUE_Base (DVALUE_Pointer c)) (IP.of_list [(ptr_to_int a, f1); (ptr_to_int b, f2); (ptr_to_int c, f3)]) = Some f3.
Proof.
  intros. unfold lookup_defn, lookup, IP.of_list. cbn [fold_right]. unfold IP.uncurry. cbn [fst snd].
  rewrite IP.F.add_neq_o by exact H. rewrite IP.F.add_neq_o by exact H0. rewrite IP.F.add_eq_o; reflexivity.
Qed.

(** * Automation for basic blocks

    In Ltac patterns, [≈] resolves to ExtLib's [eq1] (the [monad_scope]
    notation) rather than to [eutt eq], so the patterns below spell out
    [eutt eq].

    A program-specific proof restates each block of its program as a named
    definition (checked against the program by [reflexivity]), registers
    these with [Hint Unfold ... : blocks], and registers the corresponding
    [RM.find (Name "b") (ocfg_map bks) = Some _] lemmas with
    [Hint Extern 0 (RM.find (Name "b") (ocfg_map bks) = Some _) => exact lemma : find_blocks].
    [run_block] then executes a block made of integer operations,
    comparisons, branches and calls (see [run_callee]). *)

Create HintDb blocks.
Create HintDb find_blocks.

(** Side conditions "the operands fit in 64 bits". *)
Ltac bounds := unfold two64, two63, bytes8 in *; first [lia | nia].

(** [eval_iop]/[eval_icmp] on 64-bit values, with a [Z] result. *)
(* Program-specific evaluations (redefine with [Ltac eval_op_extra ::= ...]). *)
Ltac eval_op_extra := fail.

Ltac eval_op :=
  unfold dvZ;
  first [ rewrite eval_iop_mul; rewrite mul_repr64 by bounds
        | rewrite eval_iop_add; rewrite add_repr64 by bounds
        | rewrite eval_iop_sub; rewrite sub_repr64 by bounds
        | rewrite eval_iop_urem by (rewrite unsigned_repr64 by bounds; lia); rewrite modu_repr64 by bounds
        | rewrite eval_iop_udiv by (rewrite unsigned_repr64 by bounds; lia); rewrite divu_repr64 by bounds
        | eval_op_extra
        | rewrite eval_icmp_ult; rewrite ltu_repr64 by bounds
        | rewrite eval_icmp_ugt; rewrite ltu_repr64 by bounds
        | rewrite eval_icmp_eq; rewrite eq_repr64 by bounds ];
  reflexivity.

(** Expressions made of locals, globals, literals, [ibinop]s and [icmp]s.

    All the tactics below dispatch syntactically on the construct at hand
    ([lazymatch]) rather than trying lemmas in turn: a failing [apply] makes
    the unifier unfold the itree denotations, which does not terminate in
    practice. The sugar of [P]/[LL] is unfolded by [unblk] first. *)
Ltac run_exp :=
  lazymatch goal with
  | |- eutt eq (runX _ (denote_exp' _ (EXP_Integer _)) _) _ => apply runX_exp_lit
  | |- eutt eq (runX _ (denote_exp' _ (EXP_Ident (ID_Local _))) _) _ =>
      apply runX_exp_local; simpl_lookup; first [reflexivity | eassumption]
  | |- eutt eq (runX _ (denote_exp' _ (EXP_Ident (ID_Global _))) _) _ =>
      apply runX_exp_global; simpl_lookup; first [reflexivity | eassumption]
  | |- eutt eq (runX _ (denote_exp' _ (OP_IBinop _ _ _ _)) _) _ => eapply runX_exp_ibinop; [run_exp | run_exp | eval_op]
  | |- eutt eq (runX _ (denote_exp' _ (OP_ICmp _ _ _ _ _)) _) _ => eapply runX_exp_icmp; [run_exp | run_exp | eval_op]
  end.

(** The specification of a callee, for [call] instructions. Program-specific
    proofs redefine it with [Ltac run_callee ::= ...]; it faces a goal
    [runF _ (denote_function df args) s ≈ Ret (_, inr _)]. *)
Ltac run_callee := fail "run_callee: no callee specification (redefine it with Ltac run_callee ::= ...)".

Ltac run_instr :=
  lazymatch goal with
  | |- eutt eq (runX _ (denote_instr (_, INSTR_Op _, _) _) _) _ => eapply runX_instr_op; run_exp
  | |- eutt eq (runX _ (denote_instr (_, INSTR_Call _ _ _ _, _) _) _) _ =>
      eapply runX_instr_call; [reflexivity | run_exp | simpl_lookup; eassumption | eassumption | run_callee]
  end.

Ltac run_code :=
  lazymatch goal with
  | |- eutt eq (runX _ (denote_code [] _) _) _ => apply runX_code_nil
  | |- eutt eq (runX _ (denote_code (_ :: _) _) _) _ => eapply runX_code_cons; [run_instr | run_code]
  end.

Ltac run_term :=
  lazymatch goal with
  | |- eutt eq (runX _ (denote_terminator (_, TERM_Br _ _ _, _)) _) _ => eapply runX_term_br; run_exp
  | |- eutt eq (runX _ (denote_terminator (_, TERM_Ret _, _)) _) _ => eapply runX_term_ret; run_exp
  | |- eutt eq (runX _ (denote_terminator (_, TERM_Br_1 _, _)) _) _ => apply runX_term_br1
  end.

Ltac run_phis :=
  lazymatch goal with
  | |- eutt eq (runX _ (denote_phis _ []) _) _ => apply runX_phis_nil
  | |- _ => eapply runX_phis;
            [ repeat (eapply Forall2_cons; [eapply runX_phi; [reflexivity | run_exp] |]); apply Forall2_nil
            | cbn [fold_left]; reflexivity ]
  end.

(** Expose the phis, code and terminator of a restated block, down to the
    [LLVMAst] constructors. *)
Ltac unblk :=
  autounfold with blocks;
  cbv [blk_phis blk_code blk_term map P.block P.set P.call P.phi P.br P.br_if P.ret P.var P.lit P.global P.lbl
       P.mul P.urem P.icmp LL.add LL.int_lit LL.local LL.assign LL.ret LL.br_if LL.block].

(** [runX _ (denote_block bk from va) s ≈ Ret (?s', inr ?r)]. The phis may be
    given by a hypothesis (when [from] is only known by cases). *)
Ltac run_block :=
  eapply runX_block;
  [ lazymatch goal with
    | H : eutt eq (runX _ (denote_phis ?f ?ps) ?s) _ |- eutt eq (runX _ (denote_phis ?f ?ps) ?s) _ => exact H
    | |- _ => unblk; run_phis
    end
  | unblk; run_code
  | unblk; run_term ].

(** The [find_blocks] hints must be syntactic ([Hint Extern] on the block name
    and the block list), so that no wrong lemma is ever tried. *)
Ltac find_block := cbv beta iota; solve [eauto with find_blocks].

(** Enter the body of a function whose block list is [bks] and whose entry
    block is [entry], in the forms the [find_blocks] hints expect. *)
Ltac enter_cfg bks entry := eapply (runX_cfg_named _ _ bks entry); [reflexivity | reflexivity |].

(** One CFG step. [H] is a run of the current block ([run_block]); the [_block]
    forms run it on the spot. *)
Ltac ocfg_jump H := erewrite runX_ocfg_jump; [| find_block | exact H].
Ltac ocfg_ret H := erewrite runX_ocfg_ret; [| find_block | exact H].
Ltac ocfg_jump_block := erewrite runX_ocfg_jump; [| find_block | run_block].
Ltac ocfg_ret_block := erewrite runX_ocfg_ret; [| find_block | run_block].

(** [next_block H2 bk from after H1]: run block [bk], entered from [from], in
    the state in which [H1] left the previous block. *)
Tactic Notation "next_block" ident(H2) constr(bk) constr(from) "after" ident(H1) :=
  lazymatch type of H1 with
  | eutt eq (runX ?fd (denote_block _ _ ?va) _) (Ret (?S, _)) =>
      eassert (H2 : runX fd (denote_block bk from va) S ≈ Ret (_, inr _)) by run_block
  end.

(** The integer operations were made opaque above so that [cbn] never unfolds
    them in symbolic states; program-specific proof files should declare the
    same [Opaque] at their start and restore it at their end. *)
Transparent Integers.repr Integers.unsigned Integers.mul Integers.add Integers.sub Integers.modu Integers.divu Integers.shru
  Integers.eq Integers.ltu Integers.zero Integers.one.
