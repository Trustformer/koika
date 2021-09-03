(*! Proofs about our RISC-V implementation !*)
Require Import Coq.Program.Equality.
Require Import Koika.BitsToLists Koika.Frontend Koika.Instructions Koika.Logs
  Koika.ProgramTactics Koika.SimpleTypedSemantics Koika.Std Koika.UntypedLogs
  UntypedIndSemantics Koika.UntypedSemantics.
Require Export rv.Stack rv.RVCore rv.rv32 rv.rv32i.

Ltac destr_in H :=
  match type of H with
  | context[match ?a with _ => _ end] => destruct a eqn:?
  end.

Ltac destr :=
  match goal with
  |- context[match ?a with _ => _ end] => destruct a eqn:?; try congruence
  end.

Ltac inv H := inversion H; try subst; clear H.

Module RVProofs.
  Context (ext_sigma : RV32I.ext_fn_t -> BitsToLists.val -> BitsToLists.val).
  Context (ext_Sigma : RV32I.ext_fn_t -> ExternalSignature).
  Context {REnv : Env RV32I.reg_t}.

  Definition cycle (r: env_t ContextEnv (fun _ : RV32I.reg_t => BitsToLists.val)) :=
    UntypedSemantics.interp_cycle RV32I.rv_urules r ext_sigma rv_schedule.

  Definition env_type := env_t REnv RV32I.R.
  Definition initial_env := create REnv RV32I.r.

  Definition CEnv := @ContextEnv RV32I.reg_t RV32I.FiniteType_reg_t.
  Print RV32I.FiniteType_reg_t.
  Print Options.
  Set NativeCompute Profiling.
  Definition initial_context_env := CEnv.(create) (RV32I.r).

  Compute @initial_context_env.
  Definition f_init := fun x => val_of_value (initial_context_env.[x]).

  Theorem osef : initial_context_env.[RV32I.on_off] = Ob~0.
  Proof. trivial. Qed.

  Definition initial_context_env_val := ContextEnv.(create) (f_init).
  Theorem osef2 : initial_context_env_val.[RV32I.on_off] = @BitsToLists.val_of_value (bits_t 1) Ob~0.
  Proof. trivial. Qed.

  (* TODO *)
  Definition state_step_1 := cycle initial_context_env_val .

  Lemma log_app_empty_r:
    forall {V} (l: @_ULog V _ REnv), log_app l log_empty = l.
  Proof.
    unfold log_app. unfold map2.
    intros.
    etransitivity.
    2: apply create_getenv_id.
    apply create_funext. intros. unfold log_empty.
    rewrite getenv_create. rewrite app_nil_r. auto.
  Qed.

  Theorem tick_preserves_on_off :
    forall ctx ctx',
    UntypedIndSemantics.interp_cycle RV32I.rv_urules ctx ext_sigma (Tick |> done) ctx' ->
    getenv REnv ctx' RV32I.on_off = getenv REnv ctx RV32I.on_off.
  Proof.
    intros ctx ctx' A.
    inv A. inv H. inv H0.
    inv H4.
    - inv H0.
      simpl RV32I.rv_urules in H.
      unfold RV32I.tick in H.
      dependent destruction H.
      dependent destruction H.
      dependent destruction H.
      dependent destruction H.
      dependent destruction H.
      dependent destruction H0.
      dependent destruction H2.
      dependent destruction H2.
      dependent destruction H2_.
      dependent destruction H2_0.
      assert (action_log' = (log_cons RV32I.halt {| kind := Logs.LogRead; port := P0; val := Bits 0 [] |} log_empty)).
      {
        clear - H1.
        destruct val_eq_dec; simpl in *.
        dependent destruction H1.
        dependent destruction H1.
        auto.
      }
      subst. clear.
      unfold commit_update.
      rewrite getenv_create.
      unfold latest_write. unfold log_find.
      rewrite SemanticProperties.find_none_notb. auto. intros.
      rewrite log_app_empty_r in H.
      unfold log_cons in H.
      rewrite get_put_neq in H by congruence.
      rewrite get_put_neq in H by congruence.
      rewrite get_put_neq in H by congruence.
      setoid_rewrite getenv_create in H. easy.
    - inv H0. unfold commit_update.
      rewrite getenv_create.
      unfold latest_write. unfold log_find.
      rewrite SemanticProperties.find_none_notb. auto. intros.
      setoid_rewrite getenv_create in H0. easy.
  Qed.

  Lemma getenv_ulogapp:
    forall (V reg_t: Type) (REnv: Env reg_t) (l l': UntypedLogs._ULog) idx,
    REnv.(getenv) (@UntypedLogs.log_app V reg_t REnv l l') idx =
    REnv.(getenv) l idx ++ REnv.(getenv) l' idx.
  Proof.
    intros.
    unfold log_app, map2; intros; rewrite getenv_create; reflexivity.
  Qed.

  Lemma find_latest_write_top:
    forall (V reg_t : Type) (REnv : Env reg_t) (l l' : UntypedLogs._ULog) x px xval,
    @UntypedLogs.latest_write V reg_t REnv (UntypedLogs.log_app
      (UntypedLogs.log_cons x {| kind := Logs.LogWrite; port := px; val := xval |} l) l'
    ) x = Some xval.
  Proof.
    intros.
    unfold latest_write.
    unfold log_find.
    unfold RLog. (* Effects invisible without Set Printing All but required *)
    rewrite getenv_ulogapp.
    unfold log_cons.
    rewrite get_put_eq.
    simpl.
    reflexivity.
  Qed.

  (* Lemma registers_contents_match_type: *)
  (*   forall x y reg_t, *)
  (*   reg_t sz *)
  (*   getenv REnv ctx RV32I.cycle_count = y -> *)

  (*   ) *)
  (*   Bits (type_sz (RV32I.R RV32I.cycle_count)) y *)

  Theorem tick_overwrites_cycle_count:
    forall ctx ctx',
    UntypedIndSemantics.interp_cycle RV32I.rv_urules ctx ext_sigma (Tick |> done) ctx' ->
    getenv REnv ctx RV32I.halt = @val_of_value (bits_t 1) Ob~0 ->
    getenv REnv ctx RV32I.cycle_count <> getenv REnv ctx' RV32I.cycle_count.
  Proof.
    intros.
    inv H. inv H1. inv H. inv H5. inv H1. inv H0.
    simpl RV32I.rv_urules in H.
    - dependent destruction H.
      dependent destruction H.
      dependent destruction H.
      dependent destruction H.
      dependent destruction H.
      dependent destruction H0.
      dependent destruction H2.
      dependent destruction H2.
      dependent destruction H2_.
      dependent destruction H2_0.
      unfold commit_update. rewrite getenv_create.
      rewrite find_latest_write_top.
      simpl in H2.
      Check (ctx).
      Check (getenv REnv ctx RV32I.cycle_count).
      (* assert ( *)
      (*   exists x, *)
      (*   getenv REnv ctx RV32I.cycle_count *)
      (*   = Bits (type_sz (RV32I.R RV32I.cycle_count)) x *)
      (* ). { *)
      (*   destruct (getenv REnv ctx RV32I.cycle_count). *)
      (*   - exists v. *)
      (*   Check ubits_of_value_len. *)
      (*   rewrite ubits_of_value_len. *)
      (*   - exists []. *)
      (* } *)
      (* destruct (getenv REnv ctx RV32I.cycle_count); inv H2. *)
      (* Set Printing All. *)
      (* assert () *)
      (* induction v. *)
      (* (1* v is not constrained in any way, yet we need to use the fact that its size is known *1) *)
      (* + simpl. unfold vect_to_list. simpl. *)
  Admitted.

  Variable decode_opcode : list bool -> instruction.
  Variable decode_rd : list bool -> RV32I.Rf.reg_t.
  Variable decode_rs1 : list bool -> RV32I.Rf.reg_t.
  Variable decode_imm : list bool -> BitsToLists.val.

  Definition val_add (v1 v2: BitsToLists.val) :=
    match v1, v2 with
    | Bits sz1 l1, Bits sz2 l2 => Some (Bits sz1 l1)
    | _, _ => None
    end.

  Goal
    forall ctx bits_instr rs1 rd vimm l l',
      getenv REnv ctx RV32I.halt = Bits 1 [false] ->
      getenv REnv ctx (RV32I.d2e RV32I.fromDecode.data0) = Bits 32 bits_instr ->
      getenv REnv ctx (RV32I.d2e RV32I.fromDecode.valid0) = Bits 1 [true] ->
      decode_opcode bits_instr = ADDI_32I ->
      decode_rd bits_instr = rd ->
      decode_rs1 bits_instr = rs1 ->
      decode_imm bits_instr = vimm ->
      UntypedIndSemantics.interp_rule ctx ext_sigma l RV32I.execute l' ->
      (* UntypedIndSemantics.interp_cycle RV32I.rv_urules ctx ext_sigma (Execute |> done) ctx' -> *)
      let ctx1 := commit_update ctx l in
      let ctx2 := commit_update ctx l' in
      Some (getenv REnv ctx2 (RV32I.rf rd)) = val_add (getenv REnv ctx1 (RV32I.rf rs1)) vimm.
  Proof.
    intros ctx bits_instr rs1 rd vimm l l' NoHalt BitsInstr InstrValid Opcode RD RS1 IMM IR ctx1 ctx2.
    dependent destruction IR.
    dependent destruction H.
    dependent destruction H.
    destruct b.
    - dependent destruction H0.
    - dependent destruction H0.
      dependent destruction H1.
      dependent destruction H1_.
      dependent destruction H0. simpl in *.
      dependent destruction H1_.
      dependent destruction H1_1.
      dependent destruction H1_1_1.
      dependent destruction H1_1_1_1.
      dependent destruction H1_1_1_1.
      dependent destruction H.
      simpl in *.
      dependent destruction H1_1_1_1.
      simpl in *.
      dependent destruction H.
  Admitted.

  (* Goal *)
  (*   forall ctx bits_instr rs1 rd vimm ctx', *)
  (*     getenv REnv ctx RV32I.halt = Bits 1 [false] -> *)
  (*     getenv REnv ctx (RV32I.d2e RV32I.fromDecode.data0) = Bits 32 bits_instr -> *)
  (*     getenv REnv ctx (RV32I.d2e RV32I.fromDecode.valid0) = Bits 1 [true] -> *)
  (*     decode_opcode bits_instr = ADDI_32I -> *)
  (*     decode_rd bits_instr = rd -> *)
  (*     decode_rs1 bits_instr = rs1 -> *)
  (*     decode_imm bits_instr = Bits 12 vimm -> *)
  (*     UntypedIndSemantics.interp_cycle RV32I.rv_urules ctx ext_sigma rv_schedule ctx' -> *)
  (*     UntypedIndSemantics.interp_cycle RV32I.rv_urules ctx ext_sigma (Execute |> done) ctx' -> *)
  (*     getenv REnv ctx' rd = getenv REnv ctx rs1 + vimm. *)
