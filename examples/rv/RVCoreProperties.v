(*! Proofs about our RISC-V implementation !*)

Require Import Koika.BitsToLists Koika.Frontend Koika.Logs Koika.ProgramTactics
  Koika.SimpleTypedSemantics Koika.Std Koika.UntypedLogs Koika.UntypedSemantics.
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

  Require Import UntypedIndSemantics.
  Require Import Coq.Program.Equality.

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

  Goal
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

  Require Import Instructions.
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

  Qed.



  Goal
    forall ctx bits_instr rs1 rd vimm ctx',
      getenv REnv ctx RV32I.halt = Bits 1 [false] ->
      getenv REnv ctx (RV32I.d2e RV32I.fromDecode.data0) = Bits 32 bits_instr ->
      getenv REnv ctx (RV32I.d2e RV32I.fromDecode.valid0) = Bits 1 [true] ->
      decode_opcode bits_instr = ADDI_32I ->
      decode_rd bits_instr = rd ->
      decode_rs1 bits_instr = rs1 ->
      decode_imm bits_instr = Bits 12 vimm ->
      UntypedIndSemantics.interp_cycle RV32I.rv_urules ctx ext_sigma rv_schedule ctx' ->
      (* UntypedIndSemantics.interp_cycle RV32I.rv_urules ctx ext_sigma (Execute |> done) ctx' -> *)
      getenv REnv ctx' rd = getenv REnv ctx rs1 + vimm.


  Check UntypedIndSemantics.interp_cycle RV32I.rv_urules .

  (* Set Printing All. *)
  (* Set Printing Width 20000. *)
  (* Set Printing Depth 20000. *)
  (* Time Compute (UntypedSemantics.interp_scheduler RV32I.rv_urules initial_context_env_val ext_sigma (Tick |> done)). *)

  Time Compute (UntypedSemantics.interp_cycle RV32I.rv_urules initial_context_env_val ext_sigma (Tick |> done)).
  Time Compute initial_context_env_val. (* 4.8s *)

  (* Check UntypedSemantics.interp_rule initial_context_env_val ext_sigma log_empty RV32I.do_nothing. *)
  (* Time Compute UntypedSemantics.interp_action initial_context_env_val ext_sigma nil log_empty log_empty RV32I.do_nothing. *)
  Time Compute UntypedSemantics.interp_action_2 initial_context_env_val ext_sigma nil log_empty log_empty RV32I.do_nothing.
  Time Compute (UntypedSemantics.interp_scheduler RV32I.rv_urules initial_context_env_val ext_sigma (EndExecution |> done)). (* 5.9s *)
  Time Compute initial_context_env_val.
  Time Compute ext_sigma.
  Time Compute log_empty.
  Compute ccreate finite_elements (fun k _ => f_init k).
  Time Compute UntypedSemantics.interp_cycle RV32I.rv_urules initial_context_env_val ext_sigma (done). (* 5s *)
  Time Compute UntypedSemantics.interp_cycle RV32I.rv_urules initial_context_env_val ext_sigma (UpdateOnOff |> done). (* 5.6s *)
  Time Compute UntypedSemantics.interp_rule initial_context_env_val ext_sigma log_empty RV32I.writeback. (* 11.2s *)
  Time Compute (UntypedSemantics.interp_scheduler RV32I.rv_urules initial_context_env_val ext_sigma (UpdateOnOff |> done)). (* 5.2s *)
  Time Compute (UntypedSemantics.interp_scheduler RV32I.rv_urules initial_context_env_val ext_sigma (Writeback |> done)). (* 26.7s *)
  Time Compute (UntypedSemantics.interp_scheduler RV32I.rv_urules initial_context_env_val ext_sigma (Tick |> done)). (* 61.3s *)
  Time Compute (UntypedSemantics.interp_scheduler RV32I.rv_urules initial_context_env_val ext_sigma (EndExecution |> done)). (* 5.9s *)
  Time Compute UntypedSemantics.interp_cycle RV32I.rv_urules initial_context_env_val ext_sigma (Writeback |> done). (* >500s, >15G *)
  Time Compute initial_context_env_val.
  Time Compute UntypedSemantics.interp_cycle RV32I.rv_urules initial_context_env_val ext_sigma (UpdateOnOff |> Writeback |> done). (* >200s *)
  Time Compute initial_context_env_val.
  Time Compute initial_context_env_val.
  Time Compute RV32I.do_nothing.

  Time Compute ContextEnv.(create).
Time Compute @BitsToLists.val_of_value (bits_t 32000) (Bits.of_nat 32000 1).
  Compute nil.
  Set Printing All.
  Compute RV32I.do_nothing.


  Time Compute UntypedSemantics.interp_rule initial_context_env_val ext_sigma log_empty RV32I.do_nothing.

  Time Compute UntypedSemantics.interp_action initial_context_env_val ext_sigma nil log_empty log_empty RV32I.do_nothing.
  Time Compute UntypedSemantics.interp_action initial_context_env_val ext_sigma nil log_empty log_empty RV32I.update_on_off.
  Time Compute UntypedSemantics.interp_action initial_context_env_val ext_sigma nil log_empty log_empty RV32I.writeback.
  Time Compute UntypedSemantics.interp_action initial_context_env_val ext_sigma nil log_empty log_empty RV32I.execute.
  Time Compute UntypedSemantics.interp_cycle.
  Time Compute UntypedSemantics.interp_cycle RV32I.rv_urules.

  Print CompactLogs.nonep.

  Theorem on_off_cycles_firstu:
    CompactLogs.nonep (UntypedSemantics.interp_action initial_context_env_val ext_sigma nil log_empty log_empty RV32I.update_on_off) = false.
  Proof. trivial. Qed.

  Compute (cycle initial_context_env_val).[RV32I.on_off].

  Theorem on_off_cycles_first :
    initial_context_env_val.[RV32I.on_off]
    <> (cycle initial_context_env_val).[RV32I.on_off].
  Proof. vm_compute. trivial. Qed.

  Theorem add_adds :
    initial_context_env_val.[]

Module StackProofs.
  Definition rv_cycle
    (r: ContextEnv.(env_t) RV32I.R)
    (sigma : forall f, Sig_denote (RV32I.Sigma f))
  :=
  TypedSemantics.interp_cycle sigma RV32I.rv_rules rv_schedule r.

  Lemma extract_success_rewrite:
    forall {S F: Type} (res1 res2: result S F) pr1 pr2,
    res1 = res2 -> extract_success res1 pr1 = extract_success res2 pr2.
  Proof.
    intros. subst.
    refine (
      match pr1, pr2 with
      | eq_refl _, eq_refl _ => _
      end
    ).
    destruct res2; congruence.
  Qed.

  Lemma success_inj:
    forall {S F: Type} (x y: S), Success x = @Success S F y -> x = y.
  Proof. intros S F x y H. inv H; auto. Qed.

  Lemma cast_action'_eq:
    forall (pos_t fn_name_t var_t reg_t ext_fn_t : Type) (R : reg_t -> type)
           (Sigma : ext_fn_t -> ExternalSignature)
           (p: pos_t) (sig: tsig var_t) (tau1 tau2: type)
           (a: action pos_t var_t fn_name_t R Sigma sig tau1)
           (e: error_message var_t fn_name_t) a',
      cast_action' R Sigma p tau2 a e = Success a' ->
      exists p : tau1 = tau2,
        a' = eq_rect _ _ a _ p.
  Proof.
    unfold cast_action'. intros.
    destr_in H. subst.
    unfold eq_rect_r in H. simpl in H. inv H.
    exists eq_refl; reflexivity. inv H.
  Qed.

  Lemma cast_action_eq:
    forall (pos_t fn_name_t var_t reg_t ext_fn_t : Type) (R : reg_t -> type)
           (Sigma : ext_fn_t -> ExternalSignature)
           (p: pos_t) (sig: tsig var_t) (tau1 tau2: type)
           (a: action pos_t var_t fn_name_t R Sigma sig tau1)
           a',
      cast_action R Sigma p tau2 a = Success a' ->
      exists p : tau1 = tau2,
        a' = eq_rect _ _ a _ p.
  Proof.
    intros. unfold cast_action in H.
    eapply cast_action'_eq; eauto.
  Qed.


  Definition if_halt_eq : action (ext_fn_t:=RV32I.ext_fn_t) pos_t var_t fn_name_t RV32I.R RV32I.Sigma [] unit_t :=
    (If (Binop (PrimTyped.Eq (bits_t 1) false) (Read P0 RV32I.halt)
               (Const (tau:= bits_t 1) {| vhd := true; vtl := _vect_nil |}))
       (Fail unit_t) (Const (tau:=unit_t) _vect_nil)).

  Context {reg_t_eq_dec: EqDec RV32I.reg_t}.

  Lemma execute_overwrites_halt:
    forall (r: ContextEnv.(env_t) RV32I.R) sigma l,
      interp_rule r sigma log_empty
                  RV32I.tc_execute
                  = Some l ->
      log_existsb l RV32I.halt (fun k p =>
                                  match k with
                                    LogRead => false
                                  | LogWrite => true
                                  end
                               ) = true(*  -> *)
      (* let dbk := ContextEnv.(getenv) r (RV32I.d2e RV32I.fromDecode.data0) = dbk in *)
      (* let dInst :=  *)

        (* RV32I.isControlInst *)
  .
  Proof.
    intros.
    unfold interp_rule in H.
    destr_in H. 2: congruence.
    repeat destr_in H. inv H.
    unfold RV32I.tc_execute in Heqo.
    unfold desugar_action in Heqo.
    refine (
      match
        desugar_action' dummy_pos (fun r : RV32I.reg_t => r)
        (fun fn => fn) RV32I.execute
      with
         x => _
      end
    ).
    fold x in Heqo.
    refine ((
      match
        TypeInference.tc_action RV32I.R RV32I.Sigma dummy_pos [] unit_t x
      as r
      return (
        TypeInference.tc_action RV32I.R RV32I.Sigma dummy_pos [] unit_t x = r
        -> is_success r = true -> _
      ) with
      | Success s => fun H1 H2 => _
      | Failure f => fun H1 H2 => _
      end
    ) eq_refl eq_refl).
    2: (simpl in H2; congruence).
    rename Heqo into H0.
    erewrite extract_success_rewrite in H0. 2: apply H1.
    simpl (extract_success _ _) in H0.
    unfold TypeInference.tc_action in H1.
    destr_in H1. 2: congruence.
    clear H2.
    apply cast_action_eq in H1.
    destruct H1 as (p & EQ). subst s.
    revert Heqr0. simpl in x.
    unfold eq_rect in H0.
    destruct p.
    unfold desugar_action' in x.
    unfold RV32I.execute in x.
    simpl in x.
    unfold execALU32 in x. simpl in x.
    unfold RV32I.fromDecode.deq in x. simpl in x.
    unfold map_intf_body in x. vm_compute in x.
    unfold x. clear x.
    intro Heqr0.
    vm_compute in Heqr0.
    Set Printing Depth 20.
    Set Printing All.
    inv Heqr0.
    apply success_inj in Heqr0.
    subst.
    simpl projT1 in v.
    simpl projT2 in H0.

    inversion H0.
    apply Eqdep_dec.inj_pair2_eq_dec in H11.
    2:{
      apply eq_dec.
    }
    apply Eqdep_dec.inj_pair2_eq_dec in H7.
    apply Eqdep_dec.inj_pair2_eq_dec in H7.
    apply Eqdep_dec.inj_pair2_eq_dec in H8.
    apply Eqdep_dec.inj_pair2_eq_dec in H8.
    apply Eqdep_dec.inj_pair2_eq_dec in H8.
    assert (var = "res"). eapply EqdepFacts.eq_sigT_fst; eauto. subst.
    apply Eqdep_dec.inj_pair2_eq_dec in H8.
    simpl projT1 in *.
    apply Eqdep_dec.inj_pair2_eq_dec in H10. subst.
    apply Eqdep_dec.inj_pair2_eq_dec in H.
    all: try apply eq_dec. clear H0.
    subst.
    inv H12.
    apply Eqdep_dec.inj_pair2_eq_dec in H.
    apply Eqdep_dec.inj_pair2_eq_dec in H3.
    apply Eqdep_dec.inj_pair2_eq_dec in H7.
    apply Eqdep_dec.inj_pair2_eq_dec in H5.
    apply Eqdep_dec.inj_pair2_eq_dec in H3. subst.
    all: try apply eq_dec.
    inv H9.
    apply Eqdep_dec.inj_pair2_eq_dec in H6.
    apply Eqdep_dec.inj_pair2_eq_dec in H11.
    apply Eqdep_dec.inj_pair2_eq_dec in H12.
    apply Eqdep_dec.inj_pair2_eq_dec in H1.
    apply Eqdep_dec.inj_pair2_eq_dec in H6. subst.
    all: try apply eq_dec.
    inv H8.
    apply Eqdep_dec.inj_pair2_eq_dec in H4.
    apply Eqdep_dec.inj_pair2_eq_dec in H9.
    apply Eqdep_dec.inj_pair2_eq_dec in H9.
    apply Eqdep_dec.inj_pair2_eq_dec in H9.
    apply Eqdep_dec.inj_pair2_eq_dec in H12.
    apply Eqdep_dec.inj_pair2_eq_dec in H14. subst.
    all: try apply eq_dec.
    destruct (
      interp_action r sigma CtxEmpty log_empty log_empty RV32I.tc_end_execution
    ) eqn:?.
    2:{ Set Printing All. }
    destr_in H.
    inv H.
    unfold RV32I.tc_end_execution in H0.
    unfold desugar_action in H0.
    refine (
      match
        desugar_action' dummy_pos (fun r : RV32I.reg_t => r)
        (fun fn => fn) RV32I.end_execution
      with x => _ end
    ).
    fold x in H0.
    refine ((
      match
        TypeInference.tc_action RV32I.R RV32I.Sigma dummy_pos [] unit_t x
      as r
      return (
        TypeInference.tc_action RV32I.R RV32I.Sigma dummy_pos [] unit_t x = r
        -> is_success r = true -> _
      ) with
      | Success s => fun H1 H2 => _
      | Failure f => fun H1 H2 => _
      end
    ) eq_refl eq_refl).
    2: (simpl in H2; congruence).
    erewrite extract_success_rewrite in H0. 2: apply H1.
    simpl (extract_success _ _) in H0.
    unfold TypeInference.tc_action in H1.
    destr_in H1. 2: congruence.
    clear H2.
    apply cast_action_eq in H1.
    destruct H1 as (p & EQ). subst s.
    revert Heqr0. simpl in x.
    unfold eq_rect in H0.
    destruct p.
    unfold desugar_action' in x.
    unfold RV32I.end_execution in x.
    simpl in x.
    unfold x. clear x.
    intro Heqr0.
    simpl in Heqr0.
    apply success_inj in Heqr0.
    subst.
    simpl projT1 in v.
    simpl projT2 in H0.
    inversion H0.
    apply Eqdep_dec.inj_pair2_eq_dec in H11.
    2:{ apply eq_dec.  }
    apply Eqdep_dec.inj_pair2_eq_dec in H7.
    apply Eqdep_dec.inj_pair2_eq_dec in H7.
    apply Eqdep_dec.inj_pair2_eq_dec in H8.
    apply Eqdep_dec.inj_pair2_eq_dec in H8.
    apply Eqdep_dec.inj_pair2_eq_dec in H8.
    assert (var = "res"). eapply EqdepFacts.eq_sigT_fst; eauto. subst.
    apply Eqdep_dec.inj_pair2_eq_dec in H8.
    simpl projT1 in *.
    apply Eqdep_dec.inj_pair2_eq_dec in H10. subst.
    apply Eqdep_dec.inj_pair2_eq_dec in H.
    all: try apply eq_dec. clear H0.
    subst.
    inv H12.
    apply Eqdep_dec.inj_pair2_eq_dec in H.
    apply Eqdep_dec.inj_pair2_eq_dec in H3.
    apply Eqdep_dec.inj_pair2_eq_dec in H7.
    apply Eqdep_dec.inj_pair2_eq_dec in H5.
    apply Eqdep_dec.inj_pair2_eq_dec in H3. subst.
    all: try apply eq_dec.
    inv H9.
    apply Eqdep_dec.inj_pair2_eq_dec in H6.
    apply Eqdep_dec.inj_pair2_eq_dec in H11.
    apply Eqdep_dec.inj_pair2_eq_dec in H12.
    apply Eqdep_dec.inj_pair2_eq_dec in H1.
    apply Eqdep_dec.inj_pair2_eq_dec in H6. subst.
    all: try apply eq_dec.
    inv H8.
    apply Eqdep_dec.inj_pair2_eq_dec in H4.
    apply Eqdep_dec.inj_pair2_eq_dec in H9.
    apply Eqdep_dec.inj_pair2_eq_dec in H9.
    apply Eqdep_dec.inj_pair2_eq_dec in H9.
    apply Eqdep_dec.inj_pair2_eq_dec in H12.
    apply Eqdep_dec.inj_pair2_eq_dec in H14. subst.
    all: try apply eq_dec.
    apply Eqdep_dec.inj_pair2_eq_dec in H7.
    apply Eqdep_dec.inj_pair2_eq_dec in H7.
    apply Eqdep_dec.inj_pair2_eq_dec in H8.
    apply Eqdep_dec.inj_pair2_eq_dec in H8.
    apply Eqdep_dec.inj_pair2_eq_dec in H8.
    assert (var = "res"). eapply EqdepFacts.eq_sigT_fst; eauto. subst.
    apply Eqdep_dec.inj_pair2_eq_dec in H8.
    simpl projT1 in *.
    apply Eqdep_dec.inj_pair2_eq_dec in H10. subst.
    apply Eqdep_dec.inj_pair2_eq_dec in H.
    all: try apply eq_dec. clear H0.
    subst.
    2:{ intros. decide equality. apply EqDec_pair. }
    inversion H11.
    destruct H11. unfold eq_rect in e.
    cbn [projT1 projT2] in *.
    vm_compute in H0.
    Set Printing Depth 500.
    inv H0.
    unfold RV32I.tc_execute in H0.
    refine (
      match
        desugar_action' dummy_pos (fun r : RV32I.reg_t => r)
        (fun fn => fn) RV32I.execute
      with x => _ end
    ).
    fold x in H0.
    refine ((
      match
        TypeInference.tc_action RV32I.R RV32I.Sigma dummy_pos [] unit_t x
      as r
      return (
        TypeInference.tc_action RV32I.R RV32I.Sigma dummy_pos [] unit_t x = r
        -> is_success r = true -> _
      ) with
      | Success s => fun H1 H2 => _
      | Failure f => fun H1 H2 => _
      end
    ) eq_refl eq_refl).
    2: (simpl in H2; congruence).
    erewrite extract_success_rewrite in H0. 2: apply H1.
    simpl (extract_success _ _) in H0.
    unfold TypeInference.tc_action in H1.
    destr_in H1. 2: congruence.
    clear H2.
    apply cast_action_eq in H1.
    destruct H1 as (p & EQ). subst s.
    revert Heqr0. simpl in x.
    unfold eq_rect in H0.
    destruct p.
    unfold desugar_action' in x. cbn in x.
    unfold x. clear x.
    intro Heqr0.
    simpl in Heqr0.
    vm_compute in Heqr0.
    apply success_inj in Heqr0.
    subst s0. simpl projT1 in v.
    simpl projT2 in H0.
    match type of H0 with
    | context [Seq ?a1 ?a2] => set(XX:=a2); fold XX in H0
    end.
    inv H0.
    unfold eq_rect in Heqo.
    destruct p.
    assert (p = eq_refl).
    rewrite <- Heqr0 in Heqo.
    revert H1; rewrite <- Heqr0; clear Heqr0.
    simpl projT2.
    intro Hcast; vm_compute in Hcast; inv Hcast.
    Heqr0.
    vm_compute in H1. inv H1. simpl in H2.
    cbn beta delta iota zeta in H.
    revert H.
    unfold opt_bind.
    destruct may_read.
    - rewrite H0.
      rewrite (proj2 (beq_dec_iff _ _ _)). intro A; inv A. reflexivity.
      reflexivity.
    - congruence.
    unfold x in H1. vm_compute in H1.
    interp_action_t.
  Qed.

  Theorem stack_0_implies_no_setting_halt :
    (r: ContextEnv.(env_t) RV32I.R)
    (sigma : forall f, Sig_denote (RV32I.Sigma f)),
     r.(getenv) halt = 0 -> (rv_cycle r sigma).(getenv) halt = 1 ->

  Theorem forall_calls :
    forall (r : ContextEnv.(env_t) RV32I.R)
    (sigma : forall f, Sig_denote (RV32I.Sigma f)),
    rv_cycle r sigma.
  Proof.
    vm_compute.
  .

  Import StackF.
  Definition default := ContextEnv.(create) r.

  Definition is_stack_empty (reg : ContextEnv.(env_t) R) :=
    ContextEnv.(getenv) reg size = Bits.zero.

  Definition is_stack_full (reg : ContextEnv.(env_t) R) :=
    ContextEnv.(getenv) reg size = (Bits.of_nat index_sz capacity).

  Definition Sigma := RV32I.Sigma.

  Ltac unfolds :=
    unfold desugar_action, desugar_action', TypeInference.tc_action,
    TypeInference.tc_action, type_action, projT2, projT2, lift_fn1_tc_result,
    lift_fn2_tc_result, lift_fn1_tc_result, lift_fn2_tc_result, projT1, projT2,
    cast_action, cast_action' in *.

  Theorem self_implies_left : forall (n : nat), n = n ->
    Nat.eq_dec n n = left eq_refl.
  Proof.
    intros. induction n.
    - trivial.
    - simpl. assert (n = n) by trivial.
      apply IHn in H0. rewrite H0. trivial.
  Qed.

  Theorem type_eq_dec_left :
    forall (x y : type) (Heq: x = y),
      eq_dec x y = left (eq_rect x (fun y => eq x y) eq_refl _ Heq).
  Proof.
    intros. subst.
    destruct (eq_dec y y). simpl.
    f_equal. apply Eqdep_dec.UIP_dec. apply eq_dec.
    congruence.
  Qed.

  Theorem pop_returns_one_when_stack_empty :
    forall env Gamma sched_log action_log action_log_new v Gamma_new,
    interp_action env Sigma Gamma sched_log action_log
      (tc_function R Sigma pop) = Some (action_log_new, v, Gamma_new)
      -> is_stack_empty env -> v = Ob~1.
  Proof.
    intros env Gamma sched_log action_log action_log_new v Gamma_new.
    unfold desugar_action.
    intros.
    refine (
      match
        desugar_action' dummy_pos (fun r : reg_t => r)
        (fun fn : empty_ext_fn_t => fn) (int_body pop)
      with
         x => _
      end
    ).
    fold x in H.
    refine ((
      match
        TypeInference.tc_action R empty_Sigma dummy_pos (int_argspec pop)
        (int_retSig pop) x
      as r
      return (
        TypeInference.tc_action R empty_Sigma dummy_pos (int_argspec pop)
          (int_retSig pop) x = r
        -> is_success r = true -> _
      ) with
      | Success s => fun H1 H2 => _
      | Failure f => fun H1 H2 => _
      end
    ) eq_refl eq_refl).
    2: (simpl in H2; congruence).
    erewrite extract_success_rewrite in H. 2: apply H1. simpl in H.
    Unshelve. 2: reflexivity.
    revert H1.

    unfold TypeInference.tc_action.
    destr. intros.
    revert Heqr0. simpl in x.
    unfold desugar_action' in x. cbn in x.
    unfold x. clear x.

    intro Heqr0.
    vm_compute in Heqr0. inv Heqr0.
    vm_compute in H1. inv H1. simpl in H2.
    cbn beta delta iota zeta in H.
    revert H.
    unfold opt_bind.
    destruct may_read.
    - rewrite H0.
      rewrite (proj2 (beq_dec_iff _ _ _)). intro A; inv A. reflexivity.
      reflexivity.
    - congruence.
  Qed.

  Theorem push_returns_one_when_stack_full :
    forall env Gamma sched_log action_log action_log_new v Gamma_new,
    interp_action env empty_sigma Gamma sched_log action_log
      (tc_function R empty_Sigma push)
      = Some (action_log_new, v, Gamma_new)
    -> is_stack_full env -> v = Ob~1.
  Proof.
    intros env Gamma sched_log action_log action_log_new v Gamma_new.
    unfold desugar_action.
    intros.
    refine (
      match
        desugar_action' dummy_pos (fun r : reg_t => r)
        (fun fn : empty_ext_fn_t => fn) (int_body push)
      with
        x => _
      end
    ).
    fold x in H.
    refine ((
      match
        TypeInference.tc_action R empty_Sigma dummy_pos (int_argspec push)
        (int_retSig push) x
      as r
      return (
        TypeInference.tc_action R empty_Sigma dummy_pos (int_argspec push)
        (int_retSig push) x = r -> is_success r = true -> _
      ) with
      | Success s => fun H1 H2 => _
      | Failure f => fun H1 H2 => _
      end
    ) eq_refl eq_refl).
    2: (simpl in H2; congruence).
    erewrite extract_success_rewrite in H. 2: apply H1. simpl in H.
    Unshelve. 2: reflexivity.

    vm_compute in H1. inv H1. clear H2.
    cbn beta delta iota zeta in H.
    revert H.
    unfold opt_bind.
    intro H1.
    destruct may_read in H1; cbn in H1.
    - rewrite H0 in H1.
      rewrite (proj2 (beq_dec_iff _ _ _)) in H1. inv H1. reflexivity.
      reflexivity.
    - discriminate H1.
  Qed.

  Definition stack_top (reg : ContextEnv.(env_t) R) :=
    let index := (ContextEnv.(getenv) reg size) in
    stack (Vect.index_of_nat (Bits. index)).

  (* Definition pop_candidate_address (reg : ContextEnv.(env_t) R) :=. *)

  (* Definition stack_misuse. *)

  Theorem pop_returns_one_on_address_mismatch :
    forall env Gamma sched_log action_log action_log_new v Gamma_new,
    interp_action env empty_sigma Gamma sched_log action_log
      (tc_function R empty_Sigma pop) = Some (action_log_new, v, Gamma_new)
    -> stack_top env <> pop_candidate_address -> v = Ob~1.
  Proof.
    intros env Gamma sched_log action_log action_log_new v Gamma_new.
    cbn beta delta iota.
    simpl in Gamma.
    unfold TypedSemantics.tcontext in Gamma.
    simpl in Gamma.
    simpl in Gamma.
    unfold desugar_action.
    unfold desugar_action'.
    cbn beta delta iota.
    unfold TypeInference.tc_action.
    simpl desugar_action'.
    unfold desugar_action'.
    Search desugar_action.
    Locate "{{ _ }}".
    cbn beta delta iota.
    unfold log2.
    cbn beta delta iota.
    unfold cast_action.
    unfold cast_action'.
    cbn beta delta iota.
    unfold eq_rec_r.
    unfold eq_rec.
    cbn beta delta iota.
    unfold eq_rect_r.
    unfold eq_rect.
    unfold eq_sym.
    cbn beta delta iota.
    unfold eq_ind_r.
    unfold eq_ind.
    unfold eq_sym.
    cbn beta delta iota.
    unfold Nat.eq_dec.
    cbn beta delta iota.
    simpl type_action.

  Theorem stack_returns_zero_when_not_misused : .

  Theorem pop_failure_sets_halt : .
  Theorem push_failure_sets_halt : .
  Theorem stack_misuse_sets_halt: .

  Theorem all_rules_but_end_execution_fail_when_halt_set :.
  Theorem end_execution_calls_ext_finish_when_halt_set :.

  Theorem end_execution_does_not_update_the_processor_state :.

  Theorem valid_stack_use_does_not_impact_the_execution :.
End Stack.
