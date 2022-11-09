(*! Proofs about our RISC-V implementation !*)
Require Import Coq.Program.Equality.
Require Import Koika.Frontend.
Require Export rv.Instructions rv.ShadowStack rv.RVCore rv.rv32 rv.rv32i.
Require Import Koika.SimpleForm.SimpleForm.
Require Import Koika.SimpleForm.Interpretation.
Require Import Koika.SimpleForm.Operations.
Require Import Koika.SimpleForm.Tactics.
Require Import Koika.KoikaForm.Desugaring.DesugaredSyntax.
Require Import Koika.BitsToLists.
Require Import Koika.KoikaForm.SimpleVal.

Module RVProofs.
  Context (ext_sigma : RV32I.ext_fn_t -> val -> val).
  Context (ext_Sigma : RV32I.ext_fn_t -> ExternalSignature).
  Context {REnv : Env RV32I.reg_t}.

  Definition drules rule :=
    match uaction_to_daction (desugar_action tt (RV32I.rv_urules rule)) with
    | Some d => d
    | None => DFail unit_t
    end.

  Instance eq_dec_reg: EqDec RV32I.reg_t := EqDec_FiniteType.
  Existing Instance etaRuleInformationRaw.

  Section test1.
  Variable REnv: Env RV32I.reg_t.
  Variable ctx : env_t REnv (fun _ => val).
  Hypothesis WTRENV: Wt.wt_renv RV32I.R REnv ctx.

  Hypothesis wt_sigma: forall (ufn : RV32I.ext_fn_t) (vc : val),
    wt_val (arg1Sig (ext_Sigma ufn)) vc
    -> wt_val (retSig (ext_Sigma ufn)) (ext_sigma ufn vc).

  Hypothesis rules_wt:
    forall rule : rv_rules_t, exists t : type,
    wt_daction (Sigma:=ext_Sigma) (R:=RV32I.R) unit string string []
      (drules rule) t.

  Definition sf :=
    schedule_to_simple_form RV32I.R (Sigma := ext_Sigma) drules rv_schedule.

  (* temp TODO remove, import ShadowStackProperties.v instead *)
  Section ShadowStackProperties.
    Definition eql (l1 l2: list bool) : bool := list_beq bool Bool.eqb l1 l2.

    (* Propositions about the initial state *)
    Definition no_mispred (ctx: env_t REnv (fun _ : RV32I.reg_t => val)) : Prop :=
      forall v,
      getenv REnv ctx (RV32I.d2e (RV32I.fromDecode.data0)) =
        Struct (RV32I.decode_bookkeeping) v ->
      get_field_struct (struct_fields RV32I.decode_bookkeeping) v "epoch" =
      Some (getenv REnv ctx (RV32I.epoch)).

    Definition stack_empty (ctx: env_t REnv (fun _ : RV32I.reg_t => val))
    : Prop :=
      getenv REnv ctx (RV32I.stack (RV32I.ShadowStack.size))
      = @val_of_value
        (bits_t RV32I.ShadowStack.index_sz)
        (Bits.of_nat (RV32I.ShadowStack.index_sz) 0).

    Definition stack_full (ctx: env_t REnv (fun _ : RV32I.reg_t => val)) : Prop :=
      getenv REnv ctx (RV32I.stack (RV32I.ShadowStack.size))
      = @val_of_value
        (bits_t RV32I.ShadowStack.index_sz)
        (Bits.of_nat (RV32I.ShadowStack.index_sz) RV32I.ShadowStack.capacity).

    (* XXX Note that both a pop and a push can happen for the same instruction *)

    (* This function is defined in a way that mirrors RVCore.v *)
    Definition is_call_instruction (instr: bits_t 32) : bool :=
      let bits := vect_to_list (bits_of_value instr) in
      let opcode_ctrl := List.firstn 3 (List.skipn 4 bits) in
      let opcode_rest := List.firstn 4 (List.skipn 0 bits) in
      let rs1 := List.firstn 5 (List.skipn 15 bits) in
      let rd := List.firstn 5 (List.skipn 7 bits) in
      (eql opcode_ctrl (rev [true; true; false]))
      && (
        (
          (eql opcode_rest (rev [true; true; true; true]))
          && (
            (eql rd (rev [false; false; false; false; true]))
            || (eql rd (rev [false; false; true; false; true]))))
        || (
          (eql opcode_rest (rev [false; true; true; true]))
          && (
            (eql rd (rev [false; false; false; false; true]))
            || (eql rd (rev [false; false; true; false; true]))))).

    (* This function is defined in a way that mirrors RVCore.v *)
    Definition is_ret_instruction (instr: bits_t 32) : bool :=
      let bits := (vect_to_list (bits_of_value instr)) in
      let opcode_ctrl := List.firstn 3 (List.skipn 4 bits) in
      let opcode_rest := List.firstn 4 (List.skipn 0 bits) in
      let rs1 := List.firstn 5 (List.skipn 15 bits) in
      let rd := List.firstn 5 (List.skipn 7 bits) in
      (eql opcode_ctrl [false; true; true])
      && (eql opcode_rest [true; true; true; false])
      && (
        (
          (
            (eql rd (rev [false; false; false; false; true])
            || (eql rd (rev [false; false; true; false; true])))
          && (negb (eql rd rs1))
          && (
            (eql rs1 (rev [false; false; false; false; true]))
            || (eql rs1 (rev [false; false; true; false; true]))))
        || (
          (negb (eql rd (rev [false; false; false; false; true])))
          && (negb (eql rd (rev [false; false; true; false; true])))
          && (
            (eql rs1 (rev [false; false; false; false; true]))
            || (eql rs1 (rev [false; false; true; false; true])))))).

    Definition stack_push (ctx: env_t REnv (fun _ : RV32I.reg_t => val))
    : Prop :=
      forall v w b,
      getenv REnv ctx (RV32I.d2e (RV32I.fromDecode.data0))
      = Struct (RV32I.decode_bookkeeping) v
      -> get_field_struct (struct_fields RV32I.decode_bookkeeping) v "dInst"
      = Some (Struct (decoded_sig) w)
      -> get_field_struct (struct_fields decoded_sig) w "inst" = Some (Bits b)
      -> is_call_instruction (Bits.of_N 32 (Bits.to_N (vect_of_list b))) = true.

    Definition stack_pop (ctx: env_t REnv (fun _ : RV32I.reg_t => val))
    : Prop :=
      forall v w b,
      getenv REnv ctx (RV32I.d2e (RV32I.fromDecode.data0))
      = Struct (RV32I.decode_bookkeeping) v
      -> get_field_struct (struct_fields RV32I.decode_bookkeeping) v "dInst"
      = Some (Struct (decoded_sig) w)
      -> get_field_struct (struct_fields decoded_sig) w "inst" = Some (Bits b)
      -> is_ret_instruction (Bits.of_N 32 (Bits.to_N (vect_of_list b))) = true.

    (* TODO should never return None, simplify? *)
    Definition stack_push_address
      (ctx: env_t REnv (fun _ : RV32I.reg_t => val))
    : option (bits_t 32) :=
      let data := getenv REnv ctx (RV32I.d2e (RV32I.fromDecode.data0)) in
      match data with
      | Struct _ lv =>
        let v :=
          get_field_struct (struct_fields RV32I.decode_bookkeeping) lv "pc"
        in
        match v with
        | Some w =>
          let uw := ubits_of_value w in
          let addr_val := (Bits.to_N (vect_of_list uw) + 4)%N in
          Some (Bits.of_N 32 addr_val)
        | _ => None
        end
      | _ => None
      end.

    (* TODO should never return None, simplify? *)
    Definition stack_top_address (ctx: env_t REnv (fun _ : RV32I.reg_t => val))
    : option (bits_t 32) :=
      let index_raw := getenv REnv ctx (RV32I.stack RV32I.ShadowStack.size) in
      let index_nat := Bits.to_nat (vect_of_list (ubits_of_value index_raw)) in
      let index := index_of_nat (pow2 RV32I.ShadowStack.index_sz) index_nat in
      match index with
      | Some x =>
        let data_raw :=
          (getenv REnv ctx (RV32I.stack (RV32I.ShadowStack.stack x))) in
        Some (Bits.of_N 32 (Bits.to_N (vect_of_list (ubits_of_value data_raw))))
      | None => None
      end.

    Definition stack_underflow (ctx: env_t REnv (fun _ : RV32I.reg_t => val))
    : Prop :=
      no_mispred ctx /\ stack_empty ctx /\ stack_pop ctx.
    Definition stack_overflow (ctx: env_t REnv (fun _ : RV32I.reg_t => val))
    : Prop :=
      no_mispred ctx /\ stack_full ctx /\ (not (stack_pop ctx))
      /\ stack_push ctx.
    Definition stack_address_violation
      (ctx: env_t REnv (fun _ : RV32I.reg_t => val))
    : Prop :=
      no_mispred ctx /\ stack_push ctx
      /\ stack_top_address ctx <> stack_push_address ctx.

    Definition stack_violation (ctx: env_t REnv (fun _ : RV32I.reg_t => val))
    : Prop :=
      stack_underflow ctx \/ stack_overflow ctx \/ stack_address_violation ctx.

    (* Final state *)
    (* TODO transition to simple form *)
    Definition halt_set (ctx: env_t REnv (fun _ : RV32I.reg_t => val)) : Prop :=
      getenv REnv (interp_cycle ctx ext_sigma sf) RV32I.halt = Bits [true].
  End ShadowStackProperties.

    Theorem sf_wf : wf_sf RV32I.R ext_Sigma sf.
    Proof.
      eapply schedule_to_simple_form_wf; eauto.
      repeat constructor.
    Qed.

(*     Lemma fail_schedule: *)
(*       forall (H: getenv REnv ctx RV32I.halt = Bits [true]), *)
(*       getenv REnv (interp_cycle ctx ext_sigma sf) RV32I.halt = Bits [true]. *)
(*     Proof. *)
(*       intros. assert (wfsf := sf_wf). *)
(*       crusher 2. *)
(*     Time Qed. *)

    Lemma extract_bits_1:
      forall {A: Type} bs,
      Datatypes.length (A := A) bs = 1 -> exists k, bs = [k].
    Proof.
      intros.
      destruct bs; inv H.
      destruct bs; eauto. inv H1.
    Qed.

    Lemma extract_bits_32:
      forall {A: Type} bs,
      Datatypes.length (A := A) bs = 32
      ->
      exists k0 k1 k2 k3 k4 k5 k6 k7 k8 k9 k10 k11 k12 k13 k14 k15 k16 k17 k18
        k19 k20 k21 k22 k23 k24 k25 k26 k27 k28 k29 k30 k31,
      bs = [
        k0; k1; k2; k3; k4; k5; k6; k7; k8; k9; k10; k11; k12; k13; k14; k15;
        k16; k17; k18; k19; k20; k21; k22; k23; k24; k25; k26; k27; k28; k29;
        k30; k31
      ].
    Proof.
      intros.
      do 32 (destruct bs; inv H; rename H1 into H).
      do 32 eexists. do 32 f_equal. destruct bs. eauto. inv H.
    Qed.

    Lemma extract_bits_n:
      forall {A: Type} bs n,
      Datatypes.length (A := A) bs = S n -> exists k, bs = k :: tail bs.
    Proof. intros. destruct bs; inv H; eauto. Qed.

    Lemma tail_smaller:
      forall {A: Type} bs n,
      Datatypes.length (A := A) bs = S n -> Datatypes.length (tail bs) = n.
    Proof. intros. destruct bs; eauto. inv H. Qed.

    Lemma stack_violation_results_in_halt:
      forall
        (NoHalt: getenv REnv ctx RV32I.halt = Bits [false])
        (Valid:
          getenv REnv ctx (RV32I.d2e RV32I.fromDecode.valid0) = Bits [true])
        v2
        (DecodeDInst:
          get_field (getenv REnv ctx (RV32I.d2e RV32I.fromDecode.data0)) "dInst"
          = Some v2)
        (LegalOk: get_field v2 "legal" = Some (Bits [true]))
        (CanEnq:
          getenv REnv ctx (RV32I.e2w RV32I.fromExecute.valid0) = Bits [false]),
      stack_violation ctx -> halt_set ctx.
    Proof.
      intros. assert (wfsf := sf_wf).
      unfold halt_set.
      prune.
      exploit_regs.
      do 4 collapse.
      prune.

      generalize (WTRENV (RV32I.d2e RV32I.fromDecode.data0)). intro.
      inv H0. rewrite <- H2 in *.
      simpl in H3.

      inv H3. inv H6. inv H7. inv H8. inv H9. inv H10. inv H11.
      inv H6. inv H2. inv H1. inv H11. inv H12. inv H13. inv H14. inv H15.
      inv H16.
      inv H13. inv H1. inv H16. inv H17.
      inv H13. simpl in H1.
      inv H9. inv H5. inv H10. inv H11. inv H2.

      apply extract_bits_1 in H13. destruct H13.
      apply extract_bits_1 in H9. destruct H9.
      apply extract_bits_1 in H5. destruct H5.
      apply extract_bits_1 in H10. destruct H10.
      apply extract_bits_1 in H11. destruct H11.
      subst.

      simpl in DecodeDInst.
      inv DecodeDInst.
      simpl in LegalOk.
      inv LegalOk.
      inv H14.
      eapply extract_bits_1 in H2. destruct H2. subst.
      symmetry in H6. exploit_reg H6.

      generalize (WTRENV (RV32I.epoch)). intro.
      inv H0.
      eapply extract_bits_1 in H9. destruct H9. subst.
      symmetry in H5. exploit_reg H5.

      red in H.
      assert (x4 = x0). {
        destruct H.
        - repeat (destruct H as [? H]).
          red in H0. eapply H0 in H6. inv H6. congruence.
        - destruct H; red in H; repeat (destruct H as [? H]); red in H0;
            eapply H0 in H6; inv H6; congruence.
      }
      subst. clear H5.
      destruct H as [under | [over | violation]].
      - red in under.
        destruct under as [no_mispred [stack_empty stack_pop]].
        red in no_mispred, stack_empty, stack_pop. simpl in *.
        vm_compute vect_to_list in stack_empty.
        exploit_reg stack_empty. clear stack_empty.
        clear no_mispred.
        inv H12. apply extract_bits_32 in H0. do 32 destruct H0 as [? H0].
        subst.
        eapply stack_pop in H6 as ret_instr. 2-3: reflexivity.
        clear stack_pop.
        unfold is_ret_instruction in ret_instr.
        unfold eql in ret_instr.
        rewrite Bits.of_N_to_N in ret_instr.
        simpl in ret_instr.
        eapply andb_true_iff in ret_instr.
        repeat rewrite andb_true_iff in opc_ctrl.
        destruct ret_instr as [opc ret_instr].
        rewrite ! andb_true_iff in opc. destruct opc as [opc_ctrl opc_jalr].
        repeat rewrite orb_true_iff in ret_instr.
        destruct ret_instr as [pop_push | pop].
        + rewrite ! andb_true_iff in pop_push.
          rewrite ! orb_true_iff in pop_push.
          rewrite ! andb_true_iff in pop_push.
          destruct pop_push as [[rd_1_or_5 rd_neq_rs1] rs1_1_or_5].
          rewrite negb_true_iff in rd_neq_rs1.
          rewrite ! andb_false_iff in rd_neq_rs1.
          destruct rd_1_or_5 as [rd_1 | rd_5], rs1_1_or_5 as [rs1_1 | rs1_5].
          * repeat destruct rd_1 as [? rd_1].
            repeat destruct rs1_1 as [? rs1_1].
            apply Bool.eqb_prop in H, H0, H2, H5, H9, H10, H11, H12, H13, H14.
            subst. simpl in rd_neq_rs1. intuition congruence.
          * clear rd_neq_rs1.
            repeat (rewrite ? eqb_true_iff in rd_1, rs1_5, opc_ctrl, opc_jalr).
            rewrite ! eqb_true_iff in opc_jalr.
            rewrite ! eqb_true_iff in rd_1.
            rewrite ! eqb_true_iff in rs1_5.
            intuition subst.
            collapse.
            full_pass_c.
            full_pass_c.
            do 4 full_pass_c.
            destruct x0; crusher_c 3.
          * repeat (rewrite ? eqb_true_iff in rd_5, rs1_1, opc_ctrl, opc_jalr).
            rewrite ! eqb_true_iff in opc_jalr.
            rewrite ! eqb_true_iff in rd_5.
            rewrite ! eqb_true_iff in rs1_1.
            Ltac destr_and_in H :=
              repeat match type of H with _ /\ _ =>
                let H1 := fresh in let H2 := fresh in
                destruct H as [H1 H2]; destr_and_in H1; destr_and_in H2
            end.
            destr_and_in opc_ctrl.
            destr_and_in opc_jalr.
            destr_and_in rs1_1.
            destr_and_in rd_5.
            subst.
            simpl in rd_neq_rs1. clear rd_neq_rs1.
            full_pass_c.
            full_pass_c.
            do 4 full_pass_c.
            destruct x0; crusher_c 3.
          * repeat (rewrite ? eqb_true_iff in rd_5, rs1_5, opc_ctrl, opc_jalr).
            rewrite ! eqb_true_iff in opc_jalr.
            rewrite ! eqb_true_iff in rd_5.
            rewrite ! eqb_true_iff in rs1_5.
            destr_and_in opc_ctrl.
            destr_and_in opc_jalr.
            destr_and_in rs1_5.
            destr_and_in rd_5.
            subst.
            simpl in rd_neq_rs1. intuition congruence.
        + rewrite ! andb_true_iff in pop.
          rewrite ! orb_true_iff in pop.
          rewrite ! andb_true_iff in pop.
          rewrite ! negb_true_iff in pop.
          rewrite ! andb_false_iff in pop.
          rewrite ! eqb_true_iff in opc_ctrl.
          rewrite ! eqb_true_iff in opc_jalr.
          rewrite ! eqb_true_iff in pop.
          rewrite ! eqb_false_iff in pop.
          destr_and_in opc_ctrl.
          destr_and_in opc_jalr. subst.
          destruct pop as [rd_not_1_or_5 rs1_1_or_5].
          assert (x19 = true /\ x20 = false /\ x22 = false /\ x23 = false).
          destruct rs1_1_or_5; intuition. clear rs1_1_or_5.
          destr_and_in H. subst.
          do 2 collapse. prune.
          full_pass_c.
          full_pass_c.
          do 4 full_pass_c.
          destruct x0.
          * do 3 full_pass_c.
            destruct x11, x12, x13, x14, x15, x21;
              crusher_c 3; intuition congruence.
          * do 3 full_pass_c.
            destruct x11, x12, x13, x14, x15, x21;
              crusher_c 3; intuition congruence.
      - destruct over as [no_mispred [stack_full [not_stack_pop stack_push]]].
        clear no_mispred.
        red in stack_full, not_stack_pop, stack_push.
        unfold stack_pop in not_stack_pop.
  Qed.

  Definition cycle (r: env_t ContextEnv (fun _ : RV32I.reg_t => val)) :=
    UntypedSemantics.interp_dcycle drules r ext_sigma rv_schedule.

  Definition env_type := env_t REnv RV32I.R.
  Definition initial_env := create REnv RV32I.r.

  Definition CEnv := @ContextEnv RV32I.reg_t RV32I.FiniteType_reg_t.
  Definition initial_context_env := CEnv.(create) (RV32I.r).

  Definition f_init := fun x => val_of_value (initial_context_env.[x]).
