(*! Proofs about our RISC-V implementation !*)
Require Import Coq.Program.Equality.
Require Import Koika.Frontend.
Require Export rv.Decode rv.Instructions rv.ShadowStack rv.RVCore rv.rv32
  rv.rv32i.
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

  Section proof.
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

  Section ShadowStackProperties.
    Definition eql (l1 l2: list bool) : bool := list_beq bool Bool.eqb l1 l2.

    (* Propositions about the initial state *)
  Definition no_mispred (ctx: env_t REnv (fun _ : RV32I.reg_t => val))
    : Prop :=
      forall v,
      getenv REnv ctx (RV32I.d2e (RV32I.fromDecode.data0)) =
        Struct (RV32I.decode_bookkeeping) v ->
      get_field_struct (struct_fields RV32I.decode_bookkeeping) v "epoch" =
      Some (getenv REnv ctx (RV32I.epoch)).

    Definition sstack_empty (ctx: env_t REnv (fun _ : RV32I.reg_t => val))
    : Prop :=
      getenv REnv ctx (RV32I.sstack (RV32I.ShadowStack.size))
      = @val_of_value
        (bits_t RV32I.ShadowStack.index_sz)
        (Bits.of_nat (RV32I.ShadowStack.index_sz) 0).

    Definition sstack_full (ctx: env_t REnv (fun _ : RV32I.reg_t => val))
    : Prop :=
      getenv REnv ctx (RV32I.sstack (RV32I.ShadowStack.size))
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

    Definition sstack_push (ctx: env_t REnv (fun _ : RV32I.reg_t => val))
    : Prop :=
      forall v w b,
      getenv REnv ctx (RV32I.d2e (RV32I.fromDecode.data0))
      = Struct (RV32I.decode_bookkeeping) v
      -> get_field_struct (struct_fields RV32I.decode_bookkeeping) v "dInst"
      = Some (Struct (decoded_sig) w)
      -> get_field_struct (struct_fields decoded_sig) w "inst" = Some (Bits b)
      -> is_call_instruction (Bits.of_N 32 (Bits.to_N (vect_of_list b))) = true.

    Definition sstack_pop (ctx: env_t REnv (fun _ : RV32I.reg_t => val))
    : Prop :=
      forall v w b,
      getenv REnv ctx (RV32I.d2e (RV32I.fromDecode.data0))
      = Struct (RV32I.decode_bookkeeping) v
      -> get_field_struct (struct_fields RV32I.decode_bookkeeping) v "dInst"
      = Some (Struct (decoded_sig) w)
      -> get_field_struct (struct_fields decoded_sig) w "inst" = Some (Bits b)
      -> is_ret_instruction (Bits.of_N 32 (Bits.to_N (vect_of_list b))) = true.

    (* TODO should never return None, simplify? *)
    Definition ret_address (ctx: env_t REnv (fun _ : RV32I.reg_t => val))
    : option (bits_t 32) :=
      let data := getenv REnv ctx (RV32I.d2e (RV32I.fromDecode.data0)) in
      match data with
      | Struct _ lv =>
        let rs1 :=
          get_field_struct (struct_fields RV32I.decode_bookkeeping) lv "rval1"
        in
        let dInst :=
          get_field_struct (struct_fields RV32I.decode_bookkeeping) lv "dInst"
        in
        match rs1, dInst with
        | Some rs1_val, Some (Struct (decoded_sig) dInst) =>
          let inst :=
            get_field_struct (struct_fields rv.RVCore.decoded_sig) dInst "inst"
          in
          match inst with
          | Some inst_val =>
            let bits :=
              Bits.to_N (
                Bits.and
                  (Bits.of_N
                    (Datatypes.length ((ubits_of_value rs1_val)))
                    (Bits.to_N
                      (Bits.of_list (ubits_of_value rs1_val))
                      + Bits.to_N (
                        Bits.of_list (
                          List.skipn 20 (ubits_of_value inst_val) ++
                          List.repeat (List.last (ubits_of_value inst_val) true) 20
                    )))
                  )
                  (Vect.Bits.neg (Bits.of_N (
                    Datatypes.length (ubits_of_value rs1_val)) 1)
                  )
              ) in
            Some (Bits.of_N 32 bits)
          | None => None
          end
        | _, _ => None
        end
      | _ => None
      end.

    Definition sstack_top_address (ctx: env_t REnv (fun _ : RV32I.reg_t => val))
    : option (bits_t 32) :=
      let index_raw := getenv REnv ctx (RV32I.sstack RV32I.ShadowStack.size) in
      let index_nat := pred (Bits.to_nat (vect_of_list (ubits_of_value index_raw))) in
      let index := index_of_nat (pow2 RV32I.ShadowStack.index_sz) index_nat in
      match index with
      | Some x =>
        let data_raw :=
          (getenv REnv ctx (RV32I.sstack (RV32I.ShadowStack.stack x))) in
        Some (Bits.of_N 32 (Bits.to_N (vect_of_list (ubits_of_value data_raw))))
      | _ => None
      end.

    Definition sstack_underflow (ctx: env_t REnv (fun _ : RV32I.reg_t => val))
    : Prop :=
      no_mispred ctx /\ sstack_empty ctx /\ sstack_pop ctx.
    Definition sstack_overflow (ctx: env_t REnv (fun _ : RV32I.reg_t => val))
    : Prop :=
      no_mispred ctx /\ sstack_full ctx /\ (not (sstack_pop ctx))
      /\ sstack_push ctx.
    Definition sstack_address_violation
      (ctx: env_t REnv (fun _ : RV32I.reg_t => val))
    : Prop :=
      no_mispred ctx /\ ~ sstack_empty ctx /\ sstack_pop ctx
      /\ sstack_top_address ctx <> ret_address ctx.

    Definition sstack_violation (ctx: env_t REnv (fun _ : RV32I.reg_t => val))
    : Prop :=
      sstack_underflow ctx \/ sstack_overflow ctx
      \/ sstack_address_violation ctx.

    (* Final state *)
    Definition halt_set (ctx: env_t REnv (fun _ : RV32I.reg_t => val)) : Prop :=
      getenv REnv (interp_cycle ctx ext_sigma sf) RV32I.halt = Bits [true].
  End ShadowStackProperties.

    Theorem sf_wf : wf_sf RV32I.R ext_Sigma sf.
    Proof.
      eapply schedule_to_simple_form_wf; eauto.
      repeat constructor.
    Qed.

    Lemma sstack_activated_constant:
      getenv REnv (interp_cycle ctx ext_sigma sf) RV32I.sstack_activated
      = getenv REnv ctx RV32I.sstack_activated.
    Proof.
      intros. assert (wfsf := sf_wf).
      crusher 2.
    Time Qed.

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

    Lemma extract_bits_3:
      forall {A: Type} bs, Datatypes.length (A := A) bs = 3
      -> exists k0 k1 k2, bs = [k0; k1; k2].
    Proof.
      intros.
      do 3 (destruct bs; inv H; rename H1 into H).
      do 3 eexists. do 3 f_equal. destruct bs. eauto. inv H.
    Qed.

    Lemma extract_bits_n:
      forall {A: Type} bs n,
      Datatypes.length (A := A) bs = S n -> exists k, bs = k :: tail bs.
    Proof. intros. destruct bs; inv H; eauto. Qed.

    Lemma tail_smaller:
      forall {A: Type} bs n,
      Datatypes.length (A := A) bs = S n -> Datatypes.length (tail bs) = n.
    Proof. intros. destruct bs; eauto. inv H. Qed.

    Ltac destr_and_in H :=
      repeat match type of H with _ /\ _ =>
        let H1 := fresh in let H2 := fresh in
        destruct H as [H1 H2]; destr_and_in H1; destr_and_in H2
    end.

    Ltac extract_bits_info H :=
      unfold eql in H; rewrite Bits.of_N_to_N in H;
      simpl in H;
      rewrite ! andb_true_r in H;
      repeat (
        try rewrite ! andb_true_iff in H;
        try rewrite ! orb_true_iff in H
      );
      rewrite ! eqb_true_iff in H.

    Ltac inv_interp_sact :=
      match goal with
      | H: interp_sact _ _ _ (SVar _) _ |- _ => inv H
      | H: interp_sact _ _ _ (SReg _) _ |- _ => inv H
      | H: interp_sact _ _ _ (SIf _ _ _) _ |- _ => inv H
      | H: interp_sact _ _ _ (SBinop _ _ _) _ |- _ => inv H
      | H: interp_sact _ _ _ (SUnop _ _) _ |- _ => inv H
      | H: interp_sact _ _ _ (SExternalCall _ _) _ |- _ => inv H
      | H: interp_sact _ _ _ (SConst _) _ |- _ => inv H
      | H: Maps.PTree.get _ _ = _ |- _ => vm_compute in H; inv H
      end.

    Lemma sstack_underflow_results_in_halt:
      forall
        (SstackActivated: getenv REnv ctx RV32I.sstack_activated = Bits [true])
        (NoHalt: getenv REnv ctx RV32I.halt = Bits [false])
        (Valid:
          getenv REnv ctx (RV32I.d2e RV32I.fromDecode.valid0) = Bits [true])
        v2
        (DecodeDInst:
          get_field (getenv REnv ctx (RV32I.d2e RV32I.fromDecode.data0)) "dInst"
          = Some v2)
        (LegalOk: get_field v2 "legal" = Some (Bits [true]))
        (CanEnq:
          getenv REnv ctx (RV32I.e2w RV32I.fromExecute.valid0) = Bits [false])
        imm_v
        (ImmV:
          get_field v2 "immediateType"
          = Some
              (Struct
                (Std.Maybe (enum_t imm_type))
                [Bits [true]; Enum imm_type imm_v])
        )
        inst_v (InstV: get_field v2 "inst" = Some (Bits inst_v))
        (imm_coherent:
          match get_imm_name inst_v with
          | None => False
          | Some name =>
            match vect_index name imm_type.(enum_members) with
            | Some idx =>
              list_beq bool Bool.eqb
                (vect_to_list (vect_nth imm_type.(enum_bitpatterns) idx))
                imm_v
              = true
            | None => False
            end
          end
        ),
      sstack_underflow ctx -> halt_set ctx.
    Proof.
      intros. assert (wfsf := sf_wf).
      unfold halt_set.
      prune.
      exploit_regs.
      do 4 collapse.
      prune.
      generalize (WTRENV (RV32I.d2e RV32I.fromDecode.data0)). intro.
      inv H0. rewrite <- H2 in DecodeDInst.
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
        destruct H. red in H. eapply H in H6. inv H6. congruence.
      }
      subst. clear H5.
      rename H into under.
      destruct under as [no_mispred [sstack_empty sstack_pop]].
      red in no_mispred, sstack_empty, sstack_pop. simpl in *.
      vm_compute vect_to_list in sstack_empty.
      exploit_reg sstack_empty. clear sstack_empty.
      clear no_mispred.
      inv H12. apply extract_bits_32 in H0. do 32 destruct H0 as [? H0].
      subst.
      eapply sstack_pop in H6 as ret_instr. 2-3: reflexivity.
      clear sstack_pop.
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
          full_pass_c.
          full_pass_c.
          do 4 full_pass_c.
          destruct x0; crusher_c 3.
        * repeat (rewrite ? eqb_true_iff in rd_5, rs1_1, opc_ctrl, opc_jalr).
          rewrite ! eqb_true_iff in opc_jalr.
          rewrite ! eqb_true_iff in rd_5.
          rewrite ! eqb_true_iff in rs1_1.
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
    Time Qed. (* ~= 70s *)

    Optimize Heap.

    Lemma sstack_overflow_results_in_halt:
      forall
        (SstackActivated: getenv REnv ctx RV32I.sstack_activated = Bits [true])
        (NoHalt: getenv REnv ctx RV32I.halt = Bits [false])
        (Valid:
          getenv REnv ctx (RV32I.d2e RV32I.fromDecode.valid0) = Bits [true])
        v2
        (DecodeDInst:
          get_field (getenv REnv ctx (RV32I.d2e RV32I.fromDecode.data0)) "dInst"
          = Some v2)
        (LegalOk: get_field v2 "legal" = Some (Bits [true]))
        (CanEnq:
          getenv REnv ctx (RV32I.e2w RV32I.fromExecute.valid0) = Bits [false])
        imm_v
        (ImmV:
          get_field v2 "immediateType"
          = Some
              (Struct
                (Std.Maybe (enum_t imm_type))
                [Bits [true]; Enum imm_type imm_v])
        )
        inst_v (InstV: get_field v2 "inst" = Some (Bits inst_v))
        (imm_coherent:
          match get_imm_name inst_v with
          | None => False
          | Some name =>
            match vect_index name imm_type.(enum_members) with
            | Some idx =>
              list_beq bool Bool.eqb
                (vect_to_list (vect_nth imm_type.(enum_bitpatterns) idx))
                imm_v
              = true
            | None => False
            end
          end
        ),
      sstack_overflow ctx -> halt_set ctx.
    Proof.
      intros. assert (wfsf := sf_wf).
      unfold halt_set.
      prune.
      exploit_regs.
      do 4 collapse.
      prune.
      generalize (WTRENV (RV32I.d2e RV32I.fromDecode.data0)). intro.
      inv H0. rewrite <- H2 in DecodeDInst.
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
        destruct H. red in H. eapply H in H6. inv H6. congruence.
      }
      subst. clear H5.
      rename H into over.
      destruct over as [
        no_mispred [sstack_full [not_sstack_pop sstack_push]]
      ].
      clear no_mispred.
      red in sstack_full, sstack_push.
      unfold sstack_pop in not_sstack_pop.
      simpl in *.
      exploit_reg sstack_full. clear sstack_full.
      inv H12. apply extract_bits_32 in H0. do 32 destruct H0 as [? H0].
      subst.
      eapply sstack_push in H6 as push_instr. 2-3: reflexivity.
      clear sstack_push.
      unfold is_call_instruction in push_instr.
      extract_bits_info push_instr.
      destruct push_instr as [opc_ctrl call_or_ret].
      do 2 destruct opc_ctrl as [? opc_ctrl].
      subst.
      red in not_sstack_pop.
      destruct call_or_ret as [[jal rd_1_or_5] | [jalr rd_1_or_5]].
      + clear not_sstack_pop.
        do 3 destruct jal as [? jal]. subst.
        collapse.
        full_pass_c.
        full_pass_c.
        do 4 full_pass_c.
        destruct rd_1_or_5 as [rd_1 | rd_5].
        * do 4 destruct rd_1 as [? rd_1]. subst.
          destruct x0; crusher_c 3.
        * do 4 destruct rd_5 as [? rd_5]. subst.
          destruct x0; crusher_c 3.
      + do 3 destruct jalr as [? jalr]. subst.
        assert (x11 = true /\ x12 = false /\ x14 = false /\ x15 = false).
        destruct rd_1_or_5; intuition. clear rd_1_or_5. destr_and_in H. subst.
        full_pass_c.
        full_pass_c.
        full_pass_c.
        full_pass_c.
        full_pass_c.
        full_pass_c.
        full_pass_c.

        Eval vm_compute in (Maps.PTree.get 989 (vars sf0)).

        Time ssearch_in_var (
          @SBinop RV32I.reg_t RV32I.ext_fn_t
            (UEq false) (SConst (Bits [x0])) (SConst (Bits [x0]))
        )
        (vars sf0) 989%positive
        (@SConst RV32I.reg_t RV32I.ext_fn_t (Bits [true])) (bits_t 1).
        intro A. trim A. vm_compute. reflexivity.
        trim A. repeat econstructor.
        trim A. repeat econstructor.
        trim A.
        eapply ReplaceSubact.interp_sact_iff_from_implies; eauto.
        apply wfsf. apply wfsf.
        repeat econstructor.
        intros. inv H. inv H9. inv H11. simpl in H12. inv H12.
        rewrite andb_true_r. rewrite eqb_reflx. constructor.
        trim A. inversion 1.
        exploit_subact. clear A. isolate_sf.
        ssearch_in_var (@SBinop RV32I.reg_t RV32I.ext_fn_t (UEq false)
                          (SConst (Bits [x0]))
                          (SConst (Bits [x0]))
                       ) (vars sf0) 1810%positive
          (@SConst RV32I.reg_t RV32I.ext_fn_t (Bits [true])) (bits_t 1).
        intro A. trim A. vm_compute. reflexivity.
        trim A. repeat econstructor.
        trim A. repeat econstructor.
        trim A.
        eapply ReplaceSubact.interp_sact_iff_from_implies; eauto.
        apply wfsf. apply wfsf.
        repeat econstructor.
        intros. inv H. inv H9. inv H11. simpl in H12. inv H12.
        rewrite andb_true_r. rewrite eqb_reflx. constructor.
        trim A. inversion 1.
        exploit_subact. clear A. isolate_sf.
        get_subact_ok ((@SBinop RV32I.reg_t RV32I.ext_fn_t (UBits2 UOr)
                   (SBinop (UEq false) (SConst (Bits [true; false; x13; false; false]))
                      (SConst (Bits [true; false; false; false; false])))
                   (SBinop (UEq false) (SConst (Bits [true; false; x13; false; false]))
                      (SConst (Bits [true; false; true; false; false])))))
          (vars sf0)
          (@SConst RV32I.reg_t RV32I.ext_fn_t (Bits [true])) (bits_t 1)
        .
        intro A.
        trim A. repeat econstructor.
        trim A. repeat econstructor.
        trim A.
        eapply ReplaceSubact.interp_sact_iff_from_implies; eauto.
        apply wfsf. apply wfsf.
        repeat econstructor.
        intros. inv H. inv H9. inv H11. inv H5. inv H13. inv H9. inv H15.
        simpl in H14, H16. inv H14; inv H16.
        simpl in H12. inv H12.
        clear. destruct x13; cbn [Bool.eqb andb]; constructor.
        trim A. inversion 1.
        exploit_subact. clear A. isolate_sf.
        full_pass_c.
        full_pass_c.
        full_pass_c.
        full_pass_c.
        full_pass_c.
        full_pass_c.
        full_pass_c.
        full_pass_c.

        exploit_var 1461%positive uconstr:(SConst (Bits [true])).
        {
          econstructor.
          intros. inv H. vm_compute in H2. inv H2.
          inv H5. destruct b; inv H11; econstructor.
          inversion 1.
          econstructor. vm_compute. reflexivity. repeat constructor.
        }
        clear VS.
        isolate_sf.
        full_pass_c.
        full_pass_c.
        full_pass_c.
        full_pass_c.
        full_pass_c.
        exploit_var 1810%positive uconstr:(SConst (Bits [false])).
        {
          econstructor.
          intros.
          eapply interp_sact_do_eval_sact
            with (R := RV32I.R) (Sigma := ext_Sigma) in H.
          assert (OF: oldv = Bits [false]).
          clear -H. inv H. destruct x13, x19, x20, x21, x22, x23; auto.
          clear H.
          subst; constructor. apply wfsf.
          econstructor. vm_compute. reflexivity. inversion 1.
          econstructor. vm_compute. eauto.
          repeat constructor.
        }
        clear VS.
        full_pass_c.
        full_pass_c.
        full_pass_c.
        full_pass_c.
        full_pass_c.
        crusher_c 1.
      Time Qed. (* ~150s *)

      Optimize Heap.

    Lemma sstack_address_violation_results_in_halt:
      forall
        (SstackActivated: getenv REnv ctx RV32I.sstack_activated = Bits [true])
        (NoHalt: getenv REnv ctx RV32I.halt = Bits [false])
        (Valid:
          getenv REnv ctx (RV32I.d2e RV32I.fromDecode.valid0) = Bits [true])
        v2
        (DecodeDInst:
          get_field (getenv REnv ctx (RV32I.d2e RV32I.fromDecode.data0)) "dInst"
          = Some v2)
        (LegalOk: get_field v2 "legal" = Some (Bits [true]))
        (CanEnq:
          getenv REnv ctx (RV32I.e2w RV32I.fromExecute.valid0) = Bits [false])
        imm_v
        (ImmV:
          get_field v2 "immediateType"
          = Some
              (Struct
                (Std.Maybe (enum_t imm_type))
                [Bits [true]; Enum imm_type imm_v])
        )
        inst_v (InstV: get_field v2 "inst" = Some (Bits inst_v))
        (imm_coherent:
          match get_imm_name inst_v with
          | None => False
          | Some name =>
            match vect_index name imm_type.(enum_members) with
            | Some idx =>
              list_beq bool Bool.eqb
                (vect_to_list (vect_nth imm_type.(enum_bitpatterns) idx))
                imm_v
              = true
            | None => False
            end
          end
        ),
      sstack_address_violation ctx -> halt_set ctx.
    Proof.
      intros. assert (wfsf := sf_wf).
      unfold halt_set.
      prune.
      exploit_regs.
      do 4 collapse.
      prune.
      generalize (WTRENV (RV32I.d2e RV32I.fromDecode.data0)). intro.
      inv H0. rewrite <- H2 in DecodeDInst.
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
        destruct H. red in H. eapply H in H6. inv H6. congruence.
      }
      subst. clear H5.
      rename H into violation.
      destruct violation as (no_mispred & not_empty & pop & address_neq).
      clear no_mispred.
      unfold sstack_empty in not_empty. simpl in not_empty.
      generalize (WTRENV (RV32I.sstack RV32I.ShadowStack.size)).
      intro A. inv A.
      change (log2 5) with 3 in H2.
      apply extract_bits_3 in H2.
      destruct H2 as (k0 & k1 & k2 & EQ). subst.
      apply extract_bits_3 in H1.
      destruct H1 as (k3 & k4 & k5 & EQ'). subst.
      rename H0 into SIZE.
      symmetry in SIZE.
      rewrite SIZE in not_empty.
      vm_compute in not_empty.
      exploit_reg SIZE.
      unfold sstack_pop in pop.
      inv H12. apply extract_bits_32 in H0. do 32 destruct H0 as [? H0].
      subst.
      eapply pop in H6 as ret_instr. 2-3: reflexivity.
      clear pop.
      unfold is_ret_instruction in ret_instr.
      extract_bits_info ret_instr.
      rewrite ! negb_true_iff in ret_instr.
      rewrite ! andb_false_iff in ret_instr.
      rewrite ! eqb_false_iff in ret_instr.
      destruct ret_instr as [[opc1 opc2] ret_instr].
      do 2 destruct opc1 as [? opc1]. do 3 destruct opc2 as [? opc2]. subst.
      move address_neq at bottom.
      unfold sstack_top_address in address_neq.
      Opaque index_of_nat.
      simpl in address_neq.
      change (pow2 (log2 5)) with 8 in address_neq.
      rewrite SIZE in address_neq. simpl in address_neq.
      edestruct @index_of_nat_bounded as (idx & EQ).
      2: rewrite EQ in address_neq.
      generalize (Bits.to_nat_bounded Ob~k2~k1~k0).
      change (pow2 3) with 8. change (pow2 (log2 8)) with 8. lia.
      generalize (WTRENV (RV32I.sstack (RV32I.ShadowStack.stack idx))).
      intro A. inv A.
      rewrite <- H0 in address_neq. simpl in address_neq.
      unfold ret_address in address_neq.
      rewrite H6 in address_neq. Opaque List.firstn.
      simpl get_field_struct in address_neq.
      Opaque Bits.of_N Bits.to_N Bits.and Bits.neg.
      simpl in address_neq.
      move not_empty at bottom.
      move ret_instr at bottom.
      full_pass_c.
      full_pass_c.
      full_pass_c.
      full_pass_c.
      full_pass_c.
      full_pass_c.
      full_pass_c.


      exploit_var
        1376%positive
        (@SConst RV32I.reg_t RV32I.ext_fn_t (Bits bs)).
      {
        econstructor; intros.
        {
          eapply (interp_sact_do_eval_sact) in H.
          {
            unfold do_eval_sact in H. unfold eval_sact in H.
            unfold Interpretation.eval_sact in H. vm_compute Nat.add in H.
            cbn fix in H. cbn match in H. cbn beta in H. simpl in H.
            destruct k0, k1, k2;
            try (exfalso; apply not_empty; reflexivity);
            vm_compute Bool.eqb in H; cbn in H; apply Some_inj in H; subst oldv;
            rewrite H0; vm_compute in EQ; apply Some_inj in EQ; rewrite EQ;
            constructor.
          }
          eapply Properties.wf_sf_vvs. eapply wfsf.
          econstructor. vm_compute. eauto.
        }
        inv H.
        econstructor. constructor. auto.
        econstructor. constructor. eauto.
      }
      Unshelve. 2: apply RV32I.R. 2: apply RV32I.Sigma.
      clear VS.

      Eval vm_compute in (Maps.PTree.get 1529 (vars sf0)).
      exploit_var
        1529%positive
        (@SConst RV32I.reg_t RV32I.ext_fn_t (Bits bs)).
      {
        econstructor; intros.
        {
          eapply (interp_sact_do_eval_sact) in H.
          {
            unfold do_eval_sact in H. unfold eval_sact in H.
            unfold Interpretation.eval_sact in H. vm_compute Nat.add in H.
            cbn fix in H. cbn match in H. cbn beta in H. simpl in H.
            destruct k0, k1, k2;
            try (exfalso; apply not_empty; reflexivity);
            vm_compute Bool.eqb in H; cbn in H; apply Some_inj in H; subst oldv;
            rewrite H0; vm_compute in EQ; apply Some_inj in EQ; rewrite EQ;
            constructor.
          }
          eapply Properties.wf_sf_vvs. eapply wfsf.
          econstructor. vm_compute. eauto.
        }
        inv H.
        econstructor. constructor. auto.
        econstructor. constructor. eauto.
      }
      Unshelve. 2: apply RV32I.R. 2: apply RV32I.Sigma.
      clear VS.
      full_pass_c. full_pass_c.
      vm_compute in InstV. inv InstV.
      vm_compute get_imm_name in imm_coherent.
      simpl in imm_coherent.
      inv ImmV.
      vm_compute Bool.eqb in imm_coherent.
      destruct k3, k4, k5; try discriminate imm_coherent.
      clear imm_coherent.
     assert (
      forall n (v1 v2: vect bool n),
        bitwise andb (vect_to_list v1) (vect_to_list v2)
        = vect_to_list (Bits.and v1 v2)
      ) as and_equiv. {
        clear.
        induction n; intros.
        - reflexivity.
        - destruct v1, v2. simpl.
          specialize (IHn vtl vtl0).
          unfold vect_to_list. simpl.
          unfold vect_to_list in IHn. rewrite IHn.
          f_equal.
      }

      Eval vm_compute in (Maps.PTree.get 1377 (vars sf0)).
      exploit_var
        1377%positive
        (@SConst RV32I.reg_t RV32I.ext_fn_t (Bits [true])).
      {
        econstructor; intros.
        {
          eapply (interp_sact_do_eval_sact) in H.
          {
            unfold do_eval_sact in H. unfold eval_sact in H.
            unfold Interpretation.eval_sact in H. vm_compute Nat.add in H.
            cbn fix in H. cbn match in H. cbn beta in H. simpl in H.
            inv H7. apply extract_bits_32 in H5. do 32 destruct H5 as [? H5]. subst bs0.
            vm_compute Datatypes.length in H.
            unfold opt_bind in H.
            apply Some_inj in H.
            subst oldv.
            inv H1. apply extract_bits_32 in H2. do 32 destruct H2 as [? H2]. subst bs.
            replace [
              false; true; true; true; true; true; true; true; true;
              true; true; true; true; true; true; true; true; true;
              true; true; true; true; true; true; true; true; true;
              true; true; true; true; true
            ] with (
              vect_to_list
              Ob~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~0
            ). 2: auto.
            rewrite and_equiv.
            move address_neq at bottom.
            vm_compute Datatypes.length in address_neq.
            replace (Bits.neg (Bits.of_N 32 1)) with
              Ob~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~0
              in address_neq. 2: auto.
            destr. 2: constructor.
            exfalso. apply address_neq. repeat f_equal.
            apply list_eqb_correct in Heqb. 2: apply eqb_true_iff.
            replace [
               x60; x61; x62; x63; x64; x65; x66; x67; x68; x69; x70; x71; x72;
               x73; x74; x75; x76; x77; x78; x79; x80; x81; x82; x83; x84; x85;
               x86; x87; x88; x89; x90; x91
            ] with (
              vect_to_list
              Ob~x91~x90~x89~x88~x87~x86~x85~x84~x83~x82~x81~x80~x79~x78~x77~x76~x75~x74~x73~x72~x71~x70~x69~x68~x67~x66~x65~x64~x63~x62~x61~x60
            ) in Heqb. 2: auto.
            apply vect_to_list_inj in Heqb.
            replace (Bits.of_list [
               x60; x61; x62; x63; x64; x65; x66; x67; x68; x69; x70; x71; x72;
               x73; x74; x75; x76; x77; x78; x79; x80; x81; x82; x83; x84; x85;
               x86; x87; x88; x89; x90; x91
            ]) with (
              Ob~x91~x90~x89~x88~x87~x86~x85~x84~x83~x82~x81~x80~x79~x78~x77~x76~x75~x74~x73~x72~x71~x70~x69~x68~x67~x66~x65~x64~x63~x62~x61~x60
            ). 2: auto.
            rewrite Heqb. reflexivity.
          }
          apply wfsf.
          econstructor. vm_compute. eauto.
        }
      inv H.
      econstructor. vm_compute. eauto. constructor. constructor. auto.
    }
    Unshelve. 2: apply RV32I.R. 2: apply RV32I.Sigma.
    clear VS.
    isolate_sf.
    Eval vm_compute in (Maps.PTree.get 1810 (vars sf0)).
    Time ssearch_in_var (
      (@SBinop RV32I.reg_t RV32I.ext_fn_t (UEq true)
        (SConst (Bits bs)) (SVar 1160))
    ) (vars sf0) 1810%positive
    (@SConst RV32I.reg_t RV32I.ext_fn_t (Bits [true])) (bits_t 1).
    intro A.
    apply extract_bits_32 in H1. do 32 destruct H1 as [? H1]. subst bs.
    trim A. { vm_compute. reflexivity. }
    trim A.
    {
      econstructor.
      - econstructor. econstructor. auto.
      - econstructor. vm_compute. auto.
      - econstructor.
    }
    trim A. { repeat econstructor. }
    trim A.
    {
      eapply ReplaceSubact.interp_sact_iff_from_implies; eauto.
      - apply wfsf.
      - apply wfsf.
      - repeat econstructor.
      - intros.
        eapply (interp_sact_do_eval_sact) in H.
        {
          unfold do_eval_sact in H. unfold eval_sact in H.
          unfold Interpretation.eval_sact in H.
          vm_compute Nat.add in H.
          cbn fix in H. cbn match in H. cbn beta in H.
          fold (
            @Interpretation.eval_sact
              RV32I.reg_t RV32I.ext_fn_t REnv ctx ext_sigma
          ) in H.
          unfold Interpretation.eval_sact in H at 1.
          unfold opt_bind in H.
          destr_in H. 2: discriminate H.
          cbn in Heqo.
          inv H7. apply extract_bits_32 in H2. do 32 destruct H2 as [? H2].
          subst bs.
          unfold opt_bind in Heqo.
          apply Some_inj in Heqo. subst v.
          vm_compute Datatypes.length in H.
          unfold UntypedSemantics.sigma2 in H.
          destr_in H; apply Some_inj in H; subst ov.
          2: constructor.
          exfalso. apply address_neq. repeat f_equal.
          apply val_beq_correct in Heqb.
          replace [
            false; true; true; true; true; true; true; true; true;
            true; true; true; true; true; true; true; true; true;
            true; true; true; true; true; true; true; true; true;
            true; true; true; true; true
          ] with (
            vect_to_list
            Ob~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~0
          ) in Heqb. 2: auto.
          rewrite and_equiv in Heqb.
          assert (forall x1 x2, Bits x1 = Bits x2 -> x1 = x2) as Bits_inj.
          { intros. injection H. auto. }
          apply Bits_inj in Heqb.
          rewrite <- vect_to_list_of_list in Heqb at 1.
          apply vect_to_list_inj in Heqb.
          rewrite Heqb.
          reflexivity.
        }
        apply wfsf.
        econstructor. econstructor. constructor. auto.
        econstructor. reflexivity.
        constructor.
    } Unshelve. 2: apply RV32I.R. 2: apply RV32I.Sigma.
    trim A. inversion 1.
    exploit_subact. clear A. isolate_sf.
    Eval vm_compute in (Maps.PTree.get 1538 (vars sf0)).
    Time ssearch_in_var (
      (@SBinop RV32I.reg_t RV32I.ext_fn_t (UEq true)
        (SConst (Bits
          [x2; x4; x5; x6; x7; x8; x9; x10; x36; x37; x38; x39;
           x40; x41; x42; x43; x44; x45; x46; x47; x48; x49; x50;
           x51; x52; x53; x54; x55; x56; x57; x58; x59]))
      (SVar 1160))
    ) (vars sf0) 1538%positive
    (@SConst RV32I.reg_t RV32I.ext_fn_t (Bits [true])) (bits_t 1).
    intro A.
    trim A. { vm_compute. reflexivity. }
    trim A.
    {
      econstructor.
      - econstructor. econstructor. vm_compute. eauto.
      - econstructor. vm_compute. auto.
      - econstructor.
    }
    trim A. { repeat econstructor. }
    trim A.
    {
      eapply ReplaceSubact.interp_sact_iff_from_implies; eauto.
      - apply wfsf.
      - apply wfsf.
      - repeat econstructor.
      - intros.
        eapply (interp_sact_do_eval_sact) in H.
        {
          unfold do_eval_sact in H. unfold eval_sact in H.
          unfold Interpretation.eval_sact in H.
          vm_compute Nat.add in H.
          cbn fix in H. cbn match in H. cbn beta in H.
          fold (@Interpretation.eval_sact RV32I.reg_t RV32I.ext_fn_t REnv ctx ext_sigma) in H.
          unfold Interpretation.eval_sact in H at 1.
          unfold opt_bind in H.
          destr_in H. 2: discriminate H.
          cbn in Heqo.
          inv H7. apply extract_bits_32 in H2. do 32 destruct H2 as [? H2]. subst bs.
          unfold opt_bind in Heqo.
          apply Some_inj in Heqo. subst v.
          vm_compute Datatypes.length in H.
          unfold UntypedSemantics.sigma2 in H.
          destr_in H; apply Some_inj in H; subst ov.
          2: constructor.
          exfalso. apply address_neq. repeat f_equal.
          apply val_beq_correct in Heqb.
          replace [
            false; true; true; true; true; true; true; true; true;
            true; true; true; true; true; true; true; true; true;
            true; true; true; true; true; true; true; true; true;
            true; true; true; true; true
          ] with (
            vect_to_list
            Ob~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~0
          ) in Heqb. 2: auto.
          rewrite and_equiv in Heqb.
          assert (forall x1 x2, Bits x1 = Bits x2 -> x1 = x2) as Bits_inj.
          { intros. injection H. auto. }
          apply Bits_inj in Heqb.
          rewrite <- vect_to_list_of_list in Heqb at 1.
          apply vect_to_list_inj in Heqb.
          rewrite Heqb.
          reflexivity.
        }
        apply wfsf.
        econstructor. econstructor. constructor. auto.
        econstructor. reflexivity.
        constructor.
    } Unshelve. 2: apply RV32I.R. 2: apply RV32I.Sigma.
    trim A. inversion 1.
    exploit_subact. clear A. isolate_sf.
    Eval vm_compute in (Maps.PTree.get 1530 (vars sf0)).
    Time ssearch_in_var (
      (@SBinop RV32I.reg_t RV32I.ext_fn_t (UEq true)
        (SConst (Bits
          [x2; x4; x5; x6; x7; x8; x9; x10; x36; x37; x38; x39;
           x40; x41; x42; x43; x44; x45; x46; x47; x48; x49; x50;
           x51; x52; x53; x54; x55; x56; x57; x58; x59]))
      (SVar 1160))
    ) (vars sf0) 1530%positive
    (@SConst RV32I.reg_t RV32I.ext_fn_t (Bits [true])) (bits_t 1).
    intro A.
    trim A. { vm_compute. reflexivity. }
    trim A.
    {
      econstructor.
      - econstructor. econstructor. vm_compute. eauto.
      - econstructor. vm_compute. auto.
      - econstructor.
    }
    trim A. { repeat econstructor. }
    trim A.
    {
      eapply ReplaceSubact.interp_sact_iff_from_implies; eauto.
      - apply wfsf.
      - apply wfsf.
      - repeat econstructor.
      - intros.
        eapply (interp_sact_do_eval_sact) in H.
        {
          unfold do_eval_sact in H. unfold eval_sact in H.
          unfold Interpretation.eval_sact in H.
          vm_compute Nat.add in H.
          cbn fix in H. cbn match in H. cbn beta in H.
          fold (@Interpretation.eval_sact RV32I.reg_t RV32I.ext_fn_t REnv ctx ext_sigma) in H.
          unfold Interpretation.eval_sact in H at 1.
          unfold opt_bind in H.
          destr_in H. 2: discriminate H.
          cbn in Heqo.
          inv H7. apply extract_bits_32 in H2. do 32 destruct H2 as [? H2]. subst bs.
          unfold opt_bind in Heqo.
          apply Some_inj in Heqo. subst v.
          vm_compute Datatypes.length in H.
          unfold UntypedSemantics.sigma2 in H.
          destr_in H; apply Some_inj in H; subst ov.
          2: constructor.
          exfalso. apply address_neq. repeat f_equal.
          apply val_beq_correct in Heqb.
          replace [
            false; true; true; true; true; true; true; true; true;
            true; true; true; true; true; true; true; true; true;
            true; true; true; true; true; true; true; true; true;
            true; true; true; true; true
          ] with (
            vect_to_list
            Ob~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~0
          ) in Heqb. 2: auto.
          rewrite and_equiv in Heqb.
          assert (forall x1 x2, Bits x1 = Bits x2 -> x1 = x2) as Bits_inj.
          { intros. injection H. auto. }
          apply Bits_inj in Heqb.
          rewrite <- vect_to_list_of_list in Heqb at 1.
          apply vect_to_list_inj in Heqb.
          rewrite Heqb.
          reflexivity.
        }
        apply wfsf.
        econstructor. econstructor. constructor. auto.
        econstructor. reflexivity.
        constructor.
    } Unshelve. 2: apply RV32I.R. 2: apply RV32I.Sigma.
    trim A. inversion 1.
    exploit_subact. clear A. isolate_sf.
    Eval vm_compute in (Maps.PTree.get 1385 (vars sf0)).
    Time ssearch_in_var (
      (@SBinop RV32I.reg_t RV32I.ext_fn_t (UEq true)
        (SConst (Bits
          [x2; x4; x5; x6; x7; x8; x9; x10; x36; x37; x38; x39;
           x40; x41; x42; x43; x44; x45; x46; x47; x48; x49; x50;
           x51; x52; x53; x54; x55; x56; x57; x58; x59]))
      (SVar 1160))
    ) (vars sf0) 1385%positive
    (@SConst RV32I.reg_t RV32I.ext_fn_t (Bits [true])) (bits_t 1).
    intro A.
    trim A. { vm_compute. reflexivity. }
    trim A.
    {
      econstructor.
      - econstructor. econstructor. vm_compute. eauto.
      - econstructor. vm_compute. auto.
      - econstructor.
    }
    trim A. { repeat econstructor. }
    trim A.
    {
      eapply ReplaceSubact.interp_sact_iff_from_implies; eauto.
      - apply wfsf.
      - apply wfsf.
      - repeat econstructor.
      - intros.
        eapply (interp_sact_do_eval_sact) in H.
        {
          unfold do_eval_sact in H. unfold eval_sact in H.
          unfold Interpretation.eval_sact in H.
          vm_compute Nat.add in H.
          cbn fix in H. cbn match in H. cbn beta in H.
          fold (@Interpretation.eval_sact RV32I.reg_t RV32I.ext_fn_t REnv ctx ext_sigma) in H.
          unfold Interpretation.eval_sact in H at 1.
          unfold opt_bind in H.
          destr_in H. 2: discriminate H.
          cbn in Heqo.
          inv H7. apply extract_bits_32 in H2. do 32 destruct H2 as [? H2]. subst bs.
          unfold opt_bind in Heqo.
          apply Some_inj in Heqo. subst v.
          vm_compute Datatypes.length in H.
          unfold UntypedSemantics.sigma2 in H.
          destr_in H; apply Some_inj in H; subst ov.
          2: constructor.
          exfalso. apply address_neq. repeat f_equal.
          apply val_beq_correct in Heqb.
          replace [
            false; true; true; true; true; true; true; true; true;
            true; true; true; true; true; true; true; true; true;
            true; true; true; true; true; true; true; true; true;
            true; true; true; true; true
          ] with (
            vect_to_list
            Ob~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~0
          ) in Heqb. 2: auto.
          rewrite and_equiv in Heqb.
          assert (forall x1 x2, Bits x1 = Bits x2 -> x1 = x2) as Bits_inj.
          { intros. injection H. auto. }
          apply Bits_inj in Heqb.
          rewrite <- vect_to_list_of_list in Heqb at 1.
          apply vect_to_list_inj in Heqb.
          rewrite Heqb.
          reflexivity.
        }
        apply wfsf.
        econstructor. econstructor. constructor. auto.
        econstructor. reflexivity.
        constructor.
    } Unshelve. 2: apply RV32I.R. 2: apply RV32I.Sigma.
    trim A. inversion 1.
    exploit_subact. clear A. isolate_sf.
    full_pass_c.
    full_pass_c.
    full_pass_c.
    clear and_equiv.
    clear positions.
    clear positions0.
    clear positions1.
    clear positions2.
    destruct ret_instr as [ret_instr1 | ret_instr2].
    + destruct ret_instr1 as ((rd_1_or_5 & rd_neq_rs1) & rs1_1_or_5).
      assert (x11 = true /\ x12 = false /\ x14 = false /\ x15 = false)
        as rd_1_or_5' by (clear - rd_1_or_5; intuition). clear rd_1_or_5.
      assert (x19 = true /\ x20 = false /\ x22 = false /\ x23 = false)
        as rs1_1_or_5' by (clear - rs1_1_or_5; intuition). clear rs1_1_or_5.
      destr_and_in rd_1_or_5'; destr_and_in rs1_1_or_5'; subst.
      assert (x13 <> x21) as rd_neq_rs1' by intuition; clear rd_neq_rs1.
      destruct x13, x21; try congruence; clear rd_neq_rs1'.
      * full_pass_c. full_pass_c. full_pass_c. full_pass_c.
        full_pass_c. full_pass_c.
        destruct k0, k1, k2; try (exfalso; apply not_empty; reflexivity);
        simpl in EQ; vm_compute in EQ; inv EQ; symmetry in H0; exploit_reg H0;
        do 2 full_pass_c; destruct x0; crusher_c 3.
      * full_pass_c. full_pass_c. full_pass_c. full_pass_c.
        full_pass_c. full_pass_c.
        destruct k0, k1, k2; try (exfalso; apply not_empty; reflexivity);
        simpl in EQ; vm_compute in EQ; inv EQ; symmetry in H0; exploit_reg H0;
        do 2 full_pass_c; destruct x0; crusher_c 3.
    + destruct ret_instr2 as ((rd_neq_1 & rd_neq_5) & rs1_1_or_5).
      assert (x19 = true /\ x20 = false /\ x22 = false /\ x23 = false)
        as rs1_1_or_5' by (clear - rs1_1_or_5; intuition). clear rs1_1_or_5.
      destr_and_in rs1_1_or_5'; subst.
      isolate_sf.

      Eval vm_compute in (Maps.PTree.get 1810 (vars sf0)).

      Time ssearch_in_var
        (@SBinop RV32I.reg_t RV32I.ext_fn_t (UEq false)
          (SConst (Bits [x11; x12; x13; x14; x15]))
          (SConst (Bits [true; false; true; false; false])))
        (vars sf0) 1810%positive
        (@SConst RV32I.reg_t RV32I.ext_fn_t (Bits [false])) (bits_t 1).
      intro A.
      trim A. { vm_compute. reflexivity. }
      trim A.
      {
        econstructor.
        - econstructor. econstructor. eauto.
        - econstructor. econstructor. eauto.
        - econstructor.
      }
      trim A. { repeat econstructor. }
      trim A.
      {
        eapply ReplaceSubact.interp_sact_iff_from_implies; eauto.
        - apply wfsf.
        - apply wfsf.
        - repeat econstructor.
        - intros.
          inv H. inv H11. inv H9. inv H12.
          destr. 2: econstructor. exfalso.
          rewrite ! andb_true_iff in Heqb.
          rewrite ! Bool.eqb_true_iff in Heqb.
          repeat destruct Heqb as (? & Heqb).
          subst.
          repeat destruct rd_neq_5 as [wrong | rd_neq_5]; try now apply wrong.
          now apply rd_neq_5.
      }
      trim A. inversion 1.
      exploit_subact. clear A. isolate_sf.
      Time ssearch_in_var
        (@SBinop RV32I.reg_t RV32I.ext_fn_t (UEq false)
          (SConst (Bits [x11; x12; x13; x14; x15]))
          (SConst (Bits [true; false; false; false; false])))
        (vars sf0) 1810%positive
        (@SConst RV32I.reg_t RV32I.ext_fn_t (Bits [false])) (bits_t 1).
      intro A.
      trim A. { vm_compute. reflexivity. }
      trim A.
      {
        econstructor.
        - econstructor. econstructor. eauto.
        - econstructor. econstructor. eauto.
        - econstructor.
      }
      trim A. { repeat econstructor. }
      trim A.
      {
        eapply ReplaceSubact.interp_sact_iff_from_implies; eauto.
        - apply wfsf.
        - apply wfsf.
        - repeat econstructor.
        - intros.
          inv H. inv H11. inv H9. inv H12.
          destr. 2: econstructor. exfalso.
          rewrite ! andb_true_iff in Heqb.
          rewrite ! Bool.eqb_true_iff in Heqb.
          repeat destruct Heqb as (? & Heqb).
          subst.
          repeat destruct rd_neq_1 as [wrong | rd_neq_1]; try now apply wrong.
          now apply rd_neq_1.
      }
      trim A. inversion 1.
      exploit_subact. clear A. isolate_sf.
      Eval vm_compute in (Maps.PTree.get 1249 (vars sf0)).
      Time ssearch_in_var
        (@SBinop RV32I.reg_t RV32I.ext_fn_t (UEq false)
          (SConst (Bits [x11; x12; x13; x14; x15]))
          (SConst (Bits [true; false; true; false; false])))
        (vars sf0) 1249%positive
        (@SConst RV32I.reg_t RV32I.ext_fn_t (Bits [false])) (bits_t 1).
      intro A.
      trim A. { vm_compute. reflexivity. }
      trim A.
      {
        econstructor.
        - econstructor. econstructor. eauto.
        - econstructor. econstructor. eauto.
        - econstructor.
      }
      trim A. { repeat econstructor. }
      trim A.
      {
        eapply ReplaceSubact.interp_sact_iff_from_implies; eauto.
        - apply wfsf.
        - apply wfsf.
        - repeat econstructor.
        - intros.
          inv H. inv H11. inv H9. inv H12.
          destr. 2: econstructor. exfalso.
          rewrite ! andb_true_iff in Heqb.
          rewrite ! Bool.eqb_true_iff in Heqb.
          repeat destruct Heqb as (? & Heqb).
          subst.
          repeat destruct rd_neq_5 as [wrong | rd_neq_5]; try now apply wrong.
          now apply rd_neq_5.
      }
      trim A. inversion 1.
      exploit_subact. clear A. isolate_sf.
      Time ssearch_in_var
        (@SBinop RV32I.reg_t RV32I.ext_fn_t (UEq false)
          (SConst (Bits [x11; x12; x13; x14; x15]))
(SConst (Bits [true; false; false; false; false])))
        (vars sf0) 1249%positive
        (@SConst RV32I.reg_t RV32I.ext_fn_t (Bits [false])) (bits_t 1).
      intro A.
      trim A. { vm_compute. reflexivity. }
trim A.
      {
        econstructor.
        - econstructor. econstructor. eauto.
        - econstructor. econstructor. eauto.
        - econstructor.
      }
      trim A. { repeat econstructor. }
      trim A.
      {
        eapply ReplaceSubact.interp_sact_iff_from_implies; eauto.
        - apply wfsf.
        - apply wfsf.
        - repeat econstructor.
        - intros.
          inv H. inv H11. inv H9. inv H12.
          destr. 2: econstructor. exfalso.
          rewrite ! andb_true_iff in Heqb.
          rewrite ! Bool.eqb_true_iff in Heqb.
          repeat destruct Heqb as (? & Heqb).
          subst.
          repeat destruct rd_neq_1 as [wrong | rd_neq_1]; try now apply wrong.
          now apply rd_neq_1.
      }
      trim A. inversion 1.
      exploit_subact. clear A. isolate_sf.
      Eval vm_compute in (Maps.PTree.get 1252 (vars sf0)).
      Time ssearch_in_var
        (@SBinop RV32I.reg_t RV32I.ext_fn_t (UEq false)
          (SConst (Bits [x11; x12; x13; x14; x15]))
          (SConst (Bits [true; false; true; false; false])))
        (vars sf0) 1252%positive
        (@SConst RV32I.reg_t RV32I.ext_fn_t (Bits [false])) (bits_t 1).
      intro A.
      trim A. { vm_compute. reflexivity. }
      trim A.
      {
        econstructor.
        - econstructor. econstructor. eauto.
        - econstructor. econstructor. eauto.
        - econstructor.
      }
      trim A. { repeat econstructor. }
      trim A.
      {
        eapply ReplaceSubact.interp_sact_iff_from_implies; eauto.
        - apply wfsf.
        - apply wfsf.
        - repeat econstructor.
        - intros.
          inv H. inv H11. inv H9. inv H12.
          destr. 2: econstructor. exfalso.
          rewrite ! andb_true_iff in Heqb.
          rewrite ! Bool.eqb_true_iff in Heqb.
          repeat destruct Heqb as (? & Heqb).
          subst.
          repeat destruct rd_neq_5 as [wrong | rd_neq_5]; try now apply wrong.
          now apply rd_neq_5.
      }
      trim A. inversion 1.
      exploit_subact. clear A. isolate_sf.
      full_pass_c. full_pass_c.
      full_pass_c. full_pass_c.
      full_pass_c. full_pass_c.
      isolate_sf.
      Eval vm_compute in (Maps.PTree.get 1810 (vars sf0)).
      Time ssearch_in_var
        (@SBinop RV32I.reg_t RV32I.ext_fn_t (UEq false)
          (SConst (Bits [x11; x12; x13; x14; x15]))
          (SConst (Bits [true; false; x21; false; false])))
        (vars sf0) 1810%positive
        (@SConst RV32I.reg_t RV32I.ext_fn_t (Bits [false])) (bits_t 1).
      intro A.
      trim A. { vm_compute. reflexivity. }
      trim A.
      {
        econstructor.
        - econstructor. econstructor. eauto.
        - econstructor. econstructor. eauto.
        - econstructor.
      }
      trim A. { repeat econstructor. }
      trim A.
      {
        eapply ReplaceSubact.interp_sact_iff_from_implies; eauto.
        - apply wfsf.
        - apply wfsf.
        - repeat econstructor.
        - intros.
          inv H. inv H11. inv H9. inv H12.
          destr. 2: econstructor. exfalso.
          rewrite ! andb_true_iff in Heqb.
          rewrite ! Bool.eqb_true_iff in Heqb.
          repeat destruct Heqb as (? & Heqb).
          subst.
          destruct x21.
          repeat destruct rd_neq_5 as [wrong | rd_neq_5]; try now apply wrong.
          now apply rd_neq_5.
          repeat destruct rd_neq_1 as [wrong | rd_neq_1]; try now apply wrong.
          now apply rd_neq_1.
      }
      trim A. inversion 1.
      exploit_subact. clear A. isolate_sf.
      destruct k0, k1, k2; try (exfalso; apply not_empty; reflexivity);
        do 3 full_pass_c; destruct x0, x21; crusher_c 3.
      Time Qed. (* ~190s *)

Lemma sstack_violation_results_in_halt:
  forall
    (SstackActivated: getenv REnv ctx RV32I.sstack_activated = Bits [true])
    (NoHalt: getenv REnv ctx RV32I.halt = Bits [false])
    (Valid:
      getenv REnv ctx (RV32I.d2e RV32I.fromDecode.valid0) = Bits [true])
    v2
    (DecodeDInst:
      get_field (getenv REnv ctx (RV32I.d2e RV32I.fromDecode.data0)) "dInst"
      = Some v2)
    (LegalOk: get_field v2 "legal" = Some (Bits [true]))
    (CanEnq:
      getenv REnv ctx (RV32I.e2w RV32I.fromExecute.valid0) = Bits [false])
    imm_v
    (ImmV:
      get_field v2 "immediateType"
      = Some
          (Struct
            (Std.Maybe (enum_t imm_type))
            [Bits [true]; Enum imm_type imm_v])
    )
    inst_v (InstV: get_field v2 "inst" = Some (Bits inst_v))
    (imm_coherent:
      match get_imm_name inst_v with
      | None => False
      | Some name =>
        match vect_index name imm_type.(enum_members) with
        | Some idx =>
          list_beq bool Bool.eqb
            (vect_to_list (vect_nth imm_type.(enum_bitpatterns) idx))
            imm_v
          = true
        | None => False
        end
      end
    ),
  sstack_violation ctx -> halt_set ctx.
Proof.
  intros.
  destruct H. eapply sstack_underflow_results_in_halt; eassumption.
  destruct H. eapply sstack_overflow_results_in_halt; eassumption.
  eapply sstack_address_violation_results_in_halt; eassumption.
Qed.

Definition non_sstack_vars_eq (ctx ctx' : env_t REnv (fun _ => val)) :=
  (forall r, getenv REnv ctx (RV32I.toIMem r) = getenv REnv ctx' (RV32I.toIMem r))
  /\ (forall r, getenv REnv ctx (RV32I.fromIMem r) = getenv REnv ctx' (RV32I.fromIMem r))
  /\ (forall r, getenv REnv ctx (RV32I.toDMem r) = getenv REnv ctx' (RV32I.toDMem r))
  /\ (forall r, getenv REnv ctx (RV32I.fromDMem r) = getenv REnv ctx' (RV32I.fromDMem r))
  /\ (forall r, getenv REnv ctx (RV32I.f2d r) = getenv REnv ctx' (RV32I.f2d r))
  /\ (forall r, getenv REnv ctx (RV32I.f2dprim r) = getenv REnv ctx' (RV32I.f2dprim r))
  /\ (forall r, getenv REnv ctx (RV32I.d2e r) = getenv REnv ctx' (RV32I.d2e r))
  /\ (forall r, getenv REnv ctx (RV32I.e2w r) = getenv REnv ctx' (RV32I.e2w r))
  /\ (forall r, getenv REnv ctx (RV32I.rf r) = getenv REnv ctx' (RV32I.rf r))
  /\ (forall r, getenv REnv ctx (RV32I.scoreboard r) = getenv REnv ctx' (RV32I.scoreboard r))
  /\ (getenv REnv ctx RV32I.pc = getenv REnv ctx' RV32I.pc)
  /\ (getenv REnv ctx RV32I.cycle_count = getenv REnv ctx' RV32I.cycle_count)
  /\ (getenv REnv ctx RV32I.instr_count = getenv REnv ctx' RV32I.instr_count)
  /\ (getenv REnv ctx RV32I.epoch = getenv REnv ctx' RV32I.epoch)
  /\ (getenv REnv ctx RV32I.halt_emitted= getenv REnv ctx' RV32I.halt_emitted)
  /\ (getenv REnv ctx RV32I.halt = getenv REnv ctx' RV32I.halt).

Lemma sstack_deactivated_impl_sstack_values_preserved :
  forall
    (ctx : env_t REnv (fun _ => val)) (WTRENV : Wt.wt_renv RV32I.R REnv ctx),
  getenv REnv ctx RV32I.sstack_activated = Bits [false]
  -> forall r,
     getenv REnv (interp_cycle ctx ext_sigma sf) (RV32I.sstack r)
     = getenv REnv ctx (RV32I.sstack r).
Proof.
  intros. assert (wfsf := sf_wf).
  remember (
    List.map (RV32I.sstack) (finite_elements (T := RV32I.ShadowStack.reg_t))
  ) as regs.
  vm_compute in Heqregs.
  erewrite Prune.prune_irrelevant_l_interp_cycle_ok.
  2-5: eauto.
  2: {
    instantiate (1 := regs).
    destruct r; subst. now left.
    simpl in n.
    destruct n. right. now left.
    repeat (destruct a); repeat (right; try now left).
  }
  update_wfsf.
  isolate_sf.
  subst.
  unfold Prune.prune_irrelevant_l in sf0.
  vm_compute filter in sf0.
  vm_compute list_options_to_list in sf0.
  vm_compute map in sf0.
  vm_compute Prune.pos_union in sf0.
  vm_compute filter_ptree in sf0.
  exploit_regs.
  isolate_sf.
  destruct r.
  - full_pass_c. full_pass_c. full_pass_c.
    destruct (getenv REnv ctx0 (RV32I.sstack RV32I.ShadowStack.size)) eqn:?;
    try (
      red in WTRENV0;
      specialize WTRENV0 with (RV32I.sstack RV32I.ShadowStack.size);
      rewrite Heqv in WTRENV0; vm_compute in WTRENV0; inv WTRENV0; fail
    ).
    simplify_sifs. prune. collapse.
    simplify_sifs. prune. collapse.
    simplify_sifs. prune. collapse.
    simplify_sifs. prune. collapse.
    simplify_sifs.
    isolate_sf.
    crusher_c 1.
  - unfold RV32I.ShadowStack.capacity in n. simpl in n.
    destruct (getenv REnv ctx0 (RV32I.sstack (RV32I.ShadowStack.stack n))) eqn:?;
    try (
      red in WTRENV0;
      specialize WTRENV0 with (RV32I.sstack (RV32I.ShadowStack.stack n));
      rewrite Heqv in WTRENV0; vm_compute in WTRENV0; inv WTRENV0; fail
    ).
    destruct n.
    + full_pass_c. full_pass_c. full_pass_c.
      do 4 (simplify_sifs; prune; collapse). simplify_sifs.
      crusher_c 1.
    + repeat destruct a.
      { do 3 full_pass_c. do 4 (simplify_sifs; prune; collapse). simplify_sifs.
        crusher_c 1. }
      { do 3 full_pass_c. do 4 (simplify_sifs; prune; collapse). simplify_sifs.
        crusher_c 1. }
      { do 3 full_pass_c. do 4 (simplify_sifs; prune; collapse). simplify_sifs.
        crusher_c 1. }
      { do 3 full_pass_c. do 4 (simplify_sifs; prune; collapse). simplify_sifs.
        crusher_c 1. }
      { do 3 full_pass_c. do 4 (simplify_sifs; prune; collapse). simplify_sifs.
        crusher_c 1. }
      { do 3 full_pass_c. do 4 (simplify_sifs; prune; collapse). simplify_sifs.
        crusher_c 1. }
      { do 3 full_pass_c. do 4 (simplify_sifs; prune; collapse). simplify_sifs.
        crusher_c 1. }
Time Qed. (* =~ 40s *)

(*         step
    c1 ------------> c1'
    |                |
 eq |                | eq
    |                |
    c2 ------------> c2'
           step
 *)

Ltac autosplit :=
  try match goal with
  | |- _ /\ _ => split; autosplit
  end.

(* Lemma step_preserves_non_sstack_vars_eq_when_no_sstack_violation: *)
(*   forall *)
(*     (ctx': env_t REnv (fun _ => val)) (WTRENV': Wt.wt_renv RV32I.R REnv ctx'), *)
(*   getenv REnv ctx RV32I.sstack_activated = Bits [true] *)
(*   -> getenv REnv ctx' RV32I.sstack_activated = Bits [false] *)
(*   -> non_sstack_vars_eq ctx ctx' *)
(*   -> non_sstack_vars_eq *)
(*        (interp_cycle ctx ext_sigma sf) (interp_cycle ctx' ext_sigma sf). *)
(* Proof. *)

Lemma non_sstack_vars_eq_sym :
  forall c1 c2, non_sstack_vars_eq c1 c2 <-> non_sstack_vars_eq c2 c1.
Proof.
  intros. split; intro;
  red in H; repeat destruct H as (? & H);
  repeat split; try intro; symmetry; auto.
Qed.

(* Lemma step_preserves_non_sstack_vars_eq_when_no_sstack_violation: *)
(*   forall (ctx': env_t REnv (fun _ => val)) b, *)
(*   (getenv REnv ctx RV32I.sstack_activated = Bits [b]) *)
(*   -> (getenv REnv ctx' RV32I.sstack_activated = Bits [negb b]) *)
(*   -> non_sstack_vars_eq ctx ctx' *)
(*   -> non_sstack_vars_eq *)
(*        (interp_cycle ctx ext_sigma sf) (interp_cycle ctx' ext_sigma sf). *)
(* Proof. *)

Definition cycle (r: env_t ContextEnv (fun _ : RV32I.reg_t => val)) :=
  UntypedSemantics.interp_dcycle drules r ext_sigma rv_schedule.

Definition env_type := env_t REnv RV32I.R.
Definition initial_env := create REnv RV32I.r.

Definition CEnv := @ContextEnv RV32I.reg_t RV32I.FiniteType_reg_t.
Definition initial_context_env := CEnv.(create) (RV32I.r).

Definition f_init := fun x => val_of_value (initial_context_env.[x]).

  End proof.
End RVProofs.
