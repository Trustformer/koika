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

  (* temp TODO remove, import ShadowStackProperties.v instead *)
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
      getenv REnv ctx (RV32I.stack (RV32I.ShadowStack.size))
      = @val_of_value
        (bits_t RV32I.ShadowStack.index_sz)
        (Bits.of_nat (RV32I.ShadowStack.index_sz) 0).

    Definition sstack_full (ctx: env_t REnv (fun _ : RV32I.reg_t => val))
    : Prop :=
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
                      (Bits.of_N (Datatypes.length ((ubits_of_value rs1_val)))
                         (Bits.to_N (Bits.of_list (ubits_of_value rs1_val)) +
                            Bits.to_N (Bits.of_list (List.skipn 20 (ubits_of_value inst_val)))))
                      (Vect.Bits.neg (Bits.of_N (Datatypes.length (ubits_of_value rs1_val)) 1))
                ) in
            Some (Bits.of_N 32 bits)
          | None => None
          end
        | _, _ => None
        end
      | _ => None
      end.

    (* TODO should never return None, simplify? *)
    Definition sstack_top_address (ctx: env_t REnv (fun _ : RV32I.reg_t => val))
    : option (bits_t 32) :=
      let index_raw := getenv REnv ctx (RV32I.stack RV32I.ShadowStack.size) in
      let index_nat := pred (Bits.to_nat (vect_of_list (ubits_of_value index_raw))) in
      let index := index_of_nat (pow2 RV32I.ShadowStack.index_sz) index_nat in
      match index with
      | Some x =>
        let data_raw :=
          (getenv REnv ctx (RV32I.stack (RV32I.ShadowStack.stack x))) in
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

    Lemma extract_bits_3:
      forall {A: Type} bs,
      Datatypes.length (A := A) bs = 3
      ->
      exists k0 k1 k2,
      bs = [
        k0; k1; k2
      ].
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

    Definition imm_coherent
      v imm_v inst_v (DecodeDInst:
        get_field (getenv REnv ctx (RV32I.d2e RV32I.fromDecode.data0)) "dInst"
        = Some v)
      (imm_v: get_field v "immediateType" = Some imm_v)
      (inst_v: get_field v "inst" = Some inst_v)
    :=
      match get_opcode_i_type inst_v with
      | SType  => ImmS
      | BType  => ImmB
      | UType  => ImmU
      | JType  => ImmJ
      | IType  => ImmI
      | _ => ImmI
      end.

    Lemma sstack_violation_results_in_halt:
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
      sstack_violation ctx -> halt_set ctx.
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
      - admit. (* red in under.
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
            collapse.
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
              crusher_c 3; intuition congruence.*)
      (* - admit. *)
      - destruct over as [
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
          Eval vm_compute in (Maps.PTree.elements (vars sf1)).
          isolate_sf. fold sf0 in wfsf.
          ssearch_in_var (@SBinop RV32I.reg_t RV32I.ext_fn_t (UEq false)
                            (SConst (Bits [x0]))
                            (SConst (Bits [x0]))
                         ) (vars sf0) 992%positive
            (@SConst RV32I.reg_t RV32I.ext_fn_t (Bits [true])) (bits_t 1).
          intro A. trim A. vm_compute. reflexivity.
          trim A. repeat econstructor.
          trim A. repeat econstructor.
          trim A.
          eapply ReplaceSubact.interp_sact_iff_from_implies; eauto. apply wfsf. apply wfsf.
          repeat econstructor.
          intros. inv H. inv H9. inv H11. simpl in H12. inv H12.
          rewrite andb_true_r. rewrite eqb_reflx. constructor.
          trim A. inversion 1.
          exploit_subact. clear A. isolate_sf. fold sf2 in wfsf0.
          ssearch_in_var (@SBinop RV32I.reg_t RV32I.ext_fn_t (UEq false)
                            (SConst (Bits [x0]))
                            (SConst (Bits [x0]))
                         ) (vars sf2) 1788%positive
            (@SConst RV32I.reg_t RV32I.ext_fn_t (Bits [true])) (bits_t 1).
          intro A. trim A. vm_compute. reflexivity.
          trim A. repeat econstructor.
          trim A. repeat econstructor.
          trim A.
          eapply ReplaceSubact.interp_sact_iff_from_implies; eauto. apply wfsf0. apply wfsf0.
          repeat econstructor.
          intros. inv H. inv H9. inv H11. simpl in H12. inv H12.
          rewrite andb_true_r. rewrite eqb_reflx. constructor.
          trim A. inversion 1.
          exploit_subact. clear A. isolate_sf. fold sf3 in wfsf.
          Eval vm_compute in (Maps.PTree.elements (vars sf1)).
          get_subact_ok ((@SBinop RV32I.reg_t RV32I.ext_fn_t (UBits2 UOr)
                     (SBinop (UEq false) (SConst (Bits [true; false; x13; false; false]))
                        (SConst (Bits [true; false; false; false; false])))
                     (SBinop (UEq false) (SConst (Bits [true; false; x13; false; false]))
                        (SConst (Bits [true; false; true; false; false])))))
            (vars sf3)
            (@SConst RV32I.reg_t RV32I.ext_fn_t (Bits [true])) (bits_t 1)
          .
          intro A.
          trim A. repeat econstructor.
          trim A. repeat econstructor.
          trim A.
          eapply ReplaceSubact.interp_sact_iff_from_implies; eauto. apply wfsf. apply wfsf.
          repeat econstructor.
          intros. inv H. inv H9. inv H11. inv H5. inv H13. inv H9. inv H15. simpl in H14, H16. inv H14; inv H16.
          simpl in H12. inv H12.
          clear. destruct x13; cbn [Bool.eqb andb]; constructor.
          trim A. inversion 1.
          exploit_subact. clear A. isolate_sf. fold sf4 in wfsf0.
          full_pass_c.
          full_pass_c.
          full_pass_c.
          full_pass_c.
          full_pass_c.
          full_pass_c.
          full_pass_c.
          full_pass_c.
          Eval vm_compute in (Maps.PTree.elements (vars sf1)).
          exploit_var 1459%positive uconstr:(SConst (Bits [true])).
          {
            econstructor.
            intros. inv H. vm_compute in H2. inv H2.
            inv H5. destruct b; inv H11; econstructor.
            inversion 1.
            econstructor. vm_compute. reflexivity. repeat constructor.
          }
          clear VS.
          isolate_sf. fold sf2 in wfsf.
          full_pass_c.
          full_pass_c.
          full_pass_c.
          full_pass_c.
          full_pass_c.
          Eval vm_compute in (Maps.PTree.elements (vars sf6)).
          exploit_var 1788%positive uconstr:(SConst (Bits [false])).
          {
            econstructor.
            intros.
            eapply interp_sact_do_eval_sact in H.
            vm_compute in H.
            assert (OF: oldv = Bits [false]).
            clear -H. inv H. destruct x13, x19, x20, x21, x22, x23; auto.
            clear H.
            subst; constructor. apply wfsf.
            econstructor. vm_compute. reflexivity. inversion 1.
            econstructor. vm_compute. reflexivity.
            repeat constructor.
          }
          clear VS.
          isolate_sf. fold sf4 in wfsf0.
          full_pass_c.
          full_pass_c.
          full_pass_c.
          full_pass_c.
          full_pass_c.
          crusher_c 1.

      - destruct violation as (no_mispred & not_empty & pop & address_neq).
        clear no_mispred.
        unfold sstack_empty in not_empty. simpl in not_empty.
        generalize (WTRENV (RV32I.stack RV32I.ShadowStack.size)).
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
        change (pow2 3) with 8. lia.
        generalize (WTRENV (RV32I.stack (RV32I.ShadowStack.stack idx))).
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

        isolate_sf. fold sf0 in wfsf.
        ssearch_in_var (
          @SBinop
            RV32I.reg_t RV32I.ext_fn_t (UEq false)
            (SConst (Bits [x0])) (SConst (Bits [x0]))
        ) (vars sf0) 1788%positive
        (@SConst RV32I.reg_t RV32I.ext_fn_t (Bits [true])) (bits_t 1).
        intro A. trim A. vm_compute. reflexivity.
        trim A. repeat econstructor.
        trim A. repeat econstructor.
        trim A.
        eapply ReplaceSubact.interp_sact_iff_from_implies; eauto. apply wfsf.
        apply wfsf. repeat econstructor.
        intros. inv H. inv H10. inv H12. inv H13.
        rewrite Bool.eqb_reflx. unfold andb. 
        clear. constructor.
        trim A. inversion 1.
        exploit_subact. clear A. isolate_sf. fold sf2 in wfsf0.
        subst sf0. subst sf1.
        full_pass_c.

        destruct ret_instr as [ret_instr1 | ret_instr2].
        + destruct ret_instr1 as ((rd_1_or_5 & rd_neq_rs1) & rs1_1_or_5).
          assert (x11 = true /\ x12 = false /\ x14 = false /\ x15 = false)
            as rd_1_or_5' by (clear - rd_1_or_5; intuition). clear rd_1_or_5.
          assert (x19 = true /\ x20 = false /\ x22 = false /\ x23 = false)
            as rs1_1_or_5' by (clear - rs1_1_or_5; intuition). clear rs1_1_or_5.
          destr_and_in rd_1_or_5'; destr_and_in rs1_1_or_5'; subst.
          assert (x13 <> x21) as rd_neq_rs1' by intuition; clear rd_neq_rs1.
          (* Eval vm_compute in (Maps.PTree.get 1788 (vars sf0)). *)
          destruct x13, x21; try congruence; clear rd_neq_rs1'.
          * full_pass_c. full_pass_c. full_pass_c. full_pass_c. full_pass_c.
            full_pass_c. full_pass_c.
            Eval vm_compute in (Maps.PTree.get 1788 (vars sf0)).
            destruct k0, k1, k2;
              try (exfalso; apply not_empty; reflexivity); clear not_empty.
            ** simpl in EQ. vm_compute in EQ. inv EQ.
               symmetry in H0. exploit_reg H0. clear H0.
               full_pass_c.
               full_pass_c. full_pass_c. do 3 full_pass_c.
               destruct x0.
               do 2 full_pass_c.
               do 2 full_pass_c.
               Eval vm_compute in (Maps.PTree.get 1128 (vars sf0)).
               Eval vm_compute in (Maps.PTree.get 1038 (vars sf0)).
               destruct k3, k4, k5.
               *** full_pass_c. destruct x2. full_pass_c.

                   apply extract_bits_32 in H1.
                   do 32 destruct H1 as [? H1].
                   subst bs.
                   inv H7.
                   apply extract_bits_32 in H0.
                   do 32 destruct H0 as [? H0].
                   subst bs.
                   Transparent firstn.
                   simpl in address_neq.
                   collapse.
                   isolate_sf. subst sf0. fold sf1 in wfsf0. vm_compute in sf1.
                   rewrite ! Bits.of_N_to_N in address_neq.

                  Eval vm_compute in (Maps.PTree.get 1789 (vars sf1)).
                  Eval vm_compute in (Maps.PTree.get 1377 (vars sf1)).
                  Eval vm_compute in (Maps.PTree.get 1375 (vars sf1)).
                  Eval vm_compute in (Maps.PTree.get 1128 (vars sf1)).
                  Eval vm_compute in (Maps.PTree.get 1383 (vars sf1)).

                  exploit_var
                    1128%positive
                    (@SConst RV32I.reg_t RV32I.ext_fn_t
                      (Bits
                         [x49; x50; x51; x52; x53; x54; x55; x56; x57; x58; x59;
                          x60; x61; x62; x63; x64; x65; x66; x67; x68; x69; x70;
                          x71; x72; x73; x74; x75; x76; x77; x78; x79; x80])).
                    {
                      econstructor; intros.
                      {
                        inv H. simpl in H1. inv H1. inv H2. inv H5. inv H9.
                        unfold UntypedSemantics.sigma2 in H10.
                        apply Some_inj in H10. rewrite <- H10. clear H10 oldv.
                        unfold UntypedSemantics.ubits2_sigma.
                        vm_compute Datatypes.length.
                        vm_compute Bits.to_N at 2.
                        rewrite N.add_0_r.
                        rewrite Bits.of_N_to_N.
                        econstructor.
                      }
                      { inv H. }
                      { econstructor. simpl. eauto. }
                      { econstructor. econstructor. auto. }
                    }
                    {
                      clear VS.
                      Eval vm_compute in (Maps.PTree.get 1128 (vars sf1)).
                      full_pass_c. full_pass_c.
                      Eval vm_compute in (Maps.PTree.get 1377 (vars sf1)).
                      Eval vm_compute in (Maps.PTree.get 1375 (vars sf1)).
                      
                      exploit_var
                        1375%positive
                        (@SConst RV32I.reg_t RV32I.ext_fn_t (Bits [true])).
                      {
                        econstructor; intros.
                        {
                          inv H. simpl in H1. inv H1. inv H2. inv H5. inv H9.
                          unfold UntypedSemantics.sigma2 in H10.
                          unfold val_beq in H10.
                          destr_in H10.
                          { apply list_eqb_correct in Heqb. 
                            Show Proof.
                            inv Heqb.
                            TODO
                            destruct (address_neq Heqb). }
                        }
                      }
                    }



                    simpl in H10.
                    eapply interp_sact_const.
                    vm_compute. econstructor.
                    simpl in H. simpl. rewrite H.
                    econstructor. vm_compute.
                  


                   ssearch_in_var (
                     @SBinop
                       RV32I.reg_t RV32I.ext_fn_t (UEq false)
                       (SConst (Bits [x0])) (SConst (Bits [x0]))
                   ) (vars sf0) 1788%positive
        (@SConst RV32I.reg_t RV32I.ext_fn_t (Bits [true])) (bits_t 1).
        intro A. trim A. vm_compute. reflexivity.
        trim A. repeat econstructor.
        trim A. repeat econstructor.
        trim A.
        eapply ReplaceSubact.interp_sact_iff_from_implies; eauto. apply wfsf.
        apply wfsf. repeat econstructor.
        intros. inv H. inv H10. inv H12. inv H13.
        rewrite Bool.eqb_reflx. unfold andb. 
        clear. constructor.
        trim A. inversion 1.
        exploit_subact. clear A. isolate_sf. fold sf2 in wfsf0.
        subst sf0. subst sf1.
        full_pass_c.
        Eval vm_compute in (Maps.PTree.get 1128 (vars sf0)).
        
let x := eval vm_compute in (
  1128%positive,
  (bits_t 32,
   @SBinop RV32I.reg_t RV32I.ext_fn_t (UBits2 UPlus)
     (SConst
        (Bits
           [x49; x50; x51; x52; x53; x54; x55; x56; x57; x58; x59; x60; x61;
           x62; x63; x64; x65; x66; x67; x68; x69; x70; x71; x72; x73; x74;
           x75; x76; x77; x78; x79; x80]))
     (SConst
        (Bits
           [false; false; false; false; false; false; false; false; false;
           false; false; false; false; false; false; false; false; false;
           false; false; false; false; false; false; false; false; false;
           false; false; false; false; false])))
) in
probe_in_var ctx ext_sigma x.

          Opaque val_beq_bits.
          Opaque vect_to_list.
          Eval vm_compute in (
            eval_sact_no_vars ctx ext_sigma
              (SBinop (UBits2 UPlus) (SConst (Bits [x0; x1; x3])) (SConst (Bits [false; false; false])))
          ).
          Opaque Bits.of_N.
          Opaque Bits.to_N.
          Opaque UntypedSemantics.ubits2_sigma.
          cbv in (
            UntypedSemantics.ubits2_sigma UPlus [x0; x1] [x49; x48]
          ).
          Eval vm_compute in (
            vect_to_list (list_to_vec [x0; x1])
          ).
          UntypedSemantics.ubits2_sigma = 
          Eval vm_compute in (Maps.PTree.get 1383 (vars sf1)).

          destruct k3.
          full_pass_c.
          Eval vm_compute in (Maps.PTree.get 56 (vars sf0)).
          Eval vm_compute in (Maps.PTree.get 1375 (vars sf0)).
          Eval vm_compute in (Maps.PTree.get 1375 (vars sf0)).


            isolate_sf. fold sf0 in wfsf.
            ssearch_in_var (
              @SBinop
                RV32I.reg_t RV32I.ext_fn_t (UEq false)
                (SConst (Bits [k0; k1; k2])) (SConst (Bits [false; false; false]))
            ) (vars sf0) 1788%positive
            (@SConst RV32I.reg_t RV32I.ext_fn_t (Bits [true])) (bits_t 1).
            intro A. trim A. vm_compute. reflexivity.
            trim A. repeat econstructor.
            trim A. repeat econstructor.
            trim A.
            eapply ReplaceSubact.interp_sact_iff_from_implies; eauto. apply wfsf. apply wfsf.
            repeat econstructor.
            intros. inv H. inv H10. inv H12. inv H13.
            rewrite Bool.eqb_reflx. unfold andb. 
            clear. constructor.
            trim A. inversion 1.
            exploit_subact. clear A. isolate_sf. fold sf2 in wfsf0.
            subst sf0. subst sf1.
            full_pass_c.
                Eval vm_compute in (Maps.PTree.get 1788 (vars sf1)).

        rewrite Bits.of_N_to_N in ret_instr.
        collapse.
        full_pass_c. full_pass_c.
        full_pass_c. full_pass_c.
        do 4 full_pass_c.
  Qed.

  Definition cycle (r: env_t ContextEnv (fun _ : RV32I.reg_t => val)) :=
    UntypedSemantics.interp_dcycle drules r ext_sigma rv_schedule.

  Definition env_type := env_t REnv RV32I.R.
  Definition initial_env := create REnv RV32I.r.

  Definition CEnv := @ContextEnv RV32I.reg_t RV32I.FiniteType_reg_t.
  Definition initial_context_env := CEnv.(create) (RV32I.r).

  Definition f_init := fun x => val_of_value (initial_context_env.[x]).
