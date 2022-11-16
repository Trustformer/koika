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
          get_field_struct (struct_fields RV32I.decode_bookkeeping) lv "rv1"
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
              Bits.to_N (vect_of_list (
                (ubits_of_value rs1_val)
                ++ ((List.skipn 21 (ubits_of_value inst_val)) ++ [false])
            )) in
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
      let index_nat := Bits.to_nat (vect_of_list (ubits_of_value index_raw)) in
      let index := index_of_nat (pow2 RV32I.ShadowStack.index_sz) index_nat in
      match index with
      | Some x =>
        let data_raw :=
          (getenv REnv ctx (RV32I.stack (RV32I.ShadowStack.stack x))) in
        Some (Bits.of_N 32 (Bits.to_N (vect_of_list (ubits_of_value data_raw))))
      | None => None
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
      no_mispred ctx /\ sstack_pop ctx
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
      - red in under.
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
              crusher_c 3; intuition congruence.
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
          destruct (
            orb
              (andb
                (andb
                  (andb
                    (andb (Bool.eqb x19 true) (Bool.eqb x20 false))
                    (Bool.eqb x21 false))
                  (Bool.eqb x22 false))
                (Bool.eqb x23 false))
              (andb
                (andb
                  (andb
                    (andb (Bool.eqb x19 true) (Bool.eqb x20 false))
                    (Bool.eqb x21 true))
                  (Bool.eqb x22 false))
                (Bool.eqb x23 false))
          ) eqn:eq.
          * rename eq into rs1_1_or_5.
            rewrite ! orb_true_iff in rs1_1_or_5.
            rewrite ! andb_true_iff in rs1_1_or_5.
            rewrite ! eqb_true_iff in rs1_1_or_5.
            destruct rs1_1_or_5 as [rs1_1 | rs1_5], rd_1_or_5 as [rd_1 | rd_5].
            ** do 4 destruct rd_1 as [? rd_1].
               do 4 destruct rs1_1 as [rs1_1 ?].
               subst.
               collapse. full_pass_c. full_pass_c. do 4 full_pass_c.
               destruct x0; crusher_c 3.
            ** exfalso. apply not_sstack_pop. intros. clear not_sstack_pop.
               do 4 destruct rd_5 as [? rd_5].
               do 4 destruct rs1_1 as [rs1_1 ?].
               subst.
               rewrite H6 in H. inv H. inv H0. inv H2.
               rewrite Bits.of_N_to_N.
               unfold is_ret_instruction.
               simpl. reflexivity.
            ** exfalso. apply not_sstack_pop. intros. clear not_sstack_pop.
               do 4 destruct rd_1 as [? rd_1].
               do 4 destruct rs1_5 as [rs1_5 ?].
               subst.
               rewrite H6 in H. inv H. inv H0. inv H2.
               rewrite Bits.of_N_to_N.
               unfold is_ret_instruction.
               simpl. reflexivity.
            ** do 4 destruct rd_5 as [? rd_5].
               do 4 destruct rs1_5 as [rs1_5 ?].
               subst.
               collapse. full_pass_c. full_pass_c. do 4 full_pass_c.
               destruct x0; crusher_c 3.
          * clear not_sstack_pop.
            exploit_var 992%positive uconstr:(SConst (Bits [true])).
            {
              econstructor.
              intros. inv H. vm_compute in H2. inv H2.
              inv H5. inv H9. inv H2. vm_compute in H0. inv H0. inv H5. simpl in H10. inv H10.
              inv H11. vm_compute in H0. inv H0. inv H2. simpl in H12. inv H12.
              destr. constructor. rewrite andb_false_iff in Heqb. destruct Heqb. 2: congruence.
              rewrite eqb_reflx in H. congruence.
              intros. inv H. econstructor. vm_compute. reflexivity. repeat constructor.
            }
            destruct rd_1_or_5 as [rd_1 | rd_5].
            ** do 4 destruct rd_1 as [? rd_1]. subst.
               collapse. full_pass_c. full_pass_c. do 6 full_pass_c.
               destruct x0.
               *** do 3 full_pass_c.
                   destruct x19, x20, x21, x22, x23; simpl in eq;
                     try (discriminate eq); clear eq; crusher_c 2.
               *** do 3 full_pass_c.
                   destruct x19, x20, x21, x22, x23; simpl in eq;
                     try (discriminate eq); clear eq; crusher_c 2.
            ** do 4 destruct rd_5 as [? rd_5]. subst.
               collapse. full_pass_c. full_pass_c. do 6 full_pass_c.
               destruct x0; do 3 full_pass_c;
                 destruct x19, x20, x21, x22, x23; simpl in eq;
                 try (discriminate eq); clear eq; crusher_c 2.
      - destruct violation as [no_mispred [pop address_neq]].
        clear no_mispred.
        unfold sstack_pop in pop.
        inv H12. apply extract_bits_32 in H0. do 32 destruct H0 as [? H0].
        subst.
        eapply pop in H6 as ret_instr. 2-3: reflexivity.
        unfold is_ret_instruction in ret_instr.
        extract_bits_info ret_instr.
        rewrite ! negb_true_iff in ret_instr.
        rewrite ! andb_false_iff in ret_instr.
        rewrite ! eqb_false_iff in ret_instr.
        destruct ret_instr as [[opc1 opc2] ret_instr].
        do 2 destruct opc1 as [? opc1]. do 3 destruct opc2 as [? opc2]. subst.
        destruct ret_instr.
        + destruct H. destruct H.
          destruct H, H0; do 4 destruct H as [? H]; do 4 destruct H0 as [? H0];
            subst.
          * intuition.
          * unfold sstack_top_address in address_neq.
          * admit.
          * intuition.
        destruct ret_instr.
        destruct ret_instr. as [[opc1 opc2] ret_instr].
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
