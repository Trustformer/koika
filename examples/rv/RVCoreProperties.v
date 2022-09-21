(*! Proofs about our RISC-V implementation !*)
Require Import Coq.Program.Equality.
Require Import Koika.Frontend.
Require Export rv.Instructions rv.ShadowStack rv.RVCore rv.rv32 rv.rv32i.
Require Import Koika.SimpleForm.SimpleForm.
Require Import Koika.SimpleForm.SimpleFormInterpretation.
Require Import Koika.SimpleForm.SimpleFormOperations.
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
      (eql opcode_ctrl [true; true; false])
      && (
        (
          (eql opcode_rest [true; true; true; true])
          && (
            (eql rd [false; false; false; false; true])
            || (eql rd [false; false; true; false; true])))
        || (
          (eql opcode_rest [false; true; true; true])
          && (
            (eql rd [false; false; false; false; true])
            || (eql rd [false; false; true; false; true])))).

    (* This function is defined in a way that mirrors RVCore.v *)
    Definition is_ret_instruction (instr: bits_t 32) : bool :=
      let bits := vect_to_list (bits_of_value instr) in
      let opcode_ctrl := List.firstn 3 (List.skipn 4 bits) in
      let opcode_rest := List.firstn 4 (List.skipn 0 bits) in
      let rs1 := List.firstn 5 (List.skipn 15 bits) in
      let rd := List.firstn 5 (List.skipn 7 bits) in
      (eql opcode_ctrl [true; true; false])
      && (eql opcode_rest [false; true; true; true])
      && (
        (
          (
            (eql rd [false; false; false; false; true])
            || (eql rd [false; false; true; false; true]))
          && (negb (eql rd rs1))
          && (
            (eql rs1 [false; false; false; false; true])
            || (eql rs1 [false; false; true; false; true])))
        || (
          (negb (eql rd [false; false; false; false; true]))
          && (eql rd [false; false; true; false; true])
          && (
            (eql rs1 [false; false; false; false; true])
            || (eql rs1 [false; false; true; false; true])))).

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

    Lemma fail_schedule:
      forall (H: getenv REnv ctx RV32I.halt = Bits [true]),
      getenv REnv (interp_cycle ctx ext_sigma sf) RV32I.halt = Bits [true].
    Proof.
      intros. assert (wfsf := sf_wf).
      crusher 2.
    Time Qed.

    Lemma length_1_something:
      forall {A: Type} bs,
      Datatypes.length (A := A) bs = 1 -> exists k, bs = [k].
    Proof.
      intros.
      destruct bs.
      - inv H.
      - inv H. destruct bs; eauto. inv H1.
    Qed.

    Lemma length_32_something:
      forall {A: Type} bs,
      Datatypes.length (A := A) bs = 32
      ->
      exists k0, exists k1, exists k2, exists k3, exists k4, exists k5,
      exists k6, exists k7, exists k8, exists k9, exists k10, exists k11,
      exists k12, exists k13, exists k14, exists k15, exists k16, exists k17,
      exists k18, exists k19, exists k20, exists k21, exists k22, exists k23,
      exists k24, exists k25, exists k26, exists k27, exists k28, exists k29,
      exists k30, exists k31,
      bs = [
        k0; k1; k2; k3; k4; k5; k6; k7; k8; k9; k10; k11; k12; k13; k14; k15;
        k16; k17; k18; k19; k20; k21; k22; k23; k24; k25; k26; k27; k28; k29;
        k30; k31
      ].
    Proof.
      intros.
      destruct bs; inv H. destruct bs; inv H1. destruct bs; inv H0.
      destruct bs; inv H1. destruct bs; inv H0. destruct bs; inv H1.
      destruct bs; inv H0. destruct bs; inv H1. destruct bs; inv H0.
      destruct bs; inv H1. destruct bs; inv H0. destruct bs; inv H1.
      destruct bs; inv H0. destruct bs; inv H1. destruct bs; inv H0.
      destruct bs; inv H1. destruct bs; inv H0. destruct bs; inv H1.
      destruct bs; inv H0. destruct bs; inv H1. destruct bs; inv H0.
      destruct bs; inv H1. destruct bs; inv H0. destruct bs; inv H1.
      destruct bs; inv H0. destruct bs; inv H1. destruct bs; inv H0.
      destruct bs; inv H1. destruct bs; inv H0. destruct bs; inv H1.
      destruct bs; inv H0. destruct bs; inv H1. destruct bs; inv H0.
      exists
        a, a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15,
        a16, a17, a18, a19, a20, a21, a22, a23, a24, a25, a26, a27, a28, a29,
        a30.
      eauto.
    Qed.

    Lemma length_n_something:
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
        (LegalOk: get_field v2 "legal" = Some (Bits [true])),
      stack_violation ctx -> halt_set ctx.
    Proof.
      intros. assert (wfsf := sf_wf).
      unfold halt_set.
      exploit_regs.
      simplify.
      full_pass.
      simplify.
      isolate_sf.

      Eval vm_compute in Maps.PTree.get 1789 (vars sf0).
      Eval vm_compute in Maps.PTree.get 1788 (vars sf0).
      Eval vm_compute in Maps.PTree.get 13 (vars sf0).
      generalize (WTRENV (RV32I.d2e RV32I.fromDecode.data0)). intro.
      inv H0. rewrite <- H2 in *.
      simpl in H3.

      inv H3. inv H6. inv H7. inv H8. inv H9. inv H10. inv H11.
      inv H6. inv H2. inv H1. inv H11. inv H12. inv H13. inv H14. inv H15.
      inv H16.
      inv H13. inv H1. inv H16. inv H17.
      inv H13. simpl in H1.
      inv H9. inv H5. inv H10. inv H11. inv H2.

      apply length_1_something in H13. destruct H13.
      apply length_1_something in H9. destruct H9.
      apply length_1_something in H5. destruct H5.
      apply length_1_something in H10. destruct H10.
      apply length_1_something in H11. destruct H11.
      subst.

(*       inv H4. apply length_32_something in H2. *)
(*       destruct H2. do 31 (destruct H0). subst. *)
(*       inv H3. apply length_32_something in H2. *)
(*       destruct H2. do 31 (destruct H0). subst. *)
(*       inv H7. apply length_32_something in H2. *)
(*       destruct H2. do 31 (destruct H0). subst. *)
(*       inv H8. apply length_32_something in H2. *)
(*       destruct H2. do 31 (destruct H0). subst. *)
(*       inv H12. apply length_32_something in H2. *)
(*       destruct H2. do 31 (destruct H0). subst. *)

(*       eapply length_n_something in H1 as ?. *)
(*       inv H0. eapply tail_smaller in H1. *)
(*       eapply length_n_something in H1 as ?. *)
(*       inv H0. rewrite H3 in H2. clear H3. eapply tail_smaller in H1. *)
(*       eapply length_n_something in H1 as ?. *)
(*       inv H0. rewrite H3 in H2. clear H3. eapply tail_smaller in H1. *)
(*       simpl in H1. *)
(*       eapply length_zero_iff_nil in H1. rewrite H1 in H2. clear H1. subst. *)

      simpl in DecodeDInst.
      inv DecodeDInst.
      simpl in LegalOk.
      inv LegalOk.
      inv H14.
      eapply length_1_something in H2. destruct H2. subst.

      assert (
        getenv REnv ctx (RV32I.d2e RV32I.fromDecode.data0)
        = getenv REnv ctx (RV32I.d2e RV32I.fromDecode.data0)
      ) by reflexivity.
      rewrite <- H6 in H0 at 2.
      exploit_reg H0.

      generalize (WTRENV (RV32I.epoch)). intro.
      inv H2.
      eapply length_1_something in H10. destruct H10. subst.
      symmetry in H9. exploit_reg H9.

      red in H.
      assert (x4 = x0). {
        destruct H.
        - red in H. repeat (destruct H as [? H]).
          red in H2. eapply H2 in H0 as Hn. inv Hn.
          rewrite H9 in H11. inv H11. reflexivity.
        - destruct H.
          + red in H. repeat (destruct H as [? H]).
            red in H2. eapply H2 in H0 as Hn. inv Hn.
            rewrite H9 in H13. inv H13. reflexivity.
          + red in H. repeat (destruct H as [? H]).
            red in H2. eapply H2 in H0 as Hn. inv Hn.
            rewrite H9 in H11. inv H11. reflexivity.
      }
      subst.

      simplify.
      collapse.
      collapse.
      simplify.
      simplify.
      (* collapse. *)
      isolate_sf.
      destruct x0.
      - Eval vm_compute in Maps.PTree.get 1789 (vars sf1).
        Eval vm_compute in Maps.PTree.get 1788 (vars sf1).
        Eval vm_compute in Maps.PTree.get 995 (vars sf1).

      Eval cbn in eval_sact ctx ext_sigma (vars sf0) (SVar 1788) 10.
      get_var 1788 sf0.
      vm_compute replace_reg.
      red in H.
      exploit_field EpochOk.
      exploit_fields.
      exploit_hypotheses.
      exploit_fields.
      erewrite (replace_field_interp_cycle_ok _ _ _ _ _ _ EpochOk); eauto.
      update_wfsf. clear H.
      simplify.
      collapse.
      isolate_sf.
      vm_compute prune_irrelevant_aux in sf0.
      vm_compute in sf0.
      collapse.
      simplify.
      (* prune. collapse. *).
      (* simplify. *)
      isolate_sf.
      vm_compute prune_irrelevant_aux in sf0.
      vm_compute in sf0.
      get_var 1788 sf0.
      full_pass.
      simplify.
    Qed.

  Definition cycle (r: env_t ContextEnv (fun _ : RV32I.reg_t => val)) :=
    UntypedSemantics.interp_dcycle drules r ext_sigma rv_schedule.

  Definition env_type := env_t REnv RV32I.R.
  Definition initial_env := create REnv RV32I.r.

  Definition CEnv := @ContextEnv RV32I.reg_t RV32I.FiniteType_reg_t.
  Definition initial_context_env := CEnv.(create) (RV32I.r).

  Definition f_init := fun x => val_of_value (initial_context_env.[x]).
