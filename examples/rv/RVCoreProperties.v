(*! Proofs about our RISC-V implementation !*)
Require Import Coq.Program.Equality.
Require Import Koika.Frontend.
Require Export rv.Instructions rv.ShadowStack rv.RVCore rv.rv32 rv.rv32i.
Require Import Koika.SimpleForm.SimpleForm.
Require Import Koika.SimpleForm.SimpleFormInterpretation.
Require Import Koika.SimpleForm.SimpleFormTactics.
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
      intros. set (wfsf := sf_wf).
      crusher 2.
    Time Qed.

    Lemma stack_violation_results_in_halt:
      forall
        (NoHalt: getenv REnv ctx RV32I.halt = Bits [false])
        (Valid:
          getenv REnv ctx (RV32I.d2e RV32I.fromDecode.valid0) = Bits [true])
        (EpochOk:
          get_field (getenv REnv ctx (RV32I.d2e RV32I.fromDecode.data0)) "epoch"
          = Some (Bits [true]))
        v2
        (DecodeDInst:
          get_field (getenv REnv ctx (RV32I.d2e RV32I.fromDecode.data0)) "dInst"
          = Some v2)
        (LegalOk: get_field v2 "legal" = Some (Bits [true])),
      stack_violation ctx -> halt_set ctx.
    Proof.
      intros. assert (wfsf := sf_wf).
      unfold halt_set.


      exploit_reg NoHalt.
      exploit_reg Valid.
      rewrite (replace_field_interp_cycle_ok (wt_sigma:=wt_sigma) _ _ _ _ WTRENV wfsf EpochOk); eauto.
      update_wfsf.
      full_pass.
      exploit_field EpochOk.
      exploit_field DecodeDInst.
      do 10 full_pass.
      simplify.
      isolate_sf.

      vm_compute in sf0.
      Eval vm_compute in Maps.PTree.get 1789
                           (vars sf0).
      (* Opaque getenv. *)
      Eval cbn in eval_sact ctx ext_sigma (vars sf0) (SVar 1789) 10.

      Lemma dream:
          forall sf idx n fuel v,
            list_assoc (final_values sf) idx = Some n ->
            eval_sact ctx ext_sigma (vars sf) (SVar n) fuel = Some v ->
            getenv REnv (interp_cycle ctx ext_sigma sf) idx = v.
      Admitted.
      eapply dream with (fuel:=30).
      cbn. reflexivity.
      cbn. clear sf0.
      rewrite EpochOk. simpl.
      rewrite DecodeDInst; simpl.
      Eval vm_compute in Maps.PTree.get 13 (vars sf0).

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
