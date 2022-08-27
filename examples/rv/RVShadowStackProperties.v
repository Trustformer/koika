(*! Proofs about the behavior of our basic shadow stack mechanism !*)
Require Import Coq.Program.Equality.
Require Import Koika.BitsToLists Koika.DesugaredSyntax Koika.Frontend
  Koika.UntypedSemantics Koika.UntypedIndSemantics Koika.UntypedIndTactics.
Require Import Koika.SimpleFormInterpretation.
Require Import rv.ShadowStack rv.RVCore rv.rv32 rv.rv32i.
Require Import SimpleForm SimpleVal.

Import Coq.Lists.List.ListNotations.
Scheme Equality for list.

(* We mostly reason on the instruction that is currently entering the execute
   stage. All the information available about it is in the d2e buffer. *)
Section ShadowStackProperties.
  Context {REnv : Env RV32I.reg_t}.
  Context (ext_sigma : RV32I.ext_fn_t -> val -> val).
  Context (ext_Sigma : RV32I.ext_fn_t -> ExternalSignature).

  Hypothesis wt_sigma: forall (ufn : RV32I.ext_fn_t) (vc : val),
    wt_val (arg1Sig (ext_Sigma ufn)) vc
    -> wt_val (retSig (ext_Sigma ufn)) (ext_sigma ufn vc).

  Definition drules rule :=
    match uaction_to_daction (desugar_action tt (RV32I.rv_urules rule)) with
    | Some d => d
    | None => DFail unit_t
    end.

  Hypothesis rules_wt:
    forall rule : rv_rules_t,
    exists t : type,
    wt_daction
      (Sigma:=ext_Sigma) (R:=RV32I.R) unit string string [] (drules rule) t.

  Definition schedule := rv_schedule.
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

  Definition stack_push (ctx: env_t REnv (fun _ : RV32I.reg_t => val)) : Prop :=
    forall v w b,
    getenv REnv ctx (RV32I.d2e (RV32I.fromDecode.data0)) =
      Struct (RV32I.decode_bookkeeping) v ->
    get_field_struct (struct_fields RV32I.decode_bookkeeping) v "dInst" =
      Some (Struct (decoded_sig) w) ->
    get_field_struct (struct_fields decoded_sig) w "inst" =
      Some (Bits b) ->
    is_call_instruction (Bits.of_N 32 (Bits.to_N (vect_of_list b))) = true.

  Definition stack_pop (ctx: env_t REnv (fun _ : RV32I.reg_t => val)) : Prop :=
    forall v w b,
    getenv REnv ctx (RV32I.d2e (RV32I.fromDecode.data0)) =
      Struct (RV32I.decode_bookkeeping) v ->
    get_field_struct (struct_fields RV32I.decode_bookkeeping) v "dInst" =
      Some (Struct (decoded_sig) w) ->
    get_field_struct (struct_fields decoded_sig) w "inst" =
      Some (Bits b) ->
    is_ret_instruction (Bits.of_N 32 (Bits.to_N (vect_of_list b))) = true.

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
    no_mispred ctx /\ stack_full ctx /\ (not (stack_pop ctx)) /\ stack_push ctx.
  Definition stack_address_violation
    (ctx: env_t REnv (fun _ : RV32I.reg_t => val))
  : Prop :=
    no_mispred ctx /\ stack_push ctx
    /\ stack_top_address ctx <> stack_push_address ctx.

  Definition stack_violation
    (ctx: env_t REnv (fun _ : RV32I.reg_t => val))
  : Prop :=
    stack_underflow ctx \/ stack_overflow ctx \/ stack_address_violation ctx.

  (* Final state *)
  Definition halt_set (ctx: env_t REnv (fun _ : RV32I.reg_t => val))
  : Prop :=
    forall ctx',
    UntypedIndSemantics.interp_cycle
      RV32I.rv_urules ctx ext_sigma schedule ctx' ->
    getenv REnv ctx' RV32I.halt = @val_of_value (bits_t 1) Ob~1.

  Fixpoint interp_n_cycles n (ctx: env_t REnv (fun _ : RV32I.reg_t => val))
  : env_t REnv (fun _ : RV32I.reg_t => val) :=
    match n with
    | O => ctx
    | S n' =>
      interp_n_cycles
        n'
        (UntypedSemantics.interp_cycle RV32I.rv_urules ctx ext_sigma schedule)
    end.

  Ltac destr_in H :=
    match type of H with
    | context[match ?a with _ => _ end] => destruct a eqn:?
    end.

  Ltac destr :=
    match goal with
    |- context[match ?a with _ => _ end] => destruct a eqn:?; try congruence
    end.

  Definition is_write_halt
    (reg_t ext_fn_t: Type) (ua: uaction pos_t var_t fn_name_t reg_t ext_fn_t)
    (fR: reg_t -> RV32I.reg_t) (fSigma: ext_fn_t -> RV32I.ext_fn_t)
  : bool :=
    match ua with
    | UWrite _ r _ =>
      match (fR r) with
      | RV32I.halt => true
      | _ => false
      end
    | _ => false
    end.

  Instance eq_dec_reg: EqDec RV32I.reg_t := EqDec_FiniteType.
  Existing Instance etaRuleInformationRaw.

  Ltac inv H := inversion H; try subst; clear H.

  Definition simplify_sf sf ctx := {|
    final_values := final_values sf;
    vars :=
      Maps.PTree.map
        (fun _ '(t,a) => (
          t,
          simplify_sact (REnv := REnv) (reg_t := RV32I.reg_t) ctx ext_sigma a
        ))
        (vars sf)
    |}.

(*   Definition halt_set2 ctx := *)
(*     forall sf n, *)
(*     remove_vars_for_var *)
(*       (simplify_sf *)
(*         (schedule_to_simple_form RV32I.R (Sigma:=ext_Sigma) drules schedule) ctx *)
(*       ) *)
(*       RV32I.halt *)
(*     = Some sf *)
(*     -> list_assoc (final_values sf) RV32I.halt = Some n *)
(*     -> SimpleForm.interp_sact *)
(*          REnv ctx (vars sf) (sigma:=ext_sigma) (SVar n) (Bits [true]). *)

(*   Lemma stack_violation_results_in_halt: *)
(*     forall *)
(*       ctx (WTRENV: Wt.wt_renv RV32I.R REnv ctx) *)
(*       (NoHalt: (getenv REnv ctx RV32I.halt) = Bits [false]) *)
      (* (Valid: getenv REnv ctx (RV32I.d2e RV32I.fromDecode.valid0) = Bits [true]) *)
(*       (Legal: *)
(*         forall v v2, *)
(*         getenv REnv ctx (RV32I.d2e RV32I.fromDecode.data0) *)
(*         = Struct RV32I.decode_bookkeeping v *)
(*         -> get_field_struct *)
(*              (struct_fields RV32I.decode_bookkeeping) v "dInst" *)
(*         = Some (Struct decoded_sig v2 *)
(*         -> get_field_struct (struct_fields decoded_sig) v2 "legal" *)
(*         = Some (Bits [true])), *)
(*     stack_violation ctx -> halt_set2 ctx. *)
(*   Proof. *)
(*   Qed. *)

(*   Lemma no_stack_violation_behaves_as_if_no_stack: *)
(*     forall (ctx: env_t REnv (fun _ : RV32I.reg_t => val)), *)
(*     not (stack_violation ctx) -> *)
(*     interp_n_cycles 1 ctx = interp_n_cycles_no_shadow_stack 1 ctx. *)
(*   Proof. *)
(*   Qed. *)

(* Main theorem *)
(*   Theorem shadow_stack_ok: *)
(*     stack_violation_results_in_halt /\ halt_leads_to_a_sink_state *)
(*     /\ no_stack_violation_behaves_as_if_no_stack. *)
(*   Proof. *)
(*   Qed. *)
End ShadowStackProperties.
