(*! Proofs about the behavior of our basic shadow stack mechanism !*)
Require Import Koika.BitsToLists Koika.Frontend Koika.UntypedSemantics
  Koika.UntypedIndSemantics.
Require Import rv.ShadowStack rv.RVCore rv.rv32 rv.rv32i.
(* Require Import rv.RVCoreNoShadowStack rv.rv32NoShadowStack *)
(*   rv.rv32iNoShadowStack. *)

Import Coq.Lists.List.ListNotations.
Scheme Equality for list.

(* We mostly reason on the instruction that is currently entering the execute
   stage. All the information available about it is in the d2e structure
   (decode to execute buffer). *)
Section ShadowStackProperties.
  Context {REnv : Env RV32I.reg_t}.
  Context (ext_sigma : RV32I.ext_fn_t -> BitsToLists.val -> BitsToLists.val).
  Context (ext_Sigma : RV32I.ext_fn_t -> ExternalSignature).
  Definition schedule := rv_schedule.
  Definition eql (l1 l2: list bool) : bool := list_beq bool Bool.eqb l1 l2.

  (* Propositions about the initial state *)
  Definition no_mispred
    (ctx: env_t REnv (fun _ : RV32I.reg_t => BitsToLists.val))
  : Prop :=
    forall v,
    getenv REnv ctx (RV32I.d2e (RV32I.fromDecode.data0)) =
      Struct (RV32I.decode_bookkeeping) v /\
    get_field_struct (struct_fields RV32I.decode_bookkeeping) v "epoch" =
    Some (getenv REnv ctx (RV32I.epoch)).

  Definition stack_empty
    (ctx: env_t REnv (fun _ : RV32I.reg_t => BitsToLists.val))
  : Prop :=
    getenv REnv ctx (RV32I.stack (RV32I.ShadowStack.size))
    = @val_of_value
      (bits_t RV32I.ShadowStack.index_sz)
      (Bits.of_nat (RV32I.ShadowStack.index_sz) 0).

  Definition stack_full
    (ctx: env_t REnv (fun _ : RV32I.reg_t => BitsToLists.val))
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
    (eql opcode_ctrl [true; true; false])
    && (
      (
        (eql opcode_rest [true; true; true; true])
        && (
          (eql rd [false; false; false; false; true])
          || (eql rd [false; false; true; false; true])
        )
      )
      || (
        (eql opcode_rest [false; true; true; true])
        && (
          (eql rd [false; false; false; false; true])
          || (eql rd [false; false; true; false; true])
        )
      )
    ).

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
          || (eql rd [false; false; true; false; true])
        )
        && (negb (eql rd rs1))
        && (
          (eql rs1 [false; false; false; false; true])
          || (eql rs1 [false; false; true; false; true])
        )
      )
      || (
        (negb (eql rd [false; false; false; false; true]))
        && (eql rd [false; false; true; false; true])
        && (
          (eql rs1 [false; false; false; false; true])
          || (eql rs1 [false; false; true; false; true])
        )
      )
    ).

  Definition stack_push
    (ctx: env_t REnv (fun _ : RV32I.reg_t => BitsToLists.val))
  : Prop :=
    forall v w b,
    getenv REnv ctx (RV32I.d2e (RV32I.fromDecode.data0)) =
      Struct (RV32I.decode_bookkeeping) v /\
    get_field_struct (struct_fields RV32I.decode_bookkeeping) v "dInst" =
      Some (Struct (decoded_sig) w) /\
    get_field_struct (struct_fields decoded_sig) w "inst" =
      Some (Bits 32 b) /\
    is_call_instruction (Bits.of_N 32 (Bits.to_N (vect_of_list b))) = true.

  Definition stack_pop
    (ctx: env_t REnv (fun _ : RV32I.reg_t => BitsToLists.val))
  : Prop :=
    forall v w b,
    getenv REnv ctx (RV32I.d2e (RV32I.fromDecode.data0)) =
      Struct (RV32I.decode_bookkeeping) v /\
    get_field_struct (struct_fields RV32I.decode_bookkeeping) v "dInst" =
      Some (Struct (decoded_sig) w) /\
    get_field_struct (struct_fields decoded_sig) w "inst" =
      Some (Bits 32 b) /\
    is_ret_instruction (Bits.of_N 32 (Bits.to_N (vect_of_list b))) = true.

  (* TODO should never return None, simplify? *)
  Definition stack_push_address
    (ctx: env_t REnv (fun _ : RV32I.reg_t => BitsToLists.val))
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
  Definition stack_top_address
    (ctx: env_t REnv (fun _ : RV32I.reg_t => BitsToLists.val))
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

  Definition stack_underflow
    (ctx: env_t REnv (fun _ : RV32I.reg_t => BitsToLists.val))
  : Prop := no_mispred ctx /\ stack_empty ctx /\ stack_pop ctx.
  Definition stack_overflow
    (ctx: env_t REnv (fun _ : RV32I.reg_t => BitsToLists.val))
  : Prop :=
    no_mispred ctx /\ stack_full ctx /\ (not (stack_pop ctx)) /\ stack_push ctx.
  Definition stack_address_violation
    (ctx: env_t REnv (fun _ : RV32I.reg_t => BitsToLists.val))
  : Prop := forall x y,
    no_mispred ctx /\ stack_push ctx /\ stack_top_address ctx = x
    /\ stack_push_address ctx = y /\ x <> y.

  Definition stack_violation
    (ctx: env_t REnv (fun _ : RV32I.reg_t => BitsToLists.val))
  : Prop :=
    stack_underflow ctx \/ stack_overflow ctx \/ stack_address_violation ctx.

  (* Final state *)
  Definition halt_set
    (ctx: env_t REnv (fun _ : RV32I.reg_t => BitsToLists.val))
  : Prop :=
    forall ctx',
    UntypedIndSemantics.interp_cycle
      RV32I.rv_urules ctx ext_sigma schedule ctx' ->
    getenv REnv ctx' RV32I.halt = @val_of_value (bits_t 1) Ob~1.

  Fixpoint interp_n_cycles
    n (ctx: env_t REnv (fun _ : RV32I.reg_t => BitsToLists.val))
  : env_t REnv (fun _ : RV32I.reg_t => BitsToLists.val) :=
    match n with
    | O => ctx
    | S n' => interp_n_cycles n' (
        UntypedSemantics.interp_cycle RV32I.rv_urules ctx ext_sigma schedule
      )
    end.

  (* Fixpoint interp_n_cycles_no_shadow_stack *)
  (*   n (ctx: env_t REnv (fun _ : RV32I.reg_t => BitsToLists.val)) *)
  (* : env_t REnv (fun _ : RV32I.reg_t => BitsToLists.val) := *)
  (*   match n with *)
  (*   | O => ctx *)
  (*   | S n' => interp_n_cycles n' ( *)
  (*       UntypedSemantics.interp_cycle RV32I.rv_urules ctx ext_sigma schedule *)
  (*     ) *)
  (*   end. *)

  Definition is_sink_state
    (ctx: env_t REnv (fun _ : RV32I.reg_t => BitsToLists.val))
  : Prop :=
    forall n ctx', interp_n_cycles n ctx' = ctx.

  (* Main lemmas *)
  Lemma halt_leads_to_a_sink_state:
    forall (ctx: env_t REnv (fun _ : RV32I.reg_t => BitsToLists.val)),
    halt_set ctx -> is_sink_state ctx.
  Proof.
  Qed.

  Lemma stack_violation_results_in_halt:
    forall (ctx: env_t REnv (fun _ : RV32I.reg_t => BitsToLists.val)),
    stack_violation ctx -> halt_set ctx.
  Proof.
  Qed.

  Lemma no_stack_violation_behaves_as_if_no_stack:
    forall (ctx: env_t REnv (fun _ : RV32I.reg_t => BitsToLists.val)),
    not (stack_violation ctx) ->
    interp_n_cycles 1 ctx = interp_n_cycles_no_shadow_stack 1 ctx.
  Proof.
  Qed.

  (* Main theorem *)
  Theorem shadow_stack_ok:
    stack_violation_results_in_halt /\ halt_leads_to_a_sink_state
    /\ no_stack_violation_behaves_as_if_no_stack.
  Proof.
  Qed.
End ShadowStackProperties.
