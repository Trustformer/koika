(*! Proofs about the behavior of our basic shadow stack mechanism !*)
Require Import Koika.BitsToLists Koika.Frontend Koika.UntypedIndSemantics.
Require Import rv.Stack rv.RVCore rv.rv32 rv.rv32i.

(* We mostly reason on the instruction that is currently entering the execute
   stage. All the information available about it is in the d2e structure
   (decode to execute buffer). *)
Section ShadowStackProperties.
  Context {REnv : Env RV32I.reg_t}.
  Definition schedule := rv_schedule.

  (* Propositions about the initial state *)
  Definition no_mispred
    (ctx: env_t REnv (fun _ : RV32I.reg_t => BitsToLists.val))
  : Prop :=
    forall v,
    getenv REnv ctx (RV32I.d2e (RV32I.fromDecode.data0)) =
      Struct (RV32I.decode_bookkeeping) v ->
    get_field_struct (struct_fields RV32I.decode_bookkeeping) v "epoch" =
    Some (getenv REnv ctx (RV32I.epoch)).

  Definition stack_empty
    (ctx: env_t REnv (fun _ : RV32I.reg_t => BitsToLists.val))
  : Prop :=
    getenv REnv ctx (RV32I.stack (RV32I.Stack.size))
    = @val_of_value
      (bits_t RV32I.Stack.index_sz) (Bits.of_nat (RV32I.Stack.index_sz) 0).

  Definition stack_full
    (ctx: env_t REnv (fun _ : RV32I.reg_t => BitsToLists.val))
  : Prop :=
    getenv REnv ctx (RV32I.stack (RV32I.Stack.size))
    = @val_of_value
      (bits_t RV32I.Stack.index_sz)
      (Bits.of_nat (RV32I.Stack.index_sz) RV32I.Stack.capacity).

  (* Definition is_call_instruction (instr: bits_t 32) := *)
  (* Definition is_ret_instruction (instr: bits_t 32):=. *)

  (* Definition stack_push := is_call_instruction (). *)
  (* Definition stack_pop := is_ret_instruction (). *)

  (* TODO should never return None, simplify *)
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

  Definition stack_top_address
    (ctx: env_t REnv (fun _ : RV32I.reg_t => BitsToLists.val))
  : option (bits_t 32) :=
    let index := getenv REnv ctx (RV32I.stack RV32I.Stack.size) in
    let data := getenv REnv ctx (RV32I.stack RV32I.Stack.stack).

    (* forall (ctx: env_t REnv (fun _ : RV32I.reg_t => BitsToLists.val)) v,*)
    (* getenv REnv ctx (RV32I.d2e (RV32I.fromDecode.data0)) =*)
    (*   Struct (RV32I.decode_bookkeeping) v*)
    (* -> get_field_struct (struct_fields RV32I.decode_bookkeeping) v "dInst"*)
    (*   = Some (Bits 32 [*)
    (*     false; false; false; false; false; false; false; false; false; false;*)
    (*     false; false; false; false; false; false; false; false; false; false;*)
    (*     false; false; false; false; false; false; false; false; false; false;*)
    (*     false; false*)
    (*     ]). *)

  Definition stack_underflow
    (ctx: env_t REnv (fun _ : RV32I.reg_t => BitsToLists.val))
  : Prop := no_mispred ctx && stack_empty ctx && stack_pop ctx.
  Definition stack_overflow
    (ctx: env_t REnv (fun _ : RV32I.reg_t => BitsToLists.val))
  : Prop := no_mispred ctx && stack_full ctx && stack_push ctx.
  Definition stack_address_violation
    (ctx: env_t REnv (fun _ : RV32I.reg_t => BitsToLists.val))
  : Prop := forall x y,
    no_mispred ctx && stack_push ctx && stack_top_address ctx = x
    && stack_push_address ctx = y && x <> y.

  Definition stack_violation
    (ctx: env_t REnv (fun _ : RV32I.reg_t => BitsToLists.val))
  : Prop :=
    stack_underflow ctx || stack_overflow ctx || stack_address_violation ctx.

  (* Final state *)
  Definition halt_set := .

  (* Proofs *)
  (* Auxiliary lemmas *)

  (* Main lemmas *)
  Lemma halt_leads_to_a_sink_state:
    (* TODO not quite this *)
    halt_set -> cycle_end_state ctx = cycle_end_state (cycle_end_state ctx).
  Proof.
  Qed.

  Lemma stack_violation_results_in_halt:
    forall (ctx: env_t REnv (fun _ : RV32I.reg_t => BitsToLists.val)),
    stack_violation ctx -> halt_set ctx.
  Proof.
  Qed.

  Lemma no_stack_violation_behaves_as_if_no_stack:
    forall (ctx: env_t REnv (fun _ : RV32I.reg_t => BitsToLists.val)),
    !(stack_violation ctx) ->
    cycle_end_state ctx = stackless_cycle_end_state ctx.
  Proof.
  Qed.

  (* Main theorem *)
  Theorem shadow_stack_ok:
    halt_leads_to_a_sink_state && stack_violation_results_in_halt
    && no_stack_violation_behaves_as_if_no_stack.
  Proof.
  Qed.
End ShadowStackProperties.
