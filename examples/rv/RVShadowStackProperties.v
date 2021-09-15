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

  (* Definition is_sink_state *)
  (*   (ctx: env_t REnv (fun _ : RV32I.reg_t => BitsToLists.val)) *)
  (* : Prop := *)
  (*   forall n ctx', interp_n_cycles n ctx' = ctx. *)

  (* Main lemmas *)
  (* Lemma halt_leads_to_a_sink_state: *)
  (*   forall (ctx: env_t REnv (fun _ : RV32I.reg_t => BitsToLists.val)), *)
  (*   halt_set ctx -> is_sink_state ctx. *)
  (* Proof. *)
  (* Qed. *)

  Ltac destr_in H :=
    match type of H with
    | context[match ?a with _ => _ end] => destruct a eqn:?
    end.

  Ltac destr :=
    match goal with
    |- context[match ?a with _ => _ end] => destruct a eqn:?; try congruence
    end.

  Ltac inv H := inversion H; try subst; clear H.

  Require Import Coq.Program.Equality.

  Lemma invert_var:
    forall
      {pos_t var_t fn_name_t: Type} {var_t_eq_dec: EqDec var_t}
      {reg_t ext_fn_t: Type} {REnv: Env reg_t}
      (r: env_t REnv (fun _: reg_t => BitsToLists.val))
      (sigma: ext_fn_t -> BitsToLists.val -> BitsToLists.val)
      (Gamma Gamma': list (var_t * BitsToLists.val))
      (sched_log action_log action_log': Log REnv) var v,
      interp_action (pos_t := pos_t) (fn_name_t := fn_name_t) r sigma Gamma
        sched_log action_log (UVar var) action_log' v Gamma'
    -> action_log = action_log'
    /\ Gamma = Gamma'
    /\ list_assoc Gamma var = Some v.
  Proof.
    intros.
    dependent destruction H.
    repeat split.
    assumption.
  Qed.

  Lemma invert_const:
    forall
      {pos_t var_t fn_name_t: Type} {var_t_eq_dec: EqDec var_t}
      {reg_t ext_fn_t: Type} {REnv: Env reg_t}
      (r: env_t REnv (fun _: reg_t => BitsToLists.val))
      (sigma: ext_fn_t -> BitsToLists.val -> BitsToLists.val)
      (Gamma Gamma': list (var_t * BitsToLists.val))
      (sched_log action_log action_log': Log REnv) tau (cst: type_denote tau) v,
      interp_action (pos_t := pos_t) (fn_name_t := fn_name_t) r sigma Gamma
        sched_log action_log (UConst cst) action_log' v Gamma'
    -> v = val_of_value cst /\ action_log = action_log' /\ Gamma = Gamma'.
  Proof.
    intros.
    dependent destruction H.
    repeat split.
  Qed.

  Lemma invert_assign:
    forall
      {pos_t var_t fn_name_t: Type} {var_t_eq_dec: EqDec var_t}
      {reg_t ext_fn_t: Type} {REnv: Env reg_t}
      (r: env_t REnv (fun _: reg_t => BitsToLists.val))
      (sigma: ext_fn_t -> BitsToLists.val -> BitsToLists.val)
      (Gamma Gamma': list (var_t * BitsToLists.val))
      (sched_log action_log action_log': Log REnv) k a v,
      interp_action (pos_t := pos_t) (fn_name_t := fn_name_t) r sigma Gamma
        sched_log action_log (UAssign k a) action_log' v Gamma'
    -> exists v_init Gamma_init,
    v = Bits 0 []
    /\ Gamma' = list_assoc_set Gamma_init k v_init
    /\ interp_action r sigma Gamma sched_log action_log a action_log' v_init
      Gamma_init.
  Proof.
    intros.
    dependent destruction H.
    exists v.
    exists Gamma'.
    repeat split.
    assumption.
  Qed.

  Lemma invert_seq:
    forall
      {pos_t var_t fn_name_t: Type} {var_t_eq_dec: EqDec var_t}
      {reg_t ext_fn_t: Type} {REnv: Env reg_t}
      (r: env_t REnv (fun _: reg_t => BitsToLists.val))
      (sigma: ext_fn_t -> BitsToLists.val -> BitsToLists.val)
      (Gamma Gamma': list (var_t * BitsToLists.val))
      (sched_log action_log action_log': Log REnv) a1 a2 v,
      interp_action (pos_t := pos_t) (fn_name_t := fn_name_t) r sigma Gamma
        sched_log action_log (USeq a1 a2) action_log' v Gamma'
    -> exists v1 v2 Gamma1 Gamma2 action_log1 action_log2,
    v = v2
    /\ action_log' = action_log2
    /\ Gamma' = Gamma2
    /\ interp_action r sigma Gamma sched_log action_log a1 action_log1 v1 Gamma1
    /\ interp_action r sigma Gamma1 sched_log action_log1 a2 action_log2 v2
      Gamma2.
  Proof.
    intros.
    dependent destruction H.
    exists v1.
    exists v2.
    exists Gamma'.
    exists Gamma''.
    exists action_log'.
    exists action_log''.
    repeat split; assumption.
  Qed.

  Lemma invert_bind:
    forall
      {pos_t var_t fn_name_t: Type} {var_t_eq_dec: EqDec var_t}
      {reg_t ext_fn_t: Type} {REnv: Env reg_t}
      (r: env_t REnv (fun _: reg_t => BitsToLists.val))
      (sigma: ext_fn_t -> BitsToLists.val -> BitsToLists.val)
      (Gamma Gamma': list (var_t * BitsToLists.val))
      (sched_log action_log action_log': Log REnv) k a1 a2 v,
      interp_action (pos_t := pos_t) (fn_name_t := fn_name_t) r sigma Gamma
        sched_log action_log (UBind k a1 a2) action_log' v Gamma'
    -> exists v1 v2 Gamma1 Gamma2 action_log1 action_log2,
    v = v2
    /\ action_log' = action_log2
    /\ Gamma' = tl Gamma2
    /\ interp_action r sigma Gamma sched_log action_log a1 action_log1 v1 Gamma1
    /\ interp_action r sigma ((k, v1)::Gamma1) sched_log action_log1 a2
      action_log2 v2 Gamma2.
  Proof.
    intros.
    dependent destruction H.
    exists v1.
    exists v2.
    exists Gamma'.
    exists Gamma''.
    exists action_log'.
    exists action_log''.
    repeat split; assumption.
  Qed.

  Lemma invert_if:
    forall
      {pos_t var_t fn_name_t: Type} {var_t_eq_dec: EqDec var_t}
      {reg_t ext_fn_t: Type} {REnv: Env reg_t}
      (r: env_t REnv (fun _: reg_t => BitsToLists.val))
      (sigma: ext_fn_t -> BitsToLists.val -> BitsToLists.val)
      (Gamma Gamma': list (var_t * BitsToLists.val))
      (sched_log action_log action_log': Log REnv) cond athen aelse v,
      interp_action (pos_t := pos_t) (fn_name_t := fn_name_t) r sigma Gamma
        sched_log action_log (UIf cond athen aelse) action_log' v Gamma'
    -> exists v2 b Gamma1 Gamma2 action_log1 action_log2,
    v = v2
    /\ action_log' = action_log2
    /\ Gamma' = Gamma2
    /\ interp_action r sigma Gamma sched_log action_log cond action_log1
      (Bits 1 [b]) Gamma1
    /\ interp_action r sigma Gamma1 sched_log action_log1
      (if b then athen else aelse) action_log2 v2 Gamma2.
  Proof.
    intros.
    dependent destruction H.
    exists v2.
    exists b.
    exists Gamma'.
    exists Gamma''.
    exists action_log'.
    exists action_log''.
    repeat split; assumption.
  Qed.

  Lemma invert_read:
    forall
      {pos_t var_t fn_name_t: Type} {var_t_eq_dec: EqDec var_t}
      {reg_t ext_fn_t: Type} {REnv: Env reg_t}
      (r: env_t REnv (fun _: reg_t => BitsToLists.val))
      (sigma: ext_fn_t -> BitsToLists.val -> BitsToLists.val)
      (Gamma: list (var_t * BitsToLists.val)) (sched_log action_log: Log REnv)
      (prt: Port) (idx: reg_t) (v: BitsToLists.val) (action_log': Log REnv)
      (Gamma': list (var_t * BitsToLists.val)),
      interp_action (pos_t := pos_t) (fn_name_t := fn_name_t) r sigma Gamma
      sched_log action_log (URead prt idx) action_log' v Gamma'
    -> may_read sched_log prt idx = true
    /\ Gamma' = Gamma
    /\ action_log' = log_cons idx (LE Logs.LogRead prt (Bits 0 [])) action_log
    /\ v = (match prt with
      | P0 => REnv.(getenv) r idx
      | P1 =>
        match
          latest_write0 (V := BitsToLists.val) (log_app action_log sched_log)
            idx
        with
        | Some v => v
        | None => REnv.(getenv) r idx
        end
      end
    ).
  Proof.
    intros.
    dependent destruction H.
    repeat split; assumption.
  Qed.

  Lemma invert_write:
    forall
      {pos_t var_t fn_name_t: Type} {var_t_eq_dec: EqDec var_t}
      {reg_t ext_fn_t: Type} {REnv: Env reg_t}
      (r: env_t REnv (fun _: reg_t => BitsToLists.val))
      (sigma: ext_fn_t -> BitsToLists.val -> BitsToLists.val)
      (Gamma: list (var_t * BitsToLists.val))
      (sched_log action_log: Log REnv) (prt: Port)
      (idx: reg_t) (a: uaction pos_t var_t fn_name_t reg_t ext_fn_t)
      (v_after: BitsToLists.val) (action_log': Log REnv)
      (Gamma': list (var_t * BitsToLists.val)),
      interp_action r sigma Gamma sched_log action_log (UWrite prt idx a)
        action_log' v_after Gamma'
    -> exists v_init action_log_init,
    v_after = Bits 0 []
    /\ action_log' = log_cons idx (LE Logs.LogWrite prt v_init) action_log_init
    /\ interp_action r sigma Gamma sched_log action_log a action_log_init v_init
      Gamma'
    /\ may_write sched_log action_log_init prt idx = true.
  Proof.
    intros.
    dependent destruction H.
    exists v.
    exists action_log'.
    repeat split; assumption.
  Qed.

  Lemma invert_unop:
    forall
      {pos_t var_t fn_name_t: Type} {var_t_eq_dec: EqDec var_t}
      {reg_t ext_fn_t: Type} {REnv: Env reg_t}
      (r: env_t REnv (fun _: reg_t => BitsToLists.val))
      (sigma: ext_fn_t -> BitsToLists.val -> BitsToLists.val)
      (Gamma Gamma': list (var_t * BitsToLists.val))
      (sched_log action_log action_log': Log REnv) fn a v,
      interp_action (pos_t := pos_t) (fn_name_t := fn_name_t) r sigma Gamma
        sched_log action_log (UUnop fn a) action_log' v Gamma'
    -> exists v_init,
    sigma1 fn v_init = Some v
    /\ interp_action r sigma Gamma sched_log action_log a action_log' v_init
      Gamma'.
  Proof.
    intros.
    dependent destruction H.
    exists v.
    repeat split; assumption.
  Qed.

  Lemma invert_binop:
    forall
      {pos_t var_t fn_name_t: Type} {var_t_eq_dec: EqDec var_t}
      {reg_t ext_fn_t: Type} {REnv: Env reg_t}
      (r: env_t REnv (fun _: reg_t => BitsToLists.val))
      (sigma: ext_fn_t -> BitsToLists.val -> BitsToLists.val)
      (Gamma Gamma': list (var_t * BitsToLists.val))
      (sched_log action_log action_log': Log REnv) fn a1 a2 v,
      interp_action (pos_t := pos_t) (fn_name_t := fn_name_t) r sigma Gamma
        sched_log action_log (UBinop fn a1 a2) action_log' v Gamma'
    -> exists Gamma1 Gamma2 action_log1 action_log2 v1 v2,
    interp_action r sigma Gamma sched_log action_log a1 action_log1 v1 Gamma1
    /\ interp_action r sigma Gamma1 sched_log action_log1 a2 action_log2 v2
      Gamma2
    /\ sigma2 fn v1 v2 = Some v
    /\ Gamma' = Gamma2
    /\ action_log' = action_log2.
  Proof.
    intros.
    dependent destruction H.
    exists Gamma'.
    exists Gamma''.
    exists action_log'.
    exists action_log''.
    exists v1.
    exists v2.
    repeat split; assumption.
  Qed.

  Lemma invert_extcall:
    forall
      {pos_t var_t fn_name_t: Type} {var_t_eq_dec: EqDec var_t}
      {reg_t ext_fn_t: Type} {REnv: Env reg_t}
      (r: env_t REnv (fun _: reg_t => BitsToLists.val))
      (sigma: ext_fn_t -> BitsToLists.val -> BitsToLists.val)
      (Gamma Gamma': list (var_t * BitsToLists.val))
      (sched_log action_log action_log': Log REnv) fn a v,
      interp_action (pos_t := pos_t) (fn_name_t := fn_name_t) r sigma Gamma
        sched_log action_log (UExternalCall fn a) action_log' v Gamma'
    -> exists v_init,
    v = sigma fn v_init
    /\ interp_action r sigma Gamma sched_log action_log a action_log' v_init
      Gamma'.
  Proof.
    intros.
    dependent destruction H.
    exists v.
    repeat split; assumption.
  Qed.

  Lemma invert_intcall:
    forall
      {pos_t var_t fn_name_t: Type} {var_t_eq_dec: EqDec var_t}
      {reg_t ext_fn_t: Type} {REnv: Env reg_t}
      (r: env_t REnv (fun _: reg_t => BitsToLists.val))
      (sigma: ext_fn_t -> BitsToLists.val -> BitsToLists.val)
      (Gamma Gamma': list (var_t * BitsToLists.val))
      (sched_log action_log action_log': Log REnv) f args v,
      interp_action (pos_t := pos_t) (fn_name_t := fn_name_t) r sigma Gamma
        sched_log action_log (UInternalCall f args) action_log' v Gamma'
    -> exists action_log1 lv Gamma2,
    interp_list r sigma (interp_action r sigma) Gamma sched_log action_log
      args action_log1 lv Gamma'
    /\ interp_action r sigma
      (map (fun '(name, _, v) => (name, v)) (combine (rev (int_argspec f)) lv))
      sched_log action_log1 (int_body f) action_log' v Gamma2
    .
  Proof.
    intros.
    dependent destruction H.
    exists action_log'.
    exists lv.
    exists Gamma''.
    repeat split; assumption.
  Qed.

  Lemma invert_pos:
    forall
      {pos_t var_t fn_name_t: Type} {var_t_eq_dec: EqDec var_t}
      {reg_t ext_fn_t: Type} {REnv: Env reg_t}
      (r: env_t REnv (fun _: reg_t => BitsToLists.val))
      (sigma: ext_fn_t -> BitsToLists.val -> BitsToLists.val)
      (Gamma Gamma': list (var_t * BitsToLists.val))
      (sched_log action_log action_log': Log REnv) p a v,
      interp_action (pos_t := pos_t) (fn_name_t := fn_name_t) r sigma Gamma
        sched_log action_log (UAPos p a) action_log' v Gamma'
    -> interp_action r sigma Gamma sched_log action_log a action_log' v Gamma'.
  Proof.
    intros.
    dependent destruction H.
    assumption.
  Qed.

  Lemma invert_skip:
    forall
      {pos_t var_t fn_name_t: Type} {var_t_eq_dec: EqDec var_t}
      {reg_t ext_fn_t: Type} {REnv: Env reg_t}
      (r: env_t REnv (fun _: reg_t => BitsToLists.val))
      (sigma: ext_fn_t -> BitsToLists.val -> BitsToLists.val)
      (Gamma Gamma': list (var_t * BitsToLists.val))
      (sched_log action_log action_log': Log REnv) v,
      interp_action (pos_t := pos_t) (fn_name_t := fn_name_t) r sigma Gamma
        sched_log action_log (USugar USkip) action_log' v Gamma'
    -> Gamma = Gamma' /\ action_log = action_log' /\ v = Bits 0 [].
  Proof.
    intros.
    dependent destruction H.
    repeat split.
  Qed.

  Lemma invert_constbits:
    forall
      {pos_t var_t fn_name_t: Type} {var_t_eq_dec: EqDec var_t}
      {reg_t ext_fn_t: Type} {REnv: Env reg_t}
      (r: env_t REnv (fun _: reg_t => BitsToLists.val))
      (sigma: ext_fn_t -> BitsToLists.val -> BitsToLists.val)
      (Gamma Gamma': list (var_t * BitsToLists.val))
      (sched_log action_log action_log': Log REnv) {n} (b: bits n) v,
      interp_action (pos_t := pos_t) (fn_name_t := fn_name_t) r sigma Gamma
        sched_log action_log (USugar (UConstBits b)) action_log' v Gamma'
    -> let l := vect_to_list b in
    Gamma = Gamma' /\ action_log = action_log' /\ v = Bits (List.length l) l.
  Proof.
    intros.
    dependent destruction H.
    repeat split.
  Qed.

  Lemma invert_conststring:
    forall
      {pos_t var_t fn_name_t: Type} {var_t_eq_dec: EqDec var_t}
      {reg_t ext_fn_t: Type} {REnv: Env reg_t}
      (r: env_t REnv (fun _: reg_t => BitsToLists.val))
      (sigma: ext_fn_t -> BitsToLists.val -> BitsToLists.val)
      (Gamma Gamma': list (var_t * BitsToLists.val))
      (sched_log action_log action_log': Log REnv) s v,
      interp_action (pos_t := pos_t) (fn_name_t := fn_name_t) r sigma Gamma
        sched_log action_log (USugar (UConstString s)) action_log' v Gamma'
    -> action_log' = action_log /\ Gamma' = Gamma
    /\ v = (Array
        {| array_type := bits_t 8; array_len := String.length s |}
        (List.map
          (fun x => Bits 8 (vect_to_list x))
          (vect_to_list (SyntaxMacros.array_of_bytes s))
        )
      ).
  Proof.
    intros.
    dependent destruction H.
    repeat split.
  Qed.

  Lemma invert_constenum:
    forall
      {pos_t var_t fn_name_t: Type} {var_t_eq_dec: EqDec var_t}
      {reg_t ext_fn_t: Type} {REnv: Env reg_t}
      (r: env_t REnv (fun _: reg_t => BitsToLists.val))
      (sigma: ext_fn_t -> BitsToLists.val -> BitsToLists.val)
      (Gamma Gamma': list (var_t * BitsToLists.val))
      (sched_log action_log action_log': Log REnv) sig name v,
      interp_action (pos_t := pos_t) (fn_name_t := fn_name_t) r sigma Gamma
        sched_log action_log (USugar (UConstEnum sig name)) action_log' v Gamma'
    -> exists idx,
    Gamma' = Gamma /\ action_log' = action_log
    /\ v = val_of_value (tau:= enum_t sig) (
      vect_nth sig.(enum_bitpatterns) idx
    ).
  Proof.
    intros.
    dependent destruction H.
    exists idx.
    repeat split.
  Qed.

  Lemma invert_progn:
    forall
      {pos_t var_t fn_name_t: Type} {var_t_eq_dec: EqDec var_t}
      {reg_t ext_fn_t: Type} {REnv: Env reg_t}
      (r: env_t REnv (fun _: reg_t => BitsToLists.val))
      (sigma: ext_fn_t -> BitsToLists.val -> BitsToLists.val)
      (Gamma Gamma': list (var_t * BitsToLists.val))
      (sched_log action_log action_log': Log REnv) aa v,
      interp_action (pos_t := pos_t) (fn_name_t := fn_name_t) r sigma Gamma
        sched_log action_log (USugar (UProgn aa)) action_log' v Gamma'
    -> exists lv,
    v = List.hd (Bits 0 []) lv
    /\ interp_list
      r sigma (interp_action r sigma) Gamma sched_log action_log aa action_log'
      lv Gamma'.
  Proof.
    intros.
    dependent destruction H.
    exists lv.
    repeat split.
    assumption.
  Qed.

  Lemma invert_let:
    forall
      {pos_t var_t fn_name_t: Type} {var_t_eq_dec: EqDec var_t}
      {reg_t ext_fn_t: Type} {REnv: Env reg_t}
      (r: env_t REnv (fun _: reg_t => BitsToLists.val))
      (sigma: ext_fn_t -> BitsToLists.val -> BitsToLists.val)
      (Gamma Gamma': list (var_t * BitsToLists.val))
      (sched_log action_log action_log': Log REnv) bindings body v,
      interp_action (pos_t := pos_t) (fn_name_t := fn_name_t) r sigma Gamma
        sched_log action_log (USugar (ULet bindings body)) action_log' v Gamma'
    -> exists Gamma1 Gamma2 action_log1,
    Gamma' = Nat.iter (List.length bindings) (@tl _) Gamma2
    /\ interp_list_ctx
      r sigma (interp_action r sigma) Gamma sched_log action_log bindings
      action_log1 Gamma1
    /\ interp_action
      r sigma Gamma1 sched_log action_log1 body action_log' v Gamma2.
  Proof.
    intros.
    dependent destruction H.
    exists Gamma'.
    exists Gamma''.
    exists action_log'.
    repeat split; assumption.
  Qed.

  Lemma invert_when:
    forall
      {pos_t var_t fn_name_t: Type} {var_t_eq_dec: EqDec var_t}
      {reg_t ext_fn_t: Type} {REnv: Env reg_t}
      (r: env_t REnv (fun _: reg_t => BitsToLists.val))
      (sigma: ext_fn_t -> BitsToLists.val -> BitsToLists.val)
      (Gamma Gamma': list (var_t * BitsToLists.val))
      (sched_log action_log action_log': Log REnv) cond athen v,
      interp_action (pos_t := pos_t) (fn_name_t := fn_name_t) r sigma Gamma
        sched_log action_log (USugar (UWhen cond athen)) action_log' v Gamma'
    -> exists action_log1 Gamma1,
    interp_action
      r sigma Gamma sched_log action_log cond action_log1 (Bits 1 [true]) Gamma1
    /\ interp_action
      r sigma Gamma1 sched_log action_log1 athen action_log' v Gamma'.
  Proof.
    intros.
    dependent destruction H.
    exists action_log'.
    exists Gamma'.
    repeat split; assumption.
  Qed.

Lemma invert_switch_nil:
  forall
    {pos_t var_t fn_name_t: Type} {var_t_eq_dec: EqDec var_t}
    {reg_t ext_fn_t: Type} {REnv: Env reg_t}
    (r: env_t REnv (fun _: reg_t => BitsToLists.val))
    (sigma: ext_fn_t -> BitsToLists.val -> BitsToLists.val)
    (Gamma Gamma': list (var_t * BitsToLists.val))
    (sched_log action_log action_log': Log REnv) var default v,
    interp_action (pos_t := pos_t) (fn_name_t := fn_name_t) r sigma Gamma
      sched_log action_log (USugar (USwitch var default [])) action_log' v
      Gamma'
  -> interp_action r sigma Gamma sched_log action_log default action_log' v
    Gamma'.
  Proof.
    intros.
    dependent destruction H.
    repeat split; assumption.
  Qed.

(* TODO Maybe separate OK and KO so as to avoid generating useless hypotheses *)
Lemma invert_switch:
  forall
    {pos_t var_t fn_name_t: Type} {var_t_eq_dec: EqDec var_t}
    {reg_t ext_fn_t: Type} {REnv: Env reg_t}
    (r: env_t REnv (fun _: reg_t => BitsToLists.val))
    (sigma: ext_fn_t -> BitsToLists.val -> BitsToLists.val)
    (Gamma Gamma': list (var_t * BitsToLists.val))
    (sched_log action_log action_log': Log REnv) var default cond body branches
    v,
  interp_action (pos_t := pos_t) (fn_name_t := fn_name_t) r sigma Gamma
    sched_log action_log (USugar (USwitch var default ((cond, body)::branches)))
    action_log' v Gamma'
  -> exists action_log1 action_log2 Gamma1 Gamma2 v1 v2,
  interp_action r sigma Gamma sched_log action_log var action_log1 v1 Gamma1
  /\ interp_action r sigma Gamma1 sched_log action_log1 cond action_log2 v2
    Gamma2
  /\ (v1 = v2 -> interp_action r sigma Gamma2 sched_log action_log2 body
    action_log' v Gamma')
  /\ (v1 <> v2 -> interp_action r sigma Gamma2 sched_log action_log2 (
    USugar (USwitch var default branches)
  ) action_log' v Gamma').
  Proof.
    intros.
    dependent destruction H.
    - exists action_log'.
      exists action_log''.
      exists Gamma'.
      exists Gamma''.
      exists v0.
      exists v0.
      repeat split; try assumption.
      + intro. assumption.
      + intro. destruct H1. reflexivity.
    - exists action_log'.
      exists action_log''.
      exists Gamma'.
      exists Gamma''.
      exists v0.
      exists v.
      repeat split; try assumption.
      + intro. destruct H1. symmetry. assumption.
      + intro. assumption.
  Qed.

Lemma invert_structinit:
  forall
    {pos_t var_t fn_name_t: Type} {var_t_eq_dec: EqDec var_t}
    {reg_t ext_fn_t: Type} {REnv: Env reg_t}
    (r: env_t REnv (fun _: reg_t => BitsToLists.val))
    (sigma: ext_fn_t -> BitsToLists.val -> BitsToLists.val)
    (Gamma Gamma': list (var_t * BitsToLists.val))
    (sched_log action_log action_log': Log REnv) sig fields v,
  interp_action (pos_t := pos_t) (fn_name_t := fn_name_t) r sigma Gamma
    sched_log action_log (USugar (UStructInit sig fields)) action_log' v Gamma'
  -> exists vs vfields v_init,
  interp_list r sigma (interp_action r sigma) Gamma sched_log action_log
    (map snd fields) action_log' vfields Gamma'
  /\ uvalue_of_struct_bits (struct_fields sig)
      (repeat false (struct_fields_sz (struct_fields sig)))
    = Some vs
  /\ List.fold_left
    (fun vs '(name, v) =>
      let/opt vs := vs in
      subst_field_name (struct_fields sig) name v vs
    )
    (combine (map fst fields) (rev vfields)) (Some vs)
    = Some v_init
  /\ v = Struct sig v_init.
  Proof.
    intros.
    dependent destruction H.
    exists vs.
    exists vfields.
    exists v.
    repeat split; assumption.
  Qed.

Lemma invert_arrayinit:
  forall
    {pos_t var_t fn_name_t: Type} {var_t_eq_dec: EqDec var_t}
    {reg_t ext_fn_t: Type} {REnv: Env reg_t}
    (r: env_t REnv (fun _: reg_t => BitsToLists.val))
    (sigma: ext_fn_t -> BitsToLists.val -> BitsToLists.val)
    (Gamma Gamma': list (var_t * BitsToLists.val))
    (sched_log action_log action_log': Log REnv) tau elements v,
  interp_action (pos_t := pos_t) (fn_name_t := fn_name_t) r sigma Gamma
    sched_log action_log (USugar (UArrayInit tau elements)) action_log' v Gamma'
  -> exists vs velts v_init,
  interp_list r sigma (interp_action r sigma) Gamma sched_log action_log
    elements action_log' velts Gamma'
  /\ uvalue_of_list_bits (tau:=tau)
      (repeat (repeat false (type_sz tau)) (List.length elements))
    = Some vs
  /\ List.fold_left (fun acc v =>
       let/opt2 pos, vs := acc in
       let/opt2 l1, l2 := take_drop pos vs in
       match l2 with
       | [] => None
       | a::l2 => Some (S pos, l1 ++ v :: l2)
       end
     ) (rev velts) (Some (0, vs))
     = Some v_init
  /\ v = Array {| array_type := tau; array_len := List.length elements |}
    (snd v_init).
  Proof.
    intros.
    dependent destruction H.
    exists vs.
    exists velts.
    exists v.
    repeat split; assumption.
  Qed.

Lemma invert_callmodule:
  forall
    {pos_t var_t fn_name_t: Type} {var_t_eq_dec: EqDec var_t}
    {reg_t ext_fn_t: Type} {REnv: Env reg_t}
    (r: env_t REnv (fun _: reg_t => BitsToLists.val))
    (sigma: ext_fn_t -> BitsToLists.val -> BitsToLists.val)
    (Gamma Gamma': list (var_t * BitsToLists.val))
    (sched_log action_log action_log': Log REnv) v
    module_reg_t module_ext_fn_t `{finite: FiniteType module_reg_t}
    (fR: module_reg_t -> reg_t) (fSigma: module_ext_fn_t -> ext_fn_t) fn args,
  interp_action (pos_t := pos_t) (fn_name_t := fn_name_t) r sigma Gamma
    sched_log action_log (USugar (UCallModule fR fSigma fn args)) action_log' v Gamma'
  -> exists lv action_log_init action_log1 Gamma1,
  interp_list r sigma (interp_action r sigma) Gamma sched_log action_log args
    action_log_init lv Gamma'
  /\ let REnv' := @ContextEnv _ _ in
    interp_action
      (create REnv' (fun idx => getenv REnv r (fR idx)))
      (fun f => sigma (fSigma f))
      (map (fun '(name, _, v) => (name, v)) (combine (rev (int_argspec fn)) lv))
      (fLog fR REnv REnv' sched_log) (fLog fR REnv REnv' action_log_init)
      (int_body fn) action_log1 v Gamma1
  /\ action_log' = (fLog' fR REnv REnv' action_log1 action_log_init).
  Proof.
    intros.
    dependent destruction H.
    exists lv.
    exists action_log'.
    exists action_log''.
    exists Gamma''.
    repeat split; assumption.
  Qed.

  Lemma stack_violation_results_in_halt:
    forall (ctx: env_t REnv (fun _ : RV32I.reg_t => BitsToLists.val)),
    stack_violation ctx -> halt_set ctx.
  Proof.
    intros. unfold halt_set. intros. simpl.
    dependent destruction H0. dependent destruction H0.
    dependent destruction H0. dependent destruction H0.
    dependent destruction H1. dependent destruction H1.
    dependent destruction H2. dependent destruction H2.
    dependent destruction H3. dependent destruction H3.
    dependent destruction H4. dependent destruction H4.
    dependent destruction H5. dependent destruction H5.
    dependent destruction H6. dependent destruction H6.
    dependent destruction H7. dependent destruction H7.
    dependent destruction H8. dependent destruction H8.
    dependent destruction H9. dependent destruction H9.
    move l1 before l0. move l2 before l1. move l3 before l2. move l4 before l3.
    move l5 before l4. move l6 before l5. move l7 before l6. move l8 before l7.
    move l9 before l8.

    unfold RV32I.update_on_off in H0.
    dependent destruction H0.
    apply (invert_write ctx ext_sigma [] log_empty log_empty P1 RV32I.on_off ({{ read0(RV32I.on_off) + Ob~1 }}) v l0 Gamma') in H0.
    dependent destruction H0.
    (* repeat destruct H0. *)
    (* destruct H11. *)
    (* destruct H11. *)
    (* destruct H0. *)

    inv H10.
    dependent destruction H0. dependent destruction H1.
    dependent destruction H2. dependent destruction H3.
    dependent destruction H4. dependent destruction H5.
    dependent destruction H6. dependent destruction H7.
    dependent destruction H8. dependent destruction H9.
    move Gamma'0 after Gamma'. move Gamma'1 after Gamma'.
    move Gamma'2 after Gamma'. move Gamma'3 after Gamma'.
    move Gamma'4 after Gamma'. move Gamma'5 after Gamma'.
    move Gamma'6 after Gamma'. move Gamma'7 after Gamma'.
    move Gamma'8 after Gamma'.
    move v0 after v. move v1 after v. move v2 after v. move v3 after v.
    move v4 after v. move v5 after v. move v6 after v. move v7 after v.
    move v8 after v.
    dependent destruction H0. dependent destruction H0.
    dependent destruction H2. dependent destruction H3.
    dependent destruction H4. dependent destruction H5.
    dependent destruction H6. dependent destruction H7.
    dependent destruction H8. dependent destruction H9.
    dependent destruction H10.
    move v0 before H. move v1 before v0. move v2 before v1. move v3 before v2.
    move v4 before v3. move v5 before v4. move v6 before v5. move v7 before v6.
    move v8 before v7. move v9 before v8. move v10 before v9.
    move v11 before v10. move v12 before v11. move v13 before v12.
    move v14 before v13. move v15 before v14. move v16 before v15.
    move v17 before v16. move v18 before v17. move v19 before v18.
    move Gamma'9 after Gamma'. move Gamma'10 after Gamma'.
    move Gamma'11 after Gamma'. move Gamma'12 after Gamma'.
    move Gamma'13 after Gamma'. move Gamma'14 after Gamma'.
    move Gamma'15 after Gamma'. move Gamma'16 after Gamma'.
    move Gamma'17 after Gamma'. move Gamma'18 after Gamma'.
    move action_log'1 before action_log'0.
    move action_log'2 before action_log'1.
    move action_log'3 before action_log'2.
    move action_log'4 before action_log'3.
    move action_log'5 before action_log'4.
    move action_log'6 before action_log'5.
    move action_log'7 before action_log'6.
    move action_log'8 before action_log'7.
    move action_log'9 before action_log'8.
    (* Helps progress but very RAM heavy *)
    dependent destruction H0_.
    dependent destruction H0_0.
    dependent destruction H2_.
    dependent destruction H2_0.
    dependent destruction H2_1.
    dependent destruction H2_1_1.
    dependent destruction H2_1_2.
    dependent destruction H2_2.
    (* dependent destruction H2_0_1. *)
    (* dependent destruction H2_0_1. *)
    (* dependent destruction H2_0_2. *)
    (* dependent destruction H2_0_1_1. *)
    (* dependent destruction H2_0_1_2. *)
    (* dependent destruction H2_0_2_2. *)
    (* dependent destruction H2_0_2_1. *)
    (* dependent destruction H2_0_1_1_1. *)
    (* dependent destruction H2_0_1_1_2. *)
    (* dependent destruction H2_0_2_2_1. *)
    (* dependent destruction H2_0_2_2_2. *)
    (* dependent destruction H2_0_1_1_1_2. *)
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
