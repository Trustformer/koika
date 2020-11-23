Require Import Koika.Frontend.

Module ProducerConsumer.
  (* 1. Parameterization *)
  Definition r_sz := pow2 2. (** Size of a register *)
  Definition q_cap := pow2 0. (** Capacity of the queue *)

  (* 2. Registers description *)
  (* 2.1. Names *)
  Inductive reg_t :=
  | producer_counter (** State of the producer *)
  | queue_empty (** State of the queue *)
  | queue_datum (** Contents of the queue *)
  | output. (** Data sink (into which consumer writes outputs) *)

  (* 2.2. Memory requirements *)
  Definition R r :=
    match r with
    | producer_counter => bits_t r_sz
    | queue_empty => bits_t 1
    | queue_datum => bits_t r_sz
    | output => bits_t r_sz
    end.

  (* 2.3. Initial values *)
  Definition r (reg: reg_t): R reg :=
    match reg with
    | producer_counter => Bits.zero
    | queue_empty => Bits.one
    | queue_datum => Bits.zero
    | output => Bits.zero
    end.

  (* Rules *)
  (* 3. Rules description *)
  (* 3.1. Names *)
  Inductive rule_name_t :=
  | produce
  | consume.

  (* 3.2. Definitions *)
  Definition _produce : uaction reg_t empty_ext_fn_t :=
    {{
      let q := read0(queue_empty) in
      if q then
        let v := read0(producer_counter) in
        write0(queue_datum, v);
        write0(producer_counter, v+Ob~0~0~0~1);
        write0(queue_empty, Ob~1)
      else
        fail
    }}.

  Definition _consume : uaction reg_t empty_ext_fn_t :=
    {{
      let q := read1(queue_empty) in
      if !q then
        let v := read1(queue_datum) in
        write1(queue_empty, Ob~0);
        write1(output, v)
      else
        fail
    }}.

  (* 3.3. Rule name to definition mapping *)
  Definition rules :=
    tc_rules R empty_Sigma
      (fun r =>
        match r with
        | produce => _produce
        | consume => _consume
        end
      ).

  (* 4. Scheduler definition *)
  Definition pc_scheduler : scheduler :=
    produce |> consume |> done.

  (* 5. Misc. *)
  Definition cr := ContextEnv.(create) r.

  (** Way to inject Verilog code, disabled here *)
  Definition cycle_log :=
    tc_compute (interp_scheduler cr empty_sigma rules pc_scheduler).

  Definition produce_result :=
    tc_compute (
      interp_action cr empty_sigma CtxEmpty log_empty log_empty (rules produce)
    ).

  Definition consume_result :=
    tc_compute (
      interp_action cr empty_sigma CtxEmpty log_empty log_empty (rules consume)
    ).

  Definition result := tc_compute(commit_update cr cycle_log).

  Definition external (r : rule_name_t) := false.

  Definition circuits := compile_scheduler rules external pc_scheduler.

  Definition circuits_result :=
    tc_compute (
      interp_circuits empty_sigma circuits (lower_r (ContextEnv.(create) r))
    ).

  Example test: circuits_result = Environments.map _ (fun _ => bits_of_value) result :=
    eq_refl.

  Definition package :=
    {|
      ip_koika := {|
        koika_reg_types := R;
        koika_reg_init reg := r reg;
        koika_ext_fn_types := empty_Sigma;
        koika_rules := rules;
        koika_rule_external := external;
        koika_scheduler := pc_scheduler;
        koika_module_name := "vector"
      |};

      ip_sim := {|
        sp_ext_fn_specs := empty_ext_fn_props;
        sp_prelude := None
      |};

      ip_verilog := {|
        vp_ext_fn_specs := empty_ext_fn_props
      |}
    |}.
End ProducerConsumer.

Definition prog := Interop.Backends.register ProducerConsumer.package.
Extraction "producer_consumer.ml" prog.
