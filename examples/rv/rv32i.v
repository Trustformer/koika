(*! Pipelined instantiation of an RV32I core !*)
Require Import Koika.Frontend.
Require Import rv.RVCore rv.rv32.
Require Import rv.ShadowStack.

(* TODO remove, imported for temporary tests *)
Require Import rv.InstructionsProperties Koika.Normalize Koika.Utils.

(* TC_native adds overhead but makes typechecking large rules faster *)
Ltac _tc_strategy ::= exact TC_native.

Module RVIParams <: RVParams.
  Definition NREGS: nat := 32.
  Definition WIDTH: nat := 32.
  Definition HAS_SHADOW_STACK := true.
End RVIParams.

Module RV32I <: Core.
  Module ShadowStack := ShadowStackF.
  Include (RVCore RVIParams ShadowStack).

  Instance FiniteType_rf : FiniteType Rf.reg_t := _.
  Instance FiniteType_scoreboard_rf : FiniteType Scoreboard.Rf.reg_t := _.
  Instance FiniteType_scoreboard : FiniteType Scoreboard.reg_t := _.
  Instance FiniteType_reg_t : FiniteType reg_t := _.
  (* TODO generalize: more usable FiniteType instanciation. Does this make a
     difference in practice? *)
  Instance FiniteType_reg_t2: FiniteType reg_t.
  Proof.
    eapply (@Build_FiniteType
      _ (@finite_index _ FiniteType_reg_t) (@finite_elements _ FiniteType_reg_t)
    ).
    abstract (exact (@finite_surjective _ FiniteType_reg_t)).
    abstract (exact (@finite_injective _ FiniteType_reg_t)).
  Defined.

Definition is_module_call
  {pos_t var_t fn_name_t reg_t ext_fn_t: Type}
  (ua: uaction pos_t var_t )
: bool :=
  match ua with
  | USugar s =>
    match s with
    | UCallModule _ _ _ _ => true
    | _ => false
    end
  | _ => false
  end.

  Definition _reg_t := reg_t.
  Definition _ext_fn_t := ext_fn_t.

  Definition rv_urules (rl: rv_rules_t) : uaction reg_t ext_fn_t :=
    match rl with
    | Fetch        => fetch
    | Decode       => decode
    | Execute      => execute
    | Writeback    => writeback
    | WaitImem     => wait_imem
    | Imem         => (mem imem)
    | Dmem         => (mem dmem)
    | Tick         => tick
    | UpdateOnOff  => update_on_off
    | EndExecution => end_execution
    end.

  (* Definition initial_rule := writeback. *)
  (* Definition desugared := desugar_action tt initial_rule. *)
  (* Definition last_controlled_act := get_highest_binding_id action desugared. *)
  (* Definition last_controlled_expr := get_highest_binding_id expr desugared. *)
  (* Time Compute distill desugared last_controlled_act last_controlled_expr. *)

  Definition sch : scheduler :=
    UpdateOnOff |> Writeback |> Execute |> Decode |> WaitImem |> Fetch |> Imem
    |> Dmem |> Tick |> EndExecution |> done.
  Definition rules_desug := (fun x => (desugar_action tt (rv_urules x))).
  Time Compute (schedule_to_normal_form rules_desug sch).

(*   Definition rules_l := schedule_to_list_of_rules rules_desug sch2. *)
(*   Definition last_action_init := *)
(*     list_max (List.map (get_highest_binding_id action) rules_l). *)
(*   Definition last_expr_init := *)
(*     list_max (List.map (get_highest_binding_id expr) rules_l). *)
(*   Definition resf := *)
(*     List.fold_left *)
(*       (fun '(ri_acc, la', le') r => *)
(*         let '(ri, la'', le'') := distill r la' le' in *)
(*         (ri_acc++[ri], la'', le'') *)
(*       ) *)
(*       rules_l *)
(*       ([], last_action_init, last_expr_init). *)
(*   Compute resf. *)
(*   Definition rule_info_l := fst (fst resf). *)
(*   Definition la' := snd (fst resf). *)
(*   Definition le' := snd resf. *)
(*   Definition rule_info_with_conflicts_l := detect_all_conflicts rule_info_l. *)
(*   Definition schedule_info := merge_schedule rule_info_with_conflicts_l le'. *)
(*   Definition schedule_info_simpl := *)
(*     remove_write0s (remove_read1s schedule_info la'). *)
(*   Compute rule_info_l. *)
(*   Compute rule_info_with_conflicts_l. *)
(*   Compute schedule_info. *)
(*   Compute schedule_info_simpl. *)


  Definition rv_rules (rl: rv_rules_t) : rule R Sigma :=
    match rl with
    | Fetch        => tc_rule R Sigma fetch
    | Decode       => tc_rule R Sigma decode
    | Execute      => tc_rule R Sigma execute
    | Writeback    => tc_rule R Sigma writeback
    | WaitImem     => tc_rule R Sigma wait_imem
    | Imem         => tc_rule R Sigma (mem imem)
    | Dmem         => tc_rule R Sigma (mem dmem)
    | Tick         => tc_rule R Sigma tick
    | UpdateOnOff  => tc_rule R Sigma update_on_off
    | EndExecution => tc_rule R Sigma end_execution
    end.
End RV32I.

Module RV32IPackage := Package RV32I.
Definition prog := Interop.Backends.register RV32IPackage.package.
Extraction "rv32i.ml" prog.
