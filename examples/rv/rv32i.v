(*! Pipelined instantiation of an RV32I core !*)
Require Import Koika.Frontend.
Require Import rv.RVCore rv.rv32.
Require Import rv.ShadowStack.

(* TODO remove, imported for temporary tests *)
Require Import rv.InstructionsProperties Koika.Normalize Koika.Utils
  Koika.Zipper.

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

  Definition initial_rule := execute.
  Definition desugared := desugar_action tt initial_rule.
  Set Printing All.
  Compute desugared.
  Definition last_controlled := get_highest_binding_number desugared.
  Compute last_controlled.
  Definition rule_info := distill desugared last_controlled.
  Unset Printing All.
  Compute rule_info.

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

    Compute sch
End RV32I.

Module RV32IPackage := Package RV32I.
Definition prog := Interop.Backends.register RV32IPackage.package.
Extraction "rv32i.ml" prog.
