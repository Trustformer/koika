(*! Pipelined instantiation of an RV32I core !*)
Require Import Koika.Frontend.

Require Import rv.RVCore rv.rv32.
Require Import rv.Multiplier.

(* TC_native adds overhead but makes typechecking large rules faster *)
Ltac _tc_strategy ::= exact TC_native.

Module RVIParams <: RVParams.
  Definition NREGS := 32.
  Definition WIDTH := 32.
End RVIParams.

Module Mul32Params <: Multiplier_sig.
  Definition n := 32.
End Mul32Params.

Module RV32I <: Core.
  Module Multiplier := ShiftAddMultiplier Mul32Params.
  Include (RVCore RVIParams Multiplier).

  Definition _reg_t := reg_t.
  Definition _ext_fn_t := ext_fn_t.

  Definition tc_fetch := tc_rule R Sigma fetch.
  Definition tc_wait_imem := tc_rule R Sigma wait_imem.
  Definition tc_decode := tc_rule R Sigma decode.
  Definition tc_execute := tc_rule R Sigma execute.
  Definition tc_writeback := tc_rule R Sigma writeback.
  Definition tc_step_multiplier := tc_rule R Sigma step_multiplier.
  Definition tc_imem := tc_rule R Sigma (mem imem).
  Definition tc_dmem := tc_rule R Sigma (mem dmem).
  Definition tc_tick := tc_rule R Sigma tick.

  Definition rv_rules (rl: rv_rules_t) : rule R Sigma :=
    match rl with
    | Fetch => tc_fetch
    | Decode => tc_decode
    | Execute => tc_execute
    | Writeback => tc_writeback
    | WaitImem => tc_wait_imem
    | Imem => tc_imem
    | Dmem => tc_dmem
    | StepMultiplier => tc_step_multiplier
    | Tick => tc_tick
    end.

  Instance FiniteType_rf : FiniteType Rf.reg_t := _.
  Instance FiniteType_scoreboard_rf : FiniteType Scoreboard.Rf.reg_t := _.
  Instance FiniteType_scoreboard : FiniteType Scoreboard.reg_t := _.
  Instance FiniteType_reg_t : FiniteType reg_t := _.
End RV32I.

Module RV32IPackage := Package RV32I.
Definition prog := Interop.Backends.register RV32IPackage.package.
Extraction "rv32i.ml" prog.
