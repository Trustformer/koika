(*! Pipelined instantiation of an RV32E core !*)
Require Import Koika.Frontend.

Require Import rv.RVCore rv.rv32.
Require Import rv.Multiplier.

Module RV32EParams <: RVParams.
  Definition NREGS := 16.
  Definition WIDTH := 32.
End RV32EParams.

Module RV32E <: Core.
  Module Multiplier := DummyMultiplier Mul32Params.
  Include (RVCore RV32EParams Multiplier).

  Definition _reg_t := reg_t.
  Definition _ext_fn_t := ext_fn_t.

  Definition tc_fetch := tc_rule R Sigma fetch <: rule R Sigma.
  Definition tc_wait_imem := tc_rule R Sigma wait_imem <: rule R Sigma.
  Definition tc_decode := tc_rule R Sigma decode <: rule R Sigma.
  Definition tc_execute := tc_rule R Sigma execute <: rule R Sigma.
  Definition tc_writeback := tc_rule R Sigma writeback <: rule R Sigma.
  Definition tc_step_multiplier :=
    tc_rule R Sigma step_multiplier <: rule R Sigma.
  Definition tc_imem := tc_rule R Sigma (mem imem) <: rule R Sigma.
  Definition tc_dmem := tc_rule R Sigma (mem dmem) <: rule R Sigma.
  Definition tc_tick := tc_rule R Sigma tick.
  Definition tc_end_execution := tc_rule R Sigma end_execution.

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
    | EndExecution => tc_end_execution
    end.

  Instance FiniteType_rf : FiniteType Rf.reg_t := _.
  Instance FiniteType_scoreboard_rf : FiniteType Scoreboard.Rf.reg_t := _.
  Instance FiniteType_scoreboard : FiniteType Scoreboard.reg_t := _.
  Instance FiniteType_reg_t : FiniteType reg_t := _.
End RV32E.

Module RV32EPackage := Package RV32E.
Definition prog := Interop.Backends.register RV32EPackage.package.
Extraction "rv32e.ml" prog.
