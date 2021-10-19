(*! Pipelined instantiation of an RV32I core !*)
Require Import Koika.Frontend.
Require Import rv.RVCore rv.rv32.
Require Import rv.ShadowStack.

(* TC_native adds overhead but makes typechecking large rules faster *)
Ltac _tc_strategy ::= exact TC_native.

Module RVIParams <: RVParams.
  Definition NREGS := 32.
  Definition WIDTH := 32.
  Definition HAS_SHADOW_STACK := true.
End RVIParams.

Module RV32I <: Core.
  Module ShadowStack := ShadowStackF.
  Include (RVCore RVIParams ShadowStack).

  Definition _reg_t := reg_t.
  Definition _ext_fn_t := ext_fn_t.

  Instance FiniteType_rf : FiniteType Rf.reg_t := _.
  Instance FiniteType_scoreboard_rf : FiniteType Scoreboard.Rf.reg_t := _.
  Instance FiniteType_scoreboard : FiniteType Scoreboard.reg_t := _.
  Instance FiniteType_reg_t : FiniteType reg_t := _.

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

  Require Import Koika.UntypedIndTactics.
  Check inline_internal_calls fetch.
  Check desugar_action.
  Definition init := execute.
  Definition pre := desugar_action tt init.
  Definition post := inline_internal_calls pre.
  Print init.
  Time Compute pre.
  Time Compute post.
  Definition post2 := remove_first_n_bindings post 1.
  Time Compute post2.
  Definition post4 := remove_bindings post.
  Time Compute post4.
  Definition post3 := remove_first_n_bindings post2 1.
  Time Compute post3.
  Definition post4 := remove_first_n_bindings post3 1.
  Time Compute post4.
  Definition post5 := remove_first_n_bindings post4 1.
  Time Compute post5.
  Definition post4 := remove_bindings post.
  Time Compute post4.

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
