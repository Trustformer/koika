(*! Pipelined instantiation of an RV32I core !*)
Require Import Koika.Frontend.
Require Import rv.RVCore rv.rv32.
Require Import rv.ShadowStack.

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

  #[global] Instance FiniteType_rf : FiniteType Rf.reg_t := _.
  #[global] Instance FiniteType_scoreboard_rf : FiniteType Scoreboard.Rf.reg_t := _.
  #[global] Instance FiniteType_scoreboard : FiniteType Scoreboard.reg_t := _.
  #[global] Instance FiniteType_reg_t : FiniteType reg_t := _.
  (* TODO generalize: more usable FiniteType instanciation. Does this make a
     difference in practice? *)
  #[global] Instance FiniteType_reg_t2: FiniteType reg_t.
  Proof.
    eapply (@Build_FiniteType
      _ (@finite_index _ FiniteType_reg_t) (@finite_elements _ FiniteType_reg_t)
    ).
    abstract (exact (@finite_surjective _ FiniteType_reg_t)).
    abstract (exact (@finite_injective _ FiniteType_reg_t)).
  Defined.

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
    | EndExecution => end_execution
    end.

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
    | EndExecution => tc_rule R Sigma end_execution
    end.
End RV32I.

Module RV32IPackage := Package RV32I.
Definition prog := Interop.Backends.register RV32IPackage.package.
Set Extraction Output Directory "extr".
Extraction "rv32i.ml" prog.
