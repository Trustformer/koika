Require Import Koika.Frontend.

Require Import ISA.
Require Import Instructions.

Section RVHelpers.
  Context {reg_t : Type}.

  Definition inst_field := {|
    struct_name   := "instFields";
    struct_fields := ("opcode", bits_t 7) :: ("funct3", bits_t 3) :: nil
  |}.

  Definition getFields : UInternalFunction reg_t empty_ext_fn_t := {{
    fun getFields (inst : bits_t 32) : struct_t inst_field =>
      struct inst_field {
        opcode := inst[|5`d0 | :+ 7];
        funct3 := inst[|5`d12| :+ 3]
      }
  }}.
End RVHelpers.

Module Type RVParameters.
  Parameter REGISTERS_COUNT : nat.
  Parameter WIDTH : nat.
End RVParameters.

Module Type Core.
  Parameter _reg_t : Type.
  Parameter _ext_fn_t : Type.
  Parameter R : _reg_t -> type. (* State *)
  Parameter Sigma : _ext_fn_t -> ExternalSignature.
  Parameter r : forall reg, R reg. (* Initial state *)
  Parameter rv_rules : rv_rules_t -> rule R Sigma.
  Parameter FiniteType_reg_t : FiniteType _reg_t.
  Parameter Show_reg_t : Show _reg_t.
  Parameter Show_ext_fn_t : Show _ext_fn_t.
  Parameter rv_ext_fn_sim_specs : _ext_fn_t -> ext_fn_sim_spec.
  Parameter rv_ext_fn_rtl_specs : _ext_fn_t -> ext_fn_rtl_spec.
End Core.

  (* Declare state *)
  Inductive reg_t :=
  | toIMem (state: MemReq.reg_t)
  | fromIMem (state: MemResp.reg_t)
  | toDMem (state: MemReq.reg_t)
  | fromDMem (state: MemResp.reg_t)
  | f2d (state: fromFetch.reg_t)
  | f2dprim (state: waitFromFetch.reg_t)
  | d2e (state: fromDecode.reg_t)
  | e2w (state: fromExecute.reg_t)
  | rf (state: Rf.reg_t)
  | mulState (state: Multiplier.reg_t)
  | scoreboard (state: Scoreboard.reg_t)
  | cycle_count
  | instr_count
  | pc
  | epoch.

Module RV (Parameters : RVParameters).

End RV.
