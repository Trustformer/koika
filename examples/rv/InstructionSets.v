Require Import MSetInterface.

Require Import Koika.Frontend.

(* Standards *)
Inductive memory_model : Type :=
| RVWMO.

Inductive base_standard : Type :=
| RV32I
| RV64I.

Inductive extension : Type :=
| RVM
| RVA
| RVF
| RVD
| RVQ
| RVC
| RVZiCSR
| RVZifencei.

(* ExtensionsSet *)
Scheme Equality for extension.

Module DecidableExtension <: DecidableType.
  Definition t := extension.
  Definition eq := @eq extension.
  Instance eq_equiv : @Equivalence extension eq := eq_equivalence.
  Definition eq_dec := extension_eq_dec.
End DecidableExtension.

Module ExtensionsSet <: WSetsOn DecidableExtension.
  Include WSetsOn DecidableExtension.
End ExtensionsSet.

(* ISA *)
Record ISA : Type := {
  ISA_memory_model: memory_model;
  ISA_base_standard : base_standard;
  ISA_activated_extensions : ExtensionsSet.t;
}.

(* Instructions *)
Inductive instruction_internal_name : Type :=
(* RV32I *)
| LUI_32I
| AUIPC_32I
| JAL_32I
| JALR_32I
| BEQ_32I
| BNE_32I
| BLT_32I
| BGE_32I
| BLTU_32I
| BGEU_32I
| LB_32I
| LH_32I
| LW_32I
| LBU_32I
| LHU_32I
| SB_32I
| SH_32I
| SW_32I
| ADDI_32I
| SLTI_32I
| SLTIU_32I
| XORI_32I
| ORI_32I
| ANDI_32I
| SLLI_32I
| SRLI_32I
| SRAI_32I
| ADD_32I
| SUB_32I
| SLL_32I
| SLT_32I
| SLTU_32I
| XOR_32I
| SRL_32I
| SRA_32I
| OR_32I
| AND_32I
| FENCE_32I
| ECALL_32I
| EBREAK_32I
(* RV64I *)
| LUI_64I
| AUIPC_64I
| JAL_64I
| JALR_64I
| BEQ_64I
| BNE_64I
| BLT_64I
| BGE_64I
| BLTU_64I
| BGEU_64I
| LB_64I
| LH_64I
| LW_64I
| LBU_64I
| LHU_64I
| SB_64I
| SH_64I
| SW_64I
| ADDI_64I
| SLTI_64I
| SLTIU_64I
| XORI_64I
| ORI_64I
| ANDI_64I
| SLLI_64I
| SRLI_64I
| SRAI_64I
| ADD_64I
| SUB_64I
| SLL_64I
| SLT_64I
| SLTU_64I
| XOR_64I
| SRL_64I
| SRA_64I
| OR_64I
| AND_64I
| FENCE_64I
| ECALL_64I
| EBREAK_64I
| LWU_64I
| LD_64I
| SD_64I
| ADDIW_64I
| SLLIW_64I
| SRLIW_64I
| SRAIW_64I
| ADDW_64I
| SUBW_64I
| SLLW_64I
| SRLW_64I
| SRAW_64I
(* RV32Zifencei *)
| FENCE_I_32Zifencei
(* RV64Zifencei *)
| FENCE_I_64Zifencei
(* RV32Zicsr *)
| CSRRW_32Zicsr
| CSRRS_32Zicsr
| CSRRC_32Zicsr
| CSRRWI_32Zicsr
| CSRRSI_32Zicsr
| CSRRCI_32Zicsr
(* RV64Zicsr *)
| CSRRW_64Zicsr
| CSRRS_64Zicsr
| CSRRC_64Zicsr
| CSRRWI_64Zicsr
| CSRRSI_64Zicsr
| CSRRCI_64Zicsr
(* RV32M *)
| MUL_32M
| MULH_32M
| MULHSU_32M
| MULHU_32M
| DIV_32M
| DIVU_32M
| REM_32M
| REMU_32M
(* RV64M *)
| MUL_64M
| MULH_64M
| MULHSU_64M
| MULHU_64M
| DIV_64M
| DIVU_64M
| REM_64M
| REMU_64M
| MULW_64M
| DIVW_64M
| DIVUW_64M
| REMW_64M
| REMUW_64M
(* RV32A *)
| LR_W_32A
| SC_W_32A
| AMOSWAP_W_32A
| AMOADD_W_32A
| AMOXOR_W_32A
| AMOAND_W_32A
| AMOOR_W_32A
| AMOMIN_W_32A
| AMOMAX_W_32A
| AMOMINU_W_32A
| AMOMAXU_W_32A
(* RV64A *)
| LR_W_64A
| SC_W_64A
| AMOSWAP_W_64A
| AMOADD_W_64A
| AMOXOR_W_64A
| AMOAND_W_64A
| AMOOR_W_64A
| AMOMIN_W_64A
| AMOMAX_W_64A
| AMOMINU_W_64A
| AMOMAXU_W_64A
| LR_D_64A
| SC_D_64A
| AMOSWAP_D_64A
| AMOADD_D_64A
| AMOXOR_D_64A
| AMOAND_D_64A
| AMOOR_D_64A
| AMOMIN_D_64A
| AMOMAX_D_64A
| AMOMINU_D_64A
| AMOMAXU_D_64A
(* RV32F *)
| FLW_32F
| FSW_32F
| FMADD_S_32F
| FMSUB_S_32F
| FNMSUB_S_32F
| FNMADD_S_32F
| FADD_S_32F
| FSUB_S_32F
| FMUL_S_32F
| FDIV_S_32F
| FSQRT_S_32F
| FSGNJ_S_32F
| FSGNJN_S_32F
| FSGNJX_S_32F
| FMIN_S_32F
| FMAX_S_32F
| FCVT_W_S_32F
| FCVT_WU_S_32F
| FMV_X_W_32F
| FEQ_S_32F
| FLT_S_32F
| FLE_S_32F
| FCLASS_S_32F
| FCVT_S_W_32F
| FCVT_S_WU_32F
| FMV_W_X_32F
(* RV64F *)
| FLW_64F
| FSW_64F
| FMADD_S_64F
| FMSUB_S_64F
| FNMSUB_S_64F
| FNMADD_S_64F
| FADD_S_64F
| FSUB_S_64F
| FMUL_S_64F
| FDIV_S_64F
| FSQRT_S_64F
| FSGNJ_S_64F
| FSGNJN_S_64F
| FSGNJX_S_64F
| FMIN_S_64F
| FMAX_S_64F
| FCVT_W_S_64F
| FCVT_WU_S_64F
| FMV_X_W_64F
| FEQ_S_64F
| FLT_S_64F
| FLE_S_64F
| FCLASS_S_64F
| FCVT_S_W_64F
| FCVT_S_WU_64F
| FMV_W_X_64F
| FCVT_L_S_64F
| FCVT_LU_S_64F
| FCVT_S_L_64F
| FCVT_S_LU_64F
(* RV32D *)
| FLD_32D
| FSD_32D
| FMADD_D_32D
| FMSUB_D_32D
| FNMSUB_D_32D
| FNMADD_D_32D
| FADD_D_32D
| FSUB_D_32D
| FMUL_D_32D
| FDIV_D_32D
| FSQRT_D_32D
| FSGNJ_D_32D
| FSGNJN_D_32D
| FSGNJX_D_32D
| FMIN_D_32D
| FMAX_D_32D
| FCVT_S_D_32D
| FCVT_D_S_32D
| FEQ_D_32D
| FLT_D_32D
| FLE_D_32D
| FCLASS_D_32D
| FCVT_W_D_32D
| FCVT_WU_D_32D
| FCVT_D_W_32D
| FCVT_D_WU_32D
(* RV64D *)
| FLD_64D
| FSD_64D
| FMADD_D_64D
| FMSUB_D_64D
| FNMSUB_D_64D
| FNMADD_D_64D
| FADD_D_64D
| FSUB_D_64D
| FMUL_D_64D
| FDIV_D_64D
| FSQRT_D_64D
| FSGNJ_D_64D
| FSGNJN_D_64D
| FSGNJX_D_64D
| FMIN_D_64D
| FMAX_D_64D
| FCVT_S_D_64D
| FCVT_D_S_64D
| FEQ_D_64D
| FLT_D_64D
| FLE_D_64D
| FCLASS_D_64D
| FCVT_W_D_64D
| FCVT_WU_D_64D
| FCVT_D_W_64D
| FCVT_D_WU_64D
| FCVT_L_D_64D
| FCVT_LU_D_64D
| FMV_X_D_64D
| FCVT_D_L_64D
| FCVT_D_LU_64D
| FMV_D_X_64D
(* RV32Q *)
| FLQ_32Q
| FSQ_32Q
| FMADD_Q_32Q
| FMSUB_Q_32Q
| FNMSUB_Q_32Q
| FNMADD_Q_32Q
| FADD_Q_32Q
| FSUB_Q_32Q
| FMUL_Q_32Q
| FDIV_Q_32Q
| FSQRT_Q_32Q
| FSGNJ_Q_32Q
| FSGNJN_Q_32Q
| FSGNJX_Q_32Q
| FMIN_Q_32Q
| FMAX_Q_32Q
| FCVT_S_Q_32Q
| FCVT_Q_S_32Q
| FCVT_D_Q_32Q
| FCVT_Q_D_32Q
| FEQ_Q_32Q
| FLT_Q_32Q
| FLE_Q_32Q
| FCLASS_Q_32Q
| FCVT_W_Q_32Q
| FCVT_WU_Q_32Q
| FCVT_Q_W_32Q
| FCVT_Q_WU_32Q
(* RV64Q *)
| FLQ_64Q
| FSQ_64Q
| FMADD_Q_64Q
| FMSUB_Q_64Q
| FNMSUB_Q_64Q
| FNMADD_Q_64Q
| FADD_Q_64Q
| FSUB_Q_64Q
| FMUL_Q_64Q
| FDIV_Q_64Q
| FSQRT_Q_64Q
| FSGNJ_Q_64Q
| FSGNJN_Q_64Q
| FSGNJX_Q_64Q
| FMIN_Q_64Q
| FMAX_Q_64Q
| FCVT_S_Q_64Q
| FCVT_Q_S_64Q
| FCVT_D_Q_64Q
| FCVT_Q_D_64Q
| FEQ_Q_64Q
| FLT_Q_64Q
| FLE_Q_64Q
| FCLASS_Q_64Q
| FCVT_W_Q_64Q
| FCVT_WU_Q_64Q
| FCVT_Q_W_64Q
| FCVT_Q_WU_64Q
| FCVT_L_Q_64Q
| FCVT_LU_Q_64Q
| FCVT_Q_L_64Q
| FCVT_Q_LU_64Q.

Module Decidable_instruction_internal_name <: DecidableType.
  Definition t := instruction_internal_name.
  Definition eq := @eq instruction_internal_name.
  Instance eq_equiv : @Equivalence instruction_internal_name eq :=
    eq_equivalence.
  Definition eq_dec : forall a b : instruction_internal_name,
    {a = b} + {a <> b}.
  Admitted.
End Decidable_instruction_internal_name.

Module InstructionsInternalNamesSet
  <: WSetsOn Decidable_instruction_internal_name.
  Include WSetsOn Decidable_instruction_internal_name.
End InstructionsInternalNamesSet.

Definition RV32I_instruction_internal_names : InstructionsInternalNamesSet.t :=
  (InstructionsInternalNamesSet.add LUI_32I
  (InstructionsInternalNamesSet.add AUIPC_32I
  (InstructionsInternalNamesSet.add JAL_32I
  (InstructionsInternalNamesSet.add JALR_32I
  (InstructionsInternalNamesSet.add BEQ_32I
  (InstructionsInternalNamesSet.add BNE_32I
  (InstructionsInternalNamesSet.add BLT_32I
  (InstructionsInternalNamesSet.add BGE_32I
  (InstructionsInternalNamesSet.add BLTU_32I
  (InstructionsInternalNamesSet.add BGEU_32I
  (InstructionsInternalNamesSet.add LB_32I
  (InstructionsInternalNamesSet.add LH_32I
  (InstructionsInternalNamesSet.add LW_32I
  (InstructionsInternalNamesSet.add LBU_32I
  (InstructionsInternalNamesSet.add LHU_32I
  (InstructionsInternalNamesSet.add SB_32I
  (InstructionsInternalNamesSet.add SH_32I
  (InstructionsInternalNamesSet.add SW_32I
  (InstructionsInternalNamesSet.add ADDI_32I
  (InstructionsInternalNamesSet.add SLTI_32I
  (InstructionsInternalNamesSet.add SLTIU_32I
  (InstructionsInternalNamesSet.add XORI_32I
  (InstructionsInternalNamesSet.add ORI_32I
  (InstructionsInternalNamesSet.add ANDI_32I
  (InstructionsInternalNamesSet.add SLLI_32I
  (InstructionsInternalNamesSet.add SRLI_32I
  (InstructionsInternalNamesSet.add SRAI_32I
  (InstructionsInternalNamesSet.add ADD_32I
  (InstructionsInternalNamesSet.add SUB_32I
  (InstructionsInternalNamesSet.add SLL_32I
  (InstructionsInternalNamesSet.add SLT_32I
  (InstructionsInternalNamesSet.add SLTU_32I
  (InstructionsInternalNamesSet.add XOR_32I
  (InstructionsInternalNamesSet.add SRL_32I
  (InstructionsInternalNamesSet.add SRA_32I
  (InstructionsInternalNamesSet.add OR_32I
  (InstructionsInternalNamesSet.add AND_32I
  (InstructionsInternalNamesSet.add FENCE_32I
  (InstructionsInternalNamesSet.add ECALL_32I
  (InstructionsInternalNamesSet.add EBREAK_32I
  InstructionsInternalNamesSet.empty)))))))))))))))))))))))))))))))))))))))).

Definition RV64I_instruction_internal_names : InstructionsInternalNamesSet.t :=
  (InstructionsInternalNamesSet.add LUI_64I
  (InstructionsInternalNamesSet.add AUIPC_64I
  (InstructionsInternalNamesSet.add JAL_64I
  (InstructionsInternalNamesSet.add JALR_64I
  (InstructionsInternalNamesSet.add BEQ_64I
  (InstructionsInternalNamesSet.add BNE_64I
  (InstructionsInternalNamesSet.add BLT_64I
  (InstructionsInternalNamesSet.add BGE_64I
  (InstructionsInternalNamesSet.add BLTU_64I
  (InstructionsInternalNamesSet.add BGEU_64I
  (InstructionsInternalNamesSet.add LB_64I
  (InstructionsInternalNamesSet.add LH_64I
  (InstructionsInternalNamesSet.add LW_64I
  (InstructionsInternalNamesSet.add LBU_64I
  (InstructionsInternalNamesSet.add LHU_64I
  (InstructionsInternalNamesSet.add SB_64I
  (InstructionsInternalNamesSet.add SH_64I
  (InstructionsInternalNamesSet.add SW_64I
  (InstructionsInternalNamesSet.add ADDI_64I
  (InstructionsInternalNamesSet.add SLTI_64I
  (InstructionsInternalNamesSet.add SLTIU_64I
  (InstructionsInternalNamesSet.add XORI_64I
  (InstructionsInternalNamesSet.add ORI_64I
  (InstructionsInternalNamesSet.add ANDI_64I
  (InstructionsInternalNamesSet.add SLLI_64I
  (InstructionsInternalNamesSet.add SRLI_64I
  (InstructionsInternalNamesSet.add SRAI_64I
  (InstructionsInternalNamesSet.add ADD_64I
  (InstructionsInternalNamesSet.add SUB_64I
  (InstructionsInternalNamesSet.add SLL_64I
  (InstructionsInternalNamesSet.add SLT_64I
  (InstructionsInternalNamesSet.add SLTU_64I
  (InstructionsInternalNamesSet.add XOR_64I
  (InstructionsInternalNamesSet.add SRL_64I
  (InstructionsInternalNamesSet.add SRA_64I
  (InstructionsInternalNamesSet.add OR_64I
  (InstructionsInternalNamesSet.add AND_64I
  (InstructionsInternalNamesSet.add FENCE_64I
  (InstructionsInternalNamesSet.add ECALL_64I
  (InstructionsInternalNamesSet.add EBREAK_64I
  (InstructionsInternalNamesSet.add LWU_64I
  (InstructionsInternalNamesSet.add LD_64I
  (InstructionsInternalNamesSet.add SD_64I
  (InstructionsInternalNamesSet.add ADDIW_64I
  (InstructionsInternalNamesSet.add SLLIW_64I
  (InstructionsInternalNamesSet.add SRLIW_64I
  (InstructionsInternalNamesSet.add SRAIW_64I
  (InstructionsInternalNamesSet.add ADDW_64I
  (InstructionsInternalNamesSet.add SUBW_64I
  (InstructionsInternalNamesSet.add SLLW_64I
  (InstructionsInternalNamesSet.add SRLW_64I
  (InstructionsInternalNamesSet.add SRAW_64I
  InstructionsInternalNamesSet.empty
  )))))))))))))))))))))))))))))))))))))))))))))))))))).

Definition RV32Zifencei_instruction_internal_names
  : InstructionsInternalNamesSet.t :=
  InstructionsInternalNamesSet.add
    FENCE_I_32Zifencei (InstructionsInternalNamesSet.empty).

Definition RV64Zifencei_instruction_internal_names
  : InstructionsInternalNamesSet.t :=
  InstructionsInternalNamesSet.add
    FENCE_I_64Zifencei (InstructionsInternalNamesSet.empty).

Definition RV32Zicsr_instruction_internal_names
  : InstructionsInternalNamesSet.t :=
  (InstructionsInternalNamesSet.add CSRRW_32Zicsr
  (InstructionsInternalNamesSet.add CSRRS_32Zicsr
  (InstructionsInternalNamesSet.add CSRRC_32Zicsr
  (InstructionsInternalNamesSet.add CSRRWI_32Zicsr
  (InstructionsInternalNamesSet.add CSRRSI_32Zicsr
  (InstructionsInternalNamesSet.add CSRRCI_32Zicsr
  InstructionsInternalNamesSet.empty)))))).

Definition RV64Zicsr_instruction_internal_names
  : InstructionsInternalNamesSet.t :=
  (InstructionsInternalNamesSet.add CSRRW_64Zicsr
  (InstructionsInternalNamesSet.add CSRRS_64Zicsr
  (InstructionsInternalNamesSet.add CSRRC_64Zicsr
  (InstructionsInternalNamesSet.add CSRRWI_64Zicsr
  (InstructionsInternalNamesSet.add CSRRSI_64Zicsr
  (InstructionsInternalNamesSet.add CSRRCI_64Zicsr
  InstructionsInternalNamesSet.empty)))))).

Definition RV32M_instruction_internal_names : InstructionsInternalNamesSet.t :=
  (InstructionsInternalNamesSet.add MUL_32M
  (InstructionsInternalNamesSet.add MULH_32M
  (InstructionsInternalNamesSet.add MULHSU_32M
  (InstructionsInternalNamesSet.add MULHU_32M
  (InstructionsInternalNamesSet.add DIV_32M
  (InstructionsInternalNamesSet.add DIVU_32M
  (InstructionsInternalNamesSet.add REM_32M
  (InstructionsInternalNamesSet.add REMU_32M
  InstructionsInternalNamesSet.empty)))))))).

Definition RV64M_instruction_internal_names : InstructionsInternalNamesSet.t :=
  (InstructionsInternalNamesSet.add MUL_64M
  (InstructionsInternalNamesSet.add MULH_64M
  (InstructionsInternalNamesSet.add MULHSU_64M
  (InstructionsInternalNamesSet.add MULHU_64M
  (InstructionsInternalNamesSet.add DIV_64M
  (InstructionsInternalNamesSet.add DIVU_64M
  (InstructionsInternalNamesSet.add REM_64M
  (InstructionsInternalNamesSet.add REMU_64M
  (InstructionsInternalNamesSet.add MULW_64M
  (InstructionsInternalNamesSet.add DIVW_64M
  (InstructionsInternalNamesSet.add DIVUW_64M
  (InstructionsInternalNamesSet.add REMW_64M
  (InstructionsInternalNamesSet.add REMUW_64M
  InstructionsInternalNamesSet.empty))))))))))))).

Definition RV32A_instruction_internal_names : InstructionsInternalNamesSet.t :=
  (InstructionsInternalNamesSet.add LR_W_32A
  (InstructionsInternalNamesSet.add SC_W_32A
  (InstructionsInternalNamesSet.add AMOSWAP_W_32A
  (InstructionsInternalNamesSet.add AMOADD_W_32A
  (InstructionsInternalNamesSet.add AMOXOR_W_32A
  (InstructionsInternalNamesSet.add AMOAND_W_32A
  (InstructionsInternalNamesSet.add AMOOR_W_32A
  (InstructionsInternalNamesSet.add AMOMIN_W_32A
  (InstructionsInternalNamesSet.add AMOMAX_W_32A
  (InstructionsInternalNamesSet.add AMOMINU_W_32A
  (InstructionsInternalNamesSet.add AMOMAXU_W_32A
  InstructionsInternalNamesSet.empty))))))))))).

Definition RV64A_instruction_internal_names : InstructionsInternalNamesSet.t :=
  (InstructionsInternalNamesSet.add LR_W_64A
  (InstructionsInternalNamesSet.add SC_W_64A
  (InstructionsInternalNamesSet.add AMOSWAP_W_64A
  (InstructionsInternalNamesSet.add AMOADD_W_64A
  (InstructionsInternalNamesSet.add AMOXOR_W_64A
  (InstructionsInternalNamesSet.add AMOAND_W_64A
  (InstructionsInternalNamesSet.add AMOOR_W_64A
  (InstructionsInternalNamesSet.add AMOMIN_W_64A
  (InstructionsInternalNamesSet.add AMOMAX_W_64A
  (InstructionsInternalNamesSet.add AMOMINU_W_64A
  (InstructionsInternalNamesSet.add AMOMAXU_W_64A
  (InstructionsInternalNamesSet.add LR_D_64A
  (InstructionsInternalNamesSet.add SC_D_64A
  (InstructionsInternalNamesSet.add AMOSWAP_D_64A
  (InstructionsInternalNamesSet.add AMOADD_D_64A
  (InstructionsInternalNamesSet.add AMOXOR_D_64A
  (InstructionsInternalNamesSet.add AMOAND_D_64A
  (InstructionsInternalNamesSet.add AMOOR_D_64A
  (InstructionsInternalNamesSet.add AMOMIN_D_64A
  (InstructionsInternalNamesSet.add AMOMAX_D_64A
  (InstructionsInternalNamesSet.add AMOMINU_D_64A
  (InstructionsInternalNamesSet.add AMOMAXU_D_64A
  InstructionsInternalNamesSet.empty)))))))))))))))))))))).

Definition RV32F_instruction_internal_names : InstructionsInternalNamesSet.t :=
  (InstructionsInternalNamesSet.add FLW_32F
  (InstructionsInternalNamesSet.add FSW_32F
  (InstructionsInternalNamesSet.add FMADD_S_32F
  (InstructionsInternalNamesSet.add FMSUB_S_32F
  (InstructionsInternalNamesSet.add FNMSUB_S_32F
  (InstructionsInternalNamesSet.add FNMADD_S_32F
  (InstructionsInternalNamesSet.add FADD_S_32F
  (InstructionsInternalNamesSet.add FSUB_S_32F
  (InstructionsInternalNamesSet.add FMUL_S_32F
  (InstructionsInternalNamesSet.add FDIV_S_32F
  (InstructionsInternalNamesSet.add FSQRT_S_32F
  (InstructionsInternalNamesSet.add FSGNJ_S_32F
  (InstructionsInternalNamesSet.add FSGNJN_S_32F
  (InstructionsInternalNamesSet.add FSGNJX_S_32F
  (InstructionsInternalNamesSet.add FMIN_S_32F
  (InstructionsInternalNamesSet.add FMAX_S_32F
  (InstructionsInternalNamesSet.add FCVT_W_S_32F
  (InstructionsInternalNamesSet.add FCVT_WU_S_32F
  (InstructionsInternalNamesSet.add FMV_X_W_32F
  (InstructionsInternalNamesSet.add FEQ_S_32F
  (InstructionsInternalNamesSet.add FLT_S_32F
  (InstructionsInternalNamesSet.add FLE_S_32F
  (InstructionsInternalNamesSet.add FCLASS_S_32F
  (InstructionsInternalNamesSet.add FCVT_S_W_32F
  (InstructionsInternalNamesSet.add FCVT_S_WU_32F
  (InstructionsInternalNamesSet.add FMV_W_X_32F
  InstructionsInternalNamesSet.empty)))))))))))))))))))))))))).

Definition RV64F_instruction_internal_names : InstructionsInternalNamesSet.t :=
  (InstructionsInternalNamesSet.add FLW_64F
  (InstructionsInternalNamesSet.add FSW_64F
  (InstructionsInternalNamesSet.add FMADD_S_64F
  (InstructionsInternalNamesSet.add FMSUB_S_64F
  (InstructionsInternalNamesSet.add FNMSUB_S_64F
  (InstructionsInternalNamesSet.add FNMADD_S_64F
  (InstructionsInternalNamesSet.add FADD_S_64F
  (InstructionsInternalNamesSet.add FSUB_S_64F
  (InstructionsInternalNamesSet.add FMUL_S_64F
  (InstructionsInternalNamesSet.add FDIV_S_64F
  (InstructionsInternalNamesSet.add FSQRT_S_64F
  (InstructionsInternalNamesSet.add FSGNJ_S_64F
  (InstructionsInternalNamesSet.add FSGNJN_S_64F
  (InstructionsInternalNamesSet.add FSGNJX_S_64F
  (InstructionsInternalNamesSet.add FMIN_S_64F
  (InstructionsInternalNamesSet.add FMAX_S_64F
  (InstructionsInternalNamesSet.add FCVT_W_S_64F
  (InstructionsInternalNamesSet.add FCVT_WU_S_64F
  (InstructionsInternalNamesSet.add FMV_X_W_64F
  (InstructionsInternalNamesSet.add FEQ_S_64F
  (InstructionsInternalNamesSet.add FLT_S_64F
  (InstructionsInternalNamesSet.add FLE_S_64F
  (InstructionsInternalNamesSet.add FCLASS_S_64F
  (InstructionsInternalNamesSet.add FCVT_S_W_64F
  (InstructionsInternalNamesSet.add FCVT_S_WU_64F
  (InstructionsInternalNamesSet.add FMV_W_X_64F
  (InstructionsInternalNamesSet.add FCVT_L_S_64F
  (InstructionsInternalNamesSet.add FCVT_LU_S_64F
  (InstructionsInternalNamesSet.add FCVT_S_L_64F
  (InstructionsInternalNamesSet.add FCVT_S_LU_64F
  InstructionsInternalNamesSet.empty)))))))))))))))))))))))))))))).

Definition RV32D_instruction_internal_names : InstructionsInternalNamesSet.t :=
  (InstructionsInternalNamesSet.add FLD_32D
  (InstructionsInternalNamesSet.add FSD_32D
  (InstructionsInternalNamesSet.add FMADD_D_32D
  (InstructionsInternalNamesSet.add FMSUB_D_32D
  (InstructionsInternalNamesSet.add FNMSUB_D_32D
  (InstructionsInternalNamesSet.add FNMADD_D_32D
  (InstructionsInternalNamesSet.add FADD_D_32D
  (InstructionsInternalNamesSet.add FSUB_D_32D
  (InstructionsInternalNamesSet.add FMUL_D_32D
  (InstructionsInternalNamesSet.add FDIV_D_32D
  (InstructionsInternalNamesSet.add FSQRT_D_32D
  (InstructionsInternalNamesSet.add FSGNJ_D_32D
  (InstructionsInternalNamesSet.add FSGNJN_D_32D
  (InstructionsInternalNamesSet.add FSGNJX_D_32D
  (InstructionsInternalNamesSet.add FMIN_D_32D
  (InstructionsInternalNamesSet.add FMAX_D_32D
  (InstructionsInternalNamesSet.add FCVT_S_D_32D
  (InstructionsInternalNamesSet.add FCVT_D_S_32D
  (InstructionsInternalNamesSet.add FEQ_D_32D
  (InstructionsInternalNamesSet.add FLT_D_32D
  (InstructionsInternalNamesSet.add FLE_D_32D
  (InstructionsInternalNamesSet.add FCLASS_D_32D
  (InstructionsInternalNamesSet.add FCVT_W_D_32D
  (InstructionsInternalNamesSet.add FCVT_WU_D_32D
  (InstructionsInternalNamesSet.add FCVT_D_W_32D
  (InstructionsInternalNamesSet.add FCVT_D_WU_32D
  InstructionsInternalNamesSet.empty)))))))))))))))))))))))))).

Definition RV64D_instruction_internal_names : InstructionsInternalNamesSet.t :=
  (InstructionsInternalNamesSet.add FLD_64D
  (InstructionsInternalNamesSet.add FSD_64D
  (InstructionsInternalNamesSet.add FMADD_D_64D
  (InstructionsInternalNamesSet.add FMSUB_D_64D
  (InstructionsInternalNamesSet.add FNMSUB_D_64D
  (InstructionsInternalNamesSet.add FNMADD_D_64D
  (InstructionsInternalNamesSet.add FADD_D_64D
  (InstructionsInternalNamesSet.add FSUB_D_64D
  (InstructionsInternalNamesSet.add FMUL_D_64D
  (InstructionsInternalNamesSet.add FDIV_D_64D
  (InstructionsInternalNamesSet.add FSQRT_D_64D
  (InstructionsInternalNamesSet.add FSGNJ_D_64D
  (InstructionsInternalNamesSet.add FSGNJN_D_64D
  (InstructionsInternalNamesSet.add FSGNJX_D_64D
  (InstructionsInternalNamesSet.add FMIN_D_64D
  (InstructionsInternalNamesSet.add FMAX_D_64D
  (InstructionsInternalNamesSet.add FCVT_S_D_64D
  (InstructionsInternalNamesSet.add FCVT_D_S_64D
  (InstructionsInternalNamesSet.add FEQ_D_64D
  (InstructionsInternalNamesSet.add FLT_D_64D
  (InstructionsInternalNamesSet.add FLE_D_64D
  (InstructionsInternalNamesSet.add FCLASS_D_64D
  (InstructionsInternalNamesSet.add FCVT_W_D_64D
  (InstructionsInternalNamesSet.add FCVT_WU_D_64D
  (InstructionsInternalNamesSet.add FCVT_D_W_64D
  (InstructionsInternalNamesSet.add FCVT_D_WU_64D
  (InstructionsInternalNamesSet.add FCVT_L_D_64D
  (InstructionsInternalNamesSet.add FCVT_LU_D_64D
  (InstructionsInternalNamesSet.add FMV_X_D_64D
  (InstructionsInternalNamesSet.add FCVT_D_L_64D
  (InstructionsInternalNamesSet.add FCVT_D_LU_64D
  (InstructionsInternalNamesSet.add FMV_D_X_64D
  InstructionsInternalNamesSet.empty)))))))))))))))))))))))))))))))).

Definition RV32Q_instruction_internal_names : InstructionsInternalNamesSet.t :=
  (InstructionsInternalNamesSet.add FLQ_32Q
  (InstructionsInternalNamesSet.add FSQ_32Q
  (InstructionsInternalNamesSet.add FMADD_Q_32Q
  (InstructionsInternalNamesSet.add FMSUB_Q_32Q
  (InstructionsInternalNamesSet.add FNMSUB_Q_32Q
  (InstructionsInternalNamesSet.add FNMADD_Q_32Q
  (InstructionsInternalNamesSet.add FADD_Q_32Q
  (InstructionsInternalNamesSet.add FSUB_Q_32Q
  (InstructionsInternalNamesSet.add FMUL_Q_32Q
  (InstructionsInternalNamesSet.add FDIV_Q_32Q
  (InstructionsInternalNamesSet.add FSQRT_Q_32Q
  (InstructionsInternalNamesSet.add FSGNJ_Q_32Q
  (InstructionsInternalNamesSet.add FSGNJN_Q_32Q
  (InstructionsInternalNamesSet.add FSGNJX_Q_32Q
  (InstructionsInternalNamesSet.add FMIN_Q_32Q
  (InstructionsInternalNamesSet.add FMAX_Q_32Q
  (InstructionsInternalNamesSet.add FCVT_S_Q_32Q
  (InstructionsInternalNamesSet.add FCVT_Q_S_32Q
  (InstructionsInternalNamesSet.add FCVT_D_Q_32Q
  (InstructionsInternalNamesSet.add FCVT_Q_D_32Q
  (InstructionsInternalNamesSet.add FEQ_Q_32Q
  (InstructionsInternalNamesSet.add FLT_Q_32Q
  (InstructionsInternalNamesSet.add FLE_Q_32Q
  (InstructionsInternalNamesSet.add FCLASS_Q_32Q
  (InstructionsInternalNamesSet.add FCVT_W_Q_32Q
  (InstructionsInternalNamesSet.add FCVT_WU_Q_32Q
  (InstructionsInternalNamesSet.add FCVT_Q_W_32Q
  (InstructionsInternalNamesSet.add FCVT_Q_WU_32Q
  InstructionsInternalNamesSet.empty)))))))))))))))))))))))))))).

Definition RV64Q_instruction_internal_names : InstructionsInternalNamesSet.t :=
  (InstructionsInternalNamesSet.add FLQ_64Q
  (InstructionsInternalNamesSet.add FSQ_64Q
  (InstructionsInternalNamesSet.add FMADD_Q_64Q
  (InstructionsInternalNamesSet.add FMSUB_Q_64Q
  (InstructionsInternalNamesSet.add FNMSUB_Q_64Q
  (InstructionsInternalNamesSet.add FNMADD_Q_64Q
  (InstructionsInternalNamesSet.add FADD_Q_64Q
  (InstructionsInternalNamesSet.add FSUB_Q_64Q
  (InstructionsInternalNamesSet.add FMUL_Q_64Q
  (InstructionsInternalNamesSet.add FDIV_Q_64Q
  (InstructionsInternalNamesSet.add FSQRT_Q_64Q
  (InstructionsInternalNamesSet.add FSGNJ_Q_64Q
  (InstructionsInternalNamesSet.add FSGNJN_Q_64Q
  (InstructionsInternalNamesSet.add FSGNJX_Q_64Q
  (InstructionsInternalNamesSet.add FMIN_Q_64Q
  (InstructionsInternalNamesSet.add FMAX_Q_64Q
  (InstructionsInternalNamesSet.add FCVT_S_Q_64Q
  (InstructionsInternalNamesSet.add FCVT_Q_S_64Q
  (InstructionsInternalNamesSet.add FCVT_D_Q_64Q
  (InstructionsInternalNamesSet.add FCVT_Q_D_64Q
  (InstructionsInternalNamesSet.add FEQ_Q_64Q
  (InstructionsInternalNamesSet.add FLT_Q_64Q
  (InstructionsInternalNamesSet.add FLE_Q_64Q
  (InstructionsInternalNamesSet.add FCLASS_Q_64Q
  (InstructionsInternalNamesSet.add FCVT_W_Q_64Q
  (InstructionsInternalNamesSet.add FCVT_WU_Q_64Q
  (InstructionsInternalNamesSet.add FCVT_Q_W_64Q
  (InstructionsInternalNamesSet.add FCVT_Q_WU_64Q
  (InstructionsInternalNamesSet.add FCVT_L_Q_64Q
  (InstructionsInternalNamesSet.add FCVT_LU_Q_64Q
  (InstructionsInternalNamesSet.add FCVT_Q_L_64Q
  (InstructionsInternalNamesSet.add FCVT_Q_LU_64Q
  InstructionsInternalNamesSet.empty)))))))))))))))))))))))))))))))).

Inductive instruction_type_name : Type :=
| RType
| R4Type
| IType
| SType
| BType
| UType
| JType.

Inductive instruction_field_name : Type :=
| opcode
| rd
| rs1
| rs2
| rs3
| funct2
| funct3
| funct7
| immI
| immS_beg
| immS_end
| immB_beg
| immB_end
| immU
| immJ.

Inductive instruction_field_type : Type :=
| identification_field
| data_field.

Definition classify_instruction_field (f : instruction_field_name) :=
  match f with
  | opcode   => identification_field
  | rd       => data_field
  | rs1      => data_field
  | rs2      => data_field
  | rs3      => data_field
  | funct2   => identification_field
  | funct3   => identification_field
  | funct7   => identification_field
  | immI     => data_field
  | immS_beg => data_field
  | immS_end => data_field
  | immB_beg => data_field
  | immB_end => data_field
  | immU     => data_field
  | immJ     => data_field
  end.

Definition field_range (f : instruction_field_name) :=
  match f with
  | opcode   => (0, 6)
  | rd       => (7, 11)
  | rs1      => (15, 19)
  | rs2      => (20, 24)
  | rs3      => (27, 31)
  | funct2   => (25, 26)
  | funct3   => (12, 14)
  | funct7   => (25, 31)
  | immI     => (20, 31)
  | immS_beg => (7, 11)
  | immS_end => (25, 31)
  | immB_beg => (7, 11)
  | immB_end => (25, 31)
  | immU     => (12, 31)
  | immJ     => (12, 31)
  end.

Inductive opcode_name : Type :=
| opcode_OP
| opcode_JALR
| opcode_LOAD
| opcode_OP_IMM
| opcode_MISC_MEM
| opcode_STORE
| opcode_BRANCH
| opcode_LUI
| opcode_AUIPC
| opcode_JAL
| opcode_SYSTEM
| opcode_OP_32
| opcode_OP_IMM_32
| opcode_AMO
| opcode_OP_FP
| opcode_MADD
| opcode_MSUB
| opcode_NMSUB
| opcode_NMADD
| opcode_LOAD_FP
| opcode_STORE_FP.

(* Definition opcode_OP        := Ob~0~1~1~0~0~1~1. *)
(* Definition opcode_JALR      := Ob~1~1~0~0~1~1~1. *)
(* Definition opcode_LOAD      := Ob~0~0~0~0~0~1~1. *)
(* Definition opcode_OP_IMM    := Ob~0~0~1~0~0~1~1. *)
(* Definition opcode_MISC_MEM  := Ob~0~0~0~1~1~1~1. *)
(* Definition opcode_STORE     := Ob~0~1~0~0~0~1~1. *)
(* Definition opcode_BRANCH    := Ob~1~1~0~0~0~1~1. *)
(* Definition opcode_LUI       := Ob~0~1~1~0~1~1~1. *)
(* Definition opcode_AUIPC     := Ob~0~0~1~0~1~1~1. *)
(* Definition opcode_JAL       := Ob~1~1~0~1~1~1~1. *)
(* Definition opcode_SYSTEM    := Ob~1~1~1~0~0~1~1. *)
(* Definition opcode_OP_32     := Ob~0~1~1~1~0~1~1. *)
(* Definition opcode_OP_IMM_32 := Ob~0~0~1~1~0~1~1. *)
(* Definition opcode_AMO       := Ob~0~1~0~1~1~1~1. *)
(* Definition opcode_OP_FP     := Ob~1~0~1~0~0~1~1. *)
(* Definition opcode_MADD      := Ob~1~0~0~0~0~1~1. *)
(* Definition opcode_MSUB      := Ob~1~0~0~0~1~1~1. *)
(* Definition opcode_NMSUB     := Ob~1~0~0~1~0~1~1. *)
(* Definition opcode_NMADD     := Ob~1~0~0~1~1~1~1. *)
(* Definition opcode_LOAD_FP   := Ob~0~0~0~0~1~1~1. *)
(* Definition opcode_STORE_FP  := Ob~0~1~0~0~1~1~1. *)

(* Definition funct3_ADD      := Ob~0~0~0. *)
(* Definition funct3_SUB      := Ob~0~0~0. *)
(* Definition funct3_SLL      := Ob~0~0~1. *)
(* Definition funct3_SLT      := Ob~0~1~0. *)
(* Definition funct3_SLTU     := Ob~0~1~1. *)
(* Definition funct3_XOR      := Ob~1~0~0. *)
(* Definition funct3_SRL      := Ob~1~0~1. *)
(* Definition funct3_SRA      := Ob~1~0~1. *)
(* Definition funct3_OR       := Ob~1~1~0. *)
(* Definition funct3_AND      := Ob~1~1~1. *)
(* Definition funct3_LB       := Ob~0~0~0. *)
(* Definition funct3_LH       := Ob~0~0~1. *)
(* Definition funct3_LW       := Ob~0~1~0. *)
(* Definition funct3_LBU      := Ob~1~0~0. *)
(* Definition funct3_LHU      := Ob~1~0~1. *)
(* Definition funct3_SLTI     := Ob~0~1~0. *)
(* Definition funct3_SLTIU    := Ob~0~1~1. *)
(* Definition funct3_ADDI     := Ob~0~0~0. *)
(* Definition funct3_XORI     := Ob~1~0~0. *)
(* Definition funct3_ORI      := Ob~1~1~0. *)
(* Definition funct3_ANDI     := Ob~1~1~1. *)
(* Definition funct3_SLLI     := Ob~0~0~1. *)
(* Definition funct3_SRLI     := Ob~1~0~1. *)
(* Definition funct3_SRAI     := Ob~1~0~1. *)
(* Definition funct3_FENCE    := Ob~0~0~0. *)
(* Definition funct3_SB       := Ob~0~0~0. *)
(* Definition funct3_SH       := Ob~0~0~1. *)
(* Definition funct3_SW       := Ob~0~1~0. *)
(* Definition funct3_BEQ      := Ob~0~0~0. *)
(* Definition funct3_BNE      := Ob~0~0~1. *)
(* Definition funct3_BLT      := Ob~1~0~0. *)
(* Definition funct3_BGE      := Ob~1~0~1. *)
(* Definition funct3_BLTU     := Ob~1~1~0. *)
(* Definition funct3_BGEU     := Ob~1~1~1. *)
(* Definition funct3_PRIV     := Ob~0~0~0. *)
(* Definition funct3_ADDW     := Ob~0~0~0. *)
(* Definition funct3_SUBW     := Ob~0~0~0. *)
(* Definition funct3_SLLW     := Ob~0~0~1. *)
(* Definition funct3_SRLW     := Ob~1~0~1. *)
(* Definition funct3_SRAW     := Ob~1~0~1. *)
(* Definition funct3_LWU      := Ob~1~1~0. *)
(* Definition funct3_LD       := Ob~0~1~1. *)
(* Definition funct3_ADDIW    := Ob~0~0~0. *)
(* Definition funct3_SLLIW    := Ob~0~0~1. *)
(* Definition funct3_SRLIW    := Ob~1~0~1. *)
(* Definition funct3_SRAIW    := Ob~1~0~1. *)
(* Definition funct3_SD       := Ob~0~1~1. *)
(* Definition funct3_FENCE_I  := Ob~0~0~1. *)
(* Definition funct3_CSRRW    := Ob~0~0~1. *)
(* Definition funct3_CSRRS    := Ob~0~1~0. *)
(* Definition funct3_CSRRC    := Ob~0~1~1. *)
(* Definition funct3_CSRRWI   := Ob~1~0~1. *)
(* Definition funct3_CSRRSI   := Ob~1~1~0. *)
(* Definition funct3_CSRRCI   := Ob~1~1~1. *)
(* Definition funct3_MUL      := Ob~0~0~0. *)
(* Definition funct3_MULH     := Ob~0~0~1. *)
(* Definition funct3_MULHSU   := Ob~0~1~0. *)
(* Definition funct3_MULHU    := Ob~0~1~1. *)
(* Definition funct3_DIV      := Ob~1~0~0. *)
(* Definition funct3_DIVU     := Ob~1~0~1. *)
(* Definition funct3_REM      := Ob~1~1~0. *)
(* Definition funct3_REMU     := Ob~1~1~1. *)
(* Definition funct3_MULW     := Ob~0~0~0. *)
(* Definition funct3_DIVW     := Ob~1~0~0. *)
(* Definition funct3_DIVUW    := Ob~1~0~1. *)
(* Definition funct3_REMW     := Ob~1~1~0. *)
(* Definition funct3_REMUW    := Ob~1~1~1. *)
(* Definition funct3_AMOW     := Ob~0~1~0. *)
(* Definition funct3_AMOD     := Ob~0~1~1. *)
(* Definition funct3_FSGNJ_S  := Ob~0~0~0. *)
(* Definition funct3_FSGNJN_S := Ob~0~0~1. *)
(* Definition funct3_FSGNJX_S := Ob~0~1~0. *)
(* Definition funct3_FMIN_S   := Ob~0~0~0. *)
(* Definition funct3_FMAX_S   := Ob~0~0~1. *)
(* Definition funct3_FMV_X_W  := Ob~0~0~0. *)
(* Definition funct3_FEQ_S    := Ob~0~1~0. *)
(* Definition funct3_FLT_S    := Ob~0~0~1. *)
(* Definition funct3_FLE_S    := Ob~0~0~0. *)
(* Definition funct3_FCLASS_S := Ob~0~0~1. *)
(* Definition funct3_FLW      := Ob~0~1~0. *)
(* Definition funct3_FSW      := Ob~0~1~0. *)

(* Definition funct7_ADD        := Ob~0~0~0~0~0~0~0. *)
(* Definition funct7_SUB        := Ob~0~1~0~0~0~0~0. *)
(* Definition funct7_SLL        := Ob~0~0~0~0~0~0~0. *)
(* Definition funct7_SLT        := Ob~0~0~0~0~0~0~0. *)
(* Definition funct7_SLTU       := Ob~0~0~0~0~0~0~0. *)
(* Definition funct7_XOR        := Ob~0~0~0~0~0~0~0. *)
(* Definition funct7_SRL        := Ob~0~0~0~0~0~0~0. *)
(* Definition funct7_SRA        := Ob~0~1~0~0~0~0~0. *)
(* Definition funct7_OR         := Ob~0~0~0~0~0~0~0. *)
(* Definition funct7_AND        := Ob~0~0~0~0~0~0~0. *)
(* Definition funct7_ADDW       := Ob~0~0~0~0~0~0~0. *)
(* Definition funct7_SUBW       := Ob~0~1~0~0~0~0~0. *)
(* Definition funct7_SLLW       := Ob~0~0~0~0~0~0~0. *)
(* Definition funct7_SRLW       := Ob~0~0~0~0~0~0~0. *)
(* Definition funct7_SRAW       := Ob~0~1~0~0~0~0~0. *)
(* Definition funct7_SLLIW      := Ob~0~0~0~0~0~0~0. *)
(* Definition funct7_SRLIW      := Ob~0~0~0~0~0~0~0. *)
(* Definition funct7_SRAIW      := Ob~0~1~0~0~0~0~0. *)
(* Definition funct7_MUL        := Ob~0~0~0~0~0~0~1. *)
(* Definition funct7_MULH       := Ob~0~0~0~0~0~0~1. *)
(* Definition funct7_MULHSU     := Ob~0~0~0~0~0~0~1. *)
(* Definition funct7_MULHU      := Ob~0~0~0~0~0~0~1. *)
(* Definition funct7_DIV        := Ob~0~0~0~0~0~0~1. *)
(* Definition funct7_DIVU       := Ob~0~0~0~0~0~0~1. *)
(* Definition funct7_REM        := Ob~0~0~0~0~0~0~1. *)
(* Definition funct7_REMU       := Ob~0~0~0~0~0~0~1. *)
(* Definition funct7_MULW       := Ob~0~0~0~0~0~0~1. *)
(* Definition funct7_DIVW       := Ob~0~0~0~0~0~0~1. *)
(* Definition funct7_DIVUW      := Ob~0~0~0~0~0~0~1. *)
(* Definition funct7_REMW       := Ob~0~0~0~0~0~0~1. *)
(* Definition funct7_REMUW      := Ob~0~0~0~0~0~0~1. *)
(* Definition funct7_FADD_S     := Ob~0~0~0~0~0~0~0. *)
(* Definition funct7_FSUB_S     := Ob~0~0~0~0~1~0~0. *)
(* Definition funct7_FMUL_S     := Ob~0~0~0~1~0~0~0. *)
(* Definition funct7_FDIV_S     := Ob~0~0~0~1~1~0~0. *)
(* Definition funct7_FSQRT_S    := Ob~0~1~0~1~1~0~0. *)
(* Definition funct7_FSGNJ_S    := Ob~0~0~1~0~0~0~0. *)
(* Definition funct7_FMIN_S     := Ob~0~0~1~0~1~0~0. *)
(* Definition funct7_FCVT_W_S   := Ob~1~1~0~0~0~0~0. *)
(* Definition funct7_FMV_X_W    := Ob~1~1~1~0~0~0~0. *)
(* Definition funct7_FEQ_S      := Ob~1~0~1~0~0~0~0. *)
(* Definition funct7_FCLASS_S   := Ob~1~1~1~0~0~0~0. *)
(* Definition funct7_FCVT_S_W   := Ob~1~1~0~1~0~0~0. *)
(* Definition funct7_FMV_W_X    := Ob~1~1~1~1~0~0~0. *)
(* Definition funct7_SFENCE_VMA := Ob~0~0~0~1~0~0~1. *)

(* Scheme Equality for instruction_field_name. *)

(* Module DecidableInstructionField <: DecidableType. *)
(*   Definition t := instruction_field_name. *)
(*   Definition eq := @eq instruction_field_name. *)
(*   Instance eq_equiv : @Equivalence instruction_field_name eq := eq_equivalence. *)
(*   Definition eq_dec := instruction_field_name_eq_dec. *)
(* End DecidableInstructionField. *)

(* Module FieldsSet <: WSetsOn DecidableInstructionField. *)
  Include WSetsOn DecidableInstructionField.
End FieldsSet.

Definition instruction_type_fields (t : instruction_type_name) :=
  match t with
  | RType =>
    (FieldsSet.add opcode
    (FieldsSet.add rd
    (FieldsSet.add funct3
    (FieldsSet.add rs1
    (FieldsSet.add rs2
    (FieldsSet.add funct7
    FieldsSet.empty
    ))))))
  | R4Type =>
    (FieldsSet.add opcode
    (FieldsSet.add rd
    (FieldsSet.add funct3
    (FieldsSet.add rs1
    (FieldsSet.add rs2
    (FieldsSet.add funct2
    (FieldsSet.add rs3
    FieldsSet.empty
    )))))))
  | IType =>
    (FieldsSet.add opcode
    (FieldsSet.add rd
    (FieldsSet.add funct3
    (FieldsSet.add rs1
    (FieldsSet.add immI
    FieldsSet.empty
    )))))
  | SType =>
    (FieldsSet.add opcode
    (FieldsSet.add immS_beg
    (FieldsSet.add funct3
    (FieldsSet.add rs1
    (FieldsSet.add rs2
    (FieldsSet.add immS_end
    FieldsSet.empty
    ))))))
  | BType =>
    (FieldsSet.add opcode
    (FieldsSet.add immB_beg
    (FieldsSet.add funct3
    (FieldsSet.add rs1
    (FieldsSet.add rs2
    (FieldsSet.add immB_end
    FieldsSet.empty
    ))))))
  | UType =>
    (FieldsSet.add opcode
    (FieldsSet.add rd
    (FieldsSet.add immU
    FieldsSet.empty
    )))
  | JType =>
    (FieldsSet.add opcode
    (FieldsSet.add rd
    (FieldsSet.add immJ
    FieldsSet.empty
    )))
  end.

Definition opcode := bits_t 7.

Definition bin_instruction := bits_t 32.

Definition instruction_type (i : instruction_internal_name) :=
  match i with
  (* RV32I *)
  | LUI_32I    => UType
  | AUIPC_32I  => UType
  | JAL_32I    => JType
  | JALR_32I   => IType
  | BEQ_32I    => BType
  | BNE_32I    => BType
  | BLT_32I    => BType
  | BGE_32I    => BType
  | BLTU_32I   => BType
  | BGEU_32I   => BType
  | LB_32I     => IType
  | LH_32I     => IType
  | LW_32I     => IType
  | LBU_32I    => IType
  | LHU_32I    => IType
  | SB_32I     => SType
  | SH_32I     => SType
  | SW_32I     => SType
  | ADDI_32I   => IType
  | SLTI_32I   => IType
  | SLTIU_32I  => IType
  | XORI_32I   => IType
  | ORI_32I    => IType
  | ANDI_32I   => IType
  | SLLI_32I   => IType
  | SRLI_32I   => IType
  | SRAI_32I   => IType
  | ADD_32I    => RType
  | SUB_32I    => RType
  | SLL_32I    => RType
  | SLT_32I    => RType
  | SLTU_32I   => RType
  | XOR_32I    => RType
  | SRL_32I    => RType
  | SRA_32I    => RType
  | OR_32I     => RType
  | AND_32I    => RType
  | FENCE_32I  => IType
  | ECALL_32I  => IType
  | EBREAK_32I => IType
  (* RV64I *)
  | LUI_64I    => UType
  | AUIPC_64I  => UType
  | JAL_64I    => JType
  | JALR_64I   => IType
  | BEQ_64I    => BType
  | BNE_64I    => BType
  | BLT_64I    => BType
  | BGE_64I    => BType
  | BLTU_64I   => BType
  | BGEU_64I   => BType
  | LB_64I     => IType
  | LH_64I     => IType
  | LW_64I     => IType
  | LBU_64I    => IType
  | LHU_64I    => IType
  | SB_64I     => SType
  | SH_64I     => SType
  | SW_64I     => SType
  | ADDI_64I   => IType
  | SLTI_64I   => IType
  | SLTIU_64I  => IType
  | XORI_64I   => IType
  | ORI_64I    => IType
  | ANDI_64I   => IType
  | SLLI_64I   => IType
  | SRLI_64I   => IType
  | SRAI_64I   => IType
  | ADD_64I    => RType
  | SUB_64I    => RType
  | SLL_64I    => RType
  | SLT_64I    => RType
  | SLTU_64I   => RType
  | XOR_64I    => RType
  | SRL_64I    => RType
  | SRA_64I    => RType
  | OR_64I     => RType
  | AND_64I    => RType
  | FENCE_64I  => IType
  | ECALL_64I  => IType
  | EBREAK_64I => IType
  | LWU_64I    => IType
  | LD_64I     => IType
  | SD_64I     => SType
  | ADDIW_64I  => IType
  | SLLIW_64I  => IType
  | SRLIW_64I  => IType
  | SRAIW_64I  => IType
  | ADDW_64I   => RType
  | SUBW_64I   => RType
  | SLLW_64I   => RType
  | SRLW_64I   => RType
  | SRAW_64I   => RType
  (* RV32Zifencei *)
  | FENCE_I_32Zifencei => IType
  (* RV64Zifencei *)
  | FENCE_I_64Zifencei => IType
  (* RV32Zicsr *)
  | CSRRW_32Zicsr  => IType
  | CSRRS_32Zicsr  => IType
  | CSRRC_32Zicsr  => IType
  | CSRRWI_32Zicsr => IType
  | CSRRSI_32Zicsr => IType
  | CSRRCI_32Zicsr => IType
  (* RV64Zicsr *)
  | CSRRW_64Zicsr  => IType
  | CSRRS_64Zicsr  => IType
  | CSRRC_64Zicsr  => IType
  | CSRRWI_64Zicsr => IType
  | CSRRSI_64Zicsr => IType
  | CSRRCI_64Zicsr => IType
  (* RV32M *)
  | MUL_32M    => RType
  | MULH_32M   => RType
  | MULHSU_32M => RType
  | MULHU_32M  => RType
  | DIV_32M    => RType
  | DIVU_32M   => RType
  | REM_32M    => RType
  | REMU_32M   => RType
  (* RV64M *)
  | MUL_64M    => RType
  | MULH_64M   => RType
  | MULHSU_64M => RType
  | MULHU_64M  => RType
  | DIV_64M    => RType
  | DIVU_64M   => RType
  | REM_64M    => RType
  | REMU_64M   => RType
  | MULW_64M   => RType
  | DIVW_64M   => RType
  | DIVUW_64M  => RType
  | REMW_64M   => RType
  | REMUW_64M  => RType
  (* RV32A *)
  | LR_W_32A      => RType
  | SC_W_32A      => RType
  | AMOSWAP_W_32A => RType
  | AMOADD_W_32A  => RType
  | AMOXOR_W_32A  => RType
  | AMOAND_W_32A  => RType
  | AMOOR_W_32A   => RType
  | AMOMIN_W_32A  => RType
  | AMOMAX_W_32A  => RType
  | AMOMINU_W_32A => RType
  | AMOMAXU_W_32A => RType
  (* RV64A *)
  | LR_W_64A      => RType
  | SC_W_64A      => RType
  | AMOSWAP_W_64A => RType
  | AMOADD_W_64A  => RType
  | AMOXOR_W_64A  => RType
  | AMOAND_W_64A  => RType
  | AMOOR_W_64A   => RType
  | AMOMIN_W_64A  => RType
  | AMOMAX_W_64A  => RType
  | AMOMINU_W_64A => RType
  | AMOMAXU_W_64A => RType
  | LR_D_64A      => RType
  | SC_D_64A      => RType
  | AMOSWAP_D_64A => RType
  | AMOADD_D_64A  => RType
  | AMOXOR_D_64A  => RType
  | AMOAND_D_64A  => RType
  | AMOOR_D_64A   => RType
  | AMOMIN_D_64A  => RType
  | AMOMAX_D_64A  => RType
  | AMOMINU_D_64A => RType
  | AMOMAXU_D_64A => RType
  (* RV32F *)
  | FLW_32F       => IType
  | FSW_32F       => SType
  | FMADD_S_32F   => R4Type
  | FMSUB_S_32F   => R4Type
  | FNMSUB_S_32F  => R4Type
  | FNMADD_S_32F  => R4Type
  | FADD_S_32F    => RType
  | FSUB_S_32F    => RType
  | FMUL_S_32F    => RType
  | FDIV_S_32F    => RType
  | FSQRT_S_32F   => RType
  | FSGNJ_S_32F   => RType
  | FSGNJN_S_32F  => RType
  | FSGNJX_S_32F  => RType
  | FMIN_S_32F    => RType
  | FMAX_S_32F    => RType
  | FCVT_W_S_32F  => RType
  | FCVT_WU_S_32F => RType
  | FMV_X_W_32F   => RType
  | FEQ_S_32F     => RType
  | FLT_S_32F     => RType
  | FLE_S_32F     => RType
  | FCLASS_S_32F  => RType
  | FCVT_S_W_32F  => RType
  | FCVT_S_WU_32F => RType
  | FMV_W_X_32F   => RType
  (* RV64F *)
  | FLW_64F       => IType
  | FSW_64F       => SType
  | FMADD_S_64F   => R4Type
  | FMSUB_S_64F   => R4Type
  | FNMSUB_S_64F  => R4Type
  | FNMADD_S_64F  => R4Type
  | FADD_S_64F    => RType
  | FSUB_S_64F    => RType
  | FMUL_S_64F    => RType
  | FDIV_S_64F    => RType
  | FSQRT_S_64F   => RType
  | FSGNJ_S_64F   => RType
  | FSGNJN_S_64F  => RType
  | FSGNJX_S_64F  => RType
  | FMIN_S_64F    => RType
  | FMAX_S_64F    => RType
  | FCVT_W_S_64F  => RType
  | FCVT_WU_S_64F => RType
  | FMV_X_W_64F   => RType
  | FEQ_S_64F     => RType
  | FLT_S_64F     => RType
  | FLE_S_64F     => RType
  | FCLASS_S_64F  => RType
  | FCVT_S_W_64F  => RType
  | FCVT_S_WU_64F => RType
  | FMV_W_X_64F   => RType
  | FCVT_L_S_64F  => RType
  | FCVT_LU_S_64F => RType
  | FCVT_S_L_64F  => RType
  | FCVT_S_LU_64F => RType
  (* RV32D *)
  | FLD_32D       => IType
  | FSD_32D       => SType
  | FMADD_D_32D   => R4Type
  | FMSUB_D_32D   => R4Type
  | FNMSUB_D_32D  => R4Type
  | FNMADD_D_32D  => R4Type
  | FADD_D_32D    => RType
  | FSUB_D_32D    => RType
  | FMUL_D_32D    => RType
  | FDIV_D_32D    => RType
  | FSQRT_D_32D   => RType
  | FSGNJ_D_32D   => RType
  | FSGNJN_D_32D  => RType
  | FSGNJX_D_32D  => RType
  | FMIN_D_32D    => RType
  | FMAX_D_32D    => RType
  | FCVT_S_D_32D  => RType
  | FCVT_D_S_32D  => RType
  | FEQ_D_32D     => RType
  | FLT_D_32D     => RType
  | FLE_D_32D     => RType
  | FCLASS_D_32D  => RType
  | FCVT_W_D_32D  => RType
  | FCVT_WU_D_32D => RType
  | FCVT_D_W_32D  => RType
  | FCVT_D_WU_32D => RType
  (* RV64D *)
  | FLD_64D       => IType
  | FSD_64D       => SType
  | FMADD_D_64D   => R4Type
  | FMSUB_D_64D   => R4Type
  | FNMSUB_D_64D  => R4Type
  | FNMADD_D_64D  => R4Type
  | FADD_D_64D    => RType
  | FSUB_D_64D    => RType
  | FMUL_D_64D    => RType
  | FDIV_D_64D    => RType
  | FSQRT_D_64D   => RType
  | FSGNJ_D_64D   => RType
  | FSGNJN_D_64D  => RType
  | FSGNJX_D_64D  => RType
  | FMIN_D_64D    => RType
  | FMAX_D_64D    => RType
  | FCVT_S_D_64D  => RType
  | FCVT_D_S_64D  => RType
  | FEQ_D_64D     => RType
  | FLT_D_64D     => RType
  | FLE_D_64D     => RType
  | FCLASS_D_64D  => RType
  | FCVT_W_D_64D  => RType
  | FCVT_WU_D_64D => RType
  | FCVT_D_W_64D  => RType
  | FCVT_D_WU_64D => RType
  | FCVT_L_D_64D  => RType
  | FCVT_LU_D_64D => RType
  | FMV_X_D_64D   => RType
  | FCVT_D_L_64D  => RType
  | FCVT_D_LU_64D => RType
  | FMV_D_X_64D   => RType
  (* RV32Q *)
  | FLQ_32Q       => IType
  | FSQ_32Q       => SType
  | FMADD_Q_32Q   => R4Type
  | FMSUB_Q_32Q   => R4Type
  | FNMSUB_Q_32Q  => R4Type
  | FNMADD_Q_32Q  => R4Type
  | FADD_Q_32Q    => RType
  | FSUB_Q_32Q    => RType
  | FMUL_Q_32Q    => RType
  | FDIV_Q_32Q    => RType
  | FSQRT_Q_32Q   => RType
  | FSGNJ_Q_32Q   => RType
  | FSGNJN_Q_32Q  => RType
  | FSGNJX_Q_32Q  => RType
  | FMIN_Q_32Q    => RType
  | FMAX_Q_32Q    => RType
  | FCVT_S_Q_32Q  => RType
  | FCVT_Q_S_32Q  => RType
  | FCVT_D_Q_32Q  => RType
  | FCVT_Q_D_32Q  => RType
  | FEQ_Q_32Q     => RType
  | FLT_Q_32Q     => RType
  | FLE_Q_32Q     => RType
  | FCLASS_Q_32Q  => RType
  | FCVT_W_Q_32Q  => RType
  | FCVT_WU_Q_32Q => RType
  | FCVT_Q_W_32Q  => RType
  | FCVT_Q_WU_32Q => RType
  (* RV64Q *)
  | FLQ_64Q       => IType
  | FSQ_64Q       => SType
  | FMADD_Q_64Q   => R4Type
  | FMSUB_Q_64Q   => R4Type
  | FNMSUB_Q_64Q  => R4Type
  | FNMADD_Q_64Q  => R4Type
  | FADD_Q_64Q    => RType
  | FSUB_Q_64Q    => RType
  | FMUL_Q_64Q    => RType
  | FDIV_Q_64Q    => RType
  | FSQRT_Q_64Q   => RType
  | FSGNJ_Q_64Q   => RType
  | FSGNJN_Q_64Q  => RType
  | FSGNJX_Q_64Q  => RType
  | FMIN_Q_64Q    => RType
  | FMAX_Q_64Q    => RType
  | FCVT_S_Q_64Q  => RType
  | FCVT_Q_S_64Q  => RType
  | FCVT_D_Q_64Q  => RType
  | FCVT_Q_D_64Q  => RType
  | FEQ_Q_64Q     => RType
  | FLT_Q_64Q     => RType
  | FLE_Q_64Q     => RType
  | FCLASS_Q_64Q  => RType
  | FCVT_W_Q_64Q  => RType
  | FCVT_WU_Q_64Q => RType
  | FCVT_Q_W_64Q  => RType
  | FCVT_Q_WU_64Q => RType
  | FCVT_L_Q_64Q  => RType
  | FCVT_LU_Q_64Q => RType
  | FCVT_Q_L_64Q  => RType
  | FCVT_Q_LU_64Q => RType
  end.

Definition instruction_name (i : instruction_internal_name) :=
  match i with
  (* RV32I *)
  | LUI_32I    => "LUI"
  | AUIPC_32I  => "AUIPC"
  | JAL_32I    => "JAL"
  | JALR_32I   => "JALR"
  | BEQ_32I    => "BEQ"
  | BNE_32I    => "BNE"
  | BLT_32I    => "BLT"
  | BGE_32I    => "BGE"
  | BLTU_32I   => "BLTU"
  | BGEU_32I   => "BGEU"
  | LB_32I     => "LB"
  | LH_32I     => "LH"
  | LW_32I     => "LW"
  | LBU_32I    => "LBU"
  | LHU_32I    => "LHU"
  | SB_32I     => "SB"
  | SH_32I     => "SH"
  | SW_32I     => "SW"
  | ADDI_32I   => "ADDI"
  | SLTI_32I   => "SLTI"
  | SLTIU_32I  => "SLTIU"
  | XORI_32I   => "XORI"
  | ORI_32I    => "ORI"
  | ANDI_32I   => "ANDI"
  | SLLI_32I   => "SLLI"
  | SRLI_32I   => "SRLI"
  | SRAI_32I   => "SRAI"
  | ADD_32I    => "ADD"
  | SUB_32I    => "SUB"
  | SLL_32I    => "SLL"
  | SLT_32I    => "SLT"
  | SLTU_32I   => "SLTU"
  | XOR_32I    => "XOR"
  | SRL_32I    => "SRL"
  | SRA_32I    => "SRA"
  | OR_32I     => "OR"
  | AND_32I    => "AND"
  | FENCE_32I  => "FENCE"
  | ECALL_32I  => "ECALL"
  | EBREAK_32I => "EBREAK"
  (* RV64I *)
  | LUI_64I    => "LUI"
  | AUIPC_64I  => "AUIPC"
  | JAL_64I    => "JAL"
  | JALR_64I   => "JALR"
  | BEQ_64I    => "BEQ"
  | BNE_64I    => "BNE"
  | BLT_64I    => "BLT"
  | BGE_64I    => "BGE"
  | BLTU_64I   => "BLTU"
  | BGEU_64I   => "BGEU"
  | LB_64I     => "LB"
  | LH_64I     => "LH"
  | LW_64I     => "LW"
  | LBU_64I    => "LBU"
  | LHU_64I    => "LHU"
  | SB_64I     => "SB"
  | SH_64I     => "SH"
  | SW_64I     => "SW"
  | ADDI_64I   => "ADDI"
  | SLTI_64I   => "SLTI"
  | SLTIU_64I  => "SLTIU"
  | XORI_64I   => "XORI"
  | ORI_64I    => "ORI"
  | ANDI_64I   => "ANDI"
  | SLLI_64I   => "SLLI"
  | SRLI_64I   => "SRLI"
  | SRAI_64I   => "SRAI"
  | ADD_64I    => "ADD"
  | SUB_64I    => "SUB"
  | SLL_64I    => "SLL"
  | SLT_64I    => "SLT"
  | SLTU_64I   => "SLTU"
  | XOR_64I    => "XOR"
  | SRL_64I    => "SRL"
  | SRA_64I    => "SRA"
  | OR_64I     => "OR"
  | AND_64I    => "AND"
  | FENCE_64I  => "FENCE"
  | ECALL_64I  => "ECALL"
  | EBREAK_64I => "EBREAK"
  | LWU_64I    => "LWU"
  | LD_64I     => "LD"
  | SD_64I     => "SD"
  | ADDIW_64I  => "ADDIW"
  | SLLIW_64I  => "SLLIW"
  | SRLIW_64I  => "SRLIW"
  | SRAIW_64I  => "SRAIW"
  | ADDW_64I   => "ADDW"
  | SUBW_64I   => "SUBW"
  | SLLW_64I   => "SLLW"
  | SRLW_64I   => "SRLW"
  | SRAW_64I   => "SRAW"
  (* RV32Zifencei *)
  | FENCE_I_32Zifencei => "FENCE.I"
  (* RV64Zifencei *)
  | FENCE_I_64Zifencei => "FENCE.I"
  (* RV32Zicsr *)
  | CSRRW_32Zicsr  => "CSRRW"
  | CSRRS_32Zicsr  => "CSRRS"
  | CSRRC_32Zicsr  => "CSRRC"
  | CSRRWI_32Zicsr => "CSRRWI"
  | CSRRSI_32Zicsr => "CSRRSI"
  | CSRRCI_32Zicsr => "CSRRCI"
  (* RV64Zicsr *)
  | CSRRW_64Zicsr  => "CSRRW"
  | CSRRS_64Zicsr  => "CSRRS"
  | CSRRC_64Zicsr  => "CSRRC"
  | CSRRWI_64Zicsr => "CSRRWI"
  | CSRRSI_64Zicsr => "CSRRSI"
  | CSRRCI_64Zicsr => "CSRRCI"
  (* RV32M *)
  | MUL_32M    => "MUL"
  | MULH_32M   => "MULH"
  | MULHSU_32M => "MULHSU"
  | MULHU_32M  => "MULHU"
  | DIV_32M    => "DIV"
  | DIVU_32M   => "DIVU"
  | REM_32M    => "REM"
  | REMU_32M   => "REMU"
  (* RV64M *)
  | MUL_64M    => "MUL"
  | MULH_64M   => "MULH"
  | MULHSU_64M => "MULHSU"
  | MULHU_64M  => "MULHU"
  | DIV_64M    => "DIV"
  | DIVU_64M   => "DIVU"
  | REM_64M    => "REM"
  | REMU_64M   => "REMU"
  | MULW_64M   => "MULW"
  | DIVW_64M   => "DIVW"
  | DIVUW_64M  => "DIVUW"
  | REMW_64M   => "REMW"
  | REMUW_64M  => "REMUW"
  (* RV32A *)
  | LR_W_32A      => "LR.W"
  | SC_W_32A      => "SC.W"
  | AMOSWAP_W_32A => "AMOSWAP.W"
  | AMOADD_W_32A  => "AMOADD.W"
  | AMOXOR_W_32A  => "AMOXOR.W"
  | AMOAND_W_32A  => "AMOAND.W"
  | AMOOR_W_32A   => "AMOOR.W"
  | AMOMIN_W_32A  => "AMOMIN.W"
  | AMOMAX_W_32A  => "AMOMAX.W"
  | AMOMINU_W_32A => "AMOMINU.W"
  | AMOMAXU_W_32A => "AMOMAXU.W"
  (* RV64A *)
  | LR_W_64A      => "LR.W"
  | SC_W_64A      => "SC.W"
  | AMOSWAP_W_64A => "AMOSWAP.W"
  | AMOADD_W_64A  => "AMOADD.W"
  | AMOXOR_W_64A  => "AMOXOR.W"
  | AMOAND_W_64A  => "AMOAND.W"
  | AMOOR_W_64A   => "AMOOR.W"
  | AMOMIN_W_64A  => "AMOMIN.W"
  | AMOMAX_W_64A  => "AMOMAX.W"
  | AMOMINU_W_64A => "AMOMINU.W"
  | AMOMAXU_W_64A => "AMOMAXU.W"
  | LR_D_64A      => "LR.D"
  | SC_D_64A      => "SC.D"
  | AMOSWAP_D_64A => "AMOSWAP.D"
  | AMOADD_D_64A  => "AMOADD.D"
  | AMOXOR_D_64A  => "AMOXOR.D"
  | AMOAND_D_64A  => "AMOAND.D"
  | AMOOR_D_64A   => "AMOOR.D"
  | AMOMIN_D_64A  => "AMOMIN.D"
  | AMOMAX_D_64A  => "AMOMAX.D"
  | AMOMINU_D_64A => "AMOMINU.D"
  | AMOMAXU_D_64A => "AMOMAXU.D"
  (* RV32F *)
  | FLW_32F       => "FLW"
  | FSW_32F       => "FSW"
  | FMADD_S_32F   => "FMADD.S"
  | FMSUB_S_32F   => "FMSUB.S"
  | FNMSUB_S_32F  => "FNMSUB.S"
  | FNMADD_S_32F  => "FNMADD.S"
  | FADD_S_32F    => "FADD.S"
  | FSUB_S_32F    => "FSUB.S"
  | FMUL_S_32F    => "FMUL.S"
  | FDIV_S_32F    => "FDIV.S"
  | FSQRT_S_32F   => "FSQRT.S"
  | FSGNJ_S_32F   => "FSGNJ.S"
  | FSGNJN_S_32F  => "FSGNJN.S"
  | FSGNJX_S_32F  => "FSGNJX.S"
  | FMIN_S_32F    => "FMIN.S"
  | FMAX_S_32F    => "FMAX.S"
  | FCVT_W_S_32F  => "FCVT.W.S"
  | FCVT_WU_S_32F => "FCVT.WU.S"
  | FMV_X_W_32F   => "FMV.X.W"
  | FEQ_S_32F     => "FEQ.S"
  | FLT_S_32F     => "FLT.S"
  | FLE_S_32F     => "FLE.S"
  | FCLASS_S_32F  => "FCLASS.S"
  | FCVT_S_W_32F  => "FCVT.S.W"
  | FCVT_S_WU_32F => "FCVT.S.WU"
  | FMV_W_X_32F   => "FMV.W.X"
  (* RV64F *)
  | FLW_64F       => "FLW"
  | FSW_64F       => "FSW"
  | FMADD_S_64F   => "FMADD.S"
  | FMSUB_S_64F   => "FMSUB.S"
  | FNMSUB_S_64F  => "FNMSUB.S"
  | FNMADD_S_64F  => "FNMADD.S"
  | FADD_S_64F    => "FADD.S"
  | FSUB_S_64F    => "FSUB.S"
  | FMUL_S_64F    => "FMUL.S"
  | FDIV_S_64F    => "FDIV.S"
  | FSQRT_S_64F   => "FSQRT.S"
  | FSGNJ_S_64F   => "FSGNJ.S"
  | FSGNJN_S_64F  => "FSGNJN.S"
  | FSGNJX_S_64F  => "FSGNJX.S"
  | FMIN_S_64F    => "FMIN.S"
  | FMAX_S_64F    => "FMAX.S"
  | FCVT_W_S_64F  => "FCVT.W.S"
  | FCVT_WU_S_64F => "FCVT.WU.S"
  | FMV_X_W_64F   => "FMV.X.W"
  | FEQ_S_64F     => "FEQ.S"
  | FLT_S_64F     => "FLT.S"
  | FLE_S_64F     => "FLE.S"
  | FCLASS_S_64F  => "FCLASS.S"
  | FCVT_S_W_64F  => "FCVT.S.W"
  | FCVT_S_WU_64F => "FCVT.S.WU"
  | FMV_W_X_64F   => "FMV.W.X"
  | FCVT_L_S_64F  => "FCVT.L.S"
  | FCVT_LU_S_64F => "FCVT.LU.S"
  | FCVT_S_L_64F  => "FCVT.S.L"
  | FCVT_S_LU_64F => "FCVT.S.LU"
  (* RV32D *)
  | FLD_32D       => "FLD"
  | FSD_32D       => "FSD"
  | FMADD_D_32D   => "FMADD.D"
  | FMSUB_D_32D   => "FMSUB.D"
  | FNMSUB_D_32D  => "FNMSUB.D"
  | FNMADD_D_32D  => "FNMADD.D"
  | FADD_D_32D    => "FADD.D"
  | FSUB_D_32D    => "FSUB.D"
  | FMUL_D_32D    => "FMUL.D"
  | FDIV_D_32D    => "FDIV.D"
  | FSQRT_D_32D   => "FSQRT.D"
  | FSGNJ_D_32D   => "FSGNJ.D"
  | FSGNJN_D_32D  => "FSGNJN.D"
  | FSGNJX_D_32D  => "FSGNJX.D"
  | FMIN_D_32D    => "FMIN.D"
  | FMAX_D_32D    => "FMAX.D"
  | FCVT_S_D_32D  => "FCVT.S.D"
  | FCVT_D_S_32D  => "FCVT.D.S"
  | FEQ_D_32D     => "FEQ.D"
  | FLT_D_32D     => "FLT.D"
  | FLE_D_32D     => "FLE.D"
  | FCLASS_D_32D  => "FCLASS.D"
  | FCVT_W_D_32D  => "FCVT.W.D"
  | FCVT_WU_D_32D => "FCVT.WU.D"
  | FCVT_D_W_32D  => "FCVT.D.W"
  | FCVT_D_WU_32D => "FCVT.D.WU"
  (* RV64D *)
  | FLD_64D       => "FLD"
  | FSD_64D       => "FSD"
  | FMADD_D_64D   => "FMADD.D"
  | FMSUB_D_64D   => "FMSUB.D"
  | FNMSUB_D_64D  => "FNMSUB.D"
  | FNMADD_D_64D  => "FNMADD.D"
  | FADD_D_64D    => "FADD.D"
  | FSUB_D_64D    => "FSUB.D"
  | FMUL_D_64D    => "FMUL.D"
  | FDIV_D_64D    => "FDIV.D"
  | FSQRT_D_64D   => "FSQRT.D"
  | FSGNJ_D_64D   => "FSGNJ.D"
  | FSGNJN_D_64D  => "FSGNJN.D"
  | FSGNJX_D_64D  => "FSGNJX.D"
  | FMIN_D_64D    => "FMIN.D"
  | FMAX_D_64D    => "FMAX.D"
  | FCVT_S_D_64D  => "FCVT.S.D"
  | FCVT_D_S_64D  => "FCVT.D.S"
  | FEQ_D_64D     => "FEQ.D"
  | FLT_D_64D     => "FLT.D"
  | FLE_D_64D     => "FLE.D"
  | FCLASS_D_64D  => "FCLASS.D"
  | FCVT_W_D_64D  => "FCVT.W.D"
  | FCVT_WU_D_64D => "FCVT.WU.D"
  | FCVT_D_W_64D  => "FCVT.D.W"
  | FCVT_D_WU_64D => "FCVT.D.WU"
  | FCVT_L_D_64D  => "FCVT.L.D"
  | FCVT_LU_D_64D => "FCVT.LU.D"
  | FMV_X_D_64D   => "FMV.X.D"
  | FCVT_D_L_64D  => "FCVT.D.L"
  | FCVT_D_LU_64D => "FCVT.D.LU"
  | FMV_D_X_64D   => "FMV.D.X"
  (* RV32Q *)
  | FLQ_32Q       => "FLQ"
  | FSQ_32Q       => "FSQ"
  | FMADD_Q_32Q   => "FMADD.Q"
  | FMSUB_Q_32Q   => "FMSUB.Q"
  | FNMSUB_Q_32Q  => "FNMSUB.Q"
  | FNMADD_Q_32Q  => "FNMADD.Q"
  | FADD_Q_32Q    => "FADD.Q"
  | FSUB_Q_32Q    => "FSUB.Q"
  | FMUL_Q_32Q    => "FMUL.Q"
  | FDIV_Q_32Q    => "FDIV.Q"
  | FSQRT_Q_32Q   => "FSQRT.Q"
  | FSGNJ_Q_32Q   => "FSGNJ.Q"
  | FSGNJN_Q_32Q  => "FSGNJN.Q"
  | FSGNJX_Q_32Q  => "FSGNJX.Q"
  | FMIN_Q_32Q    => "FMIN.Q"
  | FMAX_Q_32Q    => "FMAX.Q"
  | FCVT_S_Q_32Q  => "FCVT.S.Q"
  | FCVT_Q_S_32Q  => "FCVT.Q.S"
  | FCVT_D_Q_32Q  => "FCVT.D.Q"
  | FCVT_Q_D_32Q  => "FCVT.Q.D"
  | FEQ_Q_32Q     => "FEQ.Q"
  | FLT_Q_32Q     => "FLT.Q"
  | FLE_Q_32Q     => "FLE.Q"
  | FCLASS_Q_32Q  => "FCLASS.Q"
  | FCVT_W_Q_32Q  => "FCVT.W.Q"
  | FCVT_WU_Q_32Q => "FCVT.WU.Q"
  | FCVT_Q_W_32Q  => "FCVT.Q.W"
  | FCVT_Q_WU_32Q => "FCVT.Q.WU"
  (* RV64Q *)
  | FLQ_64Q       => "FLQ"
  | FSQ_64Q       => "FSQ"
  | FMADD_Q_64Q   => "FMADD.Q"
  | FMSUB_Q_64Q   => "FMSUB.Q"
  | FNMSUB_Q_64Q  => "FNMSUB.Q"
  | FNMADD_Q_64Q  => "FNMADD.Q"
  | FADD_Q_64Q    => "FADD.Q"
  | FSUB_Q_64Q    => "FSUB.Q"
  | FMUL_Q_64Q    => "FMUL.Q"
  | FDIV_Q_64Q    => "FDIV.Q"
  | FSQRT_Q_64Q   => "FSQRT.Q"
  | FSGNJ_Q_64Q   => "FSGNJ.Q"
  | FSGNJN_Q_64Q  => "FSGNJN.Q"
  | FSGNJX_Q_64Q  => "FSGNJX.Q"
  | FMIN_Q_64Q    => "FMIN.Q"
  | FMAX_Q_64Q    => "FMAX.Q"
  | FCVT_S_Q_64Q  => "FCVT.S.Q"
  | FCVT_Q_S_64Q  => "FCVT.Q.S"
  | FCVT_D_Q_64Q  => "FCVT.D.Q"
  | FCVT_Q_D_64Q  => "FCVT.Q.D"
  | FEQ_Q_64Q     => "FEQ.Q"
  | FLT_Q_64Q     => "FLT.Q"
  | FLE_Q_64Q     => "FLE.Q"
  | FCLASS_Q_64Q  => "FCLASS.Q"
  | FCVT_W_Q_64Q  => "FCVT.W.Q"
  | FCVT_WU_Q_64Q => "FCVT.WU.Q"
  | FCVT_Q_W_64Q  => "FCVT.Q.W"
  | FCVT_Q_WU_64Q => "FCVT.Q.WU"
  | FCVT_L_Q_64Q  => "FCVT.L.Q"
  | FCVT_LU_Q_64Q => "FCVT.LU.Q"
  | FCVT_Q_L_64Q  => "FCVT.Q.L"
  | FCVT_Q_LU_64Q => "FCVT.Q.LU"
  end.
