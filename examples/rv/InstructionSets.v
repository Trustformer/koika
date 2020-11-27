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
Inductive instruction_internal_name_RV32I : Type :=
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
| EBREAK_32I.
Scheme Equality for instruction_internal_name_RV32I.

Inductive instruction_internal_name_RV64I : Type :=
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
| SRAW_64I.
Scheme Equality for instruction_internal_name_RV64I.

Inductive instruction_internal_name_RV32Zifencei : Type :=
| FENCE_I_32Zifencei.
Scheme Equality for instruction_internal_name_RV32Zifencei.

Inductive instruction_internal_name_RV64Zifencei : Type :=
| FENCE_I_64Zifencei.
Scheme Equality for instruction_internal_name_RV64Zifencei.

Inductive instruction_internal_name_RV32Zicsr : Type :=
| CSRRW_32Zicsr
| CSRRS_32Zicsr
| CSRRC_32Zicsr
| CSRRWI_32Zicsr
| CSRRSI_32Zicsr
| CSRRCI_32Zicsr.
Scheme Equality for instruction_internal_name_RV32Zicsr.

Inductive instruction_internal_name_RV64Zicsr : Type :=
| CSRRW_64Zicsr
| CSRRS_64Zicsr
| CSRRC_64Zicsr
| CSRRWI_64Zicsr
| CSRRSI_64Zicsr
| CSRRCI_64Zicsr.
Scheme Equality for instruction_internal_name_RV64Zicsr.

Inductive instruction_internal_name_RV32M : Type :=
| MUL_32M
| MULH_32M
| MULHSU_32M
| MULHU_32M
| DIV_32M
| DIVU_32M
| REM_32M
| REMU_32M.
Scheme Equality for instruction_internal_name_RV32M.

Inductive instruction_internal_name_RV64M : Type :=
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
| REMUW_64M.
Scheme Equality for instruction_internal_name_RV64M.

Inductive instruction_internal_name_RV32A : Type :=
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
| AMOMAXU_W_32A.
Scheme Equality for instruction_internal_name_RV32A.

Inductive instruction_internal_name_RV64A : Type :=
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
| AMOMAXU_D_64A.
Scheme Equality for instruction_internal_name_RV64A.

Inductive instruction_internal_name_RV32F : Type :=
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
| FMV_W_X_32F.
Scheme Equality for instruction_internal_name_RV32F.

Inductive instruction_internal_name_RV64F : Type :=
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
| FCVT_S_LU_64F.
Scheme Equality for instruction_internal_name_RV64F.

Inductive instruction_internal_name_RV32D : Type :=
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
| FCVT_D_WU_32D.
Scheme Equality for instruction_internal_name_RV32D.

Inductive instruction_internal_name_RV64D : Type :=
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
| FMV_D_X_64D.
Scheme Equality for instruction_internal_name_RV64D.

Inductive instruction_internal_name_RV32Q : Type :=
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
| FCVT_Q_WU_32Q.
Scheme Equality for instruction_internal_name_RV32Q.

Inductive instruction_internal_name_RV64Q : Type :=
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
Scheme Equality for instruction_internal_name_RV64Q.

Inductive instruction_internal_name : Type :=
| RV32I_instruction :
  instruction_internal_name_RV32I -> instruction_internal_name
| RV64I_instruction :
  instruction_internal_name_RV64I -> instruction_internal_name
| RV32Zifencei_instruction :
  instruction_internal_name_RV32Zifencei -> instruction_internal_name
| RV64Zifencei_instruction :
  instruction_internal_name_RV64Zifencei -> instruction_internal_name
| RV32Zicsr_instruction :
  instruction_internal_name_RV32Zicsr -> instruction_internal_name
| RV64Zicsr_instruction :
  instruction_internal_name_RV64Zicsr -> instruction_internal_name
| RV32M_instruction :
  instruction_internal_name_RV32M -> instruction_internal_name
| RV64M_instruction :
  instruction_internal_name_RV64M -> instruction_internal_name
| RV32A_instruction :
  instruction_internal_name_RV32A -> instruction_internal_name
| RV64A_instruction :
  instruction_internal_name_RV64A -> instruction_internal_name
| RV32F_instruction :
  instruction_internal_name_RV32F -> instruction_internal_name
| RV64F_instruction :
  instruction_internal_name_RV64F -> instruction_internal_name
| RV32D_instruction :
  instruction_internal_name_RV32D -> instruction_internal_name
| RV64D_instruction :
  instruction_internal_name_RV64D -> instruction_internal_name
| RV32Q_instruction :
  instruction_internal_name_RV32Q -> instruction_internal_name
| RV64Q_instruction :
  instruction_internal_name_RV64Q -> instruction_internal_name.

About instruction_internal_name_RV32I_eq_dec.

Module Decidable_instruction_internal_name <: DecidableType.
  Definition t := instruction_internal_name.
  Definition eq := @eq instruction_internal_name.
  Instance eq_equiv : @Equivalence instruction_internal_name eq :=
    eq_equivalence.
  Definition eq_dec : forall a b : instruction_internal_name,
    {a = b} + {a <> b}.
  Proof. decide equality; decide equality. Qed.
End Decidable_instruction_internal_name.

Module InstructionsInternalNamesSet
  <: WSetsOn Decidable_instruction_internal_name.
  Include WSetsOn Decidable_instruction_internal_name.
End InstructionsInternalNamesSet.

Definition RV32I_instruction_internal_names : InstructionsInternalNamesSet.t :=
  (InstructionsInternalNamesSet.add (RV32I_instruction LUI_32I)
  (InstructionsInternalNamesSet.add (RV32I_instruction AUIPC_32I)
  (InstructionsInternalNamesSet.add (RV32I_instruction JAL_32I)
  (InstructionsInternalNamesSet.add (RV32I_instruction JALR_32I)
  (InstructionsInternalNamesSet.add (RV32I_instruction BEQ_32I)
  (InstructionsInternalNamesSet.add (RV32I_instruction BNE_32I)
  (InstructionsInternalNamesSet.add (RV32I_instruction BLT_32I)
  (InstructionsInternalNamesSet.add (RV32I_instruction BGE_32I)
  (InstructionsInternalNamesSet.add (RV32I_instruction BLTU_32I)
  (InstructionsInternalNamesSet.add (RV32I_instruction BGEU_32I)
  (InstructionsInternalNamesSet.add (RV32I_instruction LB_32I)
  (InstructionsInternalNamesSet.add (RV32I_instruction LH_32I)
  (InstructionsInternalNamesSet.add (RV32I_instruction LW_32I)
  (InstructionsInternalNamesSet.add (RV32I_instruction LBU_32I)
  (InstructionsInternalNamesSet.add (RV32I_instruction LHU_32I)
  (InstructionsInternalNamesSet.add (RV32I_instruction SB_32I)
  (InstructionsInternalNamesSet.add (RV32I_instruction SH_32I)
  (InstructionsInternalNamesSet.add (RV32I_instruction SW_32I)
  (InstructionsInternalNamesSet.add (RV32I_instruction ADDI_32I)
  (InstructionsInternalNamesSet.add (RV32I_instruction SLTI_32I)
  (InstructionsInternalNamesSet.add (RV32I_instruction SLTIU_32I)
  (InstructionsInternalNamesSet.add (RV32I_instruction XORI_32I)
  (InstructionsInternalNamesSet.add (RV32I_instruction ORI_32I)
  (InstructionsInternalNamesSet.add (RV32I_instruction ANDI_32I)
  (InstructionsInternalNamesSet.add (RV32I_instruction SLLI_32I)
  (InstructionsInternalNamesSet.add (RV32I_instruction SRLI_32I)
  (InstructionsInternalNamesSet.add (RV32I_instruction SRAI_32I)
  (InstructionsInternalNamesSet.add (RV32I_instruction ADD_32I)
  (InstructionsInternalNamesSet.add (RV32I_instruction SUB_32I)
  (InstructionsInternalNamesSet.add (RV32I_instruction SLL_32I)
  (InstructionsInternalNamesSet.add (RV32I_instruction SLT_32I)
  (InstructionsInternalNamesSet.add (RV32I_instruction SLTU_32I)
  (InstructionsInternalNamesSet.add (RV32I_instruction XOR_32I)
  (InstructionsInternalNamesSet.add (RV32I_instruction SRL_32I)
  (InstructionsInternalNamesSet.add (RV32I_instruction SRA_32I)
  (InstructionsInternalNamesSet.add (RV32I_instruction OR_32I)
  (InstructionsInternalNamesSet.add (RV32I_instruction AND_32I)
  (InstructionsInternalNamesSet.add (RV32I_instruction FENCE_32I)
  (InstructionsInternalNamesSet.add (RV32I_instruction ECALL_32I)
  (InstructionsInternalNamesSet.add (RV32I_instruction EBREAK_32I)
  InstructionsInternalNamesSet.empty)))))))))))))))))))))))))))))))))))))))).

Definition RV64I_instruction_internal_names : InstructionsInternalNamesSet.t :=
  (InstructionsInternalNamesSet.add (RV64I_instruction LUI_64I)
  (InstructionsInternalNamesSet.add (RV64I_instruction AUIPC_64I)
  (InstructionsInternalNamesSet.add (RV64I_instruction JAL_64I)
  (InstructionsInternalNamesSet.add (RV64I_instruction JALR_64I)
  (InstructionsInternalNamesSet.add (RV64I_instruction BEQ_64I)
  (InstructionsInternalNamesSet.add (RV64I_instruction BNE_64I)
  (InstructionsInternalNamesSet.add (RV64I_instruction BLT_64I)
  (InstructionsInternalNamesSet.add (RV64I_instruction BGE_64I)
  (InstructionsInternalNamesSet.add (RV64I_instruction BLTU_64I)
  (InstructionsInternalNamesSet.add (RV64I_instruction BGEU_64I)
  (InstructionsInternalNamesSet.add (RV64I_instruction LB_64I)
  (InstructionsInternalNamesSet.add (RV64I_instruction LH_64I)
  (InstructionsInternalNamesSet.add (RV64I_instruction LW_64I)
  (InstructionsInternalNamesSet.add (RV64I_instruction LBU_64I)
  (InstructionsInternalNamesSet.add (RV64I_instruction LHU_64I)
  (InstructionsInternalNamesSet.add (RV64I_instruction SB_64I)
  (InstructionsInternalNamesSet.add (RV64I_instruction SH_64I)
  (InstructionsInternalNamesSet.add (RV64I_instruction SW_64I)
  (InstructionsInternalNamesSet.add (RV64I_instruction ADDI_64I)
  (InstructionsInternalNamesSet.add (RV64I_instruction SLTI_64I)
  (InstructionsInternalNamesSet.add (RV64I_instruction SLTIU_64I)
  (InstructionsInternalNamesSet.add (RV64I_instruction XORI_64I)
  (InstructionsInternalNamesSet.add (RV64I_instruction ORI_64I)
  (InstructionsInternalNamesSet.add (RV64I_instruction ANDI_64I)
  (InstructionsInternalNamesSet.add (RV64I_instruction SLLI_64I)
  (InstructionsInternalNamesSet.add (RV64I_instruction SRLI_64I)
  (InstructionsInternalNamesSet.add (RV64I_instruction SRAI_64I)
  (InstructionsInternalNamesSet.add (RV64I_instruction ADD_64I)
  (InstructionsInternalNamesSet.add (RV64I_instruction SUB_64I)
  (InstructionsInternalNamesSet.add (RV64I_instruction SLL_64I)
  (InstructionsInternalNamesSet.add (RV64I_instruction SLT_64I)
  (InstructionsInternalNamesSet.add (RV64I_instruction SLTU_64I)
  (InstructionsInternalNamesSet.add (RV64I_instruction XOR_64I)
  (InstructionsInternalNamesSet.add (RV64I_instruction SRL_64I)
  (InstructionsInternalNamesSet.add (RV64I_instruction SRA_64I)
  (InstructionsInternalNamesSet.add (RV64I_instruction OR_64I)
  (InstructionsInternalNamesSet.add (RV64I_instruction AND_64I)
  (InstructionsInternalNamesSet.add (RV64I_instruction FENCE_64I)
  (InstructionsInternalNamesSet.add (RV64I_instruction ECALL_64I)
  (InstructionsInternalNamesSet.add (RV64I_instruction EBREAK_64I)
  (InstructionsInternalNamesSet.add (RV64I_instruction LWU_64I)
  (InstructionsInternalNamesSet.add (RV64I_instruction LD_64I)
  (InstructionsInternalNamesSet.add (RV64I_instruction SD_64I)
  (InstructionsInternalNamesSet.add (RV64I_instruction ADDIW_64I)
  (InstructionsInternalNamesSet.add (RV64I_instruction SLLIW_64I)
  (InstructionsInternalNamesSet.add (RV64I_instruction SRLIW_64I)
  (InstructionsInternalNamesSet.add (RV64I_instruction SRAIW_64I)
  (InstructionsInternalNamesSet.add (RV64I_instruction ADDW_64I)
  (InstructionsInternalNamesSet.add (RV64I_instruction SUBW_64I)
  (InstructionsInternalNamesSet.add (RV64I_instruction SLLW_64I)
  (InstructionsInternalNamesSet.add (RV64I_instruction SRLW_64I)
  (InstructionsInternalNamesSet.add (RV64I_instruction SRAW_64I)
  InstructionsInternalNamesSet.empty
  )))))))))))))))))))))))))))))))))))))))))))))))))))).

Definition RV32Zifencei_instruction_internal_names
  : InstructionsInternalNamesSet.t :=
  InstructionsInternalNamesSet.add (RV32Zifencei_instruction FENCE_I_32Zifencei)
  (InstructionsInternalNamesSet.empty).

Definition RV64Zifencei_instruction_internal_names
  : InstructionsInternalNamesSet.t :=
  InstructionsInternalNamesSet.add (RV64Zifencei_instruction FENCE_I_64Zifencei)
    (InstructionsInternalNamesSet.empty).

Definition RV32Zicsr_instruction_internal_names
  : InstructionsInternalNamesSet.t :=
  (InstructionsInternalNamesSet.add (RV32Zicsr_instruction CSRRW_32Zicsr)
  (InstructionsInternalNamesSet.add (RV32Zicsr_instruction CSRRS_32Zicsr)
  (InstructionsInternalNamesSet.add (RV32Zicsr_instruction CSRRC_32Zicsr)
  (InstructionsInternalNamesSet.add (RV32Zicsr_instruction CSRRWI_32Zicsr)
  (InstructionsInternalNamesSet.add (RV32Zicsr_instruction CSRRSI_32Zicsr)
  (InstructionsInternalNamesSet.add (RV32Zicsr_instruction CSRRCI_32Zicsr)
  InstructionsInternalNamesSet.empty)))))).

Definition RV64Zicsr_instruction_internal_names
  : InstructionsInternalNamesSet.t :=
  (InstructionsInternalNamesSet.add (RV64Zicsr_instruction CSRRW_64Zicsr)
  (InstructionsInternalNamesSet.add (RV64Zicsr_instruction CSRRS_64Zicsr)
  (InstructionsInternalNamesSet.add (RV64Zicsr_instruction CSRRC_64Zicsr)
  (InstructionsInternalNamesSet.add (RV64Zicsr_instruction CSRRWI_64Zicsr)
  (InstructionsInternalNamesSet.add (RV64Zicsr_instruction CSRRSI_64Zicsr)
  (InstructionsInternalNamesSet.add (RV64Zicsr_instruction CSRRCI_64Zicsr)
  InstructionsInternalNamesSet.empty)))))).

Definition RV32M_instruction_internal_names : InstructionsInternalNamesSet.t :=
  (InstructionsInternalNamesSet.add (RV32M_instruction MUL_32M)
  (InstructionsInternalNamesSet.add (RV32M_instruction MULH_32M)
  (InstructionsInternalNamesSet.add (RV32M_instruction MULHSU_32M)
  (InstructionsInternalNamesSet.add (RV32M_instruction MULHU_32M)
  (InstructionsInternalNamesSet.add (RV32M_instruction DIV_32M)
  (InstructionsInternalNamesSet.add (RV32M_instruction DIVU_32M)
  (InstructionsInternalNamesSet.add (RV32M_instruction REM_32M)
  (InstructionsInternalNamesSet.add (RV32M_instruction REMU_32M)
  InstructionsInternalNamesSet.empty)))))))).

Definition RV64M_instruction_internal_names : InstructionsInternalNamesSet.t :=
  (InstructionsInternalNamesSet.add (RV64M_instruction MUL_64M)
  (InstructionsInternalNamesSet.add (RV64M_instruction MULH_64M)
  (InstructionsInternalNamesSet.add (RV64M_instruction MULHSU_64M)
  (InstructionsInternalNamesSet.add (RV64M_instruction MULHU_64M)
  (InstructionsInternalNamesSet.add (RV64M_instruction DIV_64M)
  (InstructionsInternalNamesSet.add (RV64M_instruction DIVU_64M)
  (InstructionsInternalNamesSet.add (RV64M_instruction REM_64M)
  (InstructionsInternalNamesSet.add (RV64M_instruction REMU_64M)
  (InstructionsInternalNamesSet.add (RV64M_instruction MULW_64M)
  (InstructionsInternalNamesSet.add (RV64M_instruction DIVW_64M)
  (InstructionsInternalNamesSet.add (RV64M_instruction DIVUW_64M)
  (InstructionsInternalNamesSet.add (RV64M_instruction REMW_64M)
  (InstructionsInternalNamesSet.add (RV64M_instruction REMUW_64M)
  InstructionsInternalNamesSet.empty))))))))))))).

Definition RV32A_instruction_internal_names : InstructionsInternalNamesSet.t :=
  (InstructionsInternalNamesSet.add (RV32A_instruction LR_W_32A)
  (InstructionsInternalNamesSet.add (RV32A_instruction SC_W_32A)
  (InstructionsInternalNamesSet.add (RV32A_instruction AMOSWAP_W_32A)
  (InstructionsInternalNamesSet.add (RV32A_instruction AMOADD_W_32A)
  (InstructionsInternalNamesSet.add (RV32A_instruction AMOXOR_W_32A)
  (InstructionsInternalNamesSet.add (RV32A_instruction AMOAND_W_32A)
  (InstructionsInternalNamesSet.add (RV32A_instruction AMOOR_W_32A)
  (InstructionsInternalNamesSet.add (RV32A_instruction AMOMIN_W_32A)
  (InstructionsInternalNamesSet.add (RV32A_instruction AMOMAX_W_32A)
  (InstructionsInternalNamesSet.add (RV32A_instruction AMOMINU_W_32A)
  (InstructionsInternalNamesSet.add (RV32A_instruction AMOMAXU_W_32A)
  InstructionsInternalNamesSet.empty))))))))))).

Definition RV64A_instruction_internal_names : InstructionsInternalNamesSet.t :=
  (InstructionsInternalNamesSet.add (RV64A_instruction LR_W_64A)
  (InstructionsInternalNamesSet.add (RV64A_instruction SC_W_64A)
  (InstructionsInternalNamesSet.add (RV64A_instruction AMOSWAP_W_64A)
  (InstructionsInternalNamesSet.add (RV64A_instruction AMOADD_W_64A)
  (InstructionsInternalNamesSet.add (RV64A_instruction AMOXOR_W_64A)
  (InstructionsInternalNamesSet.add (RV64A_instruction AMOAND_W_64A)
  (InstructionsInternalNamesSet.add (RV64A_instruction AMOOR_W_64A)
  (InstructionsInternalNamesSet.add (RV64A_instruction AMOMIN_W_64A)
  (InstructionsInternalNamesSet.add (RV64A_instruction AMOMAX_W_64A)
  (InstructionsInternalNamesSet.add (RV64A_instruction AMOMINU_W_64A)
  (InstructionsInternalNamesSet.add (RV64A_instruction AMOMAXU_W_64A)
  (InstructionsInternalNamesSet.add (RV64A_instruction LR_D_64A)
  (InstructionsInternalNamesSet.add (RV64A_instruction SC_D_64A)
  (InstructionsInternalNamesSet.add (RV64A_instruction AMOSWAP_D_64A)
  (InstructionsInternalNamesSet.add (RV64A_instruction AMOADD_D_64A)
  (InstructionsInternalNamesSet.add (RV64A_instruction AMOXOR_D_64A)
  (InstructionsInternalNamesSet.add (RV64A_instruction AMOAND_D_64A)
  (InstructionsInternalNamesSet.add (RV64A_instruction AMOOR_D_64A)
  (InstructionsInternalNamesSet.add (RV64A_instruction AMOMIN_D_64A)
  (InstructionsInternalNamesSet.add (RV64A_instruction AMOMAX_D_64A)
  (InstructionsInternalNamesSet.add (RV64A_instruction AMOMINU_D_64A)
  (InstructionsInternalNamesSet.add (RV64A_instruction AMOMAXU_D_64A)
  InstructionsInternalNamesSet.empty)))))))))))))))))))))).

Definition RV32F_instruction_internal_names : InstructionsInternalNamesSet.t :=
  (InstructionsInternalNamesSet.add (RV32F_instruction FLW_32F)
  (InstructionsInternalNamesSet.add (RV32F_instruction FSW_32F)
  (InstructionsInternalNamesSet.add (RV32F_instruction FMADD_S_32F)
  (InstructionsInternalNamesSet.add (RV32F_instruction FMSUB_S_32F)
  (InstructionsInternalNamesSet.add (RV32F_instruction FNMSUB_S_32F)
  (InstructionsInternalNamesSet.add (RV32F_instruction FNMADD_S_32F)
  (InstructionsInternalNamesSet.add (RV32F_instruction FADD_S_32F)
  (InstructionsInternalNamesSet.add (RV32F_instruction FSUB_S_32F)
  (InstructionsInternalNamesSet.add (RV32F_instruction FMUL_S_32F)
  (InstructionsInternalNamesSet.add (RV32F_instruction FDIV_S_32F)
  (InstructionsInternalNamesSet.add (RV32F_instruction FSQRT_S_32F)
  (InstructionsInternalNamesSet.add (RV32F_instruction FSGNJ_S_32F)
  (InstructionsInternalNamesSet.add (RV32F_instruction FSGNJN_S_32F)
  (InstructionsInternalNamesSet.add (RV32F_instruction FSGNJX_S_32F)
  (InstructionsInternalNamesSet.add (RV32F_instruction FMIN_S_32F)
  (InstructionsInternalNamesSet.add (RV32F_instruction FMAX_S_32F)
  (InstructionsInternalNamesSet.add (RV32F_instruction FCVT_W_S_32F)
  (InstructionsInternalNamesSet.add (RV32F_instruction FCVT_WU_S_32F)
  (InstructionsInternalNamesSet.add (RV32F_instruction FMV_X_W_32F)
  (InstructionsInternalNamesSet.add (RV32F_instruction FEQ_S_32F)
  (InstructionsInternalNamesSet.add (RV32F_instruction FLT_S_32F)
  (InstructionsInternalNamesSet.add (RV32F_instruction FLE_S_32F)
  (InstructionsInternalNamesSet.add (RV32F_instruction FCLASS_S_32F)
  (InstructionsInternalNamesSet.add (RV32F_instruction FCVT_S_W_32F)
  (InstructionsInternalNamesSet.add (RV32F_instruction FCVT_S_WU_32F)
  (InstructionsInternalNamesSet.add (RV32F_instruction FMV_W_X_32F)
  InstructionsInternalNamesSet.empty)))))))))))))))))))))))))).

Definition RV64F_instruction_internal_names : InstructionsInternalNamesSet.t :=
  (InstructionsInternalNamesSet.add (RV64F_instruction FLW_64F)
  (InstructionsInternalNamesSet.add (RV64F_instruction FSW_64F)
  (InstructionsInternalNamesSet.add (RV64F_instruction FMADD_S_64F)
  (InstructionsInternalNamesSet.add (RV64F_instruction FMSUB_S_64F)
  (InstructionsInternalNamesSet.add (RV64F_instruction FNMSUB_S_64F)
  (InstructionsInternalNamesSet.add (RV64F_instruction FNMADD_S_64F)
  (InstructionsInternalNamesSet.add (RV64F_instruction FADD_S_64F)
  (InstructionsInternalNamesSet.add (RV64F_instruction FSUB_S_64F)
  (InstructionsInternalNamesSet.add (RV64F_instruction FMUL_S_64F)
  (InstructionsInternalNamesSet.add (RV64F_instruction FDIV_S_64F)
  (InstructionsInternalNamesSet.add (RV64F_instruction FSQRT_S_64F)
  (InstructionsInternalNamesSet.add (RV64F_instruction FSGNJ_S_64F)
  (InstructionsInternalNamesSet.add (RV64F_instruction FSGNJN_S_64F)
  (InstructionsInternalNamesSet.add (RV64F_instruction FSGNJX_S_64F)
  (InstructionsInternalNamesSet.add (RV64F_instruction FMIN_S_64F)
  (InstructionsInternalNamesSet.add (RV64F_instruction FMAX_S_64F)
  (InstructionsInternalNamesSet.add (RV64F_instruction FCVT_W_S_64F)
  (InstructionsInternalNamesSet.add (RV64F_instruction FCVT_WU_S_64F)
  (InstructionsInternalNamesSet.add (RV64F_instruction FMV_X_W_64F)
  (InstructionsInternalNamesSet.add (RV64F_instruction FEQ_S_64F)
  (InstructionsInternalNamesSet.add (RV64F_instruction FLT_S_64F)
  (InstructionsInternalNamesSet.add (RV64F_instruction FLE_S_64F)
  (InstructionsInternalNamesSet.add (RV64F_instruction FCLASS_S_64F)
  (InstructionsInternalNamesSet.add (RV64F_instruction FCVT_S_W_64F)
  (InstructionsInternalNamesSet.add (RV64F_instruction FCVT_S_WU_64F)
  (InstructionsInternalNamesSet.add (RV64F_instruction FMV_W_X_64F)
  (InstructionsInternalNamesSet.add (RV64F_instruction FCVT_L_S_64F)
  (InstructionsInternalNamesSet.add (RV64F_instruction FCVT_LU_S_64F)
  (InstructionsInternalNamesSet.add (RV64F_instruction FCVT_S_L_64F)
  (InstructionsInternalNamesSet.add (RV64F_instruction FCVT_S_LU_64F)
  InstructionsInternalNamesSet.empty)))))))))))))))))))))))))))))).

Definition RV32D_instruction_internal_names : InstructionsInternalNamesSet.t :=
  (InstructionsInternalNamesSet.add (RV32D_instruction FLD_32D)
  (InstructionsInternalNamesSet.add (RV32D_instruction FSD_32D)
  (InstructionsInternalNamesSet.add (RV32D_instruction FMADD_D_32D)
  (InstructionsInternalNamesSet.add (RV32D_instruction FMSUB_D_32D)
  (InstructionsInternalNamesSet.add (RV32D_instruction FNMSUB_D_32D)
  (InstructionsInternalNamesSet.add (RV32D_instruction FNMADD_D_32D)
  (InstructionsInternalNamesSet.add (RV32D_instruction FADD_D_32D)
  (InstructionsInternalNamesSet.add (RV32D_instruction FSUB_D_32D)
  (InstructionsInternalNamesSet.add (RV32D_instruction FMUL_D_32D)
  (InstructionsInternalNamesSet.add (RV32D_instruction FDIV_D_32D)
  (InstructionsInternalNamesSet.add (RV32D_instruction FSQRT_D_32D)
  (InstructionsInternalNamesSet.add (RV32D_instruction FSGNJ_D_32D)
  (InstructionsInternalNamesSet.add (RV32D_instruction FSGNJN_D_32D)
  (InstructionsInternalNamesSet.add (RV32D_instruction FSGNJX_D_32D)
  (InstructionsInternalNamesSet.add (RV32D_instruction FMIN_D_32D)
  (InstructionsInternalNamesSet.add (RV32D_instruction FMAX_D_32D)
  (InstructionsInternalNamesSet.add (RV32D_instruction FCVT_S_D_32D)
  (InstructionsInternalNamesSet.add (RV32D_instruction FCVT_D_S_32D)
  (InstructionsInternalNamesSet.add (RV32D_instruction FEQ_D_32D)
  (InstructionsInternalNamesSet.add (RV32D_instruction FLT_D_32D)
  (InstructionsInternalNamesSet.add (RV32D_instruction FLE_D_32D)
  (InstructionsInternalNamesSet.add (RV32D_instruction FCLASS_D_32D)
  (InstructionsInternalNamesSet.add (RV32D_instruction FCVT_W_D_32D)
  (InstructionsInternalNamesSet.add (RV32D_instruction FCVT_WU_D_32D)
  (InstructionsInternalNamesSet.add (RV32D_instruction FCVT_D_W_32D)
  (InstructionsInternalNamesSet.add (RV32D_instruction FCVT_D_WU_32D)
  InstructionsInternalNamesSet.empty)))))))))))))))))))))))))).

Definition RV64D_instruction_internal_names : InstructionsInternalNamesSet.t :=
  (InstructionsInternalNamesSet.add (RV64D_instruction FLD_64D)
  (InstructionsInternalNamesSet.add (RV64D_instruction FSD_64D)
  (InstructionsInternalNamesSet.add (RV64D_instruction FMADD_D_64D)
  (InstructionsInternalNamesSet.add (RV64D_instruction FMSUB_D_64D)
  (InstructionsInternalNamesSet.add (RV64D_instruction FNMSUB_D_64D)
  (InstructionsInternalNamesSet.add (RV64D_instruction FNMADD_D_64D)
  (InstructionsInternalNamesSet.add (RV64D_instruction FADD_D_64D)
  (InstructionsInternalNamesSet.add (RV64D_instruction FSUB_D_64D)
  (InstructionsInternalNamesSet.add (RV64D_instruction FMUL_D_64D)
  (InstructionsInternalNamesSet.add (RV64D_instruction FDIV_D_64D)
  (InstructionsInternalNamesSet.add (RV64D_instruction FSQRT_D_64D)
  (InstructionsInternalNamesSet.add (RV64D_instruction FSGNJ_D_64D)
  (InstructionsInternalNamesSet.add (RV64D_instruction FSGNJN_D_64D)
  (InstructionsInternalNamesSet.add (RV64D_instruction FSGNJX_D_64D)
  (InstructionsInternalNamesSet.add (RV64D_instruction FMIN_D_64D)
  (InstructionsInternalNamesSet.add (RV64D_instruction FMAX_D_64D)
  (InstructionsInternalNamesSet.add (RV64D_instruction FCVT_S_D_64D)
  (InstructionsInternalNamesSet.add (RV64D_instruction FCVT_D_S_64D)
  (InstructionsInternalNamesSet.add (RV64D_instruction FEQ_D_64D)
  (InstructionsInternalNamesSet.add (RV64D_instruction FLT_D_64D)
  (InstructionsInternalNamesSet.add (RV64D_instruction FLE_D_64D)
  (InstructionsInternalNamesSet.add (RV64D_instruction FCLASS_D_64D)
  (InstructionsInternalNamesSet.add (RV64D_instruction FCVT_W_D_64D)
  (InstructionsInternalNamesSet.add (RV64D_instruction FCVT_WU_D_64D)
  (InstructionsInternalNamesSet.add (RV64D_instruction FCVT_D_W_64D)
  (InstructionsInternalNamesSet.add (RV64D_instruction FCVT_D_WU_64D)
  (InstructionsInternalNamesSet.add (RV64D_instruction FCVT_L_D_64D)
  (InstructionsInternalNamesSet.add (RV64D_instruction FCVT_LU_D_64D)
  (InstructionsInternalNamesSet.add (RV64D_instruction FMV_X_D_64D)
  (InstructionsInternalNamesSet.add (RV64D_instruction FCVT_D_L_64D)
  (InstructionsInternalNamesSet.add (RV64D_instruction FCVT_D_LU_64D)
  (InstructionsInternalNamesSet.add (RV64D_instruction FMV_D_X_64D)
  InstructionsInternalNamesSet.empty)))))))))))))))))))))))))))))))).

Definition RV32Q_instruction_internal_names : InstructionsInternalNamesSet.t :=
  (InstructionsInternalNamesSet.add (RV32Q_instruction FLQ_32Q)
  (InstructionsInternalNamesSet.add (RV32Q_instruction FSQ_32Q)
  (InstructionsInternalNamesSet.add (RV32Q_instruction FMADD_Q_32Q)
  (InstructionsInternalNamesSet.add (RV32Q_instruction FMSUB_Q_32Q)
  (InstructionsInternalNamesSet.add (RV32Q_instruction FNMSUB_Q_32Q)
  (InstructionsInternalNamesSet.add (RV32Q_instruction FNMADD_Q_32Q)
  (InstructionsInternalNamesSet.add (RV32Q_instruction FADD_Q_32Q)
  (InstructionsInternalNamesSet.add (RV32Q_instruction FSUB_Q_32Q)
  (InstructionsInternalNamesSet.add (RV32Q_instruction FMUL_Q_32Q)
  (InstructionsInternalNamesSet.add (RV32Q_instruction FDIV_Q_32Q)
  (InstructionsInternalNamesSet.add (RV32Q_instruction FSQRT_Q_32Q)
  (InstructionsInternalNamesSet.add (RV32Q_instruction FSGNJ_Q_32Q)
  (InstructionsInternalNamesSet.add (RV32Q_instruction FSGNJN_Q_32Q)
  (InstructionsInternalNamesSet.add (RV32Q_instruction FSGNJX_Q_32Q)
  (InstructionsInternalNamesSet.add (RV32Q_instruction FMIN_Q_32Q)
  (InstructionsInternalNamesSet.add (RV32Q_instruction FMAX_Q_32Q)
  (InstructionsInternalNamesSet.add (RV32Q_instruction FCVT_S_Q_32Q)
  (InstructionsInternalNamesSet.add (RV32Q_instruction FCVT_Q_S_32Q)
  (InstructionsInternalNamesSet.add (RV32Q_instruction FCVT_D_Q_32Q)
  (InstructionsInternalNamesSet.add (RV32Q_instruction FCVT_Q_D_32Q)
  (InstructionsInternalNamesSet.add (RV32Q_instruction FEQ_Q_32Q)
  (InstructionsInternalNamesSet.add (RV32Q_instruction FLT_Q_32Q)
  (InstructionsInternalNamesSet.add (RV32Q_instruction FLE_Q_32Q)
  (InstructionsInternalNamesSet.add (RV32Q_instruction FCLASS_Q_32Q)
  (InstructionsInternalNamesSet.add (RV32Q_instruction FCVT_W_Q_32Q)
  (InstructionsInternalNamesSet.add (RV32Q_instruction FCVT_WU_Q_32Q)
  (InstructionsInternalNamesSet.add (RV32Q_instruction FCVT_Q_W_32Q)
  (InstructionsInternalNamesSet.add (RV32Q_instruction FCVT_Q_WU_32Q)
  InstructionsInternalNamesSet.empty)))))))))))))))))))))))))))).

Definition RV64Q_instruction_internal_names : InstructionsInternalNamesSet.t :=
  (InstructionsInternalNamesSet.add (RV64Q_instruction FLQ_64Q)
  (InstructionsInternalNamesSet.add (RV64Q_instruction FSQ_64Q)
  (InstructionsInternalNamesSet.add (RV64Q_instruction FMADD_Q_64Q)
  (InstructionsInternalNamesSet.add (RV64Q_instruction FMSUB_Q_64Q)
  (InstructionsInternalNamesSet.add (RV64Q_instruction FNMSUB_Q_64Q)
  (InstructionsInternalNamesSet.add (RV64Q_instruction FNMADD_Q_64Q)
  (InstructionsInternalNamesSet.add (RV64Q_instruction FADD_Q_64Q)
  (InstructionsInternalNamesSet.add (RV64Q_instruction FSUB_Q_64Q)
  (InstructionsInternalNamesSet.add (RV64Q_instruction FMUL_Q_64Q)
  (InstructionsInternalNamesSet.add (RV64Q_instruction FDIV_Q_64Q)
  (InstructionsInternalNamesSet.add (RV64Q_instruction FSQRT_Q_64Q)
  (InstructionsInternalNamesSet.add (RV64Q_instruction FSGNJ_Q_64Q)
  (InstructionsInternalNamesSet.add (RV64Q_instruction FSGNJN_Q_64Q)
  (InstructionsInternalNamesSet.add (RV64Q_instruction FSGNJX_Q_64Q)
  (InstructionsInternalNamesSet.add (RV64Q_instruction FMIN_Q_64Q)
  (InstructionsInternalNamesSet.add (RV64Q_instruction FMAX_Q_64Q)
  (InstructionsInternalNamesSet.add (RV64Q_instruction FCVT_S_Q_64Q)
  (InstructionsInternalNamesSet.add (RV64Q_instruction FCVT_Q_S_64Q)
  (InstructionsInternalNamesSet.add (RV64Q_instruction FCVT_D_Q_64Q)
  (InstructionsInternalNamesSet.add (RV64Q_instruction FCVT_Q_D_64Q)
  (InstructionsInternalNamesSet.add (RV64Q_instruction FEQ_Q_64Q)
  (InstructionsInternalNamesSet.add (RV64Q_instruction FLT_Q_64Q)
  (InstructionsInternalNamesSet.add (RV64Q_instruction FLE_Q_64Q)
  (InstructionsInternalNamesSet.add (RV64Q_instruction FCLASS_Q_64Q)
  (InstructionsInternalNamesSet.add (RV64Q_instruction FCVT_W_Q_64Q)
  (InstructionsInternalNamesSet.add (RV64Q_instruction FCVT_WU_Q_64Q)
  (InstructionsInternalNamesSet.add (RV64Q_instruction FCVT_Q_W_64Q)
  (InstructionsInternalNamesSet.add (RV64Q_instruction FCVT_Q_WU_64Q)
  (InstructionsInternalNamesSet.add (RV64Q_instruction FCVT_L_Q_64Q)
  (InstructionsInternalNamesSet.add (RV64Q_instruction FCVT_LU_Q_64Q)
  (InstructionsInternalNamesSet.add (RV64Q_instruction FCVT_Q_L_64Q)
  (InstructionsInternalNamesSet.add (RV64Q_instruction FCVT_Q_LU_64Q)
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

Definition opcode_bin (o : opcode_name) :=
match o with
| opcode_OP        => Ob~0~1~1~0~0~1~1
| opcode_JALR      => Ob~1~1~0~0~1~1~1
| opcode_LOAD      => Ob~0~0~0~0~0~1~1
| opcode_OP_IMM    => Ob~0~0~1~0~0~1~1
| opcode_MISC_MEM  => Ob~0~0~0~1~1~1~1
| opcode_STORE     => Ob~0~1~0~0~0~1~1
| opcode_BRANCH    => Ob~1~1~0~0~0~1~1
| opcode_LUI       => Ob~0~1~1~0~1~1~1
| opcode_AUIPC     => Ob~0~0~1~0~1~1~1
| opcode_JAL       => Ob~1~1~0~1~1~1~1
| opcode_SYSTEM    => Ob~1~1~1~0~0~1~1
| opcode_OP_32     => Ob~0~1~1~1~0~1~1
| opcode_OP_IMM_32 => Ob~0~0~1~1~0~1~1
| opcode_AMO       => Ob~0~1~0~1~1~1~1
| opcode_OP_FP     => Ob~1~0~1~0~0~1~1
| opcode_MADD      => Ob~1~0~0~0~0~1~1
| opcode_MSUB      => Ob~1~0~0~0~1~1~1
| opcode_NMSUB     => Ob~1~0~0~1~0~1~1
| opcode_NMADD     => Ob~1~0~0~1~1~1~1
| opcode_LOAD_FP   => Ob~0~0~0~0~1~1~1
| opcode_STORE_FP  => Ob~0~1~0~0~1~1~1
end.

Inductive funct3_name : Type :=
| funct3_ADD
| funct3_SUB
| funct3_SLL
| funct3_SLT
| funct3_SLTU
| funct3_XOR
| funct3_SRL
| funct3_SRA
| funct3_OR
| funct3_AND
| funct3_LB
| funct3_LH
| funct3_LW
| funct3_LBU
| funct3_LHU
| funct3_SLTI
| funct3_SLTIU
| funct3_ADDI
| funct3_XORI
| funct3_ORI
| funct3_ANDI
| funct3_SLLI
| funct3_SRLI
| funct3_SRAI
| funct3_FENCE
| funct3_SB
| funct3_SH
| funct3_SW
| funct3_BEQ
| funct3_BNE
| funct3_BLT
| funct3_BGE
| funct3_BLTU
| funct3_BGEU
| funct3_PRIV
| funct3_ADDW
| funct3_SUBW
| funct3_SLLW
| funct3_SRLW
| funct3_SRAW
| funct3_LWU
| funct3_LD
| funct3_ADDIW
| funct3_SLLIW
| funct3_SRLIW
| funct3_SRAIW
| funct3_SD
| funct3_FENCE_I
| funct3_CSRRW
| funct3_CSRRS
| funct3_CSRRC
| funct3_CSRRWI
| funct3_CSRRSI
| funct3_CSRRCI
| funct3_MUL
| funct3_MULH
| funct3_MULHSU
| funct3_MULHU
| funct3_DIV
| funct3_DIVU
| funct3_REM
| funct3_REMU
| funct3_MULW
| funct3_DIVW
| funct3_DIVUW
| funct3_REMW
| funct3_REMUW
| funct3_AMOW
| funct3_AMOD
| funct3_FSGNJ_S
| funct3_FSGNJN_S
| funct3_FSGNJX_S
| funct3_FMIN_S
| funct3_FMAX_S
| funct3_FMV_X_W
| funct3_FEQ_S
| funct3_FLT_S
| funct3_FLE_S
| funct3_FCLASS_S
| funct3_FLW
| funct3_FSW.

Definition funct3_bin (f : funct3_name) :=
match f with
| funct3_ADD      => Ob~0~0~0
| funct3_SUB      => Ob~0~0~0
| funct3_SLL      => Ob~0~0~1
| funct3_SLT      => Ob~0~1~0
| funct3_SLTU     => Ob~0~1~1
| funct3_XOR      => Ob~1~0~0
| funct3_SRL      => Ob~1~0~1
| funct3_SRA      => Ob~1~0~1
| funct3_OR       => Ob~1~1~0
| funct3_AND      => Ob~1~1~1
| funct3_LB       => Ob~0~0~0
| funct3_LH       => Ob~0~0~1
| funct3_LW       => Ob~0~1~0
| funct3_LBU      => Ob~1~0~0
| funct3_LHU      => Ob~1~0~1
| funct3_SLTI     => Ob~0~1~0
| funct3_SLTIU    => Ob~0~1~1
| funct3_ADDI     => Ob~0~0~0
| funct3_XORI     => Ob~1~0~0
| funct3_ORI      => Ob~1~1~0
| funct3_ANDI     => Ob~1~1~1
| funct3_SLLI     => Ob~0~0~1
| funct3_SRLI     => Ob~1~0~1
| funct3_SRAI     => Ob~1~0~1
| funct3_FENCE    => Ob~0~0~0
| funct3_SB       => Ob~0~0~0
| funct3_SH       => Ob~0~0~1
| funct3_SW       => Ob~0~1~0
| funct3_BEQ      => Ob~0~0~0
| funct3_BNE      => Ob~0~0~1
| funct3_BLT      => Ob~1~0~0
| funct3_BGE      => Ob~1~0~1
| funct3_BLTU     => Ob~1~1~0
| funct3_BGEU     => Ob~1~1~1
| funct3_PRIV     => Ob~0~0~0
| funct3_ADDW     => Ob~0~0~0
| funct3_SUBW     => Ob~0~0~0
| funct3_SLLW     => Ob~0~0~1
| funct3_SRLW     => Ob~1~0~1
| funct3_SRAW     => Ob~1~0~1
| funct3_LWU      => Ob~1~1~0
| funct3_LD       => Ob~0~1~1
| funct3_ADDIW    => Ob~0~0~0
| funct3_SLLIW    => Ob~0~0~1
| funct3_SRLIW    => Ob~1~0~1
| funct3_SRAIW    => Ob~1~0~1
| funct3_SD       => Ob~0~1~1
| funct3_FENCE_I  => Ob~0~0~1
| funct3_CSRRW    => Ob~0~0~1
| funct3_CSRRS    => Ob~0~1~0
| funct3_CSRRC    => Ob~0~1~1
| funct3_CSRRWI   => Ob~1~0~1
| funct3_CSRRSI   => Ob~1~1~0
| funct3_CSRRCI   => Ob~1~1~1
| funct3_MUL      => Ob~0~0~0
| funct3_MULH     => Ob~0~0~1
| funct3_MULHSU   => Ob~0~1~0
| funct3_MULHU    => Ob~0~1~1
| funct3_DIV      => Ob~1~0~0
| funct3_DIVU     => Ob~1~0~1
| funct3_REM      => Ob~1~1~0
| funct3_REMU     => Ob~1~1~1
| funct3_MULW     => Ob~0~0~0
| funct3_DIVW     => Ob~1~0~0
| funct3_DIVUW    => Ob~1~0~1
| funct3_REMW     => Ob~1~1~0
| funct3_REMUW    => Ob~1~1~1
| funct3_AMOW     => Ob~0~1~0
| funct3_AMOD     => Ob~0~1~1
| funct3_FSGNJ_S  => Ob~0~0~0
| funct3_FSGNJN_S => Ob~0~0~1
| funct3_FSGNJX_S => Ob~0~1~0
| funct3_FMIN_S   => Ob~0~0~0
| funct3_FMAX_S   => Ob~0~0~1
| funct3_FMV_X_W  => Ob~0~0~0
| funct3_FEQ_S    => Ob~0~1~0
| funct3_FLT_S    => Ob~0~0~1
| funct3_FLE_S    => Ob~0~0~0
| funct3_FCLASS_S => Ob~0~0~1
| funct3_FLW      => Ob~0~1~0
| funct3_FSW      => Ob~0~1~0
end.

Inductive funct7_name : Type :=
| funct7_ADD
| funct7_SUB
| funct7_SLL
| funct7_SLT
| funct7_SLTU
| funct7_XOR
| funct7_SRL
| funct7_SRA
| funct7_OR
| funct7_AND
| funct7_ADDW
| funct7_SUBW
| funct7_SLLW
| funct7_SRLW
| funct7_SRAW
| funct7_SLLIW
| funct7_SRLIW
| funct7_SRAIW
| funct7_MUL
| funct7_MULH
| funct7_MULHSU
| funct7_MULHU
| funct7_DIV
| funct7_DIVU
| funct7_REM
| funct7_REMU
| funct7_MULW
| funct7_DIVW
| funct7_DIVUW
| funct7_REMW
| funct7_REMUW
| funct7_FADD_S
| funct7_FSUB_S
| funct7_FMUL_S
| funct7_FDIV_S
| funct7_FSQRT_S
| funct7_FSGNJ_S
| funct7_FMIN_S
| funct7_FCVT_W_S
| funct7_FMV_X_W
| funct7_FEQ_S
| funct7_FCLASS_S
| funct7_FCVT_S_W
| funct7_FMV_W_X
| funct7_SFENCE_VMA.

Definition funct7_bin (f : funct7_name) :=
match f with
| funct7_ADD        => Ob~0~0~0~0~0~0~0
| funct7_SUB        => Ob~0~1~0~0~0~0~0
| funct7_SLL        => Ob~0~0~0~0~0~0~0
| funct7_SLT        => Ob~0~0~0~0~0~0~0
| funct7_SLTU       => Ob~0~0~0~0~0~0~0
| funct7_XOR        => Ob~0~0~0~0~0~0~0
| funct7_SRL        => Ob~0~0~0~0~0~0~0
| funct7_SRA        => Ob~0~1~0~0~0~0~0
| funct7_OR         => Ob~0~0~0~0~0~0~0
| funct7_AND        => Ob~0~0~0~0~0~0~0
| funct7_ADDW       => Ob~0~0~0~0~0~0~0
| funct7_SUBW       => Ob~0~1~0~0~0~0~0
| funct7_SLLW       => Ob~0~0~0~0~0~0~0
| funct7_SRLW       => Ob~0~0~0~0~0~0~0
| funct7_SRAW       => Ob~0~1~0~0~0~0~0
| funct7_SLLIW      => Ob~0~0~0~0~0~0~0
| funct7_SRLIW      => Ob~0~0~0~0~0~0~0
| funct7_SRAIW      => Ob~0~1~0~0~0~0~0
| funct7_MUL        => Ob~0~0~0~0~0~0~1
| funct7_MULH       => Ob~0~0~0~0~0~0~1
| funct7_MULHSU     => Ob~0~0~0~0~0~0~1
| funct7_MULHU      => Ob~0~0~0~0~0~0~1
| funct7_DIV        => Ob~0~0~0~0~0~0~1
| funct7_DIVU       => Ob~0~0~0~0~0~0~1
| funct7_REM        => Ob~0~0~0~0~0~0~1
| funct7_REMU       => Ob~0~0~0~0~0~0~1
| funct7_MULW       => Ob~0~0~0~0~0~0~1
| funct7_DIVW       => Ob~0~0~0~0~0~0~1
| funct7_DIVUW      => Ob~0~0~0~0~0~0~1
| funct7_REMW       => Ob~0~0~0~0~0~0~1
| funct7_REMUW      => Ob~0~0~0~0~0~0~1
| funct7_FADD_S     => Ob~0~0~0~0~0~0~0
| funct7_FSUB_S     => Ob~0~0~0~0~1~0~0
| funct7_FMUL_S     => Ob~0~0~0~1~0~0~0
| funct7_FDIV_S     => Ob~0~0~0~1~1~0~0
| funct7_FSQRT_S    => Ob~0~1~0~1~1~0~0
| funct7_FSGNJ_S    => Ob~0~0~1~0~0~0~0
| funct7_FMIN_S     => Ob~0~0~1~0~1~0~0
| funct7_FCVT_W_S   => Ob~1~1~0~0~0~0~0
| funct7_FMV_X_W    => Ob~1~1~1~0~0~0~0
| funct7_FEQ_S      => Ob~1~0~1~0~0~0~0
| funct7_FCLASS_S   => Ob~1~1~1~0~0~0~0
| funct7_FCVT_S_W   => Ob~1~1~0~1~0~0~0
| funct7_FMV_W_X    => Ob~1~1~1~1~0~0~0
| funct7_SFENCE_VMA => Ob~0~0~0~1~0~0~1
end.

Scheme Equality for instruction_field_name.

Module DecidableInstructionField <: DecidableType.
  Definition t := instruction_field_name.
  Definition eq := @eq instruction_field_name.
  Instance eq_equiv : @Equivalence instruction_field_name eq := eq_equivalence.
  Definition eq_dec := instruction_field_name_eq_dec.
End DecidableInstructionField.

Module FieldsSet <: WSetsOn DecidableInstructionField.
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

Definition instruction_type (i : instruction_internal_name) :=
  match i with
  | RV32I_instruction x =>
    match x with
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
    end
  | RV64I_instruction x =>
    match x with
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
    end
  | RV32Zifencei_instruction x =>
    match x with
    | FENCE_I_32Zifencei => IType
    end
  | RV64Zifencei_instruction x =>
    match x with
    | FENCE_I_64Zifencei => IType
    end
  | RV32Zicsr_instruction x =>
    match x with
    | CSRRW_32Zicsr  => IType
    | CSRRS_32Zicsr  => IType
    | CSRRC_32Zicsr  => IType
    | CSRRWI_32Zicsr => IType
    | CSRRSI_32Zicsr => IType
    | CSRRCI_32Zicsr => IType
    end
  | RV64Zicsr_instruction x =>
    match x with
    | CSRRW_64Zicsr  => IType
    | CSRRS_64Zicsr  => IType
    | CSRRC_64Zicsr  => IType
    | CSRRWI_64Zicsr => IType
    | CSRRSI_64Zicsr => IType
    | CSRRCI_64Zicsr => IType
    end
  | RV32M_instruction x =>
    match x with
    | MUL_32M    => RType
    | MULH_32M   => RType
    | MULHSU_32M => RType
    | MULHU_32M  => RType
    | DIV_32M    => RType
    | DIVU_32M   => RType
    | REM_32M    => RType
    | REMU_32M   => RType
    end
  | RV64M_instruction x =>
    match x with
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
    end
  | RV32A_instruction x =>
    match x with
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
    end
  | RV64A_instruction x =>
    match x with
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
    end
  | RV32F_instruction x =>
    match x with
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
    end
  | RV64F_instruction x =>
    match x with
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
    end
  | RV32D_instruction x =>
    match x with
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
    end
  | RV64D_instruction x =>
    match x with
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
    end
  | RV32Q_instruction x =>
    match x with
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
    end
  | RV64Q_instruction x =>
    match x with
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
    end
  end.

Definition instruction_name (i : instruction_internal_name) :=
  match i with
  | RV32I_instruction x =>
    match x with
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
    end
  | RV64I_instruction x =>
    match x with
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
    end
  | RV32Zifencei_instruction x =>
    match x with
    | FENCE_I_32Zifencei => "FENCE.I"
    end
  | RV64Zifencei_instruction x =>
    match x with
    | FENCE_I_64Zifencei => "FENCE.I"
    end
  | RV32Zicsr_instruction x =>
    match x with
    | CSRRW_32Zicsr  => "CSRRW"
    | CSRRS_32Zicsr  => "CSRRS"
    | CSRRC_32Zicsr  => "CSRRC"
    | CSRRWI_32Zicsr => "CSRRWI"
    | CSRRSI_32Zicsr => "CSRRSI"
    | CSRRCI_32Zicsr => "CSRRCI"
    end
  | RV64Zicsr_instruction x =>
    match x with
    | CSRRW_64Zicsr  => "CSRRW"
    | CSRRS_64Zicsr  => "CSRRS"
    | CSRRC_64Zicsr  => "CSRRC"
    | CSRRWI_64Zicsr => "CSRRWI"
    | CSRRSI_64Zicsr => "CSRRSI"
    | CSRRCI_64Zicsr => "CSRRCI"
    end
  | RV32M_instruction x =>
    match x with
    | MUL_32M    => "MUL"
    | MULH_32M   => "MULH"
    | MULHSU_32M => "MULHSU"
    | MULHU_32M  => "MULHU"
    | DIV_32M    => "DIV"
    | DIVU_32M   => "DIVU"
    | REM_32M    => "REM"
    | REMU_32M   => "REMU"
    end
  | RV64M_instruction x =>
    match x with
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
    end
  | RV32A_instruction x =>
    match x with
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
    end
  | RV64A_instruction x =>
    match x with
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
    end
  | RV32F_instruction x =>
    match x with
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
    end
  | RV64F_instruction x =>
    match x with
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
    end
  | RV32D_instruction x =>
    match x with
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
    end
  | RV64D_instruction x =>
    match x with
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
    end
  | RV32Q_instruction x =>
    match x with
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
    end
  | RV64Q_instruction x =>
    match x with
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
    end
  end.
