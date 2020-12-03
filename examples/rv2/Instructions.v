Require Import MSetInterface.

Require Import ISA.

(* Instructions *)
Inductive instruction_RV32I : Type :=
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
Scheme Equality for instruction_RV32I.

Inductive instruction_RV64I : Type :=
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
Scheme Equality for instruction_RV64I.

Inductive instruction_RV32Zifencei : Type :=
| FENCE_I_32Zifencei.
Scheme Equality for instruction_RV32Zifencei.

Inductive instruction_RV64Zifencei : Type :=
| FENCE_I_64Zifencei.
Scheme Equality for instruction_RV64Zifencei.

Inductive instruction_RV32Zicsr : Type :=
| CSRRW_32Zicsr
| CSRRS_32Zicsr
| CSRRC_32Zicsr
| CSRRWI_32Zicsr
| CSRRSI_32Zicsr
| CSRRCI_32Zicsr.
Scheme Equality for instruction_RV32Zicsr.

Inductive instruction_RV64Zicsr : Type :=
| CSRRW_64Zicsr
| CSRRS_64Zicsr
| CSRRC_64Zicsr
| CSRRWI_64Zicsr
| CSRRSI_64Zicsr
| CSRRCI_64Zicsr.
Scheme Equality for instruction_RV64Zicsr.

Inductive instruction_RV32M : Type :=
| MUL_32M
| MULH_32M
| MULHSU_32M
| MULHU_32M
| DIV_32M
| DIVU_32M
| REM_32M
| REMU_32M.
Scheme Equality for instruction_RV32M.

Inductive instruction_RV64M : Type :=
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
Scheme Equality for instruction_RV64M.

Inductive instruction_RV32A : Type :=
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
Scheme Equality for instruction_RV32A.

Inductive instruction_RV64A : Type :=
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
Scheme Equality for instruction_RV64A.

Inductive instruction_RV32F : Type :=
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
Scheme Equality for instruction_RV32F.

Inductive instruction_RV64F : Type :=
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
Scheme Equality for instruction_RV64F.

Inductive instruction_RV32D : Type :=
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
Scheme Equality for instruction_RV32D.

Inductive instruction_RV64D : Type :=
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
Scheme Equality for instruction_RV64D.

Inductive instruction_RV32Q : Type :=
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
Scheme Equality for instruction_RV32Q.

Inductive instruction_RV64Q : Type :=
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
Scheme Equality for instruction_RV64Q.

Inductive instruction : Type :=
| RV32I_instruction :
  instruction_RV32I -> instruction
| RV64I_instruction :
  instruction_RV64I -> instruction
| RV32Zifencei_instruction :
  instruction_RV32Zifencei -> instruction
| RV64Zifencei_instruction :
  instruction_RV64Zifencei -> instruction
| RV32Zicsr_instruction :
  instruction_RV32Zicsr -> instruction
| RV64Zicsr_instruction :
  instruction_RV64Zicsr -> instruction
| RV32M_instruction :
  instruction_RV32M -> instruction
| RV64M_instruction :
  instruction_RV64M -> instruction
| RV32A_instruction :
  instruction_RV32A -> instruction
| RV64A_instruction :
  instruction_RV64A -> instruction
| RV32F_instruction :
  instruction_RV32F -> instruction
| RV64F_instruction :
  instruction_RV64F -> instruction
| RV32D_instruction :
  instruction_RV32D -> instruction
| RV64D_instruction :
  instruction_RV64D -> instruction
| RV32Q_instruction :
  instruction_RV32Q -> instruction
| RV64Q_instruction :
  instruction_RV64Q -> instruction.

Module Decidable_instruction <: DecidableType.
  Definition t := instruction.
  Definition eq := @eq instruction.
  Instance eq_equiv : @Equivalence instruction eq :=
    eq_equivalence.
  Definition eq_dec : forall a b : instruction,
    {a = b} + {a <> b}.
  Proof. decide equality; decide equality. Defined.
End Decidable_instruction.

Module InstructionsSet
  <: WSetsOn Decidable_instruction.
  Include WSetsOn Decidable_instruction.
End InstructionsSet.

Definition RV32I_instructions : InstructionsSet.t :=
  (InstructionsSet.add (RV32I_instruction LUI_32I)
  (InstructionsSet.add (RV32I_instruction AUIPC_32I)
  (InstructionsSet.add (RV32I_instruction JAL_32I)
  (InstructionsSet.add (RV32I_instruction JALR_32I)
  (InstructionsSet.add (RV32I_instruction BEQ_32I)
  (InstructionsSet.add (RV32I_instruction BNE_32I)
  (InstructionsSet.add (RV32I_instruction BLT_32I)
  (InstructionsSet.add (RV32I_instruction BGE_32I)
  (InstructionsSet.add (RV32I_instruction BLTU_32I)
  (InstructionsSet.add (RV32I_instruction BGEU_32I)
  (InstructionsSet.add (RV32I_instruction LB_32I)
  (InstructionsSet.add (RV32I_instruction LH_32I)
  (InstructionsSet.add (RV32I_instruction LW_32I)
  (InstructionsSet.add (RV32I_instruction LBU_32I)
  (InstructionsSet.add (RV32I_instruction LHU_32I)
  (InstructionsSet.add (RV32I_instruction SB_32I)
  (InstructionsSet.add (RV32I_instruction SH_32I)
  (InstructionsSet.add (RV32I_instruction SW_32I)
  (InstructionsSet.add (RV32I_instruction ADDI_32I)
  (InstructionsSet.add (RV32I_instruction SLTI_32I)
  (InstructionsSet.add (RV32I_instruction SLTIU_32I)
  (InstructionsSet.add (RV32I_instruction XORI_32I)
  (InstructionsSet.add (RV32I_instruction ORI_32I)
  (InstructionsSet.add (RV32I_instruction ANDI_32I)
  (InstructionsSet.add (RV32I_instruction SLLI_32I)
  (InstructionsSet.add (RV32I_instruction SRLI_32I)
  (InstructionsSet.add (RV32I_instruction SRAI_32I)
  (InstructionsSet.add (RV32I_instruction ADD_32I)
  (InstructionsSet.add (RV32I_instruction SUB_32I)
  (InstructionsSet.add (RV32I_instruction SLL_32I)
  (InstructionsSet.add (RV32I_instruction SLT_32I)
  (InstructionsSet.add (RV32I_instruction SLTU_32I)
  (InstructionsSet.add (RV32I_instruction XOR_32I)
  (InstructionsSet.add (RV32I_instruction SRL_32I)
  (InstructionsSet.add (RV32I_instruction SRA_32I)
  (InstructionsSet.add (RV32I_instruction OR_32I)
  (InstructionsSet.add (RV32I_instruction AND_32I)
  (InstructionsSet.add (RV32I_instruction FENCE_32I)
  (InstructionsSet.add (RV32I_instruction ECALL_32I)
  (InstructionsSet.add (RV32I_instruction EBREAK_32I)
  InstructionsSet.empty)))))))))))))))))))))))))))))))))))))))).

Definition RV64I_instructions : InstructionsSet.t :=
  (InstructionsSet.add (RV64I_instruction LUI_64I)
  (InstructionsSet.add (RV64I_instruction AUIPC_64I)
  (InstructionsSet.add (RV64I_instruction JAL_64I)
  (InstructionsSet.add (RV64I_instruction JALR_64I)
  (InstructionsSet.add (RV64I_instruction BEQ_64I)
  (InstructionsSet.add (RV64I_instruction BNE_64I)
  (InstructionsSet.add (RV64I_instruction BLT_64I)
  (InstructionsSet.add (RV64I_instruction BGE_64I)
  (InstructionsSet.add (RV64I_instruction BLTU_64I)
  (InstructionsSet.add (RV64I_instruction BGEU_64I)
  (InstructionsSet.add (RV64I_instruction LB_64I)
  (InstructionsSet.add (RV64I_instruction LH_64I)
  (InstructionsSet.add (RV64I_instruction LW_64I)
  (InstructionsSet.add (RV64I_instruction LBU_64I)
  (InstructionsSet.add (RV64I_instruction LHU_64I)
  (InstructionsSet.add (RV64I_instruction SB_64I)
  (InstructionsSet.add (RV64I_instruction SH_64I)
  (InstructionsSet.add (RV64I_instruction SW_64I)
  (InstructionsSet.add (RV64I_instruction ADDI_64I)
  (InstructionsSet.add (RV64I_instruction SLTI_64I)
  (InstructionsSet.add (RV64I_instruction SLTIU_64I)
  (InstructionsSet.add (RV64I_instruction XORI_64I)
  (InstructionsSet.add (RV64I_instruction ORI_64I)
  (InstructionsSet.add (RV64I_instruction ANDI_64I)
  (InstructionsSet.add (RV64I_instruction SLLI_64I)
  (InstructionsSet.add (RV64I_instruction SRLI_64I)
  (InstructionsSet.add (RV64I_instruction SRAI_64I)
  (InstructionsSet.add (RV64I_instruction ADD_64I)
  (InstructionsSet.add (RV64I_instruction SUB_64I)
  (InstructionsSet.add (RV64I_instruction SLL_64I)
  (InstructionsSet.add (RV64I_instruction SLT_64I)
  (InstructionsSet.add (RV64I_instruction SLTU_64I)
  (InstructionsSet.add (RV64I_instruction XOR_64I)
  (InstructionsSet.add (RV64I_instruction SRL_64I)
  (InstructionsSet.add (RV64I_instruction SRA_64I)
  (InstructionsSet.add (RV64I_instruction OR_64I)
  (InstructionsSet.add (RV64I_instruction AND_64I)
  (InstructionsSet.add (RV64I_instruction FENCE_64I)
  (InstructionsSet.add (RV64I_instruction ECALL_64I)
  (InstructionsSet.add (RV64I_instruction EBREAK_64I)
  (InstructionsSet.add (RV64I_instruction LWU_64I)
  (InstructionsSet.add (RV64I_instruction LD_64I)
  (InstructionsSet.add (RV64I_instruction SD_64I)
  (InstructionsSet.add (RV64I_instruction ADDIW_64I)
  (InstructionsSet.add (RV64I_instruction SLLIW_64I)
  (InstructionsSet.add (RV64I_instruction SRLIW_64I)
  (InstructionsSet.add (RV64I_instruction SRAIW_64I)
  (InstructionsSet.add (RV64I_instruction ADDW_64I)
  (InstructionsSet.add (RV64I_instruction SUBW_64I)
  (InstructionsSet.add (RV64I_instruction SLLW_64I)
  (InstructionsSet.add (RV64I_instruction SRLW_64I)
  (InstructionsSet.add (RV64I_instruction SRAW_64I)
  InstructionsSet.empty)))))))))))))))))))))))))))))))))))))))))))))))))))).

Definition RV32Zifencei_instructions
  : InstructionsSet.t :=
  InstructionsSet.add (RV32Zifencei_instruction FENCE_I_32Zifencei)
  (InstructionsSet.empty).

Definition RV64Zifencei_instructions
  : InstructionsSet.t :=
  InstructionsSet.add (RV64Zifencei_instruction FENCE_I_64Zifencei)
    (InstructionsSet.empty).

Definition RV32Zicsr_instructions
  : InstructionsSet.t :=
  (InstructionsSet.add (RV32Zicsr_instruction CSRRW_32Zicsr)
  (InstructionsSet.add (RV32Zicsr_instruction CSRRS_32Zicsr)
  (InstructionsSet.add (RV32Zicsr_instruction CSRRC_32Zicsr)
  (InstructionsSet.add (RV32Zicsr_instruction CSRRWI_32Zicsr)
  (InstructionsSet.add (RV32Zicsr_instruction CSRRSI_32Zicsr)
  (InstructionsSet.add (RV32Zicsr_instruction CSRRCI_32Zicsr)
  InstructionsSet.empty)))))).

Definition RV64Zicsr_instructions
  : InstructionsSet.t :=
  (InstructionsSet.add (RV64Zicsr_instruction CSRRW_64Zicsr)
  (InstructionsSet.add (RV64Zicsr_instruction CSRRS_64Zicsr)
  (InstructionsSet.add (RV64Zicsr_instruction CSRRC_64Zicsr)
  (InstructionsSet.add (RV64Zicsr_instruction CSRRWI_64Zicsr)
  (InstructionsSet.add (RV64Zicsr_instruction CSRRSI_64Zicsr)
  (InstructionsSet.add (RV64Zicsr_instruction CSRRCI_64Zicsr)
  InstructionsSet.empty)))))).

Definition RV32M_instructions : InstructionsSet.t :=
  (InstructionsSet.add (RV32M_instruction MUL_32M)
  (InstructionsSet.add (RV32M_instruction MULH_32M)
  (InstructionsSet.add (RV32M_instruction MULHSU_32M)
  (InstructionsSet.add (RV32M_instruction MULHU_32M)
  (InstructionsSet.add (RV32M_instruction DIV_32M)
  (InstructionsSet.add (RV32M_instruction DIVU_32M)
  (InstructionsSet.add (RV32M_instruction REM_32M)
  (InstructionsSet.add (RV32M_instruction REMU_32M)
  InstructionsSet.empty)))))))).

Definition RV64M_instructions : InstructionsSet.t :=
  (InstructionsSet.add (RV64M_instruction MUL_64M)
  (InstructionsSet.add (RV64M_instruction MULH_64M)
  (InstructionsSet.add (RV64M_instruction MULHSU_64M)
  (InstructionsSet.add (RV64M_instruction MULHU_64M)
  (InstructionsSet.add (RV64M_instruction DIV_64M)
  (InstructionsSet.add (RV64M_instruction DIVU_64M)
  (InstructionsSet.add (RV64M_instruction REM_64M)
  (InstructionsSet.add (RV64M_instruction REMU_64M)
  (InstructionsSet.add (RV64M_instruction MULW_64M)
  (InstructionsSet.add (RV64M_instruction DIVW_64M)
  (InstructionsSet.add (RV64M_instruction DIVUW_64M)
  (InstructionsSet.add (RV64M_instruction REMW_64M)
  (InstructionsSet.add (RV64M_instruction REMUW_64M)
  InstructionsSet.empty))))))))))))).

Definition RV32A_instructions : InstructionsSet.t :=
  (InstructionsSet.add (RV32A_instruction LR_W_32A)
  (InstructionsSet.add (RV32A_instruction SC_W_32A)
  (InstructionsSet.add (RV32A_instruction AMOSWAP_W_32A)
  (InstructionsSet.add (RV32A_instruction AMOADD_W_32A)
  (InstructionsSet.add (RV32A_instruction AMOXOR_W_32A)
  (InstructionsSet.add (RV32A_instruction AMOAND_W_32A)
  (InstructionsSet.add (RV32A_instruction AMOOR_W_32A)
  (InstructionsSet.add (RV32A_instruction AMOMIN_W_32A)
  (InstructionsSet.add (RV32A_instruction AMOMAX_W_32A)
  (InstructionsSet.add (RV32A_instruction AMOMINU_W_32A)
  (InstructionsSet.add (RV32A_instruction AMOMAXU_W_32A)
  InstructionsSet.empty))))))))))).

Definition RV64A_instructions : InstructionsSet.t :=
  (InstructionsSet.add (RV64A_instruction LR_W_64A)
  (InstructionsSet.add (RV64A_instruction SC_W_64A)
  (InstructionsSet.add (RV64A_instruction AMOSWAP_W_64A)
  (InstructionsSet.add (RV64A_instruction AMOADD_W_64A)
  (InstructionsSet.add (RV64A_instruction AMOXOR_W_64A)
  (InstructionsSet.add (RV64A_instruction AMOAND_W_64A)
  (InstructionsSet.add (RV64A_instruction AMOOR_W_64A)
  (InstructionsSet.add (RV64A_instruction AMOMIN_W_64A)
  (InstructionsSet.add (RV64A_instruction AMOMAX_W_64A)
  (InstructionsSet.add (RV64A_instruction AMOMINU_W_64A)
  (InstructionsSet.add (RV64A_instruction AMOMAXU_W_64A)
  (InstructionsSet.add (RV64A_instruction LR_D_64A)
  (InstructionsSet.add (RV64A_instruction SC_D_64A)
  (InstructionsSet.add (RV64A_instruction AMOSWAP_D_64A)
  (InstructionsSet.add (RV64A_instruction AMOADD_D_64A)
  (InstructionsSet.add (RV64A_instruction AMOXOR_D_64A)
  (InstructionsSet.add (RV64A_instruction AMOAND_D_64A)
  (InstructionsSet.add (RV64A_instruction AMOOR_D_64A)
  (InstructionsSet.add (RV64A_instruction AMOMIN_D_64A)
  (InstructionsSet.add (RV64A_instruction AMOMAX_D_64A)
  (InstructionsSet.add (RV64A_instruction AMOMINU_D_64A)
  (InstructionsSet.add (RV64A_instruction AMOMAXU_D_64A)
  InstructionsSet.empty)))))))))))))))))))))).

Definition RV32F_instructions : InstructionsSet.t :=
  (InstructionsSet.add (RV32F_instruction FLW_32F)
  (InstructionsSet.add (RV32F_instruction FSW_32F)
  (InstructionsSet.add (RV32F_instruction FMADD_S_32F)
  (InstructionsSet.add (RV32F_instruction FMSUB_S_32F)
  (InstructionsSet.add (RV32F_instruction FNMSUB_S_32F)
  (InstructionsSet.add (RV32F_instruction FNMADD_S_32F)
  (InstructionsSet.add (RV32F_instruction FADD_S_32F)
  (InstructionsSet.add (RV32F_instruction FSUB_S_32F)
  (InstructionsSet.add (RV32F_instruction FMUL_S_32F)
  (InstructionsSet.add (RV32F_instruction FDIV_S_32F)
  (InstructionsSet.add (RV32F_instruction FSQRT_S_32F)
  (InstructionsSet.add (RV32F_instruction FSGNJ_S_32F)
  (InstructionsSet.add (RV32F_instruction FSGNJN_S_32F)
  (InstructionsSet.add (RV32F_instruction FSGNJX_S_32F)
  (InstructionsSet.add (RV32F_instruction FMIN_S_32F)
  (InstructionsSet.add (RV32F_instruction FMAX_S_32F)
  (InstructionsSet.add (RV32F_instruction FCVT_W_S_32F)
  (InstructionsSet.add (RV32F_instruction FCVT_WU_S_32F)
  (InstructionsSet.add (RV32F_instruction FMV_X_W_32F)
  (InstructionsSet.add (RV32F_instruction FEQ_S_32F)
  (InstructionsSet.add (RV32F_instruction FLT_S_32F)
  (InstructionsSet.add (RV32F_instruction FLE_S_32F)
  (InstructionsSet.add (RV32F_instruction FCLASS_S_32F)
  (InstructionsSet.add (RV32F_instruction FCVT_S_W_32F)
  (InstructionsSet.add (RV32F_instruction FCVT_S_WU_32F)
  (InstructionsSet.add (RV32F_instruction FMV_W_X_32F)
  InstructionsSet.empty)))))))))))))))))))))))))).

Definition RV64F_instructions : InstructionsSet.t :=
  (InstructionsSet.add (RV64F_instruction FLW_64F)
  (InstructionsSet.add (RV64F_instruction FSW_64F)
  (InstructionsSet.add (RV64F_instruction FMADD_S_64F)
  (InstructionsSet.add (RV64F_instruction FMSUB_S_64F)
  (InstructionsSet.add (RV64F_instruction FNMSUB_S_64F)
  (InstructionsSet.add (RV64F_instruction FNMADD_S_64F)
  (InstructionsSet.add (RV64F_instruction FADD_S_64F)
  (InstructionsSet.add (RV64F_instruction FSUB_S_64F)
  (InstructionsSet.add (RV64F_instruction FMUL_S_64F)
  (InstructionsSet.add (RV64F_instruction FDIV_S_64F)
  (InstructionsSet.add (RV64F_instruction FSQRT_S_64F)
  (InstructionsSet.add (RV64F_instruction FSGNJ_S_64F)
  (InstructionsSet.add (RV64F_instruction FSGNJN_S_64F)
  (InstructionsSet.add (RV64F_instruction FSGNJX_S_64F)
  (InstructionsSet.add (RV64F_instruction FMIN_S_64F)
  (InstructionsSet.add (RV64F_instruction FMAX_S_64F)
  (InstructionsSet.add (RV64F_instruction FCVT_W_S_64F)
  (InstructionsSet.add (RV64F_instruction FCVT_WU_S_64F)
  (InstructionsSet.add (RV64F_instruction FMV_X_W_64F)
  (InstructionsSet.add (RV64F_instruction FEQ_S_64F)
  (InstructionsSet.add (RV64F_instruction FLT_S_64F)
  (InstructionsSet.add (RV64F_instruction FLE_S_64F)
  (InstructionsSet.add (RV64F_instruction FCLASS_S_64F)
  (InstructionsSet.add (RV64F_instruction FCVT_S_W_64F)
  (InstructionsSet.add (RV64F_instruction FCVT_S_WU_64F)
  (InstructionsSet.add (RV64F_instruction FMV_W_X_64F)
  (InstructionsSet.add (RV64F_instruction FCVT_L_S_64F)
  (InstructionsSet.add (RV64F_instruction FCVT_LU_S_64F)
  (InstructionsSet.add (RV64F_instruction FCVT_S_L_64F)
  (InstructionsSet.add (RV64F_instruction FCVT_S_LU_64F)
  InstructionsSet.empty)))))))))))))))))))))))))))))).

Definition RV32D_instructions : InstructionsSet.t :=
  (InstructionsSet.add (RV32D_instruction FLD_32D)
  (InstructionsSet.add (RV32D_instruction FSD_32D)
  (InstructionsSet.add (RV32D_instruction FMADD_D_32D)
  (InstructionsSet.add (RV32D_instruction FMSUB_D_32D)
  (InstructionsSet.add (RV32D_instruction FNMSUB_D_32D)
  (InstructionsSet.add (RV32D_instruction FNMADD_D_32D)
  (InstructionsSet.add (RV32D_instruction FADD_D_32D)
  (InstructionsSet.add (RV32D_instruction FSUB_D_32D)
  (InstructionsSet.add (RV32D_instruction FMUL_D_32D)
  (InstructionsSet.add (RV32D_instruction FDIV_D_32D)
  (InstructionsSet.add (RV32D_instruction FSQRT_D_32D)
  (InstructionsSet.add (RV32D_instruction FSGNJ_D_32D)
  (InstructionsSet.add (RV32D_instruction FSGNJN_D_32D)
  (InstructionsSet.add (RV32D_instruction FSGNJX_D_32D)
  (InstructionsSet.add (RV32D_instruction FMIN_D_32D)
  (InstructionsSet.add (RV32D_instruction FMAX_D_32D)
  (InstructionsSet.add (RV32D_instruction FCVT_S_D_32D)
  (InstructionsSet.add (RV32D_instruction FCVT_D_S_32D)
  (InstructionsSet.add (RV32D_instruction FEQ_D_32D)
  (InstructionsSet.add (RV32D_instruction FLT_D_32D)
  (InstructionsSet.add (RV32D_instruction FLE_D_32D)
  (InstructionsSet.add (RV32D_instruction FCLASS_D_32D)
  (InstructionsSet.add (RV32D_instruction FCVT_W_D_32D)
  (InstructionsSet.add (RV32D_instruction FCVT_WU_D_32D)
  (InstructionsSet.add (RV32D_instruction FCVT_D_W_32D)
  (InstructionsSet.add (RV32D_instruction FCVT_D_WU_32D)
  InstructionsSet.empty)))))))))))))))))))))))))).

Definition RV64D_instructions : InstructionsSet.t :=
  (InstructionsSet.add (RV64D_instruction FLD_64D)
  (InstructionsSet.add (RV64D_instruction FSD_64D)
  (InstructionsSet.add (RV64D_instruction FMADD_D_64D)
  (InstructionsSet.add (RV64D_instruction FMSUB_D_64D)
  (InstructionsSet.add (RV64D_instruction FNMSUB_D_64D)
  (InstructionsSet.add (RV64D_instruction FNMADD_D_64D)
  (InstructionsSet.add (RV64D_instruction FADD_D_64D)
  (InstructionsSet.add (RV64D_instruction FSUB_D_64D)
  (InstructionsSet.add (RV64D_instruction FMUL_D_64D)
  (InstructionsSet.add (RV64D_instruction FDIV_D_64D)
  (InstructionsSet.add (RV64D_instruction FSQRT_D_64D)
  (InstructionsSet.add (RV64D_instruction FSGNJ_D_64D)
  (InstructionsSet.add (RV64D_instruction FSGNJN_D_64D)
  (InstructionsSet.add (RV64D_instruction FSGNJX_D_64D)
  (InstructionsSet.add (RV64D_instruction FMIN_D_64D)
  (InstructionsSet.add (RV64D_instruction FMAX_D_64D)
  (InstructionsSet.add (RV64D_instruction FCVT_S_D_64D)
  (InstructionsSet.add (RV64D_instruction FCVT_D_S_64D)
  (InstructionsSet.add (RV64D_instruction FEQ_D_64D)
  (InstructionsSet.add (RV64D_instruction FLT_D_64D)
  (InstructionsSet.add (RV64D_instruction FLE_D_64D)
  (InstructionsSet.add (RV64D_instruction FCLASS_D_64D)
  (InstructionsSet.add (RV64D_instruction FCVT_W_D_64D)
  (InstructionsSet.add (RV64D_instruction FCVT_WU_D_64D)
  (InstructionsSet.add (RV64D_instruction FCVT_D_W_64D)
  (InstructionsSet.add (RV64D_instruction FCVT_D_WU_64D)
  (InstructionsSet.add (RV64D_instruction FCVT_L_D_64D)
  (InstructionsSet.add (RV64D_instruction FCVT_LU_D_64D)
  (InstructionsSet.add (RV64D_instruction FMV_X_D_64D)
  (InstructionsSet.add (RV64D_instruction FCVT_D_L_64D)
  (InstructionsSet.add (RV64D_instruction FCVT_D_LU_64D)
  (InstructionsSet.add (RV64D_instruction FMV_D_X_64D)
  InstructionsSet.empty)))))))))))))))))))))))))))))))).

Definition RV32Q_instructions : InstructionsSet.t :=
  (InstructionsSet.add (RV32Q_instruction FLQ_32Q)
  (InstructionsSet.add (RV32Q_instruction FSQ_32Q)
  (InstructionsSet.add (RV32Q_instruction FMADD_Q_32Q)
  (InstructionsSet.add (RV32Q_instruction FMSUB_Q_32Q)
  (InstructionsSet.add (RV32Q_instruction FNMSUB_Q_32Q)
  (InstructionsSet.add (RV32Q_instruction FNMADD_Q_32Q)
  (InstructionsSet.add (RV32Q_instruction FADD_Q_32Q)
  (InstructionsSet.add (RV32Q_instruction FSUB_Q_32Q)
  (InstructionsSet.add (RV32Q_instruction FMUL_Q_32Q)
  (InstructionsSet.add (RV32Q_instruction FDIV_Q_32Q)
  (InstructionsSet.add (RV32Q_instruction FSQRT_Q_32Q)
  (InstructionsSet.add (RV32Q_instruction FSGNJ_Q_32Q)
  (InstructionsSet.add (RV32Q_instruction FSGNJN_Q_32Q)
  (InstructionsSet.add (RV32Q_instruction FSGNJX_Q_32Q)
  (InstructionsSet.add (RV32Q_instruction FMIN_Q_32Q)
  (InstructionsSet.add (RV32Q_instruction FMAX_Q_32Q)
  (InstructionsSet.add (RV32Q_instruction FCVT_S_Q_32Q)
  (InstructionsSet.add (RV32Q_instruction FCVT_Q_S_32Q)
  (InstructionsSet.add (RV32Q_instruction FCVT_D_Q_32Q)
  (InstructionsSet.add (RV32Q_instruction FCVT_Q_D_32Q)
  (InstructionsSet.add (RV32Q_instruction FEQ_Q_32Q)
  (InstructionsSet.add (RV32Q_instruction FLT_Q_32Q)
  (InstructionsSet.add (RV32Q_instruction FLE_Q_32Q)
  (InstructionsSet.add (RV32Q_instruction FCLASS_Q_32Q)
  (InstructionsSet.add (RV32Q_instruction FCVT_W_Q_32Q)
  (InstructionsSet.add (RV32Q_instruction FCVT_WU_Q_32Q)
  (InstructionsSet.add (RV32Q_instruction FCVT_Q_W_32Q)
  (InstructionsSet.add (RV32Q_instruction FCVT_Q_WU_32Q)
  InstructionsSet.empty)))))))))))))))))))))))))))).

Definition RV64Q_instructions : InstructionsSet.t :=
  (InstructionsSet.add (RV64Q_instruction FLQ_64Q)
  (InstructionsSet.add (RV64Q_instruction FSQ_64Q)
  (InstructionsSet.add (RV64Q_instruction FMADD_Q_64Q)
  (InstructionsSet.add (RV64Q_instruction FMSUB_Q_64Q)
  (InstructionsSet.add (RV64Q_instruction FNMSUB_Q_64Q)
  (InstructionsSet.add (RV64Q_instruction FNMADD_Q_64Q)
  (InstructionsSet.add (RV64Q_instruction FADD_Q_64Q)
  (InstructionsSet.add (RV64Q_instruction FSUB_Q_64Q)
  (InstructionsSet.add (RV64Q_instruction FMUL_Q_64Q)
  (InstructionsSet.add (RV64Q_instruction FDIV_Q_64Q)
  (InstructionsSet.add (RV64Q_instruction FSQRT_Q_64Q)
  (InstructionsSet.add (RV64Q_instruction FSGNJ_Q_64Q)
  (InstructionsSet.add (RV64Q_instruction FSGNJN_Q_64Q)
  (InstructionsSet.add (RV64Q_instruction FSGNJX_Q_64Q)
  (InstructionsSet.add (RV64Q_instruction FMIN_Q_64Q)
  (InstructionsSet.add (RV64Q_instruction FMAX_Q_64Q)
  (InstructionsSet.add (RV64Q_instruction FCVT_S_Q_64Q)
  (InstructionsSet.add (RV64Q_instruction FCVT_Q_S_64Q)
  (InstructionsSet.add (RV64Q_instruction FCVT_D_Q_64Q)
  (InstructionsSet.add (RV64Q_instruction FCVT_Q_D_64Q)
  (InstructionsSet.add (RV64Q_instruction FEQ_Q_64Q)
  (InstructionsSet.add (RV64Q_instruction FLT_Q_64Q)
  (InstructionsSet.add (RV64Q_instruction FLE_Q_64Q)
  (InstructionsSet.add (RV64Q_instruction FCLASS_Q_64Q)
  (InstructionsSet.add (RV64Q_instruction FCVT_W_Q_64Q)
  (InstructionsSet.add (RV64Q_instruction FCVT_WU_Q_64Q)
  (InstructionsSet.add (RV64Q_instruction FCVT_Q_W_64Q)
  (InstructionsSet.add (RV64Q_instruction FCVT_Q_WU_64Q)
  (InstructionsSet.add (RV64Q_instruction FCVT_L_Q_64Q)
  (InstructionsSet.add (RV64Q_instruction FCVT_LU_Q_64Q)
  (InstructionsSet.add (RV64Q_instruction FCVT_Q_L_64Q)
  (InstructionsSet.add (RV64Q_instruction FCVT_Q_LU_64Q)
  InstructionsSet.empty)))))))))))))))))))))))))))))))).


Definition extension_instructions_set (b : base_standard) (e : extension) :=
  match b with
  | RV32I =>
    match e with
    | RVM        => RV32M_instructions
    | RVA        => RV32A_instructions
    | RVF        => RV32F_instructions
    | RVD        => RV32D_instructions
    | RVQ        => RV32Q_instructions
    | RVZiCSR    => RV32Zicsr_instructions
    | RVZifencei => RV32Zifencei_instructions
    end
  | RV64I =>
    match e with
    | RVM        => RV64M_instructions
    | RVA        => RV64A_instructions
    | RVF        => RV64F_instructions
    | RVD        => RV64D_instructions
    | RVQ        => RV64Q_instructions
    | RVZiCSR    => RV64Zicsr_instructions
    | RVZifencei => RV64Zifencei_instructions
    end
  end.

Definition foldable_extension_instructions_set
  (b : base_standard) (e : extension) (i : InstructionsSet.t)
:=
  InstructionsSet.union i (extension_instructions_set b e).

Definition ISA_instructions_set (isa : ISA) :=
  InstructionsSet.union (
    match (ISA_base_standard isa) with
    | RV32I => RV32I_instructions
    | RV64I => RV64I_instructions
    end
  )
  (
    ExtensionsSet.fold
      (foldable_extension_instructions_set (ISA_base_standard isa))
      (ISA_activated_extensions isa) InstructionsSet.empty
  ).

Definition instruction_name (i : instruction) :=
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
