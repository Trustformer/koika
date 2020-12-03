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
