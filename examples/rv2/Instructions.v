Require Import Strings.String List.
Import ListNotations.

Require Import ISA.

Inductive instruction_RV32I :=
| LUI_32I  | AUIPC_32I | JAL_32I   | JALR_32I | BEQ_32I | BNE_32I
| BLT_32I  | BGE_32I   | BLTU_32I  | BGEU_32I | LB_32I  | LH_32I
| LW_32I   | LBU_32I   | LHU_32I   | SB_32I   | SH_32I  | SW_32I
| ADDI_32I | SLTI_32I  | SLTIU_32I | XORI_32I | ORI_32I | ANDI_32I
| SLLI_32I | SRLI_32I  | SRAI_32I  | ADD_32I  | SUB_32I | SLL_32I
| SLT_32I  | SLTU_32I  | XOR_32I   | SRL_32I  | SRA_32I | OR_32I
| AND_32I  | FENCE_32I | ECALL_32I | EBREAK_32I.
Inductive instruction_RV64I :=
| LUI_64I  | AUIPC_64I | JAL_64I   | JALR_64I   | BEQ_64I   | BNE_64I
| BLT_64I  | BGE_64I   | BLTU_64I  | BGEU_64I   | LB_64I    | LH_64I
| LW_64I   | LBU_64I   | LHU_64I   | SB_64I     | SH_64I    | SW_64I
| ADDI_64I | SLTI_64I  | SLTIU_64I | XORI_64I   | ORI_64I   | ANDI_64I
| SLLI_64I | SRLI_64I  | SRAI_64I  | ADD_64I    | SUB_64I   | SLL_64I
| SLT_64I  | SLTU_64I  | XOR_64I   | SRL_64I    | SRA_64I   | OR_64I
| AND_64I  | FENCE_64I | ECALL_64I | EBREAK_64I | LWU_64I   | LD_64I
| SD_64I   | ADDIW_64I | SLLIW_64I | SRLIW_64I  | SRAIW_64I | ADDW_64I
| SUBW_64I | SLLW_64I  | SRLW_64I  | SRAW_64I.
Inductive instruction_RV32Zifencei := FENCE_I_32Zifencei.
Inductive instruction_RV64Zifencei := FENCE_I_64Zifencei.
Inductive instruction_RV32Zicsr :=
| CSRRW_32Zicsr  | CSRRS_32Zicsr | CSRRC_32Zicsr | CSRRWI_32Zicsr
| CSRRSI_32Zicsr | CSRRCI_32Zicsr.
Inductive instruction_RV64Zicsr :=
| CSRRW_64Zicsr  | CSRRS_64Zicsr | CSRRC_64Zicsr | CSRRWI_64Zicsr
| CSRRSI_64Zicsr | CSRRCI_64Zicsr.
Inductive instruction_RV32M :=
| MUL_32M | MULH_32M | MULHSU_32M | MULHU_32M | DIV_32M | DIVU_32M | REM_32M
| REMU_32M.
Inductive instruction_RV64M :=
| MUL_64M    | MULH_64M | MULHSU_64M | MULHU_64M | DIV_64M   | DIVU_64M
| REM_64M    | REMU_64M | MULW_64M   | DIVW_64M  | DIVUW_64M | REMW_64M
| REMUW_64M.
Inductive instruction_RV32A :=
| LR_W_00_32A      | LR_W_01_32A      | LR_W_10_32A      | LR_W_11_32A
| SC_W_00_32A      | SC_W_01_32A      | SC_W_10_32A      | SC_W_11_32A
| AMOSWAP_W_00_32A | AMOSWAP_W_01_32A | AMOSWAP_W_10_32A | AMOSWAP_W_11_32A
| AMOADD_W_00_32A  | AMOADD_W_01_32A  | AMOADD_W_10_32A  | AMOADD_W_11_32A
| AMOXOR_W_00_32A  | AMOXOR_W_01_32A  | AMOXOR_W_10_32A  | AMOXOR_W_11_32A
| AMOAND_W_00_32A  | AMOAND_W_01_32A  | AMOAND_W_10_32A  | AMOAND_W_11_32A
| AMOOR_W_00_32A   | AMOOR_W_01_32A   | AMOOR_W_10_32A   | AMOOR_W_11_32A
| AMOMIN_W_00_32A  | AMOMIN_W_01_32A  | AMOMIN_W_10_32A  | AMOMIN_W_11_32A
| AMOMAX_W_00_32A  | AMOMAX_W_01_32A  | AMOMAX_W_10_32A  | AMOMAX_W_11_32A
| AMOMINU_W_00_32A | AMOMINU_W_01_32A | AMOMINU_W_10_32A | AMOMINU_W_11_32A
| AMOMAXU_W_00_32A | AMOMAXU_W_01_32A | AMOMAXU_W_10_32A | AMOMAXU_W_11_32A.
Inductive instruction_RV64A :=
| LR_W_00_64A      | LR_W_01_64A      | LR_W_10_64A      | LR_W_11_64A
| SC_W_00_64A      | SC_W_01_64A      | SC_W_10_64A      | SC_W_11_64A
| AMOSWAP_W_00_64A | AMOSWAP_W_01_64A | AMOSWAP_W_10_64A | AMOSWAP_W_11_64A
| AMOADD_W_00_64A  | AMOADD_W_01_64A  | AMOADD_W_10_64A  | AMOADD_W_11_64A
| AMOXOR_W_00_64A  | AMOXOR_W_01_64A  | AMOXOR_W_10_64A  | AMOXOR_W_11_64A
| AMOAND_W_00_64A  | AMOAND_W_01_64A  | AMOAND_W_10_64A  | AMOAND_W_11_64A
| AMOOR_W_00_64A   | AMOOR_W_01_64A   | AMOOR_W_10_64A   | AMOOR_W_11_64A
| AMOMIN_W_00_64A  | AMOMIN_W_01_64A  | AMOMIN_W_10_64A  | AMOMIN_W_11_64A
| AMOMAX_W_00_64A  | AMOMAX_W_01_64A  | AMOMAX_W_10_64A  | AMOMAX_W_11_64A
| AMOMINU_W_00_64A | AMOMINU_W_01_64A | AMOMINU_W_10_64A | AMOMINU_W_11_64A
| AMOMAXU_W_00_64A | AMOMAXU_W_01_64A | AMOMAXU_W_10_64A | AMOMAXU_W_11_64A
| LR_D_00_64A      | LR_D_01_64A      | LR_D_10_64A      | LR_D_11_64A
| SC_D_00_64A      | SC_D_01_64A      | SC_D_10_64A      | SC_D_11_64A
| AMOSWAP_D_00_64A | AMOSWAP_D_01_64A | AMOSWAP_D_10_64A | AMOSWAP_D_11_64A
| AMOADD_D_00_64A  | AMOADD_D_01_64A  | AMOADD_D_10_64A  | AMOADD_D_11_64A
| AMOXOR_D_00_64A  | AMOXOR_D_01_64A  | AMOXOR_D_10_64A  | AMOXOR_D_11_64A
| AMOAND_D_00_64A  | AMOAND_D_01_64A  | AMOAND_D_10_64A  | AMOAND_D_11_64A
| AMOOR_D_00_64A   | AMOOR_D_01_64A   | AMOOR_D_10_64A   | AMOOR_D_11_64A
| AMOMIN_D_00_64A  | AMOMIN_D_01_64A  | AMOMIN_D_10_64A  | AMOMIN_D_11_64A
| AMOMAX_D_00_64A  | AMOMAX_D_01_64A  | AMOMAX_D_10_64A  | AMOMAX_D_11_64A
| AMOMINU_D_00_64A | AMOMINU_D_01_64A | AMOMINU_D_10_64A | AMOMINU_D_11_64A
| AMOMAXU_D_00_64A | AMOMAXU_D_01_64A | AMOMAXU_D_10_64A | AMOMAXU_D_11_64A.
Inductive instruction_RV32F :=
| FLW_32F           | FSW_32F           | FMADD_RNE_S_32F   | FMADD_RTZ_S_32F
| FMADD_RDN_S_32F   | FMADD_RUP_S_32F   | FMADD_RMM_S_32F   | FMADD_DYN_S_32F
| FMSUB_RNE_S_32F   | FMSUB_RTZ_S_32F   | FMSUB_RDN_S_32F   | FMSUB_RUP_S_32F
| FMSUB_RMM_S_32F   | FMSUB_DYN_S_32F   | FNMSUB_RNE_S_32F  | FNMSUB_RTZ_S_32F
| FNMSUB_RDN_S_32F  | FNMSUB_RUP_S_32F  | FNMSUB_RMM_S_32F  | FNMSUB_DYN_S_32F
| FNMADD_RNE_S_32F  | FNMADD_RTZ_S_32F  | FNMADD_RDN_S_32F  | FNMADD_RUP_S_32F
| FNMADD_RMM_S_32F  | FNMADD_DYN_S_32F  | FADD_RNE_S_32F    | FADD_RTZ_S_32F
| FADD_RDN_S_32F    | FADD_RUP_S_32F    | FADD_RMM_S_32F    | FADD_DYN_S_32F
| FSUB_RNE_S_32F    | FSUB_RTZ_S_32F    | FSUB_RDN_S_32F    | FSUB_RUP_S_32F
| FSUB_RMM_S_32F    | FSUB_DYN_S_32F    | FMUL_RNE_S_32F    | FMUL_RTZ_S_32F
| FMUL_RDN_S_32F    | FMUL_RUP_S_32F    | FMUL_RMM_S_32F    | FMUL_DYN_S_32F
| FDIV_RNE_S_32F    | FDIV_RTZ_S_32F    | FDIV_RDN_S_32F    | FDIV_RUP_S_32F
| FDIV_RMM_S_32F    | FDIV_DYN_S_32F    | FSQRT_RNE_S_32F   | FSQRT_RTZ_S_32F
| FSQRT_RDN_S_32F   | FSQRT_RUP_S_32F   | FSQRT_RMM_S_32F   | FSQRT_DYN_S_32F
| FSGNJ_S_32F       | FSGNJN_S_32F      | FSGNJX_S_32F      | FMIN_S_32F
| FMAX_S_32F        | FCVT_RNE_W_S_32F  | FCVT_RTZ_W_S_32F  | FCVT_RDN_W_S_32F
| FCVT_RUP_W_S_32F  | FCVT_RMM_W_S_32F  | FCVT_DYN_W_S_32F  | FCVT_RNE_WU_S_32F
| FCVT_RTZ_WU_S_32F | FCVT_RDN_WU_S_32F | FCVT_RUP_WU_S_32F | FCVT_RMM_WU_S_32F
| FCVT_DYN_WU_S_32F | FMV_X_W_32F       | FEQ_S_32F         | FLT_S_32F
| FLE_S_32F         | FCLASS_S_32F      | FCVT_RNE_S_W_32F  | FCVT_RTZ_S_W_32F
| FCVT_RDN_S_W_32F  | FCVT_RUP_S_W_32F  | FCVT_RMM_S_W_32F  | FCVT_DYN_S_W_32F
| FCVT_RNE_S_WU_32F | FCVT_RTZ_S_WU_32F | FCVT_RDN_S_WU_32F | FCVT_RUP_S_WU_32F
| FCVT_RMM_S_WU_32F | FCVT_DYN_S_WU_32F | FMV_W_X_32F.
Inductive instruction_RV64F :=
| FLW_64F           | FSW_64F           | FMADD_RNE_S_64F    | FMADD_RTZ_S_64F
| FMADD_RDN_S_64F   | FMADD_RUP_S_64F   | FMADD_RMM_S_64F    | FMADD_DYN_S_64F
| FMSUB_RNE_S_64F   | FMSUB_RTZ_S_64F   | FMSUB_RDN_S_64F    | FMSUB_RUP_S_64F
| FMSUB_RMM_S_64F   | FMSUB_DYN_S_64F   | FNMSUB_RNE_S_64F   | FNMSUB_RTZ_S_64F
| FNMSUB_RDN_S_64F  | FNMSUB_RUP_S_64F  | FNMSUB_RMM_S_64F   | FNMSUB_DYN_S_64F
| FNMADD_RNE_S_64F  | FNMADD_RTZ_S_64F  | FNMADD_RDN_S_64F   | FNMADD_RUP_S_64F
| FNMADD_RMM_S_64F  | FNMADD_DYN_S_64F  | FADD_RNE_S_64F     | FADD_RTZ_S_64F
| FADD_RDN_S_64F    | FADD_RUP_S_64F    | FADD_RMM_S_64F     | FADD_DYN_S_64F
| FSUB_RNE_S_64F    | FSUB_RTZ_S_64F    | FSUB_RDN_S_64F     | FSUB_RUP_S_64F
| FSUB_RMM_S_64F    | FSUB_DYN_S_64F    | FMUL_RNE_S_64F     | FMUL_RTZ_S_64F
| FMUL_RDN_S_64F    | FMUL_RUP_S_64F    | FMUL_RMM_S_64F     | FMUL_DYN_S_64F
| FDIV_RNE_S_64F    | FDIV_RTZ_S_64F    | FDIV_RDN_S_64F     | FDIV_RUP_S_64F
| FDIV_RMM_S_64F    | FDIV_DYN_S_64F    | FSQRT_RNE_S_64F    | FSQRT_RTZ_S_64F
| FSQRT_RDN_S_64F   | FSQRT_RUP_S_64F   | FSQRT_RMM_S_64F    | FSQRT_DYN_S_64F
| FSGNJ_S_64F       | FSGNJN_S_64F      | FSGNJX_S_64F       | FMIN_S_64F
| FMAX_S_64F        | FCVT_RNE_W_S_64F  | FCVT_RTZ_W_S_64F   | FCVT_RDN_W_S_64F
| FCVT_RUP_W_S_64F  | FCVT_RMM_W_S_64F  | FCVT_DYN_W_S_64F   | FCVT_RNE_WU_S_64F
| FCVT_RTZ_WU_S_64F | FCVT_RDN_WU_S_64F | FCVT_RUP_WU_S_64F  | FCVT_RMM_WU_S_64F
| FCVT_DYN_WU_S_64F | FMV_X_W_64F       | FEQ_S_64F          | FLT_S_64F
| FLE_S_64F         | FCLASS_S_64F      | FCVT_RNE_S_W_64F   | FCVT_RTZ_S_W_64F
| FCVT_RDN_S_W_64F  | FCVT_RUP_S_W_64F  | FCVT_RMM_S_W_64F   | FCVT_DYN_S_W_64F
| FCVT_RNE_S_WU_64F | FCVT_RTZ_S_WU_64F | FCVT_RDN_S_WU_64F  | FCVT_RUP_S_WU_64F
| FCVT_RMM_S_WU_64F | FCVT_DYN_S_WU_64F | FMV_W_X_64F        | FCVT_RNE_L_S_64F
| FCVT_RTZ_L_S_64F  | FCVT_RDN_L_S_64F  | FCVT_RUP_L_S_64F   | FCVT_RMM_L_S_64F
| FCVT_DYN_L_S_64F  | FCVT_RNE_LU_S_64F | FCVT_RTZ_LU_S_64F  | FCVT_RDN_LU_S_64F
| FCVT_RUP_LU_S_64F | FCVT_RMM_LU_S_64F | FCVT_DYN_LU_S_64F  | FCVT_RNE_S_L_64F
| FCVT_RTZ_S_L_64F  | FCVT_RDN_S_L_64F  | FCVT_RUP_S_L_64F   | FCVT_RMM_S_L_64F
| FCVT_DYN_S_L_64F  | FCVT_RNE_S_LU_64F | FCVT_RTZ_S_LU_64F  | FCVT_RDN_S_LU_64F
| FCVT_RUP_S_LU_64F | FCVT_RMM_S_LU_64F | FCVT_DYN_S_LU_64F.
Inductive instruction_RV32D :=
| FLD_32D           | FSD_32D           | FMADD_RNE_D_32D   | FMADD_RTZ_D_32D
| FMADD_RDN_D_32D   | FMADD_RUP_D_32D   | FMADD_RMM_D_32D   | FMADD_DYN_D_32D
| FMSUB_RNE_D_32D   | FMSUB_RTZ_D_32D   | FMSUB_RDN_D_32D   | FMSUB_RUP_D_32D
| FMSUB_RMM_D_32D   | FMSUB_DYN_D_32D   | FNMSUB_RNE_D_32D  | FNMSUB_RTZ_D_32D
| FNMSUB_RDN_D_32D  | FNMSUB_RUP_D_32D  | FNMSUB_RMM_D_32D  | FNMSUB_DYN_D_32D
| FNMADD_RNE_D_32D  | FNMADD_RTZ_D_32D  | FNMADD_RDN_D_32D  | FNMADD_RUP_D_32D
| FNMADD_RMM_D_32D  | FNMADD_DYN_D_32D  | FADD_RNE_D_32D    | FADD_RTZ_D_32D
| FADD_RDN_D_32D    | FADD_RUP_D_32D    | FADD_RMM_D_32D    | FADD_DYN_D_32D
| FSUB_RNE_D_32D    | FSUB_RTZ_D_32D    | FSUB_RDN_D_32D    | FSUB_RUP_D_32D
| FSUB_RMM_D_32D    | FSUB_DYN_D_32D    | FMUL_RNE_D_32D    | FMUL_RTZ_D_32D
| FMUL_RDN_D_32D    | FMUL_RUP_D_32D    | FMUL_RMM_D_32D    | FMUL_DYN_D_32D
| FDIV_RNE_D_32D    | FDIV_RTZ_D_32D    | FDIV_RDN_D_32D    | FDIV_RUP_D_32D
| FDIV_RMM_D_32D    | FDIV_DYN_D_32D    | FSQRT_RNE_D_32D   | FSQRT_RTZ_D_32D
| FSQRT_RDN_D_32D   | FSQRT_RUP_D_32D   | FSQRT_RMM_D_32D   | FSQRT_DYN_D_32D
| FSGNJ_D_32D       | FSGNJN_D_32D      | FSGNJX_D_32D      | FMIN_D_32D
| FMAX_D_32D        | FCVT_RNE_S_D_32D  | FCVT_RTZ_S_D_32D  | FCVT_RDN_S_D_32D
| FCVT_RUP_S_D_32D  | FCVT_RMM_S_D_32D  | FCVT_DYN_S_D_32D  | FCVT_RNE_D_S_32D
| FCVT_RTZ_D_S_32D  | FCVT_RDN_D_S_32D  | FCVT_RUP_D_S_32D  | FCVT_RMM_D_S_32D
| FCVT_DYN_D_S_32D  | FEQ_D_32D         | FLT_D_32D         | FLE_D_32D
| FCLASS_D_32D      | FCVT_RNE_W_D_32D  | FCVT_RTZ_W_D_32D  | FCVT_RDN_W_D_32D
| FCVT_RUP_W_D_32D  | FCVT_RMM_W_D_32D  | FCVT_DYN_W_D_32D  | FCVT_RNE_WU_D_32D
| FCVT_RTZ_WU_D_32D | FCVT_RDN_WU_D_32D | FCVT_RUP_WU_D_32D | FCVT_RMM_WU_D_32D
| FCVT_DYN_WU_D_32D | FCVT_RNE_D_W_32D  | FCVT_RTZ_D_W_32D  | FCVT_RDN_D_W_32D
| FCVT_RUP_D_W_32D  | FCVT_RMM_D_W_32D  | FCVT_DYN_D_W_32D  | FCVT_RNE_D_WU_32D
| FCVT_RTZ_D_WU_32D | FCVT_RDN_D_WU_32D | FCVT_RUP_D_WU_32D | FCVT_RMM_D_WU_32D
| FCVT_DYN_D_WU_32D.
Inductive instruction_RV64D :=
| FLD_64D           | FSD_64D           | FMADD_RNE_D_64D   | FMADD_RTZ_D_64D
| FMADD_RDN_D_64D   | FMADD_RUP_D_64D   | FMADD_RMM_D_64D   | FMADD_DYN_D_64D
| FMSUB_RNE_D_64D   | FMSUB_RTZ_D_64D   | FMSUB_RDN_D_64D   | FMSUB_RUP_D_64D
| FMSUB_RMM_D_64D   | FMSUB_DYN_D_64D   | FNMSUB_RNE_D_64D  | FNMSUB_RTZ_D_64D
| FNMSUB_RDN_D_64D  | FNMSUB_RUP_D_64D  | FNMSUB_RMM_D_64D  | FNMSUB_DYN_D_64D
| FNMADD_RNE_D_64D  | FNMADD_RTZ_D_64D  | FNMADD_RDN_D_64D  | FNMADD_RUP_D_64D
| FNMADD_RMM_D_64D  | FNMADD_DYN_D_64D  | FADD_RNE_D_64D    | FADD_RTZ_D_64D
| FADD_RDN_D_64D    | FADD_RUP_D_64D    | FADD_RMM_D_64D    | FADD_DYN_D_64D
| FSUB_RNE_D_64D    | FSUB_RTZ_D_64D    | FSUB_RDN_D_64D    | FSUB_RUP_D_64D
| FSUB_RMM_D_64D    | FSUB_DYN_D_64D    | FMUL_RNE_D_64D    | FMUL_RTZ_D_64D
| FMUL_RDN_D_64D    | FMUL_RUP_D_64D    | FMUL_RMM_D_64D    | FMUL_DYN_D_64D
| FDIV_RNE_D_64D    | FDIV_RTZ_D_64D    | FDIV_RDN_D_64D    | FDIV_RUP_D_64D
| FDIV_RMM_D_64D    | FDIV_DYN_D_64D    | FSQRT_RNE_D_64D   | FSQRT_RTZ_D_64D
| FSQRT_RDN_D_64D   | FSQRT_RUP_D_64D   | FSQRT_RMM_D_64D   | FSQRT_DYN_D_64D
| FSGNJ_D_64D       | FSGNJN_D_64D      | FSGNJX_D_64D      | FMIN_D_64D
| FMAX_D_64D        | FCVT_RNE_S_D_64D  | FCVT_RTZ_S_D_64D  | FCVT_RDN_S_D_64D
| FCVT_RUP_S_D_64D  | FCVT_RMM_S_D_64D  | FCVT_DYN_S_D_64D  | FCVT_RNE_D_S_64D
| FCVT_RTZ_D_S_64D  | FCVT_RDN_D_S_64D  | FCVT_RUP_D_S_64D  | FCVT_RMM_D_S_64D
| FCVT_DYN_D_S_64D  | FEQ_D_64D         | FLT_D_64D         | FLE_D_64D
| FCLASS_D_64D      | FCVT_RNE_W_D_64D  | FCVT_RTZ_W_D_64D  | FCVT_RDN_W_D_64D
| FCVT_RUP_W_D_64D  | FCVT_RMM_W_D_64D  | FCVT_DYN_W_D_64D  | FCVT_RNE_WU_D_64D
| FCVT_RTZ_WU_D_64D | FCVT_RDN_WU_D_64D | FCVT_RUP_WU_D_64D | FCVT_RMM_WU_D_64D
| FCVT_DYN_WU_D_64D | FCVT_RNE_D_W_64D  | FCVT_RTZ_D_W_64D  | FCVT_RDN_D_W_64D
| FCVT_RUP_D_W_64D  | FCVT_RMM_D_W_64D  | FCVT_DYN_D_W_64D  | FCVT_RNE_D_WU_64D
| FCVT_RTZ_D_WU_64D | FCVT_RDN_D_WU_64D | FCVT_RUP_D_WU_64D | FCVT_RMM_D_WU_64D
| FCVT_DYN_D_WU_64D | FCVT_RNE_L_D_64D  | FCVT_RTZ_L_D_64D  | FCVT_RDN_L_D_64D
| FCVT_RUP_L_D_64D  | FCVT_RMM_L_D_64D  | FCVT_DYN_L_D_64D  | FCVT_RNE_LU_D_64D
| FCVT_RTZ_LU_D_64D | FCVT_RDN_LU_D_64D | FCVT_RUP_LU_D_64D | FCVT_RMM_LU_D_64D
| FCVT_DYN_LU_D_64D | FMV_X_D_64D       | FCVT_RNE_D_L_64D  | FCVT_RTZ_D_L_64D
| FCVT_RDN_D_L_64D  | FCVT_RUP_D_L_64D  | FCVT_RMM_D_L_64D  | FCVT_DYN_D_L_64D
| FCVT_RNE_D_LU_64D | FCVT_RTZ_D_LU_64D | FCVT_RDN_D_LU_64D | FCVT_RUP_D_LU_64D
| FCVT_RMM_D_LU_64D | FCVT_DYN_D_LU_64D | FMV_D_X_64D.
Inductive instruction_RV32Q :=
| FLQ_32Q            | FSQ_32Q           | FMADD_RNE_Q_32Q   | FMADD_RTZ_Q_32Q
| FMADD_RDN_Q_32Q    | FMADD_RUP_Q_32Q   | FMADD_RMM_Q_32Q   | FMADD_DYN_Q_32Q
| FMSUB_RNE_Q_32Q    | FMSUB_RTZ_Q_32Q   | FMSUB_RDN_Q_32Q   | FMSUB_RUP_Q_32Q
| FMSUB_RMM_Q_32Q    | FMSUB_DYN_Q_32Q   | FNMSUB_RNE_Q_32Q  | FNMSUB_RTZ_Q_32Q
| FNMSUB_RDN_Q_32Q   | FNMSUB_RUP_Q_32Q  | FNMSUB_RMM_Q_32Q  | FNMSUB_DYN_Q_32Q
| FNMADD_RNE_Q_32Q   | FNMADD_RTZ_Q_32Q  | FNMADD_RDN_Q_32Q  | FNMADD_RUP_Q_32Q
| FNMADD_RMM_Q_32Q   | FNMADD_DYN_Q_32Q  | FADD_RNE_Q_32Q    | FADD_RTZ_Q_32Q
| FADD_RDN_Q_32Q     | FADD_RUP_Q_32Q    | FADD_RMM_Q_32Q    | FADD_DYN_Q_32Q
| FSUB_RNE_Q_32Q     | FSUB_RTZ_Q_32Q    | FSUB_RDN_Q_32Q    | FSUB_RUP_Q_32Q
| FSUB_RMM_Q_32Q     | FSUB_DYN_Q_32Q    | FMUL_RNE_Q_32Q    | FMUL_RTZ_Q_32Q
| FMUL_RDN_Q_32Q     | FMUL_RUP_Q_32Q    | FMUL_RMM_Q_32Q    | FMUL_DYN_Q_32Q
| FDIV_RNE_Q_32Q     | FDIV_RTZ_Q_32Q    | FDIV_RDN_Q_32Q    | FDIV_RUP_Q_32Q
| FDIV_RMM_Q_32Q     | FDIV_DYN_Q_32Q    | FSQRT_RNE_Q_32Q   | FSQRT_RTZ_Q_32Q
| FSQRT_RDN_Q_32Q    | FSQRT_RUP_Q_32Q   | FSQRT_RMM_Q_32Q   | FSQRT_DYN_Q_32Q
| FSGNJ_Q_32Q        | FSGNJN_Q_32Q      | FSGNJX_Q_32Q      | FMIN_Q_32Q
| FMAX_Q_32Q         | FCVT_RNE_S_Q_32Q  | FCVT_RTZ_S_Q_32Q  | FCVT_RDN_S_Q_32Q
| FCVT_RUP_S_Q_32Q   | FCVT_RMM_S_Q_32Q  | FCVT_DYN_S_Q_32Q  | FCVT_RNE_Q_S_32Q
| FCVT_RTZ_Q_S_32Q   | FCVT_RDN_Q_S_32Q  | FCVT_RUP_Q_S_32Q  | FCVT_RMM_Q_S_32Q
| FCVT_DYN_Q_S_32Q   | FCVT_RNE_D_Q_32Q  | FCVT_RTZ_D_Q_32Q  | FCVT_RDN_D_Q_32Q
| FCVT_RUP_D_Q_32Q   | FCVT_RMM_D_Q_32Q  | FCVT_DYN_D_Q_32Q  | FCVT_RNE_Q_D_32Q
| FCVT_RTZ_Q_D_32Q   | FCVT_RDN_Q_D_32Q  | FCVT_RUP_Q_D_32Q  | FCVT_RMM_Q_D_32Q
| FCVT_DYN_Q_D_32Q   | FEQ_Q_32Q         | FLT_Q_32Q         | FLE_Q_32Q
| FCLASS_Q_32Q       | FCVT_RNE_W_Q_32Q  | FCVT_RTZ_W_Q_32Q  | FCVT_RDN_W_Q_32Q
| FCVT_RUP_W_Q_32Q   | FCVT_RMM_W_Q_32Q  | FCVT_DYN_W_Q_32Q  | FCVT_RNE_WU_Q_32Q
| FCVT_RTZ_WU_Q_32Q  | FCVT_RDN_WU_Q_32Q | FCVT_RUP_WU_Q_32Q | FCVT_RMM_WU_Q_32Q
| FCVT_DYN_WU_Q_32Q  | FCVT_RNE_Q_W_32Q  | FCVT_RTZ_Q_W_32Q  | FCVT_RDN_Q_W_32Q
| FCVT_RUP_Q_W_32Q   | FCVT_RMM_Q_W_32Q  | FCVT_DYN_Q_W_32Q  | FCVT_RNE_Q_WU_32Q
| FCVT_RTZ_Q_WU_32Q  | FCVT_RDN_Q_WU_32Q | FCVT_RUP_Q_WU_32Q | FCVT_RMM_Q_WU_32Q
| FCVT_DYN_Q_WU_32Q.
Inductive instruction_RV64Q :=
| FLQ_64Q           | FSQ_64Q           | FMADD_RNE_Q_64Q   | FMADD_RTZ_Q_64Q
| FMADD_RDN_Q_64Q   | FMADD_RUP_Q_64Q   | FMADD_RMM_Q_64Q   | FMADD_DYN_Q_64Q
| FMSUB_RNE_Q_64Q   | FMSUB_RTZ_Q_64Q   | FMSUB_RDN_Q_64Q   | FMSUB_RUP_Q_64Q
| FMSUB_RMM_Q_64Q   | FMSUB_DYN_Q_64Q   | FNMSUB_RNE_Q_64Q  | FNMSUB_RTZ_Q_64Q
| FNMSUB_RDN_Q_64Q  | FNMSUB_RUP_Q_64Q  | FNMSUB_RMM_Q_64Q  | FNMSUB_DYN_Q_64Q
| FNMADD_RNE_Q_64Q  | FNMADD_RTZ_Q_64Q  | FNMADD_RDN_Q_64Q  | FNMADD_RUP_Q_64Q
| FNMADD_RMM_Q_64Q  | FNMADD_DYN_Q_64Q  | FADD_RNE_Q_64Q    | FADD_RTZ_Q_64Q
| FADD_RDN_Q_64Q    | FADD_RUP_Q_64Q    | FADD_RMM_Q_64Q    | FADD_DYN_Q_64Q
| FSUB_RNE_Q_64Q    | FSUB_RTZ_Q_64Q    | FSUB_RDN_Q_64Q    | FSUB_RUP_Q_64Q
| FSUB_RMM_Q_64Q    | FSUB_DYN_Q_64Q    | FMUL_RNE_Q_64Q    | FMUL_RTZ_Q_64Q
| FMUL_RDN_Q_64Q    | FMUL_RUP_Q_64Q    | FMUL_RMM_Q_64Q    | FMUL_DYN_Q_64Q
| FDIV_RNE_Q_64Q    | FDIV_RTZ_Q_64Q    | FDIV_RDN_Q_64Q    | FDIV_RUP_Q_64Q
| FDIV_RMM_Q_64Q    | FDIV_DYN_Q_64Q    | FSQRT_RNE_Q_64Q   | FSQRT_RTZ_Q_64Q
| FSQRT_RDN_Q_64Q   | FSQRT_RUP_Q_64Q   | FSQRT_RMM_Q_64Q   | FSQRT_DYN_Q_64Q
| FSGNJ_Q_64Q       | FSGNJN_Q_64Q      | FSGNJX_Q_64Q      | FMIN_Q_64Q
| FMAX_Q_64Q        | FCVT_RNE_S_Q_64Q  | FCVT_RTZ_S_Q_64Q  | FCVT_RDN_S_Q_64Q
| FCVT_RUP_S_Q_64Q  | FCVT_RMM_S_Q_64Q  | FCVT_DYN_S_Q_64Q  | FCVT_RNE_Q_S_64Q
| FCVT_RTZ_Q_S_64Q  | FCVT_RDN_Q_S_64Q  | FCVT_RUP_Q_S_64Q  | FCVT_RMM_Q_S_64Q
| FCVT_DYN_Q_S_64Q  | FCVT_RNE_D_Q_64Q  | FCVT_RTZ_D_Q_64Q  | FCVT_RDN_D_Q_64Q
| FCVT_RUP_D_Q_64Q  | FCVT_RMM_D_Q_64Q  | FCVT_DYN_D_Q_64Q  | FCVT_RNE_Q_D_64Q
| FCVT_RTZ_Q_D_64Q  | FCVT_RDN_Q_D_64Q  | FCVT_RUP_Q_D_64Q  | FCVT_RMM_Q_D_64Q
| FCVT_DYN_Q_D_64Q  | FEQ_Q_64Q         | FLT_Q_64Q         | FLE_Q_64Q
| FCLASS_Q_64Q      | FCVT_RNE_W_Q_64Q  | FCVT_RTZ_W_Q_64Q  | FCVT_RDN_W_Q_64Q
| FCVT_RUP_W_Q_64Q  | FCVT_RMM_W_Q_64Q  | FCVT_DYN_W_Q_64Q  | FCVT_RNE_WU_Q_64Q
| FCVT_RTZ_WU_Q_64Q | FCVT_RDN_WU_Q_64Q | FCVT_RUP_WU_Q_64Q | FCVT_RMM_WU_Q_64Q
| FCVT_DYN_WU_Q_64Q | FCVT_RNE_Q_W_64Q  | FCVT_RTZ_Q_W_64Q  | FCVT_RDN_Q_W_64Q
| FCVT_RUP_Q_W_64Q  | FCVT_RMM_Q_W_64Q  | FCVT_DYN_Q_W_64Q  | FCVT_RNE_Q_WU_64Q
| FCVT_RTZ_Q_WU_64Q | FCVT_RDN_Q_WU_64Q | FCVT_RUP_Q_WU_64Q | FCVT_RMM_Q_WU_64Q
| FCVT_DYN_Q_WU_64Q | FCVT_RNE_L_Q_64Q  | FCVT_RTZ_L_Q_64Q  | FCVT_RDN_L_Q_64Q
| FCVT_RUP_L_Q_64Q  | FCVT_RMM_L_Q_64Q  | FCVT_DYN_L_Q_64Q  | FCVT_RNE_LU_Q_64Q
| FCVT_RTZ_LU_Q_64Q | FCVT_RDN_LU_Q_64Q | FCVT_RUP_LU_Q_64Q | FCVT_RMM_LU_Q_64Q
| FCVT_DYN_LU_Q_64Q | FCVT_RNE_Q_L_64Q  | FCVT_RTZ_Q_L_64Q  | FCVT_RDN_Q_L_64Q
| FCVT_RUP_Q_L_64Q  | FCVT_RMM_Q_L_64Q  | FCVT_DYN_Q_L_64Q  | FCVT_RNE_Q_LU_64Q
| FCVT_RTZ_Q_LU_64Q | FCVT_RDN_Q_LU_64Q | FCVT_RUP_Q_LU_64Q | FCVT_RMM_Q_LU_64Q
| FCVT_DYN_Q_LU_64Q.

Inductive instruction :=
| RV32I_instruction        (i : instruction_RV32I)
| RV64I_instruction        (i : instruction_RV64I)
| RV32Zifencei_instruction (i : instruction_RV32Zifencei)
| RV64Zifencei_instruction (i : instruction_RV64Zifencei)
| RV32Zicsr_instruction    (i : instruction_RV32Zicsr)
| RV64Zicsr_instruction    (i : instruction_RV64Zicsr)
| RV32M_instruction        (i : instruction_RV32M)
| RV64M_instruction        (i : instruction_RV64M)
| RV32A_instruction        (i : instruction_RV32A)
| RV64A_instruction        (i : instruction_RV64A)
| RV32F_instruction        (i : instruction_RV32F)
| RV64F_instruction        (i : instruction_RV64F)
| RV32D_instruction        (i : instruction_RV32D)
| RV64D_instruction        (i : instruction_RV64D)
| RV32Q_instruction        (i : instruction_RV32Q)
| RV64Q_instruction        (i : instruction_RV64Q).

Definition RV32I_instructions := [
  RV32I_instruction LUI_32I  ; RV32I_instruction AUIPC_32I ;
  RV32I_instruction JAL_32I  ; RV32I_instruction JALR_32I  ;
  RV32I_instruction BEQ_32I  ; RV32I_instruction BNE_32I   ;
  RV32I_instruction BLT_32I  ; RV32I_instruction BGE_32I   ;
  RV32I_instruction BLTU_32I ; RV32I_instruction BGEU_32I  ;
  RV32I_instruction LB_32I   ; RV32I_instruction LH_32I    ;
  RV32I_instruction LW_32I   ; RV32I_instruction LBU_32I   ;
  RV32I_instruction LHU_32I  ; RV32I_instruction SB_32I    ;
  RV32I_instruction SH_32I   ; RV32I_instruction SW_32I    ;
  RV32I_instruction ADDI_32I ; RV32I_instruction SLTI_32I  ;
  RV32I_instruction SLTIU_32I; RV32I_instruction XORI_32I  ;
  RV32I_instruction ORI_32I  ; RV32I_instruction ANDI_32I  ;
  RV32I_instruction SLLI_32I ; RV32I_instruction SRLI_32I  ;
  RV32I_instruction SRAI_32I ; RV32I_instruction ADD_32I   ;
  RV32I_instruction SUB_32I  ; RV32I_instruction SLL_32I   ;
  RV32I_instruction SLT_32I  ; RV32I_instruction SLTU_32I  ;
  RV32I_instruction XOR_32I  ; RV32I_instruction SRL_32I   ;
  RV32I_instruction SRA_32I  ; RV32I_instruction OR_32I    ;
  RV32I_instruction AND_32I  ; RV32I_instruction FENCE_32I ;
  RV32I_instruction ECALL_32I; RV32I_instruction EBREAK_32I
].

Definition RV64I_instructions := [
  RV64I_instruction LUI_64I  ; RV64I_instruction AUIPC_64I ;
  RV64I_instruction JAL_64I  ; RV64I_instruction JALR_64I  ;
  RV64I_instruction BEQ_64I  ; RV64I_instruction BNE_64I   ;
  RV64I_instruction BLT_64I  ; RV64I_instruction BGE_64I   ;
  RV64I_instruction BLTU_64I ; RV64I_instruction BGEU_64I  ;
  RV64I_instruction LB_64I   ; RV64I_instruction LH_64I    ;
  RV64I_instruction LW_64I   ; RV64I_instruction LBU_64I   ;
  RV64I_instruction LHU_64I  ; RV64I_instruction SB_64I    ;
  RV64I_instruction SH_64I   ; RV64I_instruction SW_64I    ;
  RV64I_instruction ADDI_64I ; RV64I_instruction SLTI_64I  ;
  RV64I_instruction SLTIU_64I; RV64I_instruction XORI_64I  ;
  RV64I_instruction ORI_64I  ; RV64I_instruction ANDI_64I  ;
  RV64I_instruction SLLI_64I ; RV64I_instruction SRLI_64I  ;
  RV64I_instruction SRAI_64I ; RV64I_instruction ADD_64I   ;
  RV64I_instruction SUB_64I  ; RV64I_instruction SLL_64I   ;
  RV64I_instruction SLT_64I  ; RV64I_instruction SLTU_64I  ;
  RV64I_instruction XOR_64I  ; RV64I_instruction SRL_64I   ;
  RV64I_instruction SRA_64I  ; RV64I_instruction OR_64I    ;
  RV64I_instruction AND_64I  ; RV64I_instruction FENCE_64I ;
  RV64I_instruction ECALL_64I; RV64I_instruction EBREAK_64I;
  RV64I_instruction LWU_64I  ; RV64I_instruction LD_64I    ;
  RV64I_instruction SD_64I   ; RV64I_instruction ADDIW_64I ;
  RV64I_instruction SLLIW_64I; RV64I_instruction SRLIW_64I ;
  RV64I_instruction SRAIW_64I; RV64I_instruction ADDW_64I  ;
  RV64I_instruction SUBW_64I ; RV64I_instruction SLLW_64I  ;
  RV64I_instruction SRLW_64I ; RV64I_instruction SRAW_64I
].

Definition RV32Zifencei_instructions :=
  [RV32Zifencei_instruction FENCE_I_32Zifencei].

Definition RV64Zifencei_instructions :=
  [RV64Zifencei_instruction FENCE_I_64Zifencei].

Definition RV32Zicsr_instructions := [
  RV32Zicsr_instruction CSRRW_32Zicsr ; RV32Zicsr_instruction CSRRS_32Zicsr ;
  RV32Zicsr_instruction CSRRC_32Zicsr ; RV32Zicsr_instruction CSRRWI_32Zicsr;
  RV32Zicsr_instruction CSRRSI_32Zicsr; RV32Zicsr_instruction CSRRCI_32Zicsr
].

Definition RV64Zicsr_instructions := [
  RV64Zicsr_instruction CSRRW_64Zicsr; RV64Zicsr_instruction CSRRS_64Zicsr;
  RV64Zicsr_instruction CSRRC_64Zicsr; RV64Zicsr_instruction CSRRWI_64Zicsr;
  RV64Zicsr_instruction CSRRSI_64Zicsr; RV64Zicsr_instruction CSRRCI_64Zicsr
].

Definition RV32M_instructions := [
  RV32M_instruction MUL_32M   ; RV32M_instruction MULH_32M ;
  RV32M_instruction MULHSU_32M; RV32M_instruction MULHU_32M;
  RV32M_instruction DIV_32M   ; RV32M_instruction DIVU_32M ;
  RV32M_instruction REM_32M   ; RV32M_instruction REMU_32M
].

Definition RV64M_instructions := [
  RV64M_instruction MUL_64M   ; RV64M_instruction MULH_64M ;
  RV64M_instruction MULHSU_64M; RV64M_instruction MULHU_64M;
  RV64M_instruction DIV_64M   ; RV64M_instruction DIVU_64M ;
  RV64M_instruction REM_64M   ; RV64M_instruction REMU_64M ;
  RV64M_instruction MULW_64M  ; RV64M_instruction DIVW_64M ;
  RV64M_instruction DIVUW_64M ; RV64M_instruction REMW_64M ;
  RV64M_instruction REMUW_64M
].

Definition RV32A_instructions := [
  RV32A_instruction LR_W_00_32A     ; RV32A_instruction LR_W_01_32A     ;
  RV32A_instruction LR_W_10_32A     ; RV32A_instruction LR_W_11_32A     ;
  RV32A_instruction SC_W_00_32A     ; RV32A_instruction SC_W_01_32A     ;
  RV32A_instruction SC_W_10_32A     ; RV32A_instruction SC_W_11_32A     ;
  RV32A_instruction AMOSWAP_W_00_32A; RV32A_instruction AMOSWAP_W_01_32A;
  RV32A_instruction AMOSWAP_W_10_32A; RV32A_instruction AMOSWAP_W_11_32A;
  RV32A_instruction AMOADD_W_00_32A ; RV32A_instruction AMOADD_W_01_32A ;
  RV32A_instruction AMOADD_W_10_32A ; RV32A_instruction AMOADD_W_11_32A ;
  RV32A_instruction AMOXOR_W_00_32A ; RV32A_instruction AMOXOR_W_01_32A ;
  RV32A_instruction AMOXOR_W_10_32A ; RV32A_instruction AMOXOR_W_11_32A ;
  RV32A_instruction AMOAND_W_00_32A ; RV32A_instruction AMOAND_W_01_32A ;
  RV32A_instruction AMOAND_W_10_32A ; RV32A_instruction AMOAND_W_11_32A ;
  RV32A_instruction AMOOR_W_00_32A  ; RV32A_instruction AMOOR_W_01_32A  ;
  RV32A_instruction AMOOR_W_10_32A  ; RV32A_instruction AMOOR_W_11_32A  ;
  RV32A_instruction AMOMIN_W_00_32A ; RV32A_instruction AMOMIN_W_01_32A ;
  RV32A_instruction AMOMIN_W_10_32A ; RV32A_instruction AMOMIN_W_11_32A ;
  RV32A_instruction AMOMAX_W_00_32A ; RV32A_instruction AMOMAX_W_01_32A ;
  RV32A_instruction AMOMAX_W_10_32A ; RV32A_instruction AMOMAX_W_11_32A ;
  RV32A_instruction AMOMINU_W_00_32A; RV32A_instruction AMOMINU_W_01_32A;
  RV32A_instruction AMOMINU_W_10_32A; RV32A_instruction AMOMINU_W_11_32A;
  RV32A_instruction AMOMAXU_W_00_32A; RV32A_instruction AMOMAXU_W_01_32A;
  RV32A_instruction AMOMAXU_W_10_32A; RV32A_instruction AMOMAXU_W_11_32A
].

Definition RV64A_instructions := [
  RV64A_instruction LR_W_00_64A     ; RV64A_instruction LR_W_01_64A     ;
  RV64A_instruction LR_W_10_64A     ; RV64A_instruction LR_W_11_64A     ;
  RV64A_instruction SC_W_00_64A     ; RV64A_instruction SC_W_01_64A     ;
  RV64A_instruction SC_W_10_64A     ; RV64A_instruction SC_W_11_64A     ;
  RV64A_instruction AMOSWAP_W_00_64A; RV64A_instruction AMOSWAP_W_01_64A;
  RV64A_instruction AMOSWAP_W_10_64A; RV64A_instruction AMOSWAP_W_11_64A;
  RV64A_instruction AMOADD_W_00_64A ; RV64A_instruction AMOADD_W_01_64A ;
  RV64A_instruction AMOADD_W_10_64A ; RV64A_instruction AMOADD_W_11_64A ;
  RV64A_instruction AMOXOR_W_00_64A ; RV64A_instruction AMOXOR_W_01_64A ;
  RV64A_instruction AMOXOR_W_10_64A ; RV64A_instruction AMOXOR_W_11_64A ;
  RV64A_instruction AMOAND_W_00_64A ; RV64A_instruction AMOAND_W_01_64A ;
  RV64A_instruction AMOAND_W_10_64A ; RV64A_instruction AMOAND_W_11_64A ;
  RV64A_instruction AMOOR_W_00_64A  ; RV64A_instruction AMOOR_W_01_64A  ;
  RV64A_instruction AMOOR_W_10_64A  ; RV64A_instruction AMOOR_W_11_64A  ;
  RV64A_instruction AMOMIN_W_00_64A ; RV64A_instruction AMOMIN_W_01_64A ;
  RV64A_instruction AMOMIN_W_10_64A ; RV64A_instruction AMOMIN_W_11_64A ;
  RV64A_instruction AMOMAX_W_00_64A ; RV64A_instruction AMOMAX_W_01_64A ;
  RV64A_instruction AMOMAX_W_10_64A ; RV64A_instruction AMOMAX_W_11_64A ;
  RV64A_instruction AMOMINU_W_00_64A; RV64A_instruction AMOMINU_W_01_64A;
  RV64A_instruction AMOMINU_W_10_64A; RV64A_instruction AMOMINU_W_11_64A;
  RV64A_instruction AMOMAXU_W_00_64A; RV64A_instruction AMOMAXU_W_01_64A;
  RV64A_instruction AMOMAXU_W_10_64A; RV64A_instruction AMOMAXU_W_11_64A;
  RV64A_instruction LR_D_00_64A     ; RV64A_instruction LR_D_01_64A     ;
  RV64A_instruction LR_D_10_64A     ; RV64A_instruction LR_D_11_64A     ;
  RV64A_instruction SC_D_00_64A     ; RV64A_instruction SC_D_01_64A     ;
  RV64A_instruction SC_D_10_64A     ; RV64A_instruction SC_D_11_64A     ;
  RV64A_instruction AMOSWAP_D_00_64A; RV64A_instruction AMOSWAP_D_01_64A;
  RV64A_instruction AMOSWAP_D_10_64A; RV64A_instruction AMOSWAP_D_11_64A;
  RV64A_instruction AMOADD_D_00_64A ; RV64A_instruction AMOADD_D_01_64A ;
  RV64A_instruction AMOADD_D_10_64A ; RV64A_instruction AMOADD_D_11_64A ;
  RV64A_instruction AMOXOR_D_00_64A ; RV64A_instruction AMOXOR_D_01_64A ;
  RV64A_instruction AMOXOR_D_10_64A ; RV64A_instruction AMOXOR_D_11_64A ;
  RV64A_instruction AMOAND_D_00_64A ; RV64A_instruction AMOAND_D_01_64A ;
  RV64A_instruction AMOAND_D_10_64A ; RV64A_instruction AMOAND_D_11_64A ;
  RV64A_instruction AMOOR_D_00_64A  ; RV64A_instruction AMOOR_D_01_64A  ;
  RV64A_instruction AMOOR_D_10_64A  ; RV64A_instruction AMOOR_D_11_64A  ;
  RV64A_instruction AMOMIN_D_00_64A ; RV64A_instruction AMOMIN_D_01_64A ;
  RV64A_instruction AMOMIN_D_10_64A ; RV64A_instruction AMOMIN_D_11_64A ;
  RV64A_instruction AMOMAX_D_00_64A ; RV64A_instruction AMOMAX_D_01_64A ;
  RV64A_instruction AMOMAX_D_10_64A ; RV64A_instruction AMOMAX_D_11_64A ;
  RV64A_instruction AMOMINU_D_00_64A; RV64A_instruction AMOMINU_D_01_64A;
  RV64A_instruction AMOMINU_D_10_64A; RV64A_instruction AMOMINU_D_11_64A;
  RV64A_instruction AMOMAXU_D_00_64A; RV64A_instruction AMOMAXU_D_01_64A;
  RV64A_instruction AMOMAXU_D_10_64A; RV64A_instruction AMOMAXU_D_11_64A
].

Definition RV32F_instructions := [
  RV32F_instruction FLW_32F          ; RV32F_instruction FSW_32F          ;
  RV32F_instruction FMADD_RNE_S_32F  ; RV32F_instruction FMADD_RTZ_S_32F  ;
  RV32F_instruction FMADD_RDN_S_32F  ; RV32F_instruction FMADD_RUP_S_32F  ;
  RV32F_instruction FMADD_RMM_S_32F  ; RV32F_instruction FMADD_DYN_S_32F  ;
  RV32F_instruction FMSUB_RNE_S_32F  ; RV32F_instruction FMSUB_RTZ_S_32F  ;
  RV32F_instruction FMSUB_RDN_S_32F  ; RV32F_instruction FMSUB_RUP_S_32F  ;
  RV32F_instruction FMSUB_RMM_S_32F  ; RV32F_instruction FMSUB_DYN_S_32F  ;
  RV32F_instruction FNMSUB_RNE_S_32F ; RV32F_instruction FNMSUB_RTZ_S_32F ;
  RV32F_instruction FNMSUB_RDN_S_32F ; RV32F_instruction FNMSUB_RUP_S_32F ;
  RV32F_instruction FNMSUB_RMM_S_32F ; RV32F_instruction FNMSUB_DYN_S_32F ;
  RV32F_instruction FNMADD_RNE_S_32F ; RV32F_instruction FNMADD_RTZ_S_32F ;
  RV32F_instruction FNMADD_RDN_S_32F ; RV32F_instruction FNMADD_RUP_S_32F ;
  RV32F_instruction FNMADD_RMM_S_32F ; RV32F_instruction FNMADD_DYN_S_32F ;
  RV32F_instruction FADD_RNE_S_32F   ; RV32F_instruction FADD_RTZ_S_32F   ;
  RV32F_instruction FADD_RDN_S_32F   ; RV32F_instruction FADD_RUP_S_32F   ;
  RV32F_instruction FADD_RMM_S_32F   ; RV32F_instruction FADD_DYN_S_32F   ;
  RV32F_instruction FSUB_RNE_S_32F   ; RV32F_instruction FSUB_RTZ_S_32F   ;
  RV32F_instruction FSUB_RDN_S_32F   ; RV32F_instruction FSUB_RUP_S_32F   ;
  RV32F_instruction FSUB_RMM_S_32F   ; RV32F_instruction FSUB_DYN_S_32F   ;
  RV32F_instruction FMUL_RNE_S_32F   ; RV32F_instruction FMUL_RTZ_S_32F   ;
  RV32F_instruction FMUL_RDN_S_32F   ; RV32F_instruction FMUL_RUP_S_32F   ;
  RV32F_instruction FMUL_RMM_S_32F   ; RV32F_instruction FMUL_DYN_S_32F   ;
  RV32F_instruction FDIV_RNE_S_32F   ; RV32F_instruction FDIV_RTZ_S_32F   ;
  RV32F_instruction FDIV_RDN_S_32F   ; RV32F_instruction FDIV_RUP_S_32F   ;
  RV32F_instruction FDIV_RMM_S_32F   ; RV32F_instruction FDIV_DYN_S_32F   ;
  RV32F_instruction FSQRT_RNE_S_32F  ; RV32F_instruction FSQRT_RTZ_S_32F  ;
  RV32F_instruction FSQRT_RDN_S_32F  ; RV32F_instruction FSQRT_RUP_S_32F  ;
  RV32F_instruction FSQRT_RMM_S_32F  ; RV32F_instruction FSQRT_DYN_S_32F  ;
  RV32F_instruction FSGNJ_S_32F      ; RV32F_instruction FSGNJN_S_32F     ;
  RV32F_instruction FSGNJX_S_32F     ; RV32F_instruction FMIN_S_32F       ;
  RV32F_instruction FMAX_S_32F       ; RV32F_instruction FCVT_RNE_W_S_32F ;
  RV32F_instruction FCVT_RTZ_W_S_32F ; RV32F_instruction FCVT_RDN_W_S_32F ;
  RV32F_instruction FCVT_RUP_W_S_32F ; RV32F_instruction FCVT_RMM_W_S_32F ;
  RV32F_instruction FCVT_DYN_W_S_32F ; RV32F_instruction FCVT_RNE_WU_S_32F;
  RV32F_instruction FCVT_RTZ_WU_S_32F; RV32F_instruction FCVT_RDN_WU_S_32F;
  RV32F_instruction FCVT_RUP_WU_S_32F; RV32F_instruction FCVT_RMM_WU_S_32F;
  RV32F_instruction FCVT_DYN_WU_S_32F; RV32F_instruction FMV_X_W_32F      ;
  RV32F_instruction FEQ_S_32F        ; RV32F_instruction FLT_S_32F        ;
  RV32F_instruction FLE_S_32F        ; RV32F_instruction FCLASS_S_32F     ;
  RV32F_instruction FCVT_RNE_S_W_32F ; RV32F_instruction FCVT_RTZ_S_W_32F ;
  RV32F_instruction FCVT_RDN_S_W_32F ; RV32F_instruction FCVT_RUP_S_W_32F ;
  RV32F_instruction FCVT_RMM_S_W_32F ; RV32F_instruction FCVT_DYN_S_W_32F ;
  RV32F_instruction FCVT_RNE_S_WU_32F; RV32F_instruction FCVT_RTZ_S_WU_32F;
  RV32F_instruction FCVT_RDN_S_WU_32F; RV32F_instruction FCVT_RUP_S_WU_32F;
  RV32F_instruction FCVT_RMM_S_WU_32F; RV32F_instruction FCVT_DYN_S_WU_32F;
  RV32F_instruction FMV_W_X_32F
].

Definition RV64F_instructions := [
  RV64F_instruction FLW_64F          ; RV64F_instruction FSW_64F          ;
  RV64F_instruction FMADD_RNE_S_64F  ; RV64F_instruction FMADD_RTZ_S_64F  ;
  RV64F_instruction FMADD_RDN_S_64F  ; RV64F_instruction FMADD_RUP_S_64F  ;
  RV64F_instruction FMADD_RMM_S_64F  ; RV64F_instruction FMADD_DYN_S_64F  ;
  RV64F_instruction FMSUB_RNE_S_64F  ; RV64F_instruction FMSUB_RTZ_S_64F  ;
  RV64F_instruction FMSUB_RDN_S_64F  ; RV64F_instruction FMSUB_RUP_S_64F  ;
  RV64F_instruction FMSUB_RMM_S_64F  ; RV64F_instruction FMSUB_DYN_S_64F  ;
  RV64F_instruction FNMSUB_RNE_S_64F ; RV64F_instruction FNMSUB_RTZ_S_64F ;
  RV64F_instruction FNMSUB_RDN_S_64F ; RV64F_instruction FNMSUB_RUP_S_64F ;
  RV64F_instruction FNMSUB_RMM_S_64F ; RV64F_instruction FNMSUB_DYN_S_64F ;
  RV64F_instruction FNMADD_RNE_S_64F ; RV64F_instruction FNMADD_RTZ_S_64F ;
  RV64F_instruction FNMADD_RDN_S_64F ; RV64F_instruction FNMADD_RUP_S_64F ;
  RV64F_instruction FNMADD_RMM_S_64F ; RV64F_instruction FNMADD_DYN_S_64F ;
  RV64F_instruction FADD_RNE_S_64F   ; RV64F_instruction FADD_RTZ_S_64F   ;
  RV64F_instruction FADD_RDN_S_64F   ; RV64F_instruction FADD_RUP_S_64F   ;
  RV64F_instruction FADD_RMM_S_64F   ; RV64F_instruction FADD_DYN_S_64F   ;
  RV64F_instruction FSUB_RNE_S_64F   ; RV64F_instruction FSUB_RTZ_S_64F   ;
  RV64F_instruction FSUB_RDN_S_64F   ; RV64F_instruction FSUB_RUP_S_64F   ;
  RV64F_instruction FSUB_RMM_S_64F   ; RV64F_instruction FSUB_DYN_S_64F   ;
  RV64F_instruction FMUL_RNE_S_64F   ; RV64F_instruction FMUL_RTZ_S_64F   ;
  RV64F_instruction FMUL_RDN_S_64F   ; RV64F_instruction FMUL_RUP_S_64F   ;
  RV64F_instruction FMUL_RMM_S_64F   ; RV64F_instruction FMUL_DYN_S_64F   ;
  RV64F_instruction FDIV_RNE_S_64F   ; RV64F_instruction FDIV_RTZ_S_64F   ;
  RV64F_instruction FDIV_RDN_S_64F   ; RV64F_instruction FDIV_RUP_S_64F   ;
  RV64F_instruction FDIV_RMM_S_64F   ; RV64F_instruction FDIV_DYN_S_64F   ;
  RV64F_instruction FSQRT_RNE_S_64F  ; RV64F_instruction FSQRT_RTZ_S_64F  ;
  RV64F_instruction FSQRT_RDN_S_64F  ; RV64F_instruction FSQRT_RUP_S_64F  ;
  RV64F_instruction FSQRT_RMM_S_64F  ; RV64F_instruction FSQRT_DYN_S_64F  ;
  RV64F_instruction FSGNJ_S_64F      ; RV64F_instruction FSGNJN_S_64F     ;
  RV64F_instruction FSGNJX_S_64F     ; RV64F_instruction FMIN_S_64F       ;
  RV64F_instruction FMAX_S_64F       ; RV64F_instruction FCVT_RNE_W_S_64F ;
  RV64F_instruction FCVT_RTZ_W_S_64F ; RV64F_instruction FCVT_RDN_W_S_64F ;
  RV64F_instruction FCVT_RUP_W_S_64F ; RV64F_instruction FCVT_RMM_W_S_64F ;
  RV64F_instruction FCVT_DYN_W_S_64F ; RV64F_instruction FCVT_RNE_WU_S_64F;
  RV64F_instruction FCVT_RTZ_WU_S_64F; RV64F_instruction FCVT_RDN_WU_S_64F;
  RV64F_instruction FCVT_RUP_WU_S_64F; RV64F_instruction FCVT_RMM_WU_S_64F;
  RV64F_instruction FCVT_DYN_WU_S_64F; RV64F_instruction FMV_X_W_64F      ;
  RV64F_instruction FEQ_S_64F        ; RV64F_instruction FLT_S_64F        ;
  RV64F_instruction FLE_S_64F        ; RV64F_instruction FCLASS_S_64F     ;
  RV64F_instruction FCVT_RNE_S_W_64F ; RV64F_instruction FCVT_RTZ_S_W_64F ;
  RV64F_instruction FCVT_RDN_S_W_64F ; RV64F_instruction FCVT_RUP_S_W_64F ;
  RV64F_instruction FCVT_RMM_S_W_64F ; RV64F_instruction FCVT_DYN_S_W_64F ;
  RV64F_instruction FCVT_RNE_S_WU_64F; RV64F_instruction FCVT_RTZ_S_WU_64F;
  RV64F_instruction FCVT_RDN_S_WU_64F; RV64F_instruction FCVT_RUP_S_WU_64F;
  RV64F_instruction FCVT_RMM_S_WU_64F; RV64F_instruction FCVT_DYN_S_WU_64F;
  RV64F_instruction FMV_W_X_64F      ; RV64F_instruction FCVT_RNE_L_S_64F ;
  RV64F_instruction FCVT_RTZ_L_S_64F ; RV64F_instruction FCVT_RDN_L_S_64F ;
  RV64F_instruction FCVT_RUP_L_S_64F ; RV64F_instruction FCVT_RMM_L_S_64F ;
  RV64F_instruction FCVT_DYN_L_S_64F ; RV64F_instruction FCVT_RNE_LU_S_64F;
  RV64F_instruction FCVT_RTZ_LU_S_64F; RV64F_instruction FCVT_RDN_LU_S_64F;
  RV64F_instruction FCVT_RUP_LU_S_64F; RV64F_instruction FCVT_RMM_LU_S_64F;
  RV64F_instruction FCVT_DYN_LU_S_64F; RV64F_instruction FCVT_RNE_S_L_64F ;
  RV64F_instruction FCVT_RTZ_S_L_64F ; RV64F_instruction FCVT_RDN_S_L_64F ;
  RV64F_instruction FCVT_RUP_S_L_64F ; RV64F_instruction FCVT_RMM_S_L_64F ;
  RV64F_instruction FCVT_DYN_S_L_64F ; RV64F_instruction FCVT_RNE_S_LU_64F;
  RV64F_instruction FCVT_RTZ_S_LU_64F; RV64F_instruction FCVT_RDN_S_LU_64F;
  RV64F_instruction FCVT_RUP_S_LU_64F; RV64F_instruction FCVT_RMM_S_LU_64F;
  RV64F_instruction FCVT_DYN_S_LU_64F
].

Definition RV32D_instructions := [
  RV32D_instruction FLD_32D          ; RV32D_instruction FSD_32D          ;
  RV32D_instruction FMADD_RNE_D_32D  ; RV32D_instruction FMADD_RTZ_D_32D  ;
  RV32D_instruction FMADD_RDN_D_32D  ; RV32D_instruction FMADD_RUP_D_32D  ;
  RV32D_instruction FMADD_RMM_D_32D  ; RV32D_instruction FMADD_DYN_D_32D  ;
  RV32D_instruction FMSUB_RNE_D_32D  ; RV32D_instruction FMSUB_RTZ_D_32D  ;
  RV32D_instruction FMSUB_RDN_D_32D  ; RV32D_instruction FMSUB_RUP_D_32D  ;
  RV32D_instruction FMSUB_RMM_D_32D  ; RV32D_instruction FMSUB_DYN_D_32D  ;
  RV32D_instruction FNMSUB_RNE_D_32D ; RV32D_instruction FNMSUB_RTZ_D_32D ;
  RV32D_instruction FNMSUB_RDN_D_32D ; RV32D_instruction FNMSUB_RUP_D_32D ;
  RV32D_instruction FNMSUB_RMM_D_32D ; RV32D_instruction FNMSUB_DYN_D_32D ;
  RV32D_instruction FNMADD_RNE_D_32D ; RV32D_instruction FNMADD_RTZ_D_32D ;
  RV32D_instruction FNMADD_RDN_D_32D ; RV32D_instruction FNMADD_RUP_D_32D ;
  RV32D_instruction FNMADD_RMM_D_32D ; RV32D_instruction FNMADD_DYN_D_32D ;
  RV32D_instruction FADD_RNE_D_32D   ; RV32D_instruction FADD_RTZ_D_32D   ;
  RV32D_instruction FADD_RDN_D_32D   ; RV32D_instruction FADD_RUP_D_32D   ;
  RV32D_instruction FADD_RMM_D_32D   ; RV32D_instruction FADD_DYN_D_32D   ;
  RV32D_instruction FSUB_RNE_D_32D   ; RV32D_instruction FSUB_RTZ_D_32D   ;
  RV32D_instruction FSUB_RDN_D_32D   ; RV32D_instruction FSUB_RUP_D_32D   ;
  RV32D_instruction FSUB_RMM_D_32D   ; RV32D_instruction FSUB_DYN_D_32D   ;
  RV32D_instruction FMUL_RNE_D_32D   ; RV32D_instruction FMUL_RTZ_D_32D   ;
  RV32D_instruction FMUL_RDN_D_32D   ; RV32D_instruction FMUL_RUP_D_32D   ;
  RV32D_instruction FMUL_RMM_D_32D   ; RV32D_instruction FMUL_DYN_D_32D   ;
  RV32D_instruction FDIV_RNE_D_32D   ; RV32D_instruction FDIV_RTZ_D_32D   ;
  RV32D_instruction FDIV_RDN_D_32D   ; RV32D_instruction FDIV_RUP_D_32D   ;
  RV32D_instruction FDIV_RMM_D_32D   ; RV32D_instruction FDIV_DYN_D_32D   ;
  RV32D_instruction FSQRT_RNE_D_32D  ; RV32D_instruction FSQRT_RTZ_D_32D  ;
  RV32D_instruction FSQRT_RDN_D_32D  ; RV32D_instruction FSQRT_RUP_D_32D  ;
  RV32D_instruction FSQRT_RMM_D_32D  ; RV32D_instruction FSQRT_DYN_D_32D  ;
  RV32D_instruction FSGNJ_D_32D      ; RV32D_instruction FSGNJN_D_32D     ;
  RV32D_instruction FSGNJX_D_32D     ; RV32D_instruction FMIN_D_32D       ;
  RV32D_instruction FMAX_D_32D       ; RV32D_instruction FCVT_RNE_S_D_32D ;
  RV32D_instruction FCVT_RTZ_S_D_32D ; RV32D_instruction FCVT_RDN_S_D_32D ;
  RV32D_instruction FCVT_RUP_S_D_32D ; RV32D_instruction FCVT_RMM_S_D_32D ;
  RV32D_instruction FCVT_DYN_S_D_32D ; RV32D_instruction FCVT_RNE_D_S_32D ;
  RV32D_instruction FCVT_RTZ_D_S_32D ; RV32D_instruction FCVT_RDN_D_S_32D ;
  RV32D_instruction FCVT_RUP_D_S_32D ; RV32D_instruction FCVT_RMM_D_S_32D ;
  RV32D_instruction FCVT_DYN_D_S_32D ; RV32D_instruction FEQ_D_32D        ;
  RV32D_instruction FLT_D_32D        ; RV32D_instruction FLE_D_32D        ;
  RV32D_instruction FCLASS_D_32D     ; RV32D_instruction FCVT_RNE_W_D_32D ;
  RV32D_instruction FCVT_RTZ_W_D_32D ; RV32D_instruction FCVT_RDN_W_D_32D ;
  RV32D_instruction FCVT_RUP_W_D_32D ; RV32D_instruction FCVT_RMM_W_D_32D ;
  RV32D_instruction FCVT_DYN_W_D_32D ; RV32D_instruction FCVT_RNE_WU_D_32D;
  RV32D_instruction FCVT_RTZ_WU_D_32D; RV32D_instruction FCVT_RDN_WU_D_32D;
  RV32D_instruction FCVT_RUP_WU_D_32D; RV32D_instruction FCVT_RMM_WU_D_32D;
  RV32D_instruction FCVT_DYN_WU_D_32D; RV32D_instruction FCVT_RNE_D_W_32D ;
  RV32D_instruction FCVT_RTZ_D_W_32D ; RV32D_instruction FCVT_RDN_D_W_32D ;
  RV32D_instruction FCVT_RUP_D_W_32D ; RV32D_instruction FCVT_RMM_D_W_32D ;
  RV32D_instruction FCVT_DYN_D_W_32D ; RV32D_instruction FCVT_RNE_D_WU_32D;
  RV32D_instruction FCVT_RTZ_D_WU_32D; RV32D_instruction FCVT_RDN_D_WU_32D;
  RV32D_instruction FCVT_RUP_D_WU_32D; RV32D_instruction FCVT_RMM_D_WU_32D;
  RV32D_instruction FCVT_DYN_D_WU_32D
].

Definition RV64D_instructions := [
  RV64D_instruction FLD_64D          ; RV64D_instruction FSD_64D          ;
  RV64D_instruction FMADD_RNE_D_64D  ; RV64D_instruction FMADD_RTZ_D_64D  ;
  RV64D_instruction FMADD_RDN_D_64D  ; RV64D_instruction FMADD_RUP_D_64D  ;
  RV64D_instruction FMADD_RMM_D_64D  ; RV64D_instruction FMADD_DYN_D_64D  ;
  RV64D_instruction FMSUB_RNE_D_64D  ; RV64D_instruction FMSUB_RTZ_D_64D  ;
  RV64D_instruction FMSUB_RDN_D_64D  ; RV64D_instruction FMSUB_RUP_D_64D  ;
  RV64D_instruction FMSUB_RMM_D_64D  ; RV64D_instruction FMSUB_DYN_D_64D  ;
  RV64D_instruction FNMSUB_RNE_D_64D ; RV64D_instruction FNMSUB_RTZ_D_64D ;
  RV64D_instruction FNMSUB_RDN_D_64D ; RV64D_instruction FNMSUB_RUP_D_64D ;
  RV64D_instruction FNMSUB_RMM_D_64D ; RV64D_instruction FNMSUB_DYN_D_64D ;
  RV64D_instruction FNMADD_RNE_D_64D ; RV64D_instruction FNMADD_RTZ_D_64D ;
  RV64D_instruction FNMADD_RDN_D_64D ; RV64D_instruction FNMADD_RUP_D_64D ;
  RV64D_instruction FNMADD_RMM_D_64D ; RV64D_instruction FNMADD_DYN_D_64D ;
  RV64D_instruction FADD_RNE_D_64D   ; RV64D_instruction FADD_RTZ_D_64D   ;
  RV64D_instruction FADD_RDN_D_64D   ; RV64D_instruction FADD_RUP_D_64D   ;
  RV64D_instruction FADD_RMM_D_64D   ; RV64D_instruction FADD_DYN_D_64D   ;
  RV64D_instruction FSUB_RNE_D_64D   ; RV64D_instruction FSUB_RTZ_D_64D   ;
  RV64D_instruction FSUB_RDN_D_64D   ; RV64D_instruction FSUB_RUP_D_64D   ;
  RV64D_instruction FSUB_RMM_D_64D   ; RV64D_instruction FSUB_DYN_D_64D   ;
  RV64D_instruction FMUL_RNE_D_64D   ; RV64D_instruction FMUL_RTZ_D_64D   ;
  RV64D_instruction FMUL_RDN_D_64D   ; RV64D_instruction FMUL_RUP_D_64D   ;
  RV64D_instruction FMUL_RMM_D_64D   ; RV64D_instruction FMUL_DYN_D_64D   ;
  RV64D_instruction FDIV_RNE_D_64D   ; RV64D_instruction FDIV_RTZ_D_64D   ;
  RV64D_instruction FDIV_RDN_D_64D   ; RV64D_instruction FDIV_RUP_D_64D   ;
  RV64D_instruction FDIV_RMM_D_64D   ; RV64D_instruction FDIV_DYN_D_64D   ;
  RV64D_instruction FSQRT_RNE_D_64D  ; RV64D_instruction FSQRT_RTZ_D_64D  ;
  RV64D_instruction FSQRT_RDN_D_64D  ; RV64D_instruction FSQRT_RUP_D_64D  ;
  RV64D_instruction FSQRT_RMM_D_64D  ; RV64D_instruction FSQRT_DYN_D_64D  ;
  RV64D_instruction FSGNJ_D_64D      ; RV64D_instruction FSGNJN_D_64D     ;
  RV64D_instruction FSGNJX_D_64D     ; RV64D_instruction FMIN_D_64D       ;
  RV64D_instruction FMAX_D_64D       ; RV64D_instruction FCVT_RNE_S_D_64D ;
  RV64D_instruction FCVT_RTZ_S_D_64D ; RV64D_instruction FCVT_RDN_S_D_64D ;
  RV64D_instruction FCVT_RUP_S_D_64D ; RV64D_instruction FCVT_RMM_S_D_64D ;
  RV64D_instruction FCVT_DYN_S_D_64D ; RV64D_instruction FCVT_RNE_D_S_64D ;
  RV64D_instruction FCVT_RTZ_D_S_64D ; RV64D_instruction FCVT_RDN_D_S_64D ;
  RV64D_instruction FCVT_RUP_D_S_64D ; RV64D_instruction FCVT_RMM_D_S_64D ;
  RV64D_instruction FCVT_DYN_D_S_64D ; RV64D_instruction FEQ_D_64D        ;
  RV64D_instruction FLT_D_64D        ; RV64D_instruction FLE_D_64D        ;
  RV64D_instruction FCLASS_D_64D     ; RV64D_instruction FCVT_RNE_W_D_64D ;
  RV64D_instruction FCVT_RTZ_W_D_64D ; RV64D_instruction FCVT_RDN_W_D_64D ;
  RV64D_instruction FCVT_RUP_W_D_64D ; RV64D_instruction FCVT_RMM_W_D_64D ;
  RV64D_instruction FCVT_DYN_W_D_64D ; RV64D_instruction FCVT_RNE_WU_D_64D;
  RV64D_instruction FCVT_RTZ_WU_D_64D; RV64D_instruction FCVT_RDN_WU_D_64D;
  RV64D_instruction FCVT_RUP_WU_D_64D; RV64D_instruction FCVT_RMM_WU_D_64D;
  RV64D_instruction FCVT_DYN_WU_D_64D; RV64D_instruction FCVT_RNE_D_W_64D ;
  RV64D_instruction FCVT_RTZ_D_W_64D ; RV64D_instruction FCVT_RDN_D_W_64D ;
  RV64D_instruction FCVT_RUP_D_W_64D ; RV64D_instruction FCVT_RMM_D_W_64D ;
  RV64D_instruction FCVT_DYN_D_W_64D ; RV64D_instruction FCVT_RNE_D_WU_64D;
  RV64D_instruction FCVT_RTZ_D_WU_64D; RV64D_instruction FCVT_RDN_D_WU_64D;
  RV64D_instruction FCVT_RUP_D_WU_64D; RV64D_instruction FCVT_RMM_D_WU_64D;
  RV64D_instruction FCVT_DYN_D_WU_64D; RV64D_instruction FCVT_RNE_L_D_64D ;
  RV64D_instruction FCVT_RTZ_L_D_64D ; RV64D_instruction FCVT_RDN_L_D_64D ;
  RV64D_instruction FCVT_RUP_L_D_64D ; RV64D_instruction FCVT_RMM_L_D_64D ;
  RV64D_instruction FCVT_DYN_L_D_64D ; RV64D_instruction FCVT_RNE_LU_D_64D;
  RV64D_instruction FCVT_RTZ_LU_D_64D; RV64D_instruction FCVT_RDN_LU_D_64D;
  RV64D_instruction FCVT_RUP_LU_D_64D; RV64D_instruction FCVT_RMM_LU_D_64D;
  RV64D_instruction FCVT_DYN_LU_D_64D; RV64D_instruction FMV_X_D_64D      ;
  RV64D_instruction FCVT_RNE_D_L_64D ; RV64D_instruction FCVT_RTZ_D_L_64D ;
  RV64D_instruction FCVT_RDN_D_L_64D ; RV64D_instruction FCVT_RUP_D_L_64D ;
  RV64D_instruction FCVT_RMM_D_L_64D ; RV64D_instruction FCVT_DYN_D_L_64D ;
  RV64D_instruction FCVT_RNE_D_LU_64D; RV64D_instruction FCVT_RTZ_D_LU_64D;
  RV64D_instruction FCVT_RDN_D_LU_64D; RV64D_instruction FCVT_RUP_D_LU_64D;
  RV64D_instruction FCVT_RMM_D_LU_64D; RV64D_instruction FCVT_DYN_D_LU_64D;
  RV64D_instruction FMV_D_X_64D
].

Definition RV32Q_instructions := [
  RV32Q_instruction FLQ_32Q          ; RV32Q_instruction FSQ_32Q          ;
  RV32Q_instruction FMADD_RNE_Q_32Q  ; RV32Q_instruction FMADD_RTZ_Q_32Q  ;
  RV32Q_instruction FMADD_RDN_Q_32Q  ; RV32Q_instruction FMADD_RUP_Q_32Q  ;
  RV32Q_instruction FMADD_RMM_Q_32Q  ; RV32Q_instruction FMADD_DYN_Q_32Q  ;
  RV32Q_instruction FMSUB_RNE_Q_32Q  ; RV32Q_instruction FMSUB_RTZ_Q_32Q  ;
  RV32Q_instruction FMSUB_RDN_Q_32Q  ; RV32Q_instruction FMSUB_RUP_Q_32Q  ;
  RV32Q_instruction FMSUB_RMM_Q_32Q  ; RV32Q_instruction FMSUB_DYN_Q_32Q  ;
  RV32Q_instruction FNMSUB_RNE_Q_32Q ; RV32Q_instruction FNMSUB_RTZ_Q_32Q ;
  RV32Q_instruction FNMSUB_RDN_Q_32Q ; RV32Q_instruction FNMSUB_RUP_Q_32Q ;
  RV32Q_instruction FNMSUB_RMM_Q_32Q ; RV32Q_instruction FNMSUB_DYN_Q_32Q ;
  RV32Q_instruction FNMADD_RNE_Q_32Q ; RV32Q_instruction FNMADD_RTZ_Q_32Q ;
  RV32Q_instruction FNMADD_RDN_Q_32Q ; RV32Q_instruction FNMADD_RUP_Q_32Q ;
  RV32Q_instruction FNMADD_RMM_Q_32Q ; RV32Q_instruction FNMADD_DYN_Q_32Q ;
  RV32Q_instruction FADD_RNE_Q_32Q   ; RV32Q_instruction FADD_RTZ_Q_32Q   ;
  RV32Q_instruction FADD_RDN_Q_32Q   ; RV32Q_instruction FADD_RUP_Q_32Q   ;
  RV32Q_instruction FADD_RMM_Q_32Q   ; RV32Q_instruction FADD_DYN_Q_32Q   ;
  RV32Q_instruction FSUB_RNE_Q_32Q   ; RV32Q_instruction FSUB_RTZ_Q_32Q   ;
  RV32Q_instruction FSUB_RDN_Q_32Q   ; RV32Q_instruction FSUB_RUP_Q_32Q   ;
  RV32Q_instruction FSUB_RMM_Q_32Q   ; RV32Q_instruction FSUB_DYN_Q_32Q   ;
  RV32Q_instruction FMUL_RNE_Q_32Q   ; RV32Q_instruction FMUL_RTZ_Q_32Q   ;
  RV32Q_instruction FMUL_RDN_Q_32Q   ; RV32Q_instruction FMUL_RUP_Q_32Q   ;
  RV32Q_instruction FMUL_RMM_Q_32Q   ; RV32Q_instruction FMUL_DYN_Q_32Q   ;
  RV32Q_instruction FDIV_RNE_Q_32Q   ; RV32Q_instruction FDIV_RTZ_Q_32Q   ;
  RV32Q_instruction FDIV_RDN_Q_32Q   ; RV32Q_instruction FDIV_RUP_Q_32Q   ;
  RV32Q_instruction FDIV_RMM_Q_32Q   ; RV32Q_instruction FDIV_DYN_Q_32Q   ;
  RV32Q_instruction FSQRT_RNE_Q_32Q  ; RV32Q_instruction FSQRT_RTZ_Q_32Q  ;
  RV32Q_instruction FSQRT_RDN_Q_32Q  ; RV32Q_instruction FSQRT_RUP_Q_32Q  ;
  RV32Q_instruction FSQRT_RMM_Q_32Q  ; RV32Q_instruction FSQRT_DYN_Q_32Q  ;
  RV32Q_instruction FSGNJ_Q_32Q      ; RV32Q_instruction FSGNJN_Q_32Q     ;
  RV32Q_instruction FSGNJX_Q_32Q     ; RV32Q_instruction FMIN_Q_32Q       ;
  RV32Q_instruction FMAX_Q_32Q       ; RV32Q_instruction FCVT_RNE_S_Q_32Q ;
  RV32Q_instruction FCVT_RTZ_S_Q_32Q ; RV32Q_instruction FCVT_RDN_S_Q_32Q ;
  RV32Q_instruction FCVT_RUP_S_Q_32Q ; RV32Q_instruction FCVT_RMM_S_Q_32Q ;
  RV32Q_instruction FCVT_DYN_S_Q_32Q ; RV32Q_instruction FCVT_RNE_Q_S_32Q ;
  RV32Q_instruction FCVT_RTZ_Q_S_32Q ; RV32Q_instruction FCVT_RDN_Q_S_32Q ;
  RV32Q_instruction FCVT_RUP_Q_S_32Q ; RV32Q_instruction FCVT_RMM_Q_S_32Q ;
  RV32Q_instruction FCVT_DYN_Q_S_32Q ; RV32Q_instruction FCVT_RNE_D_Q_32Q ;
  RV32Q_instruction FCVT_RTZ_D_Q_32Q ; RV32Q_instruction FCVT_RDN_D_Q_32Q ;
  RV32Q_instruction FCVT_RUP_D_Q_32Q ; RV32Q_instruction FCVT_RMM_D_Q_32Q ;
  RV32Q_instruction FCVT_DYN_D_Q_32Q ; RV32Q_instruction FCVT_RNE_Q_D_32Q ;
  RV32Q_instruction FCVT_RTZ_Q_D_32Q ; RV32Q_instruction FCVT_RDN_Q_D_32Q ;
  RV32Q_instruction FCVT_RUP_Q_D_32Q ; RV32Q_instruction FCVT_RMM_Q_D_32Q ;
  RV32Q_instruction FCVT_DYN_Q_D_32Q ; RV32Q_instruction FEQ_Q_32Q        ;
  RV32Q_instruction FLT_Q_32Q        ; RV32Q_instruction FLE_Q_32Q        ;
  RV32Q_instruction FCLASS_Q_32Q     ; RV32Q_instruction FCVT_RNE_W_Q_32Q ;
  RV32Q_instruction FCVT_RTZ_W_Q_32Q ; RV32Q_instruction FCVT_RDN_W_Q_32Q ;
  RV32Q_instruction FCVT_RUP_W_Q_32Q ; RV32Q_instruction FCVT_RMM_W_Q_32Q ;
  RV32Q_instruction FCVT_DYN_W_Q_32Q ; RV32Q_instruction FCVT_RNE_WU_Q_32Q;
  RV32Q_instruction FCVT_RTZ_WU_Q_32Q; RV32Q_instruction FCVT_RDN_WU_Q_32Q;
  RV32Q_instruction FCVT_RUP_WU_Q_32Q; RV32Q_instruction FCVT_RMM_WU_Q_32Q;
  RV32Q_instruction FCVT_DYN_WU_Q_32Q; RV32Q_instruction FCVT_RNE_Q_W_32Q ;
  RV32Q_instruction FCVT_RTZ_Q_W_32Q ; RV32Q_instruction FCVT_RDN_Q_W_32Q ;
  RV32Q_instruction FCVT_RUP_Q_W_32Q ; RV32Q_instruction FCVT_RMM_Q_W_32Q ;
  RV32Q_instruction FCVT_DYN_Q_W_32Q ; RV32Q_instruction FCVT_RNE_Q_WU_32Q;
  RV32Q_instruction FCVT_RTZ_Q_WU_32Q; RV32Q_instruction FCVT_RDN_Q_WU_32Q;
  RV32Q_instruction FCVT_RUP_Q_WU_32Q; RV32Q_instruction FCVT_RMM_Q_WU_32Q;
  RV32Q_instruction FCVT_DYN_Q_WU_32Q
].

Definition RV64Q_instructions := [
  RV64Q_instruction FLQ_64Q          ; RV64Q_instruction FSQ_64Q          ;
  RV64Q_instruction FMADD_RNE_Q_64Q  ; RV64Q_instruction FMADD_RTZ_Q_64Q  ;
  RV64Q_instruction FMADD_RDN_Q_64Q  ; RV64Q_instruction FMADD_RUP_Q_64Q  ;
  RV64Q_instruction FMADD_RMM_Q_64Q  ; RV64Q_instruction FMADD_DYN_Q_64Q  ;
  RV64Q_instruction FMSUB_RNE_Q_64Q  ; RV64Q_instruction FMSUB_RTZ_Q_64Q  ;
  RV64Q_instruction FMSUB_RDN_Q_64Q  ; RV64Q_instruction FMSUB_RUP_Q_64Q  ;
  RV64Q_instruction FMSUB_RMM_Q_64Q  ; RV64Q_instruction FMSUB_DYN_Q_64Q  ;
  RV64Q_instruction FNMSUB_RNE_Q_64Q ; RV64Q_instruction FNMSUB_RTZ_Q_64Q ;
  RV64Q_instruction FNMSUB_RDN_Q_64Q ; RV64Q_instruction FNMSUB_RUP_Q_64Q ;
  RV64Q_instruction FNMSUB_RMM_Q_64Q ; RV64Q_instruction FNMSUB_DYN_Q_64Q ;
  RV64Q_instruction FNMADD_RNE_Q_64Q ; RV64Q_instruction FNMADD_RTZ_Q_64Q ;
  RV64Q_instruction FNMADD_RDN_Q_64Q ; RV64Q_instruction FNMADD_RUP_Q_64Q ;
  RV64Q_instruction FNMADD_RMM_Q_64Q ; RV64Q_instruction FNMADD_DYN_Q_64Q ;
  RV64Q_instruction FADD_RNE_Q_64Q   ; RV64Q_instruction FADD_RTZ_Q_64Q   ;
  RV64Q_instruction FADD_RDN_Q_64Q   ; RV64Q_instruction FADD_RUP_Q_64Q   ;
  RV64Q_instruction FADD_RMM_Q_64Q   ; RV64Q_instruction FADD_DYN_Q_64Q   ;
  RV64Q_instruction FSUB_RNE_Q_64Q   ; RV64Q_instruction FSUB_RTZ_Q_64Q   ;
  RV64Q_instruction FSUB_RDN_Q_64Q   ; RV64Q_instruction FSUB_RUP_Q_64Q   ;
  RV64Q_instruction FSUB_RMM_Q_64Q   ; RV64Q_instruction FSUB_DYN_Q_64Q   ;
  RV64Q_instruction FMUL_RNE_Q_64Q   ; RV64Q_instruction FMUL_RTZ_Q_64Q   ;
  RV64Q_instruction FMUL_RDN_Q_64Q   ; RV64Q_instruction FMUL_RUP_Q_64Q   ;
  RV64Q_instruction FMUL_RMM_Q_64Q   ; RV64Q_instruction FMUL_DYN_Q_64Q   ;
  RV64Q_instruction FDIV_RNE_Q_64Q   ; RV64Q_instruction FDIV_RTZ_Q_64Q   ;
  RV64Q_instruction FDIV_RDN_Q_64Q   ; RV64Q_instruction FDIV_RUP_Q_64Q   ;
  RV64Q_instruction FDIV_RMM_Q_64Q   ; RV64Q_instruction FDIV_DYN_Q_64Q   ;
  RV64Q_instruction FSQRT_RNE_Q_64Q  ; RV64Q_instruction FSQRT_RTZ_Q_64Q  ;
  RV64Q_instruction FSQRT_RDN_Q_64Q  ; RV64Q_instruction FSQRT_RUP_Q_64Q  ;
  RV64Q_instruction FSQRT_RMM_Q_64Q  ; RV64Q_instruction FSQRT_DYN_Q_64Q  ;
  RV64Q_instruction FSGNJ_Q_64Q      ; RV64Q_instruction FSGNJN_Q_64Q     ;
  RV64Q_instruction FSGNJX_Q_64Q     ; RV64Q_instruction FMIN_Q_64Q       ;
  RV64Q_instruction FMAX_Q_64Q       ; RV64Q_instruction FCVT_RNE_S_Q_64Q ;
  RV64Q_instruction FCVT_RTZ_S_Q_64Q ; RV64Q_instruction FCVT_RDN_S_Q_64Q ;
  RV64Q_instruction FCVT_RUP_S_Q_64Q ; RV64Q_instruction FCVT_RMM_S_Q_64Q ;
  RV64Q_instruction FCVT_DYN_S_Q_64Q ; RV64Q_instruction FCVT_RNE_Q_S_64Q ;
  RV64Q_instruction FCVT_RTZ_Q_S_64Q ; RV64Q_instruction FCVT_RDN_Q_S_64Q ;
  RV64Q_instruction FCVT_RUP_Q_S_64Q ; RV64Q_instruction FCVT_RMM_Q_S_64Q ;
  RV64Q_instruction FCVT_DYN_Q_S_64Q ; RV64Q_instruction FCVT_RNE_D_Q_64Q ;
  RV64Q_instruction FCVT_RTZ_D_Q_64Q ; RV64Q_instruction FCVT_RDN_D_Q_64Q ;
  RV64Q_instruction FCVT_RUP_D_Q_64Q ; RV64Q_instruction FCVT_RMM_D_Q_64Q ;
  RV64Q_instruction FCVT_DYN_D_Q_64Q ; RV64Q_instruction FCVT_RNE_Q_D_64Q ;
  RV64Q_instruction FCVT_RTZ_Q_D_64Q ; RV64Q_instruction FCVT_RDN_Q_D_64Q ;
  RV64Q_instruction FCVT_RUP_Q_D_64Q ; RV64Q_instruction FCVT_RMM_Q_D_64Q ;
  RV64Q_instruction FCVT_DYN_Q_D_64Q ; RV64Q_instruction FEQ_Q_64Q        ;
  RV64Q_instruction FLT_Q_64Q        ; RV64Q_instruction FLE_Q_64Q        ;
  RV64Q_instruction FCLASS_Q_64Q     ; RV64Q_instruction FCVT_RNE_W_Q_64Q ;
  RV64Q_instruction FCVT_RTZ_W_Q_64Q ; RV64Q_instruction FCVT_RDN_W_Q_64Q ;
  RV64Q_instruction FCVT_RUP_W_Q_64Q ; RV64Q_instruction FCVT_RMM_W_Q_64Q ;
  RV64Q_instruction FCVT_DYN_W_Q_64Q ; RV64Q_instruction FCVT_RNE_WU_Q_64Q;
  RV64Q_instruction FCVT_RTZ_WU_Q_64Q; RV64Q_instruction FCVT_RDN_WU_Q_64Q;
  RV64Q_instruction FCVT_RUP_WU_Q_64Q; RV64Q_instruction FCVT_RMM_WU_Q_64Q;
  RV64Q_instruction FCVT_DYN_WU_Q_64Q; RV64Q_instruction FCVT_RNE_Q_W_64Q ;
  RV64Q_instruction FCVT_RTZ_Q_W_64Q ; RV64Q_instruction FCVT_RDN_Q_W_64Q ;
  RV64Q_instruction FCVT_RUP_Q_W_64Q ; RV64Q_instruction FCVT_RMM_Q_W_64Q ;
  RV64Q_instruction FCVT_DYN_Q_W_64Q ; RV64Q_instruction FCVT_RNE_Q_WU_64Q;
  RV64Q_instruction FCVT_RTZ_Q_WU_64Q; RV64Q_instruction FCVT_RDN_Q_WU_64Q;
  RV64Q_instruction FCVT_RUP_Q_WU_64Q; RV64Q_instruction FCVT_RMM_Q_WU_64Q;
  RV64Q_instruction FCVT_DYN_Q_WU_64Q; RV64Q_instruction FCVT_RNE_L_Q_64Q ;
  RV64Q_instruction FCVT_RTZ_L_Q_64Q ; RV64Q_instruction FCVT_RDN_L_Q_64Q ;
  RV64Q_instruction FCVT_RUP_L_Q_64Q ; RV64Q_instruction FCVT_RMM_L_Q_64Q ;
  RV64Q_instruction FCVT_DYN_L_Q_64Q ; RV64Q_instruction FCVT_RNE_LU_Q_64Q;
  RV64Q_instruction FCVT_RTZ_LU_Q_64Q; RV64Q_instruction FCVT_RDN_LU_Q_64Q;
  RV64Q_instruction FCVT_RUP_LU_Q_64Q; RV64Q_instruction FCVT_RMM_LU_Q_64Q;
  RV64Q_instruction FCVT_DYN_LU_Q_64Q; RV64Q_instruction FCVT_RNE_Q_L_64Q ;
  RV64Q_instruction FCVT_RTZ_Q_L_64Q ; RV64Q_instruction FCVT_RDN_Q_L_64Q ;
  RV64Q_instruction FCVT_RUP_Q_L_64Q ; RV64Q_instruction FCVT_RMM_Q_L_64Q ;
  RV64Q_instruction FCVT_DYN_Q_L_64Q ; RV64Q_instruction FCVT_RNE_Q_LU_64Q;
  RV64Q_instruction FCVT_RTZ_Q_LU_64Q; RV64Q_instruction FCVT_RDN_Q_LU_64Q;
  RV64Q_instruction FCVT_RUP_Q_LU_64Q; RV64Q_instruction FCVT_RMM_Q_LU_64Q;
  RV64Q_instruction FCVT_DYN_Q_LU_64Q
].

Definition extension_instructions (b : base_standard) (e : extension) :=
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

Definition ISA_instructions_set (isa : ISA) :=
  app (
    match (ISA_base_standard isa) with
    | RV32I => RV32I_instructions
    | RV64I => RV64I_instructions
    end
  )
  (
    fold_left (fun i e =>
      app i (extension_instructions (ISA_base_standard isa) e)
    ) (ISA_extensions isa) []
  ).

Definition instruction_name (i : instruction) : string :=
  match i with
  | RV32I_instruction x =>
    match x with
    | LUI_32I  => "LUI"  | AUIPC_32I => "AUIPC" | JAL_32I   => "JAL"
    | JALR_32I => "JALR" | BEQ_32I   => "BEQ"   | BNE_32I   => "BNE"
    | BLT_32I  => "BLT"  | BGE_32I   => "BGE"   | BLTU_32I  => "BLTU"
    | BGEU_32I => "BGEU" | LB_32I    => "LB"    | LH_32I    => "LH"
    | LW_32I   => "LW"   | LBU_32I   => "LBU"   | LHU_32I   => "LHU"
    | SB_32I   => "SB"   | SH_32I    => "SH"    | SW_32I    => "SW"
    | ADDI_32I => "ADDI" | SLTI_32I  => "SLTI"  | SLTIU_32I => "SLTIU"
    | XORI_32I => "XORI" | ORI_32I   => "ORI"   | ANDI_32I  => "ANDI"
    | SLLI_32I => "SLLI" | SRLI_32I  => "SRLI"  | SRAI_32I  => "SRAI"
    | ADD_32I  => "ADD"  | SUB_32I   => "SUB"   | SLL_32I   => "SLL"
    | SLT_32I  => "SLT"  | SLTU_32I  => "SLTU"  | XOR_32I   => "XOR"
    | SRL_32I  => "SRL"  | SRA_32I   => "SRA"   | OR_32I    => "OR"
    | AND_32I  => "AND"  | FENCE_32I => "FENCE" | ECALL_32I => "ECALL"
    | EBREAK_32I => "EBREAK"
    end
  | RV64I_instruction x =>
    match x with
    | LUI_64I    => "LUI"    | AUIPC_64I  => "AUIPC" | JAL_64I    => "JAL"
    | JALR_64I   => "JALR"   | BEQ_64I    => "BEQ"   | BNE_64I    => "BNE"
    | BLT_64I    => "BLT"    | BGE_64I    => "BGE"   | BLTU_64I   => "BLTU"
    | BGEU_64I   => "BGEU"   | LB_64I     => "LB"    | LH_64I     => "LH"
    | LW_64I     => "LW"     | LBU_64I    => "LBU"   | LHU_64I    => "LHU"
    | SB_64I     => "SB"     | SH_64I     => "SH"    | SW_64I     => "SW"
    | ADDI_64I   => "ADDI"   | SLTI_64I   => "SLTI"  | SLTIU_64I  => "SLTIU"
    | XORI_64I   => "XORI"   | ORI_64I    => "ORI"   | ANDI_64I   => "ANDI"
    | SLLI_64I   => "SLLI"   | SRLI_64I   => "SRLI"  | SRAI_64I   => "SRAI"
    | ADD_64I    => "ADD"    | SUB_64I    => "SUB"   | SLL_64I    => "SLL"
    | SLT_64I    => "SLT"    | SLTU_64I   => "SLTU"  | XOR_64I    => "XOR"
    | SRL_64I    => "SRL"    | SRA_64I    => "SRA"   | OR_64I     => "OR"
    | AND_64I    => "AND"    | FENCE_64I  => "FENCE" | ECALL_64I  => "ECALL"
    | EBREAK_64I => "EBREAK" | LWU_64I    => "LWU"   | LD_64I     => "LD"
    | SD_64I     => "SD"     | ADDIW_64I  => "ADDIW" | SLLIW_64I  => "SLLIW"
    | SRLIW_64I  => "SRLIW"  | SRAIW_64I  => "SRAIW" | ADDW_64I   => "ADDW"
    | SUBW_64I   => "SUBW"   | SLLW_64I   => "SLLW"  | SRLW_64I   => "SRLW"
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
    | CSRRW_32Zicsr  => "CSRRW"  | CSRRS_32Zicsr  => "CSRRS"
    | CSRRC_32Zicsr  => "CSRRC"  | CSRRWI_32Zicsr => "CSRRWI"
    | CSRRSI_32Zicsr => "CSRRSI" | CSRRCI_32Zicsr => "CSRRCI"
    end
  | RV64Zicsr_instruction x =>
    match x with
    | CSRRW_64Zicsr  => "CSRRW"  | CSRRS_64Zicsr  => "CSRRS"
    | CSRRC_64Zicsr  => "CSRRC"  | CSRRWI_64Zicsr => "CSRRWI"
    | CSRRSI_64Zicsr => "CSRRSI" | CSRRCI_64Zicsr => "CSRRCI"
    end
  | RV32M_instruction x =>
    match x with
    | MUL_32M    => "MUL"   | MULH_32M   => "MULH" | MULHSU_32M => "MULHSU"
    | MULHU_32M  => "MULHU" | DIV_32M    => "DIV"  | DIVU_32M   => "DIVU"
    | REM_32M    => "REM"   | REMU_32M   => "REMU"
    end
  | RV64M_instruction x =>
    match x with
    | MUL_64M    => "MUL"   | MULH_64M   => "MULH"  | MULHSU_64M => "MULHSU"
    | MULHU_64M  => "MULHU" | DIV_64M    => "DIV"   | DIVU_64M   => "DIVU"
    | REM_64M    => "REM"   | REMU_64M   => "REMU"  | MULW_64M   => "MULW"
    | DIVW_64M   => "DIVW"  | DIVUW_64M  => "DIVUW" | REMW_64M   => "REMW"
    | REMUW_64M  => "REMUW"
    end
  | RV32A_instruction x =>
    match x with
    | LR_W_00_32A      => "LR.W"      | LR_W_01_32A      => "LR.W"
    | LR_W_10_32A      => "LR.W"      | LR_W_11_32A      => "LR.W"
    | SC_W_00_32A      => "SC.W"      | SC_W_01_32A      => "SC.W"
    | SC_W_10_32A      => "SC.W"      | SC_W_11_32A      => "SC.W"
    | AMOSWAP_W_00_32A => "AMOSWAP.W" | AMOSWAP_W_01_32A => "AMOSWAP.W"
    | AMOSWAP_W_10_32A => "AMOSWAP.W" | AMOSWAP_W_11_32A => "AMOSWAP.W"
    | AMOADD_W_00_32A  => "AMOADD.W"  | AMOADD_W_01_32A  => "AMOADD.W"
    | AMOADD_W_10_32A  => "AMOADD.W"  | AMOADD_W_11_32A  => "AMOADD.W"
    | AMOXOR_W_00_32A  => "AMOXOR.W"  | AMOXOR_W_01_32A  => "AMOXOR.W"
    | AMOXOR_W_10_32A  => "AMOXOR.W"  | AMOXOR_W_11_32A  => "AMOXOR.W"
    | AMOAND_W_00_32A  => "AMOAND.W"  | AMOAND_W_01_32A  => "AMOAND.W"
    | AMOAND_W_10_32A  => "AMOAND.W"  | AMOAND_W_11_32A  => "AMOAND.W"
    | AMOOR_W_00_32A   => "AMOOR.W"   | AMOOR_W_01_32A   => "AMOOR.W"
    | AMOOR_W_10_32A   => "AMOOR.W"   | AMOOR_W_11_32A   => "AMOOR.W"
    | AMOMIN_W_00_32A  => "AMOMIN.W"  | AMOMIN_W_01_32A  => "AMOMIN.W"
    | AMOMIN_W_10_32A  => "AMOMIN.W"  | AMOMIN_W_11_32A  => "AMOMIN.W"
    | AMOMAX_W_00_32A  => "AMOMAX.W"  | AMOMAX_W_01_32A  => "AMOMAX.W"
    | AMOMAX_W_10_32A  => "AMOMAX.W"  | AMOMAX_W_11_32A  => "AMOMAX.W"
    | AMOMINU_W_00_32A => "AMOMINU.W" | AMOMINU_W_01_32A => "AMOMINU.W"
    | AMOMINU_W_10_32A => "AMOMINU.W" | AMOMINU_W_11_32A => "AMOMINU.W"
    | AMOMAXU_W_00_32A => "AMOMAXU.W" | AMOMAXU_W_01_32A => "AMOMAXU.W"
    | AMOMAXU_W_10_32A => "AMOMAXU.W" | AMOMAXU_W_11_32A => "AMOMAXU.W"
    end
  | RV64A_instruction x =>
    match x with
    | LR_W_00_64A      => "LR.W"      | LR_W_01_64A      => "LR.W"
    | LR_W_10_64A      => "LR.W"      | LR_W_11_64A      => "LR.W"
    | SC_W_00_64A      => "SC.W"      | SC_W_01_64A      => "SC.W"
    | SC_W_10_64A      => "SC.W"      | SC_W_11_64A      => "SC.W"
    | AMOSWAP_W_00_64A => "AMOSWAP.W" | AMOSWAP_W_01_64A => "AMOSWAP.W"
    | AMOSWAP_W_10_64A => "AMOSWAP.W" | AMOSWAP_W_11_64A => "AMOSWAP.W"
    | AMOADD_W_00_64A  => "AMOADD.W"  | AMOADD_W_01_64A  => "AMOADD.W"
    | AMOADD_W_10_64A  => "AMOADD.W"  | AMOADD_W_11_64A  => "AMOADD.W"
    | AMOXOR_W_00_64A  => "AMOXOR.W"  | AMOXOR_W_01_64A  => "AMOXOR.W"
    | AMOXOR_W_10_64A  => "AMOXOR.W"  | AMOXOR_W_11_64A  => "AMOXOR.W"
    | AMOAND_W_00_64A  => "AMOAND.W"  | AMOAND_W_01_64A  => "AMOAND.W"
    | AMOAND_W_10_64A  => "AMOAND.W"  | AMOAND_W_11_64A  => "AMOAND.W"
    | AMOOR_W_00_64A   => "AMOOR.W"   | AMOOR_W_01_64A   => "AMOOR.W"
    | AMOOR_W_10_64A   => "AMOOR.W"   | AMOOR_W_11_64A   => "AMOOR.W"
    | AMOMIN_W_00_64A  => "AMOMIN.W"  | AMOMIN_W_01_64A  => "AMOMIN.W"
    | AMOMIN_W_10_64A  => "AMOMIN.W"  | AMOMIN_W_11_64A  => "AMOMIN.W"
    | AMOMAX_W_00_64A  => "AMOMAX.W"  | AMOMAX_W_01_64A  => "AMOMAX.W"
    | AMOMAX_W_10_64A  => "AMOMAX.W"  | AMOMAX_W_11_64A  => "AMOMAX.W"
    | AMOMINU_W_00_64A => "AMOMINU.W" | AMOMINU_W_01_64A => "AMOMINU.W"
    | AMOMINU_W_10_64A => "AMOMINU.W" | AMOMINU_W_11_64A => "AMOMINU.W"
    | AMOMAXU_W_00_64A => "AMOMAXU.W" | AMOMAXU_W_01_64A => "AMOMAXU.W"
    | AMOMAXU_W_10_64A => "AMOMAXU.W" | AMOMAXU_W_11_64A => "AMOMAXU.W"
    | LR_D_00_64A      => "LR.D"      | LR_D_01_64A      => "LR.D"
    | LR_D_10_64A      => "LR.D"      | LR_D_11_64A      => "LR.D"
    | SC_D_00_64A      => "SC.D"      | SC_D_01_64A      => "SC.D"
    | SC_D_10_64A      => "SC.D"      | SC_D_11_64A      => "SC.D"
    | AMOSWAP_D_00_64A => "AMOSWAP.D" | AMOSWAP_D_01_64A => "AMOSWAP.D"
    | AMOSWAP_D_10_64A => "AMOSWAP.D" | AMOSWAP_D_11_64A => "AMOSWAP.D"
    | AMOADD_D_00_64A  => "AMOADD.D"  | AMOADD_D_01_64A  => "AMOADD.D"
    | AMOADD_D_10_64A  => "AMOADD.D"  | AMOADD_D_11_64A  => "AMOADD.D"
    | AMOXOR_D_00_64A  => "AMOXOR.D"  | AMOXOR_D_01_64A  => "AMOXOR.D"
    | AMOXOR_D_10_64A  => "AMOXOR.D"  | AMOXOR_D_11_64A  => "AMOXOR.D"
    | AMOAND_D_00_64A  => "AMOAND.D"  | AMOAND_D_01_64A  => "AMOAND.D"
    | AMOAND_D_10_64A  => "AMOAND.D"  | AMOAND_D_11_64A  => "AMOAND.D"
    | AMOOR_D_00_64A   => "AMOOR.D"   | AMOOR_D_01_64A   => "AMOOR.D"
    | AMOOR_D_10_64A   => "AMOOR.D"   | AMOOR_D_11_64A   => "AMOOR.D"
    | AMOMIN_D_00_64A  => "AMOMIN.D"  | AMOMIN_D_01_64A  => "AMOMIN.D"
    | AMOMIN_D_10_64A  => "AMOMIN.D"  | AMOMIN_D_11_64A  => "AMOMIN.D"
    | AMOMAX_D_00_64A  => "AMOMAX.D"  | AMOMAX_D_01_64A  => "AMOMAX.D"
    | AMOMAX_D_10_64A  => "AMOMAX.D"  | AMOMAX_D_11_64A  => "AMOMAX.D"
    | AMOMINU_D_00_64A => "AMOMINU.D" | AMOMINU_D_01_64A => "AMOMINU.D"
    | AMOMINU_D_10_64A => "AMOMINU.D" | AMOMINU_D_11_64A => "AMOMINU.D"
    | AMOMAXU_D_00_64A => "AMOMAXU.D" | AMOMAXU_D_01_64A => "AMOMAXU.D"
    | AMOMAXU_D_10_64A => "AMOMAXU.D" | AMOMAXU_D_11_64A => "AMOMAXU.D"
    end
  | RV32F_instruction x =>
    match x with
    | FLW_32F           => "FLW"
    | FSW_32F           => "FSW"
    | FMADD_RNE_S_32F   => "FMADD_RNE.S"
    | FMADD_RTZ_S_32F   => "FMADD_RTZ.S"
    | FMADD_RDN_S_32F   => "FMADD_RDN.S"
    | FMADD_RUP_S_32F   => "FMADD_RUP.S"
    | FMADD_RMM_S_32F   => "FMADD_RMM.S"
    | FMADD_DYN_S_32F   => "FMADD_DYN.S"
    | FMSUB_RNE_S_32F   => "FMSUB_RNE.S"
    | FMSUB_RTZ_S_32F   => "FMSUB_RTZ.S"
    | FMSUB_RDN_S_32F   => "FMSUB_RDN.S"
    | FMSUB_RUP_S_32F   => "FMSUB_RUP.S"
    | FMSUB_RMM_S_32F   => "FMSUB_RMM.S"
    | FMSUB_DYN_S_32F   => "FMSUB_DYN.S"
    | FNMSUB_RNE_S_32F  => "FNMSUB_RNE.S"
    | FNMSUB_RTZ_S_32F  => "FNMSUB_RTZ.S"
    | FNMSUB_RDN_S_32F  => "FNMSUB_RDN.S"
    | FNMSUB_RUP_S_32F  => "FNMSUB_RUP.S"
    | FNMSUB_RMM_S_32F  => "FNMSUB_RMM.S"
    | FNMSUB_DYN_S_32F  => "FNMSUB_DYN.S"
    | FNMADD_RNE_S_32F  => "FNMADD_RNE.S"
    | FNMADD_RTZ_S_32F  => "FNMADD_RTZ.S"
    | FNMADD_RDN_S_32F  => "FNMADD_RDN.S"
    | FNMADD_RUP_S_32F  => "FNMADD_RUP.S"
    | FNMADD_RMM_S_32F  => "FNMADD_RMM.S"
    | FNMADD_DYN_S_32F  => "FNMADD_DYN.S"
    | FADD_RNE_S_32F    => "FADD_RNE.S"
    | FADD_RTZ_S_32F    => "FADD_RTZ.S"
    | FADD_RDN_S_32F    => "FADD_RDN.S"
    | FADD_RUP_S_32F    => "FADD_RUP.S"
    | FADD_RMM_S_32F    => "FADD_RMM.S"
    | FADD_DYN_S_32F    => "FADD_DYN.S"
    | FSUB_RNE_S_32F    => "FSUB_RNE.S"
    | FSUB_RTZ_S_32F    => "FSUB_RTZ.S"
    | FSUB_RDN_S_32F    => "FSUB_RDN.S"
    | FSUB_RUP_S_32F    => "FSUB_RUP.S"
    | FSUB_RMM_S_32F    => "FSUB_RMM.S"
    | FSUB_DYN_S_32F    => "FSUB_DYN.S"
    | FMUL_RNE_S_32F    => "FMUL_RNE.S"
    | FMUL_RTZ_S_32F    => "FMUL_RTZ.S"
    | FMUL_RDN_S_32F    => "FMUL_RDN.S"
    | FMUL_RUP_S_32F    => "FMUL_RUP.S"
    | FMUL_RMM_S_32F    => "FMUL_RMM.S"
    | FMUL_DYN_S_32F    => "FMUL_DYN.S"
    | FDIV_RNE_S_32F    => "FDIV_RNE.S"
    | FDIV_RTZ_S_32F    => "FDIV_RTZ.S"
    | FDIV_RDN_S_32F    => "FDIV_RDN.S"
    | FDIV_RUP_S_32F    => "FDIV_RUP.S"
    | FDIV_RMM_S_32F    => "FDIV_RMM.S"
    | FDIV_DYN_S_32F    => "FDIV_DYN.S"
    | FSQRT_RNE_S_32F   => "FSQRT_RNE.S"
    | FSQRT_RTZ_S_32F   => "FSQRT_RTZ.S"
    | FSQRT_RDN_S_32F   => "FSQRT_RDN.S"
    | FSQRT_RUP_S_32F   => "FSQRT_RUP.S"
    | FSQRT_RMM_S_32F   => "FSQRT_RMM.S"
    | FSQRT_DYN_S_32F   => "FSQRT_DYN.S"
    | FSGNJ_S_32F       => "FSGNJ.S"
    | FSGNJN_S_32F      => "FSGNJN.S"
    | FSGNJX_S_32F      => "FSGNJX.S"
    | FMIN_S_32F        => "FMIN.S"
    | FMAX_S_32F        => "FMAX.S"
    | FCVT_RNE_W_S_32F  => "FCVT_RNE.W.S"
    | FCVT_RTZ_W_S_32F  => "FCVT_RTZ.W.S"
    | FCVT_RDN_W_S_32F  => "FCVT_RDN.W.S"
    | FCVT_RUP_W_S_32F  => "FCVT_RUP.W.S"
    | FCVT_RMM_W_S_32F  => "FCVT_RMM.W.S"
    | FCVT_DYN_W_S_32F  => "FCVT_DYN.W.S"
    | FCVT_RNE_WU_S_32F => "FCVT_RNE.WU.S"
    | FCVT_RTZ_WU_S_32F => "FCVT_RTZ.WU.S"
    | FCVT_RDN_WU_S_32F => "FCVT_RDN.WU.S"
    | FCVT_RUP_WU_S_32F => "FCVT_RUP.WU.S"
    | FCVT_RMM_WU_S_32F => "FCVT_RMM.WU.S"
    | FCVT_DYN_WU_S_32F => "FCVT_DYN.WU.S"
    | FMV_X_W_32F       => "FMV.X.W"
    | FEQ_S_32F         => "FEQ.S"
    | FLT_S_32F         => "FLT.S"
    | FLE_S_32F         => "FLE.S"
    | FCLASS_S_32F      => "FCLASS.S"
    | FCVT_RNE_S_W_32F  => "FCVT_RNE.S.W"
    | FCVT_RTZ_S_W_32F  => "FCVT_RTZ.S.W"
    | FCVT_RDN_S_W_32F  => "FCVT_RDN.S.W"
    | FCVT_RUP_S_W_32F  => "FCVT_RUP.S.W"
    | FCVT_RMM_S_W_32F  => "FCVT_RMM.S.W"
    | FCVT_DYN_S_W_32F  => "FCVT_DYN.S.W"
    | FCVT_RNE_S_WU_32F => "FCVT_RNE.S.WU"
    | FCVT_RTZ_S_WU_32F => "FCVT_RTZ.S.WU"
    | FCVT_RDN_S_WU_32F => "FCVT_RDN.S.WU"
    | FCVT_RUP_S_WU_32F => "FCVT_RUP.S.WU"
    | FCVT_RMM_S_WU_32F => "FCVT_RMM.S.WU"
    | FCVT_DYN_S_WU_32F => "FCVT_DYN.S.WU"
    | FMV_W_X_32F       => "FMV.W.X"
    end
  | RV64F_instruction x =>
    match x with
    | FLW_64F           => "FLW"
    | FSW_64F           => "FSW"
    | FMADD_RNE_S_64F   => "FMADD_RNE.S"
    | FMADD_RTZ_S_64F   => "FMADD_RTZ.S"
    | FMADD_RDN_S_64F   => "FMADD_RDN.S"
    | FMADD_RUP_S_64F   => "FMADD_RUP.S"
    | FMADD_RMM_S_64F   => "FMADD_RMM.S"
    | FMADD_DYN_S_64F   => "FMADD_DYN.S"
    | FMSUB_RNE_S_64F   => "FMSUB_RNE.S"
    | FMSUB_RTZ_S_64F   => "FMSUB_RTZ.S"
    | FMSUB_RDN_S_64F   => "FMSUB_RDN.S"
    | FMSUB_RUP_S_64F   => "FMSUB_RUP.S"
    | FMSUB_RMM_S_64F   => "FMSUB_RMM.S"
    | FMSUB_DYN_S_64F   => "FMSUB_DYN.S"
    | FNMSUB_RNE_S_64F  => "FNMSUB_RNE.S"
    | FNMSUB_RTZ_S_64F  => "FNMSUB_RTZ.S"
    | FNMSUB_RDN_S_64F  => "FNMSUB_RDN.S"
    | FNMSUB_RUP_S_64F  => "FNMSUB_RUP.S"
    | FNMSUB_RMM_S_64F  => "FNMSUB_RMM.S"
    | FNMSUB_DYN_S_64F  => "FNMSUB_DYN.S"
    | FNMADD_RNE_S_64F  => "FNMADD_RNE.S"
    | FNMADD_RTZ_S_64F  => "FNMADD_RTZ.S"
    | FNMADD_RDN_S_64F  => "FNMADD_RDN.S"
    | FNMADD_RUP_S_64F  => "FNMADD_RUP.S"
    | FNMADD_RMM_S_64F  => "FNMADD_RMM.S"
    | FNMADD_DYN_S_64F  => "FNMADD_DYN.S"
    | FADD_RNE_S_64F    => "FADD_RNE.S"
    | FADD_RTZ_S_64F    => "FADD_RTZ.S"
    | FADD_RDN_S_64F    => "FADD_RDN.S"
    | FADD_RUP_S_64F    => "FADD_RUP.S"
    | FADD_RMM_S_64F    => "FADD_RMM.S"
    | FADD_DYN_S_64F    => "FADD_DYN.S"
    | FSUB_RNE_S_64F    => "FSUB_RNE.S"
    | FSUB_RTZ_S_64F    => "FSUB_RTZ.S"
    | FSUB_RDN_S_64F    => "FSUB_RDN.S"
    | FSUB_RUP_S_64F    => "FSUB_RUP.S"
    | FSUB_RMM_S_64F    => "FSUB_RMM.S"
    | FSUB_DYN_S_64F    => "FSUB_DYN.S"
    | FMUL_RNE_S_64F    => "FMUL_RNE.S"
    | FMUL_RTZ_S_64F    => "FMUL_RTZ.S"
    | FMUL_RDN_S_64F    => "FMUL_RDN.S"
    | FMUL_RUP_S_64F    => "FMUL_RUP.S"
    | FMUL_RMM_S_64F    => "FMUL_RMM.S"
    | FMUL_DYN_S_64F    => "FMUL_DYN.S"
    | FDIV_RNE_S_64F    => "FDIV_RNE.S"
    | FDIV_RTZ_S_64F    => "FDIV_RTZ.S"
    | FDIV_RDN_S_64F    => "FDIV_RDN.S"
    | FDIV_RUP_S_64F    => "FDIV_RUP.S"
    | FDIV_RMM_S_64F    => "FDIV_RMM.S"
    | FDIV_DYN_S_64F    => "FDIV_DYN.S"
    | FSQRT_RNE_S_64F   => "FSQRT_RNE.S"
    | FSQRT_RTZ_S_64F   => "FSQRT_RTZ.S"
    | FSQRT_RDN_S_64F   => "FSQRT_RDN.S"
    | FSQRT_RUP_S_64F   => "FSQRT_RUP.S"
    | FSQRT_RMM_S_64F   => "FSQRT_RMM.S"
    | FSQRT_DYN_S_64F   => "FSQRT_DYN.S"
    | FSGNJ_S_64F       => "FSGNJ.S"
    | FSGNJN_S_64F      => "FSGNJN.S"
    | FSGNJX_S_64F      => "FSGNJX.S"
    | FMIN_S_64F        => "FMIN.S"
    | FMAX_S_64F        => "FMAX.S"
    | FCVT_RNE_W_S_64F  => "FCVT_RNE.W.S"
    | FCVT_RTZ_W_S_64F  => "FCVT_RTZ.W.S"
    | FCVT_RDN_W_S_64F  => "FCVT_RDN.W.S"
    | FCVT_RUP_W_S_64F  => "FCVT_RUP.W.S"
    | FCVT_RMM_W_S_64F  => "FCVT_RMM.W.S"
    | FCVT_DYN_W_S_64F  => "FCVT_DYN.W.S"
    | FCVT_RNE_WU_S_64F => "FCVT_RNE.WU.S"
    | FCVT_RTZ_WU_S_64F => "FCVT_RTZ.WU.S"
    | FCVT_RDN_WU_S_64F => "FCVT_RDN.WU.S"
    | FCVT_RUP_WU_S_64F => "FCVT_RUP.WU.S"
    | FCVT_RMM_WU_S_64F => "FCVT_RMM.WU.S"
    | FCVT_DYN_WU_S_64F => "FCVT_DYN.WU.S"
    | FMV_X_W_64F       => "FMV.X.W"
    | FEQ_S_64F         => "FEQ.S"
    | FLT_S_64F         => "FLT.S"
    | FLE_S_64F         => "FLE.S"
    | FCLASS_S_64F      => "FCLASS.S"
    | FCVT_RNE_S_W_64F  => "FCVT_RNE.S.W"
    | FCVT_RTZ_S_W_64F  => "FCVT_RTZ.S.W"
    | FCVT_RDN_S_W_64F  => "FCVT_RDN.S.W"
    | FCVT_RUP_S_W_64F  => "FCVT_RUP.S.W"
    | FCVT_RMM_S_W_64F  => "FCVT_RMM.S.W"
    | FCVT_DYN_S_W_64F  => "FCVT_DYN.S.W"
    | FCVT_RNE_S_WU_64F => "FCVT_RNE.S.WU"
    | FCVT_RTZ_S_WU_64F => "FCVT_RTZ.S.WU"
    | FCVT_RDN_S_WU_64F => "FCVT_RDN.S.WU"
    | FCVT_RUP_S_WU_64F => "FCVT_RUP.S.WU"
    | FCVT_RMM_S_WU_64F => "FCVT_RMM.S.WU"
    | FCVT_DYN_S_WU_64F => "FCVT_DYN.S.WU"
    | FMV_W_X_64F       => "FMV.W.X"
    | FCVT_RNE_L_S_64F  => "FCVT_RNE.L.S"
    | FCVT_RTZ_L_S_64F  => "FCVT_RTZ.L.S"
    | FCVT_RDN_L_S_64F  => "FCVT_RDN.L.S"
    | FCVT_RUP_L_S_64F  => "FCVT_RUP.L.S"
    | FCVT_RMM_L_S_64F  => "FCVT_RMM.L.S"
    | FCVT_DYN_L_S_64F  => "FCVT_DYN.L.S"
    | FCVT_RNE_LU_S_64F => "FCVT_RNE.LU.S"
    | FCVT_RTZ_LU_S_64F => "FCVT_RTZ.LU.S"
    | FCVT_RDN_LU_S_64F => "FCVT_RDN.LU.S"
    | FCVT_RUP_LU_S_64F => "FCVT_RUP.LU.S"
    | FCVT_RMM_LU_S_64F => "FCVT_RMM.LU.S"
    | FCVT_DYN_LU_S_64F => "FCVT_DYN.LU.S"
    | FCVT_RNE_S_L_64F  => "FCVT_RNE.S.L"
    | FCVT_RTZ_S_L_64F  => "FCVT_RTZ.S.L"
    | FCVT_RDN_S_L_64F  => "FCVT_RDN.S.L"
    | FCVT_RUP_S_L_64F  => "FCVT_RUP.S.L"
    | FCVT_RMM_S_L_64F  => "FCVT_RMM.S.L"
    | FCVT_DYN_S_L_64F  => "FCVT_DYN.S.L"
    | FCVT_RNE_S_LU_64F => "FCVT_RNE.S.LU"
    | FCVT_RTZ_S_LU_64F => "FCVT_RTZ.S.LU"
    | FCVT_RDN_S_LU_64F => "FCVT_RDN.S.LU"
    | FCVT_RUP_S_LU_64F => "FCVT_RUP.S.LU"
    | FCVT_RMM_S_LU_64F => "FCVT_RMM.S.LU"
    | FCVT_DYN_S_LU_64F => "FCVT_DYN.S.LU"
    end
  | RV32D_instruction x =>
    match x with
    | FLD_32D           => "FLD"
    | FSD_32D           => "FSD"
    | FMADD_RNE_D_32D   => "FMADD_RNE.D"
    | FMADD_RTZ_D_32D   => "FMADD_RTZ.D"
    | FMADD_RDN_D_32D   => "FMADD_RDN.D"
    | FMADD_RUP_D_32D   => "FMADD_RUP.D"
    | FMADD_RMM_D_32D   => "FMADD_RMM.D"
    | FMADD_DYN_D_32D   => "FMADD_DYN.D"
    | FMSUB_RNE_D_32D   => "FMSUB_RNE.D"
    | FMSUB_RTZ_D_32D   => "FMSUB_RTZ.D"
    | FMSUB_RDN_D_32D   => "FMSUB_RDN.D"
    | FMSUB_RUP_D_32D   => "FMSUB_RUP.D"
    | FMSUB_RMM_D_32D   => "FMSUB_RMM.D"
    | FMSUB_DYN_D_32D   => "FMSUB_DYN.D"
    | FNMSUB_RNE_D_32D  => "FNMSUB_RNE.D"
    | FNMSUB_RTZ_D_32D  => "FNMSUB_RTZ.D"
    | FNMSUB_RDN_D_32D  => "FNMSUB_RDN.D"
    | FNMSUB_RUP_D_32D  => "FNMSUB_RUP.D"
    | FNMSUB_RMM_D_32D  => "FNMSUB_RMM.D"
    | FNMSUB_DYN_D_32D  => "FNMSUB_DYN.D"
    | FNMADD_RNE_D_32D  => "FNMADD_RNE.D"
    | FNMADD_RTZ_D_32D  => "FNMADD_RTZ.D"
    | FNMADD_RDN_D_32D  => "FNMADD_RDN.D"
    | FNMADD_RUP_D_32D  => "FNMADD_RUP.D"
    | FNMADD_RMM_D_32D  => "FNMADD_RMM.D"
    | FNMADD_DYN_D_32D  => "FNMADD_DYN.D"
    | FADD_RNE_D_32D    => "FADD_RNE.D"
    | FADD_RTZ_D_32D    => "FADD_RTZ.D"
    | FADD_RDN_D_32D    => "FADD_RDN.D"
    | FADD_RUP_D_32D    => "FADD_RUP.D"
    | FADD_RMM_D_32D    => "FADD_RMM.D"
    | FADD_DYN_D_32D    => "FADD_DYN.D"
    | FSUB_RNE_D_32D    => "FSUB_RNE.D"
    | FSUB_RTZ_D_32D    => "FSUB_RTZ.D"
    | FSUB_RDN_D_32D    => "FSUB_RDN.D"
    | FSUB_RUP_D_32D    => "FSUB_RUP.D"
    | FSUB_RMM_D_32D    => "FSUB_RMM.D"
    | FSUB_DYN_D_32D    => "FSUB_DYN.D"
    | FMUL_RNE_D_32D    => "FMUL_RNE.D"
    | FMUL_RTZ_D_32D    => "FMUL_RTZ.D"
    | FMUL_RDN_D_32D    => "FMUL_RDN.D"
    | FMUL_RUP_D_32D    => "FMUL_RUP.D"
    | FMUL_RMM_D_32D    => "FMUL_RMM.D"
    | FMUL_DYN_D_32D    => "FMUL_DYN.D"
    | FDIV_RNE_D_32D    => "FDIV_RNE.D"
    | FDIV_RTZ_D_32D    => "FDIV_RTZ.D"
    | FDIV_RDN_D_32D    => "FDIV_RDN.D"
    | FDIV_RUP_D_32D    => "FDIV_RUP.D"
    | FDIV_RMM_D_32D    => "FDIV_RMM.D"
    | FDIV_DYN_D_32D    => "FDIV_DYN.D"
    | FSQRT_RNE_D_32D   => "FSQRT_RNE.D"
    | FSQRT_RTZ_D_32D   => "FSQRT_RTZ.D"
    | FSQRT_RDN_D_32D   => "FSQRT_RDN.D"
    | FSQRT_RUP_D_32D   => "FSQRT_RUP.D"
    | FSQRT_RMM_D_32D   => "FSQRT_RMM.D"
    | FSQRT_DYN_D_32D   => "FSQRT_DYN.D"
    | FSGNJ_D_32D       => "FSGNJ.D"
    | FSGNJN_D_32D      => "FSGNJN.D"
    | FSGNJX_D_32D      => "FSGNJX.D"
    | FMIN_D_32D        => "FMIN.D"
    | FMAX_D_32D        => "FMAX.D"
    | FCVT_RNE_S_D_32D  => "FCVT_RNE.S.D"
    | FCVT_RTZ_S_D_32D  => "FCVT_RTZ.S.D"
    | FCVT_RDN_S_D_32D  => "FCVT_RDN.S.D"
    | FCVT_RUP_S_D_32D  => "FCVT_RUP.S.D"
    | FCVT_RMM_S_D_32D  => "FCVT_RMM.S.D"
    | FCVT_DYN_S_D_32D  => "FCVT_DYN.S.D"
    | FCVT_RNE_D_S_32D  => "FCVT_RNE.D.S"
    | FCVT_RTZ_D_S_32D  => "FCVT_RTZ.D.S"
    | FCVT_RDN_D_S_32D  => "FCVT_RDN.D.S"
    | FCVT_RUP_D_S_32D  => "FCVT_RUP.D.S"
    | FCVT_RMM_D_S_32D  => "FCVT_RMM.D.S"
    | FCVT_DYN_D_S_32D  => "FCVT_DYN.D.S"
    | FEQ_D_32D         => "FEQ.D"
    | FLT_D_32D         => "FLT.D"
    | FLE_D_32D         => "FLE.D"
    | FCLASS_D_32D      => "FCLASS.D"
    | FCVT_RNE_W_D_32D  => "FCVT_RNE.W.D"
    | FCVT_RTZ_W_D_32D  => "FCVT_RTZ.W.D"
    | FCVT_RDN_W_D_32D  => "FCVT_RDN.W.D"
    | FCVT_RUP_W_D_32D  => "FCVT_RUP.W.D"
    | FCVT_RMM_W_D_32D  => "FCVT_RMM.W.D"
    | FCVT_DYN_W_D_32D  => "FCVT_DYN.W.D"
    | FCVT_RNE_WU_D_32D => "FCVT_RNE.WU.D"
    | FCVT_RTZ_WU_D_32D => "FCVT_RTZ.WU.D"
    | FCVT_RDN_WU_D_32D => "FCVT_RDN.WU.D"
    | FCVT_RUP_WU_D_32D => "FCVT_RUP.WU.D"
    | FCVT_RMM_WU_D_32D => "FCVT_RMM.WU.D"
    | FCVT_DYN_WU_D_32D => "FCVT_DYN.WU.D"
    | FCVT_RNE_D_W_32D  => "FCVT_RNE.D.W"
    | FCVT_RTZ_D_W_32D  => "FCVT_RTZ.D.W"
    | FCVT_RDN_D_W_32D  => "FCVT_RDN.D.W"
    | FCVT_RUP_D_W_32D  => "FCVT_RUP.D.W"
    | FCVT_RMM_D_W_32D  => "FCVT_RMM.D.W"
    | FCVT_DYN_D_W_32D  => "FCVT_DYN.D.W"
    | FCVT_RNE_D_WU_32D => "FCVT_RNE.D.WU"
    | FCVT_RTZ_D_WU_32D => "FCVT_RTZ.D.WU"
    | FCVT_RDN_D_WU_32D => "FCVT_RDN.D.WU"
    | FCVT_RUP_D_WU_32D => "FCVT_RUP.D.WU"
    | FCVT_RMM_D_WU_32D => "FCVT_RMM.D.WU"
    | FCVT_DYN_D_WU_32D => "FCVT_DYN.D.WU"
    end
  | RV64D_instruction x =>
    match x with
    | FLD_64D           => "FLD"
    | FSD_64D           => "FSD"
    | FMADD_RNE_D_64D   => "FMADD_RNE.D"
    | FMADD_RTZ_D_64D   => "FMADD_RTZ.D"
    | FMADD_RDN_D_64D   => "FMADD_RDN.D"
    | FMADD_RUP_D_64D   => "FMADD_RUP.D"
    | FMADD_RMM_D_64D   => "FMADD_RMM.D"
    | FMADD_DYN_D_64D   => "FMADD_DYN.D"
    | FMSUB_RNE_D_64D   => "FMSUB_RNE.D"
    | FMSUB_RTZ_D_64D   => "FMSUB_RTZ.D"
    | FMSUB_RDN_D_64D   => "FMSUB_RDN.D"
    | FMSUB_RUP_D_64D   => "FMSUB_RUP.D"
    | FMSUB_RMM_D_64D   => "FMSUB_RMM.D"
    | FMSUB_DYN_D_64D   => "FMSUB_DYN.D"
    | FNMSUB_RNE_D_64D  => "FNMSUB_RNE.D"
    | FNMSUB_RTZ_D_64D  => "FNMSUB_RTZ.D"
    | FNMSUB_RDN_D_64D  => "FNMSUB_RDN.D"
    | FNMSUB_RUP_D_64D  => "FNMSUB_RUP.D"
    | FNMSUB_RMM_D_64D  => "FNMSUB_RMM.D"
    | FNMSUB_DYN_D_64D  => "FNMSUB_DYN.D"
    | FNMADD_RNE_D_64D  => "FNMADD_RNE.D"
    | FNMADD_RTZ_D_64D  => "FNMADD_RTZ.D"
    | FNMADD_RDN_D_64D  => "FNMADD_RDN.D"
    | FNMADD_RUP_D_64D  => "FNMADD_RUP.D"
    | FNMADD_RMM_D_64D  => "FNMADD_RMM.D"
    | FNMADD_DYN_D_64D  => "FNMADD_DYN.D"
    | FADD_RNE_D_64D    => "FADD_RNE.D"
    | FADD_RTZ_D_64D    => "FADD_RTZ.D"
    | FADD_RDN_D_64D    => "FADD_RDN.D"
    | FADD_RUP_D_64D    => "FADD_RUP.D"
    | FADD_RMM_D_64D    => "FADD_RMM.D"
    | FADD_DYN_D_64D    => "FADD_DYN.D"
    | FSUB_RNE_D_64D    => "FSUB_RNE.D"
    | FSUB_RTZ_D_64D    => "FSUB_RTZ.D"
    | FSUB_RDN_D_64D    => "FSUB_RDN.D"
    | FSUB_RUP_D_64D    => "FSUB_RUP.D"
    | FSUB_RMM_D_64D    => "FSUB_RMM.D"
    | FSUB_DYN_D_64D    => "FSUB_DYN.D"
    | FMUL_RNE_D_64D    => "FMUL_RNE.D"
    | FMUL_RTZ_D_64D    => "FMUL_RTZ.D"
    | FMUL_RDN_D_64D    => "FMUL_RDN.D"
    | FMUL_RUP_D_64D    => "FMUL_RUP.D"
    | FMUL_RMM_D_64D    => "FMUL_RMM.D"
    | FMUL_DYN_D_64D    => "FMUL_DYN.D"
    | FDIV_RNE_D_64D    => "FDIV_RNE.D"
    | FDIV_RTZ_D_64D    => "FDIV_RTZ.D"
    | FDIV_RDN_D_64D    => "FDIV_RDN.D"
    | FDIV_RUP_D_64D    => "FDIV_RUP.D"
    | FDIV_RMM_D_64D    => "FDIV_RMM.D"
    | FDIV_DYN_D_64D    => "FDIV_DYN.D"
    | FSQRT_RNE_D_64D   => "FSQRT_RNE.D"
    | FSQRT_RTZ_D_64D   => "FSQRT_RTZ.D"
    | FSQRT_RDN_D_64D   => "FSQRT_RDN.D"
    | FSQRT_RUP_D_64D   => "FSQRT_RUP.D"
    | FSQRT_RMM_D_64D   => "FSQRT_RMM.D"
    | FSQRT_DYN_D_64D   => "FSQRT_DYN.D"
    | FSGNJ_D_64D       => "FSGNJ.D"
    | FSGNJN_D_64D      => "FSGNJN.D"
    | FSGNJX_D_64D      => "FSGNJX.D"
    | FMIN_D_64D        => "FMIN.D"
    | FMAX_D_64D        => "FMAX.D"
    | FCVT_RNE_S_D_64D  => "FCVT_RNE.S.D"
    | FCVT_RTZ_S_D_64D  => "FCVT_RTZ.S.D"
    | FCVT_RDN_S_D_64D  => "FCVT_RDN.S.D"
    | FCVT_RUP_S_D_64D  => "FCVT_RUP.S.D"
    | FCVT_RMM_S_D_64D  => "FCVT_RMM.S.D"
    | FCVT_DYN_S_D_64D  => "FCVT_DYN.S.D"
    | FCVT_RNE_D_S_64D  => "FCVT_RNE.D.S"
    | FCVT_RTZ_D_S_64D  => "FCVT_RTZ.D.S"
    | FCVT_RDN_D_S_64D  => "FCVT_RDN.D.S"
    | FCVT_RUP_D_S_64D  => "FCVT_RUP.D.S"
    | FCVT_RMM_D_S_64D  => "FCVT_RMM.D.S"
    | FCVT_DYN_D_S_64D  => "FCVT_DYN.D.S"
    | FEQ_D_64D         => "FEQ.D"
    | FLT_D_64D         => "FLT.D"
    | FLE_D_64D         => "FLE.D"
    | FCLASS_D_64D      => "FCLASS.D"
    | FCVT_RNE_W_D_64D  => "FCVT_RNE.W.D"
    | FCVT_RTZ_W_D_64D  => "FCVT_RTZ.W.D"
    | FCVT_RDN_W_D_64D  => "FCVT_RDN.W.D"
    | FCVT_RUP_W_D_64D  => "FCVT_RUP.W.D"
    | FCVT_RMM_W_D_64D  => "FCVT_RMM.W.D"
    | FCVT_DYN_W_D_64D  => "FCVT_DYN.W.D"
    | FCVT_RNE_WU_D_64D => "FCVT_RNE.WU.D"
    | FCVT_RTZ_WU_D_64D => "FCVT_RTZ.WU.D"
    | FCVT_RDN_WU_D_64D => "FCVT_RDN.WU.D"
    | FCVT_RUP_WU_D_64D => "FCVT_RUP.WU.D"
    | FCVT_RMM_WU_D_64D => "FCVT_RMM.WU.D"
    | FCVT_DYN_WU_D_64D => "FCVT_DYN.WU.D"
    | FCVT_RNE_D_W_64D  => "FCVT_RNE.D.W"
    | FCVT_RTZ_D_W_64D  => "FCVT_RTZ.D.W"
    | FCVT_RDN_D_W_64D  => "FCVT_RDN.D.W"
    | FCVT_RUP_D_W_64D  => "FCVT_RUP.D.W"
    | FCVT_RMM_D_W_64D  => "FCVT_RMM.D.W"
    | FCVT_DYN_D_W_64D  => "FCVT_DYN.D.W"
    | FCVT_RNE_D_WU_64D => "FCVT_RNE.D.WU"
    | FCVT_RTZ_D_WU_64D => "FCVT_RTZ.D.WU"
    | FCVT_RDN_D_WU_64D => "FCVT_RDN.D.WU"
    | FCVT_RUP_D_WU_64D => "FCVT_RUP.D.WU"
    | FCVT_RMM_D_WU_64D => "FCVT_RMM.D.WU"
    | FCVT_DYN_D_WU_64D => "FCVT_DYN.D.WU"
    | FCVT_RNE_L_D_64D  => "FCVT_RNE.L.D"
    | FCVT_RTZ_L_D_64D  => "FCVT_RTZ.L.D"
    | FCVT_RDN_L_D_64D  => "FCVT_RDN.L.D"
    | FCVT_RUP_L_D_64D  => "FCVT_RUP.L.D"
    | FCVT_RMM_L_D_64D  => "FCVT_RMM.L.D"
    | FCVT_DYN_L_D_64D  => "FCVT_DYN.L.D"
    | FCVT_RNE_LU_D_64D => "FCVT_RNE.LU.D"
    | FCVT_RTZ_LU_D_64D => "FCVT_RTZ.LU.D"
    | FCVT_RDN_LU_D_64D => "FCVT_RDN.LU.D"
    | FCVT_RUP_LU_D_64D => "FCVT_RUP.LU.D"
    | FCVT_RMM_LU_D_64D => "FCVT_RMM.LU.D"
    | FCVT_DYN_LU_D_64D => "FCVT_DYN.LU.D"
    | FMV_X_D_64D       => "FMV.X.D"
    | FCVT_RNE_D_L_64D  => "FCVT_RNE.D.L"
    | FCVT_RTZ_D_L_64D  => "FCVT_RTZ.D.L"
    | FCVT_RDN_D_L_64D  => "FCVT_RDN.D.L"
    | FCVT_RUP_D_L_64D  => "FCVT_RUP.D.L"
    | FCVT_RMM_D_L_64D  => "FCVT_RMM.D.L"
    | FCVT_DYN_D_L_64D  => "FCVT_DYN.D.L"
    | FCVT_RNE_D_LU_64D => "FCVT_RNE.D.LU"
    | FCVT_RTZ_D_LU_64D => "FCVT_RTZ.D.LU"
    | FCVT_RDN_D_LU_64D => "FCVT_RDN.D.LU"
    | FCVT_RUP_D_LU_64D => "FCVT_RUP.D.LU"
    | FCVT_RMM_D_LU_64D => "FCVT_RMM.D.LU"
    | FCVT_DYN_D_LU_64D => "FCVT_DYN.D.LU"
    | FMV_D_X_64D       => "FMV.D.X"
    end
  | RV32Q_instruction x =>
    match x with
    | FLQ_32Q           => "FLQ"
    | FSQ_32Q           => "FSQ"
    | FMADD_RNE_Q_32Q   => "FMADD_RNE.Q"
    | FMADD_RTZ_Q_32Q   => "FMADD_RTZ.Q"
    | FMADD_RDN_Q_32Q   => "FMADD_RDN.Q"
    | FMADD_RUP_Q_32Q   => "FMADD_RUP.Q"
    | FMADD_RMM_Q_32Q   => "FMADD_RMM.Q"
    | FMADD_DYN_Q_32Q   => "FMADD_DYN.Q"
    | FMSUB_RNE_Q_32Q   => "FMSUB_RNE.Q"
    | FMSUB_RTZ_Q_32Q   => "FMSUB_RTZ.Q"
    | FMSUB_RDN_Q_32Q   => "FMSUB_RDN.Q"
    | FMSUB_RUP_Q_32Q   => "FMSUB_RUP.Q"
    | FMSUB_RMM_Q_32Q   => "FMSUB_RMM.Q"
    | FMSUB_DYN_Q_32Q   => "FMSUB_DYN.Q"
    | FNMSUB_RNE_Q_32Q  => "FNMSUB_RNE.Q"
    | FNMSUB_RTZ_Q_32Q  => "FNMSUB_RTZ.Q"
    | FNMSUB_RDN_Q_32Q  => "FNMSUB_RDN.Q"
    | FNMSUB_RUP_Q_32Q  => "FNMSUB_RUP.Q"
    | FNMSUB_RMM_Q_32Q  => "FNMSUB_RMM.Q"
    | FNMSUB_DYN_Q_32Q  => "FNMSUB_DYN.Q"
    | FNMADD_RNE_Q_32Q  => "FNMADD_RNE.Q"
    | FNMADD_RTZ_Q_32Q  => "FNMADD_RTZ.Q"
    | FNMADD_RDN_Q_32Q  => "FNMADD_RDN.Q"
    | FNMADD_RUP_Q_32Q  => "FNMADD_RUP.Q"
    | FNMADD_RMM_Q_32Q  => "FNMADD_RMM.Q"
    | FNMADD_DYN_Q_32Q  => "FNMADD_DYN.Q"
    | FADD_RNE_Q_32Q    => "FADD_RNE.Q"
    | FADD_RTZ_Q_32Q    => "FADD_RTZ.Q"
    | FADD_RDN_Q_32Q    => "FADD_RDN.Q"
    | FADD_RUP_Q_32Q    => "FADD_RUP.Q"
    | FADD_RMM_Q_32Q    => "FADD_RMM.Q"
    | FADD_DYN_Q_32Q    => "FADD_DYN.Q"
    | FSUB_RNE_Q_32Q    => "FSUB_RNE.Q"
    | FSUB_RTZ_Q_32Q    => "FSUB_RTZ.Q"
    | FSUB_RDN_Q_32Q    => "FSUB_RDN.Q"
    | FSUB_RUP_Q_32Q    => "FSUB_RUP.Q"
    | FSUB_RMM_Q_32Q    => "FSUB_RMM.Q"
    | FSUB_DYN_Q_32Q    => "FSUB_DYN.Q"
    | FMUL_RNE_Q_32Q    => "FMUL_RNE.Q"
    | FMUL_RTZ_Q_32Q    => "FMUL_RTZ.Q"
    | FMUL_RDN_Q_32Q    => "FMUL_RDN.Q"
    | FMUL_RUP_Q_32Q    => "FMUL_RUP.Q"
    | FMUL_RMM_Q_32Q    => "FMUL_RMM.Q"
    | FMUL_DYN_Q_32Q    => "FMUL_DYN.Q"
    | FDIV_RNE_Q_32Q    => "FDIV_RNE.Q"
    | FDIV_RTZ_Q_32Q    => "FDIV_RTZ.Q"
    | FDIV_RDN_Q_32Q    => "FDIV_RDN.Q"
    | FDIV_RUP_Q_32Q    => "FDIV_RUP.Q"
    | FDIV_RMM_Q_32Q    => "FDIV_RMM.Q"
    | FDIV_DYN_Q_32Q    => "FDIV_DYN.Q"
    | FSQRT_RNE_Q_32Q   => "FSQRT_RNE.Q"
    | FSQRT_RTZ_Q_32Q   => "FSQRT_RTZ.Q"
    | FSQRT_RDN_Q_32Q   => "FSQRT_RDN.Q"
    | FSQRT_RUP_Q_32Q   => "FSQRT_RUP.Q"
    | FSQRT_RMM_Q_32Q   => "FSQRT_RMM.Q"
    | FSQRT_DYN_Q_32Q   => "FSQRT_DYN.Q"
    | FSGNJ_Q_32Q       => "FSGNJ.Q"
    | FSGNJN_Q_32Q      => "FSGNJN.Q"
    | FSGNJX_Q_32Q      => "FSGNJX.Q"
    | FMIN_Q_32Q        => "FMIN.Q"
    | FMAX_Q_32Q        => "FMAX.Q"
    | FCVT_RNE_S_Q_32Q  => "FCVT_RNE.S.Q"
    | FCVT_RTZ_S_Q_32Q  => "FCVT_RTZ.S.Q"
    | FCVT_RDN_S_Q_32Q  => "FCVT_RDN.S.Q"
    | FCVT_RUP_S_Q_32Q  => "FCVT_RUP.S.Q"
    | FCVT_RMM_S_Q_32Q  => "FCVT_RMM.S.Q"
    | FCVT_DYN_S_Q_32Q  => "FCVT_DYN.S.Q"
    | FCVT_RNE_Q_S_32Q  => "FCVT_RNE.Q.S"
    | FCVT_RTZ_Q_S_32Q  => "FCVT_RTZ.Q.S"
    | FCVT_RDN_Q_S_32Q  => "FCVT_RDN.Q.S"
    | FCVT_RUP_Q_S_32Q  => "FCVT_RUP.Q.S"
    | FCVT_RMM_Q_S_32Q  => "FCVT_RMM.Q.S"
    | FCVT_DYN_Q_S_32Q  => "FCVT_DYN.Q.S"
    | FCVT_RNE_D_Q_32Q  => "FCVT_RNE.D.Q"
    | FCVT_RTZ_D_Q_32Q  => "FCVT_RTZ.D.Q"
    | FCVT_RDN_D_Q_32Q  => "FCVT_RDN.D.Q"
    | FCVT_RUP_D_Q_32Q  => "FCVT_RUP.D.Q"
    | FCVT_RMM_D_Q_32Q  => "FCVT_RMM.D.Q"
    | FCVT_DYN_D_Q_32Q  => "FCVT_DYN.D.Q"
    | FCVT_RNE_Q_D_32Q  => "FCVT_RNE.Q.D"
    | FCVT_RTZ_Q_D_32Q  => "FCVT_RTZ.Q.D"
    | FCVT_RDN_Q_D_32Q  => "FCVT_RDN.Q.D"
    | FCVT_RUP_Q_D_32Q  => "FCVT_RUP.Q.D"
    | FCVT_RMM_Q_D_32Q  => "FCVT_RMM.Q.D"
    | FCVT_DYN_Q_D_32Q  => "FCVT_DYN.Q.D"
    | FEQ_Q_32Q         => "FEQ.Q"
    | FLT_Q_32Q         => "FLT.Q"
    | FLE_Q_32Q         => "FLE.Q"
    | FCLASS_Q_32Q      => "FCLASS.Q"
    | FCVT_RNE_W_Q_32Q  => "FCVT_RNE.W.Q"
    | FCVT_RTZ_W_Q_32Q  => "FCVT_RTZ.W.Q"
    | FCVT_RDN_W_Q_32Q  => "FCVT_RDN.W.Q"
    | FCVT_RUP_W_Q_32Q  => "FCVT_RUP.W.Q"
    | FCVT_RMM_W_Q_32Q  => "FCVT_RMM.W.Q"
    | FCVT_DYN_W_Q_32Q  => "FCVT_DYN.W.Q"
    | FCVT_RNE_WU_Q_32Q => "FCVT_RNE.WU.Q"
    | FCVT_RTZ_WU_Q_32Q => "FCVT_RTZ.WU.Q"
    | FCVT_RDN_WU_Q_32Q => "FCVT_RDN.WU.Q"
    | FCVT_RUP_WU_Q_32Q => "FCVT_RUP.WU.Q"
    | FCVT_RMM_WU_Q_32Q => "FCVT_RMM.WU.Q"
    | FCVT_DYN_WU_Q_32Q => "FCVT_DYN.WU.Q"
    | FCVT_RNE_Q_W_32Q  => "FCVT_RNE.Q.W"
    | FCVT_RTZ_Q_W_32Q  => "FCVT_RTZ.Q.W"
    | FCVT_RDN_Q_W_32Q  => "FCVT_RDN.Q.W"
    | FCVT_RUP_Q_W_32Q  => "FCVT_RUP.Q.W"
    | FCVT_RMM_Q_W_32Q  => "FCVT_RMM.Q.W"
    | FCVT_DYN_Q_W_32Q  => "FCVT_DYN.Q.W"
    | FCVT_RNE_Q_WU_32Q => "FCVT_RNE.Q.WU"
    | FCVT_RTZ_Q_WU_32Q => "FCVT_RTZ.Q.WU"
    | FCVT_RDN_Q_WU_32Q => "FCVT_RDN.Q.WU"
    | FCVT_RUP_Q_WU_32Q => "FCVT_RUP.Q.WU"
    | FCVT_RMM_Q_WU_32Q => "FCVT_RMM.Q.WU"
    | FCVT_DYN_Q_WU_32Q => "FCVT_DYN.Q.WU"
    end
  | RV64Q_instruction x =>
    match x with
    | FLQ_64Q           => "FLQ"
    | FSQ_64Q           => "FSQ"
    | FMADD_RNE_Q_64Q   => "FMADD_RNE.Q"
    | FMADD_RTZ_Q_64Q   => "FMADD_RTZ.Q"
    | FMADD_RDN_Q_64Q   => "FMADD_RDN.Q"
    | FMADD_RUP_Q_64Q   => "FMADD_RUP.Q"
    | FMADD_RMM_Q_64Q   => "FMADD_RMM.Q"
    | FMADD_DYN_Q_64Q   => "FMADD_DYN.Q"
    | FMSUB_RNE_Q_64Q   => "FMSUB_RNE.Q"
    | FMSUB_RTZ_Q_64Q   => "FMSUB_RTZ.Q"
    | FMSUB_RDN_Q_64Q   => "FMSUB_RDN.Q"
    | FMSUB_RUP_Q_64Q   => "FMSUB_RUP.Q"
    | FMSUB_RMM_Q_64Q   => "FMSUB_RMM.Q"
    | FMSUB_DYN_Q_64Q   => "FMSUB_DYN.Q"
    | FNMSUB_RNE_Q_64Q  => "FNMSUB_RNE.Q"
    | FNMSUB_RTZ_Q_64Q  => "FNMSUB_RTZ.Q"
    | FNMSUB_RDN_Q_64Q  => "FNMSUB_RDN.Q"
    | FNMSUB_RUP_Q_64Q  => "FNMSUB_RUP.Q"
    | FNMSUB_RMM_Q_64Q  => "FNMSUB_RMM.Q"
    | FNMSUB_DYN_Q_64Q  => "FNMSUB_DYN.Q"
    | FNMADD_RNE_Q_64Q  => "FNMADD_RNE.Q"
    | FNMADD_RTZ_Q_64Q  => "FNMADD_RTZ.Q"
    | FNMADD_RDN_Q_64Q  => "FNMADD_RDN.Q"
    | FNMADD_RUP_Q_64Q  => "FNMADD_RUP.Q"
    | FNMADD_RMM_Q_64Q  => "FNMADD_RMM.Q"
    | FNMADD_DYN_Q_64Q  => "FNMADD_DYN.Q"
    | FADD_RNE_Q_64Q    => "FADD_RNE.Q"
    | FADD_RTZ_Q_64Q    => "FADD_RTZ.Q"
    | FADD_RDN_Q_64Q    => "FADD_RDN.Q"
    | FADD_RUP_Q_64Q    => "FADD_RUP.Q"
    | FADD_RMM_Q_64Q    => "FADD_RMM.Q"
    | FADD_DYN_Q_64Q    => "FADD_DYN.Q"
    | FSUB_RNE_Q_64Q    => "FSUB_RNE.Q"
    | FSUB_RTZ_Q_64Q    => "FSUB_RTZ.Q"
    | FSUB_RDN_Q_64Q    => "FSUB_RDN.Q"
    | FSUB_RUP_Q_64Q    => "FSUB_RUP.Q"
    | FSUB_RMM_Q_64Q    => "FSUB_RMM.Q"
    | FSUB_DYN_Q_64Q    => "FSUB_DYN.Q"
    | FMUL_RNE_Q_64Q    => "FMUL_RNE.Q"
    | FMUL_RTZ_Q_64Q    => "FMUL_RTZ.Q"
    | FMUL_RDN_Q_64Q    => "FMUL_RDN.Q"
    | FMUL_RUP_Q_64Q    => "FMUL_RUP.Q"
    | FMUL_RMM_Q_64Q    => "FMUL_RMM.Q"
    | FMUL_DYN_Q_64Q    => "FMUL_DYN.Q"
    | FDIV_RNE_Q_64Q    => "FDIV_RNE.Q"
    | FDIV_RTZ_Q_64Q    => "FDIV_RTZ.Q"
    | FDIV_RDN_Q_64Q    => "FDIV_RDN.Q"
    | FDIV_RUP_Q_64Q    => "FDIV_RUP.Q"
    | FDIV_RMM_Q_64Q    => "FDIV_RMM.Q"
    | FDIV_DYN_Q_64Q    => "FDIV_DYN.Q"
    | FSQRT_RNE_Q_64Q   => "FSQRT_RNE.Q"
    | FSQRT_RTZ_Q_64Q   => "FSQRT_RTZ.Q"
    | FSQRT_RDN_Q_64Q   => "FSQRT_RDN.Q"
    | FSQRT_RUP_Q_64Q   => "FSQRT_RUP.Q"
    | FSQRT_RMM_Q_64Q   => "FSQRT_RMM.Q"
    | FSQRT_DYN_Q_64Q   => "FSQRT_DYN.Q"
    | FSGNJ_Q_64Q       => "FSGNJ.Q"
    | FSGNJN_Q_64Q      => "FSGNJN.Q"
    | FSGNJX_Q_64Q      => "FSGNJX.Q"
    | FMIN_Q_64Q        => "FMIN.Q"
    | FMAX_Q_64Q        => "FMAX.Q"
    | FCVT_RNE_S_Q_64Q  => "FCVT_RNE.S.Q"
    | FCVT_RTZ_S_Q_64Q  => "FCVT_RTZ.S.Q"
    | FCVT_RDN_S_Q_64Q  => "FCVT_RDN.S.Q"
    | FCVT_RUP_S_Q_64Q  => "FCVT_RUP.S.Q"
    | FCVT_RMM_S_Q_64Q  => "FCVT_RMM.S.Q"
    | FCVT_DYN_S_Q_64Q  => "FCVT_DYN.S.Q"
    | FCVT_RNE_Q_S_64Q  => "FCVT_RNE.Q.S"
    | FCVT_RTZ_Q_S_64Q  => "FCVT_RTZ.Q.S"
    | FCVT_RDN_Q_S_64Q  => "FCVT_RDN.Q.S"
    | FCVT_RUP_Q_S_64Q  => "FCVT_RUP.Q.S"
    | FCVT_RMM_Q_S_64Q  => "FCVT_RMM.Q.S"
    | FCVT_DYN_Q_S_64Q  => "FCVT_DYN.Q.S"
    | FCVT_RNE_D_Q_64Q  => "FCVT_RNE.D.Q"
    | FCVT_RTZ_D_Q_64Q  => "FCVT_RTZ.D.Q"
    | FCVT_RDN_D_Q_64Q  => "FCVT_RDN.D.Q"
    | FCVT_RUP_D_Q_64Q  => "FCVT_RUP.D.Q"
    | FCVT_RMM_D_Q_64Q  => "FCVT_RMM.D.Q"
    | FCVT_DYN_D_Q_64Q  => "FCVT_DYN.D.Q"
    | FCVT_RNE_Q_D_64Q  => "FCVT_RNE.Q.D"
    | FCVT_RTZ_Q_D_64Q  => "FCVT_RTZ.Q.D"
    | FCVT_RDN_Q_D_64Q  => "FCVT_RDN.Q.D"
    | FCVT_RUP_Q_D_64Q  => "FCVT_RUP.Q.D"
    | FCVT_RMM_Q_D_64Q  => "FCVT_RMM.Q.D"
    | FCVT_DYN_Q_D_64Q  => "FCVT_DYN.Q.D"
    | FEQ_Q_64Q         => "FEQ.Q"
    | FLT_Q_64Q         => "FLT.Q"
    | FLE_Q_64Q         => "FLE.Q"
    | FCLASS_Q_64Q      => "FCLASS.Q"
    | FCVT_RNE_W_Q_64Q  => "FCVT_RNE.W.Q"
    | FCVT_RTZ_W_Q_64Q  => "FCVT_RTZ.W.Q"
    | FCVT_RDN_W_Q_64Q  => "FCVT_RDN.W.Q"
    | FCVT_RUP_W_Q_64Q  => "FCVT_RUP.W.Q"
    | FCVT_RMM_W_Q_64Q  => "FCVT_RMM.W.Q"
    | FCVT_DYN_W_Q_64Q  => "FCVT_DYN.W.Q"
    | FCVT_RNE_WU_Q_64Q => "FCVT_RNE.WU.Q"
    | FCVT_RTZ_WU_Q_64Q => "FCVT_RTZ.WU.Q"
    | FCVT_RDN_WU_Q_64Q => "FCVT_RDN.WU.Q"
    | FCVT_RUP_WU_Q_64Q => "FCVT_RUP.WU.Q"
    | FCVT_RMM_WU_Q_64Q => "FCVT_RMM.WU.Q"
    | FCVT_DYN_WU_Q_64Q => "FCVT_DYN.WU.Q"
    | FCVT_RNE_Q_W_64Q  => "FCVT_RNE.Q.W"
    | FCVT_RTZ_Q_W_64Q  => "FCVT_RTZ.Q.W"
    | FCVT_RDN_Q_W_64Q  => "FCVT_RDN.Q.W"
    | FCVT_RUP_Q_W_64Q  => "FCVT_RUP.Q.W"
    | FCVT_RMM_Q_W_64Q  => "FCVT_RMM.Q.W"
    | FCVT_DYN_Q_W_64Q  => "FCVT_DYN.Q.W"
    | FCVT_RNE_Q_WU_64Q => "FCVT_RNE.Q.WU"
    | FCVT_RTZ_Q_WU_64Q => "FCVT_RTZ.Q.WU"
    | FCVT_RDN_Q_WU_64Q => "FCVT_RDN.Q.WU"
    | FCVT_RUP_Q_WU_64Q => "FCVT_RUP.Q.WU"
    | FCVT_RMM_Q_WU_64Q => "FCVT_RMM.Q.WU"
    | FCVT_DYN_Q_WU_64Q => "FCVT_DYN.Q.WU"
    | FCVT_RNE_L_Q_64Q  => "FCVT_RNE.L.Q"
    | FCVT_RTZ_L_Q_64Q  => "FCVT_RTZ.L.Q"
    | FCVT_RDN_L_Q_64Q  => "FCVT_RDN.L.Q"
    | FCVT_RUP_L_Q_64Q  => "FCVT_RUP.L.Q"
    | FCVT_RMM_L_Q_64Q  => "FCVT_RMM.L.Q"
    | FCVT_DYN_L_Q_64Q  => "FCVT_DYN.L.Q"
    | FCVT_RNE_LU_Q_64Q => "FCVT_RNE.LU.Q"
    | FCVT_RTZ_LU_Q_64Q => "FCVT_RTZ.LU.Q"
    | FCVT_RDN_LU_Q_64Q => "FCVT_RDN.LU.Q"
    | FCVT_RUP_LU_Q_64Q => "FCVT_RUP.LU.Q"
    | FCVT_RMM_LU_Q_64Q => "FCVT_RMM.LU.Q"
    | FCVT_DYN_LU_Q_64Q => "FCVT_DYN.LU.Q"
    | FCVT_RNE_Q_L_64Q  => "FCVT_RNE.Q.L"
    | FCVT_RTZ_Q_L_64Q  => "FCVT_RTZ.Q.L"
    | FCVT_RDN_Q_L_64Q  => "FCVT_RDN.Q.L"
    | FCVT_RUP_Q_L_64Q  => "FCVT_RUP.Q.L"
    | FCVT_RMM_Q_L_64Q  => "FCVT_RMM.Q.L"
    | FCVT_DYN_Q_L_64Q  => "FCVT_DYN.Q.L"
    | FCVT_RNE_Q_LU_64Q => "FCVT_RNE.Q.LU"
    | FCVT_RTZ_Q_LU_64Q => "FCVT_RTZ.Q.LU"
    | FCVT_RDN_Q_LU_64Q => "FCVT_RDN.Q.LU"
    | FCVT_RUP_Q_LU_64Q => "FCVT_RUP.Q.LU"
    | FCVT_RMM_Q_LU_64Q => "FCVT_RMM.Q.LU"
    | FCVT_DYN_Q_LU_64Q => "FCVT_DYN.Q.LU"
    end
  end.
