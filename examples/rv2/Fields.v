(*! Definition of the instruction fields as defined in the RISC-V specification,
    as well as of the values required for identifying instructions (opcode,
    fct7, etc).
!*)

Require Import Koika.Frontend Koika.Std Koika.Parsing.

Require Import Instructions.

Inductive instruction_type :=
| RType | R4Type | IType | SType | BType | UType | JType.

Definition get_instruction_type (i : instruction) :=
  match i with
  | LUI_32I            => UType  | AUIPC_32I          => UType
  | JAL_32I            => JType  | JALR_32I           => IType
  | BEQ_32I            => BType  | BNE_32I            => BType
  | BLT_32I            => BType  | BGE_32I            => BType
  | BLTU_32I           => BType  | BGEU_32I           => BType
  | LB_32I             => IType  | LH_32I             => IType
  | LW_32I             => IType  | LBU_32I            => IType
  | LHU_32I            => IType  | SB_32I             => SType
  | SH_32I             => SType  | SW_32I             => SType
  | ADDI_32I           => IType  | SLTI_32I           => IType
  | SLTIU_32I          => IType  | XORI_32I           => IType
  | ORI_32I            => IType  | ANDI_32I           => IType
  | SLLI_32I           => IType  | SRLI_32I           => IType
  | SRAI_32I           => IType  | ADD_32I            => RType
  | SUB_32I            => RType  | SLL_32I            => RType
  | SLT_32I            => RType  | SLTU_32I           => RType
  | XOR_32I            => RType  | SRL_32I            => RType
  | SRA_32I            => RType  | OR_32I             => RType
  | AND_32I            => RType  | FENCE_32I          => IType
  | ECALL_32I          => IType  | EBREAK_32I         => IType
  | LUI_64I            => UType  | AUIPC_64I          => UType
  | JAL_64I            => JType  | JALR_64I           => IType
  | BEQ_64I            => BType  | BNE_64I            => BType
  | BLT_64I            => BType  | BGE_64I            => BType
  | BLTU_64I           => BType  | BGEU_64I           => BType
  | LB_64I             => IType  | LH_64I             => IType
  | LW_64I             => IType  | LBU_64I            => IType
  | LHU_64I            => IType  | SB_64I             => SType
  | SH_64I             => SType  | SW_64I             => SType
  | ADDI_64I           => IType  | SLTI_64I           => IType
  | SLTIU_64I          => IType  | XORI_64I           => IType
  | ORI_64I            => IType  | ANDI_64I           => IType
  | SLLI_64I           => IType  | SRLI_64I           => IType
  | SRAI_64I           => IType  | ADD_64I            => RType
  | SUB_64I            => RType  | SLL_64I            => RType
  | SLT_64I            => RType  | SLTU_64I           => RType
  | XOR_64I            => RType  | SRL_64I            => RType
  | SRA_64I            => RType  | OR_64I             => RType
  | AND_64I            => RType  | FENCE_64I          => IType
  | ECALL_64I          => IType  | EBREAK_64I         => IType
  | LWU_64I            => IType  | LD_64I             => IType
  | SD_64I             => SType  | ADDIW_64I          => IType
  | SLLIW_64I          => IType  | SRLIW_64I          => IType
  | SRAIW_64I          => IType  | ADDW_64I           => RType
  | SUBW_64I           => RType  | SLLW_64I           => RType
  | SRLW_64I           => RType  | SRAW_64I           => RType
  | FENCE_I_32Zifencei => IType  | FENCE_I_64Zifencei => IType
  | CSRRW_32Zicsr      => IType  | CSRRS_32Zicsr      => IType
  | CSRRC_32Zicsr      => IType  | CSRRWI_32Zicsr     => IType
  | CSRRSI_32Zicsr     => IType  | CSRRCI_32Zicsr     => IType
  | CSRRW_64Zicsr      => IType  | CSRRS_64Zicsr      => IType
  | CSRRC_64Zicsr      => IType  | CSRRWI_64Zicsr     => IType
  | CSRRSI_64Zicsr     => IType  | CSRRCI_64Zicsr     => IType
  | MUL_32M            => RType  | MULH_32M           => RType
  | MULHSU_32M         => RType  | MULHU_32M          => RType
  | DIV_32M            => RType  | DIVU_32M           => RType
  | REM_32M            => RType  | REMU_32M           => RType
  | MUL_64M            => RType  | MULH_64M           => RType
  | MULHSU_64M         => RType  | MULHU_64M          => RType
  | DIV_64M            => RType  | DIVU_64M           => RType
  | REM_64M            => RType  | REMU_64M           => RType
  | MULW_64M           => RType  | DIVW_64M           => RType
  | DIVUW_64M          => RType  | REMW_64M           => RType
  | REMUW_64M          => RType  | LR_W_00_32A        => RType
  | LR_W_01_32A        => RType  | LR_W_10_32A        => RType
  | LR_W_11_32A        => RType  | SC_W_00_32A        => RType
  | SC_W_01_32A        => RType  | SC_W_10_32A        => RType
  | SC_W_11_32A        => RType  | AMOSWAP_W_00_32A   => RType
  | AMOSWAP_W_01_32A   => RType  | AMOSWAP_W_10_32A   => RType
  | AMOSWAP_W_11_32A   => RType  | AMOADD_W_00_32A    => RType
  | AMOADD_W_01_32A    => RType  | AMOADD_W_10_32A    => RType
  | AMOADD_W_11_32A    => RType  | AMOXOR_W_00_32A    => RType
  | AMOXOR_W_01_32A    => RType  | AMOXOR_W_10_32A    => RType
  | AMOXOR_W_11_32A    => RType  | AMOAND_W_00_32A    => RType
  | AMOAND_W_01_32A    => RType  | AMOAND_W_10_32A    => RType
  | AMOAND_W_11_32A    => RType  | AMOOR_W_00_32A     => RType
  | AMOOR_W_01_32A     => RType  | AMOOR_W_10_32A     => RType
  | AMOOR_W_11_32A     => RType  | AMOMIN_W_00_32A    => RType
  | AMOMIN_W_01_32A    => RType  | AMOMIN_W_10_32A    => RType
  | AMOMIN_W_11_32A    => RType  | AMOMAX_W_00_32A    => RType
  | AMOMAX_W_01_32A    => RType  | AMOMAX_W_10_32A    => RType
  | AMOMAX_W_11_32A    => RType  | AMOMINU_W_00_32A   => RType
  | AMOMINU_W_01_32A   => RType  | AMOMINU_W_10_32A   => RType
  | AMOMINU_W_11_32A   => RType  | AMOMAXU_W_00_32A   => RType
  | AMOMAXU_W_01_32A   => RType  | AMOMAXU_W_10_32A   => RType
  | AMOMAXU_W_11_32A   => RType  | LR_W_00_64A        => RType
  | LR_W_01_64A        => RType  | LR_W_10_64A        => RType
  | LR_W_11_64A        => RType  | SC_W_00_64A        => RType
  | SC_W_01_64A        => RType  | SC_W_10_64A        => RType
  | SC_W_11_64A        => RType  | AMOSWAP_W_00_64A   => RType
  | AMOSWAP_W_01_64A   => RType  | AMOSWAP_W_10_64A   => RType
  | AMOSWAP_W_11_64A   => RType  | AMOADD_W_00_64A    => RType
  | AMOADD_W_01_64A    => RType  | AMOADD_W_10_64A    => RType
  | AMOADD_W_11_64A    => RType  | AMOXOR_W_00_64A    => RType
  | AMOXOR_W_01_64A    => RType  | AMOXOR_W_10_64A    => RType
  | AMOXOR_W_11_64A    => RType  | AMOAND_W_00_64A    => RType
  | AMOAND_W_01_64A    => RType  | AMOAND_W_10_64A    => RType
  | AMOAND_W_11_64A    => RType  | AMOOR_W_00_64A     => RType
  | AMOOR_W_01_64A     => RType  | AMOOR_W_10_64A     => RType
  | AMOOR_W_11_64A     => RType  | AMOMIN_W_00_64A    => RType
  | AMOMIN_W_01_64A    => RType  | AMOMIN_W_10_64A    => RType
  | AMOMIN_W_11_64A    => RType  | AMOMAX_W_00_64A    => RType
  | AMOMAX_W_01_64A    => RType  | AMOMAX_W_10_64A    => RType
  | AMOMAX_W_11_64A    => RType  | AMOMINU_W_00_64A   => RType
  | AMOMINU_W_01_64A   => RType  | AMOMINU_W_10_64A   => RType
  | AMOMINU_W_11_64A   => RType  | AMOMAXU_W_00_64A   => RType
  | AMOMAXU_W_01_64A   => RType  | AMOMAXU_W_10_64A   => RType
  | AMOMAXU_W_11_64A   => RType  | LR_D_00_64A        => RType
  | LR_D_01_64A        => RType  | LR_D_10_64A        => RType
  | LR_D_11_64A        => RType  | SC_D_00_64A        => RType
  | SC_D_01_64A        => RType  | SC_D_10_64A        => RType
  | SC_D_11_64A        => RType  | AMOSWAP_D_00_64A   => RType
  | AMOSWAP_D_01_64A   => RType  | AMOSWAP_D_10_64A   => RType
  | AMOSWAP_D_11_64A   => RType  | AMOADD_D_00_64A    => RType
  | AMOADD_D_01_64A    => RType  | AMOADD_D_10_64A    => RType
  | AMOADD_D_11_64A    => RType  | AMOXOR_D_00_64A    => RType
  | AMOXOR_D_01_64A    => RType  | AMOXOR_D_10_64A    => RType
  | AMOXOR_D_11_64A    => RType  | AMOAND_D_00_64A    => RType
  | AMOAND_D_01_64A    => RType  | AMOAND_D_10_64A    => RType
  | AMOAND_D_11_64A    => RType  | AMOOR_D_00_64A     => RType
  | AMOOR_D_01_64A     => RType  | AMOOR_D_10_64A     => RType
  | AMOOR_D_11_64A     => RType  | AMOMIN_D_00_64A    => RType
  | AMOMIN_D_01_64A    => RType  | AMOMIN_D_10_64A    => RType
  | AMOMIN_D_11_64A    => RType  | AMOMAX_D_00_64A    => RType
  | AMOMAX_D_01_64A    => RType  | AMOMAX_D_10_64A    => RType
  | AMOMAX_D_11_64A    => RType  | AMOMINU_D_00_64A   => RType
  | AMOMINU_D_01_64A   => RType  | AMOMINU_D_10_64A   => RType
  | AMOMINU_D_11_64A   => RType  | AMOMAXU_D_00_64A   => RType
  | AMOMAXU_D_01_64A   => RType  | AMOMAXU_D_10_64A   => RType
  | AMOMAXU_D_11_64A   => RType  | FLW_32F            => IType
  | FSW_32F            => SType  | FMADD_RNE_S_32F    => R4Type
  | FMADD_RTZ_S_32F    => R4Type | FMADD_RDN_S_32F    => R4Type
  | FMADD_RUP_S_32F    => R4Type | FMADD_RMM_S_32F    => R4Type
  | FMADD_DYN_S_32F    => R4Type | FMSUB_RNE_S_32F    => R4Type
  | FMSUB_RTZ_S_32F    => R4Type | FMSUB_RDN_S_32F    => R4Type
  | FMSUB_RUP_S_32F    => R4Type | FMSUB_RMM_S_32F    => R4Type
  | FMSUB_DYN_S_32F    => R4Type | FNMSUB_RNE_S_32F   => R4Type
  | FNMSUB_RTZ_S_32F   => R4Type | FNMSUB_RDN_S_32F   => R4Type
  | FNMSUB_RUP_S_32F   => R4Type | FNMSUB_RMM_S_32F   => R4Type
  | FNMSUB_DYN_S_32F   => R4Type | FNMADD_RNE_S_32F   => R4Type
  | FNMADD_RTZ_S_32F   => R4Type | FNMADD_RDN_S_32F   => R4Type
  | FNMADD_RUP_S_32F   => R4Type | FNMADD_RMM_S_32F   => R4Type
  | FNMADD_DYN_S_32F   => R4Type | FADD_RNE_S_32F     => RType
  | FADD_RTZ_S_32F     => RType  | FADD_RDN_S_32F     => RType
  | FADD_RUP_S_32F     => RType  | FADD_RMM_S_32F     => RType
  | FADD_DYN_S_32F     => RType  | FSUB_RNE_S_32F     => RType
  | FSUB_RTZ_S_32F     => RType  | FSUB_RDN_S_32F     => RType
  | FSUB_RUP_S_32F     => RType  | FSUB_RMM_S_32F     => RType
  | FSUB_DYN_S_32F     => RType  | FMUL_RNE_S_32F     => RType
  | FMUL_RTZ_S_32F     => RType  | FMUL_RDN_S_32F     => RType
  | FMUL_RUP_S_32F     => RType  | FMUL_RMM_S_32F     => RType
  | FMUL_DYN_S_32F     => RType  | FDIV_RNE_S_32F     => RType
  | FDIV_RTZ_S_32F     => RType  | FDIV_RDN_S_32F     => RType
  | FDIV_RUP_S_32F     => RType  | FDIV_RMM_S_32F     => RType
  | FDIV_DYN_S_32F     => RType  | FSQRT_RNE_S_32F    => RType
  | FSQRT_RTZ_S_32F    => RType  | FSQRT_RDN_S_32F    => RType
  | FSQRT_RUP_S_32F    => RType  | FSQRT_RMM_S_32F    => RType
  | FSQRT_DYN_S_32F    => RType  | FSGNJ_S_32F        => RType
  | FSGNJN_S_32F       => RType  | FSGNJX_S_32F       => RType
  | FMIN_S_32F         => RType  | FMAX_S_32F         => RType
  | FCVT_RNE_W_S_32F   => RType  | FCVT_RTZ_W_S_32F   => RType
  | FCVT_RDN_W_S_32F   => RType  | FCVT_RUP_W_S_32F   => RType
  | FCVT_RMM_W_S_32F   => RType  | FCVT_DYN_W_S_32F   => RType
  | FCVT_RNE_WU_S_32F  => RType  | FCVT_RTZ_WU_S_32F  => RType
  | FCVT_RDN_WU_S_32F  => RType  | FCVT_RUP_WU_S_32F  => RType
  | FCVT_RMM_WU_S_32F  => RType  | FCVT_DYN_WU_S_32F  => RType
  | FMV_X_W_32F        => RType  | FEQ_S_32F          => RType
  | FLT_S_32F          => RType  | FLE_S_32F          => RType
  | FCLASS_S_32F       => RType  | FCVT_RNE_S_W_32F   => RType
  | FCVT_RTZ_S_W_32F   => RType  | FCVT_RDN_S_W_32F   => RType
  | FCVT_RUP_S_W_32F   => RType  | FCVT_RMM_S_W_32F   => RType
  | FCVT_DYN_S_W_32F   => RType  | FCVT_RNE_S_WU_32F  => RType
  | FCVT_RTZ_S_WU_32F  => RType  | FCVT_RDN_S_WU_32F  => RType
  | FCVT_RUP_S_WU_32F  => RType  | FCVT_RMM_S_WU_32F  => RType
  | FCVT_DYN_S_WU_32F  => RType  | FMV_W_X_32F        => RType
  | FLW_64F            => IType  | FSW_64F            => SType
  | FMADD_RNE_S_64F    => R4Type | FMADD_RTZ_S_64F    => R4Type
  | FMADD_RDN_S_64F    => R4Type | FMADD_RUP_S_64F    => R4Type
  | FMADD_RMM_S_64F    => R4Type | FMADD_DYN_S_64F    => R4Type
  | FMSUB_RNE_S_64F    => R4Type | FMSUB_RTZ_S_64F    => R4Type
  | FMSUB_RDN_S_64F    => R4Type | FMSUB_RUP_S_64F    => R4Type
  | FMSUB_RMM_S_64F    => R4Type | FMSUB_DYN_S_64F    => R4Type
  | FNMSUB_RNE_S_64F   => R4Type | FNMSUB_RTZ_S_64F   => R4Type
  | FNMSUB_RDN_S_64F   => R4Type | FNMSUB_RUP_S_64F   => R4Type
  | FNMSUB_RMM_S_64F   => R4Type | FNMSUB_DYN_S_64F   => R4Type
  | FNMADD_RNE_S_64F   => R4Type | FNMADD_RTZ_S_64F   => R4Type
  | FNMADD_RDN_S_64F   => R4Type | FNMADD_RUP_S_64F   => R4Type
  | FNMADD_RMM_S_64F   => R4Type | FNMADD_DYN_S_64F   => R4Type
  | FADD_RNE_S_64F     => RType  | FADD_RTZ_S_64F     => RType
  | FADD_RDN_S_64F     => RType  | FADD_RUP_S_64F     => RType
  | FADD_RMM_S_64F     => RType  | FADD_DYN_S_64F     => RType
  | FSUB_RNE_S_64F     => RType  | FSUB_RTZ_S_64F     => RType
  | FSUB_RDN_S_64F     => RType  | FSUB_RUP_S_64F     => RType
  | FSUB_RMM_S_64F     => RType  | FSUB_DYN_S_64F     => RType
  | FMUL_RNE_S_64F     => RType  | FMUL_RTZ_S_64F     => RType
  | FMUL_RDN_S_64F     => RType  | FMUL_RUP_S_64F     => RType
  | FMUL_RMM_S_64F     => RType  | FMUL_DYN_S_64F     => RType
  | FDIV_RNE_S_64F     => RType  | FDIV_RTZ_S_64F     => RType
  | FDIV_RDN_S_64F     => RType  | FDIV_RUP_S_64F     => RType
  | FDIV_RMM_S_64F     => RType  | FDIV_DYN_S_64F     => RType
  | FSQRT_RNE_S_64F    => RType  | FSQRT_RTZ_S_64F    => RType
  | FSQRT_RDN_S_64F    => RType  | FSQRT_RUP_S_64F    => RType
  | FSQRT_RMM_S_64F    => RType  | FSQRT_DYN_S_64F    => RType
  | FSGNJ_S_64F        => RType  | FSGNJN_S_64F       => RType
  | FSGNJX_S_64F       => RType  | FMIN_S_64F         => RType
  | FMAX_S_64F         => RType  | FCVT_RNE_W_S_64F   => RType
  | FCVT_RTZ_W_S_64F   => RType  | FCVT_RDN_W_S_64F   => RType
  | FCVT_RUP_W_S_64F   => RType  | FCVT_RMM_W_S_64F   => RType
  | FCVT_DYN_W_S_64F   => RType  | FCVT_RNE_WU_S_64F  => RType
  | FCVT_RTZ_WU_S_64F  => RType  | FCVT_RDN_WU_S_64F  => RType
  | FCVT_RUP_WU_S_64F  => RType  | FCVT_RMM_WU_S_64F  => RType
  | FCVT_DYN_WU_S_64F  => RType  | FMV_X_W_64F        => RType
  | FEQ_S_64F          => RType  | FLT_S_64F          => RType
  | FLE_S_64F          => RType  | FCLASS_S_64F       => RType
  | FCVT_RNE_S_W_64F   => RType  | FCVT_RTZ_S_W_64F   => RType
  | FCVT_RDN_S_W_64F   => RType  | FCVT_RUP_S_W_64F   => RType
  | FCVT_RMM_S_W_64F   => RType  | FCVT_DYN_S_W_64F   => RType
  | FCVT_RNE_S_WU_64F  => RType  | FCVT_RTZ_S_WU_64F  => RType
  | FCVT_RDN_S_WU_64F  => RType  | FCVT_RUP_S_WU_64F  => RType
  | FCVT_RMM_S_WU_64F  => RType  | FCVT_DYN_S_WU_64F  => RType
  | FMV_W_X_64F        => RType  | FCVT_RNE_L_S_64F   => RType
  | FCVT_RTZ_L_S_64F   => RType  | FCVT_RDN_L_S_64F   => RType
  | FCVT_RUP_L_S_64F   => RType  | FCVT_RMM_L_S_64F   => RType
  | FCVT_DYN_L_S_64F   => RType  | FCVT_RNE_LU_S_64F  => RType
  | FCVT_RTZ_LU_S_64F  => RType  | FCVT_RDN_LU_S_64F  => RType
  | FCVT_RUP_LU_S_64F  => RType  | FCVT_RMM_LU_S_64F  => RType
  | FCVT_DYN_LU_S_64F  => RType  | FCVT_RNE_S_L_64F   => RType
  | FCVT_RTZ_S_L_64F   => RType  | FCVT_RDN_S_L_64F   => RType
  | FCVT_RUP_S_L_64F   => RType  | FCVT_RMM_S_L_64F   => RType
  | FCVT_DYN_S_L_64F   => RType  | FCVT_RNE_S_LU_64F  => RType
  | FCVT_RTZ_S_LU_64F  => RType  | FCVT_RDN_S_LU_64F  => RType
  | FCVT_RUP_S_LU_64F  => RType  | FCVT_RMM_S_LU_64F  => RType
  | FCVT_DYN_S_LU_64F  => RType  | FLD_32D            => IType
  | FSD_32D            => SType  | FMADD_RNE_D_32D    => R4Type
  | FMADD_RTZ_D_32D    => R4Type | FMADD_RDN_D_32D    => R4Type
  | FMADD_RUP_D_32D    => R4Type | FMADD_RMM_D_32D    => R4Type
  | FMADD_DYN_D_32D    => R4Type | FMSUB_RNE_D_32D    => R4Type
  | FMSUB_RTZ_D_32D    => R4Type | FMSUB_RDN_D_32D    => R4Type
  | FMSUB_RUP_D_32D    => R4Type | FMSUB_RMM_D_32D    => R4Type
  | FMSUB_DYN_D_32D    => R4Type | FNMSUB_RNE_D_32D   => R4Type
  | FNMSUB_RTZ_D_32D   => R4Type | FNMSUB_RDN_D_32D   => R4Type
  | FNMSUB_RUP_D_32D   => R4Type | FNMSUB_RMM_D_32D   => R4Type
  | FNMSUB_DYN_D_32D   => R4Type | FNMADD_RNE_D_32D   => R4Type
  | FNMADD_RTZ_D_32D   => R4Type | FNMADD_RDN_D_32D   => R4Type
  | FNMADD_RUP_D_32D   => R4Type | FNMADD_RMM_D_32D   => R4Type
  | FNMADD_DYN_D_32D   => R4Type | FADD_RNE_D_32D     => RType
  | FADD_RTZ_D_32D     => RType  | FADD_RDN_D_32D     => RType
  | FADD_RUP_D_32D     => RType  | FADD_RMM_D_32D     => RType
  | FADD_DYN_D_32D     => RType  | FSUB_RNE_D_32D     => RType
  | FSUB_RTZ_D_32D     => RType  | FSUB_RDN_D_32D     => RType
  | FSUB_RUP_D_32D     => RType  | FSUB_RMM_D_32D     => RType
  | FSUB_DYN_D_32D     => RType  | FMUL_RNE_D_32D     => RType
  | FMUL_RTZ_D_32D     => RType  | FMUL_RDN_D_32D     => RType
  | FMUL_RUP_D_32D     => RType  | FMUL_RMM_D_32D     => RType
  | FMUL_DYN_D_32D     => RType  | FDIV_RNE_D_32D     => RType
  | FDIV_RTZ_D_32D     => RType  | FDIV_RDN_D_32D     => RType
  | FDIV_RUP_D_32D     => RType  | FDIV_RMM_D_32D     => RType
  | FDIV_DYN_D_32D     => RType  | FSQRT_RNE_D_32D    => RType
  | FSQRT_RTZ_D_32D    => RType  | FSQRT_RDN_D_32D    => RType
  | FSQRT_RUP_D_32D    => RType  | FSQRT_RMM_D_32D    => RType
  | FSQRT_DYN_D_32D    => RType  | FSGNJ_D_32D        => RType
  | FSGNJN_D_32D       => RType  | FSGNJX_D_32D       => RType
  | FMIN_D_32D         => RType  | FMAX_D_32D         => RType
  | FCVT_RNE_S_D_32D   => RType  | FCVT_RTZ_S_D_32D   => RType
  | FCVT_RDN_S_D_32D   => RType  | FCVT_RUP_S_D_32D   => RType
  | FCVT_RMM_S_D_32D   => RType  | FCVT_DYN_S_D_32D   => RType
  | FCVT_RNE_D_S_32D   => RType  | FCVT_RTZ_D_S_32D   => RType
  | FCVT_RDN_D_S_32D   => RType  | FCVT_RUP_D_S_32D   => RType
  | FCVT_RMM_D_S_32D   => RType  | FCVT_DYN_D_S_32D   => RType
  | FEQ_D_32D          => RType  | FLT_D_32D          => RType
  | FLE_D_32D          => RType  | FCLASS_D_32D       => RType
  | FCVT_RNE_W_D_32D   => RType  | FCVT_RTZ_W_D_32D   => RType
  | FCVT_RDN_W_D_32D   => RType  | FCVT_RUP_W_D_32D   => RType
  | FCVT_RMM_W_D_32D   => RType  | FCVT_DYN_W_D_32D   => RType
  | FCVT_RNE_WU_D_32D  => RType  | FCVT_RTZ_WU_D_32D  => RType
  | FCVT_RDN_WU_D_32D  => RType  | FCVT_RUP_WU_D_32D  => RType
  | FCVT_RMM_WU_D_32D  => RType  | FCVT_DYN_WU_D_32D  => RType
  | FCVT_RNE_D_W_32D   => RType  | FCVT_RTZ_D_W_32D   => RType
  | FCVT_RDN_D_W_32D   => RType  | FCVT_RUP_D_W_32D   => RType
  | FCVT_RMM_D_W_32D   => RType  | FCVT_DYN_D_W_32D   => RType
  | FCVT_RNE_D_WU_32D  => RType  | FCVT_RTZ_D_WU_32D  => RType
  | FCVT_RDN_D_WU_32D  => RType  | FCVT_RUP_D_WU_32D  => RType
  | FCVT_RMM_D_WU_32D  => RType  | FCVT_DYN_D_WU_32D  => RType
  | FLD_64D            => IType  | FSD_64D            => SType
  | FMADD_RNE_D_64D    => R4Type | FMADD_RTZ_D_64D    => R4Type
  | FMADD_RDN_D_64D    => R4Type | FMADD_RUP_D_64D    => R4Type
  | FMADD_RMM_D_64D    => R4Type | FMADD_DYN_D_64D    => R4Type
  | FMSUB_RNE_D_64D    => R4Type | FMSUB_RTZ_D_64D    => R4Type
  | FMSUB_RDN_D_64D    => R4Type | FMSUB_RUP_D_64D    => R4Type
  | FMSUB_RMM_D_64D    => R4Type | FMSUB_DYN_D_64D    => R4Type
  | FNMSUB_RNE_D_64D   => R4Type | FNMSUB_RTZ_D_64D   => R4Type
  | FNMSUB_RDN_D_64D   => R4Type | FNMSUB_RUP_D_64D   => R4Type
  | FNMSUB_RMM_D_64D   => R4Type | FNMSUB_DYN_D_64D   => R4Type
  | FNMADD_RNE_D_64D   => R4Type | FNMADD_RTZ_D_64D   => R4Type
  | FNMADD_RDN_D_64D   => R4Type | FNMADD_RUP_D_64D   => R4Type
  | FNMADD_RMM_D_64D   => R4Type | FNMADD_DYN_D_64D   => R4Type
  | FADD_RNE_D_64D     => RType  | FADD_RTZ_D_64D     => RType
  | FADD_RDN_D_64D     => RType  | FADD_RUP_D_64D     => RType
  | FADD_RMM_D_64D     => RType  | FADD_DYN_D_64D     => RType
  | FSUB_RNE_D_64D     => RType  | FSUB_RTZ_D_64D     => RType
  | FSUB_RDN_D_64D     => RType  | FSUB_RUP_D_64D     => RType
  | FSUB_RMM_D_64D     => RType  | FSUB_DYN_D_64D     => RType
  | FMUL_RNE_D_64D     => RType  | FMUL_RTZ_D_64D     => RType
  | FMUL_RDN_D_64D     => RType  | FMUL_RUP_D_64D     => RType
  | FMUL_RMM_D_64D     => RType  | FMUL_DYN_D_64D     => RType
  | FDIV_RNE_D_64D     => RType  | FDIV_RTZ_D_64D     => RType
  | FDIV_RDN_D_64D     => RType  | FDIV_RUP_D_64D     => RType
  | FDIV_RMM_D_64D     => RType  | FDIV_DYN_D_64D     => RType
  | FSQRT_RNE_D_64D    => RType  | FSQRT_RTZ_D_64D    => RType
  | FSQRT_RDN_D_64D    => RType  | FSQRT_RUP_D_64D    => RType
  | FSQRT_RMM_D_64D    => RType  | FSQRT_DYN_D_64D    => RType
  | FSGNJ_D_64D        => RType  | FSGNJN_D_64D       => RType
  | FSGNJX_D_64D       => RType  | FMIN_D_64D         => RType
  | FMAX_D_64D         => RType  | FCVT_RNE_S_D_64D   => RType
  | FCVT_RTZ_S_D_64D   => RType  | FCVT_RDN_S_D_64D   => RType
  | FCVT_RUP_S_D_64D   => RType  | FCVT_RMM_S_D_64D   => RType
  | FCVT_DYN_S_D_64D   => RType  | FCVT_RNE_D_S_64D   => RType
  | FCVT_RTZ_D_S_64D   => RType  | FCVT_RDN_D_S_64D   => RType
  | FCVT_RUP_D_S_64D   => RType  | FCVT_RMM_D_S_64D   => RType
  | FCVT_DYN_D_S_64D   => RType  | FEQ_D_64D          => RType
  | FLT_D_64D          => RType  | FLE_D_64D          => RType
  | FCLASS_D_64D       => RType  | FCVT_RNE_W_D_64D   => RType
  | FCVT_RTZ_W_D_64D   => RType  | FCVT_RDN_W_D_64D   => RType
  | FCVT_RUP_W_D_64D   => RType  | FCVT_RMM_W_D_64D   => RType
  | FCVT_DYN_W_D_64D   => RType  | FCVT_RNE_WU_D_64D  => RType
  | FCVT_RTZ_WU_D_64D  => RType  | FCVT_RDN_WU_D_64D  => RType
  | FCVT_RUP_WU_D_64D  => RType  | FCVT_RMM_WU_D_64D  => RType
  | FCVT_DYN_WU_D_64D  => RType  | FCVT_RNE_D_W_64D   => RType
  | FCVT_RTZ_D_W_64D   => RType  | FCVT_RDN_D_W_64D   => RType
  | FCVT_RUP_D_W_64D   => RType  | FCVT_RMM_D_W_64D   => RType
  | FCVT_DYN_D_W_64D   => RType  | FCVT_RNE_D_WU_64D  => RType
  | FCVT_RTZ_D_WU_64D  => RType  | FCVT_RDN_D_WU_64D  => RType
  | FCVT_RUP_D_WU_64D  => RType  | FCVT_RMM_D_WU_64D  => RType
  | FCVT_DYN_D_WU_64D  => RType  | FCVT_RNE_L_D_64D   => RType
  | FCVT_RTZ_L_D_64D   => RType  | FCVT_RDN_L_D_64D   => RType
  | FCVT_RUP_L_D_64D   => RType  | FCVT_RMM_L_D_64D   => RType
  | FCVT_DYN_L_D_64D   => RType  | FCVT_RNE_LU_D_64D  => RType
  | FCVT_RTZ_LU_D_64D  => RType  | FCVT_RDN_LU_D_64D  => RType
  | FCVT_RUP_LU_D_64D  => RType  | FCVT_RMM_LU_D_64D  => RType
  | FCVT_DYN_LU_D_64D  => RType  | FMV_X_D_64D        => RType
  | FCVT_RNE_D_L_64D   => RType  | FCVT_RTZ_D_L_64D   => RType
  | FCVT_RDN_D_L_64D   => RType  | FCVT_RUP_D_L_64D   => RType
  | FCVT_RMM_D_L_64D   => RType  | FCVT_DYN_D_L_64D   => RType
  | FCVT_RNE_D_LU_64D  => RType  | FCVT_RTZ_D_LU_64D  => RType
  | FCVT_RDN_D_LU_64D  => RType  | FCVT_RUP_D_LU_64D  => RType
  | FCVT_RMM_D_LU_64D  => RType  | FCVT_DYN_D_LU_64D  => RType
  | FMV_D_X_64D        => RType  | FLQ_32Q            => IType
  | FSQ_32Q            => SType  | FMADD_RNE_Q_32Q    => R4Type
  | FMADD_RTZ_Q_32Q    => R4Type | FMADD_RDN_Q_32Q    => R4Type
  | FMADD_RUP_Q_32Q    => R4Type | FMADD_RMM_Q_32Q    => R4Type
  | FMADD_DYN_Q_32Q    => R4Type | FMSUB_RNE_Q_32Q    => R4Type
  | FMSUB_RTZ_Q_32Q    => R4Type | FMSUB_RDN_Q_32Q    => R4Type
  | FMSUB_RUP_Q_32Q    => R4Type | FMSUB_RMM_Q_32Q    => R4Type
  | FMSUB_DYN_Q_32Q    => R4Type | FNMSUB_RNE_Q_32Q   => R4Type
  | FNMSUB_RTZ_Q_32Q   => R4Type | FNMSUB_RDN_Q_32Q   => R4Type
  | FNMSUB_RUP_Q_32Q   => R4Type | FNMSUB_RMM_Q_32Q   => R4Type
  | FNMSUB_DYN_Q_32Q   => R4Type | FNMADD_RNE_Q_32Q   => R4Type
  | FNMADD_RTZ_Q_32Q   => R4Type | FNMADD_RDN_Q_32Q   => R4Type
  | FNMADD_RUP_Q_32Q   => R4Type | FNMADD_RMM_Q_32Q   => R4Type
  | FNMADD_DYN_Q_32Q   => R4Type | FADD_RNE_Q_32Q     => RType
  | FADD_RTZ_Q_32Q     => RType  | FADD_RDN_Q_32Q     => RType
  | FADD_RUP_Q_32Q     => RType  | FADD_RMM_Q_32Q     => RType
  | FADD_DYN_Q_32Q     => RType  | FSUB_RNE_Q_32Q     => RType
  | FSUB_RTZ_Q_32Q     => RType  | FSUB_RDN_Q_32Q     => RType
  | FSUB_RUP_Q_32Q     => RType  | FSUB_RMM_Q_32Q     => RType
  | FSUB_DYN_Q_32Q     => RType  | FMUL_RNE_Q_32Q     => RType
  | FMUL_RTZ_Q_32Q     => RType  | FMUL_RDN_Q_32Q     => RType
  | FMUL_RUP_Q_32Q     => RType  | FMUL_RMM_Q_32Q     => RType
  | FMUL_DYN_Q_32Q     => RType  | FDIV_RNE_Q_32Q     => RType
  | FDIV_RTZ_Q_32Q     => RType  | FDIV_RDN_Q_32Q     => RType
  | FDIV_RUP_Q_32Q     => RType  | FDIV_RMM_Q_32Q     => RType
  | FDIV_DYN_Q_32Q     => RType  | FSQRT_RNE_Q_32Q    => RType
  | FSQRT_RTZ_Q_32Q    => RType  | FSQRT_RDN_Q_32Q    => RType
  | FSQRT_RUP_Q_32Q    => RType  | FSQRT_RMM_Q_32Q    => RType
  | FSQRT_DYN_Q_32Q    => RType  | FSGNJ_Q_32Q        => RType
  | FSGNJN_Q_32Q       => RType  | FSGNJX_Q_32Q       => RType
  | FMIN_Q_32Q         => RType  | FMAX_Q_32Q         => RType
  | FCVT_RNE_S_Q_32Q   => RType  | FCVT_RTZ_S_Q_32Q   => RType
  | FCVT_RDN_S_Q_32Q   => RType  | FCVT_RUP_S_Q_32Q   => RType
  | FCVT_RMM_S_Q_32Q   => RType  | FCVT_DYN_S_Q_32Q   => RType
  | FCVT_RNE_Q_S_32Q   => RType  | FCVT_RTZ_Q_S_32Q   => RType
  | FCVT_RDN_Q_S_32Q   => RType  | FCVT_RUP_Q_S_32Q   => RType
  | FCVT_RMM_Q_S_32Q   => RType  | FCVT_DYN_Q_S_32Q   => RType
  | FCVT_RNE_D_Q_32Q   => RType  | FCVT_RTZ_D_Q_32Q   => RType
  | FCVT_RDN_D_Q_32Q   => RType  | FCVT_RUP_D_Q_32Q   => RType
  | FCVT_RMM_D_Q_32Q   => RType  | FCVT_DYN_D_Q_32Q   => RType
  | FCVT_RNE_Q_D_32Q   => RType  | FCVT_RTZ_Q_D_32Q   => RType
  | FCVT_RDN_Q_D_32Q   => RType  | FCVT_RUP_Q_D_32Q   => RType
  | FCVT_RMM_Q_D_32Q   => RType  | FCVT_DYN_Q_D_32Q   => RType
  | FEQ_Q_32Q          => RType  | FLT_Q_32Q          => RType
  | FLE_Q_32Q          => RType  | FCLASS_Q_32Q       => RType
  | FCVT_RNE_W_Q_32Q   => RType  | FCVT_RTZ_W_Q_32Q   => RType
  | FCVT_RDN_W_Q_32Q   => RType  | FCVT_RUP_W_Q_32Q   => RType
  | FCVT_RMM_W_Q_32Q   => RType  | FCVT_DYN_W_Q_32Q   => RType
  | FCVT_RNE_WU_Q_32Q  => RType  | FCVT_RTZ_WU_Q_32Q  => RType
  | FCVT_RDN_WU_Q_32Q  => RType  | FCVT_RUP_WU_Q_32Q  => RType
  | FCVT_RMM_WU_Q_32Q  => RType  | FCVT_DYN_WU_Q_32Q  => RType
  | FCVT_RNE_Q_W_32Q   => RType  | FCVT_RTZ_Q_W_32Q   => RType
  | FCVT_RDN_Q_W_32Q   => RType  | FCVT_RUP_Q_W_32Q   => RType
  | FCVT_RMM_Q_W_32Q   => RType  | FCVT_DYN_Q_W_32Q   => RType
  | FCVT_RNE_Q_WU_32Q  => RType  | FCVT_RTZ_Q_WU_32Q  => RType
  | FCVT_RDN_Q_WU_32Q  => RType  | FCVT_RUP_Q_WU_32Q  => RType
  | FCVT_RMM_Q_WU_32Q  => RType  | FCVT_DYN_Q_WU_32Q  => RType
  | FLQ_64Q            => IType  | FSQ_64Q            => SType
  | FMADD_RNE_Q_64Q    => R4Type | FMADD_RTZ_Q_64Q    => R4Type
  | FMADD_RDN_Q_64Q    => R4Type | FMADD_RUP_Q_64Q    => R4Type
  | FMADD_RMM_Q_64Q    => R4Type | FMADD_DYN_Q_64Q    => R4Type
  | FMSUB_RNE_Q_64Q    => R4Type | FMSUB_RTZ_Q_64Q    => R4Type
  | FMSUB_RDN_Q_64Q    => R4Type | FMSUB_RUP_Q_64Q    => R4Type
  | FMSUB_RMM_Q_64Q    => R4Type | FMSUB_DYN_Q_64Q    => R4Type
  | FNMSUB_RNE_Q_64Q   => R4Type | FNMSUB_RTZ_Q_64Q   => R4Type
  | FNMSUB_RDN_Q_64Q   => R4Type | FNMSUB_RUP_Q_64Q   => R4Type
  | FNMSUB_RMM_Q_64Q   => R4Type | FNMSUB_DYN_Q_64Q   => R4Type
  | FNMADD_RNE_Q_64Q   => R4Type | FNMADD_RTZ_Q_64Q   => R4Type
  | FNMADD_RDN_Q_64Q   => R4Type | FNMADD_RUP_Q_64Q   => R4Type
  | FNMADD_RMM_Q_64Q   => R4Type | FNMADD_DYN_Q_64Q   => R4Type
  | FADD_RNE_Q_64Q     => RType  | FADD_RTZ_Q_64Q     => RType
  | FADD_RDN_Q_64Q     => RType  | FADD_RUP_Q_64Q     => RType
  | FADD_RMM_Q_64Q     => RType  | FADD_DYN_Q_64Q     => RType
  | FSUB_RNE_Q_64Q     => RType  | FSUB_RTZ_Q_64Q     => RType
  | FSUB_RDN_Q_64Q     => RType  | FSUB_RUP_Q_64Q     => RType
  | FSUB_RMM_Q_64Q     => RType  | FSUB_DYN_Q_64Q     => RType
  | FMUL_RNE_Q_64Q     => RType  | FMUL_RTZ_Q_64Q     => RType
  | FMUL_RDN_Q_64Q     => RType  | FMUL_RUP_Q_64Q     => RType
  | FMUL_RMM_Q_64Q     => RType  | FMUL_DYN_Q_64Q     => RType
  | FDIV_RNE_Q_64Q     => RType  | FDIV_RTZ_Q_64Q     => RType
  | FDIV_RDN_Q_64Q     => RType  | FDIV_RUP_Q_64Q     => RType
  | FDIV_RMM_Q_64Q     => RType  | FDIV_DYN_Q_64Q     => RType
  | FSQRT_RNE_Q_64Q    => RType  | FSQRT_RTZ_Q_64Q    => RType
  | FSQRT_RDN_Q_64Q    => RType  | FSQRT_RUP_Q_64Q    => RType
  | FSQRT_RMM_Q_64Q    => RType  | FSQRT_DYN_Q_64Q    => RType
  | FSGNJ_Q_64Q        => RType  | FSGNJN_Q_64Q       => RType
  | FSGNJX_Q_64Q       => RType  | FMIN_Q_64Q         => RType
  | FMAX_Q_64Q         => RType  | FCVT_RNE_S_Q_64Q   => RType
  | FCVT_RTZ_S_Q_64Q   => RType  | FCVT_RDN_S_Q_64Q   => RType
  | FCVT_RUP_S_Q_64Q   => RType  | FCVT_RMM_S_Q_64Q   => RType
  | FCVT_DYN_S_Q_64Q   => RType  | FCVT_RNE_Q_S_64Q   => RType
  | FCVT_RTZ_Q_S_64Q   => RType  | FCVT_RDN_Q_S_64Q   => RType
  | FCVT_RUP_Q_S_64Q   => RType  | FCVT_RMM_Q_S_64Q   => RType
  | FCVT_DYN_Q_S_64Q   => RType  | FCVT_RNE_D_Q_64Q   => RType
  | FCVT_RTZ_D_Q_64Q   => RType  | FCVT_RDN_D_Q_64Q   => RType
  | FCVT_RUP_D_Q_64Q   => RType  | FCVT_RMM_D_Q_64Q   => RType
  | FCVT_DYN_D_Q_64Q   => RType  | FCVT_RNE_Q_D_64Q   => RType
  | FCVT_RTZ_Q_D_64Q   => RType  | FCVT_RDN_Q_D_64Q   => RType
  | FCVT_RUP_Q_D_64Q   => RType  | FCVT_RMM_Q_D_64Q   => RType
  | FCVT_DYN_Q_D_64Q   => RType  | FEQ_Q_64Q          => RType
  | FLT_Q_64Q          => RType  | FLE_Q_64Q          => RType
  | FCLASS_Q_64Q       => RType  | FCVT_RNE_W_Q_64Q   => RType
  | FCVT_RTZ_W_Q_64Q   => RType  | FCVT_RDN_W_Q_64Q   => RType
  | FCVT_RUP_W_Q_64Q   => RType  | FCVT_RMM_W_Q_64Q   => RType
  | FCVT_DYN_W_Q_64Q   => RType  | FCVT_RNE_WU_Q_64Q  => RType
  | FCVT_RTZ_WU_Q_64Q  => RType  | FCVT_RDN_WU_Q_64Q  => RType
  | FCVT_RUP_WU_Q_64Q  => RType  | FCVT_RMM_WU_Q_64Q  => RType
  | FCVT_DYN_WU_Q_64Q  => RType  | FCVT_RNE_Q_W_64Q   => RType
  | FCVT_RTZ_Q_W_64Q   => RType  | FCVT_RDN_Q_W_64Q   => RType
  | FCVT_RUP_Q_W_64Q   => RType  | FCVT_RMM_Q_W_64Q   => RType
  | FCVT_DYN_Q_W_64Q   => RType  | FCVT_RNE_Q_WU_64Q  => RType
  | FCVT_RTZ_Q_WU_64Q  => RType  | FCVT_RDN_Q_WU_64Q  => RType
  | FCVT_RUP_Q_WU_64Q  => RType  | FCVT_RMM_Q_WU_64Q  => RType
  | FCVT_DYN_Q_WU_64Q  => RType  | FCVT_RNE_L_Q_64Q   => RType
  | FCVT_RTZ_L_Q_64Q   => RType  | FCVT_RDN_L_Q_64Q   => RType
  | FCVT_RUP_L_Q_64Q   => RType  | FCVT_RMM_L_Q_64Q   => RType
  | FCVT_DYN_L_Q_64Q   => RType  | FCVT_RNE_LU_Q_64Q  => RType
  | FCVT_RTZ_LU_Q_64Q  => RType  | FCVT_RDN_LU_Q_64Q  => RType
  | FCVT_RUP_LU_Q_64Q  => RType  | FCVT_RMM_LU_Q_64Q  => RType
  | FCVT_DYN_LU_Q_64Q  => RType  | FCVT_RNE_Q_L_64Q   => RType
  | FCVT_RTZ_Q_L_64Q   => RType  | FCVT_RDN_Q_L_64Q   => RType
  | FCVT_RUP_Q_L_64Q   => RType  | FCVT_RMM_Q_L_64Q   => RType
  | FCVT_DYN_Q_L_64Q   => RType  | FCVT_RNE_Q_LU_64Q  => RType
  | FCVT_RTZ_Q_LU_64Q  => RType  | FCVT_RDN_Q_LU_64Q  => RType
  | FCVT_RUP_Q_LU_64Q  => RType  | FCVT_RMM_Q_LU_64Q  => RType
  | FCVT_DYN_Q_LU_64Q  => RType
  end.

Inductive field :=
| opcode | fct2 | fct3 | fct7 | rs1 | rs2 | rs3 | rd | immI | immS | immB | immU
| immJ.

Definition has_opcode (t : instruction_type) :=
  match t with
  | RType => true | R4Type => true | IType => true | SType => true
  | BType => true | UType  => true | JType => true
  end.

Definition has_fct2 (t : instruction_type) :=
  match t with
  | RType => false | R4Type => true  | IType => false | SType => false
  | BType => false | UType  => false | JType => false
  end.

Definition has_fct3 (t : instruction_type) :=
  match t with
  | RType => true | R4Type => true  | IType => true  | SType => true
  | BType => true | UType  => false | JType => false
  end.

Definition has_fct7 (t : instruction_type) :=
  match t with
  | RType => true  | R4Type => false | IType => false | SType => false
  | BType => false | UType  => false | JType => false
  end.

Definition has_rs1 (t : instruction_type) :=
  match t with
  | RType => true | R4Type => true  | IType => true  | SType => true
  | BType => true | UType  => false | JType => false
  end.

Definition has_rs2 (t : instruction_type) :=
  match t with
  | RType => true | R4Type => true  | IType => false | SType => true
  | BType => true | UType  => false | JType => false
  end.

Definition has_rs3 (t : instruction_type) :=
  match t with
  | RType => false | R4Type => true  | IType => false | SType => false
  | BType => false | UType  => false | JType => false
  end.

Definition has_rd (t : instruction_type) :=
  match t with
  | RType => true  | R4Type => true | IType => true | SType => false
  | BType => false | UType  => true | JType => true
  end.

Definition has_immI (t : instruction_type) :=
  match t with
  | RType => false | R4Type => false | IType => true | SType => false
  | BType => false | UType  => false | JType => false
  end.

Definition has_immS (t : instruction_type) :=
  match t with
  | RType => false | R4Type => false | IType => false | SType => true
  | BType => false | UType  => false | JType => false
  end.

Definition has_immB (t : instruction_type) :=
  match t with
  | RType => false | R4Type => false | IType => false | SType => false
  | BType => true  | UType  => false | JType => false
  end.

Definition has_immU (t : instruction_type) :=
  match t with
  | RType => false | R4Type => false | IType => false | SType => false
  | BType => false | UType  => true  | JType => false
  end.

Definition has_immJ (t : instruction_type) :=
  match t with
  | RType => false | R4Type => false | IType => false | SType => false
  | BType => false | UType  => false | JType => true
  end.

Definition instruction_type_fields (t : instruction_type) :=
  app (if has_opcode t then [opcode] else []) (
  app (if has_fct2   t then [fct2  ] else []) (
  app (if has_fct3   t then [fct3  ] else []) (
  app (if has_fct7   t then [fct7  ] else []) (
  app (if has_rs1    t then [rs1   ] else []) (
  app (if has_rs2    t then [rs2   ] else []) (
  app (if has_rs3    t then [rs3   ] else []) (
  app (if has_rd     t then [rd    ] else []) (
  app (if has_immI   t then [immI  ] else []) (
  app (if has_immS   t then [immS  ] else []) (
  app (if has_immB   t then [immB  ] else []) (
  app (if has_immU   t then [immU  ] else []) (
       if has_immJ   t then [immJ  ] else [])
  ))))))))))).

Definition is_field_identifier (f : field) :=
  match f with
  | opcode => true  | fct2 => true  | fct3 => true  | fct7 => true
  | rs1    => false | rs2  => false | rs3  => false | rd   => false
  | immI   => false | immS => false | immB => false | immU => false
  | immJ   => false
  end.

Definition is_field_data (f : field) := negb (is_field_identifier f).

Inductive opcode_name :=
| opc_OP     | opc_JALR   | opc_LOAD      | opc_OP_IMM | opc_MISC_MEM
| opc_STORE  | opc_BRANCH | opc_LUI       | opc_AUIPC  | opc_JAL
| opc_SYSTEM | opc_OP_32  | opc_OP_IMM_32 | opc_AMO    | opc_OP_FP
| opc_MADD   | opc_MSUB   | opc_NMSUB     | opc_NMADD  | opc_LOAD_FP
| opc_STORE_FP.

Definition opcode_bin (o : opcode_name) :=
  match o with
  | opc_OP        => Ob~0~1~1~0~0~1~1 | opc_JALR    => Ob~1~1~0~0~1~1~1
  | opc_LOAD      => Ob~0~0~0~0~0~1~1 | opc_OP_IMM  => Ob~0~0~1~0~0~1~1
  | opc_MISC_MEM  => Ob~0~0~0~1~1~1~1 | opc_STORE   => Ob~0~1~0~0~0~1~1
  | opc_BRANCH    => Ob~1~1~0~0~0~1~1 | opc_LUI     => Ob~0~1~1~0~1~1~1
  | opc_AUIPC     => Ob~0~0~1~0~1~1~1 | opc_JAL     => Ob~1~1~0~1~1~1~1
  | opc_SYSTEM    => Ob~1~1~1~0~0~1~1 | opc_OP_32   => Ob~0~1~1~1~0~1~1
  | opc_OP_IMM_32 => Ob~0~0~1~1~0~1~1 | opc_AMO     => Ob~0~1~0~1~1~1~1
  | opc_OP_FP     => Ob~1~0~1~0~0~1~1 | opc_MADD    => Ob~1~0~0~0~0~1~1
  | opc_MSUB      => Ob~1~0~0~0~1~1~1 | opc_NMSUB   => Ob~1~0~0~1~0~1~1
  | opc_NMADD     => Ob~1~0~0~1~1~1~1 | opc_LOAD_FP => Ob~0~0~0~0~1~1~1
  | opc_STORE_FP  => Ob~0~1~0~0~1~1~1
  end.

Definition instruction_opcode
  (i : {i : instruction | has_opcode (get_instruction_type i) = true})
:=
  match proj1_sig i with
  | LUI_32I            => opc_LUI       | AUIPC_32I          => opc_AUIPC
  | JAL_32I            => opc_JAL       | JALR_32I           => opc_JALR
  | BEQ_32I            => opc_BRANCH    | BNE_32I            => opc_BRANCH
  | BLT_32I            => opc_BRANCH    | BGE_32I            => opc_BRANCH
  | BLTU_32I           => opc_BRANCH    | BGEU_32I           => opc_BRANCH
  | LB_32I             => opc_LOAD      | LH_32I             => opc_LOAD
  | LW_32I             => opc_LOAD      | LBU_32I            => opc_LOAD
  | LHU_32I            => opc_LOAD      | SB_32I             => opc_STORE
  | SH_32I             => opc_STORE     | SW_32I             => opc_STORE
  | ADDI_32I           => opc_OP_IMM    | SLTI_32I           => opc_OP_IMM
  | SLTIU_32I          => opc_OP_IMM    | XORI_32I           => opc_OP_IMM
  | ORI_32I            => opc_OP_IMM    | ANDI_32I           => opc_OP_IMM
  | SLLI_32I           => opc_OP_IMM    | SRLI_32I           => opc_OP_IMM
  | SRAI_32I           => opc_OP_IMM    | ADD_32I            => opc_OP
  | SUB_32I            => opc_OP        | SLL_32I            => opc_OP
  | SLT_32I            => opc_OP        | SLTU_32I           => opc_OP
  | XOR_32I            => opc_OP        | SRL_32I            => opc_OP
  | SRA_32I            => opc_OP        | OR_32I             => opc_OP
  | AND_32I            => opc_OP        | FENCE_32I          => opc_MISC_MEM
  | ECALL_32I          => opc_SYSTEM    | EBREAK_32I         => opc_SYSTEM
  | LUI_64I            => opc_LUI       | AUIPC_64I          => opc_AUIPC
  | JAL_64I            => opc_JAL       | JALR_64I           => opc_JALR
  | BEQ_64I            => opc_BRANCH    | BNE_64I            => opc_BRANCH
  | BLT_64I            => opc_BRANCH    | BGE_64I            => opc_BRANCH
  | BLTU_64I           => opc_BRANCH    | BGEU_64I           => opc_BRANCH
  | LB_64I             => opc_LOAD      | LH_64I             => opc_LOAD
  | LW_64I             => opc_LOAD      | LBU_64I            => opc_LOAD
  | LHU_64I            => opc_LOAD      | SB_64I             => opc_STORE
  | SH_64I             => opc_STORE     | SW_64I             => opc_STORE
  | ADDI_64I           => opc_OP_IMM    | SLTI_64I           => opc_OP_IMM
  | SLTIU_64I          => opc_OP_IMM    | XORI_64I           => opc_OP_IMM
  | ORI_64I            => opc_OP_IMM    | ANDI_64I           => opc_OP_IMM
  | SLLI_64I           => opc_OP_IMM    | SRLI_64I           => opc_OP_IMM
  | SRAI_64I           => opc_OP_IMM    | ADD_64I            => opc_OP
  | SUB_64I            => opc_OP        | SLL_64I            => opc_OP
  | SLT_64I            => opc_OP        | SLTU_64I           => opc_OP
  | XOR_64I            => opc_OP        | SRL_64I            => opc_OP
  | SRA_64I            => opc_OP        | OR_64I             => opc_OP
  | AND_64I            => opc_OP        | FENCE_64I          => opc_MISC_MEM
  | ECALL_64I          => opc_SYSTEM    | EBREAK_64I         => opc_SYSTEM
  | LWU_64I            => opc_LOAD      | LD_64I             => opc_LOAD
  | SD_64I             => opc_STORE     | ADDIW_64I          => opc_OP_IMM_32
  | SLLIW_64I          => opc_OP_IMM_32 | SRLIW_64I          => opc_OP_IMM_32
  | SRAIW_64I          => opc_OP_IMM_32 | ADDW_64I           => opc_OP_32
  | SUBW_64I           => opc_OP_32     | SLLW_64I           => opc_OP_32
  | SRLW_64I           => opc_OP_32     | SRAW_64I           => opc_OP_32
  | FENCE_I_32Zifencei => opc_MISC_MEM  | FENCE_I_64Zifencei => opc_MISC_MEM
  | CSRRW_32Zicsr      => opc_SYSTEM    | CSRRS_32Zicsr      => opc_SYSTEM
  | CSRRC_32Zicsr      => opc_SYSTEM    | CSRRWI_32Zicsr     => opc_SYSTEM
  | CSRRSI_32Zicsr     => opc_SYSTEM    | CSRRCI_32Zicsr     => opc_SYSTEM
  | CSRRW_64Zicsr      => opc_SYSTEM    | CSRRS_64Zicsr      => opc_SYSTEM
  | CSRRC_64Zicsr      => opc_SYSTEM    | CSRRWI_64Zicsr     => opc_SYSTEM
  | CSRRSI_64Zicsr     => opc_SYSTEM    | CSRRCI_64Zicsr     => opc_SYSTEM
  | MUL_32M            => opc_OP        | MULH_32M           => opc_OP
  | MULHSU_32M         => opc_OP        | MULHU_32M          => opc_OP
  | DIV_32M            => opc_OP        | DIVU_32M           => opc_OP
  | REM_32M            => opc_OP        | REMU_32M           => opc_OP
  | MUL_64M            => opc_OP        | MULH_64M           => opc_OP
  | MULHSU_64M         => opc_OP        | MULHU_64M          => opc_OP
  | DIV_64M            => opc_OP        | DIVU_64M           => opc_OP
  | REM_64M            => opc_OP        | REMU_64M           => opc_OP
  | MULW_64M           => opc_OP_32     | DIVW_64M           => opc_OP_32
  | DIVUW_64M          => opc_OP_32     | REMW_64M           => opc_OP_32
  | REMUW_64M          => opc_OP_32     | LR_W_00_32A        => opc_AMO
  | LR_W_01_32A        => opc_AMO       | LR_W_10_32A        => opc_AMO
  | LR_W_11_32A        => opc_AMO       | SC_W_00_32A        => opc_AMO
  | SC_W_01_32A        => opc_AMO       | SC_W_10_32A        => opc_AMO
  | SC_W_11_32A        => opc_AMO       | AMOSWAP_W_00_32A   => opc_AMO
  | AMOSWAP_W_01_32A   => opc_AMO       | AMOSWAP_W_10_32A   => opc_AMO
  | AMOSWAP_W_11_32A   => opc_AMO       | AMOADD_W_00_32A    => opc_AMO
  | AMOADD_W_01_32A    => opc_AMO       | AMOADD_W_10_32A    => opc_AMO
  | AMOADD_W_11_32A    => opc_AMO       | AMOXOR_W_00_32A    => opc_AMO
  | AMOXOR_W_01_32A    => opc_AMO       | AMOXOR_W_10_32A    => opc_AMO
  | AMOXOR_W_11_32A    => opc_AMO       | AMOAND_W_00_32A    => opc_AMO
  | AMOAND_W_01_32A    => opc_AMO       | AMOAND_W_10_32A    => opc_AMO
  | AMOAND_W_11_32A    => opc_AMO       | AMOOR_W_00_32A     => opc_AMO
  | AMOOR_W_01_32A     => opc_AMO       | AMOOR_W_10_32A     => opc_AMO
  | AMOOR_W_11_32A     => opc_AMO       | AMOMIN_W_00_32A    => opc_AMO
  | AMOMIN_W_01_32A    => opc_AMO       | AMOMIN_W_10_32A    => opc_AMO
  | AMOMIN_W_11_32A    => opc_AMO       | AMOMAX_W_00_32A    => opc_AMO
  | AMOMAX_W_01_32A    => opc_AMO       | AMOMAX_W_10_32A    => opc_AMO
  | AMOMAX_W_11_32A    => opc_AMO       | AMOMINU_W_00_32A   => opc_AMO
  | AMOMINU_W_01_32A   => opc_AMO       | AMOMINU_W_10_32A   => opc_AMO
  | AMOMINU_W_11_32A   => opc_AMO       | AMOMAXU_W_00_32A   => opc_AMO
  | AMOMAXU_W_01_32A   => opc_AMO       | AMOMAXU_W_10_32A   => opc_AMO
  | AMOMAXU_W_11_32A   => opc_AMO       | LR_W_00_64A        => opc_AMO
  | LR_W_01_64A        => opc_AMO       | LR_W_10_64A        => opc_AMO
  | LR_W_11_64A        => opc_AMO       | SC_W_00_64A        => opc_AMO
  | SC_W_01_64A        => opc_AMO       | SC_W_10_64A        => opc_AMO
  | SC_W_11_64A        => opc_AMO       | AMOSWAP_W_00_64A   => opc_AMO
  | AMOSWAP_W_01_64A   => opc_AMO       | AMOSWAP_W_10_64A   => opc_AMO
  | AMOSWAP_W_11_64A   => opc_AMO       | AMOADD_W_00_64A    => opc_AMO
  | AMOADD_W_01_64A    => opc_AMO       | AMOADD_W_10_64A    => opc_AMO
  | AMOADD_W_11_64A    => opc_AMO       | AMOXOR_W_00_64A    => opc_AMO
  | AMOXOR_W_01_64A    => opc_AMO       | AMOXOR_W_10_64A    => opc_AMO
  | AMOXOR_W_11_64A    => opc_AMO       | AMOAND_W_00_64A    => opc_AMO
  | AMOAND_W_01_64A    => opc_AMO       | AMOAND_W_10_64A    => opc_AMO
  | AMOAND_W_11_64A    => opc_AMO       | AMOOR_W_00_64A     => opc_AMO
  | AMOOR_W_01_64A     => opc_AMO       | AMOOR_W_10_64A     => opc_AMO
  | AMOOR_W_11_64A     => opc_AMO       | AMOMIN_W_00_64A    => opc_AMO
  | AMOMIN_W_01_64A    => opc_AMO       | AMOMIN_W_10_64A    => opc_AMO
  | AMOMIN_W_11_64A    => opc_AMO       | AMOMAX_W_00_64A    => opc_AMO
  | AMOMAX_W_01_64A    => opc_AMO       | AMOMAX_W_10_64A    => opc_AMO
  | AMOMAX_W_11_64A    => opc_AMO       | AMOMINU_W_00_64A   => opc_AMO
  | AMOMINU_W_01_64A   => opc_AMO       | AMOMINU_W_10_64A   => opc_AMO
  | AMOMINU_W_11_64A   => opc_AMO       | AMOMAXU_W_00_64A   => opc_AMO
  | AMOMAXU_W_01_64A   => opc_AMO       | AMOMAXU_W_10_64A   => opc_AMO
  | AMOMAXU_W_11_64A   => opc_AMO       | LR_D_00_64A        => opc_AMO
  | LR_D_01_64A        => opc_AMO       | LR_D_10_64A        => opc_AMO
  | LR_D_11_64A        => opc_AMO       | SC_D_00_64A        => opc_AMO
  | SC_D_01_64A        => opc_AMO       | SC_D_10_64A        => opc_AMO
  | SC_D_11_64A        => opc_AMO       | AMOSWAP_D_00_64A   => opc_AMO
  | AMOSWAP_D_01_64A   => opc_AMO       | AMOSWAP_D_10_64A   => opc_AMO
  | AMOSWAP_D_11_64A   => opc_AMO       | AMOADD_D_00_64A    => opc_AMO
  | AMOADD_D_01_64A    => opc_AMO       | AMOADD_D_10_64A    => opc_AMO
  | AMOADD_D_11_64A    => opc_AMO       | AMOXOR_D_00_64A    => opc_AMO
  | AMOXOR_D_01_64A    => opc_AMO       | AMOXOR_D_10_64A    => opc_AMO
  | AMOXOR_D_11_64A    => opc_AMO       | AMOAND_D_00_64A    => opc_AMO
  | AMOAND_D_01_64A    => opc_AMO       | AMOAND_D_10_64A    => opc_AMO
  | AMOAND_D_11_64A    => opc_AMO       | AMOOR_D_00_64A     => opc_AMO
  | AMOOR_D_01_64A     => opc_AMO       | AMOOR_D_10_64A     => opc_AMO
  | AMOOR_D_11_64A     => opc_AMO       | AMOMIN_D_00_64A    => opc_AMO
  | AMOMIN_D_01_64A    => opc_AMO       | AMOMIN_D_10_64A    => opc_AMO
  | AMOMIN_D_11_64A    => opc_AMO       | AMOMAX_D_00_64A    => opc_AMO
  | AMOMAX_D_01_64A    => opc_AMO       | AMOMAX_D_10_64A    => opc_AMO
  | AMOMAX_D_11_64A    => opc_AMO       | AMOMINU_D_00_64A   => opc_AMO
  | AMOMINU_D_01_64A   => opc_AMO       | AMOMINU_D_10_64A   => opc_AMO
  | AMOMINU_D_11_64A   => opc_AMO       | AMOMAXU_D_00_64A   => opc_AMO
  | AMOMAXU_D_01_64A   => opc_AMO       | AMOMAXU_D_10_64A   => opc_AMO
  | AMOMAXU_D_11_64A   => opc_AMO       | FLW_32F            => opc_LOAD_FP
  | FSW_32F            => opc_STORE_FP  | FMADD_RNE_S_32F    => opc_MADD
  | FMADD_RTZ_S_32F    => opc_MADD      | FMADD_RDN_S_32F    => opc_MADD
  | FMADD_RUP_S_32F    => opc_MADD      | FMADD_RMM_S_32F    => opc_MADD
  | FMADD_DYN_S_32F    => opc_MADD      | FMSUB_RNE_S_32F    => opc_MSUB
  | FMSUB_RTZ_S_32F    => opc_MSUB      | FMSUB_RDN_S_32F    => opc_MSUB
  | FMSUB_RUP_S_32F    => opc_MSUB      | FMSUB_RMM_S_32F    => opc_MSUB
  | FMSUB_DYN_S_32F    => opc_MSUB      | FNMSUB_RNE_S_32F   => opc_NMSUB
  | FNMSUB_RTZ_S_32F   => opc_NMSUB     | FNMSUB_RDN_S_32F   => opc_NMSUB
  | FNMSUB_RUP_S_32F   => opc_NMSUB     | FNMSUB_RMM_S_32F   => opc_NMSUB
  | FNMSUB_DYN_S_32F   => opc_NMSUB     | FNMADD_RNE_S_32F   => opc_NMADD
  | FNMADD_RTZ_S_32F   => opc_NMADD     | FNMADD_RDN_S_32F   => opc_NMADD
  | FNMADD_RUP_S_32F   => opc_NMADD     | FNMADD_RMM_S_32F   => opc_NMADD
  | FNMADD_DYN_S_32F   => opc_NMADD     | FADD_RNE_S_32F     => opc_OP_FP
  | FADD_RTZ_S_32F     => opc_OP_FP     | FADD_RDN_S_32F     => opc_OP_FP
  | FADD_RUP_S_32F     => opc_OP_FP     | FADD_RMM_S_32F     => opc_OP_FP
  | FADD_DYN_S_32F     => opc_OP_FP     | FSUB_RNE_S_32F     => opc_OP_FP
  | FSUB_RTZ_S_32F     => opc_OP_FP     | FSUB_RDN_S_32F     => opc_OP_FP
  | FSUB_RUP_S_32F     => opc_OP_FP     | FSUB_RMM_S_32F     => opc_OP_FP
  | FSUB_DYN_S_32F     => opc_OP_FP     | FMUL_RNE_S_32F     => opc_OP_FP
  | FMUL_RTZ_S_32F     => opc_OP_FP     | FMUL_RDN_S_32F     => opc_OP_FP
  | FMUL_RUP_S_32F     => opc_OP_FP     | FMUL_RMM_S_32F     => opc_OP_FP
  | FMUL_DYN_S_32F     => opc_OP_FP     | FDIV_RNE_S_32F     => opc_OP_FP
  | FDIV_RTZ_S_32F     => opc_OP_FP     | FDIV_RDN_S_32F     => opc_OP_FP
  | FDIV_RUP_S_32F     => opc_OP_FP     | FDIV_RMM_S_32F     => opc_OP_FP
  | FDIV_DYN_S_32F     => opc_OP_FP     | FSQRT_RNE_S_32F    => opc_OP_FP
  | FSQRT_RTZ_S_32F    => opc_OP_FP     | FSQRT_RDN_S_32F    => opc_OP_FP
  | FSQRT_RUP_S_32F    => opc_OP_FP     | FSQRT_RMM_S_32F    => opc_OP_FP
  | FSQRT_DYN_S_32F    => opc_OP_FP     | FSGNJ_S_32F        => opc_OP_FP
  | FSGNJN_S_32F       => opc_OP_FP     | FSGNJX_S_32F       => opc_OP_FP
  | FMIN_S_32F         => opc_OP_FP     | FMAX_S_32F         => opc_OP_FP
  | FCVT_RNE_W_S_32F   => opc_OP_FP     | FCVT_RTZ_W_S_32F   => opc_OP_FP
  | FCVT_RDN_W_S_32F   => opc_OP_FP     | FCVT_RUP_W_S_32F   => opc_OP_FP
  | FCVT_RMM_W_S_32F   => opc_OP_FP     | FCVT_DYN_W_S_32F   => opc_OP_FP
  | FCVT_RNE_WU_S_32F  => opc_OP_FP     | FCVT_RTZ_WU_S_32F  => opc_OP_FP
  | FCVT_RDN_WU_S_32F  => opc_OP_FP     | FCVT_RUP_WU_S_32F  => opc_OP_FP
  | FCVT_RMM_WU_S_32F  => opc_OP_FP     | FCVT_DYN_WU_S_32F  => opc_OP_FP
  | FMV_X_W_32F        => opc_OP_FP     | FEQ_S_32F          => opc_OP_FP
  | FLT_S_32F          => opc_OP_FP     | FLE_S_32F          => opc_OP_FP
  | FCLASS_S_32F       => opc_OP_FP     | FCVT_RNE_S_W_32F   => opc_OP_FP
  | FCVT_RTZ_S_W_32F   => opc_OP_FP     | FCVT_RDN_S_W_32F   => opc_OP_FP
  | FCVT_RUP_S_W_32F   => opc_OP_FP     | FCVT_RMM_S_W_32F   => opc_OP_FP
  | FCVT_DYN_S_W_32F   => opc_OP_FP     | FCVT_RNE_S_WU_32F  => opc_OP_FP
  | FCVT_RTZ_S_WU_32F  => opc_OP_FP     | FCVT_RDN_S_WU_32F  => opc_OP_FP
  | FCVT_RUP_S_WU_32F  => opc_OP_FP     | FCVT_RMM_S_WU_32F  => opc_OP_FP
  | FCVT_DYN_S_WU_32F  => opc_OP_FP     | FMV_W_X_32F        => opc_OP_FP
  | FLW_64F            => opc_LOAD_FP   | FSW_64F            => opc_LOAD_FP
  | FMADD_RNE_S_64F    => opc_MADD      | FMADD_RTZ_S_64F    => opc_MADD
  | FMADD_RDN_S_64F    => opc_MADD      | FMADD_RUP_S_64F    => opc_MADD
  | FMADD_RMM_S_64F    => opc_MADD      | FMADD_DYN_S_64F    => opc_MADD
  | FMSUB_RNE_S_64F    => opc_MSUB      | FMSUB_RTZ_S_64F    => opc_MSUB
  | FMSUB_RDN_S_64F    => opc_MSUB      | FMSUB_RUP_S_64F    => opc_MSUB
  | FMSUB_RMM_S_64F    => opc_MSUB      | FMSUB_DYN_S_64F    => opc_MSUB
  | FNMSUB_RNE_S_64F   => opc_NMSUB     | FNMSUB_RTZ_S_64F   => opc_NMSUB
  | FNMSUB_RDN_S_64F   => opc_NMSUB     | FNMSUB_RUP_S_64F   => opc_NMSUB
  | FNMSUB_RMM_S_64F   => opc_NMSUB     | FNMSUB_DYN_S_64F   => opc_NMSUB
  | FNMADD_RNE_S_64F   => opc_NMADD     | FNMADD_RTZ_S_64F   => opc_NMADD
  | FNMADD_RDN_S_64F   => opc_NMADD     | FNMADD_RUP_S_64F   => opc_NMADD
  | FNMADD_RMM_S_64F   => opc_NMADD     | FNMADD_DYN_S_64F   => opc_NMADD
  | FADD_RNE_S_64F     => opc_OP_FP     | FADD_RTZ_S_64F     => opc_OP_FP
  | FADD_RDN_S_64F     => opc_OP_FP     | FADD_RUP_S_64F     => opc_OP_FP
  | FADD_RMM_S_64F     => opc_OP_FP     | FADD_DYN_S_64F     => opc_OP_FP
  | FSUB_RNE_S_64F     => opc_OP_FP     | FSUB_RTZ_S_64F     => opc_OP_FP
  | FSUB_RDN_S_64F     => opc_OP_FP     | FSUB_RUP_S_64F     => opc_OP_FP
  | FSUB_RMM_S_64F     => opc_OP_FP     | FSUB_DYN_S_64F     => opc_OP_FP
  | FMUL_RNE_S_64F     => opc_OP_FP     | FMUL_RTZ_S_64F     => opc_OP_FP
  | FMUL_RDN_S_64F     => opc_OP_FP     | FMUL_RUP_S_64F     => opc_OP_FP
  | FMUL_RMM_S_64F     => opc_OP_FP     | FMUL_DYN_S_64F     => opc_OP_FP
  | FDIV_RNE_S_64F     => opc_OP_FP     | FDIV_RTZ_S_64F     => opc_OP_FP
  | FDIV_RDN_S_64F     => opc_OP_FP     | FDIV_RUP_S_64F     => opc_OP_FP
  | FDIV_RMM_S_64F     => opc_OP_FP     | FDIV_DYN_S_64F     => opc_OP_FP
  | FSQRT_RNE_S_64F    => opc_OP_FP     | FSQRT_RTZ_S_64F    => opc_OP_FP
  | FSQRT_RDN_S_64F    => opc_OP_FP     | FSQRT_RUP_S_64F    => opc_OP_FP
  | FSQRT_RMM_S_64F    => opc_OP_FP     | FSQRT_DYN_S_64F    => opc_OP_FP
  | FSGNJ_S_64F        => opc_OP_FP     | FSGNJN_S_64F       => opc_OP_FP
  | FSGNJX_S_64F       => opc_OP_FP     | FMIN_S_64F         => opc_OP_FP
  | FMAX_S_64F         => opc_OP_FP     | FCVT_RNE_W_S_64F   => opc_OP_FP
  | FCVT_RTZ_W_S_64F   => opc_OP_FP     | FCVT_RDN_W_S_64F   => opc_OP_FP
  | FCVT_RUP_W_S_64F   => opc_OP_FP     | FCVT_RMM_W_S_64F   => opc_OP_FP
  | FCVT_DYN_W_S_64F   => opc_OP_FP     | FCVT_RNE_WU_S_64F  => opc_OP_FP
  | FCVT_RTZ_WU_S_64F  => opc_OP_FP     | FCVT_RDN_WU_S_64F  => opc_OP_FP
  | FCVT_RUP_WU_S_64F  => opc_OP_FP     | FCVT_RMM_WU_S_64F  => opc_OP_FP
  | FCVT_DYN_WU_S_64F  => opc_OP_FP     | FMV_X_W_64F        => opc_OP_FP
  | FEQ_S_64F          => opc_OP_FP     | FLT_S_64F          => opc_OP_FP
  | FLE_S_64F          => opc_OP_FP     | FCLASS_S_64F       => opc_OP_FP
  | FCVT_RNE_S_W_64F   => opc_OP_FP     | FCVT_RTZ_S_W_64F   => opc_OP_FP
  | FCVT_RDN_S_W_64F   => opc_OP_FP     | FCVT_RUP_S_W_64F   => opc_OP_FP
  | FCVT_RMM_S_W_64F   => opc_OP_FP     | FCVT_DYN_S_W_64F   => opc_OP_FP
  | FCVT_RNE_S_WU_64F  => opc_OP_FP     | FCVT_RTZ_S_WU_64F  => opc_OP_FP
  | FCVT_RDN_S_WU_64F  => opc_OP_FP     | FCVT_RUP_S_WU_64F  => opc_OP_FP
  | FCVT_RMM_S_WU_64F  => opc_OP_FP     | FCVT_DYN_S_WU_64F  => opc_OP_FP
  | FMV_W_X_64F        => opc_OP_FP     | FCVT_RNE_L_S_64F   => opc_OP_FP
  | FCVT_RTZ_L_S_64F   => opc_OP_FP     | FCVT_RDN_L_S_64F   => opc_OP_FP
  | FCVT_RUP_L_S_64F   => opc_OP_FP     | FCVT_RMM_L_S_64F   => opc_OP_FP
  | FCVT_DYN_L_S_64F   => opc_OP_FP     | FCVT_RNE_LU_S_64F  => opc_OP_FP
  | FCVT_RTZ_LU_S_64F  => opc_OP_FP     | FCVT_RDN_LU_S_64F  => opc_OP_FP
  | FCVT_RUP_LU_S_64F  => opc_OP_FP     | FCVT_RMM_LU_S_64F  => opc_OP_FP
  | FCVT_DYN_LU_S_64F  => opc_OP_FP     | FCVT_RNE_S_L_64F   => opc_OP_FP
  | FCVT_RTZ_S_L_64F   => opc_OP_FP     | FCVT_RDN_S_L_64F   => opc_OP_FP
  | FCVT_RUP_S_L_64F   => opc_OP_FP     | FCVT_RMM_S_L_64F   => opc_OP_FP
  | FCVT_DYN_S_L_64F   => opc_OP_FP     | FCVT_RNE_S_LU_64F  => opc_OP_FP
  | FCVT_RTZ_S_LU_64F  => opc_OP_FP     | FCVT_RDN_S_LU_64F  => opc_OP_FP
  | FCVT_RUP_S_LU_64F  => opc_OP_FP     | FCVT_RMM_S_LU_64F  => opc_OP_FP
  | FCVT_DYN_S_LU_64F  => opc_OP_FP     | FLD_32D            => opc_LOAD_FP
  | FSD_32D            => opc_STORE_FP  | FMADD_RNE_D_32D    => opc_MADD
  | FMADD_RTZ_D_32D    => opc_MADD      | FMADD_RDN_D_32D    => opc_MADD
  | FMADD_RUP_D_32D    => opc_MADD      | FMADD_RMM_D_32D    => opc_MADD
  | FMADD_DYN_D_32D    => opc_MADD      | FMSUB_RNE_D_32D    => opc_MSUB
  | FMSUB_RTZ_D_32D    => opc_MSUB      | FMSUB_RDN_D_32D    => opc_MSUB
  | FMSUB_RUP_D_32D    => opc_MSUB      | FMSUB_RMM_D_32D    => opc_MSUB
  | FMSUB_DYN_D_32D    => opc_MSUB      | FNMSUB_RNE_D_32D   => opc_NMSUB
  | FNMSUB_RTZ_D_32D   => opc_NMSUB     | FNMSUB_RDN_D_32D   => opc_NMSUB
  | FNMSUB_RUP_D_32D   => opc_NMSUB     | FNMSUB_RMM_D_32D   => opc_NMSUB
  | FNMSUB_DYN_D_32D   => opc_NMSUB     | FNMADD_RNE_D_32D   => opc_NMADD
  | FNMADD_RTZ_D_32D   => opc_NMADD     | FNMADD_RDN_D_32D   => opc_NMADD
  | FNMADD_RUP_D_32D   => opc_NMADD     | FNMADD_RMM_D_32D   => opc_NMADD
  | FNMADD_DYN_D_32D   => opc_NMADD     | FADD_RNE_D_32D     => opc_OP_FP
  | FADD_RTZ_D_32D     => opc_OP_FP     | FADD_RDN_D_32D     => opc_OP_FP
  | FADD_RUP_D_32D     => opc_OP_FP     | FADD_RMM_D_32D     => opc_OP_FP
  | FADD_DYN_D_32D     => opc_OP_FP     | FSUB_RNE_D_32D     => opc_OP_FP
  | FSUB_RTZ_D_32D     => opc_OP_FP     | FSUB_RDN_D_32D     => opc_OP_FP
  | FSUB_RUP_D_32D     => opc_OP_FP     | FSUB_RMM_D_32D     => opc_OP_FP
  | FSUB_DYN_D_32D     => opc_OP_FP     | FMUL_RNE_D_32D     => opc_OP_FP
  | FMUL_RTZ_D_32D     => opc_OP_FP     | FMUL_RDN_D_32D     => opc_OP_FP
  | FMUL_RUP_D_32D     => opc_OP_FP     | FMUL_RMM_D_32D     => opc_OP_FP
  | FMUL_DYN_D_32D     => opc_OP_FP     | FDIV_RNE_D_32D     => opc_OP_FP
  | FDIV_RTZ_D_32D     => opc_OP_FP     | FDIV_RDN_D_32D     => opc_OP_FP
  | FDIV_RUP_D_32D     => opc_OP_FP     | FDIV_RMM_D_32D     => opc_OP_FP
  | FDIV_DYN_D_32D     => opc_OP_FP     | FSQRT_RNE_D_32D    => opc_OP_FP
  | FSQRT_RTZ_D_32D    => opc_OP_FP     | FSQRT_RDN_D_32D    => opc_OP_FP
  | FSQRT_RUP_D_32D    => opc_OP_FP     | FSQRT_RMM_D_32D    => opc_OP_FP
  | FSQRT_DYN_D_32D    => opc_OP_FP     | FSGNJ_D_32D        => opc_OP_FP
  | FSGNJN_D_32D       => opc_OP_FP     | FSGNJX_D_32D       => opc_OP_FP
  | FMIN_D_32D         => opc_OP_FP     | FMAX_D_32D         => opc_OP_FP
  | FCVT_RNE_S_D_32D   => opc_OP_FP     | FCVT_RTZ_S_D_32D   => opc_OP_FP
  | FCVT_RDN_S_D_32D   => opc_OP_FP     | FCVT_RUP_S_D_32D   => opc_OP_FP
  | FCVT_RMM_S_D_32D   => opc_OP_FP     | FCVT_DYN_S_D_32D   => opc_OP_FP
  | FCVT_RNE_D_S_32D   => opc_OP_FP     | FCVT_RTZ_D_S_32D   => opc_OP_FP
  | FCVT_RDN_D_S_32D   => opc_OP_FP     | FCVT_RUP_D_S_32D   => opc_OP_FP
  | FCVT_RMM_D_S_32D   => opc_OP_FP     | FCVT_DYN_D_S_32D   => opc_OP_FP
  | FEQ_D_32D          => opc_OP_FP     | FLT_D_32D          => opc_OP_FP
  | FLE_D_32D          => opc_OP_FP     | FCLASS_D_32D       => opc_OP_FP
  | FCVT_RNE_W_D_32D   => opc_OP_FP     | FCVT_RTZ_W_D_32D   => opc_OP_FP
  | FCVT_RDN_W_D_32D   => opc_OP_FP     | FCVT_RUP_W_D_32D   => opc_OP_FP
  | FCVT_RMM_W_D_32D   => opc_OP_FP     | FCVT_DYN_W_D_32D   => opc_OP_FP
  | FCVT_RNE_WU_D_32D  => opc_OP_FP     | FCVT_RTZ_WU_D_32D  => opc_OP_FP
  | FCVT_RDN_WU_D_32D  => opc_OP_FP     | FCVT_RUP_WU_D_32D  => opc_OP_FP
  | FCVT_RMM_WU_D_32D  => opc_OP_FP     | FCVT_DYN_WU_D_32D  => opc_OP_FP
  | FCVT_RNE_D_W_32D   => opc_OP_FP     | FCVT_RTZ_D_W_32D   => opc_OP_FP
  | FCVT_RDN_D_W_32D   => opc_OP_FP     | FCVT_RUP_D_W_32D   => opc_OP_FP
  | FCVT_RMM_D_W_32D   => opc_OP_FP     | FCVT_DYN_D_W_32D   => opc_OP_FP
  | FCVT_RNE_D_WU_32D  => opc_OP_FP     | FCVT_RTZ_D_WU_32D  => opc_OP_FP
  | FCVT_RDN_D_WU_32D  => opc_OP_FP     | FCVT_RUP_D_WU_32D  => opc_OP_FP
  | FCVT_RMM_D_WU_32D  => opc_OP_FP     | FCVT_DYN_D_WU_32D  => opc_OP_FP
  | FLD_64D            => opc_LOAD_FP   | FSD_64D            => opc_STORE_FP
  | FMADD_RNE_D_64D    => opc_MADD      | FMADD_RTZ_D_64D    => opc_MADD
  | FMADD_RDN_D_64D    => opc_MADD      | FMADD_RUP_D_64D    => opc_MADD
  | FMADD_RMM_D_64D    => opc_MADD      | FMADD_DYN_D_64D    => opc_MADD
  | FMSUB_RNE_D_64D    => opc_MSUB      | FMSUB_RTZ_D_64D    => opc_MSUB
  | FMSUB_RDN_D_64D    => opc_MSUB      | FMSUB_RUP_D_64D    => opc_MSUB
  | FMSUB_RMM_D_64D    => opc_MSUB      | FMSUB_DYN_D_64D    => opc_MSUB
  | FNMSUB_RNE_D_64D   => opc_NMSUB     | FNMSUB_RTZ_D_64D   => opc_NMSUB
  | FNMSUB_RDN_D_64D   => opc_NMSUB     | FNMSUB_RUP_D_64D   => opc_NMSUB
  | FNMSUB_RMM_D_64D   => opc_NMSUB     | FNMSUB_DYN_D_64D   => opc_NMSUB
  | FNMADD_RNE_D_64D   => opc_NMADD     | FNMADD_RTZ_D_64D   => opc_NMADD
  | FNMADD_RDN_D_64D   => opc_NMADD     | FNMADD_RUP_D_64D   => opc_NMADD
  | FNMADD_RMM_D_64D   => opc_NMADD     | FNMADD_DYN_D_64D   => opc_NMADD
  | FADD_RNE_D_64D     => opc_OP_FP     | FADD_RTZ_D_64D     => opc_OP_FP
  | FADD_RDN_D_64D     => opc_OP_FP     | FADD_RUP_D_64D     => opc_OP_FP
  | FADD_RMM_D_64D     => opc_OP_FP     | FADD_DYN_D_64D     => opc_OP_FP
  | FSUB_RNE_D_64D     => opc_OP_FP     | FSUB_RTZ_D_64D     => opc_OP_FP
  | FSUB_RDN_D_64D     => opc_OP_FP     | FSUB_RUP_D_64D     => opc_OP_FP
  | FSUB_RMM_D_64D     => opc_OP_FP     | FSUB_DYN_D_64D     => opc_OP_FP
  | FMUL_RNE_D_64D     => opc_OP_FP     | FMUL_RTZ_D_64D     => opc_OP_FP
  | FMUL_RDN_D_64D     => opc_OP_FP     | FMUL_RUP_D_64D     => opc_OP_FP
  | FMUL_RMM_D_64D     => opc_OP_FP     | FMUL_DYN_D_64D     => opc_OP_FP
  | FDIV_RNE_D_64D     => opc_OP_FP     | FDIV_RTZ_D_64D     => opc_OP_FP
  | FDIV_RDN_D_64D     => opc_OP_FP     | FDIV_RUP_D_64D     => opc_OP_FP
  | FDIV_RMM_D_64D     => opc_OP_FP     | FDIV_DYN_D_64D     => opc_OP_FP
  | FSQRT_RNE_D_64D    => opc_OP_FP     | FSQRT_RTZ_D_64D    => opc_OP_FP
  | FSQRT_RDN_D_64D    => opc_OP_FP     | FSQRT_RUP_D_64D    => opc_OP_FP
  | FSQRT_RMM_D_64D    => opc_OP_FP     | FSQRT_DYN_D_64D    => opc_OP_FP
  | FSGNJ_D_64D        => opc_OP_FP     | FSGNJN_D_64D       => opc_OP_FP
  | FSGNJX_D_64D       => opc_OP_FP     | FMIN_D_64D         => opc_OP_FP
  | FMAX_D_64D         => opc_OP_FP     | FCVT_RNE_S_D_64D   => opc_OP_FP
  | FCVT_RTZ_S_D_64D   => opc_OP_FP     | FCVT_RDN_S_D_64D   => opc_OP_FP
  | FCVT_RUP_S_D_64D   => opc_OP_FP     | FCVT_RMM_S_D_64D   => opc_OP_FP
  | FCVT_DYN_S_D_64D   => opc_OP_FP     | FCVT_RNE_D_S_64D   => opc_OP_FP
  | FCVT_RTZ_D_S_64D   => opc_OP_FP     | FCVT_RDN_D_S_64D   => opc_OP_FP
  | FCVT_RUP_D_S_64D   => opc_OP_FP     | FCVT_RMM_D_S_64D   => opc_OP_FP
  | FCVT_DYN_D_S_64D   => opc_OP_FP     | FEQ_D_64D          => opc_OP_FP
  | FLT_D_64D          => opc_OP_FP     | FLE_D_64D          => opc_OP_FP
  | FCLASS_D_64D       => opc_OP_FP     | FCVT_RNE_W_D_64D   => opc_OP_FP
  | FCVT_RTZ_W_D_64D   => opc_OP_FP     | FCVT_RDN_W_D_64D   => opc_OP_FP
  | FCVT_RUP_W_D_64D   => opc_OP_FP     | FCVT_RMM_W_D_64D   => opc_OP_FP
  | FCVT_DYN_W_D_64D   => opc_OP_FP     | FCVT_RNE_WU_D_64D  => opc_OP_FP
  | FCVT_RTZ_WU_D_64D  => opc_OP_FP     | FCVT_RDN_WU_D_64D  => opc_OP_FP
  | FCVT_RUP_WU_D_64D  => opc_OP_FP     | FCVT_RMM_WU_D_64D  => opc_OP_FP
  | FCVT_DYN_WU_D_64D  => opc_OP_FP     | FCVT_RNE_D_W_64D   => opc_OP_FP
  | FCVT_RTZ_D_W_64D   => opc_OP_FP     | FCVT_RDN_D_W_64D   => opc_OP_FP
  | FCVT_RUP_D_W_64D   => opc_OP_FP     | FCVT_RMM_D_W_64D   => opc_OP_FP
  | FCVT_DYN_D_W_64D   => opc_OP_FP     | FCVT_RNE_D_WU_64D  => opc_OP_FP
  | FCVT_RTZ_D_WU_64D  => opc_OP_FP     | FCVT_RDN_D_WU_64D  => opc_OP_FP
  | FCVT_RUP_D_WU_64D  => opc_OP_FP     | FCVT_RMM_D_WU_64D  => opc_OP_FP
  | FCVT_DYN_D_WU_64D  => opc_OP_FP     | FCVT_RNE_L_D_64D   => opc_OP_FP
  | FCVT_RTZ_L_D_64D   => opc_OP_FP     | FCVT_RDN_L_D_64D   => opc_OP_FP
  | FCVT_RUP_L_D_64D   => opc_OP_FP     | FCVT_RMM_L_D_64D   => opc_OP_FP
  | FCVT_DYN_L_D_64D   => opc_OP_FP     | FCVT_RNE_LU_D_64D  => opc_OP_FP
  | FCVT_RTZ_LU_D_64D  => opc_OP_FP     | FCVT_RDN_LU_D_64D  => opc_OP_FP
  | FCVT_RUP_LU_D_64D  => opc_OP_FP     | FCVT_RMM_LU_D_64D  => opc_OP_FP
  | FCVT_DYN_LU_D_64D  => opc_OP_FP     | FMV_X_D_64D        => opc_OP_FP
  | FCVT_RNE_D_L_64D   => opc_OP_FP     | FCVT_RTZ_D_L_64D   => opc_OP_FP
  | FCVT_RDN_D_L_64D   => opc_OP_FP     | FCVT_RUP_D_L_64D   => opc_OP_FP
  | FCVT_RMM_D_L_64D   => opc_OP_FP     | FCVT_DYN_D_L_64D   => opc_OP_FP
  | FCVT_RNE_D_LU_64D  => opc_OP_FP     | FCVT_RTZ_D_LU_64D  => opc_OP_FP
  | FCVT_RDN_D_LU_64D  => opc_OP_FP     | FCVT_RUP_D_LU_64D  => opc_OP_FP
  | FCVT_RMM_D_LU_64D  => opc_OP_FP     | FCVT_DYN_D_LU_64D  => opc_OP_FP
  | FMV_D_X_64D        => opc_OP_FP     | FLQ_32Q            => opc_LOAD_FP
  | FSQ_32Q            => opc_STORE_FP  | FMADD_RNE_Q_32Q    => opc_MADD
  | FMADD_RTZ_Q_32Q    => opc_MADD      | FMADD_RDN_Q_32Q    => opc_MADD
  | FMADD_RUP_Q_32Q    => opc_MADD      | FMADD_RMM_Q_32Q    => opc_MADD
  | FMADD_DYN_Q_32Q    => opc_MADD      | FMSUB_RNE_Q_32Q    => opc_MSUB
  | FMSUB_RTZ_Q_32Q    => opc_MSUB      | FMSUB_RDN_Q_32Q    => opc_MSUB
  | FMSUB_RUP_Q_32Q    => opc_MSUB      | FMSUB_RMM_Q_32Q    => opc_MSUB
  | FMSUB_DYN_Q_32Q    => opc_MSUB      | FNMSUB_RNE_Q_32Q   => opc_NMSUB
  | FNMSUB_RTZ_Q_32Q   => opc_NMSUB     | FNMSUB_RDN_Q_32Q   => opc_NMSUB
  | FNMSUB_RUP_Q_32Q   => opc_NMSUB     | FNMSUB_RMM_Q_32Q   => opc_NMSUB
  | FNMSUB_DYN_Q_32Q   => opc_NMSUB     | FNMADD_RNE_Q_32Q   => opc_NMADD
  | FNMADD_RTZ_Q_32Q   => opc_NMADD     | FNMADD_RDN_Q_32Q   => opc_NMADD
  | FNMADD_RUP_Q_32Q   => opc_NMADD     | FNMADD_RMM_Q_32Q   => opc_NMADD
  | FNMADD_DYN_Q_32Q   => opc_NMADD     | FADD_RNE_Q_32Q     => opc_OP_FP
  | FADD_RTZ_Q_32Q     => opc_OP_FP     | FADD_RDN_Q_32Q     => opc_OP_FP
  | FADD_RUP_Q_32Q     => opc_OP_FP     | FADD_RMM_Q_32Q     => opc_OP_FP
  | FADD_DYN_Q_32Q     => opc_OP_FP     | FSUB_RNE_Q_32Q     => opc_OP_FP
  | FSUB_RTZ_Q_32Q     => opc_OP_FP     | FSUB_RDN_Q_32Q     => opc_OP_FP
  | FSUB_RUP_Q_32Q     => opc_OP_FP     | FSUB_RMM_Q_32Q     => opc_OP_FP
  | FSUB_DYN_Q_32Q     => opc_OP_FP     | FMUL_RNE_Q_32Q     => opc_OP_FP
  | FMUL_RTZ_Q_32Q     => opc_OP_FP     | FMUL_RDN_Q_32Q     => opc_OP_FP
  | FMUL_RUP_Q_32Q     => opc_OP_FP     | FMUL_RMM_Q_32Q     => opc_OP_FP
  | FMUL_DYN_Q_32Q     => opc_OP_FP     | FDIV_RNE_Q_32Q     => opc_OP_FP
  | FDIV_RTZ_Q_32Q     => opc_OP_FP     | FDIV_RDN_Q_32Q     => opc_OP_FP
  | FDIV_RUP_Q_32Q     => opc_OP_FP     | FDIV_RMM_Q_32Q     => opc_OP_FP
  | FDIV_DYN_Q_32Q     => opc_OP_FP     | FSQRT_RNE_Q_32Q    => opc_OP_FP
  | FSQRT_RTZ_Q_32Q    => opc_OP_FP     | FSQRT_RDN_Q_32Q    => opc_OP_FP
  | FSQRT_RUP_Q_32Q    => opc_OP_FP     | FSQRT_RMM_Q_32Q    => opc_OP_FP
  | FSQRT_DYN_Q_32Q    => opc_OP_FP     | FSGNJ_Q_32Q        => opc_OP_FP
  | FSGNJN_Q_32Q       => opc_OP_FP     | FSGNJX_Q_32Q       => opc_OP_FP
  | FMIN_Q_32Q         => opc_OP_FP     | FMAX_Q_32Q         => opc_OP_FP
  | FCVT_RNE_S_Q_32Q   => opc_OP_FP     | FCVT_RTZ_S_Q_32Q   => opc_OP_FP
  | FCVT_RDN_S_Q_32Q   => opc_OP_FP     | FCVT_RUP_S_Q_32Q   => opc_OP_FP
  | FCVT_RMM_S_Q_32Q   => opc_OP_FP     | FCVT_DYN_S_Q_32Q   => opc_OP_FP
  | FCVT_RNE_Q_S_32Q   => opc_OP_FP     | FCVT_RTZ_Q_S_32Q   => opc_OP_FP
  | FCVT_RDN_Q_S_32Q   => opc_OP_FP     | FCVT_RUP_Q_S_32Q   => opc_OP_FP
  | FCVT_RMM_Q_S_32Q   => opc_OP_FP     | FCVT_DYN_Q_S_32Q   => opc_OP_FP
  | FCVT_RNE_D_Q_32Q   => opc_OP_FP     | FCVT_RTZ_D_Q_32Q   => opc_OP_FP
  | FCVT_RDN_D_Q_32Q   => opc_OP_FP     | FCVT_RUP_D_Q_32Q   => opc_OP_FP
  | FCVT_RMM_D_Q_32Q   => opc_OP_FP     | FCVT_DYN_D_Q_32Q   => opc_OP_FP
  | FCVT_RNE_Q_D_32Q   => opc_OP_FP     | FCVT_RTZ_Q_D_32Q   => opc_OP_FP
  | FCVT_RDN_Q_D_32Q   => opc_OP_FP     | FCVT_RUP_Q_D_32Q   => opc_OP_FP
  | FCVT_RMM_Q_D_32Q   => opc_OP_FP     | FCVT_DYN_Q_D_32Q   => opc_OP_FP
  | FEQ_Q_32Q          => opc_OP_FP     | FLT_Q_32Q          => opc_OP_FP
  | FLE_Q_32Q          => opc_OP_FP     | FCLASS_Q_32Q       => opc_OP_FP
  | FCVT_RNE_W_Q_32Q   => opc_OP_FP     | FCVT_RTZ_W_Q_32Q   => opc_OP_FP
  | FCVT_RDN_W_Q_32Q   => opc_OP_FP     | FCVT_RUP_W_Q_32Q   => opc_OP_FP
  | FCVT_RMM_W_Q_32Q   => opc_OP_FP     | FCVT_DYN_W_Q_32Q   => opc_OP_FP
  | FCVT_RNE_WU_Q_32Q  => opc_OP_FP     | FCVT_RTZ_WU_Q_32Q  => opc_OP_FP
  | FCVT_RDN_WU_Q_32Q  => opc_OP_FP     | FCVT_RUP_WU_Q_32Q  => opc_OP_FP
  | FCVT_RMM_WU_Q_32Q  => opc_OP_FP     | FCVT_DYN_WU_Q_32Q  => opc_OP_FP
  | FCVT_RNE_Q_W_32Q   => opc_OP_FP     | FCVT_RTZ_Q_W_32Q   => opc_OP_FP
  | FCVT_RDN_Q_W_32Q   => opc_OP_FP     | FCVT_RUP_Q_W_32Q   => opc_OP_FP
  | FCVT_RMM_Q_W_32Q   => opc_OP_FP     | FCVT_DYN_Q_W_32Q   => opc_OP_FP
  | FCVT_RNE_Q_WU_32Q  => opc_OP_FP     | FCVT_RTZ_Q_WU_32Q  => opc_OP_FP
  | FCVT_RDN_Q_WU_32Q  => opc_OP_FP     | FCVT_RUP_Q_WU_32Q  => opc_OP_FP
  | FCVT_RMM_Q_WU_32Q  => opc_OP_FP     | FCVT_DYN_Q_WU_32Q  => opc_OP_FP
  | FLQ_64Q            => opc_LOAD_FP   | FSQ_64Q            => opc_STORE_FP
  | FMADD_RNE_Q_64Q    => opc_MADD      | FMADD_RTZ_Q_64Q    => opc_MADD
  | FMADD_RDN_Q_64Q    => opc_MADD      | FMADD_RUP_Q_64Q    => opc_MADD
  | FMADD_RMM_Q_64Q    => opc_MADD      | FMADD_DYN_Q_64Q    => opc_MADD
  | FMSUB_RNE_Q_64Q    => opc_MSUB      | FMSUB_RTZ_Q_64Q    => opc_MSUB
  | FMSUB_RDN_Q_64Q    => opc_MSUB      | FMSUB_RUP_Q_64Q    => opc_MSUB
  | FMSUB_RMM_Q_64Q    => opc_MSUB      | FMSUB_DYN_Q_64Q    => opc_MSUB
  | FNMSUB_RNE_Q_64Q   => opc_NMSUB     | FNMSUB_RTZ_Q_64Q   => opc_NMSUB
  | FNMSUB_RDN_Q_64Q   => opc_NMSUB     | FNMSUB_RUP_Q_64Q   => opc_NMSUB
  | FNMSUB_RMM_Q_64Q   => opc_NMSUB     | FNMSUB_DYN_Q_64Q   => opc_NMSUB
  | FNMADD_RNE_Q_64Q   => opc_NMADD     | FNMADD_RTZ_Q_64Q   => opc_NMADD
  | FNMADD_RDN_Q_64Q   => opc_NMADD     | FNMADD_RUP_Q_64Q   => opc_NMADD
  | FNMADD_RMM_Q_64Q   => opc_NMADD     | FNMADD_DYN_Q_64Q   => opc_NMADD
  | FADD_RNE_Q_64Q     => opc_OP_FP     | FADD_RTZ_Q_64Q     => opc_OP_FP
  | FADD_RDN_Q_64Q     => opc_OP_FP     | FADD_RUP_Q_64Q     => opc_OP_FP
  | FADD_RMM_Q_64Q     => opc_OP_FP     | FADD_DYN_Q_64Q     => opc_OP_FP
  | FSUB_RNE_Q_64Q     => opc_OP_FP     | FSUB_RTZ_Q_64Q     => opc_OP_FP
  | FSUB_RDN_Q_64Q     => opc_OP_FP     | FSUB_RUP_Q_64Q     => opc_OP_FP
  | FSUB_RMM_Q_64Q     => opc_OP_FP     | FSUB_DYN_Q_64Q     => opc_OP_FP
  | FMUL_RNE_Q_64Q     => opc_OP_FP     | FMUL_RTZ_Q_64Q     => opc_OP_FP
  | FMUL_RDN_Q_64Q     => opc_OP_FP     | FMUL_RUP_Q_64Q     => opc_OP_FP
  | FMUL_RMM_Q_64Q     => opc_OP_FP     | FMUL_DYN_Q_64Q     => opc_OP_FP
  | FDIV_RNE_Q_64Q     => opc_OP_FP     | FDIV_RTZ_Q_64Q     => opc_OP_FP
  | FDIV_RDN_Q_64Q     => opc_OP_FP     | FDIV_RUP_Q_64Q     => opc_OP_FP
  | FDIV_RMM_Q_64Q     => opc_OP_FP     | FDIV_DYN_Q_64Q     => opc_OP_FP
  | FSQRT_RNE_Q_64Q    => opc_OP_FP     | FSQRT_RTZ_Q_64Q    => opc_OP_FP
  | FSQRT_RDN_Q_64Q    => opc_OP_FP     | FSQRT_RUP_Q_64Q    => opc_OP_FP
  | FSQRT_RMM_Q_64Q    => opc_OP_FP     | FSQRT_DYN_Q_64Q    => opc_OP_FP
  | FSGNJ_Q_64Q        => opc_OP_FP     | FSGNJN_Q_64Q       => opc_OP_FP
  | FSGNJX_Q_64Q       => opc_OP_FP     | FMIN_Q_64Q         => opc_OP_FP
  | FMAX_Q_64Q         => opc_OP_FP     | FCVT_RNE_S_Q_64Q   => opc_OP_FP
  | FCVT_RTZ_S_Q_64Q   => opc_OP_FP     | FCVT_RDN_S_Q_64Q   => opc_OP_FP
  | FCVT_RUP_S_Q_64Q   => opc_OP_FP     | FCVT_RMM_S_Q_64Q   => opc_OP_FP
  | FCVT_DYN_S_Q_64Q   => opc_OP_FP     | FCVT_RNE_Q_S_64Q   => opc_OP_FP
  | FCVT_RTZ_Q_S_64Q   => opc_OP_FP     | FCVT_RDN_Q_S_64Q   => opc_OP_FP
  | FCVT_RUP_Q_S_64Q   => opc_OP_FP     | FCVT_RMM_Q_S_64Q   => opc_OP_FP
  | FCVT_DYN_Q_S_64Q   => opc_OP_FP     | FCVT_RNE_D_Q_64Q   => opc_OP_FP
  | FCVT_RTZ_D_Q_64Q   => opc_OP_FP     | FCVT_RDN_D_Q_64Q   => opc_OP_FP
  | FCVT_RUP_D_Q_64Q   => opc_OP_FP     | FCVT_RMM_D_Q_64Q   => opc_OP_FP
  | FCVT_DYN_D_Q_64Q   => opc_OP_FP     | FCVT_RNE_Q_D_64Q   => opc_OP_FP
  | FCVT_RTZ_Q_D_64Q   => opc_OP_FP     | FCVT_RDN_Q_D_64Q   => opc_OP_FP
  | FCVT_RUP_Q_D_64Q   => opc_OP_FP     | FCVT_RMM_Q_D_64Q   => opc_OP_FP
  | FCVT_DYN_Q_D_64Q   => opc_OP_FP     | FEQ_Q_64Q          => opc_OP_FP
  | FLT_Q_64Q          => opc_OP_FP     | FLE_Q_64Q          => opc_OP_FP
  | FCLASS_Q_64Q       => opc_OP_FP     | FCVT_RNE_W_Q_64Q   => opc_OP_FP
  | FCVT_RTZ_W_Q_64Q   => opc_OP_FP     | FCVT_RDN_W_Q_64Q   => opc_OP_FP
  | FCVT_RUP_W_Q_64Q   => opc_OP_FP     | FCVT_RMM_W_Q_64Q   => opc_OP_FP
  | FCVT_DYN_W_Q_64Q   => opc_OP_FP     | FCVT_RNE_WU_Q_64Q  => opc_OP_FP
  | FCVT_RTZ_WU_Q_64Q  => opc_OP_FP     | FCVT_RDN_WU_Q_64Q  => opc_OP_FP
  | FCVT_RUP_WU_Q_64Q  => opc_OP_FP     | FCVT_RMM_WU_Q_64Q  => opc_OP_FP
  | FCVT_DYN_WU_Q_64Q  => opc_OP_FP     | FCVT_RNE_Q_W_64Q   => opc_OP_FP
  | FCVT_RTZ_Q_W_64Q   => opc_OP_FP     | FCVT_RDN_Q_W_64Q   => opc_OP_FP
  | FCVT_RUP_Q_W_64Q   => opc_OP_FP     | FCVT_RMM_Q_W_64Q   => opc_OP_FP
  | FCVT_DYN_Q_W_64Q   => opc_OP_FP     | FCVT_RNE_Q_WU_64Q  => opc_OP_FP
  | FCVT_RTZ_Q_WU_64Q  => opc_OP_FP     | FCVT_RDN_Q_WU_64Q  => opc_OP_FP
  | FCVT_RUP_Q_WU_64Q  => opc_OP_FP     | FCVT_RMM_Q_WU_64Q  => opc_OP_FP
  | FCVT_DYN_Q_WU_64Q  => opc_OP_FP     | FCVT_RNE_L_Q_64Q   => opc_OP_FP
  | FCVT_RTZ_L_Q_64Q   => opc_OP_FP     | FCVT_RDN_L_Q_64Q   => opc_OP_FP
  | FCVT_RUP_L_Q_64Q   => opc_OP_FP     | FCVT_RMM_L_Q_64Q   => opc_OP_FP
  | FCVT_DYN_L_Q_64Q   => opc_OP_FP     | FCVT_RNE_LU_Q_64Q  => opc_OP_FP
  | FCVT_RTZ_LU_Q_64Q  => opc_OP_FP     | FCVT_RDN_LU_Q_64Q  => opc_OP_FP
  | FCVT_RUP_LU_Q_64Q  => opc_OP_FP     | FCVT_RMM_LU_Q_64Q  => opc_OP_FP
  | FCVT_DYN_LU_Q_64Q  => opc_OP_FP     | FCVT_RNE_Q_L_64Q   => opc_OP_FP
  | FCVT_RTZ_Q_L_64Q   => opc_OP_FP     | FCVT_RDN_Q_L_64Q   => opc_OP_FP
  | FCVT_RUP_Q_L_64Q   => opc_OP_FP     | FCVT_RMM_Q_L_64Q   => opc_OP_FP
  | FCVT_DYN_Q_L_64Q   => opc_OP_FP     | FCVT_RNE_Q_LU_64Q  => opc_OP_FP
  | FCVT_RTZ_Q_LU_64Q  => opc_OP_FP     | FCVT_RDN_Q_LU_64Q  => opc_OP_FP
  | FCVT_RUP_Q_LU_64Q  => opc_OP_FP     | FCVT_RMM_Q_LU_64Q  => opc_OP_FP
  | FCVT_DYN_Q_LU_64Q  => opc_OP_FP
  end.

Inductive fct3_type :=
| fct3_ADD    | fct3_SUB    | fct3_SLL     | fct3_SLT    | fct3_SLTU
| fct3_XOR    | fct3_SRL    | fct3_SRA     | fct3_OR     | fct3_AND
| fct3_LB     | fct3_LH     | fct3_LW      | fct3_LBU    | fct3_LHU
| fct3_SLTI   | fct3_SLTIU  | fct3_ADDI    | fct3_XORI   | fct3_ORI
| fct3_ANDI   | fct3_SLLI   | fct3_SRLI    | fct3_SRAI   | fct3_FENCE
| fct3_SB     | fct3_SH     | fct3_SW      | fct3_BEQ    | fct3_BNE
| fct3_BLT    | fct3_BGE    | fct3_BLTU    | fct3_BGEU   | fct3_PRIV
| fct3_ADDW   | fct3_SUBW   | fct3_SLLW    | fct3_SRLW   | fct3_SRAW
| fct3_LWU    | fct3_LD     | fct3_ADDIW   | fct3_SLLIW  | fct3_SRLIW
| fct3_SRAIW  | fct3_SD     | fct3_FENCE_I | fct3_CSRRW  | fct3_CSRRS
| fct3_CSRRC  | fct3_CSRRWI | fct3_CSRRSI  | fct3_CSRRCI | fct3_MUL
| fct3_MULH   | fct3_MULHSU | fct3_MULHU   | fct3_DIV    | fct3_DIVU
| fct3_REM    | fct3_REMU   | fct3_MULW    | fct3_DIVW   | fct3_DIVUW
| fct3_REMW   | fct3_REMUW  | fct3_AMOW    | fct3_AMOD   | fct3_FSGNJ
| fct3_FSGNJN | fct3_FSGNJX | fct3_FMIN    | fct3_FMAX   | fct3_FMV
| fct3_FEQ    | fct3_FLT    | fct3_FLE     | fct3_FCLASS | fct3_FLW
| fct3_FSW    | fct3_JALR   | fct3_AW      | fct3_AD     | fct3_RNE
| fct3_RTZ    | fct3_RDN    | fct3_RUP     | fct3_RMM    | fct3_DYN
| fct3_LSF    | fct3_LSD    | fct3_LSQ.

Definition fct3_bin (f : fct3_type) :=
  match f with
  | fct3_ADD    => Ob~0~0~0 | fct3_SUB    => Ob~0~0~0 | fct3_SLL     => Ob~0~0~1
  | fct3_SLT    => Ob~0~1~0 | fct3_SLTU   => Ob~0~1~1 | fct3_XOR     => Ob~1~0~0
  | fct3_SRL    => Ob~1~0~1 | fct3_SRA    => Ob~1~0~1 | fct3_OR      => Ob~1~1~0
  | fct3_AND    => Ob~1~1~1 | fct3_LB     => Ob~0~0~0 | fct3_LH      => Ob~0~0~1
  | fct3_LW     => Ob~0~1~0 | fct3_LBU    => Ob~1~0~0 | fct3_LHU     => Ob~1~0~1
  | fct3_SLTI   => Ob~0~1~0 | fct3_SLTIU  => Ob~0~1~1 | fct3_ADDI    => Ob~0~0~0
  | fct3_XORI   => Ob~1~0~0 | fct3_ORI    => Ob~1~1~0 | fct3_ANDI    => Ob~1~1~1
  | fct3_SLLI   => Ob~0~0~1 | fct3_SRLI   => Ob~1~0~1 | fct3_SRAI    => Ob~1~0~1
  | fct3_FENCE  => Ob~0~0~0 | fct3_SB     => Ob~0~0~0 | fct3_SH      => Ob~0~0~1
  | fct3_SW     => Ob~0~1~0 | fct3_BEQ    => Ob~0~0~0 | fct3_BNE     => Ob~0~0~1
  | fct3_BLT    => Ob~1~0~0 | fct3_BGE    => Ob~1~0~1 | fct3_BLTU    => Ob~1~1~0
  | fct3_BGEU   => Ob~1~1~1 | fct3_PRIV   => Ob~0~0~0 | fct3_ADDW    => Ob~0~0~0
  | fct3_SUBW   => Ob~0~0~0 | fct3_SLLW   => Ob~0~0~1 | fct3_SRLW    => Ob~1~0~1
  | fct3_SRAW   => Ob~1~0~1 | fct3_LWU    => Ob~1~1~0 | fct3_LD      => Ob~0~1~1
  | fct3_ADDIW  => Ob~0~0~0 | fct3_SLLIW  => Ob~0~0~1 | fct3_SRLIW   => Ob~1~0~1
  | fct3_SRAIW  => Ob~1~0~1 | fct3_SD     => Ob~0~1~1 | fct3_FENCE_I => Ob~0~0~1
  | fct3_CSRRW  => Ob~0~0~1 | fct3_CSRRS  => Ob~0~1~0 | fct3_CSRRC   => Ob~0~1~1
  | fct3_CSRRWI => Ob~1~0~1 | fct3_CSRRSI => Ob~1~1~0 | fct3_CSRRCI  => Ob~1~1~1
  | fct3_MUL    => Ob~0~0~0 | fct3_MULH   => Ob~0~0~1 | fct3_MULHSU  => Ob~0~1~0
  | fct3_MULHU  => Ob~0~1~1 | fct3_DIV    => Ob~1~0~0 | fct3_DIVU    => Ob~1~0~1
  | fct3_REM    => Ob~1~1~0 | fct3_REMU   => Ob~1~1~1 | fct3_MULW    => Ob~0~0~0
  | fct3_DIVW   => Ob~1~0~0 | fct3_DIVUW  => Ob~1~0~1 | fct3_REMW    => Ob~1~1~0
  | fct3_REMUW  => Ob~1~1~1 | fct3_AMOW   => Ob~0~1~0 | fct3_AMOD    => Ob~0~1~1
  | fct3_FSGNJ  => Ob~0~0~0 | fct3_FSGNJN => Ob~0~0~1 | fct3_FSGNJX  => Ob~0~1~0
  | fct3_FMIN   => Ob~0~0~0 | fct3_FMAX   => Ob~0~0~1 | fct3_FMV     => Ob~0~0~0
  | fct3_FEQ    => Ob~0~1~0 | fct3_FLT    => Ob~0~0~1 | fct3_FLE     => Ob~0~0~0
  | fct3_FCLASS => Ob~0~0~1 | fct3_FLW    => Ob~0~1~0 | fct3_FSW     => Ob~0~1~0
  | fct3_JALR   => Ob~0~0~0 | fct3_AW     => Ob~0~1~0 | fct3_AD      => Ob~0~1~1
  | fct3_RNE    => Ob~0~0~0 | fct3_RTZ    => Ob~0~0~1 | fct3_RDN     => Ob~0~1~0
  | fct3_RUP    => Ob~0~1~1 | fct3_RMM    => Ob~1~0~0 | fct3_DYN     => Ob~1~1~1
  | fct3_LSF    => Ob~0~1~0 | fct3_LSD    => Ob~0~1~1 | fct3_LSQ     => Ob~1~0~0
  end.

Definition instruction_fct3 :
  forall (i : instruction), has_fct3 (get_instruction_type i) = true
  -> fct3_type.
refine (fun i =>
  match i with
  | JALR_32I           => fun _ => fct3_JALR
  | BEQ_32I            => fun _ => fct3_BEQ
  | BNE_32I            => fun _ => fct3_BNE
  | BLT_32I            => fun _ => fct3_BLT
  | BGE_32I            => fun _ => fct3_BGE
  | BLTU_32I           => fun _ => fct3_BLTU
  | BGEU_32I           => fun _ => fct3_BGEU
  | LB_32I             => fun _ => fct3_LB
  | LH_32I             => fun _ => fct3_LH
  | LW_32I             => fun _ => fct3_LW
  | LBU_32I            => fun _ => fct3_LBU
  | LHU_32I            => fun _ => fct3_LHU
  | SB_32I             => fun _ => fct3_SB
  | SH_32I             => fun _ => fct3_SH
  | SW_32I             => fun _ => fct3_SW
  | ADDI_32I           => fun _ => fct3_ADDI
  | SLTI_32I           => fun _ => fct3_SLTI
  | SLTIU_32I          => fun _ => fct3_SLTIU
  | XORI_32I           => fun _ => fct3_XORI
  | ORI_32I            => fun _ => fct3_ORI
  | ANDI_32I           => fun _ => fct3_ANDI
  | SLLI_32I           => fun _ => fct3_SLLI
  | SRLI_32I           => fun _ => fct3_SRLI
  | SRAI_32I           => fun _ => fct3_SRAI
  | ADD_32I            => fun _ => fct3_ADD
  | SUB_32I            => fun _ => fct3_SUB
  | SLL_32I            => fun _ => fct3_SLL
  | SLT_32I            => fun _ => fct3_SLT
  | SLTU_32I           => fun _ => fct3_SLTU
  | XOR_32I            => fun _ => fct3_XOR
  | SRL_32I            => fun _ => fct3_SRL
  | SRA_32I            => fun _ => fct3_SRA
  | OR_32I             => fun _ => fct3_OR
  | AND_32I            => fun _ => fct3_AND
  | FENCE_32I          => fun _ => fct3_FENCE
  | ECALL_32I          => fun _ => fct3_PRIV
  | EBREAK_32I         => fun _ => fct3_PRIV
  | JALR_64I           => fun _ => fct3_JALR
  | BEQ_64I            => fun _ => fct3_BEQ
  | BNE_64I            => fun _ => fct3_BNE
  | BLT_64I            => fun _ => fct3_BLT
  | BGE_64I            => fun _ => fct3_BGE
  | BLTU_64I           => fun _ => fct3_BLTU
  | BGEU_64I           => fun _ => fct3_BGEU
  | LB_64I             => fun _ => fct3_LB
  | LH_64I             => fun _ => fct3_LH
  | LW_64I             => fun _ => fct3_LW
  | LBU_64I            => fun _ => fct3_LBU
  | LHU_64I            => fun _ => fct3_LHU
  | SB_64I             => fun _ => fct3_SB
  | SH_64I             => fun _ => fct3_SH
  | SW_64I             => fun _ => fct3_SW
  | ADDI_64I           => fun _ => fct3_ADDI
  | SLTI_64I           => fun _ => fct3_SLTI
  | SLTIU_64I          => fun _ => fct3_SLTIU
  | XORI_64I           => fun _ => fct3_XORI
  | ORI_64I            => fun _ => fct3_ORI
  | ANDI_64I           => fun _ => fct3_ANDI
  | SLLI_64I           => fun _ => fct3_SLLI
  | SRLI_64I           => fun _ => fct3_SRLI
  | SRAI_64I           => fun _ => fct3_SRAI
  | ADD_64I            => fun _ => fct3_ADD
  | SUB_64I            => fun _ => fct3_SUB
  | SLL_64I            => fun _ => fct3_SLL
  | SLT_64I            => fun _ => fct3_SLT
  | SLTU_64I           => fun _ => fct3_SLTU
  | XOR_64I            => fun _ => fct3_XOR
  | SRL_64I            => fun _ => fct3_SRL
  | SRA_64I            => fun _ => fct3_SRA
  | OR_64I             => fun _ => fct3_OR
  | AND_64I            => fun _ => fct3_AND
  | FENCE_64I          => fun _ => fct3_FENCE
  | ECALL_64I          => fun _ => fct3_PRIV
  | EBREAK_64I         => fun _ => fct3_PRIV
  | LWU_64I            => fun _ => fct3_LWU
  | LD_64I             => fun _ => fct3_LD
  | SD_64I             => fun _ => fct3_SD
  | ADDIW_64I          => fun _ => fct3_ADDIW
  | SLLIW_64I          => fun _ => fct3_SLLIW
  | SRLIW_64I          => fun _ => fct3_SRLIW
  | SRAIW_64I          => fun _ => fct3_SRAIW
  | ADDW_64I           => fun _ => fct3_ADDW
  | SUBW_64I           => fun _ => fct3_SUBW
  | SLLW_64I           => fun _ => fct3_SLLW
  | SRLW_64I           => fun _ => fct3_SRLW
  | SRAW_64I           => fun _ => fct3_SRAW
  | FENCE_I_32Zifencei => fun _ => fct3_FENCE_I
  | FENCE_I_64Zifencei => fun _ => fct3_FENCE_I
  | CSRRW_32Zicsr      => fun _ => fct3_CSRRW
  | CSRRS_32Zicsr      => fun _ => fct3_CSRRS
  | CSRRC_32Zicsr      => fun _ => fct3_CSRRC
  | CSRRWI_32Zicsr     => fun _ => fct3_CSRRWI
  | CSRRSI_32Zicsr     => fun _ => fct3_CSRRSI
  | CSRRCI_32Zicsr     => fun _ => fct3_CSRRCI
  | CSRRW_64Zicsr      => fun _ => fct3_CSRRW
  | CSRRS_64Zicsr      => fun _ => fct3_CSRRS
  | CSRRC_64Zicsr      => fun _ => fct3_CSRRC
  | CSRRWI_64Zicsr     => fun _ => fct3_CSRRWI
  | CSRRSI_64Zicsr     => fun _ => fct3_CSRRSI
  | CSRRCI_64Zicsr     => fun _ => fct3_CSRRCI
  | MUL_32M            => fun _ => fct3_MUL
  | MULH_32M           => fun _ => fct3_MULH
  | MULHSU_32M         => fun _ => fct3_MULHSU
  | MULHU_32M          => fun _ => fct3_MULHU
  | DIV_32M            => fun _ => fct3_DIV
  | DIVU_32M           => fun _ => fct3_DIVU
  | REM_32M            => fun _ => fct3_REM
  | REMU_32M           => fun _ => fct3_REMU
  | MUL_64M            => fun _ => fct3_MUL
  | MULH_64M           => fun _ => fct3_MULH
  | MULHSU_64M         => fun _ => fct3_MULHSU
  | MULHU_64M          => fun _ => fct3_MULHU
  | DIV_64M            => fun _ => fct3_DIV
  | DIVU_64M           => fun _ => fct3_DIVU
  | REM_64M            => fun _ => fct3_REM
  | REMU_64M           => fun _ => fct3_REMU
  | MULW_64M           => fun _ => fct3_MULW
  | DIVW_64M           => fun _ => fct3_DIVW
  | DIVUW_64M          => fun _ => fct3_DIVUW
  | REMW_64M           => fun _ => fct3_REMW
  | REMUW_64M          => fun _ => fct3_REMUW
  | LR_W_00_32A        => fun _ => fct3_AW
  | LR_W_01_32A        => fun _ => fct3_AW
  | LR_W_10_32A        => fun _ => fct3_AW
  | LR_W_11_32A        => fun _ => fct3_AW
  | SC_W_00_32A        => fun _ => fct3_AW
  | SC_W_01_32A        => fun _ => fct3_AW
  | SC_W_10_32A        => fun _ => fct3_AW
  | SC_W_11_32A        => fun _ => fct3_AW
  | AMOSWAP_W_00_32A   => fun _ => fct3_AW
  | AMOSWAP_W_01_32A   => fun _ => fct3_AW
  | AMOSWAP_W_10_32A   => fun _ => fct3_AW
  | AMOSWAP_W_11_32A   => fun _ => fct3_AW
  | AMOADD_W_00_32A    => fun _ => fct3_AW
  | AMOADD_W_01_32A    => fun _ => fct3_AW
  | AMOADD_W_10_32A    => fun _ => fct3_AW
  | AMOADD_W_11_32A    => fun _ => fct3_AW
  | AMOXOR_W_00_32A    => fun _ => fct3_AW
  | AMOXOR_W_01_32A    => fun _ => fct3_AW
  | AMOXOR_W_10_32A    => fun _ => fct3_AW
  | AMOXOR_W_11_32A    => fun _ => fct3_AW
  | AMOAND_W_00_32A    => fun _ => fct3_AW
  | AMOAND_W_01_32A    => fun _ => fct3_AW
  | AMOAND_W_10_32A    => fun _ => fct3_AW
  | AMOAND_W_11_32A    => fun _ => fct3_AW
  | AMOOR_W_00_32A     => fun _ => fct3_AW
  | AMOOR_W_01_32A     => fun _ => fct3_AW
  | AMOOR_W_10_32A     => fun _ => fct3_AW
  | AMOOR_W_11_32A     => fun _ => fct3_AW
  | AMOMIN_W_00_32A    => fun _ => fct3_AW
  | AMOMIN_W_01_32A    => fun _ => fct3_AW
  | AMOMIN_W_10_32A    => fun _ => fct3_AW
  | AMOMIN_W_11_32A    => fun _ => fct3_AW
  | AMOMAX_W_00_32A    => fun _ => fct3_AW
  | AMOMAX_W_01_32A    => fun _ => fct3_AW
  | AMOMAX_W_10_32A    => fun _ => fct3_AW
  | AMOMAX_W_11_32A    => fun _ => fct3_AW
  | AMOMINU_W_00_32A   => fun _ => fct3_AW
  | AMOMINU_W_01_32A   => fun _ => fct3_AW
  | AMOMINU_W_10_32A   => fun _ => fct3_AW
  | AMOMINU_W_11_32A   => fun _ => fct3_AW
  | AMOMAXU_W_00_32A   => fun _ => fct3_AW
  | AMOMAXU_W_01_32A   => fun _ => fct3_AW
  | AMOMAXU_W_10_32A   => fun _ => fct3_AW
  | AMOMAXU_W_11_32A   => fun _ => fct3_AW
  | LR_W_00_64A        => fun _ => fct3_AW
  | LR_W_01_64A        => fun _ => fct3_AW
  | LR_W_10_64A        => fun _ => fct3_AW
  | LR_W_11_64A        => fun _ => fct3_AW
  | SC_W_00_64A        => fun _ => fct3_AW
  | SC_W_01_64A        => fun _ => fct3_AW
  | SC_W_10_64A        => fun _ => fct3_AW
  | SC_W_11_64A        => fun _ => fct3_AW
  | AMOSWAP_W_00_64A   => fun _ => fct3_AW
  | AMOSWAP_W_01_64A   => fun _ => fct3_AW
  | AMOSWAP_W_10_64A   => fun _ => fct3_AW
  | AMOSWAP_W_11_64A   => fun _ => fct3_AW
  | AMOADD_W_00_64A    => fun _ => fct3_AW
  | AMOADD_W_01_64A    => fun _ => fct3_AW
  | AMOADD_W_10_64A    => fun _ => fct3_AW
  | AMOADD_W_11_64A    => fun _ => fct3_AW
  | AMOXOR_W_00_64A    => fun _ => fct3_AW
  | AMOXOR_W_01_64A    => fun _ => fct3_AW
  | AMOXOR_W_10_64A    => fun _ => fct3_AW
  | AMOXOR_W_11_64A    => fun _ => fct3_AW
  | AMOAND_W_00_64A    => fun _ => fct3_AW
  | AMOAND_W_01_64A    => fun _ => fct3_AW
  | AMOAND_W_10_64A    => fun _ => fct3_AW
  | AMOAND_W_11_64A    => fun _ => fct3_AW
  | AMOOR_W_00_64A     => fun _ => fct3_AW
  | AMOOR_W_01_64A     => fun _ => fct3_AW
  | AMOOR_W_10_64A     => fun _ => fct3_AW
  | AMOOR_W_11_64A     => fun _ => fct3_AW
  | AMOMIN_W_00_64A    => fun _ => fct3_AW
  | AMOMIN_W_01_64A    => fun _ => fct3_AW
  | AMOMIN_W_10_64A    => fun _ => fct3_AW
  | AMOMIN_W_11_64A    => fun _ => fct3_AW
  | AMOMAX_W_00_64A    => fun _ => fct3_AW
  | AMOMAX_W_01_64A    => fun _ => fct3_AW
  | AMOMAX_W_10_64A    => fun _ => fct3_AW
  | AMOMAX_W_11_64A    => fun _ => fct3_AW
  | AMOMINU_W_00_64A   => fun _ => fct3_AW
  | AMOMINU_W_01_64A   => fun _ => fct3_AW
  | AMOMINU_W_10_64A   => fun _ => fct3_AW
  | AMOMINU_W_11_64A   => fun _ => fct3_AW
  | AMOMAXU_W_00_64A   => fun _ => fct3_AW
  | AMOMAXU_W_01_64A   => fun _ => fct3_AW
  | AMOMAXU_W_10_64A   => fun _ => fct3_AW
  | AMOMAXU_W_11_64A   => fun _ => fct3_AW
  | LR_D_00_64A        => fun _ => fct3_AD
  | LR_D_01_64A        => fun _ => fct3_AD
  | LR_D_10_64A        => fun _ => fct3_AD
  | LR_D_11_64A        => fun _ => fct3_AD
  | SC_D_00_64A        => fun _ => fct3_AD
  | SC_D_01_64A        => fun _ => fct3_AD
  | SC_D_10_64A        => fun _ => fct3_AD
  | SC_D_11_64A        => fun _ => fct3_AD
  | AMOSWAP_D_00_64A   => fun _ => fct3_AD
  | AMOSWAP_D_01_64A   => fun _ => fct3_AD
  | AMOSWAP_D_10_64A   => fun _ => fct3_AD
  | AMOSWAP_D_11_64A   => fun _ => fct3_AD
  | AMOADD_D_00_64A    => fun _ => fct3_AD
  | AMOADD_D_01_64A    => fun _ => fct3_AD
  | AMOADD_D_10_64A    => fun _ => fct3_AD
  | AMOADD_D_11_64A    => fun _ => fct3_AD
  | AMOXOR_D_00_64A    => fun _ => fct3_AD
  | AMOXOR_D_01_64A    => fun _ => fct3_AD
  | AMOXOR_D_10_64A    => fun _ => fct3_AD
  | AMOXOR_D_11_64A    => fun _ => fct3_AD
  | AMOAND_D_00_64A    => fun _ => fct3_AD
  | AMOAND_D_01_64A    => fun _ => fct3_AD
  | AMOAND_D_10_64A    => fun _ => fct3_AD
  | AMOAND_D_11_64A    => fun _ => fct3_AD
  | AMOOR_D_00_64A     => fun _ => fct3_AD
  | AMOOR_D_01_64A     => fun _ => fct3_AD
  | AMOOR_D_10_64A     => fun _ => fct3_AD
  | AMOOR_D_11_64A     => fun _ => fct3_AD
  | AMOMIN_D_00_64A    => fun _ => fct3_AD
  | AMOMIN_D_01_64A    => fun _ => fct3_AD
  | AMOMIN_D_10_64A    => fun _ => fct3_AD
  | AMOMIN_D_11_64A    => fun _ => fct3_AD
  | AMOMAX_D_00_64A    => fun _ => fct3_AD
  | AMOMAX_D_01_64A    => fun _ => fct3_AD
  | AMOMAX_D_10_64A    => fun _ => fct3_AD
  | AMOMAX_D_11_64A    => fun _ => fct3_AD
  | AMOMINU_D_00_64A   => fun _ => fct3_AD
  | AMOMINU_D_01_64A   => fun _ => fct3_AD
  | AMOMINU_D_10_64A   => fun _ => fct3_AD
  | AMOMINU_D_11_64A   => fun _ => fct3_AD
  | AMOMAXU_D_00_64A   => fun _ => fct3_AD
  | AMOMAXU_D_01_64A   => fun _ => fct3_AD
  | AMOMAXU_D_10_64A   => fun _ => fct3_AD
  | AMOMAXU_D_11_64A   => fun _ => fct3_AD
  | FLW_32F            => fun _ => fct3_LSF
  | FSW_32F            => fun _ => fct3_LSF
  | FMADD_RNE_S_32F    => fun _ => fct3_RNE
  | FMADD_RTZ_S_32F    => fun _ => fct3_RTZ
  | FMADD_RDN_S_32F    => fun _ => fct3_RDN
  | FMADD_RUP_S_32F    => fun _ => fct3_RUP
  | FMADD_RMM_S_32F    => fun _ => fct3_RMM
  | FMADD_DYN_S_32F    => fun _ => fct3_DYN
  | FMSUB_RNE_S_32F    => fun _ => fct3_RNE
  | FMSUB_RTZ_S_32F    => fun _ => fct3_RTZ
  | FMSUB_RDN_S_32F    => fun _ => fct3_RDN
  | FMSUB_RUP_S_32F    => fun _ => fct3_RUP
  | FMSUB_RMM_S_32F    => fun _ => fct3_RMM
  | FMSUB_DYN_S_32F    => fun _ => fct3_DYN
  | FNMSUB_RNE_S_32F   => fun _ => fct3_RNE
  | FNMSUB_RTZ_S_32F   => fun _ => fct3_RTZ
  | FNMSUB_RDN_S_32F   => fun _ => fct3_RDN
  | FNMSUB_RUP_S_32F   => fun _ => fct3_RUP
  | FNMSUB_RMM_S_32F   => fun _ => fct3_RMM
  | FNMSUB_DYN_S_32F   => fun _ => fct3_DYN
  | FNMADD_RNE_S_32F   => fun _ => fct3_RNE
  | FNMADD_RTZ_S_32F   => fun _ => fct3_RTZ
  | FNMADD_RDN_S_32F   => fun _ => fct3_RDN
  | FNMADD_RUP_S_32F   => fun _ => fct3_RUP
  | FNMADD_RMM_S_32F   => fun _ => fct3_RMM
  | FNMADD_DYN_S_32F   => fun _ => fct3_DYN
  | FADD_RNE_S_32F     => fun _ => fct3_RNE
  | FADD_RTZ_S_32F     => fun _ => fct3_RTZ
  | FADD_RDN_S_32F     => fun _ => fct3_RDN
  | FADD_RUP_S_32F     => fun _ => fct3_RUP
  | FADD_RMM_S_32F     => fun _ => fct3_RMM
  | FADD_DYN_S_32F     => fun _ => fct3_DYN
  | FSUB_RNE_S_32F     => fun _ => fct3_RNE
  | FSUB_RTZ_S_32F     => fun _ => fct3_RTZ
  | FSUB_RDN_S_32F     => fun _ => fct3_RDN
  | FSUB_RUP_S_32F     => fun _ => fct3_RUP
  | FSUB_RMM_S_32F     => fun _ => fct3_RMM
  | FSUB_DYN_S_32F     => fun _ => fct3_DYN
  | FMUL_RNE_S_32F     => fun _ => fct3_RNE
  | FMUL_RTZ_S_32F     => fun _ => fct3_RTZ
  | FMUL_RDN_S_32F     => fun _ => fct3_RDN
  | FMUL_RUP_S_32F     => fun _ => fct3_RUP
  | FMUL_RMM_S_32F     => fun _ => fct3_RMM
  | FMUL_DYN_S_32F     => fun _ => fct3_DYN
  | FDIV_RNE_S_32F     => fun _ => fct3_RNE
  | FDIV_RTZ_S_32F     => fun _ => fct3_RTZ
  | FDIV_RDN_S_32F     => fun _ => fct3_RDN
  | FDIV_RUP_S_32F     => fun _ => fct3_RUP
  | FDIV_RMM_S_32F     => fun _ => fct3_RMM
  | FDIV_DYN_S_32F     => fun _ => fct3_DYN
  | FSQRT_RNE_S_32F    => fun _ => fct3_RNE
  | FSQRT_RTZ_S_32F    => fun _ => fct3_RTZ
  | FSQRT_RDN_S_32F    => fun _ => fct3_RDN
  | FSQRT_RUP_S_32F    => fun _ => fct3_RUP
  | FSQRT_RMM_S_32F    => fun _ => fct3_RMM
  | FSQRT_DYN_S_32F    => fun _ => fct3_DYN
  | FSGNJ_S_32F        => fun _ => fct3_FSGNJ
  | FSGNJN_S_32F       => fun _ => fct3_FSGNJN
  | FSGNJX_S_32F       => fun _ => fct3_FSGNJX
  | FMIN_S_32F         => fun _ => fct3_FMIN
  | FMAX_S_32F         => fun _ => fct3_FMAX
  | FCVT_RNE_W_S_32F   => fun _ => fct3_RNE
  | FCVT_RTZ_W_S_32F   => fun _ => fct3_RTZ
  | FCVT_RDN_W_S_32F   => fun _ => fct3_RDN
  | FCVT_RUP_W_S_32F   => fun _ => fct3_RUP
  | FCVT_RMM_W_S_32F   => fun _ => fct3_RMM
  | FCVT_DYN_W_S_32F   => fun _ => fct3_DYN
  | FCVT_RNE_WU_S_32F  => fun _ => fct3_RNE
  | FCVT_RTZ_WU_S_32F  => fun _ => fct3_RTZ
  | FCVT_RDN_WU_S_32F  => fun _ => fct3_RDN
  | FCVT_RUP_WU_S_32F  => fun _ => fct3_RUP
  | FCVT_RMM_WU_S_32F  => fun _ => fct3_RMM
  | FCVT_DYN_WU_S_32F  => fun _ => fct3_DYN
  | FMV_X_W_32F        => fun _ => fct3_FMV
  | FEQ_S_32F          => fun _ => fct3_FEQ
  | FLT_S_32F          => fun _ => fct3_FLT
  | FLE_S_32F          => fun _ => fct3_FLE
  | FCLASS_S_32F       => fun _ => fct3_FCLASS
  | FCVT_RNE_S_W_32F   => fun _ => fct3_RNE
  | FCVT_RTZ_S_W_32F   => fun _ => fct3_RTZ
  | FCVT_RDN_S_W_32F   => fun _ => fct3_RDN
  | FCVT_RUP_S_W_32F   => fun _ => fct3_RUP
  | FCVT_RMM_S_W_32F   => fun _ => fct3_RMM
  | FCVT_DYN_S_W_32F   => fun _ => fct3_DYN
  | FCVT_RNE_S_WU_32F  => fun _ => fct3_RNE
  | FCVT_RTZ_S_WU_32F  => fun _ => fct3_RTZ
  | FCVT_RDN_S_WU_32F  => fun _ => fct3_RDN
  | FCVT_RUP_S_WU_32F  => fun _ => fct3_RUP
  | FCVT_RMM_S_WU_32F  => fun _ => fct3_RMM
  | FCVT_DYN_S_WU_32F  => fun _ => fct3_DYN
  | FMV_W_X_32F        => fun _ => fct3_FMV
  | FLW_64F            => fun _ => fct3_LSF
  | FSW_64F            => fun _ => fct3_LSF
  | FMADD_RNE_S_64F    => fun _ => fct3_RNE
  | FMADD_RTZ_S_64F    => fun _ => fct3_RTZ
  | FMADD_RDN_S_64F    => fun _ => fct3_RDN
  | FMADD_RUP_S_64F    => fun _ => fct3_RUP
  | FMADD_RMM_S_64F    => fun _ => fct3_RMM
  | FMADD_DYN_S_64F    => fun _ => fct3_DYN
  | FMSUB_RNE_S_64F    => fun _ => fct3_RNE
  | FMSUB_RTZ_S_64F    => fun _ => fct3_RTZ
  | FMSUB_RDN_S_64F    => fun _ => fct3_RDN
  | FMSUB_RUP_S_64F    => fun _ => fct3_RUP
  | FMSUB_RMM_S_64F    => fun _ => fct3_RMM
  | FMSUB_DYN_S_64F    => fun _ => fct3_DYN
  | FNMSUB_RNE_S_64F   => fun _ => fct3_RNE
  | FNMSUB_RTZ_S_64F   => fun _ => fct3_RTZ
  | FNMSUB_RDN_S_64F   => fun _ => fct3_RDN
  | FNMSUB_RUP_S_64F   => fun _ => fct3_RUP
  | FNMSUB_RMM_S_64F   => fun _ => fct3_RMM
  | FNMSUB_DYN_S_64F   => fun _ => fct3_DYN
  | FNMADD_RNE_S_64F   => fun _ => fct3_RNE
  | FNMADD_RTZ_S_64F   => fun _ => fct3_RTZ
  | FNMADD_RDN_S_64F   => fun _ => fct3_RDN
  | FNMADD_RUP_S_64F   => fun _ => fct3_RUP
  | FNMADD_RMM_S_64F   => fun _ => fct3_RMM
  | FNMADD_DYN_S_64F   => fun _ => fct3_DYN
  | FADD_RNE_S_64F     => fun _ => fct3_RNE
  | FADD_RTZ_S_64F     => fun _ => fct3_RTZ
  | FADD_RDN_S_64F     => fun _ => fct3_RDN
  | FADD_RUP_S_64F     => fun _ => fct3_RUP
  | FADD_RMM_S_64F     => fun _ => fct3_RMM
  | FADD_DYN_S_64F     => fun _ => fct3_DYN
  | FSUB_RNE_S_64F     => fun _ => fct3_RNE
  | FSUB_RTZ_S_64F     => fun _ => fct3_RTZ
  | FSUB_RDN_S_64F     => fun _ => fct3_RDN
  | FSUB_RUP_S_64F     => fun _ => fct3_RUP
  | FSUB_RMM_S_64F     => fun _ => fct3_RMM
  | FSUB_DYN_S_64F     => fun _ => fct3_DYN
  | FMUL_RNE_S_64F     => fun _ => fct3_RNE
  | FMUL_RTZ_S_64F     => fun _ => fct3_RTZ
  | FMUL_RDN_S_64F     => fun _ => fct3_RDN
  | FMUL_RUP_S_64F     => fun _ => fct3_RUP
  | FMUL_RMM_S_64F     => fun _ => fct3_RMM
  | FMUL_DYN_S_64F     => fun _ => fct3_DYN
  | FDIV_RNE_S_64F     => fun _ => fct3_RNE
  | FDIV_RTZ_S_64F     => fun _ => fct3_RTZ
  | FDIV_RDN_S_64F     => fun _ => fct3_RDN
  | FDIV_RUP_S_64F     => fun _ => fct3_RUP
  | FDIV_RMM_S_64F     => fun _ => fct3_RMM
  | FDIV_DYN_S_64F     => fun _ => fct3_DYN
  | FSQRT_RNE_S_64F    => fun _ => fct3_RNE
  | FSQRT_RTZ_S_64F    => fun _ => fct3_RTZ
  | FSQRT_RDN_S_64F    => fun _ => fct3_RDN
  | FSQRT_RUP_S_64F    => fun _ => fct3_RUP
  | FSQRT_RMM_S_64F    => fun _ => fct3_RMM
  | FSQRT_DYN_S_64F    => fun _ => fct3_DYN
  | FSGNJ_S_64F        => fun _ => fct3_FSGNJ
  | FSGNJN_S_64F       => fun _ => fct3_FSGNJN
  | FSGNJX_S_64F       => fun _ => fct3_FSGNJX
  | FMIN_S_64F         => fun _ => fct3_FMIN
  | FMAX_S_64F         => fun _ => fct3_FMAX
  | FCVT_RNE_W_S_64F   => fun _ => fct3_RNE
  | FCVT_RTZ_W_S_64F   => fun _ => fct3_RTZ
  | FCVT_RDN_W_S_64F   => fun _ => fct3_RDN
  | FCVT_RUP_W_S_64F   => fun _ => fct3_RUP
  | FCVT_RMM_W_S_64F   => fun _ => fct3_RMM
  | FCVT_DYN_W_S_64F   => fun _ => fct3_DYN
  | FCVT_RNE_WU_S_64F  => fun _ => fct3_RNE
  | FCVT_RTZ_WU_S_64F  => fun _ => fct3_RTZ
  | FCVT_RDN_WU_S_64F  => fun _ => fct3_RDN
  | FCVT_RUP_WU_S_64F  => fun _ => fct3_RUP
  | FCVT_RMM_WU_S_64F  => fun _ => fct3_RMM
  | FCVT_DYN_WU_S_64F  => fun _ => fct3_DYN
  | FMV_X_W_64F        => fun _ => fct3_FMV
  | FEQ_S_64F          => fun _ => fct3_FEQ
  | FLT_S_64F          => fun _ => fct3_FLT
  | FLE_S_64F          => fun _ => fct3_FLE
  | FCLASS_S_64F       => fun _ => fct3_FCLASS
  | FCVT_RNE_S_W_64F   => fun _ => fct3_RNE
  | FCVT_RTZ_S_W_64F   => fun _ => fct3_RTZ
  | FCVT_RDN_S_W_64F   => fun _ => fct3_RDN
  | FCVT_RUP_S_W_64F   => fun _ => fct3_RUP
  | FCVT_RMM_S_W_64F   => fun _ => fct3_RMM
  | FCVT_DYN_S_W_64F   => fun _ => fct3_DYN
  | FCVT_RNE_S_WU_64F  => fun _ => fct3_RNE
  | FCVT_RTZ_S_WU_64F  => fun _ => fct3_RTZ
  | FCVT_RDN_S_WU_64F  => fun _ => fct3_RDN
  | FCVT_RUP_S_WU_64F  => fun _ => fct3_RUP
  | FCVT_RMM_S_WU_64F  => fun _ => fct3_RMM
  | FCVT_DYN_S_WU_64F  => fun _ => fct3_DYN
  | FMV_W_X_64F        => fun _ => fct3_FMV
  | FCVT_RNE_L_S_64F   => fun _ => fct3_RNE
  | FCVT_RTZ_L_S_64F   => fun _ => fct3_RTZ
  | FCVT_RDN_L_S_64F   => fun _ => fct3_RDN
  | FCVT_RUP_L_S_64F   => fun _ => fct3_RUP
  | FCVT_RMM_L_S_64F   => fun _ => fct3_RMM
  | FCVT_DYN_L_S_64F   => fun _ => fct3_DYN
  | FCVT_RNE_LU_S_64F  => fun _ => fct3_RNE
  | FCVT_RTZ_LU_S_64F  => fun _ => fct3_RTZ
  | FCVT_RDN_LU_S_64F  => fun _ => fct3_RDN
  | FCVT_RUP_LU_S_64F  => fun _ => fct3_RUP
  | FCVT_RMM_LU_S_64F  => fun _ => fct3_RMM
  | FCVT_DYN_LU_S_64F  => fun _ => fct3_DYN
  | FCVT_RNE_S_L_64F   => fun _ => fct3_RNE
  | FCVT_RTZ_S_L_64F   => fun _ => fct3_RTZ
  | FCVT_RDN_S_L_64F   => fun _ => fct3_RDN
  | FCVT_RUP_S_L_64F   => fun _ => fct3_RUP
  | FCVT_RMM_S_L_64F   => fun _ => fct3_RMM
  | FCVT_DYN_S_L_64F   => fun _ => fct3_DYN
  | FCVT_RNE_S_LU_64F  => fun _ => fct3_RNE
  | FCVT_RTZ_S_LU_64F  => fun _ => fct3_RTZ
  | FCVT_RDN_S_LU_64F  => fun _ => fct3_RDN
  | FCVT_RUP_S_LU_64F  => fun _ => fct3_RUP
  | FCVT_RMM_S_LU_64F  => fun _ => fct3_RMM
  | FCVT_DYN_S_LU_64F  => fun _ => fct3_DYN
  | FLD_32D            => fun _ => fct3_LSD
  | FSD_32D            => fun _ => fct3_LSD
  | FMADD_RNE_D_32D    => fun _ => fct3_RNE
  | FMADD_RTZ_D_32D    => fun _ => fct3_RTZ
  | FMADD_RDN_D_32D    => fun _ => fct3_RDN
  | FMADD_RUP_D_32D    => fun _ => fct3_RUP
  | FMADD_RMM_D_32D    => fun _ => fct3_RMM
  | FMADD_DYN_D_32D    => fun _ => fct3_DYN
  | FMSUB_RNE_D_32D    => fun _ => fct3_RNE
  | FMSUB_RTZ_D_32D    => fun _ => fct3_RTZ
  | FMSUB_RDN_D_32D    => fun _ => fct3_RDN
  | FMSUB_RUP_D_32D    => fun _ => fct3_RUP
  | FMSUB_RMM_D_32D    => fun _ => fct3_RMM
  | FMSUB_DYN_D_32D    => fun _ => fct3_DYN
  | FNMSUB_RNE_D_32D   => fun _ => fct3_RNE
  | FNMSUB_RTZ_D_32D   => fun _ => fct3_RTZ
  | FNMSUB_RDN_D_32D   => fun _ => fct3_RDN
  | FNMSUB_RUP_D_32D   => fun _ => fct3_RUP
  | FNMSUB_RMM_D_32D   => fun _ => fct3_RMM
  | FNMSUB_DYN_D_32D   => fun _ => fct3_DYN
  | FNMADD_RNE_D_32D   => fun _ => fct3_RNE
  | FNMADD_RTZ_D_32D   => fun _ => fct3_RTZ
  | FNMADD_RDN_D_32D   => fun _ => fct3_RDN
  | FNMADD_RUP_D_32D   => fun _ => fct3_RUP
  | FNMADD_RMM_D_32D   => fun _ => fct3_RMM
  | FNMADD_DYN_D_32D   => fun _ => fct3_DYN
  | FADD_RNE_D_32D     => fun _ => fct3_RNE
  | FADD_RTZ_D_32D     => fun _ => fct3_RTZ
  | FADD_RDN_D_32D     => fun _ => fct3_RDN
  | FADD_RUP_D_32D     => fun _ => fct3_RUP
  | FADD_RMM_D_32D     => fun _ => fct3_RMM
  | FADD_DYN_D_32D     => fun _ => fct3_DYN
  | FSUB_RNE_D_32D     => fun _ => fct3_RNE
  | FSUB_RTZ_D_32D     => fun _ => fct3_RTZ
  | FSUB_RDN_D_32D     => fun _ => fct3_RDN
  | FSUB_RUP_D_32D     => fun _ => fct3_RUP
  | FSUB_RMM_D_32D     => fun _ => fct3_RMM
  | FSUB_DYN_D_32D     => fun _ => fct3_DYN
  | FMUL_RNE_D_32D     => fun _ => fct3_RNE
  | FMUL_RTZ_D_32D     => fun _ => fct3_RTZ
  | FMUL_RDN_D_32D     => fun _ => fct3_RDN
  | FMUL_RUP_D_32D     => fun _ => fct3_RUP
  | FMUL_RMM_D_32D     => fun _ => fct3_RMM
  | FMUL_DYN_D_32D     => fun _ => fct3_DYN
  | FDIV_RNE_D_32D     => fun _ => fct3_RNE
  | FDIV_RTZ_D_32D     => fun _ => fct3_RTZ
  | FDIV_RDN_D_32D     => fun _ => fct3_RDN
  | FDIV_RUP_D_32D     => fun _ => fct3_RUP
  | FDIV_RMM_D_32D     => fun _ => fct3_RMM
  | FDIV_DYN_D_32D     => fun _ => fct3_DYN
  | FSQRT_RNE_D_32D    => fun _ => fct3_RNE
  | FSQRT_RTZ_D_32D    => fun _ => fct3_RTZ
  | FSQRT_RDN_D_32D    => fun _ => fct3_RDN
  | FSQRT_RUP_D_32D    => fun _ => fct3_RUP
  | FSQRT_RMM_D_32D    => fun _ => fct3_RMM
  | FSQRT_DYN_D_32D    => fun _ => fct3_DYN
  | FSGNJ_D_32D        => fun _ => fct3_FSGNJ
  | FSGNJN_D_32D       => fun _ => fct3_FSGNJN
  | FSGNJX_D_32D       => fun _ => fct3_FSGNJX
  | FMIN_D_32D         => fun _ => fct3_FMIN
  | FMAX_D_32D         => fun _ => fct3_FMAX
  | FCVT_RNE_S_D_32D   => fun _ => fct3_RNE
  | FCVT_RTZ_S_D_32D   => fun _ => fct3_RTZ
  | FCVT_RDN_S_D_32D   => fun _ => fct3_RDN
  | FCVT_RUP_S_D_32D   => fun _ => fct3_RUP
  | FCVT_RMM_S_D_32D   => fun _ => fct3_RMM
  | FCVT_DYN_S_D_32D   => fun _ => fct3_DYN
  | FCVT_RNE_D_S_32D   => fun _ => fct3_RNE
  | FCVT_RTZ_D_S_32D   => fun _ => fct3_RTZ
  | FCVT_RDN_D_S_32D   => fun _ => fct3_RDN
  | FCVT_RUP_D_S_32D   => fun _ => fct3_RUP
  | FCVT_RMM_D_S_32D   => fun _ => fct3_RMM
  | FCVT_DYN_D_S_32D   => fun _ => fct3_DYN
  | FEQ_D_32D          => fun _ => fct3_FEQ
  | FLT_D_32D          => fun _ => fct3_FLT
  | FLE_D_32D          => fun _ => fct3_FLE
  | FCLASS_D_32D       => fun _ => fct3_FCLASS
  | FCVT_RNE_W_D_32D   => fun _ => fct3_RNE
  | FCVT_RTZ_W_D_32D   => fun _ => fct3_RTZ
  | FCVT_RDN_W_D_32D   => fun _ => fct3_RDN
  | FCVT_RUP_W_D_32D   => fun _ => fct3_RUP
  | FCVT_RMM_W_D_32D   => fun _ => fct3_RMM
  | FCVT_DYN_W_D_32D   => fun _ => fct3_DYN
  | FCVT_RNE_WU_D_32D  => fun _ => fct3_RNE
  | FCVT_RTZ_WU_D_32D  => fun _ => fct3_RTZ
  | FCVT_RDN_WU_D_32D  => fun _ => fct3_RDN
  | FCVT_RUP_WU_D_32D  => fun _ => fct3_RUP
  | FCVT_RMM_WU_D_32D  => fun _ => fct3_RMM
  | FCVT_DYN_WU_D_32D  => fun _ => fct3_DYN
  | FCVT_RNE_D_W_32D   => fun _ => fct3_RNE
  | FCVT_RTZ_D_W_32D   => fun _ => fct3_RTZ
  | FCVT_RDN_D_W_32D   => fun _ => fct3_RDN
  | FCVT_RUP_D_W_32D   => fun _ => fct3_RUP
  | FCVT_RMM_D_W_32D   => fun _ => fct3_RMM
  | FCVT_DYN_D_W_32D   => fun _ => fct3_DYN
  | FCVT_RNE_D_WU_32D  => fun _ => fct3_RNE
  | FCVT_RTZ_D_WU_32D  => fun _ => fct3_RTZ
  | FCVT_RDN_D_WU_32D  => fun _ => fct3_RDN
  | FCVT_RUP_D_WU_32D  => fun _ => fct3_RUP
  | FCVT_RMM_D_WU_32D  => fun _ => fct3_RMM
  | FCVT_DYN_D_WU_32D  => fun _ => fct3_DYN
  | FLD_64D            => fun _ => fct3_LSD
  | FSD_64D            => fun _ => fct3_LSD
  | FMADD_RNE_D_64D    => fun _ => fct3_RNE
  | FMADD_RTZ_D_64D    => fun _ => fct3_RTZ
  | FMADD_RDN_D_64D    => fun _ => fct3_RDN
  | FMADD_RUP_D_64D    => fun _ => fct3_RUP
  | FMADD_RMM_D_64D    => fun _ => fct3_RMM
  | FMADD_DYN_D_64D    => fun _ => fct3_DYN
  | FMSUB_RNE_D_64D    => fun _ => fct3_RNE
  | FMSUB_RTZ_D_64D    => fun _ => fct3_RTZ
  | FMSUB_RDN_D_64D    => fun _ => fct3_RDN
  | FMSUB_RUP_D_64D    => fun _ => fct3_RUP
  | FMSUB_RMM_D_64D    => fun _ => fct3_RMM
  | FMSUB_DYN_D_64D    => fun _ => fct3_DYN
  | FNMSUB_RNE_D_64D   => fun _ => fct3_RNE
  | FNMSUB_RTZ_D_64D   => fun _ => fct3_RTZ
  | FNMSUB_RDN_D_64D   => fun _ => fct3_RDN
  | FNMSUB_RUP_D_64D   => fun _ => fct3_RUP
  | FNMSUB_RMM_D_64D   => fun _ => fct3_RMM
  | FNMSUB_DYN_D_64D   => fun _ => fct3_DYN
  | FNMADD_RNE_D_64D   => fun _ => fct3_RNE
  | FNMADD_RTZ_D_64D   => fun _ => fct3_RTZ
  | FNMADD_RDN_D_64D   => fun _ => fct3_RDN
  | FNMADD_RUP_D_64D   => fun _ => fct3_RUP
  | FNMADD_RMM_D_64D   => fun _ => fct3_RMM
  | FNMADD_DYN_D_64D   => fun _ => fct3_DYN
  | FADD_RNE_D_64D     => fun _ => fct3_RNE
  | FADD_RTZ_D_64D     => fun _ => fct3_RTZ
  | FADD_RDN_D_64D     => fun _ => fct3_RDN
  | FADD_RUP_D_64D     => fun _ => fct3_RUP
  | FADD_RMM_D_64D     => fun _ => fct3_RMM
  | FADD_DYN_D_64D     => fun _ => fct3_DYN
  | FSUB_RNE_D_64D     => fun _ => fct3_RNE
  | FSUB_RTZ_D_64D     => fun _ => fct3_RTZ
  | FSUB_RDN_D_64D     => fun _ => fct3_RDN
  | FSUB_RUP_D_64D     => fun _ => fct3_RUP
  | FSUB_RMM_D_64D     => fun _ => fct3_RMM
  | FSUB_DYN_D_64D     => fun _ => fct3_DYN
  | FMUL_RNE_D_64D     => fun _ => fct3_RNE
  | FMUL_RTZ_D_64D     => fun _ => fct3_RTZ
  | FMUL_RDN_D_64D     => fun _ => fct3_RDN
  | FMUL_RUP_D_64D     => fun _ => fct3_RUP
  | FMUL_RMM_D_64D     => fun _ => fct3_RMM
  | FMUL_DYN_D_64D     => fun _ => fct3_DYN
  | FDIV_RNE_D_64D     => fun _ => fct3_RNE
  | FDIV_RTZ_D_64D     => fun _ => fct3_RTZ
  | FDIV_RDN_D_64D     => fun _ => fct3_RDN
  | FDIV_RUP_D_64D     => fun _ => fct3_RUP
  | FDIV_RMM_D_64D     => fun _ => fct3_RMM
  | FDIV_DYN_D_64D     => fun _ => fct3_DYN
  | FSQRT_RNE_D_64D    => fun _ => fct3_RNE
  | FSQRT_RTZ_D_64D    => fun _ => fct3_RTZ
  | FSQRT_RDN_D_64D    => fun _ => fct3_RDN
  | FSQRT_RUP_D_64D    => fun _ => fct3_RUP
  | FSQRT_RMM_D_64D    => fun _ => fct3_RMM
  | FSQRT_DYN_D_64D    => fun _ => fct3_DYN
  | FSGNJ_D_64D        => fun _ => fct3_FSGNJ
  | FSGNJN_D_64D       => fun _ => fct3_FSGNJN
  | FSGNJX_D_64D       => fun _ => fct3_FSGNJX
  | FMIN_D_64D         => fun _ => fct3_FMIN
  | FMAX_D_64D         => fun _ => fct3_FMAX
  | FCVT_RNE_S_D_64D   => fun _ => fct3_RNE
  | FCVT_RTZ_S_D_64D   => fun _ => fct3_RTZ
  | FCVT_RDN_S_D_64D   => fun _ => fct3_RDN
  | FCVT_RUP_S_D_64D   => fun _ => fct3_RUP
  | FCVT_RMM_S_D_64D   => fun _ => fct3_RMM
  | FCVT_DYN_S_D_64D   => fun _ => fct3_DYN
  | FCVT_RNE_D_S_64D   => fun _ => fct3_RNE
  | FCVT_RTZ_D_S_64D   => fun _ => fct3_RTZ
  | FCVT_RDN_D_S_64D   => fun _ => fct3_RDN
  | FCVT_RUP_D_S_64D   => fun _ => fct3_RUP
  | FCVT_RMM_D_S_64D   => fun _ => fct3_RMM
  | FCVT_DYN_D_S_64D   => fun _ => fct3_DYN
  | FEQ_D_64D          => fun _ => fct3_FEQ
  | FLT_D_64D          => fun _ => fct3_FLT
  | FLE_D_64D          => fun _ => fct3_FLE
  | FCLASS_D_64D       => fun _ => fct3_FCLASS
  | FCVT_RNE_W_D_64D   => fun _ => fct3_RNE
  | FCVT_RTZ_W_D_64D   => fun _ => fct3_RTZ
  | FCVT_RDN_W_D_64D   => fun _ => fct3_RDN
  | FCVT_RUP_W_D_64D   => fun _ => fct3_RUP
  | FCVT_RMM_W_D_64D   => fun _ => fct3_RMM
  | FCVT_DYN_W_D_64D   => fun _ => fct3_DYN
  | FCVT_RNE_WU_D_64D  => fun _ => fct3_RNE
  | FCVT_RTZ_WU_D_64D  => fun _ => fct3_RTZ
  | FCVT_RDN_WU_D_64D  => fun _ => fct3_RDN
  | FCVT_RUP_WU_D_64D  => fun _ => fct3_RUP
  | FCVT_RMM_WU_D_64D  => fun _ => fct3_RMM
  | FCVT_DYN_WU_D_64D  => fun _ => fct3_DYN
  | FCVT_RNE_D_W_64D   => fun _ => fct3_RNE
  | FCVT_RTZ_D_W_64D   => fun _ => fct3_RTZ
  | FCVT_RDN_D_W_64D   => fun _ => fct3_RDN
  | FCVT_RUP_D_W_64D   => fun _ => fct3_RUP
  | FCVT_RMM_D_W_64D   => fun _ => fct3_RMM
  | FCVT_DYN_D_W_64D   => fun _ => fct3_DYN
  | FCVT_RNE_D_WU_64D  => fun _ => fct3_RNE
  | FCVT_RTZ_D_WU_64D  => fun _ => fct3_RTZ
  | FCVT_RDN_D_WU_64D  => fun _ => fct3_RDN
  | FCVT_RUP_D_WU_64D  => fun _ => fct3_RUP
  | FCVT_RMM_D_WU_64D  => fun _ => fct3_RMM
  | FCVT_DYN_D_WU_64D  => fun _ => fct3_DYN
  | FCVT_RNE_L_D_64D   => fun _ => fct3_RNE
  | FCVT_RTZ_L_D_64D   => fun _ => fct3_RTZ
  | FCVT_RDN_L_D_64D   => fun _ => fct3_RDN
  | FCVT_RUP_L_D_64D   => fun _ => fct3_RUP
  | FCVT_RMM_L_D_64D   => fun _ => fct3_RMM
  | FCVT_DYN_L_D_64D   => fun _ => fct3_DYN
  | FCVT_RNE_LU_D_64D  => fun _ => fct3_RNE
  | FCVT_RTZ_LU_D_64D  => fun _ => fct3_RTZ
  | FCVT_RDN_LU_D_64D  => fun _ => fct3_RDN
  | FCVT_RUP_LU_D_64D  => fun _ => fct3_RUP
  | FCVT_RMM_LU_D_64D  => fun _ => fct3_RMM
  | FCVT_DYN_LU_D_64D  => fun _ => fct3_DYN
  | FMV_X_D_64D        => fun _ => fct3_FMV
  | FCVT_RNE_D_L_64D   => fun _ => fct3_RNE
  | FCVT_RTZ_D_L_64D   => fun _ => fct3_RTZ
  | FCVT_RDN_D_L_64D   => fun _ => fct3_RDN
  | FCVT_RUP_D_L_64D   => fun _ => fct3_RUP
  | FCVT_RMM_D_L_64D   => fun _ => fct3_RMM
  | FCVT_DYN_D_L_64D   => fun _ => fct3_DYN
  | FCVT_RNE_D_LU_64D  => fun _ => fct3_RNE
  | FCVT_RTZ_D_LU_64D  => fun _ => fct3_RTZ
  | FCVT_RDN_D_LU_64D  => fun _ => fct3_RDN
  | FCVT_RUP_D_LU_64D  => fun _ => fct3_RUP
  | FCVT_RMM_D_LU_64D  => fun _ => fct3_RMM
  | FCVT_DYN_D_LU_64D  => fun _ => fct3_DYN
  | FMV_D_X_64D        => fun _ => fct3_FMV
  | FLQ_32Q            => fun _ => fct3_LSQ
  | FSQ_32Q            => fun _ => fct3_LSQ
  | FMADD_RNE_Q_32Q    => fun _ => fct3_RNE
  | FMADD_RTZ_Q_32Q    => fun _ => fct3_RTZ
  | FMADD_RDN_Q_32Q    => fun _ => fct3_RDN
  | FMADD_RUP_Q_32Q    => fun _ => fct3_RUP
  | FMADD_RMM_Q_32Q    => fun _ => fct3_RMM
  | FMADD_DYN_Q_32Q    => fun _ => fct3_DYN
  | FMSUB_RNE_Q_32Q    => fun _ => fct3_RNE
  | FMSUB_RTZ_Q_32Q    => fun _ => fct3_RTZ
  | FMSUB_RDN_Q_32Q    => fun _ => fct3_RDN
  | FMSUB_RUP_Q_32Q    => fun _ => fct3_RUP
  | FMSUB_RMM_Q_32Q    => fun _ => fct3_RMM
  | FMSUB_DYN_Q_32Q    => fun _ => fct3_DYN
  | FNMSUB_RNE_Q_32Q   => fun _ => fct3_RNE
  | FNMSUB_RTZ_Q_32Q   => fun _ => fct3_RTZ
  | FNMSUB_RDN_Q_32Q   => fun _ => fct3_RDN
  | FNMSUB_RUP_Q_32Q   => fun _ => fct3_RUP
  | FNMSUB_RMM_Q_32Q   => fun _ => fct3_RMM
  | FNMSUB_DYN_Q_32Q   => fun _ => fct3_DYN
  | FNMADD_RNE_Q_32Q   => fun _ => fct3_RNE
  | FNMADD_RTZ_Q_32Q   => fun _ => fct3_RTZ
  | FNMADD_RDN_Q_32Q   => fun _ => fct3_RDN
  | FNMADD_RUP_Q_32Q   => fun _ => fct3_RUP
  | FNMADD_RMM_Q_32Q   => fun _ => fct3_RMM
  | FNMADD_DYN_Q_32Q   => fun _ => fct3_DYN
  | FADD_RNE_Q_32Q     => fun _ => fct3_RNE
  | FADD_RTZ_Q_32Q     => fun _ => fct3_RTZ
  | FADD_RDN_Q_32Q     => fun _ => fct3_RDN
  | FADD_RUP_Q_32Q     => fun _ => fct3_RUP
  | FADD_RMM_Q_32Q     => fun _ => fct3_RMM
  | FADD_DYN_Q_32Q     => fun _ => fct3_DYN
  | FSUB_RNE_Q_32Q     => fun _ => fct3_RNE
  | FSUB_RTZ_Q_32Q     => fun _ => fct3_RTZ
  | FSUB_RDN_Q_32Q     => fun _ => fct3_RDN
  | FSUB_RUP_Q_32Q     => fun _ => fct3_RUP
  | FSUB_RMM_Q_32Q     => fun _ => fct3_RMM
  | FSUB_DYN_Q_32Q     => fun _ => fct3_DYN
  | FMUL_RNE_Q_32Q     => fun _ => fct3_RNE
  | FMUL_RTZ_Q_32Q     => fun _ => fct3_RTZ
  | FMUL_RDN_Q_32Q     => fun _ => fct3_RDN
  | FMUL_RUP_Q_32Q     => fun _ => fct3_RUP
  | FMUL_RMM_Q_32Q     => fun _ => fct3_RMM
  | FMUL_DYN_Q_32Q     => fun _ => fct3_DYN
  | FDIV_RNE_Q_32Q     => fun _ => fct3_RNE
  | FDIV_RTZ_Q_32Q     => fun _ => fct3_RTZ
  | FDIV_RDN_Q_32Q     => fun _ => fct3_RDN
  | FDIV_RUP_Q_32Q     => fun _ => fct3_RUP
  | FDIV_RMM_Q_32Q     => fun _ => fct3_RMM
  | FDIV_DYN_Q_32Q     => fun _ => fct3_DYN
  | FSQRT_RNE_Q_32Q    => fun _ => fct3_RNE
  | FSQRT_RTZ_Q_32Q    => fun _ => fct3_RTZ
  | FSQRT_RDN_Q_32Q    => fun _ => fct3_RDN
  | FSQRT_RUP_Q_32Q    => fun _ => fct3_RUP
  | FSQRT_RMM_Q_32Q    => fun _ => fct3_RMM
  | FSQRT_DYN_Q_32Q    => fun _ => fct3_DYN
  | FSGNJ_Q_32Q        => fun _ => fct3_FSGNJ
  | FSGNJN_Q_32Q       => fun _ => fct3_FSGNJN
  | FSGNJX_Q_32Q       => fun _ => fct3_FSGNJX
  | FMIN_Q_32Q         => fun _ => fct3_FMIN
  | FMAX_Q_32Q         => fun _ => fct3_FMAX
  | FCVT_RNE_S_Q_32Q   => fun _ => fct3_RNE
  | FCVT_RTZ_S_Q_32Q   => fun _ => fct3_RTZ
  | FCVT_RDN_S_Q_32Q   => fun _ => fct3_RDN
  | FCVT_RUP_S_Q_32Q   => fun _ => fct3_RUP
  | FCVT_RMM_S_Q_32Q   => fun _ => fct3_RMM
  | FCVT_DYN_S_Q_32Q   => fun _ => fct3_DYN
  | FCVT_RNE_Q_S_32Q   => fun _ => fct3_RNE
  | FCVT_RTZ_Q_S_32Q   => fun _ => fct3_RTZ
  | FCVT_RDN_Q_S_32Q   => fun _ => fct3_RDN
  | FCVT_RUP_Q_S_32Q   => fun _ => fct3_RUP
  | FCVT_RMM_Q_S_32Q   => fun _ => fct3_RMM
  | FCVT_DYN_Q_S_32Q   => fun _ => fct3_DYN
  | FCVT_RNE_D_Q_32Q   => fun _ => fct3_RNE
  | FCVT_RTZ_D_Q_32Q   => fun _ => fct3_RTZ
  | FCVT_RDN_D_Q_32Q   => fun _ => fct3_RDN
  | FCVT_RUP_D_Q_32Q   => fun _ => fct3_RUP
  | FCVT_RMM_D_Q_32Q   => fun _ => fct3_RMM
  | FCVT_DYN_D_Q_32Q   => fun _ => fct3_DYN
  | FCVT_RNE_Q_D_32Q   => fun _ => fct3_RNE
  | FCVT_RTZ_Q_D_32Q   => fun _ => fct3_RTZ
  | FCVT_RDN_Q_D_32Q   => fun _ => fct3_RDN
  | FCVT_RUP_Q_D_32Q   => fun _ => fct3_RUP
  | FCVT_RMM_Q_D_32Q   => fun _ => fct3_RMM
  | FCVT_DYN_Q_D_32Q   => fun _ => fct3_DYN
  | FEQ_Q_32Q          => fun _ => fct3_FEQ
  | FLT_Q_32Q          => fun _ => fct3_FLT
  | FLE_Q_32Q          => fun _ => fct3_FLE
  | FCLASS_Q_32Q       => fun _ => fct3_FCLASS
  | FCVT_RNE_W_Q_32Q   => fun _ => fct3_RNE
  | FCVT_RTZ_W_Q_32Q   => fun _ => fct3_RTZ
  | FCVT_RDN_W_Q_32Q   => fun _ => fct3_RDN
  | FCVT_RUP_W_Q_32Q   => fun _ => fct3_RUP
  | FCVT_RMM_W_Q_32Q   => fun _ => fct3_RMM
  | FCVT_DYN_W_Q_32Q   => fun _ => fct3_DYN
  | FCVT_RNE_WU_Q_32Q  => fun _ => fct3_RNE
  | FCVT_RTZ_WU_Q_32Q  => fun _ => fct3_RTZ
  | FCVT_RDN_WU_Q_32Q  => fun _ => fct3_RDN
  | FCVT_RUP_WU_Q_32Q  => fun _ => fct3_RUP
  | FCVT_RMM_WU_Q_32Q  => fun _ => fct3_RMM
  | FCVT_DYN_WU_Q_32Q  => fun _ => fct3_DYN
  | FCVT_RNE_Q_W_32Q   => fun _ => fct3_RNE
  | FCVT_RTZ_Q_W_32Q   => fun _ => fct3_RTZ
  | FCVT_RDN_Q_W_32Q   => fun _ => fct3_RDN
  | FCVT_RUP_Q_W_32Q   => fun _ => fct3_RUP
  | FCVT_RMM_Q_W_32Q   => fun _ => fct3_RMM
  | FCVT_DYN_Q_W_32Q   => fun _ => fct3_DYN
  | FCVT_RNE_Q_WU_32Q  => fun _ => fct3_RNE
  | FCVT_RTZ_Q_WU_32Q  => fun _ => fct3_RTZ
  | FCVT_RDN_Q_WU_32Q  => fun _ => fct3_RDN
  | FCVT_RUP_Q_WU_32Q  => fun _ => fct3_RUP
  | FCVT_RMM_Q_WU_32Q  => fun _ => fct3_RMM
  | FCVT_DYN_Q_WU_32Q  => fun _ => fct3_DYN
  | FLQ_64Q            => fun _ => fct3_LSQ
  | FSQ_64Q            => fun _ => fct3_LSQ
  | FMADD_RNE_Q_64Q    => fun _ => fct3_RNE
  | FMADD_RTZ_Q_64Q    => fun _ => fct3_RTZ
  | FMADD_RDN_Q_64Q    => fun _ => fct3_RDN
  | FMADD_RUP_Q_64Q    => fun _ => fct3_RUP
  | FMADD_RMM_Q_64Q    => fun _ => fct3_RMM
  | FMADD_DYN_Q_64Q    => fun _ => fct3_DYN
  | FMSUB_RNE_Q_64Q    => fun _ => fct3_RNE
  | FMSUB_RTZ_Q_64Q    => fun _ => fct3_RTZ
  | FMSUB_RDN_Q_64Q    => fun _ => fct3_RDN
  | FMSUB_RUP_Q_64Q    => fun _ => fct3_RUP
  | FMSUB_RMM_Q_64Q    => fun _ => fct3_RMM
  | FMSUB_DYN_Q_64Q    => fun _ => fct3_DYN
  | FNMSUB_RNE_Q_64Q   => fun _ => fct3_RNE
  | FNMSUB_RTZ_Q_64Q   => fun _ => fct3_RTZ
  | FNMSUB_RDN_Q_64Q   => fun _ => fct3_RDN
  | FNMSUB_RUP_Q_64Q   => fun _ => fct3_RUP
  | FNMSUB_RMM_Q_64Q   => fun _ => fct3_RMM
  | FNMSUB_DYN_Q_64Q   => fun _ => fct3_DYN
  | FNMADD_RNE_Q_64Q   => fun _ => fct3_RNE
  | FNMADD_RTZ_Q_64Q   => fun _ => fct3_RTZ
  | FNMADD_RDN_Q_64Q   => fun _ => fct3_RDN
  | FNMADD_RUP_Q_64Q   => fun _ => fct3_RUP
  | FNMADD_RMM_Q_64Q   => fun _ => fct3_RMM
  | FNMADD_DYN_Q_64Q   => fun _ => fct3_DYN
  | FADD_RNE_Q_64Q     => fun _ => fct3_RNE
  | FADD_RTZ_Q_64Q     => fun _ => fct3_RTZ
  | FADD_RDN_Q_64Q     => fun _ => fct3_RDN
  | FADD_RUP_Q_64Q     => fun _ => fct3_RUP
  | FADD_RMM_Q_64Q     => fun _ => fct3_RMM
  | FADD_DYN_Q_64Q     => fun _ => fct3_DYN
  | FSUB_RNE_Q_64Q     => fun _ => fct3_RNE
  | FSUB_RTZ_Q_64Q     => fun _ => fct3_RTZ
  | FSUB_RDN_Q_64Q     => fun _ => fct3_RDN
  | FSUB_RUP_Q_64Q     => fun _ => fct3_RUP
  | FSUB_RMM_Q_64Q     => fun _ => fct3_RMM
  | FSUB_DYN_Q_64Q     => fun _ => fct3_DYN
  | FMUL_RNE_Q_64Q     => fun _ => fct3_RNE
  | FMUL_RTZ_Q_64Q     => fun _ => fct3_RTZ
  | FMUL_RDN_Q_64Q     => fun _ => fct3_RDN
  | FMUL_RUP_Q_64Q     => fun _ => fct3_RUP
  | FMUL_RMM_Q_64Q     => fun _ => fct3_RMM
  | FMUL_DYN_Q_64Q     => fun _ => fct3_DYN
  | FDIV_RNE_Q_64Q     => fun _ => fct3_RNE
  | FDIV_RTZ_Q_64Q     => fun _ => fct3_RTZ
  | FDIV_RDN_Q_64Q     => fun _ => fct3_RDN
  | FDIV_RUP_Q_64Q     => fun _ => fct3_RUP
  | FDIV_RMM_Q_64Q     => fun _ => fct3_RMM
  | FDIV_DYN_Q_64Q     => fun _ => fct3_DYN
  | FSQRT_RNE_Q_64Q    => fun _ => fct3_RNE
  | FSQRT_RTZ_Q_64Q    => fun _ => fct3_RTZ
  | FSQRT_RDN_Q_64Q    => fun _ => fct3_RDN
  | FSQRT_RUP_Q_64Q    => fun _ => fct3_RUP
  | FSQRT_RMM_Q_64Q    => fun _ => fct3_RMM
  | FSQRT_DYN_Q_64Q    => fun _ => fct3_DYN
  | FSGNJ_Q_64Q        => fun _ => fct3_FSGNJ
  | FSGNJN_Q_64Q       => fun _ => fct3_FSGNJN
  | FSGNJX_Q_64Q       => fun _ => fct3_FSGNJX
  | FMIN_Q_64Q         => fun _ => fct3_FMIN
  | FMAX_Q_64Q         => fun _ => fct3_FMAX
  | FCVT_RNE_S_Q_64Q   => fun _ => fct3_RNE
  | FCVT_RTZ_S_Q_64Q   => fun _ => fct3_RTZ
  | FCVT_RDN_S_Q_64Q   => fun _ => fct3_RDN
  | FCVT_RUP_S_Q_64Q   => fun _ => fct3_RUP
  | FCVT_RMM_S_Q_64Q   => fun _ => fct3_RMM
  | FCVT_DYN_S_Q_64Q   => fun _ => fct3_DYN
  | FCVT_RNE_Q_S_64Q   => fun _ => fct3_RNE
  | FCVT_RTZ_Q_S_64Q   => fun _ => fct3_RTZ
  | FCVT_RDN_Q_S_64Q   => fun _ => fct3_RDN
  | FCVT_RUP_Q_S_64Q   => fun _ => fct3_RUP
  | FCVT_RMM_Q_S_64Q   => fun _ => fct3_RMM
  | FCVT_DYN_Q_S_64Q   => fun _ => fct3_DYN
  | FCVT_RNE_D_Q_64Q   => fun _ => fct3_RNE
  | FCVT_RTZ_D_Q_64Q   => fun _ => fct3_RTZ
  | FCVT_RDN_D_Q_64Q   => fun _ => fct3_RDN
  | FCVT_RUP_D_Q_64Q   => fun _ => fct3_RUP
  | FCVT_RMM_D_Q_64Q   => fun _ => fct3_RMM
  | FCVT_DYN_D_Q_64Q   => fun _ => fct3_DYN
  | FCVT_RNE_Q_D_64Q   => fun _ => fct3_RNE
  | FCVT_RTZ_Q_D_64Q   => fun _ => fct3_RTZ
  | FCVT_RDN_Q_D_64Q   => fun _ => fct3_RDN
  | FCVT_RUP_Q_D_64Q   => fun _ => fct3_RUP
  | FCVT_RMM_Q_D_64Q   => fun _ => fct3_RMM
  | FCVT_DYN_Q_D_64Q   => fun _ => fct3_DYN
  | FEQ_Q_64Q          => fun _ => fct3_FEQ
  | FLT_Q_64Q          => fun _ => fct3_FLT
  | FLE_Q_64Q          => fun _ => fct3_FLE
  | FCLASS_Q_64Q       => fun _ => fct3_FCLASS
  | FCVT_RNE_W_Q_64Q   => fun _ => fct3_RNE
  | FCVT_RTZ_W_Q_64Q   => fun _ => fct3_RTZ
  | FCVT_RDN_W_Q_64Q   => fun _ => fct3_RDN
  | FCVT_RUP_W_Q_64Q   => fun _ => fct3_RUP
  | FCVT_RMM_W_Q_64Q   => fun _ => fct3_RMM
  | FCVT_DYN_W_Q_64Q   => fun _ => fct3_DYN
  | FCVT_RNE_WU_Q_64Q  => fun _ => fct3_RNE
  | FCVT_RTZ_WU_Q_64Q  => fun _ => fct3_RTZ
  | FCVT_RDN_WU_Q_64Q  => fun _ => fct3_RDN
  | FCVT_RUP_WU_Q_64Q  => fun _ => fct3_RUP
  | FCVT_RMM_WU_Q_64Q  => fun _ => fct3_RMM
  | FCVT_DYN_WU_Q_64Q  => fun _ => fct3_DYN
  | FCVT_RNE_Q_W_64Q   => fun _ => fct3_RNE
  | FCVT_RTZ_Q_W_64Q   => fun _ => fct3_RTZ
  | FCVT_RDN_Q_W_64Q   => fun _ => fct3_RDN
  | FCVT_RUP_Q_W_64Q   => fun _ => fct3_RUP
  | FCVT_RMM_Q_W_64Q   => fun _ => fct3_RMM
  | FCVT_DYN_Q_W_64Q   => fun _ => fct3_DYN
  | FCVT_RNE_Q_WU_64Q  => fun _ => fct3_RNE
  | FCVT_RTZ_Q_WU_64Q  => fun _ => fct3_RTZ
  | FCVT_RDN_Q_WU_64Q  => fun _ => fct3_RDN
  | FCVT_RUP_Q_WU_64Q  => fun _ => fct3_RUP
  | FCVT_RMM_Q_WU_64Q  => fun _ => fct3_RMM
  | FCVT_DYN_Q_WU_64Q  => fun _ => fct3_DYN
  | FCVT_RNE_L_Q_64Q   => fun _ => fct3_RNE
  | FCVT_RTZ_L_Q_64Q   => fun _ => fct3_RTZ
  | FCVT_RDN_L_Q_64Q   => fun _ => fct3_RDN
  | FCVT_RUP_L_Q_64Q   => fun _ => fct3_RUP
  | FCVT_RMM_L_Q_64Q   => fun _ => fct3_RMM
  | FCVT_DYN_L_Q_64Q   => fun _ => fct3_DYN
  | FCVT_RNE_LU_Q_64Q  => fun _ => fct3_RNE
  | FCVT_RTZ_LU_Q_64Q  => fun _ => fct3_RTZ
  | FCVT_RDN_LU_Q_64Q  => fun _ => fct3_RDN
  | FCVT_RUP_LU_Q_64Q  => fun _ => fct3_RUP
  | FCVT_RMM_LU_Q_64Q  => fun _ => fct3_RMM
  | FCVT_DYN_LU_Q_64Q  => fun _ => fct3_DYN
  | FCVT_RNE_Q_L_64Q   => fun _ => fct3_RNE
  | FCVT_RTZ_Q_L_64Q   => fun _ => fct3_RTZ
  | FCVT_RDN_Q_L_64Q   => fun _ => fct3_RDN
  | FCVT_RUP_Q_L_64Q   => fun _ => fct3_RUP
  | FCVT_RMM_Q_L_64Q   => fun _ => fct3_RMM
  | FCVT_DYN_Q_L_64Q   => fun _ => fct3_DYN
  | FCVT_RNE_Q_LU_64Q  => fun _ => fct3_RNE
  | FCVT_RTZ_Q_LU_64Q  => fun _ => fct3_RTZ
  | FCVT_RDN_Q_LU_64Q  => fun _ => fct3_RDN
  | FCVT_RUP_Q_LU_64Q  => fun _ => fct3_RUP
  | FCVT_RMM_Q_LU_64Q  => fun _ => fct3_RMM
  | FCVT_DYN_Q_LU_64Q  => fun _ => fct3_DYN
  | _                  => fun _ => False_rec _ _
  end); try reflexivity; simpl in e; inversion e.
Defined.

Inductive fct7_type :=
| fct7_ADD        | fct7_SUB        | fct7_SLL        | fct7_SLT
| fct7_SLTU       | fct7_XOR        | fct7_SRL        | fct7_SRA
| fct7_OR         | fct7_AND        | fct7_ADDW       | fct7_SUBW
| fct7_SLLW       | fct7_SRLW       | fct7_SRAW       | fct7_MUL
| fct7_MULH       | fct7_MULHSU     | fct7_MULHU      | fct7_DIV
| fct7_DIVU       | fct7_REM        | fct7_REMU       | fct7_MULW
| fct7_DIVW       | fct7_DIVUW      | fct7_REMW       | fct7_REMUW
| fct7_FADD_S     | fct7_FSUB_S     | fct7_FMUL_S     | fct7_FDIV_S
| fct7_FSQRT_S    | fct7_FSGNJ_S    | fct7_FMIN_S     | fct7_FCVT_W_S
| fct7_FMV_X_W    | fct7_FEQ_S      | fct7_FCLASS_S   | fct7_FCVT_S_W
| fct7_FMV_W_X    | fct7_FADD_D     | fct7_FSUB_D     | fct7_FMUL_D
| fct7_FDIV_D     | fct7_FSQRT_D    | fct7_FSGNJ_D    | fct7_FMIN_D
| fct7_FCVT_W_D   | fct7_FMV_X_D    | fct7_FEQ_D      | fct7_FCLASS_D
| fct7_FCVT_D_W   | fct7_FMV_D_X    | fct7_FCVT_S_D   | fct7_FCVT_D_S
| fct7_FCVT_D_Q   | fct7_FCVT_Q_D   | fct7_FADD_Q     | fct7_FSUB_Q
| fct7_FMUL_Q     | fct7_FDIV_Q     | fct7_FSQRT_Q    | fct7_FSGNJ_Q
| fct7_FMIN_Q     | fct7_FCVT_X_Q   | fct7_FMV_Q_W    | fct7_FEQ_Q
| fct7_FCLASS_Q   | fct7_FCVT_Q_X   | fct7_FMV_W_Q    | fct7_FCVT_Q_S
| fct7_SFENCE_VMA | fct7_LR_00      | fct7_LR_01      | fct7_LR_10
| fct7_LR_11      | fct7_SC_00      | fct7_SC_01      | fct7_SC_10
| fct7_SC_11      | fct7_AMOSWAP_00 | fct7_AMOSWAP_01 | fct7_AMOSWAP_10
| fct7_AMOSWAP_11 | fct7_AMOADD_00  | fct7_AMOADD_01  | fct7_AMOADD_10
| fct7_AMOADD_11  | fct7_AMOXOR_00  | fct7_AMOXOR_01  | fct7_AMOXOR_10
| fct7_AMOXOR_11  | fct7_AMOAND_00  | fct7_AMOAND_01  | fct7_AMOAND_10
| fct7_AMOAND_11  | fct7_AMOOR_00   | fct7_AMOOR_01   | fct7_AMOOR_10
| fct7_AMOOR_11   | fct7_AMOMIN_00  | fct7_AMOMIN_01  | fct7_AMOMIN_10
| fct7_AMOMIN_11  | fct7_AMOMAX_00  | fct7_AMOMAX_01  | fct7_AMOMAX_10
| fct7_AMOMAX_11  | fct7_AMOMINU_00 | fct7_AMOMINU_01 | fct7_AMOMINU_10
| fct7_AMOMINU_11 | fct7_AMOMAXU_00 | fct7_AMOMAXU_01 | fct7_AMOMAXU_10
| fct7_AMOMAXU_11.

Definition fct7_bin (f : fct7_type) :=
  match f with
  | fct7_ADD        => Ob~0~0~0~0~0~0~0 | fct7_SUB        => Ob~0~1~0~0~0~0~0
  | fct7_SLL        => Ob~0~0~0~0~0~0~0 | fct7_SLT        => Ob~0~0~0~0~0~0~0
  | fct7_SLTU       => Ob~0~0~0~0~0~0~0 | fct7_XOR        => Ob~0~0~0~0~0~0~0
  | fct7_SRL        => Ob~0~0~0~0~0~0~0 | fct7_SRA        => Ob~0~1~0~0~0~0~0
  | fct7_OR         => Ob~0~0~0~0~0~0~0 | fct7_AND        => Ob~0~0~0~0~0~0~0
  | fct7_ADDW       => Ob~0~0~0~0~0~0~0 | fct7_SUBW       => Ob~0~1~0~0~0~0~0
  | fct7_SLLW       => Ob~0~0~0~0~0~0~0 | fct7_SRLW       => Ob~0~0~0~0~0~0~0
  | fct7_SRAW       => Ob~0~1~0~0~0~0~0 | fct7_MUL        => Ob~0~0~0~0~0~0~1
  | fct7_MULH       => Ob~0~0~0~0~0~0~1 | fct7_MULHSU     => Ob~0~0~0~0~0~0~1
  | fct7_MULHU      => Ob~0~0~0~0~0~0~1 | fct7_DIV        => Ob~0~0~0~0~0~0~1
  | fct7_DIVU       => Ob~0~0~0~0~0~0~1 | fct7_REM        => Ob~0~0~0~0~0~0~1
  | fct7_REMU       => Ob~0~0~0~0~0~0~1 | fct7_MULW       => Ob~0~0~0~0~0~0~1
  | fct7_DIVW       => Ob~0~0~0~0~0~0~1 | fct7_DIVUW      => Ob~0~0~0~0~0~0~1
  | fct7_REMW       => Ob~0~0~0~0~0~0~1 | fct7_REMUW      => Ob~0~0~0~0~0~0~1
  | fct7_FADD_S     => Ob~0~0~0~0~0~0~0 | fct7_FSUB_S     => Ob~0~0~0~0~1~0~0
  | fct7_FMUL_S     => Ob~0~0~0~1~0~0~0 | fct7_FDIV_S     => Ob~0~0~0~1~1~0~0
  | fct7_FSQRT_S    => Ob~0~1~0~1~1~0~0 | fct7_FSGNJ_S    => Ob~0~0~1~0~0~0~0
  | fct7_FMIN_S     => Ob~0~0~1~0~1~0~0 | fct7_FCVT_W_S   => Ob~1~1~0~0~0~0~0
  | fct7_FMV_X_W    => Ob~1~1~1~0~0~0~0 | fct7_FEQ_S      => Ob~1~0~1~0~0~0~0
  | fct7_FCLASS_S   => Ob~1~1~1~0~0~0~0 | fct7_FCVT_S_W   => Ob~1~1~0~1~0~0~0
  | fct7_FMV_W_X    => Ob~1~1~1~1~0~0~0 | fct7_FADD_D     => Ob~0~0~0~0~0~0~1
  | fct7_FCVT_S_D   => Ob~0~1~0~0~0~0~0 | fct7_FCVT_D_S   => Ob~0~1~0~0~0~0~1
  | fct7_FSUB_D     => Ob~0~0~0~0~1~0~1 | fct7_FMUL_D     => Ob~0~0~0~1~0~0~1
  | fct7_FDIV_D     => Ob~0~0~0~1~1~0~1 | fct7_FSQRT_D    => Ob~0~1~0~1~1~0~1
  | fct7_FSGNJ_D    => Ob~0~0~1~0~0~0~1 | fct7_FMIN_D     => Ob~0~0~1~0~1~0~1
  | fct7_FCVT_W_D   => Ob~1~1~0~0~0~0~1 | fct7_FMV_X_D    => Ob~1~1~1~0~0~0~1
  | fct7_FEQ_D      => Ob~1~0~1~0~0~0~1 | fct7_FCLASS_D   => Ob~1~1~1~0~0~0~1
  | fct7_FCVT_D_W   => Ob~1~1~0~1~0~0~1 | fct7_FMV_D_X    => Ob~1~1~1~1~0~0~1
  | fct7_FADD_Q     => Ob~0~0~0~0~0~1~1 | fct7_FSUB_Q     => Ob~0~0~0~0~1~1~1
  | fct7_FMUL_Q     => Ob~0~0~0~1~0~1~1 | fct7_FDIV_Q     => Ob~0~0~0~1~1~1~1
  | fct7_FSQRT_Q    => Ob~0~1~0~1~1~1~1 | fct7_FSGNJ_Q    => Ob~0~0~1~0~0~1~1
  | fct7_FMIN_Q     => Ob~0~0~1~0~1~1~1 | fct7_FCVT_X_Q   => Ob~1~1~0~0~0~1~1
  | fct7_FMV_Q_W    => Ob~1~1~1~0~0~1~1 | fct7_FEQ_Q      => Ob~1~0~1~0~0~1~1
  | fct7_FCLASS_Q   => Ob~1~1~1~0~0~1~1 | fct7_FCVT_Q_X   => Ob~1~1~0~1~0~1~1
  | fct7_FMV_W_Q    => Ob~1~1~1~1~0~1~1 | fct7_SFENCE_VMA => Ob~0~0~0~1~0~0~1
  | fct7_LR_00      => Ob~0~0~0~1~0~0~0 | fct7_LR_01      => Ob~0~0~0~1~0~0~1
  | fct7_LR_10      => Ob~0~0~0~1~0~1~0 | fct7_LR_11      => Ob~0~0~0~1~0~1~1
  | fct7_SC_00      => Ob~0~0~0~1~1~0~0 | fct7_SC_01      => Ob~0~0~0~1~1~0~1
  | fct7_SC_10      => Ob~0~0~0~1~1~1~0 | fct7_SC_11      => Ob~0~0~0~1~1~1~1
  | fct7_AMOSWAP_00 => Ob~0~0~0~0~1~0~0 | fct7_AMOSWAP_01 => Ob~0~0~0~0~1~0~1
  | fct7_AMOSWAP_10 => Ob~0~0~0~0~1~1~0 | fct7_AMOSWAP_11 => Ob~0~0~0~0~1~1~1
  | fct7_AMOADD_00  => Ob~0~0~0~0~0~0~0 | fct7_AMOADD_01  => Ob~0~0~0~0~0~0~1
  | fct7_AMOADD_10  => Ob~0~0~0~0~0~1~0 | fct7_AMOADD_11  => Ob~0~0~0~0~0~1~1
  | fct7_AMOXOR_00  => Ob~0~0~1~0~0~0~0 | fct7_AMOXOR_01  => Ob~0~0~1~0~0~0~1
  | fct7_AMOXOR_10  => Ob~0~0~1~0~0~1~0 | fct7_AMOXOR_11  => Ob~0~0~1~0~0~1~1
  | fct7_AMOAND_00  => Ob~0~1~1~0~0~0~0 | fct7_AMOAND_01  => Ob~0~1~1~0~0~0~1
  | fct7_AMOAND_10  => Ob~0~1~1~0~0~1~0 | fct7_AMOAND_11  => Ob~0~1~1~0~0~1~1
  | fct7_AMOOR_00   => Ob~0~1~0~0~0~0~0 | fct7_AMOOR_01   => Ob~0~1~0~0~0~0~1
  | fct7_AMOOR_10   => Ob~0~1~0~0~0~1~0 | fct7_AMOOR_11   => Ob~0~1~0~0~0~1~1
  | fct7_AMOMIN_00  => Ob~1~0~0~0~0~0~0 | fct7_AMOMIN_01  => Ob~1~0~0~0~0~0~1
  | fct7_AMOMIN_10  => Ob~1~0~0~0~0~1~0 | fct7_AMOMIN_11  => Ob~1~0~0~0~0~1~1
  | fct7_AMOMAX_00  => Ob~1~0~1~0~0~0~0 | fct7_AMOMAX_01  => Ob~1~0~1~0~0~0~1
  | fct7_AMOMAX_10  => Ob~1~0~1~0~0~1~0 | fct7_AMOMAX_11  => Ob~1~0~1~0~0~1~1
  | fct7_AMOMINU_00 => Ob~1~1~0~0~0~0~0 | fct7_AMOMINU_01 => Ob~1~1~0~0~0~0~1
  | fct7_AMOMINU_10 => Ob~1~1~0~0~0~1~0 | fct7_AMOMINU_11 => Ob~1~1~0~0~0~1~1
  | fct7_AMOMAXU_00 => Ob~1~1~1~0~0~0~0 | fct7_AMOMAXU_01 => Ob~1~1~1~0~0~0~1
  | fct7_AMOMAXU_10 => Ob~1~1~1~0~0~1~0 | fct7_AMOMAXU_11 => Ob~1~1~1~0~0~1~1
  | fct7_FCVT_Q_S   => Ob~0~1~0~0~0~1~1 | fct7_FCVT_D_Q   => Ob~0~1~0~0~0~0~1
  | fct7_FCVT_Q_D   => Ob~0~1~0~0~0~1~1
  end.

Definition instruction_fct7 :
  forall (i : instruction), has_fct7 (get_instruction_type i) = true
  -> fct7_type.
refine (fun i =>
  match i with
  | ADD_32I           => fun _ => fct7_ADD
  | SUB_32I           => fun _ => fct7_SUB
  | SLL_32I           => fun _ => fct7_SLL
  | SLT_32I           => fun _ => fct7_SLT
  | SLTU_32I          => fun _ => fct7_SLTU
  | XOR_32I           => fun _ => fct7_XOR
  | SRL_32I           => fun _ => fct7_SRL
  | SRA_32I           => fun _ => fct7_SRA
  | OR_32I            => fun _ => fct7_OR
  | AND_32I           => fun _ => fct7_AND
  | ADD_64I           => fun _ => fct7_ADD
  | SUB_64I           => fun _ => fct7_SUB
  | SLL_64I           => fun _ => fct7_SLL
  | SLT_64I           => fun _ => fct7_SLT
  | SLTU_64I          => fun _ => fct7_SLTU
  | XOR_64I           => fun _ => fct7_XOR
  | SRL_64I           => fun _ => fct7_SRL
  | SRA_64I           => fun _ => fct7_SRA
  | OR_64I            => fun _ => fct7_OR
  | AND_64I           => fun _ => fct7_AND
  | ADDW_64I          => fun _ => fct7_ADDW
  | SUBW_64I          => fun _ => fct7_SUBW
  | SLLW_64I          => fun _ => fct7_SLLW
  | SRLW_64I          => fun _ => fct7_SRLW
  | SRAW_64I          => fun _ => fct7_SRAW
  | MUL_32M           => fun _ => fct7_MUL
  | MULH_32M          => fun _ => fct7_MULH
  | MULHSU_32M        => fun _ => fct7_MULHSU
  | MULHU_32M         => fun _ => fct7_MULHU
  | DIV_32M           => fun _ => fct7_DIV
  | DIVU_32M          => fun _ => fct7_DIVU
  | REM_32M           => fun _ => fct7_REM
  | REMU_32M          => fun _ => fct7_REMU
  | MUL_64M           => fun _ => fct7_MUL
  | MULH_64M          => fun _ => fct7_MULH
  | MULHSU_64M        => fun _ => fct7_MULHSU
  | MULHU_64M         => fun _ => fct7_MULHU
  | DIV_64M           => fun _ => fct7_DIV
  | DIVU_64M          => fun _ => fct7_REM
  | REM_64M           => fun _ => fct7_REM
  | REMU_64M          => fun _ => fct7_REMU
  | MULW_64M          => fun _ => fct7_MULW
  | DIVW_64M          => fun _ => fct7_DIVW
  | DIVUW_64M         => fun _ => fct7_DIVUW
  | REMW_64M          => fun _ => fct7_REMW
  | REMUW_64M         => fun _ => fct7_REMUW
  | LR_W_00_32A       => fun _ => fct7_LR_00
  | LR_W_01_32A       => fun _ => fct7_LR_01
  | LR_W_10_32A       => fun _ => fct7_LR_10
  | LR_W_11_32A       => fun _ => fct7_LR_11
  | SC_W_00_32A       => fun _ => fct7_SC_00
  | SC_W_01_32A       => fun _ => fct7_SC_01
  | SC_W_10_32A       => fun _ => fct7_SC_10
  | SC_W_11_32A       => fun _ => fct7_SC_11
  | AMOSWAP_W_00_32A  => fun _ => fct7_AMOSWAP_00
  | AMOSWAP_W_01_32A  => fun _ => fct7_AMOSWAP_01
  | AMOSWAP_W_10_32A  => fun _ => fct7_AMOSWAP_10
  | AMOSWAP_W_11_32A  => fun _ => fct7_AMOSWAP_11
  | AMOADD_W_00_32A   => fun _ => fct7_AMOADD_00
  | AMOADD_W_01_32A   => fun _ => fct7_AMOADD_01
  | AMOADD_W_10_32A   => fun _ => fct7_AMOADD_10
  | AMOADD_W_11_32A   => fun _ => fct7_AMOADD_11
  | AMOXOR_W_00_32A   => fun _ => fct7_AMOXOR_00
  | AMOXOR_W_01_32A   => fun _ => fct7_AMOXOR_01
  | AMOXOR_W_10_32A   => fun _ => fct7_AMOXOR_10
  | AMOXOR_W_11_32A   => fun _ => fct7_AMOXOR_11
  | AMOAND_W_00_32A   => fun _ => fct7_AMOAND_00
  | AMOAND_W_01_32A   => fun _ => fct7_AMOAND_01
  | AMOAND_W_10_32A   => fun _ => fct7_AMOAND_10
  | AMOAND_W_11_32A   => fun _ => fct7_AMOAND_11
  | AMOOR_W_00_32A    => fun _ => fct7_AMOOR_00
  | AMOOR_W_01_32A    => fun _ => fct7_AMOOR_01
  | AMOOR_W_10_32A    => fun _ => fct7_AMOOR_10
  | AMOOR_W_11_32A    => fun _ => fct7_AMOOR_11
  | AMOMIN_W_00_32A   => fun _ => fct7_AMOMIN_00
  | AMOMIN_W_01_32A   => fun _ => fct7_AMOMIN_01
  | AMOMIN_W_10_32A   => fun _ => fct7_AMOMIN_10
  | AMOMIN_W_11_32A   => fun _ => fct7_AMOMIN_11
  | AMOMAX_W_00_32A   => fun _ => fct7_AMOMAX_00
  | AMOMAX_W_01_32A   => fun _ => fct7_AMOMAX_01
  | AMOMAX_W_10_32A   => fun _ => fct7_AMOMAX_10
  | AMOMAX_W_11_32A   => fun _ => fct7_AMOMAX_11
  | AMOMINU_W_00_32A  => fun _ => fct7_AMOMINU_00
  | AMOMINU_W_01_32A  => fun _ => fct7_AMOMINU_01
  | AMOMINU_W_10_32A  => fun _ => fct7_AMOMINU_10
  | AMOMINU_W_11_32A  => fun _ => fct7_AMOMINU_11
  | AMOMAXU_W_00_32A  => fun _ => fct7_AMOMAXU_00
  | AMOMAXU_W_01_32A  => fun _ => fct7_AMOMAXU_01
  | AMOMAXU_W_10_32A  => fun _ => fct7_AMOMAXU_10
  | AMOMAXU_W_11_32A  => fun _ => fct7_AMOMAXU_11
  | LR_W_00_64A       => fun _ => fct7_LR_00
  | LR_W_01_64A       => fun _ => fct7_LR_01
  | LR_W_10_64A       => fun _ => fct7_LR_10
  | LR_W_11_64A       => fun _ => fct7_LR_11
  | SC_W_00_64A       => fun _ => fct7_SC_00
  | SC_W_01_64A       => fun _ => fct7_SC_01
  | SC_W_10_64A       => fun _ => fct7_SC_10
  | SC_W_11_64A       => fun _ => fct7_SC_11
  | AMOSWAP_W_00_64A  => fun _ => fct7_AMOSWAP_00
  | AMOSWAP_W_01_64A  => fun _ => fct7_AMOSWAP_01
  | AMOSWAP_W_10_64A  => fun _ => fct7_AMOSWAP_10
  | AMOSWAP_W_11_64A  => fun _ => fct7_AMOSWAP_11
  | AMOADD_W_00_64A   => fun _ => fct7_AMOADD_00
  | AMOADD_W_01_64A   => fun _ => fct7_AMOADD_01
  | AMOADD_W_10_64A   => fun _ => fct7_AMOADD_10
  | AMOADD_W_11_64A   => fun _ => fct7_AMOADD_11
  | AMOXOR_W_00_64A   => fun _ => fct7_AMOXOR_00
  | AMOXOR_W_01_64A   => fun _ => fct7_AMOXOR_01
  | AMOXOR_W_10_64A   => fun _ => fct7_AMOXOR_10
  | AMOXOR_W_11_64A   => fun _ => fct7_AMOXOR_11
  | AMOAND_W_00_64A   => fun _ => fct7_AMOAND_00
  | AMOAND_W_01_64A   => fun _ => fct7_AMOAND_01
  | AMOAND_W_10_64A   => fun _ => fct7_AMOAND_10
  | AMOAND_W_11_64A   => fun _ => fct7_AMOAND_11
  | AMOOR_W_00_64A    => fun _ => fct7_AMOOR_00
  | AMOOR_W_01_64A    => fun _ => fct7_AMOOR_01
  | AMOOR_W_10_64A    => fun _ => fct7_AMOOR_10
  | AMOOR_W_11_64A    => fun _ => fct7_AMOOR_11
  | AMOMIN_W_00_64A   => fun _ => fct7_AMOMIN_00
  | AMOMIN_W_01_64A   => fun _ => fct7_AMOMIN_01
  | AMOMIN_W_10_64A   => fun _ => fct7_AMOMIN_10
  | AMOMIN_W_11_64A   => fun _ => fct7_AMOMIN_11
  | AMOMAX_W_00_64A   => fun _ => fct7_AMOMAX_00
  | AMOMAX_W_01_64A   => fun _ => fct7_AMOMAX_01
  | AMOMAX_W_10_64A   => fun _ => fct7_AMOMAX_10
  | AMOMAX_W_11_64A   => fun _ => fct7_AMOMAX_11
  | AMOMINU_W_00_64A  => fun _ => fct7_AMOMINU_00
  | AMOMINU_W_01_64A  => fun _ => fct7_AMOMINU_01
  | AMOMINU_W_10_64A  => fun _ => fct7_AMOMINU_10
  | AMOMINU_W_11_64A  => fun _ => fct7_AMOMINU_11
  | AMOMAXU_W_00_64A  => fun _ => fct7_AMOMAXU_00
  | AMOMAXU_W_01_64A  => fun _ => fct7_AMOMAXU_01
  | AMOMAXU_W_10_64A  => fun _ => fct7_AMOMAXU_10
  | AMOMAXU_W_11_64A  => fun _ => fct7_AMOMAXU_11
  | LR_D_00_64A       => fun _ => fct7_LR_00
  | LR_D_01_64A       => fun _ => fct7_LR_01
  | LR_D_10_64A       => fun _ => fct7_LR_10
  | LR_D_11_64A       => fun _ => fct7_LR_11
  | SC_D_00_64A       => fun _ => fct7_SC_00
  | SC_D_01_64A       => fun _ => fct7_SC_01
  | SC_D_10_64A       => fun _ => fct7_SC_10
  | SC_D_11_64A       => fun _ => fct7_SC_11
  | AMOSWAP_D_00_64A  => fun _ => fct7_AMOSWAP_00
  | AMOSWAP_D_01_64A  => fun _ => fct7_AMOSWAP_01
  | AMOSWAP_D_10_64A  => fun _ => fct7_AMOSWAP_10
  | AMOSWAP_D_11_64A  => fun _ => fct7_AMOSWAP_11
  | AMOADD_D_00_64A   => fun _ => fct7_AMOADD_00
  | AMOADD_D_01_64A   => fun _ => fct7_AMOADD_01
  | AMOADD_D_10_64A   => fun _ => fct7_AMOADD_10
  | AMOADD_D_11_64A   => fun _ => fct7_AMOADD_11
  | AMOXOR_D_00_64A   => fun _ => fct7_AMOXOR_00
  | AMOXOR_D_01_64A   => fun _ => fct7_AMOXOR_01
  | AMOXOR_D_10_64A   => fun _ => fct7_AMOXOR_10
  | AMOXOR_D_11_64A   => fun _ => fct7_AMOXOR_11
  | AMOAND_D_00_64A   => fun _ => fct7_AMOAND_00
  | AMOAND_D_01_64A   => fun _ => fct7_AMOAND_01
  | AMOAND_D_10_64A   => fun _ => fct7_AMOAND_10
  | AMOAND_D_11_64A   => fun _ => fct7_AMOAND_11
  | AMOOR_D_00_64A    => fun _ => fct7_AMOOR_00
  | AMOOR_D_01_64A    => fun _ => fct7_AMOOR_01
  | AMOOR_D_10_64A    => fun _ => fct7_AMOOR_10
  | AMOOR_D_11_64A    => fun _ => fct7_AMOOR_11
  | AMOMIN_D_00_64A   => fun _ => fct7_AMOMIN_00
  | AMOMIN_D_01_64A   => fun _ => fct7_AMOMIN_01
  | AMOMIN_D_10_64A   => fun _ => fct7_AMOMIN_10
  | AMOMIN_D_11_64A   => fun _ => fct7_AMOMIN_11
  | AMOMAX_D_00_64A   => fun _ => fct7_AMOMAX_00
  | AMOMAX_D_01_64A   => fun _ => fct7_AMOMAX_01
  | AMOMAX_D_10_64A   => fun _ => fct7_AMOMAX_10
  | AMOMAX_D_11_64A   => fun _ => fct7_AMOMAX_11
  | AMOMINU_D_00_64A  => fun _ => fct7_AMOMINU_00
  | AMOMINU_D_01_64A  => fun _ => fct7_AMOMINU_01
  | AMOMINU_D_10_64A  => fun _ => fct7_AMOMINU_10
  | AMOMINU_D_11_64A  => fun _ => fct7_AMOMINU_11
  | AMOMAXU_D_00_64A  => fun _ => fct7_AMOMAXU_00
  | AMOMAXU_D_01_64A  => fun _ => fct7_AMOMAXU_01
  | AMOMAXU_D_10_64A  => fun _ => fct7_AMOMAXU_10
  | AMOMAXU_D_11_64A  => fun _ => fct7_AMOMAXU_11
  | FADD_RNE_S_32F    => fun _ => fct7_FADD_S
  | FADD_RTZ_S_32F    => fun _ => fct7_FADD_S
  | FADD_RDN_S_32F    => fun _ => fct7_FADD_S
  | FADD_RUP_S_32F    => fun _ => fct7_FADD_S
  | FADD_RMM_S_32F    => fun _ => fct7_FADD_S
  | FADD_DYN_S_32F    => fun _ => fct7_FADD_S
  | FSUB_RNE_S_32F    => fun _ => fct7_FSUB_S
  | FSUB_RTZ_S_32F    => fun _ => fct7_FSUB_S
  | FSUB_RDN_S_32F    => fun _ => fct7_FSUB_S
  | FSUB_RUP_S_32F    => fun _ => fct7_FSUB_S
  | FSUB_RMM_S_32F    => fun _ => fct7_FSUB_S
  | FSUB_DYN_S_32F    => fun _ => fct7_FSUB_S
  | FMUL_RNE_S_32F    => fun _ => fct7_FMUL_S
  | FMUL_RTZ_S_32F    => fun _ => fct7_FMUL_S
  | FMUL_RDN_S_32F    => fun _ => fct7_FMUL_S
  | FMUL_RUP_S_32F    => fun _ => fct7_FMUL_S
  | FMUL_RMM_S_32F    => fun _ => fct7_FMUL_S
  | FMUL_DYN_S_32F    => fun _ => fct7_FMUL_S
  | FDIV_RNE_S_32F    => fun _ => fct7_FDIV_S
  | FDIV_RTZ_S_32F    => fun _ => fct7_FDIV_S
  | FDIV_RDN_S_32F    => fun _ => fct7_FDIV_S
  | FDIV_RUP_S_32F    => fun _ => fct7_FDIV_S
  | FDIV_RMM_S_32F    => fun _ => fct7_FDIV_S
  | FDIV_DYN_S_32F    => fun _ => fct7_FDIV_S
  | FSQRT_RNE_S_32F   => fun _ => fct7_FSQRT_S
  | FSQRT_RTZ_S_32F   => fun _ => fct7_FSQRT_S
  | FSQRT_RDN_S_32F   => fun _ => fct7_FSQRT_S
  | FSQRT_RUP_S_32F   => fun _ => fct7_FSQRT_S
  | FSQRT_RMM_S_32F   => fun _ => fct7_FSQRT_S
  | FSQRT_DYN_S_32F   => fun _ => fct7_FSQRT_S
  | FSGNJ_S_32F       => fun _ => fct7_FSGNJ_S
  | FSGNJN_S_32F      => fun _ => fct7_FSGNJ_S
  | FSGNJX_S_32F      => fun _ => fct7_FSGNJ_S
  | FMIN_S_32F        => fun _ => fct7_FMIN_S
  | FMAX_S_32F        => fun _ => fct7_FMIN_S
  | FCVT_RNE_W_S_32F  => fun _ => fct7_FCVT_W_S
  | FCVT_RTZ_W_S_32F  => fun _ => fct7_FCVT_W_S
  | FCVT_RDN_W_S_32F  => fun _ => fct7_FCVT_W_S
  | FCVT_RUP_W_S_32F  => fun _ => fct7_FCVT_W_S
  | FCVT_RMM_W_S_32F  => fun _ => fct7_FCVT_W_S
  | FCVT_DYN_W_S_32F  => fun _ => fct7_FCVT_W_S
  | FCVT_RNE_WU_S_32F => fun _ => fct7_FCVT_W_S
  | FCVT_RTZ_WU_S_32F => fun _ => fct7_FCVT_W_S
  | FCVT_RDN_WU_S_32F => fun _ => fct7_FCVT_W_S
  | FCVT_RUP_WU_S_32F => fun _ => fct7_FCVT_W_S
  | FCVT_RMM_WU_S_32F => fun _ => fct7_FCVT_W_S
  | FCVT_DYN_WU_S_32F => fun _ => fct7_FCVT_W_S
  | FMV_X_W_32F       => fun _ => fct7_FMV_X_W
  | FEQ_S_32F         => fun _ => fct7_FEQ_S
  | FLT_S_32F         => fun _ => fct7_FEQ_S
  | FLE_S_32F         => fun _ => fct7_FEQ_S
  | FCLASS_S_32F      => fun _ => fct7_FCLASS_S
  | FCVT_RNE_S_W_32F  => fun _ => fct7_FCVT_S_W
  | FCVT_RTZ_S_W_32F  => fun _ => fct7_FCVT_S_W
  | FCVT_RDN_S_W_32F  => fun _ => fct7_FCVT_S_W
  | FCVT_RUP_S_W_32F  => fun _ => fct7_FCVT_S_W
  | FCVT_RMM_S_W_32F  => fun _ => fct7_FCVT_S_W
  | FCVT_DYN_S_W_32F  => fun _ => fct7_FCVT_S_W
  | FCVT_RNE_S_WU_32F => fun _ => fct7_FCVT_S_W
  | FCVT_RTZ_S_WU_32F => fun _ => fct7_FCVT_S_W
  | FCVT_RDN_S_WU_32F => fun _ => fct7_FCVT_S_W
  | FCVT_RUP_S_WU_32F => fun _ => fct7_FCVT_S_W
  | FCVT_RMM_S_WU_32F => fun _ => fct7_FCVT_S_W
  | FCVT_DYN_S_WU_32F => fun _ => fct7_FCVT_S_W
  | FMV_W_X_32F       => fun _ => fct7_FMV_W_X
  | FADD_RNE_S_64F    => fun _ => fct7_FADD_S
  | FADD_RTZ_S_64F    => fun _ => fct7_FADD_S
  | FADD_RDN_S_64F    => fun _ => fct7_FADD_S
  | FADD_RUP_S_64F    => fun _ => fct7_FADD_S
  | FADD_RMM_S_64F    => fun _ => fct7_FADD_S
  | FADD_DYN_S_64F    => fun _ => fct7_FADD_S
  | FSUB_RNE_S_64F    => fun _ => fct7_FSUB_S
  | FSUB_RTZ_S_64F    => fun _ => fct7_FSUB_S
  | FSUB_RDN_S_64F    => fun _ => fct7_FSUB_S
  | FSUB_RUP_S_64F    => fun _ => fct7_FSUB_S
  | FSUB_RMM_S_64F    => fun _ => fct7_FSUB_S
  | FSUB_DYN_S_64F    => fun _ => fct7_FSUB_S
  | FMUL_RNE_S_64F    => fun _ => fct7_FMUL_S
  | FMUL_RTZ_S_64F    => fun _ => fct7_FMUL_S
  | FMUL_RDN_S_64F    => fun _ => fct7_FMUL_S
  | FMUL_RUP_S_64F    => fun _ => fct7_FMUL_S
  | FMUL_RMM_S_64F    => fun _ => fct7_FMUL_S
  | FMUL_DYN_S_64F    => fun _ => fct7_FMUL_S
  | FDIV_RNE_S_64F    => fun _ => fct7_FDIV_S
  | FDIV_RTZ_S_64F    => fun _ => fct7_FDIV_S
  | FDIV_RDN_S_64F    => fun _ => fct7_FDIV_S
  | FDIV_RUP_S_64F    => fun _ => fct7_FDIV_S
  | FDIV_RMM_S_64F    => fun _ => fct7_FDIV_S
  | FDIV_DYN_S_64F    => fun _ => fct7_FDIV_S
  | FSQRT_RNE_S_64F   => fun _ => fct7_FSQRT_S
  | FSQRT_RTZ_S_64F   => fun _ => fct7_FSQRT_S
  | FSQRT_RDN_S_64F   => fun _ => fct7_FSQRT_S
  | FSQRT_RUP_S_64F   => fun _ => fct7_FSQRT_S
  | FSQRT_RMM_S_64F   => fun _ => fct7_FSQRT_S
  | FSQRT_DYN_S_64F   => fun _ => fct7_FSQRT_S
  | FSGNJ_S_64F       => fun _ => fct7_FSGNJ_S
  | FSGNJN_S_64F      => fun _ => fct7_FSGNJ_S
  | FSGNJX_S_64F      => fun _ => fct7_FSGNJ_S
  | FMIN_S_64F        => fun _ => fct7_FMIN_S
  | FMAX_S_64F        => fun _ => fct7_FMIN_S
  | FCVT_RNE_W_S_64F  => fun _ => fct7_FCVT_W_S
  | FCVT_RTZ_W_S_64F  => fun _ => fct7_FCVT_W_S
  | FCVT_RDN_W_S_64F  => fun _ => fct7_FCVT_W_S
  | FCVT_RUP_W_S_64F  => fun _ => fct7_FCVT_W_S
  | FCVT_RMM_W_S_64F  => fun _ => fct7_FCVT_W_S
  | FCVT_DYN_W_S_64F  => fun _ => fct7_FCVT_W_S
  | FCVT_RNE_WU_S_64F => fun _ => fct7_FCVT_W_S
  | FCVT_RTZ_WU_S_64F => fun _ => fct7_FCVT_W_S
  | FCVT_RDN_WU_S_64F => fun _ => fct7_FCVT_W_S
  | FCVT_RUP_WU_S_64F => fun _ => fct7_FCVT_W_S
  | FCVT_RMM_WU_S_64F => fun _ => fct7_FCVT_W_S
  | FCVT_DYN_WU_S_64F => fun _ => fct7_FCVT_W_S
  | FMV_X_W_64F       => fun _ => fct7_FMV_X_W
  | FEQ_S_64F         => fun _ => fct7_FEQ_S
  | FLT_S_64F         => fun _ => fct7_FEQ_S
  | FLE_S_64F         => fun _ => fct7_FEQ_S
  | FCLASS_S_64F      => fun _ => fct7_FCLASS_S
  | FCVT_RNE_S_W_64F  => fun _ => fct7_FCVT_S_W
  | FCVT_RTZ_S_W_64F  => fun _ => fct7_FCVT_S_W
  | FCVT_RDN_S_W_64F  => fun _ => fct7_FCVT_S_W
  | FCVT_RUP_S_W_64F  => fun _ => fct7_FCVT_S_W
  | FCVT_RMM_S_W_64F  => fun _ => fct7_FCVT_S_W
  | FCVT_DYN_S_W_64F  => fun _ => fct7_FCVT_S_W
  | FCVT_RNE_S_WU_64F => fun _ => fct7_FCVT_S_W
  | FCVT_RTZ_S_WU_64F => fun _ => fct7_FCVT_S_W
  | FCVT_RDN_S_WU_64F => fun _ => fct7_FCVT_S_W
  | FCVT_RUP_S_WU_64F => fun _ => fct7_FCVT_S_W
  | FCVT_RMM_S_WU_64F => fun _ => fct7_FCVT_S_W
  | FCVT_DYN_S_WU_64F => fun _ => fct7_FCVT_S_W
  | FMV_W_X_64F       => fun _ => fct7_FMV_W_X
  | FCVT_RNE_L_S_64F  => fun _ => fct7_FCVT_W_S
  | FCVT_RTZ_L_S_64F  => fun _ => fct7_FCVT_W_S
  | FCVT_RDN_L_S_64F  => fun _ => fct7_FCVT_W_S
  | FCVT_RUP_L_S_64F  => fun _ => fct7_FCVT_W_S
  | FCVT_RMM_L_S_64F  => fun _ => fct7_FCVT_W_S
  | FCVT_DYN_L_S_64F  => fun _ => fct7_FCVT_W_S
  | FCVT_RNE_LU_S_64F => fun _ => fct7_FCVT_W_S
  | FCVT_RTZ_LU_S_64F => fun _ => fct7_FCVT_W_S
  | FCVT_RDN_LU_S_64F => fun _ => fct7_FCVT_W_S
  | FCVT_RUP_LU_S_64F => fun _ => fct7_FCVT_W_S
  | FCVT_RMM_LU_S_64F => fun _ => fct7_FCVT_W_S
  | FCVT_DYN_LU_S_64F => fun _ => fct7_FCVT_W_S
  | FCVT_RNE_S_L_64F  => fun _ => fct7_FCVT_S_W
  | FCVT_RTZ_S_L_64F  => fun _ => fct7_FCVT_S_W
  | FCVT_RDN_S_L_64F  => fun _ => fct7_FCVT_S_W
  | FCVT_RUP_S_L_64F  => fun _ => fct7_FCVT_S_W
  | FCVT_RMM_S_L_64F  => fun _ => fct7_FCVT_S_W
  | FCVT_DYN_S_L_64F  => fun _ => fct7_FCVT_S_W
  | FCVT_RNE_S_LU_64F => fun _ => fct7_FCVT_S_W
  | FCVT_RTZ_S_LU_64F => fun _ => fct7_FCVT_S_W
  | FCVT_RDN_S_LU_64F => fun _ => fct7_FCVT_S_W
  | FCVT_RUP_S_LU_64F => fun _ => fct7_FCVT_S_W
  | FCVT_RMM_S_LU_64F => fun _ => fct7_FCVT_S_W
  | FCVT_DYN_S_LU_64F => fun _ => fct7_FCVT_S_W
  | FADD_RNE_D_32D    => fun _ => fct7_FADD_D
  | FADD_RTZ_D_32D    => fun _ => fct7_FADD_D
  | FADD_RDN_D_32D    => fun _ => fct7_FADD_D
  | FADD_RUP_D_32D    => fun _ => fct7_FADD_D
  | FADD_RMM_D_32D    => fun _ => fct7_FADD_D
  | FADD_DYN_D_32D    => fun _ => fct7_FADD_D
  | FSUB_RNE_D_32D    => fun _ => fct7_FSUB_D
  | FSUB_RTZ_D_32D    => fun _ => fct7_FSUB_D
  | FSUB_RDN_D_32D    => fun _ => fct7_FSUB_D
  | FSUB_RUP_D_32D    => fun _ => fct7_FSUB_D
  | FSUB_RMM_D_32D    => fun _ => fct7_FSUB_D
  | FSUB_DYN_D_32D    => fun _ => fct7_FSUB_D
  | FMUL_RNE_D_32D    => fun _ => fct7_FMUL_D
  | FMUL_RTZ_D_32D    => fun _ => fct7_FMUL_D
  | FMUL_RDN_D_32D    => fun _ => fct7_FMUL_D
  | FMUL_RUP_D_32D    => fun _ => fct7_FMUL_D
  | FMUL_RMM_D_32D    => fun _ => fct7_FMUL_D
  | FMUL_DYN_D_32D    => fun _ => fct7_FMUL_D
  | FDIV_RNE_D_32D    => fun _ => fct7_FDIV_D
  | FDIV_RTZ_D_32D    => fun _ => fct7_FDIV_D
  | FDIV_RDN_D_32D    => fun _ => fct7_FDIV_D
  | FDIV_RUP_D_32D    => fun _ => fct7_FDIV_D
  | FDIV_RMM_D_32D    => fun _ => fct7_FDIV_D
  | FDIV_DYN_D_32D    => fun _ => fct7_FDIV_D
  | FSQRT_RNE_D_32D   => fun _ => fct7_FSQRT_D
  | FSQRT_RTZ_D_32D   => fun _ => fct7_FSQRT_D
  | FSQRT_RDN_D_32D   => fun _ => fct7_FSQRT_D
  | FSQRT_RUP_D_32D   => fun _ => fct7_FSQRT_D
  | FSQRT_RMM_D_32D   => fun _ => fct7_FSQRT_D
  | FSQRT_DYN_D_32D   => fun _ => fct7_FSQRT_D
  | FSGNJ_D_32D       => fun _ => fct7_FSGNJ_D
  | FSGNJN_D_32D      => fun _ => fct7_FSGNJ_D
  | FSGNJX_D_32D      => fun _ => fct7_FSGNJ_D
  | FMIN_D_32D        => fun _ => fct7_FMIN_D
  | FMAX_D_32D        => fun _ => fct7_FMIN_D
  | FCVT_RNE_S_D_32D  => fun _ => fct7_FCVT_S_D
  | FCVT_RTZ_S_D_32D  => fun _ => fct7_FCVT_S_D
  | FCVT_RDN_S_D_32D  => fun _ => fct7_FCVT_S_D
  | FCVT_RUP_S_D_32D  => fun _ => fct7_FCVT_S_D
  | FCVT_RMM_S_D_32D  => fun _ => fct7_FCVT_S_D
  | FCVT_DYN_S_D_32D  => fun _ => fct7_FCVT_S_D
  | FCVT_RNE_D_S_32D  => fun _ => fct7_FCVT_D_S
  | FCVT_RTZ_D_S_32D  => fun _ => fct7_FCVT_D_S
  | FCVT_RDN_D_S_32D  => fun _ => fct7_FCVT_D_S
  | FCVT_RUP_D_S_32D  => fun _ => fct7_FCVT_D_S
  | FCVT_RMM_D_S_32D  => fun _ => fct7_FCVT_D_S
  | FCVT_DYN_D_S_32D  => fun _ => fct7_FCVT_D_S
  | FEQ_D_32D         => fun _ => fct7_FEQ_D
  | FLT_D_32D         => fun _ => fct7_FEQ_D
  | FLE_D_32D         => fun _ => fct7_FEQ_D
  | FCLASS_D_32D      => fun _ => fct7_FCLASS_D
  | FCVT_RNE_W_D_32D  => fun _ => fct7_FCVT_W_D
  | FCVT_RTZ_W_D_32D  => fun _ => fct7_FCVT_W_D
  | FCVT_RDN_W_D_32D  => fun _ => fct7_FCVT_W_D
  | FCVT_RUP_W_D_32D  => fun _ => fct7_FCVT_W_D
  | FCVT_RMM_W_D_32D  => fun _ => fct7_FCVT_W_D
  | FCVT_DYN_W_D_32D  => fun _ => fct7_FCVT_W_D
  | FCVT_RNE_WU_D_32D => fun _ => fct7_FCVT_W_D
  | FCVT_RTZ_WU_D_32D => fun _ => fct7_FCVT_W_D
  | FCVT_RDN_WU_D_32D => fun _ => fct7_FCVT_W_D
  | FCVT_RUP_WU_D_32D => fun _ => fct7_FCVT_W_D
  | FCVT_RMM_WU_D_32D => fun _ => fct7_FCVT_W_D
  | FCVT_DYN_WU_D_32D => fun _ => fct7_FCVT_W_D
  | FCVT_RNE_D_W_32D  => fun _ => fct7_FCVT_D_W
  | FCVT_RTZ_D_W_32D  => fun _ => fct7_FCVT_D_W
  | FCVT_RDN_D_W_32D  => fun _ => fct7_FCVT_D_W
  | FCVT_RUP_D_W_32D  => fun _ => fct7_FCVT_D_W
  | FCVT_RMM_D_W_32D  => fun _ => fct7_FCVT_D_W
  | FCVT_DYN_D_W_32D  => fun _ => fct7_FCVT_D_W
  | FCVT_RNE_D_WU_32D => fun _ => fct7_FCVT_D_W
  | FCVT_RTZ_D_WU_32D => fun _ => fct7_FCVT_D_W
  | FCVT_RDN_D_WU_32D => fun _ => fct7_FCVT_D_W
  | FCVT_RUP_D_WU_32D => fun _ => fct7_FCVT_D_W
  | FCVT_RMM_D_WU_32D => fun _ => fct7_FCVT_D_W
  | FCVT_DYN_D_WU_32D => fun _ => fct7_FCVT_D_W
  | FADD_RNE_D_64D    => fun _ => fct7_FADD_D
  | FADD_RTZ_D_64D    => fun _ => fct7_FADD_D
  | FADD_RDN_D_64D    => fun _ => fct7_FADD_D
  | FADD_RUP_D_64D    => fun _ => fct7_FADD_D
  | FADD_RMM_D_64D    => fun _ => fct7_FADD_D
  | FADD_DYN_D_64D    => fun _ => fct7_FADD_D
  | FSUB_RNE_D_64D    => fun _ => fct7_FSUB_D
  | FSUB_RTZ_D_64D    => fun _ => fct7_FSUB_D
  | FSUB_RDN_D_64D    => fun _ => fct7_FSUB_D
  | FSUB_RUP_D_64D    => fun _ => fct7_FSUB_D
  | FSUB_RMM_D_64D    => fun _ => fct7_FSUB_D
  | FSUB_DYN_D_64D    => fun _ => fct7_FSUB_D
  | FMUL_RNE_D_64D    => fun _ => fct7_FMUL_D
  | FMUL_RTZ_D_64D    => fun _ => fct7_FMUL_D
  | FMUL_RDN_D_64D    => fun _ => fct7_FMUL_D
  | FMUL_RUP_D_64D    => fun _ => fct7_FMUL_D
  | FMUL_RMM_D_64D    => fun _ => fct7_FMUL_D
  | FMUL_DYN_D_64D    => fun _ => fct7_FMUL_D
  | FDIV_RNE_D_64D    => fun _ => fct7_FDIV_D
  | FDIV_RTZ_D_64D    => fun _ => fct7_FDIV_D
  | FDIV_RDN_D_64D    => fun _ => fct7_FDIV_D
  | FDIV_RUP_D_64D    => fun _ => fct7_FDIV_D
  | FDIV_RMM_D_64D    => fun _ => fct7_FDIV_D
  | FDIV_DYN_D_64D    => fun _ => fct7_FDIV_D
  | FSQRT_RNE_D_64D   => fun _ => fct7_FSQRT_D
  | FSQRT_RTZ_D_64D   => fun _ => fct7_FSQRT_D
  | FSQRT_RDN_D_64D   => fun _ => fct7_FSQRT_D
  | FSQRT_RUP_D_64D   => fun _ => fct7_FSQRT_D
  | FSQRT_RMM_D_64D   => fun _ => fct7_FSQRT_D
  | FSQRT_DYN_D_64D   => fun _ => fct7_FSQRT_D
  | FSGNJ_D_64D       => fun _ => fct7_FSGNJ_D
  | FSGNJN_D_64D      => fun _ => fct7_FSGNJ_D
  | FSGNJX_D_64D      => fun _ => fct7_FSGNJ_D
  | FMIN_D_64D        => fun _ => fct7_FMIN_D
  | FMAX_D_64D        => fun _ => fct7_FMIN_D
  | FCVT_RNE_S_D_64D  => fun _ => fct7_FCVT_S_D
  | FCVT_RTZ_S_D_64D  => fun _ => fct7_FCVT_S_D
  | FCVT_RDN_S_D_64D  => fun _ => fct7_FCVT_S_D
  | FCVT_RUP_S_D_64D  => fun _ => fct7_FCVT_S_D
  | FCVT_RMM_S_D_64D  => fun _ => fct7_FCVT_S_D
  | FCVT_DYN_S_D_64D  => fun _ => fct7_FCVT_S_D
  | FCVT_RNE_D_S_64D  => fun _ => fct7_FCVT_D_S
  | FCVT_RTZ_D_S_64D  => fun _ => fct7_FCVT_D_S
  | FCVT_RDN_D_S_64D  => fun _ => fct7_FCVT_D_S
  | FCVT_RUP_D_S_64D  => fun _ => fct7_FCVT_D_S
  | FCVT_RMM_D_S_64D  => fun _ => fct7_FCVT_D_S
  | FCVT_DYN_D_S_64D  => fun _ => fct7_FCVT_D_S
  | FEQ_D_64D         => fun _ => fct7_FEQ_D
  | FLT_D_64D         => fun _ => fct7_FEQ_D
  | FLE_D_64D         => fun _ => fct7_FEQ_D
  | FCLASS_D_64D      => fun _ => fct7_FCLASS_D
  | FCVT_RNE_W_D_64D  => fun _ => fct7_FCVT_W_D
  | FCVT_RTZ_W_D_64D  => fun _ => fct7_FCVT_W_D
  | FCVT_RDN_W_D_64D  => fun _ => fct7_FCVT_W_D
  | FCVT_RUP_W_D_64D  => fun _ => fct7_FCVT_W_D
  | FCVT_RMM_W_D_64D  => fun _ => fct7_FCVT_W_D
  | FCVT_DYN_W_D_64D  => fun _ => fct7_FCVT_W_D
  | FCVT_RNE_WU_D_64D => fun _ => fct7_FCVT_W_D
  | FCVT_RTZ_WU_D_64D => fun _ => fct7_FCVT_W_D
  | FCVT_RDN_WU_D_64D => fun _ => fct7_FCVT_W_D
  | FCVT_RUP_WU_D_64D => fun _ => fct7_FCVT_W_D
  | FCVT_RMM_WU_D_64D => fun _ => fct7_FCVT_W_D
  | FCVT_DYN_WU_D_64D => fun _ => fct7_FCVT_W_D
  | FCVT_RNE_D_W_64D  => fun _ => fct7_FCVT_D_W
  | FCVT_RTZ_D_W_64D  => fun _ => fct7_FCVT_D_W
  | FCVT_RDN_D_W_64D  => fun _ => fct7_FCVT_D_W
  | FCVT_RUP_D_W_64D  => fun _ => fct7_FCVT_D_W
  | FCVT_RMM_D_W_64D  => fun _ => fct7_FCVT_D_W
  | FCVT_DYN_D_W_64D  => fun _ => fct7_FCVT_D_W
  | FCVT_RNE_D_WU_64D => fun _ => fct7_FCVT_D_W
  | FCVT_RTZ_D_WU_64D => fun _ => fct7_FCVT_D_W
  | FCVT_RDN_D_WU_64D => fun _ => fct7_FCVT_D_W
  | FCVT_RUP_D_WU_64D => fun _ => fct7_FCVT_D_W
  | FCVT_RMM_D_WU_64D => fun _ => fct7_FCVT_D_W
  | FCVT_DYN_D_WU_64D => fun _ => fct7_FCVT_D_W
  | FCVT_RNE_L_D_64D  => fun _ => fct7_FCVT_W_D
  | FCVT_RTZ_L_D_64D  => fun _ => fct7_FCVT_W_D
  | FCVT_RDN_L_D_64D  => fun _ => fct7_FCVT_W_D
  | FCVT_RUP_L_D_64D  => fun _ => fct7_FCVT_W_D
  | FCVT_RMM_L_D_64D  => fun _ => fct7_FCVT_W_D
  | FCVT_DYN_L_D_64D  => fun _ => fct7_FCVT_W_D
  | FCVT_RNE_LU_D_64D => fun _ => fct7_FCVT_W_D
  | FCVT_RTZ_LU_D_64D => fun _ => fct7_FCVT_W_D
  | FCVT_RDN_LU_D_64D => fun _ => fct7_FCVT_W_D
  | FCVT_RUP_LU_D_64D => fun _ => fct7_FCVT_W_D
  | FCVT_RMM_LU_D_64D => fun _ => fct7_FCVT_W_D
  | FCVT_DYN_LU_D_64D => fun _ => fct7_FCVT_W_D
  | FMV_X_D_64D       => fun _ => fct7_FCLASS_D
  | FCVT_RNE_D_L_64D  => fun _ => fct7_FCVT_D_W
  | FCVT_RTZ_D_L_64D  => fun _ => fct7_FCVT_D_W
  | FCVT_RDN_D_L_64D  => fun _ => fct7_FCVT_D_W
  | FCVT_RUP_D_L_64D  => fun _ => fct7_FCVT_D_W
  | FCVT_RMM_D_L_64D  => fun _ => fct7_FCVT_D_W
  | FCVT_DYN_D_L_64D  => fun _ => fct7_FCVT_D_W
  | FCVT_RNE_D_LU_64D => fun _ => fct7_FCVT_D_W
  | FCVT_RTZ_D_LU_64D => fun _ => fct7_FCVT_D_W
  | FCVT_RDN_D_LU_64D => fun _ => fct7_FCVT_D_W
  | FCVT_RUP_D_LU_64D => fun _ => fct7_FCVT_D_W
  | FCVT_RMM_D_LU_64D => fun _ => fct7_FCVT_D_W
  | FCVT_DYN_D_LU_64D => fun _ => fct7_FCVT_D_W
  | FMV_D_X_64D       => fun _ => fct7_FMV_D_X
  | FADD_RNE_Q_32Q    => fun _ => fct7_FADD_Q
  | FADD_RTZ_Q_32Q    => fun _ => fct7_FADD_Q
  | FADD_RDN_Q_32Q    => fun _ => fct7_FADD_Q
  | FADD_RUP_Q_32Q    => fun _ => fct7_FADD_Q
  | FADD_RMM_Q_32Q    => fun _ => fct7_FADD_Q
  | FADD_DYN_Q_32Q    => fun _ => fct7_FADD_Q
  | FSUB_RNE_Q_32Q    => fun _ => fct7_FSUB_Q
  | FSUB_RTZ_Q_32Q    => fun _ => fct7_FSUB_Q
  | FSUB_RDN_Q_32Q    => fun _ => fct7_FSUB_Q
  | FSUB_RUP_Q_32Q    => fun _ => fct7_FSUB_Q
  | FSUB_RMM_Q_32Q    => fun _ => fct7_FSUB_Q
  | FSUB_DYN_Q_32Q    => fun _ => fct7_FSUB_Q
  | FMUL_RNE_Q_32Q    => fun _ => fct7_FMUL_Q
  | FMUL_RTZ_Q_32Q    => fun _ => fct7_FMUL_Q
  | FMUL_RDN_Q_32Q    => fun _ => fct7_FMUL_Q
  | FMUL_RUP_Q_32Q    => fun _ => fct7_FMUL_Q
  | FMUL_RMM_Q_32Q    => fun _ => fct7_FMUL_Q
  | FMUL_DYN_Q_32Q    => fun _ => fct7_FMUL_Q
  | FDIV_RNE_Q_32Q    => fun _ => fct7_FDIV_Q
  | FDIV_RTZ_Q_32Q    => fun _ => fct7_FDIV_Q
  | FDIV_RDN_Q_32Q    => fun _ => fct7_FDIV_Q
  | FDIV_RUP_Q_32Q    => fun _ => fct7_FDIV_Q
  | FDIV_RMM_Q_32Q    => fun _ => fct7_FDIV_Q
  | FDIV_DYN_Q_32Q    => fun _ => fct7_FDIV_Q
  | FSQRT_RNE_Q_32Q   => fun _ => fct7_FSQRT_Q
  | FSQRT_RTZ_Q_32Q   => fun _ => fct7_FSQRT_Q
  | FSQRT_RDN_Q_32Q   => fun _ => fct7_FSQRT_Q
  | FSQRT_RUP_Q_32Q   => fun _ => fct7_FSQRT_Q
  | FSQRT_RMM_Q_32Q   => fun _ => fct7_FSQRT_Q
  | FSQRT_DYN_Q_32Q   => fun _ => fct7_FSQRT_Q
  | FSGNJ_Q_32Q       => fun _ => fct7_FSGNJ_Q
  | FSGNJN_Q_32Q      => fun _ => fct7_FSGNJ_Q
  | FSGNJX_Q_32Q      => fun _ => fct7_FSGNJ_Q
  | FMIN_Q_32Q        => fun _ => fct7_FMIN_Q
  | FMAX_Q_32Q        => fun _ => fct7_FMIN_Q
  | FCVT_RNE_S_Q_32Q  => fun _ => fct7_FCVT_S_D
  | FCVT_RTZ_S_Q_32Q  => fun _ => fct7_FCVT_S_D
  | FCVT_RDN_S_Q_32Q  => fun _ => fct7_FCVT_S_D
  | FCVT_RUP_S_Q_32Q  => fun _ => fct7_FCVT_S_D
  | FCVT_RMM_S_Q_32Q  => fun _ => fct7_FCVT_S_D
  | FCVT_DYN_S_Q_32Q  => fun _ => fct7_FCVT_S_D
  | FCVT_RNE_Q_S_32Q  => fun _ => fct7_FCVT_Q_S
  | FCVT_RTZ_Q_S_32Q  => fun _ => fct7_FCVT_Q_S
  | FCVT_RDN_Q_S_32Q  => fun _ => fct7_FCVT_Q_S
  | FCVT_RUP_Q_S_32Q  => fun _ => fct7_FCVT_Q_S
  | FCVT_RMM_Q_S_32Q  => fun _ => fct7_FCVT_Q_S
  | FCVT_DYN_Q_S_32Q  => fun _ => fct7_FCVT_Q_S
  | FCVT_RNE_D_Q_32Q  => fun _ => fct7_FCVT_D_Q
  | FCVT_RTZ_D_Q_32Q  => fun _ => fct7_FCVT_D_Q
  | FCVT_RDN_D_Q_32Q  => fun _ => fct7_FCVT_D_Q
  | FCVT_RUP_D_Q_32Q  => fun _ => fct7_FCVT_D_Q
  | FCVT_RMM_D_Q_32Q  => fun _ => fct7_FCVT_D_Q
  | FCVT_DYN_D_Q_32Q  => fun _ => fct7_FCVT_D_Q
  | FCVT_RNE_Q_D_32Q  => fun _ => fct7_FCVT_Q_D
  | FCVT_RTZ_Q_D_32Q  => fun _ => fct7_FCVT_Q_D
  | FCVT_RDN_Q_D_32Q  => fun _ => fct7_FCVT_Q_D
  | FCVT_RUP_Q_D_32Q  => fun _ => fct7_FCVT_Q_D
  | FCVT_RMM_Q_D_32Q  => fun _ => fct7_FCVT_Q_D
  | FCVT_DYN_Q_D_32Q  => fun _ => fct7_FCVT_Q_D
  | FEQ_Q_32Q         => fun _ => fct7_FEQ_Q
  | FLT_Q_32Q         => fun _ => fct7_FEQ_Q
  | FLE_Q_32Q         => fun _ => fct7_FEQ_Q
  | FCLASS_Q_32Q      => fun _ => fct7_FCLASS_Q
  | FCVT_RNE_W_Q_32Q  => fun _ => fct7_FCVT_X_Q
  | FCVT_RTZ_W_Q_32Q  => fun _ => fct7_FCVT_X_Q
  | FCVT_RDN_W_Q_32Q  => fun _ => fct7_FCVT_X_Q
  | FCVT_RUP_W_Q_32Q  => fun _ => fct7_FCVT_X_Q
  | FCVT_RMM_W_Q_32Q  => fun _ => fct7_FCVT_X_Q
  | FCVT_DYN_W_Q_32Q  => fun _ => fct7_FCVT_X_Q
  | FCVT_RNE_WU_Q_32Q => fun _ => fct7_FCVT_X_Q
  | FCVT_RTZ_WU_Q_32Q => fun _ => fct7_FCVT_X_Q
  | FCVT_RDN_WU_Q_32Q => fun _ => fct7_FCVT_X_Q
  | FCVT_RUP_WU_Q_32Q => fun _ => fct7_FCVT_X_Q
  | FCVT_RMM_WU_Q_32Q => fun _ => fct7_FCVT_X_Q
  | FCVT_DYN_WU_Q_32Q => fun _ => fct7_FCVT_X_Q
  | FCVT_RNE_Q_W_32Q  => fun _ => fct7_FCVT_Q_X
  | FCVT_RTZ_Q_W_32Q  => fun _ => fct7_FCVT_Q_X
  | FCVT_RDN_Q_W_32Q  => fun _ => fct7_FCVT_Q_X
  | FCVT_RUP_Q_W_32Q  => fun _ => fct7_FCVT_Q_X
  | FCVT_RMM_Q_W_32Q  => fun _ => fct7_FCVT_Q_X
  | FCVT_DYN_Q_W_32Q  => fun _ => fct7_FCVT_Q_X
  | FCVT_RNE_Q_WU_32Q => fun _ => fct7_FCVT_Q_X
  | FCVT_RTZ_Q_WU_32Q => fun _ => fct7_FCVT_Q_X
  | FCVT_RDN_Q_WU_32Q => fun _ => fct7_FCVT_Q_X
  | FCVT_RUP_Q_WU_32Q => fun _ => fct7_FCVT_Q_X
  | FCVT_RMM_Q_WU_32Q => fun _ => fct7_FCVT_Q_X
  | FCVT_DYN_Q_WU_32Q => fun _ => fct7_FCVT_Q_X
  | FADD_RNE_Q_64Q    => fun _ => fct7_FADD_Q
  | FADD_RTZ_Q_64Q    => fun _ => fct7_FADD_Q
  | FADD_RDN_Q_64Q    => fun _ => fct7_FADD_Q
  | FADD_RUP_Q_64Q    => fun _ => fct7_FADD_Q
  | FADD_RMM_Q_64Q    => fun _ => fct7_FADD_Q
  | FADD_DYN_Q_64Q    => fun _ => fct7_FADD_Q
  | FSUB_RNE_Q_64Q    => fun _ => fct7_FSUB_Q
  | FSUB_RTZ_Q_64Q    => fun _ => fct7_FSUB_Q
  | FSUB_RDN_Q_64Q    => fun _ => fct7_FSUB_Q
  | FSUB_RUP_Q_64Q    => fun _ => fct7_FSUB_Q
  | FSUB_RMM_Q_64Q    => fun _ => fct7_FSUB_Q
  | FSUB_DYN_Q_64Q    => fun _ => fct7_FSUB_Q
  | FMUL_RNE_Q_64Q    => fun _ => fct7_FMUL_Q
  | FMUL_RTZ_Q_64Q    => fun _ => fct7_FMUL_Q
  | FMUL_RDN_Q_64Q    => fun _ => fct7_FMUL_Q
  | FMUL_RUP_Q_64Q    => fun _ => fct7_FMUL_Q
  | FMUL_RMM_Q_64Q    => fun _ => fct7_FMUL_Q
  | FMUL_DYN_Q_64Q    => fun _ => fct7_FMUL_Q
  | FDIV_RNE_Q_64Q    => fun _ => fct7_FDIV_Q
  | FDIV_RTZ_Q_64Q    => fun _ => fct7_FDIV_Q
  | FDIV_RDN_Q_64Q    => fun _ => fct7_FDIV_Q
  | FDIV_RUP_Q_64Q    => fun _ => fct7_FDIV_Q
  | FDIV_RMM_Q_64Q    => fun _ => fct7_FDIV_Q
  | FDIV_DYN_Q_64Q    => fun _ => fct7_FDIV_Q
  | FSQRT_RNE_Q_64Q   => fun _ => fct7_FSQRT_Q
  | FSQRT_RTZ_Q_64Q   => fun _ => fct7_FSQRT_Q
  | FSQRT_RDN_Q_64Q   => fun _ => fct7_FSQRT_Q
  | FSQRT_RUP_Q_64Q   => fun _ => fct7_FSQRT_Q
  | FSQRT_RMM_Q_64Q   => fun _ => fct7_FSQRT_Q
  | FSQRT_DYN_Q_64Q   => fun _ => fct7_FSQRT_Q
  | FSGNJ_Q_64Q       => fun _ => fct7_FSGNJ_Q
  | FSGNJN_Q_64Q      => fun _ => fct7_FSGNJ_Q
  | FSGNJX_Q_64Q      => fun _ => fct7_FSGNJ_Q
  | FMIN_Q_64Q        => fun _ => fct7_FMIN_Q
  | FMAX_Q_64Q        => fun _ => fct7_FMIN_Q
  | FCVT_RNE_S_Q_64Q  => fun _ => fct7_FCVT_S_D
  | FCVT_RTZ_S_Q_64Q  => fun _ => fct7_FCVT_S_D
  | FCVT_RDN_S_Q_64Q  => fun _ => fct7_FCVT_S_D
  | FCVT_RUP_S_Q_64Q  => fun _ => fct7_FCVT_S_D
  | FCVT_RMM_S_Q_64Q  => fun _ => fct7_FCVT_S_D
  | FCVT_DYN_S_Q_64Q  => fun _ => fct7_FCVT_S_D
  | FCVT_RNE_Q_S_64Q  => fun _ => fct7_FCVT_Q_S
  | FCVT_RTZ_Q_S_64Q  => fun _ => fct7_FCVT_Q_S
  | FCVT_RDN_Q_S_64Q  => fun _ => fct7_FCVT_Q_S
  | FCVT_RUP_Q_S_64Q  => fun _ => fct7_FCVT_Q_S
  | FCVT_RMM_Q_S_64Q  => fun _ => fct7_FCVT_Q_S
  | FCVT_DYN_Q_S_64Q  => fun _ => fct7_FCVT_Q_S
  | FCVT_RNE_D_Q_64Q  => fun _ => fct7_FCVT_D_Q
  | FCVT_RTZ_D_Q_64Q  => fun _ => fct7_FCVT_D_Q
  | FCVT_RDN_D_Q_64Q  => fun _ => fct7_FCVT_D_Q
  | FCVT_RUP_D_Q_64Q  => fun _ => fct7_FCVT_D_Q
  | FCVT_RMM_D_Q_64Q  => fun _ => fct7_FCVT_D_Q
  | FCVT_DYN_D_Q_64Q  => fun _ => fct7_FCVT_D_Q
  | FCVT_RNE_Q_D_64Q  => fun _ => fct7_FCVT_Q_D
  | FCVT_RTZ_Q_D_64Q  => fun _ => fct7_FCVT_Q_D
  | FCVT_RDN_Q_D_64Q  => fun _ => fct7_FCVT_Q_D
  | FCVT_RUP_Q_D_64Q  => fun _ => fct7_FCVT_Q_D
  | FCVT_RMM_Q_D_64Q  => fun _ => fct7_FCVT_Q_D
  | FCVT_DYN_Q_D_64Q  => fun _ => fct7_FCVT_Q_D
  | FEQ_Q_64Q         => fun _ => fct7_FEQ_Q
  | FLT_Q_64Q         => fun _ => fct7_FEQ_Q
  | FLE_Q_64Q         => fun _ => fct7_FEQ_Q
  | FCLASS_Q_64Q      => fun _ => fct7_FCLASS_Q
  | FCVT_RNE_W_Q_64Q  => fun _ => fct7_FCVT_X_Q
  | FCVT_RTZ_W_Q_64Q  => fun _ => fct7_FCVT_X_Q
  | FCVT_RDN_W_Q_64Q  => fun _ => fct7_FCVT_X_Q
  | FCVT_RUP_W_Q_64Q  => fun _ => fct7_FCVT_X_Q
  | FCVT_RMM_W_Q_64Q  => fun _ => fct7_FCVT_X_Q
  | FCVT_DYN_W_Q_64Q  => fun _ => fct7_FCVT_X_Q
  | FCVT_RNE_WU_Q_64Q => fun _ => fct7_FCVT_X_Q
  | FCVT_RTZ_WU_Q_64Q => fun _ => fct7_FCVT_X_Q
  | FCVT_RDN_WU_Q_64Q => fun _ => fct7_FCVT_X_Q
  | FCVT_RUP_WU_Q_64Q => fun _ => fct7_FCVT_X_Q
  | FCVT_RMM_WU_Q_64Q => fun _ => fct7_FCVT_X_Q
  | FCVT_DYN_WU_Q_64Q => fun _ => fct7_FCVT_X_Q
  | FCVT_RNE_Q_W_64Q  => fun _ => fct7_FCVT_Q_X
  | FCVT_RTZ_Q_W_64Q  => fun _ => fct7_FCVT_Q_X
  | FCVT_RDN_Q_W_64Q  => fun _ => fct7_FCVT_Q_X
  | FCVT_RUP_Q_W_64Q  => fun _ => fct7_FCVT_Q_X
  | FCVT_RMM_Q_W_64Q  => fun _ => fct7_FCVT_Q_X
  | FCVT_DYN_Q_W_64Q  => fun _ => fct7_FCVT_Q_X
  | FCVT_RNE_Q_WU_64Q => fun _ => fct7_FCVT_Q_X
  | FCVT_RTZ_Q_WU_64Q => fun _ => fct7_FCVT_Q_X
  | FCVT_RDN_Q_WU_64Q => fun _ => fct7_FCVT_Q_X
  | FCVT_RUP_Q_WU_64Q => fun _ => fct7_FCVT_Q_X
  | FCVT_RMM_Q_WU_64Q => fun _ => fct7_FCVT_Q_X
  | FCVT_DYN_Q_WU_64Q => fun _ => fct7_FCVT_Q_X
  | FCVT_RNE_L_Q_64Q  => fun _ => fct7_FCVT_X_Q
  | FCVT_RTZ_L_Q_64Q  => fun _ => fct7_FCVT_X_Q
  | FCVT_RDN_L_Q_64Q  => fun _ => fct7_FCVT_X_Q
  | FCVT_RUP_L_Q_64Q  => fun _ => fct7_FCVT_X_Q
  | FCVT_RMM_L_Q_64Q  => fun _ => fct7_FCVT_X_Q
  | FCVT_DYN_L_Q_64Q  => fun _ => fct7_FCVT_X_Q
  | FCVT_RNE_LU_Q_64Q => fun _ => fct7_FCVT_X_Q
  | FCVT_RTZ_LU_Q_64Q => fun _ => fct7_FCVT_X_Q
  | FCVT_RDN_LU_Q_64Q => fun _ => fct7_FCVT_X_Q
  | FCVT_RUP_LU_Q_64Q => fun _ => fct7_FCVT_X_Q
  | FCVT_RMM_LU_Q_64Q => fun _ => fct7_FCVT_X_Q
  | FCVT_DYN_LU_Q_64Q => fun _ => fct7_FCVT_X_Q
  | FCVT_RNE_Q_L_64Q  => fun _ => fct7_FCVT_Q_X
  | FCVT_RTZ_Q_L_64Q  => fun _ => fct7_FCVT_Q_X
  | FCVT_RDN_Q_L_64Q  => fun _ => fct7_FCVT_Q_X
  | FCVT_RUP_Q_L_64Q  => fun _ => fct7_FCVT_Q_X
  | FCVT_RMM_Q_L_64Q  => fun _ => fct7_FCVT_Q_X
  | FCVT_DYN_Q_L_64Q  => fun _ => fct7_FCVT_Q_X
  | FCVT_RNE_Q_LU_64Q => fun _ => fct7_FCVT_Q_X
  | FCVT_RTZ_Q_LU_64Q => fun _ => fct7_FCVT_Q_X
  | FCVT_RDN_Q_LU_64Q => fun _ => fct7_FCVT_Q_X
  | FCVT_RUP_Q_LU_64Q => fun _ => fct7_FCVT_Q_X
  | FCVT_RMM_Q_LU_64Q => fun _ => fct7_FCVT_Q_X
  | FCVT_DYN_Q_LU_64Q => fun _ => fct7_FCVT_Q_X
  | _                 => fun _ => False_rec _ _
  end); try reflexivity; simpl in e; inversion e.
Defined.

Definition sample_instruction :=
  Ob~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0.

Compute bits_t 7.

Definition getFields : UInternalFunction reg_t empty_ext_fn_t := {{
  fun (inst : bits_t 32) : struct_t inst_field =>
  inst[|5`d0| :+ 7]
}}.

Compute (sample_instruction [|5`d0| :+  7]).

Record subfield_properties := {
  first_bit : nat;
  length : nat
}.

Record field_properties := {
  is_sign_extended : bool;
  shift : nat;
  field_subfields : list subfield_properties
}.

Definition get_field_properties (f : instruction_field) :=
  match f with
  | opcode => {|
      is_sign_extended := false;
      shift            := 0;
      field_subfields  := {| first_bit := 0 ; length := 7 |}::[]
    |}
  | rd     => {|
      is_sign_extended := false;
      shift            := 0;
      field_subfields  := {| first_bit := 7 ; length := 5 |}::[]
    |}
  | rs1    => {|
      is_sign_extended := false;
      shift            := 0;
      field_subfields  := {| first_bit := 15; length := 5 |}::[]
    |}
  | rs2    => {|
      is_sign_extended := false;
      shift            := 0;
      field_subfields  := {| first_bit := 20; length := 5 |}::[]
    |}
  | rs3    => {|
      is_sign_extended := false;
      shift            := 0;
      field_subfields  := {| first_bit := 27; length := 5 |}::[]
    |}
  | fct2 => {|
      is_sign_extended := false;
      shift            := 0;
      field_subfields  := {| first_bit := 25; length := 2 |}::[]
    |}
  | fct3 => {|
      is_sign_extended := false;
      shift            := 0;
      field_subfields  := {| first_bit := 12; length := 3 |}::[]
    |}
  | fct7 => {|
      is_sign_extended := false;
      shift            := 0;
      field_subfields  := {| first_bit := 25; length := 7 |}::[]
    |}
  | immI   => {|
      is_sign_extended := true;
      shift            := 0;
      field_subfields  := {| first_bit := 20; length := 12 |}::[]
    |}
  | immS   => {|
      is_sign_extended := true;
      shift            := 0;
      field_subfields  :=
        {| first_bit := 25; length := 7 |}::
        {| first_bit := 7 ; length := 5 |}::[]
    |}
  | immB   => {|
      is_sign_extended := true;
      shift            := 1;
      field_subfields  :=
        {| first_bit := 31; length := 1 |}::
        {| first_bit := 7 ; length := 1 |}::
        {| first_bit := 25; length := 6 |}::
        {| first_bit := 8 ; length := 4 |}::[]
    |}
  | immU   => {|
      is_sign_extended := false;
      shift            := 12;
      field_subfields  := {| first_bit := 12; length := 20 |}::[];
    |}
  | immJ   => {|
      is_sign_extended := true;
      shift            := 1;
      field_subfields  :=
        {| first_bit := 31; length := 1  |}::
        {| first_bit := 12; length := 8  |}::
        {| first_bit := 20; length := 1  |}::
        {| first_bit := 21; length := 10 |}::[]
    |}
  end.

Definition get_field_information_quantity (f : instruction_field) :=
  let fp := get_field_properties f in
  let sfs := field_subfields fp in
  (shift fp) + (fold_left (fun c sfp => c + length sfp) sfs 0).

Record instruction_struct := {
  identification_fields := lis
  data_fields :=
}

Record RType_struct := {
  RType
  RType_opcode : bits_t (get_field_information_quantity opcode);
  RType_rd     : bits_t (get_field_information_quantity rd    );
  RType_fct3   : bits_t (get_field_information_quantity fct3  );
  RType_rs1    : bits_t (get_field_information_quantity rs1   );
  RType_rs2    : bits_t (get_field_information_quantity rs2   );
  RType_fct7   : bits_t (get_field_information_quantity fct7  )
}.

Record R4Type_struct := {
  R4Type_opcode : bits_t (get_field_information_quantity opcode);
  R4Type_rd     : bits_t (get_field_information_quantity rd    );
  R4Type_fct3   : bits_t (get_field_information_quantity fct3  );
  R4Type_rs1    : bits_t (get_field_information_quantity rs1   );
  R4Type_rs2    : bits_t (get_field_information_quantity rs2   );
  R4Type_fct2   : bits_t (get_field_information_quantity fct2  );
  R4Type_rs3    : bits_t (get_field_information_quantity rs3   )
}.

Record IType_struct := {
  IType_opcode : bits_t (get_field_information_quantity opcode);
  IType_rd     : bits_t (get_field_information_quantity rd    );
  IType_fct3   : bits_t (get_field_information_quantity fct3  );
  IType_rs1    : bits_t (get_field_information_quantity rs1   );
  IType_immI   : bits_t (get_field_information_quantity immI  )
}.

Record SType_struct := {
  SType_opcode : bits_t (get_field_information_quantity opcode);
  SType_immS   : bits_t (get_field_information_quantity immS  );
  SType_fct3   : bits_t (get_field_information_quantity fct3  );
  SType_rs1    : bits_t (get_field_information_quantity rs1   );
  SType_rs2    : bits_t (get_field_information_quantity rs2   )
}.

Record BType_struct := {
  BType_opcode : bits_t (get_field_information_quantity opcode);
  BType_immB   : bits_t (get_field_information_quantity immB  );
  BType_fct3   : bits_t (get_field_information_quantity fct3  );
  BType_rs1    : bits_t (get_field_information_quantity rs1   );
  BType_rs2    : bits_t (get_field_information_quantity rs2   )
}.

Record UType_struct := {
  UType_opcode : bits_t (get_field_information_quantity opcode);
  UType_rd     : bits_t (get_field_information_quantity rd    );
  UType_immU   : bits_t (get_field_information_quantity immU  )
}.

Record JType_struct := {
  JType_opcode : bits_t (get_field_information_quantity opcode);
  JType_rd     : bits_t (get_field_information_quantity rd    );
  JType_immJ   : bits_t (get_field_information_quantity immJ  )
}.

Inductive instruction_struct :=
| RTypeStruct  (s : RType_struct )
| R4TypeStruct (s : R4Type_struct)
| ITypeStruct  (s : IType_struct )
| STypeStruct  (s : SType_struct )
| BTypeStruct  (s : BType_struct )
| UTypeStruct  (s : UType_struct )
| JTypeStruct  (s : JType_struct ).
