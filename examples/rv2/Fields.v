Require Import Koika.Frontend Koika.Std Koika.Parsing.
Require Import Instructions.

Inductive instruction_type :=
| RType | R4Type | IType | SType | BType | UType | JType.

Definition get_instruction_type (i : instruction) :=
  match i with
  | RV32I_instruction x =>
    match x with
    | LUI_32I    => UType | AUIPC_32I => UType | JAL_32I   => JType
    | JALR_32I   => IType | BEQ_32I   => BType | BNE_32I   => BType
    | BLT_32I    => BType | BGE_32I   => BType | BLTU_32I  => BType
    | BGEU_32I   => BType | LB_32I    => IType | LH_32I    => IType
    | LW_32I     => IType | LBU_32I   => IType | LHU_32I   => IType
    | SB_32I     => SType | SH_32I    => SType | SW_32I    => SType
    | ADDI_32I   => IType | SLTI_32I  => IType | SLTIU_32I => IType
    | XORI_32I   => IType | ORI_32I   => IType | ANDI_32I  => IType
    | SLLI_32I   => IType | SRLI_32I  => IType | SRAI_32I  => IType
    | ADD_32I    => RType | SUB_32I   => RType | SLL_32I   => RType
    | SLT_32I    => RType | SLTU_32I  => RType | XOR_32I   => RType
    | SRL_32I    => RType | SRA_32I   => RType | OR_32I    => RType
    | AND_32I    => RType | FENCE_32I => IType | ECALL_32I => IType
    | EBREAK_32I => IType
    end
  | RV64I_instruction x =>
    match x with
    | LUI_64I    => UType | AUIPC_64I => UType | JAL_64I   => JType
    | JALR_64I   => IType | BEQ_64I   => BType | BNE_64I   => BType
    | BLT_64I    => BType | BGE_64I   => BType | BLTU_64I  => BType
    | BGEU_64I   => BType | LB_64I    => IType | LH_64I    => IType
    | LW_64I     => IType | LBU_64I   => IType | LHU_64I   => IType
    | SB_64I     => SType | SH_64I    => SType | SW_64I    => SType
    | ADDI_64I   => IType | SLTI_64I  => IType | SLTIU_64I => IType
    | XORI_64I   => IType | ORI_64I   => IType | ANDI_64I  => IType
    | SLLI_64I   => IType | SRLI_64I  => IType | SRAI_64I  => IType
    | ADD_64I    => RType | SUB_64I   => RType | SLL_64I   => RType
    | SLT_64I    => RType | SLTU_64I  => RType | XOR_64I   => RType
    | SRL_64I    => RType | SRA_64I   => RType | OR_64I    => RType
    | AND_64I    => RType | FENCE_64I => IType | ECALL_64I => IType
    | EBREAK_64I => IType | LWU_64I   => IType | LD_64I    => IType
    | SD_64I     => SType | ADDIW_64I => IType | SLLIW_64I => IType
    | SRLIW_64I  => IType | SRAIW_64I => IType | ADDW_64I  => RType
    | SUBW_64I   => RType | SLLW_64I  => RType | SRLW_64I  => RType
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
    | CSRRW_32Zicsr  => IType | CSRRS_32Zicsr  => IType
    | CSRRC_32Zicsr  => IType | CSRRWI_32Zicsr => IType
    | CSRRSI_32Zicsr => IType | CSRRCI_32Zicsr => IType
    end
  | RV64Zicsr_instruction x =>
    match x with
    | CSRRW_64Zicsr  => IType | CSRRS_64Zicsr  => IType
    | CSRRC_64Zicsr  => IType | CSRRWI_64Zicsr => IType
    | CSRRSI_64Zicsr => IType | CSRRCI_64Zicsr => IType
    end
  | RV32M_instruction x =>
    match x with
    | MUL_32M   => RType | MULH_32M => RType | MULHSU_32M => RType
    | MULHU_32M => RType | DIV_32M  => RType | DIVU_32M   => RType
    | REM_32M   => RType | REMU_32M => RType
    end
  | RV64M_instruction x =>
    match x with
    | MUL_64M   => RType | MULH_64M  => RType | MULHSU_64M => RType
    | MULHU_64M => RType | DIV_64M   => RType | DIVU_64M   => RType
    | REM_64M   => RType | REMU_64M  => RType | MULW_64M   => RType
    | DIVW_64M  => RType | DIVUW_64M => RType | REMW_64M   => RType
    | REMUW_64M => RType
    end
  | RV32A_instruction x =>
    match x with
    | LR_W_00_32A      => RType | LR_W_01_32A      => RType
    | LR_W_10_32A      => RType | LR_W_11_32A      => RType
    | SC_W_00_32A      => RType | SC_W_01_32A      => RType
    | SC_W_10_32A      => RType | SC_W_11_32A      => RType
    | AMOSWAP_W_00_32A => RType | AMOSWAP_W_01_32A => RType
    | AMOSWAP_W_10_32A => RType | AMOSWAP_W_11_32A => RType
    | AMOADD_W_00_32A  => RType | AMOADD_W_01_32A  => RType
    | AMOADD_W_10_32A  => RType | AMOADD_W_11_32A  => RType
    | AMOXOR_W_00_32A  => RType | AMOXOR_W_01_32A  => RType
    | AMOXOR_W_10_32A  => RType | AMOXOR_W_11_32A  => RType
    | AMOAND_W_00_32A  => RType | AMOAND_W_01_32A  => RType
    | AMOAND_W_10_32A  => RType | AMOAND_W_11_32A  => RType
    | AMOOR_W_00_32A   => RType | AMOOR_W_01_32A   => RType
    | AMOOR_W_10_32A   => RType | AMOOR_W_11_32A   => RType
    | AMOMIN_W_00_32A  => RType | AMOMIN_W_01_32A  => RType
    | AMOMIN_W_10_32A  => RType | AMOMIN_W_11_32A  => RType
    | AMOMAX_W_00_32A  => RType | AMOMAX_W_01_32A  => RType
    | AMOMAX_W_10_32A  => RType | AMOMAX_W_11_32A  => RType
    | AMOMINU_W_00_32A => RType | AMOMINU_W_01_32A => RType
    | AMOMINU_W_10_32A => RType | AMOMINU_W_11_32A => RType
    | AMOMAXU_W_00_32A => RType | AMOMAXU_W_01_32A => RType
    | AMOMAXU_W_10_32A => RType | AMOMAXU_W_11_32A => RType
    end
  | RV64A_instruction x =>
    match x with
    | LR_W_00_64A      => RType | LR_W_01_64A      => RType
    | LR_W_10_64A      => RType | LR_W_11_64A      => RType
    | SC_W_00_64A      => RType | SC_W_01_64A      => RType
    | SC_W_10_64A      => RType | SC_W_11_64A      => RType
    | AMOSWAP_W_00_64A => RType | AMOSWAP_W_01_64A => RType
    | AMOSWAP_W_10_64A => RType | AMOSWAP_W_11_64A => RType
    | AMOADD_W_00_64A  => RType | AMOADD_W_01_64A  => RType
    | AMOADD_W_10_64A  => RType | AMOADD_W_11_64A  => RType
    | AMOXOR_W_00_64A  => RType | AMOXOR_W_01_64A  => RType
    | AMOXOR_W_10_64A  => RType | AMOXOR_W_11_64A  => RType
    | AMOAND_W_00_64A  => RType | AMOAND_W_01_64A  => RType
    | AMOAND_W_10_64A  => RType | AMOAND_W_11_64A  => RType
    | AMOOR_W_00_64A   => RType | AMOOR_W_01_64A   => RType
    | AMOOR_W_10_64A   => RType | AMOOR_W_11_64A   => RType
    | AMOMIN_W_00_64A  => RType | AMOMIN_W_01_64A  => RType
    | AMOMIN_W_10_64A  => RType | AMOMIN_W_11_64A  => RType
    | AMOMAX_W_00_64A  => RType | AMOMAX_W_01_64A  => RType
    | AMOMAX_W_10_64A  => RType | AMOMAX_W_11_64A  => RType
    | AMOMINU_W_00_64A => RType | AMOMINU_W_01_64A => RType
    | AMOMINU_W_10_64A => RType | AMOMINU_W_11_64A => RType
    | AMOMAXU_W_00_64A => RType | AMOMAXU_W_01_64A => RType
    | AMOMAXU_W_10_64A => RType | AMOMAXU_W_11_64A => RType
    | LR_D_00_64A      => RType | LR_D_01_64A      => RType
    | LR_D_10_64A      => RType | LR_D_11_64A      => RType
    | SC_D_00_64A      => RType | SC_D_01_64A      => RType
    | SC_D_10_64A      => RType | SC_D_11_64A      => RType
    | AMOSWAP_D_00_64A => RType | AMOSWAP_D_01_64A => RType
    | AMOSWAP_D_10_64A => RType | AMOSWAP_D_11_64A => RType
    | AMOADD_D_00_64A  => RType | AMOADD_D_01_64A  => RType
    | AMOADD_D_10_64A  => RType | AMOADD_D_11_64A  => RType
    | AMOXOR_D_00_64A  => RType | AMOXOR_D_01_64A  => RType
    | AMOXOR_D_10_64A  => RType | AMOXOR_D_11_64A  => RType
    | AMOAND_D_00_64A  => RType | AMOAND_D_01_64A  => RType
    | AMOAND_D_10_64A  => RType | AMOAND_D_11_64A  => RType
    | AMOOR_D_00_64A   => RType | AMOOR_D_01_64A   => RType
    | AMOOR_D_10_64A   => RType | AMOOR_D_11_64A   => RType
    | AMOMIN_D_00_64A  => RType | AMOMIN_D_01_64A  => RType
    | AMOMIN_D_10_64A  => RType | AMOMIN_D_11_64A  => RType
    | AMOMAX_D_00_64A  => RType | AMOMAX_D_01_64A  => RType
    | AMOMAX_D_10_64A  => RType | AMOMAX_D_11_64A  => RType
    | AMOMINU_D_00_64A => RType | AMOMINU_D_01_64A => RType
    | AMOMINU_D_10_64A => RType | AMOMINU_D_11_64A => RType
    | AMOMAXU_D_00_64A => RType | AMOMAXU_D_01_64A => RType
    | AMOMAXU_D_10_64A => RType | AMOMAXU_D_11_64A => RType
    end
  | RV32F_instruction x =>
    match x with
    | FLW_32F       => IType  | FSW_32F       => SType
    | FMADD_S_32F   => R4Type | FMSUB_S_32F   => R4Type
    | FNMSUB_S_32F  => R4Type | FNMADD_S_32F  => R4Type
    | FADD_S_32F    => RType  | FSUB_S_32F    => RType
    | FMUL_S_32F    => RType  | FDIV_S_32F    => RType
    | FSQRT_S_32F   => RType  | FSGNJ_S_32F   => RType
    | FSGNJN_S_32F  => RType  | FSGNJX_S_32F  => RType
    | FMIN_S_32F    => RType  | FMAX_S_32F    => RType
    | FCVT_W_S_32F  => RType  | FCVT_WU_S_32F => RType
    | FMV_X_W_32F   => RType  | FEQ_S_32F     => RType
    | FLT_S_32F     => RType  | FLE_S_32F     => RType
    | FCLASS_S_32F  => RType  | FCVT_S_W_32F  => RType
    | FCVT_S_WU_32F => RType  | FMV_W_X_32F   => RType
    end
  | RV64F_instruction x =>
    match x with
    | FLW_64F       => IType  | FSW_64F       => SType
    | FMADD_S_64F   => R4Type | FMSUB_S_64F   => R4Type
    | FNMSUB_S_64F  => R4Type | FNMADD_S_64F  => R4Type
    | FADD_S_64F    => RType  | FSUB_S_64F    => RType
    | FMUL_S_64F    => RType  | FDIV_S_64F    => RType
    | FSQRT_S_64F   => RType  | FSGNJ_S_64F   => RType
    | FSGNJN_S_64F  => RType  | FSGNJX_S_64F  => RType
    | FMIN_S_64F    => RType  | FMAX_S_64F    => RType
    | FCVT_W_S_64F  => RType  | FCVT_WU_S_64F => RType
    | FMV_X_W_64F   => RType  | FEQ_S_64F     => RType
    | FLT_S_64F     => RType  | FLE_S_64F     => RType
    | FCLASS_S_64F  => RType  | FCVT_S_W_64F  => RType
    | FCVT_S_WU_64F => RType  | FMV_W_X_64F   => RType
    | FCVT_L_S_64F  => RType  | FCVT_LU_S_64F => RType
    | FCVT_S_L_64F  => RType  | FCVT_S_LU_64F => RType
    end
  | RV32D_instruction x =>
    match x with
    | FLD_32D      => IType  | FSD_32D       => SType
    | FMADD_D_32D  => R4Type | FMSUB_D_32D   => R4Type
    | FNMSUB_D_32D => R4Type | FNMADD_D_32D  => R4Type
    | FADD_D_32D   => RType  | FSUB_D_32D    => RType
    | FMUL_D_32D   => RType  | FDIV_D_32D    => RType
    | FSQRT_D_32D  => RType  | FSGNJ_D_32D   => RType
    | FSGNJN_D_32D => RType  | FSGNJX_D_32D  => RType
    | FMIN_D_32D   => RType  | FMAX_D_32D    => RType
    | FCVT_S_D_32D => RType  | FCVT_D_S_32D  => RType
    | FEQ_D_32D    => RType  | FLT_D_32D     => RType
    | FLE_D_32D    => RType  | FCLASS_D_32D  => RType
    | FCVT_W_D_32D => RType  | FCVT_WU_D_32D => RType
    | FCVT_D_W_32D => RType  | FCVT_D_WU_32D => RType
    end
  | RV64D_instruction x =>
    match x with
    | FLD_64D       => IType  | FSD_64D       => SType
    | FMADD_D_64D   => R4Type | FMSUB_D_64D   => R4Type
    | FNMSUB_D_64D  => R4Type | FNMADD_D_64D  => R4Type
    | FADD_D_64D    => RType  | FSUB_D_64D    => RType
    | FMUL_D_64D    => RType  | FDIV_D_64D    => RType
    | FSQRT_D_64D   => RType  | FSGNJ_D_64D   => RType
    | FSGNJN_D_64D  => RType  | FSGNJX_D_64D  => RType
    | FMIN_D_64D    => RType  | FMAX_D_64D    => RType
    | FCVT_S_D_64D  => RType  | FCVT_D_S_64D  => RType
    | FEQ_D_64D     => RType  | FLT_D_64D     => RType
    | FLE_D_64D     => RType  | FCLASS_D_64D  => RType
    | FCVT_W_D_64D  => RType  | FCVT_WU_D_64D => RType
    | FCVT_D_W_64D  => RType  | FCVT_D_WU_64D => RType
    | FCVT_L_D_64D  => RType  | FCVT_LU_D_64D => RType
    | FMV_X_D_64D   => RType  | FCVT_D_L_64D  => RType
    | FCVT_D_LU_64D => RType  | FMV_D_X_64D   => RType
    end
  | RV32Q_instruction x =>
    match x with
    | FLQ_32Q      => IType  | FSQ_32Q       => SType
    | FMADD_Q_32Q  => R4Type | FMSUB_Q_32Q   => R4Type
    | FNMSUB_Q_32Q => R4Type | FNMADD_Q_32Q  => R4Type
    | FADD_Q_32Q   => RType  | FSUB_Q_32Q    => RType
    | FMUL_Q_32Q   => RType  | FDIV_Q_32Q    => RType
    | FSQRT_Q_32Q  => RType  | FSGNJ_Q_32Q   => RType
    | FSGNJN_Q_32Q => RType  | FSGNJX_Q_32Q  => RType
    | FMIN_Q_32Q   => RType  | FMAX_Q_32Q    => RType
    | FCVT_S_Q_32Q => RType  | FCVT_Q_S_32Q  => RType
    | FCVT_D_Q_32Q => RType  | FCVT_Q_D_32Q  => RType
    | FEQ_Q_32Q    => RType  | FLT_Q_32Q     => RType
    | FLE_Q_32Q    => RType  | FCLASS_Q_32Q  => RType
    | FCVT_W_Q_32Q => RType  | FCVT_WU_Q_32Q => RType
    | FCVT_Q_W_32Q => RType  | FCVT_Q_WU_32Q => RType
    end
  | RV64Q_instruction x =>
    match x with
    | FLQ_64Q      => IType  | FSQ_64Q       => SType
    | FMADD_Q_64Q  => R4Type | FMSUB_Q_64Q   => R4Type
    | FNMSUB_Q_64Q => R4Type | FNMADD_Q_64Q  => R4Type
    | FADD_Q_64Q   => RType  | FSUB_Q_64Q    => RType
    | FMUL_Q_64Q   => RType  | FDIV_Q_64Q    => RType
    | FSQRT_Q_64Q  => RType  | FSGNJ_Q_64Q   => RType
    | FSGNJN_Q_64Q => RType  | FSGNJX_Q_64Q  => RType
    | FMIN_Q_64Q   => RType  | FMAX_Q_64Q    => RType
    | FCVT_S_Q_64Q => RType  | FCVT_Q_S_64Q  => RType
    | FCVT_D_Q_64Q => RType  | FCVT_Q_D_64Q  => RType
    | FEQ_Q_64Q    => RType  | FLT_Q_64Q     => RType
    | FLE_Q_64Q    => RType  | FCLASS_Q_64Q  => RType
    | FCVT_W_Q_64Q => RType  | FCVT_WU_Q_64Q => RType
    | FCVT_Q_W_64Q => RType  | FCVT_Q_WU_64Q => RType
    | FCVT_L_Q_64Q => RType  | FCVT_LU_Q_64Q => RType
    | FCVT_Q_L_64Q => RType  | FCVT_Q_LU_64Q => RType
    end
  end.

Inductive field :=
| opcode | fct2 | fct3 | fct7 | rs1 | rs2 | rs3 | rd | immI | immS | immB | immU
| immJ.

Definition has_opcode (t : instruction_type) :=
  match t with
  | RType  => true
  | R4Type => true
  | IType  => true
  | SType  => true
  | BType  => true
  | UType  => true
  | JType  => true
  end.

Definition has_fct2 (t : instruction_type) :=
  match t with
  | RType  => false
  | R4Type => true
  | IType  => false
  | SType  => false
  | BType  => false
  | UType  => false
  | JType  => false
  end.

Definition has_fct3 (t : instruction_type) :=
  match t with
  | RType  => true
  | R4Type => true
  | IType  => true
  | SType  => true
  | BType  => true
  | UType  => false
  | JType  => false
  end.

Definition has_fct7 (t : instruction_type) :=
  match t with
  | RType  => true
  | R4Type => false
  | IType  => false
  | SType  => false
  | BType  => false
  | UType  => false
  | JType  => false
  end.

Definition has_rs1 (t : instruction_type) :=
  match t with
  | RType  => true
  | R4Type => true
  | IType  => true
  | SType  => true
  | BType  => true
  | UType  => false
  | JType  => false
  end.

Definition has_rs2 (t : instruction_type) :=
  match t with
  | RType  => true
  | R4Type => true
  | IType  => false
  | SType  => true
  | BType  => true
  | UType  => false
  | JType  => false
  end.

Definition has_rs3 (t : instruction_type) :=
  match t with
  | RType  => false
  | R4Type => true
  | IType  => false
  | SType  => false
  | BType  => false
  | UType  => false
  | JType  => false
  end.

Definition has_rd (t : instruction_type) :=
  match t with
  | RType  => true
  | R4Type => true
  | IType  => true
  | SType  => false
  | BType  => false
  | UType  => true
  | JType  => true
  end.

Definition has_immI (t : instruction_type) :=
  match t with
  | RType  => false
  | R4Type => false
  | IType  => true
  | SType  => false
  | BType  => false
  | UType  => false
  | JType  => false
  end.

Definition has_immS (t : instruction_type) :=
  match t with
  | RType  => false
  | R4Type => false
  | IType  => false
  | SType  => true
  | BType  => false
  | UType  => false
  | JType  => false
  end.

Definition has_immB (t : instruction_type) :=
  match t with
  | RType  => false
  | R4Type => false
  | IType  => false
  | SType  => false
  | BType  => true
  | UType  => false
  | JType  => false
  end.

Definition has_immU (t : instruction_type) :=
  match t with
  | RType  => false
  | R4Type => false
  | IType  => false
  | SType  => false
  | BType  => false
  | UType  => true
  | JType  => false
  end.

Definition has_immJ (t : instruction_type) :=
  match t with
  | RType  => false
  | R4Type => false
  | IType  => false
  | SType  => false
  | BType  => false
  | UType  => false
  | JType  => true
  end.

Definition instruction_type_fields (t : instruction_type) :=
  app (if has_opcode t then [opcode] else []) (
  app (if has_fct2 t then [fct2] else []) (
  app (if has_fct3 t then [fct3] else []) (
  app (if has_fct7 t then [fct7] else []) (
  app (if has_rs1 t then [rs1] else []) (
  app (if has_rs2 t then [rs2] else []) (
  app (if has_rs3 t then [rs3] else []) (
  app (if has_rd t then [rd] else []) (
  app (if has_immI t then [immI] else []) (
  app (if has_immS t then [immS] else []) (
  app (if has_immB t then [immB] else []) (
  app (if has_immU t then [immU] else []) (
  if has_immJ t then [immJ] else [])))))))))))).

Definition is_field_identifier (f : field) :=
  match f with
  | opcode => true
  | fct2   => true
  | fct3   => true
  | fct7   => true
  | rs1    => false
  | rs2    => false
  | rs3    => false
  | rd     => false
  | immI   => false
  | immS   => false
  | immB   => false
  | immU   => false
  | immJ   => false
  end.

Definition is_field_data (f : field) := negb (is_field_identifier f).

Inductive opcode_name :=
| opcode_OP        | opcode_JALR  | opcode_LOAD   | opcode_OP_IMM
| opcode_MISC_MEM  | opcode_STORE | opcode_BRANCH | opcode_LUI
| opcode_AUIPC     | opcode_JAL   | opcode_SYSTEM | opcode_OP_32
| opcode_OP_IMM_32 | opcode_AMO   | opcode_OP_FP  | opcode_MADD
| opcode_MSUB      | opcode_NMSUB | opcode_NMADD  | opcode_LOAD_FP
| opcode_STORE_FP.

Definition opcode_bin (o : opcode_name) :=
  match o with
  | opcode_OP        => Ob~0~1~1~0~0~1~1 | opcode_JALR    => Ob~1~1~0~0~1~1~1
  | opcode_LOAD      => Ob~0~0~0~0~0~1~1 | opcode_OP_IMM  => Ob~0~0~1~0~0~1~1
  | opcode_MISC_MEM  => Ob~0~0~0~1~1~1~1 | opcode_STORE   => Ob~0~1~0~0~0~1~1
  | opcode_BRANCH    => Ob~1~1~0~0~0~1~1 | opcode_LUI     => Ob~0~1~1~0~1~1~1
  | opcode_AUIPC     => Ob~0~0~1~0~1~1~1 | opcode_JAL     => Ob~1~1~0~1~1~1~1
  | opcode_SYSTEM    => Ob~1~1~1~0~0~1~1 | opcode_OP_32   => Ob~0~1~1~1~0~1~1
  | opcode_OP_IMM_32 => Ob~0~0~1~1~0~1~1 | opcode_AMO     => Ob~0~1~0~1~1~1~1
  | opcode_OP_FP     => Ob~1~0~1~0~0~1~1 | opcode_MADD    => Ob~1~0~0~0~0~1~1
  | opcode_MSUB      => Ob~1~0~0~0~1~1~1 | opcode_NMSUB   => Ob~1~0~0~1~0~1~1
  | opcode_NMADD     => Ob~1~0~0~1~1~1~1 | opcode_LOAD_FP => Ob~0~0~0~0~1~1~1
  | opcode_STORE_FP  => Ob~0~1~0~0~1~1~1
  end.

Definition instruction_opcode
  (i : {i : instruction | has_opcode (get_instruction_type i) = true})
:=
  match proj1_sig i with
  | RV32I_instruction x =>
    match x with
    | LUI_32I   => opcode_LUI    | AUIPC_32I  => opcode_AUIPC
    | JAL_32I   => opcode_JAL    | JALR_32I   => opcode_JALR
    | BEQ_32I   => opcode_BRANCH | BNE_32I    => opcode_BRANCH
    | BLT_32I   => opcode_BRANCH | BGE_32I    => opcode_BRANCH
    | BLTU_32I  => opcode_BRANCH | BGEU_32I   => opcode_BRANCH
    | LB_32I    => opcode_LOAD   | LH_32I     => opcode_LOAD
    | LW_32I    => opcode_LOAD   | LBU_32I    => opcode_LOAD
    | LHU_32I   => opcode_LOAD   | SB_32I     => opcode_STORE
    | SH_32I    => opcode_STORE  | SW_32I     => opcode_STORE
    | ADDI_32I  => opcode_OP_IMM | SLTI_32I   => opcode_OP_IMM
    | SLTIU_32I => opcode_OP_IMM | XORI_32I   => opcode_OP_IMM
    | ORI_32I   => opcode_OP_IMM | ANDI_32I   => opcode_OP_IMM
    | SLLI_32I  => opcode_OP_IMM | SRLI_32I   => opcode_OP_IMM
    | SRAI_32I  => opcode_OP_IMM | ADD_32I    => opcode_OP
    | SUB_32I   => opcode_OP     | SLL_32I    => opcode_OP
    | SLT_32I   => opcode_OP     | SLTU_32I   => opcode_OP
    | XOR_32I   => opcode_OP     | SRL_32I    => opcode_OP
    | SRA_32I   => opcode_OP     | OR_32I     => opcode_OP
    | AND_32I   => opcode_OP     | FENCE_32I  => opcode_MISC_MEM
    | ECALL_32I => opcode_SYSTEM | EBREAK_32I => opcode_SYSTEM
    end
  | RV64I_instruction x =>
    match x with
    | LUI_64I    => opcode_LUI       | AUIPC_64I  => opcode_AUIPC
    | JAL_64I    => opcode_JAL       | JALR_64I   => opcode_JALR
    | BEQ_64I    => opcode_BRANCH    | BNE_64I    => opcode_BRANCH
    | BLT_64I    => opcode_BRANCH    | BGE_64I    => opcode_BRANCH
    | BLTU_64I   => opcode_BRANCH    | BGEU_64I   => opcode_BRANCH
    | LB_64I     => opcode_LOAD      | LH_64I     => opcode_LOAD
    | LW_64I     => opcode_LOAD      | LBU_64I    => opcode_LOAD
    | LHU_64I    => opcode_LOAD      | SB_64I     => opcode_STORE
    | SH_64I     => opcode_STORE     | SW_64I     => opcode_STORE
    | ADDI_64I   => opcode_OP_IMM    | SLTI_64I   => opcode_OP_IMM
    | SLTIU_64I  => opcode_OP_IMM    | XORI_64I   => opcode_OP_IMM
    | ORI_64I    => opcode_OP_IMM    | ANDI_64I   => opcode_OP_IMM
    | SLLI_64I   => opcode_OP_IMM    | SRLI_64I   => opcode_OP_IMM
    | SRAI_64I   => opcode_OP_IMM    | ADD_64I    => opcode_OP
    | SUB_64I    => opcode_OP        | SLL_64I    => opcode_OP
    | SLT_64I    => opcode_OP        | SLTU_64I   => opcode_OP
    | XOR_64I    => opcode_OP        | SRL_64I    => opcode_OP
    | SRA_64I    => opcode_OP        | OR_64I     => opcode_OP
    | AND_64I    => opcode_OP        | FENCE_64I  => opcode_MISC_MEM
    | ECALL_64I  => opcode_SYSTEM    | EBREAK_64I => opcode_SYSTEM
    | LWU_64I    => opcode_LOAD      | LD_64I     => opcode_LOAD
    | SD_64I     => opcode_STORE     | ADDIW_64I  => opcode_OP_IMM_32
    | SLLIW_64I  => opcode_OP_IMM_32 | SRLIW_64I  => opcode_OP_IMM_32
    | SRAIW_64I  => opcode_OP_IMM_32 | ADDW_64I   => opcode_OP_32
    | SUBW_64I   => opcode_OP_32     | SLLW_64I   => opcode_OP_32
    | SRLW_64I   => opcode_OP_32     | SRAW_64I   => opcode_OP_32
    end
  | RV32Zifencei_instruction x =>
    match x with
    | FENCE_I_32Zifencei => opcode_MISC_MEM
    end
  | RV64Zifencei_instruction x =>
    match x with
    | FENCE_I_64Zifencei => opcode_MISC_MEM
    end
  | RV32Zicsr_instruction x =>
    match x with
    | CSRRW_32Zicsr  => opcode_SYSTEM | CSRRS_32Zicsr  => opcode_SYSTEM
    | CSRRC_32Zicsr  => opcode_SYSTEM | CSRRWI_32Zicsr => opcode_SYSTEM
    | CSRRSI_32Zicsr => opcode_SYSTEM | CSRRCI_32Zicsr => opcode_SYSTEM
    end
  | RV64Zicsr_instruction x =>
    match x with
    | CSRRW_64Zicsr  => opcode_SYSTEM | CSRRS_64Zicsr  => opcode_SYSTEM
    | CSRRC_64Zicsr  => opcode_SYSTEM | CSRRWI_64Zicsr => opcode_SYSTEM
    | CSRRSI_64Zicsr => opcode_SYSTEM | CSRRCI_64Zicsr => opcode_SYSTEM
    end
  | RV32M_instruction x =>
    match x with
    | MUL_32M   => opcode_OP | MULH_32M => opcode_OP | MULHSU_32M => opcode_OP
    | MULHU_32M => opcode_OP | DIV_32M  => opcode_OP | DIVU_32M   => opcode_OP
    | REM_32M   => opcode_OP | REMU_32M => opcode_OP
    end
  | RV64M_instruction x =>
    match x with
    | MUL_64M    => opcode_OP    | MULH_64M  => opcode_OP
    | MULHSU_64M => opcode_OP    | MULHU_64M => opcode_OP
    | DIV_64M    => opcode_OP    | DIVU_64M  => opcode_OP
    | REM_64M    => opcode_OP    | REMU_64M  => opcode_OP
    | MULW_64M   => opcode_OP_32 | DIVW_64M  => opcode_OP_32
    | DIVUW_64M  => opcode_OP_32 | REMW_64M  => opcode_OP_32
    | REMUW_64M  => opcode_OP_32
    end
  | RV32A_instruction x =>
    match x with
    | LR_W_00_32A      => opcode_AMO | LR_W_01_32A      => opcode_AMO
    | LR_W_10_32A      => opcode_AMO | LR_W_11_32A      => opcode_AMO
    | SC_W_00_32A      => opcode_AMO | SC_W_01_32A      => opcode_AMO
    | SC_W_10_32A      => opcode_AMO | SC_W_11_32A      => opcode_AMO
    | AMOSWAP_W_00_32A => opcode_AMO | AMOSWAP_W_01_32A => opcode_AMO
    | AMOSWAP_W_10_32A => opcode_AMO | AMOSWAP_W_11_32A => opcode_AMO
    | AMOADD_W_00_32A  => opcode_AMO | AMOADD_W_01_32A  => opcode_AMO
    | AMOADD_W_10_32A  => opcode_AMO | AMOADD_W_11_32A  => opcode_AMO
    | AMOXOR_W_00_32A  => opcode_AMO | AMOXOR_W_01_32A  => opcode_AMO
    | AMOXOR_W_10_32A  => opcode_AMO | AMOXOR_W_11_32A  => opcode_AMO
    | AMOAND_W_00_32A  => opcode_AMO | AMOAND_W_01_32A  => opcode_AMO
    | AMOAND_W_10_32A  => opcode_AMO | AMOAND_W_11_32A  => opcode_AMO
    | AMOOR_W_00_32A   => opcode_AMO | AMOOR_W_01_32A   => opcode_AMO
    | AMOOR_W_10_32A   => opcode_AMO | AMOOR_W_11_32A   => opcode_AMO
    | AMOMIN_W_00_32A  => opcode_AMO | AMOMIN_W_01_32A  => opcode_AMO
    | AMOMIN_W_10_32A  => opcode_AMO | AMOMIN_W_11_32A  => opcode_AMO
    | AMOMAX_W_00_32A  => opcode_AMO | AMOMAX_W_01_32A  => opcode_AMO
    | AMOMAX_W_10_32A  => opcode_AMO | AMOMAX_W_11_32A  => opcode_AMO
    | AMOMINU_W_00_32A => opcode_AMO | AMOMINU_W_01_32A => opcode_AMO
    | AMOMINU_W_10_32A => opcode_AMO | AMOMINU_W_11_32A => opcode_AMO
    | AMOMAXU_W_00_32A => opcode_AMO | AMOMAXU_W_01_32A => opcode_AMO
    | AMOMAXU_W_10_32A => opcode_AMO | AMOMAXU_W_11_32A => opcode_AMO
    end
  | RV64A_instruction x =>
    match x with
    | LR_W_00_64A      => opcode_AMO | LR_W_01_64A      => opcode_AMO
    | LR_W_10_64A      => opcode_AMO | LR_W_11_64A      => opcode_AMO
    | SC_W_00_64A      => opcode_AMO | SC_W_01_64A      => opcode_AMO
    | SC_W_10_64A      => opcode_AMO | SC_W_11_64A      => opcode_AMO
    | AMOSWAP_W_00_64A => opcode_AMO | AMOSWAP_W_01_64A => opcode_AMO
    | AMOSWAP_W_10_64A => opcode_AMO | AMOSWAP_W_11_64A => opcode_AMO
    | AMOADD_W_00_64A  => opcode_AMO | AMOADD_W_01_64A  => opcode_AMO
    | AMOADD_W_10_64A  => opcode_AMO | AMOADD_W_11_64A  => opcode_AMO
    | AMOXOR_W_00_64A  => opcode_AMO | AMOXOR_W_01_64A  => opcode_AMO
    | AMOXOR_W_10_64A  => opcode_AMO | AMOXOR_W_11_64A  => opcode_AMO
    | AMOAND_W_00_64A  => opcode_AMO | AMOAND_W_01_64A  => opcode_AMO
    | AMOAND_W_10_64A  => opcode_AMO | AMOAND_W_11_64A  => opcode_AMO
    | AMOOR_W_00_64A   => opcode_AMO | AMOOR_W_01_64A   => opcode_AMO
    | AMOOR_W_10_64A   => opcode_AMO | AMOOR_W_11_64A   => opcode_AMO
    | AMOMIN_W_00_64A  => opcode_AMO | AMOMIN_W_01_64A  => opcode_AMO
    | AMOMIN_W_10_64A  => opcode_AMO | AMOMIN_W_11_64A  => opcode_AMO
    | AMOMAX_W_00_64A  => opcode_AMO | AMOMAX_W_01_64A  => opcode_AMO
    | AMOMAX_W_10_64A  => opcode_AMO | AMOMAX_W_11_64A  => opcode_AMO
    | AMOMINU_W_00_64A => opcode_AMO | AMOMINU_W_01_64A => opcode_AMO
    | AMOMINU_W_10_64A => opcode_AMO | AMOMINU_W_11_64A => opcode_AMO
    | AMOMAXU_W_00_64A => opcode_AMO | AMOMAXU_W_01_64A => opcode_AMO
    | AMOMAXU_W_10_64A => opcode_AMO | AMOMAXU_W_11_64A => opcode_AMO
    | LR_D_00_64A      => opcode_AMO | LR_D_01_64A      => opcode_AMO
    | LR_D_10_64A      => opcode_AMO | LR_D_11_64A      => opcode_AMO
    | SC_D_00_64A      => opcode_AMO | SC_D_01_64A      => opcode_AMO
    | SC_D_10_64A      => opcode_AMO | SC_D_11_64A      => opcode_AMO
    | AMOSWAP_D_00_64A => opcode_AMO | AMOSWAP_D_01_64A => opcode_AMO
    | AMOSWAP_D_10_64A => opcode_AMO | AMOSWAP_D_11_64A => opcode_AMO
    | AMOADD_D_00_64A  => opcode_AMO | AMOADD_D_01_64A  => opcode_AMO
    | AMOADD_D_10_64A  => opcode_AMO | AMOADD_D_11_64A  => opcode_AMO
    | AMOXOR_D_00_64A  => opcode_AMO | AMOXOR_D_01_64A  => opcode_AMO
    | AMOXOR_D_10_64A  => opcode_AMO | AMOXOR_D_11_64A  => opcode_AMO
    | AMOAND_D_00_64A  => opcode_AMO | AMOAND_D_01_64A  => opcode_AMO
    | AMOAND_D_10_64A  => opcode_AMO | AMOAND_D_11_64A  => opcode_AMO
    | AMOOR_D_00_64A   => opcode_AMO | AMOOR_D_01_64A   => opcode_AMO
    | AMOOR_D_10_64A   => opcode_AMO | AMOOR_D_11_64A   => opcode_AMO
    | AMOMIN_D_00_64A  => opcode_AMO | AMOMIN_D_01_64A  => opcode_AMO
    | AMOMIN_D_10_64A  => opcode_AMO | AMOMIN_D_11_64A  => opcode_AMO
    | AMOMAX_D_00_64A  => opcode_AMO | AMOMAX_D_01_64A  => opcode_AMO
    | AMOMAX_D_10_64A  => opcode_AMO | AMOMAX_D_11_64A  => opcode_AMO
    | AMOMINU_D_00_64A => opcode_AMO | AMOMINU_D_01_64A => opcode_AMO
    | AMOMINU_D_10_64A => opcode_AMO | AMOMINU_D_11_64A => opcode_AMO
    | AMOMAXU_D_00_64A => opcode_AMO | AMOMAXU_D_01_64A => opcode_AMO
    | AMOMAXU_D_10_64A => opcode_AMO | AMOMAXU_D_11_64A => opcode_AMO
    end
  | RV32F_instruction x =>
    match x with
    | FLW_32F       => opcode_LOAD_FP | FSW_32F       => opcode_STORE_FP
    | FMADD_S_32F   => opcode_MADD    | FMSUB_S_32F   => opcode_MSUB
    | FNMSUB_S_32F  => opcode_NMSUB   | FNMADD_S_32F  => opcode_NMADD
    | FADD_S_32F    => opcode_OP_FP   | FSUB_S_32F    => opcode_OP_FP
    | FMUL_S_32F    => opcode_OP_FP   | FDIV_S_32F    => opcode_OP_FP
    | FSQRT_S_32F   => opcode_OP_FP   | FSGNJ_S_32F   => opcode_OP_FP
    | FSGNJN_S_32F  => opcode_OP_FP   | FSGNJX_S_32F  => opcode_OP_FP
    | FMIN_S_32F    => opcode_OP_FP   | FMAX_S_32F    => opcode_OP_FP
    | FCVT_W_S_32F  => opcode_OP_FP   | FCVT_WU_S_32F => opcode_OP_FP
    | FMV_X_W_32F   => opcode_OP_FP   | FEQ_S_32F     => opcode_OP_FP
    | FLT_S_32F     => opcode_OP_FP   | FLE_S_32F     => opcode_OP_FP
    | FCLASS_S_32F  => opcode_OP_FP   | FCVT_S_W_32F  => opcode_OP_FP
    | FCVT_S_WU_32F => opcode_OP_FP   | FMV_W_X_32F   => opcode_OP_FP
    end
  | RV64F_instruction x =>
    match x with
    | FLW_64F       => opcode_LOAD_FP | FSW_64F       => opcode_LOAD_FP
    | FMADD_S_64F   => opcode_MADD    | FMSUB_S_64F   => opcode_MSUB
    | FNMSUB_S_64F  => opcode_NMSUB   | FNMADD_S_64F  => opcode_NMADD
    | FADD_S_64F    => opcode_OP_FP   | FSUB_S_64F    => opcode_OP_FP
    | FMUL_S_64F    => opcode_OP_FP   | FDIV_S_64F    => opcode_OP_FP
    | FSQRT_S_64F   => opcode_OP_FP   | FSGNJ_S_64F   => opcode_OP_FP
    | FSGNJN_S_64F  => opcode_OP_FP   | FSGNJX_S_64F  => opcode_OP_FP
    | FMIN_S_64F    => opcode_OP_FP   | FMAX_S_64F    => opcode_OP_FP
    | FCVT_W_S_64F  => opcode_OP_FP   | FCVT_WU_S_64F => opcode_OP_FP
    | FMV_X_W_64F   => opcode_OP_FP   | FEQ_S_64F     => opcode_OP_FP
    | FLT_S_64F     => opcode_OP_FP   | FLE_S_64F     => opcode_OP_FP
    | FCLASS_S_64F  => opcode_OP_FP   | FCVT_S_W_64F  => opcode_OP_FP
    | FCVT_S_WU_64F => opcode_OP_FP   | FMV_W_X_64F   => opcode_OP_FP
    | FCVT_L_S_64F  => opcode_OP_FP   | FCVT_LU_S_64F => opcode_OP_FP
    | FCVT_S_L_64F  => opcode_OP_FP   | FCVT_S_LU_64F => opcode_OP_FP
    end
  | RV32D_instruction x =>
    match x with
    | FLD_32D      => opcode_LOAD_FP | FSD_32D       => opcode_STORE_FP
    | FMADD_D_32D  => opcode_MADD    | FMSUB_D_32D   => opcode_MSUB
    | FNMSUB_D_32D => opcode_NMSUB   | FNMADD_D_32D  => opcode_NMADD
    | FADD_D_32D   => opcode_OP_FP   | FSUB_D_32D    => opcode_OP_FP
    | FMUL_D_32D   => opcode_OP_FP   | FDIV_D_32D    => opcode_OP_FP
    | FSQRT_D_32D  => opcode_OP_FP   | FSGNJ_D_32D   => opcode_OP_FP
    | FSGNJN_D_32D => opcode_OP_FP   | FSGNJX_D_32D  => opcode_OP_FP
    | FMIN_D_32D   => opcode_OP_FP   | FMAX_D_32D    => opcode_OP_FP
    | FCVT_S_D_32D => opcode_OP_FP   | FCVT_D_S_32D  => opcode_OP_FP
    | FEQ_D_32D    => opcode_OP_FP   | FLT_D_32D     => opcode_OP_FP
    | FLE_D_32D    => opcode_OP_FP   | FCLASS_D_32D  => opcode_OP_FP
    | FCVT_W_D_32D => opcode_OP_FP   | FCVT_WU_D_32D => opcode_OP_FP
    | FCVT_D_W_32D => opcode_OP_FP   | FCVT_D_WU_32D => opcode_OP_FP
    end
  | RV64D_instruction x =>
    match x with
    | FLD_64D       => opcode_LOAD_FP | FSD_64D       => opcode_STORE_FP
    | FMADD_D_64D   => opcode_MADD    | FMSUB_D_64D   => opcode_MSUB
    | FNMSUB_D_64D  => opcode_NMSUB   | FNMADD_D_64D  => opcode_NMADD
    | FADD_D_64D    => opcode_OP_FP   | FSUB_D_64D    => opcode_OP_FP
    | FMUL_D_64D    => opcode_OP_FP   | FDIV_D_64D    => opcode_OP_FP
    | FSQRT_D_64D   => opcode_OP_FP   | FSGNJ_D_64D   => opcode_OP_FP
    | FSGNJN_D_64D  => opcode_OP_FP   | FSGNJX_D_64D  => opcode_OP_FP
    | FMIN_D_64D    => opcode_OP_FP   | FMAX_D_64D    => opcode_OP_FP
    | FCVT_S_D_64D  => opcode_OP_FP   | FCVT_D_S_64D  => opcode_OP_FP
    | FEQ_D_64D     => opcode_OP_FP   | FLT_D_64D     => opcode_OP_FP
    | FLE_D_64D     => opcode_OP_FP   | FCLASS_D_64D  => opcode_OP_FP
    | FCVT_W_D_64D  => opcode_OP_FP   | FCVT_WU_D_64D => opcode_OP_FP
    | FCVT_D_W_64D  => opcode_OP_FP   | FCVT_D_WU_64D => opcode_OP_FP
    | FCVT_L_D_64D  => opcode_OP_FP   | FCVT_LU_D_64D => opcode_OP_FP
    | FMV_X_D_64D   => opcode_OP_FP   | FCVT_D_L_64D  => opcode_OP_FP
    | FCVT_D_LU_64D => opcode_OP_FP   | FMV_D_X_64D   => opcode_OP_FP
    end
  | RV32Q_instruction x =>
    match x with
    | FLQ_32Q      => opcode_LOAD_FP | FSQ_32Q       => opcode_STORE_FP
    | FMADD_Q_32Q  => opcode_MADD    | FMSUB_Q_32Q   => opcode_MSUB
    | FNMSUB_Q_32Q => opcode_NMSUB   | FNMADD_Q_32Q  => opcode_NMADD
    | FADD_Q_32Q   => opcode_OP_FP   | FSUB_Q_32Q    => opcode_OP_FP
    | FMUL_Q_32Q   => opcode_OP_FP   | FDIV_Q_32Q    => opcode_OP_FP
    | FSQRT_Q_32Q  => opcode_OP_FP   | FSGNJ_Q_32Q   => opcode_OP_FP
    | FSGNJN_Q_32Q => opcode_OP_FP   | FSGNJX_Q_32Q  => opcode_OP_FP
    | FMIN_Q_32Q   => opcode_OP_FP   | FMAX_Q_32Q    => opcode_OP_FP
    | FCVT_S_Q_32Q => opcode_OP_FP   | FCVT_Q_S_32Q  => opcode_OP_FP
    | FCVT_D_Q_32Q => opcode_OP_FP   | FCVT_Q_D_32Q  => opcode_OP_FP
    | FEQ_Q_32Q    => opcode_OP_FP   | FLT_Q_32Q     => opcode_OP_FP
    | FLE_Q_32Q    => opcode_OP_FP   | FCLASS_Q_32Q  => opcode_OP_FP
    | FCVT_W_Q_32Q => opcode_OP_FP   | FCVT_WU_Q_32Q => opcode_OP_FP
    | FCVT_Q_W_32Q => opcode_OP_FP   | FCVT_Q_WU_32Q => opcode_OP_FP
    end
  | RV64Q_instruction x =>
    match x with
    | FLQ_64Q      => opcode_LOAD_FP | FSQ_64Q       => opcode_STORE_FP
    | FMADD_Q_64Q  => opcode_MADD    | FMSUB_Q_64Q   => opcode_MSUB
    | FNMSUB_Q_64Q => opcode_NMSUB   | FNMADD_Q_64Q  => opcode_NMADD
    | FADD_Q_64Q   => opcode_OP_FP   | FSUB_Q_64Q    => opcode_OP_FP
    | FMUL_Q_64Q   => opcode_OP_FP   | FDIV_Q_64Q    => opcode_OP_FP
    | FSQRT_Q_64Q  => opcode_OP_FP   | FSGNJ_Q_64Q   => opcode_OP_FP
    | FSGNJN_Q_64Q => opcode_OP_FP   | FSGNJX_Q_64Q  => opcode_OP_FP
    | FMIN_Q_64Q   => opcode_OP_FP   | FMAX_Q_64Q    => opcode_OP_FP
    | FCVT_S_Q_64Q => opcode_OP_FP   | FCVT_Q_S_64Q  => opcode_OP_FP
    | FCVT_D_Q_64Q => opcode_OP_FP   | FCVT_Q_D_64Q  => opcode_OP_FP
    | FEQ_Q_64Q    => opcode_OP_FP   | FLT_Q_64Q     => opcode_OP_FP
    | FLE_Q_64Q    => opcode_OP_FP   | FCLASS_Q_64Q  => opcode_OP_FP
    | FCVT_W_Q_64Q => opcode_OP_FP   | FCVT_WU_Q_64Q => opcode_OP_FP
    | FCVT_Q_W_64Q => opcode_OP_FP   | FCVT_Q_WU_64Q => opcode_OP_FP
    | FCVT_L_Q_64Q => opcode_OP_FP   | FCVT_LU_Q_64Q => opcode_OP_FP
    | FCVT_Q_L_64Q => opcode_OP_FP   | FCVT_Q_LU_64Q => opcode_OP_FP
    end
  end.

Inductive fct3_type :=
| fct3_ADD      | fct3_SUB      | fct3_SLL     | fct3_SLT      | fct3_SLTU
| fct3_XOR      | fct3_SRL      | fct3_SRA     | fct3_OR       | fct3_AND
| fct3_LB       | fct3_LH       | fct3_LW      | fct3_LBU      | fct3_LHU
| fct3_SLTI     | fct3_SLTIU    | fct3_ADDI    | fct3_XORI     | fct3_ORI
| fct3_ANDI     | fct3_SLLI     | fct3_SRLI    | fct3_SRAI     | fct3_FENCE
| fct3_SB       | fct3_SH       | fct3_SW      | fct3_BEQ      | fct3_BNE
| fct3_BLT      | fct3_BGE      | fct3_BLTU    | fct3_BGEU     | fct3_PRIV
| fct3_ADDW     | fct3_SUBW     | fct3_SLLW    | fct3_SRLW     | fct3_SRAW
| fct3_LWU      | fct3_LD       | fct3_ADDIW   | fct3_SLLIW    | fct3_SRLIW
| fct3_SRAIW    | fct3_SD       | fct3_FENCE_I | fct3_CSRRW    | fct3_CSRRS
| fct3_CSRRC    | fct3_CSRRWI   | fct3_CSRRSI  | fct3_CSRRCI   | fct3_MUL
| fct3_MULH     | fct3_MULHSU   | fct3_MULHU   | fct3_DIV      | fct3_DIVU
| fct3_REM      | fct3_REMU     | fct3_MULW    | fct3_DIVW     | fct3_DIVUW
| fct3_REMW     | fct3_REMUW    | fct3_AMOW    | fct3_AMOD     | fct3_FSGNJ_S
| fct3_FSGNJN_S | fct3_FSGNJX_S | fct3_FMIN_S  | fct3_FMAX_S   | fct3_FMV_X_W
| fct3_FEQ_S    | fct3_FLT_S    | fct3_FLE_S   | fct3_FCLASS_S | fct3_FLW
| fct3_FSW.

Definition fct3_bin (f : fct3_type) :=
  match f with
  | fct3_ADD      => Ob~0~0~0 | fct3_SUB      => Ob~0~0~0
  | fct3_SLL      => Ob~0~0~1 | fct3_SLT      => Ob~0~1~0
  | fct3_SLTU     => Ob~0~1~1 | fct3_XOR      => Ob~1~0~0
  | fct3_SRL      => Ob~1~0~1 | fct3_SRA      => Ob~1~0~1
  | fct3_OR       => Ob~1~1~0 | fct3_AND      => Ob~1~1~1
  | fct3_LB       => Ob~0~0~0 | fct3_LH       => Ob~0~0~1
  | fct3_LW       => Ob~0~1~0 | fct3_LBU      => Ob~1~0~0
  | fct3_LHU      => Ob~1~0~1 | fct3_SLTI     => Ob~0~1~0
  | fct3_SLTIU    => Ob~0~1~1 | fct3_ADDI     => Ob~0~0~0
  | fct3_XORI     => Ob~1~0~0 | fct3_ORI      => Ob~1~1~0
  | fct3_ANDI     => Ob~1~1~1 | fct3_SLLI     => Ob~0~0~1
  | fct3_SRLI     => Ob~1~0~1 | fct3_SRAI     => Ob~1~0~1
  | fct3_FENCE    => Ob~0~0~0 | fct3_SB       => Ob~0~0~0
  | fct3_SH       => Ob~0~0~1 | fct3_SW       => Ob~0~1~0
  | fct3_BEQ      => Ob~0~0~0 | fct3_BNE      => Ob~0~0~1
  | fct3_BLT      => Ob~1~0~0 | fct3_BGE      => Ob~1~0~1
  | fct3_BLTU     => Ob~1~1~0 | fct3_BGEU     => Ob~1~1~1
  | fct3_PRIV     => Ob~0~0~0 | fct3_ADDW     => Ob~0~0~0
  | fct3_SUBW     => Ob~0~0~0 | fct3_SLLW     => Ob~0~0~1
  | fct3_SRLW     => Ob~1~0~1 | fct3_SRAW     => Ob~1~0~1
  | fct3_LWU      => Ob~1~1~0 | fct3_LD       => Ob~0~1~1
  | fct3_ADDIW    => Ob~0~0~0 | fct3_SLLIW    => Ob~0~0~1
  | fct3_SRLIW    => Ob~1~0~1 | fct3_SRAIW    => Ob~1~0~1
  | fct3_SD       => Ob~0~1~1 | fct3_FENCE_I  => Ob~0~0~1
  | fct3_CSRRW    => Ob~0~0~1 | fct3_CSRRS    => Ob~0~1~0
  | fct3_CSRRC    => Ob~0~1~1 | fct3_CSRRWI   => Ob~1~0~1
  | fct3_CSRRSI   => Ob~1~1~0 | fct3_CSRRCI   => Ob~1~1~1
  | fct3_MUL      => Ob~0~0~0 | fct3_MULH     => Ob~0~0~1
  | fct3_MULHSU   => Ob~0~1~0 | fct3_MULHU    => Ob~0~1~1
  | fct3_DIV      => Ob~1~0~0 | fct3_DIVU     => Ob~1~0~1
  | fct3_REM      => Ob~1~1~0 | fct3_REMU     => Ob~1~1~1
  | fct3_MULW     => Ob~0~0~0 | fct3_DIVW     => Ob~1~0~0
  | fct3_DIVUW    => Ob~1~0~1 | fct3_REMW     => Ob~1~1~0
  | fct3_REMUW    => Ob~1~1~1 | fct3_AMOW     => Ob~0~1~0
  | fct3_AMOD     => Ob~0~1~1 | fct3_FSGNJ_S  => Ob~0~0~0
  | fct3_FSGNJN_S => Ob~0~0~1 | fct3_FSGNJX_S => Ob~0~1~0
  | fct3_FMIN_S   => Ob~0~0~0 | fct3_FMAX_S   => Ob~0~0~1
  | fct3_FMV_X_W  => Ob~0~0~0 | fct3_FEQ_S    => Ob~0~1~0
  | fct3_FLT_S    => Ob~0~0~1 | fct3_FLE_S    => Ob~0~0~0
  | fct3_FCLASS_S => Ob~0~0~1 | fct3_FLW      => Ob~0~1~0
  | fct3_FSW      => Ob~0~1~0
  end.

Inductive fct7_type :=
| fct7_ADD        | fct7_SUB        | fct7_SLL        | fct7_SLT
| fct7_SLTU       | fct7_XOR        | fct7_SRL        | fct7_SRA
| fct7_OR         | fct7_AND        | fct7_ADDW       | fct7_SUBW
| fct7_SLLW       | fct7_SRLW       | fct7_SRAW       | fct7_SLLIW
| fct7_SRLIW      | fct7_SRAIW      | fct7_MUL        | fct7_MULH
| fct7_MULHSU     | fct7_MULHU      | fct7_DIV        | fct7_DIVU
| fct7_REM        | fct7_REMU       | fct7_MULW       | fct7_DIVW
| fct7_DIVUW      | fct7_REMW       | fct7_REMUW

| fct7_FADD_S
| fct7_FSUB_S     | fct7_FMUL_S     | fct7_FDIV_S     | fct7_FSQRT_S
| fct7_FSGNJ_S    | fct7_FMIN_S     | fct7_FCVT_W_S   | fct7_FMV_X_W
| fct7_FEQ_S      | fct7_FCLASS_S   | fct7_FCVT_S_W   | fct7_FMV_W_X

| fct7_FADD_D
| fct7_FSUB_D     | fct7_FMUL_D     | fct7_FDIV_D     | fct7_FSQRT_D
| fct7_FSGNJ_D    | fct7_FMIN_D     | fct7_FCVT_W_D   | fct7_FMV_D_W
| fct7_FEQ_D      | fct7_FCLASS_D   | fct7_FCVT_D_W   | fct7_FMV_W_D

| fct7_FADD_Q
| fct7_FSUB_Q     | fct7_FMUL_Q     | fct7_FDIV_Q     | fct7_FSQRT_Q
| fct7_FSGNJ_Q    | fct7_FMIN_Q     | fct7_FCVT_W_Q   | fct7_FMV_Q_W
| fct7_FEQ_Q      | fct7_FCLASS_Q   | fct7_FCVT_Q_W   | fct7_FMV_W_Q

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
  | fct7_SRAW       => Ob~0~1~0~0~0~0~0 | fct7_SLLIW      => Ob~0~0~0~0~0~0~0
  | fct7_SRLIW      => Ob~0~0~0~0~0~0~0 | fct7_SRAIW      => Ob~0~1~0~0~0~0~0
  | fct7_MUL        => Ob~0~0~0~0~0~0~1 | fct7_MULH       => Ob~0~0~0~0~0~0~1
  | fct7_MULHSU     => Ob~0~0~0~0~0~0~1 | fct7_MULHU      => Ob~0~0~0~0~0~0~1
  | fct7_DIV        => Ob~0~0~0~0~0~0~1 | fct7_DIVU       => Ob~0~0~0~0~0~0~1
  | fct7_REM        => Ob~0~0~0~0~0~0~1 | fct7_REMU       => Ob~0~0~0~0~0~0~1
  | fct7_MULW       => Ob~0~0~0~0~0~0~1 | fct7_DIVW       => Ob~0~0~0~0~0~0~1
  | fct7_DIVUW      => Ob~0~0~0~0~0~0~1 | fct7_REMW       => Ob~0~0~0~0~0~0~1
  | fct7_REMUW      => Ob~0~0~0~0~0~0~1

  | fct7_FADD_S     => Ob~0~0~0~0~0~0~0
  | fct7_FSUB_S     => Ob~0~0~0~0~1~0~0 | fct7_FMUL_S     => Ob~0~0~0~1~0~0~0
  | fct7_FDIV_S     => Ob~0~0~0~1~1~0~0 | fct7_FSQRT_S    => Ob~0~1~0~1~1~0~0
  | fct7_FSGNJ_S    => Ob~0~0~1~0~0~0~0 | fct7_FMIN_S     => Ob~0~0~1~0~1~0~0
  | fct7_FCVT_W_S   => Ob~1~1~0~0~0~0~0 | fct7_FMV_X_W    => Ob~1~1~1~0~0~0~0
  | fct7_FEQ_S      => Ob~1~0~1~0~0~0~0 | fct7_FCLASS_S   => Ob~1~1~1~0~0~0~0
  | fct7_FCVT_S_W   => Ob~1~1~0~1~0~0~0 | fct7_FMV_W_X    => Ob~1~1~1~1~0~0~0

  | fct7_FADD_D     => Ob~0~0~0~0~0~0~1
  | fct7_FSUB_D     => Ob~0~0~0~0~1~0~1 | fct7_FMUL_D     => Ob~0~0~0~1~0~0~1
  | fct7_FDIV_D     => Ob~0~0~0~1~1~0~1 | fct7_FSQRT_D    => Ob~0~1~0~1~1~0~1
  | fct7_FSGNJ_D    => Ob~0~0~1~0~0~0~1 | fct7_FMIN_D     => Ob~0~0~1~0~1~0~1
  | fct7_FCVT_W_D   => Ob~1~1~0~0~0~0~1 | fct7_FMV_D_W    => Ob~1~1~1~0~0~0~1
  | fct7_FEQ_D      => Ob~1~0~1~0~0~0~1 | fct7_FCLASS_D   => Ob~1~1~1~0~0~0~1
  | fct7_FCVT_D_W   => Ob~1~1~0~1~0~0~1 | fct7_FMV_W_D    => Ob~1~1~1~1~0~0~1

  | fct7_FADD_S     => Ob~0~0~0~0~0~1~1
  | fct7_FSUB_S     => Ob~0~0~0~0~1~1~1 | fct7_FMUL_S     => Ob~0~0~0~1~0~1~1
  | fct7_FDIV_S     => Ob~0~0~0~1~1~1~1 | fct7_FSQRT_S    => Ob~0~1~0~1~1~1~1
  | fct7_FSGNJ_S    => Ob~0~0~1~0~0~1~1 | fct7_FMIN_S     => Ob~0~0~1~0~1~1~1
  | fct7_FCVT_W_S   => Ob~1~1~0~0~0~1~1 | fct7_FMV_X_W    => Ob~1~1~1~0~0~1~1
  | fct7_FEQ_S      => Ob~1~0~1~0~0~1~1 | fct7_FCLASS_S   => Ob~1~1~1~0~0~1~1
  | fct7_FCVT_S_W   => Ob~1~1~0~1~0~1~1 | fct7_FMV_W_X    => Ob~1~1~1~1~0~1~1

  | fct7_SFENCE_VMA => Ob~0~0~0~1~0~0~1 | fct7_LR_00      => Ob~0~0~0~1~0~0~0
  | fct7_LR_01      => Ob~0~0~0~1~0~0~1 | fct7_LR_10      => Ob~0~0~0~1~0~1~0
  | fct7_LR_11      => Ob~0~0~0~1~0~1~1 | fct7_SC_00      => Ob~0~0~0~1~1~0~0
  | fct7_SC_01      => Ob~0~0~0~1~1~0~1 | fct7_SC_10      => Ob~0~0~0~1~1~1~0
  | fct7_SC_11      => Ob~0~0~0~1~1~1~1 | fct7_AMOSWAP_00 => Ob~0~0~0~0~1~0~0
  | fct7_AMOSWAP_01 => Ob~0~0~0~0~1~0~1 | fct7_AMOSWAP_10 => Ob~0~0~0~0~1~1~0
  | fct7_AMOSWAP_11 => Ob~0~0~0~0~1~1~1 | fct7_AMOADD_00  => Ob~0~0~0~0~0~0~0
  | fct7_AMOADD_01  => Ob~0~0~0~0~0~0~1 | fct7_AMOADD_10  => Ob~0~0~0~0~0~1~0
  | fct7_AMOADD_11  => Ob~0~0~0~0~0~1~1 | fct7_AMOXOR_00  => Ob~0~0~1~0~0~0~0
  | fct7_AMOXOR_01  => Ob~0~0~1~0~0~0~1 | fct7_AMOXOR_10  => Ob~0~0~1~0~0~1~0
  | fct7_AMOXOR_11  => Ob~0~0~1~0~0~1~1 | fct7_AMOAND_00  => Ob~0~1~1~0~0~0~0
  | fct7_AMOAND_01  => Ob~0~1~1~0~0~0~1 | fct7_AMOAND_10  => Ob~0~1~1~0~0~1~0
  | fct7_AMOAND_11  => Ob~0~1~1~0~0~1~1 | fct7_AMOOR_00   => Ob~0~1~0~0~0~0~0
  | fct7_AMOOR_01   => Ob~0~1~0~0~0~0~1 | fct7_AMOOR_10   => Ob~0~1~0~0~0~1~0
  | fct7_AMOOR_11   => Ob~0~1~0~0~0~1~1 | fct7_AMOMIN_00  => Ob~1~0~0~0~0~0~0
  | fct7_AMOMIN_01  => Ob~1~0~0~0~0~0~1 | fct7_AMOMIN_10  => Ob~1~0~0~0~0~1~0
  | fct7_AMOMIN_11  => Ob~1~0~0~0~0~1~1 | fct7_AMOMAX_00  => Ob~1~0~1~0~0~0~0
  | fct7_AMOMAX_01  => Ob~1~0~1~0~0~0~1 | fct7_AMOMAX_10  => Ob~1~0~1~0~0~1~0
  | fct7_AMOMAX_11  => Ob~1~0~1~0~0~1~1 | fct7_AMOMINU_00 => Ob~1~1~0~0~0~0~0
  | fct7_AMOMINU_01 => Ob~1~1~0~0~0~0~1 | fct7_AMOMINU_10 => Ob~1~1~0~0~0~1~0
  | fct7_AMOMINU_11 => Ob~1~1~0~0~0~1~1 | fct7_AMOMAXU_00 => Ob~1~1~1~0~0~0~0
  | fct7_AMOMAXU_01 => Ob~1~1~1~0~0~0~1 | fct7_AMOMAXU_10 => Ob~1~1~1~0~0~1~0
  | fct7_AMOMAXU_11 => Ob~1~1~1~0~0~1~1
  end.

Definition instruction_fct7 (i : instruction) :=
  match i with
  | RV32I_instruction x =>
    match x with
    | ADD_32I => fct7_ADD | SUB_32I  => fct7_SUB  | SLL_32I => fct7_SLL
    | SLT_32I => fct7_SLT | SLTU_32I => fct7_SLTU | XOR_32I => fct7_XOR
    | SRL_32I => fct7_SRL | SRA_32I  => fct7_SRA  | OR_32I  => fct7_OR
    | AND_32I => fct7_AND
    end
  | RV64I_instruction x =>
    match x with
    | ADD_64I  => fct7_ADD  | SUB_64I  => fct7_SUB  | SLL_64I  => fct7_SLL
    | SLT_64I  => fct7_SLT  | SLTU_64I => fct7_SLTU | XOR_64I  => fct7_XOR
    | SRL_64I  => fct7_SRL  | SRA_64I  => fct7_SRA  | OR_64I   => fct7_OR
    | AND_64I  => fct7_AND  | ADDW_64I => fct7_ADDW | SUBW_64I => fct7_SUBW
    | SLLW_64I => fct7_SLLW | SRLW_64I => fct7_SRLW | SRAW_64I => fct7_SRAW
    end
  | RV32M_instruction x =>
    match x with
    | MUL_32M    => fct7_MUL    | MULH_32M  => fct7_MULH
    | MULHSU_32M => fct7_MULHSU | MULHU_32M => fct7_MULHU
    | DIV_32M    => fct7_DIV    | DIVU_32M  => fct7_DIVU
    | REM_32M    => fct7_REM    | REMU_32M  => fct7_REMU
    end
  | RV64M_instruction x =>
    match x with
    | MUL_64M    => fct7_MUL    | MULH_64M  => fct7_MULH
    | MULHSU_64M => fct7_MULHSU | MULHU_64M => fct7_MULHU
    | DIV_64M    => fct7_DIV    | DIVU_64M  => fct7_REM
    | REM_64M    => fct7_REM    | REMU_64M  => fct7_REMU
    | MULW_64M   => fct7_MULW   | DIVW_64M  => fct7_DIVW
    | DIVUW_64M  => fct7_DIVUW  | REMW_64M  => fct7_REMW
    | REMUW_64M  => fct7_REMUW
    end
  | RV32A_instruction x =>
    match x with
    | LR_W_00_32A      => fct7_LR_00      | LR_W_01_32A      => fct7_LR_01
    | LR_W_10_32A      => fct7_LR_10      | LR_W_11_32A      => fct7_LR_11
    | SC_W_00_32A      => fct7_SC_00      | SC_W_01_32A      => fct7_SC_01
    | SC_W_10_32A      => fct7_SC_10      | SC_W_11_32A      => fct7_SC_11
    | AMOSWAP_W_00_32A => fct7_AMOSWAP_00 | AMOSWAP_W_01_32A => fct7_AMOSWAP_01
    | AMOSWAP_W_10_32A => fct7_AMOSWAP_10 | AMOSWAP_W_11_32A => fct7_AMOSWAP_11
    | AMOADD_W_00_32A  => fct7_AMOADD_00  | AMOADD_W_01_32A  => fct7_AMOADD_01
    | AMOADD_W_10_32A  => fct7_AMOADD_10  | AMOADD_W_11_32A  => fct7_AMOADD_11
    | AMOXOR_W_00_32A  => fct7_AMOXOR_00  | AMOXOR_W_01_32A  => fct7_AMOXOR_01
    | AMOXOR_W_10_32A  => fct7_AMOXOR_10  | AMOXOR_W_11_32A  => fct7_AMOXOR_11
    | AMOAND_W_00_32A  => fct7_AMOAND_00  | AMOAND_W_01_32A  => fct7_AMOAND_01
    | AMOAND_W_10_32A  => fct7_AMOAND_10  | AMOAND_W_11_32A  => fct7_AMOAND_11
    | AMOOR_W_00_32A   => fct7_AMOOR_00   | AMOOR_W_01_32A   => fct7_AMOOR_01
    | AMOOR_W_10_32A   => fct7_AMOOR_10   | AMOOR_W_11_32A   => fct7_AMOOR_11
    | AMOMIN_W_00_32A  => fct7_AMOMIN_00  | AMOMIN_W_01_32A  => fct7_AMOMIN_01
    | AMOMIN_W_10_32A  => fct7_AMOMIN_10  | AMOMIN_W_11_32A  => fct7_AMOMIN_11
    | AMOMAX_W_00_32A  => fct7_AMOMAX_00  | AMOMAX_W_01_32A  => fct7_AMOMAX_01
    | AMOMAX_W_10_32A  => fct7_AMOMAX_10  | AMOMAX_W_11_32A  => fct7_AMOMAX_11
    | AMOMINU_W_00_32A => fct7_AMOMINU_00 | AMOMINU_W_01_32A => fct7_AMOMINU_01
    | AMOMINU_W_10_32A => fct7_AMOMINU_10 | AMOMINU_W_11_32A => fct7_AMOMINU_11
    | AMOMAXU_W_00_32A => fct7_AMOMAXU_00 | AMOMAXU_W_01_32A => fct7_AMOMAXU_01
    | AMOMAXU_W_10_32A => fct7_AMOMAXU_10 | AMOMAXU_W_11_32A => fct7_AMOMAXU_11
    end
  | RV64A_instruction x =>
    match x with
    | LR_W_00_64A      => fct7_LR_00      | LR_W_01_64A      => fct7_LR_01
    | LR_W_10_64A      => fct7_LR_10      | LR_W_64A         => fct7_LR_11
    | SC_W_00_64A      => fct7_SC_00      | SC_W_01_64A      => fct7_SC_01
    | SC_W_10_64A      => fct7_SC_10      | SC_W_11_64A      => fct7_SC_11
    | AMOSWAP_W_00_64A => fct7_AMOSWAP_00 | AMOSWAP_W_01_64A => fct7_AMOSWAP_01
    | AMOSWAP_W_10_64A => fct7_AMOSWAP_10 | AMOSWAP_W_11_64A => fct7_AMOSWAP_11
    | AMOADD_W_00_64A  => fct7_AMOADD_00  | AMOADD_W_01_64A  => fct7_AMOADD_01
    | AMOADD_W_10_64A  => fct7_AMOADD_10  | AMOADD_W_11_64A  => fct7_AMOADD_11
    | AMOXOR_W_00_64A  => fct7_AMOXOR_00  | AMOXOR_W_01_64A  => fct7_AMOXOR_01
    | AMOXOR_W_10_64A  => fct7_AMOXOR_10  | AMOXOR_W_11_64A  => fct7_AMOXOR_11
    | AMOAND_W_00_64A  => fct7_AMOAND_00  | AMOAND_W_01_64A  => fct7_AMOAND_01
    | AMOAND_W_10_64A  => fct7_AMOAND_10  | AMOAND_W_11_64A  => fct7_AMOAND_11
    | AMOOR_W_00_64A   => fct7_AMOOR_00   | AMOOR_W_01_64A   => fct7_AMOOR_01
    | AMOOR_W_10_64A   => fct7_AMOOR_10   | AMOOR_W_11_64A   => fct7_AMOOR_11
    | AMOMIN_W_00_64A  => fct7_AMOMIN_00  | AMOMIN_W_01_64A  => fct7_AMOMIN_01
    | AMOMIN_W_10_64A  => fct7_AMOMIN_10  | AMOMIN_W_11_64A  => fct7_AMOMIN_11
    | AMOMAX_W_00_64A  => fct7_AMOMAX_00  | AMOMAX_W_01_64A  => fct7_AMOMAX_01
    | AMOMAX_W_10_64A  => fct7_AMOMAX_10  | AMOMAX_W_11_64A  => fct7_AMOMAX_11
    | AMOMINU_W_00_64A => fct7_AMOMINU_00 | AMOMINU_W_01_64A => fct7_AMOMINU_01
    | AMOMINU_W_10_64A => fct7_AMOMINU_10 | AMOMINU_W_11_64A => fct7_AMOMINU_11
    | AMOMAXU_W_00_64A => fct7_AMOMAXU_00 | AMOMAXU_W_01_64A => fct7_AMOMAXU_01
    | AMOMAXU_W_10_64A => fct7_AMOMAXU_10 | AMOMAXU_W_11_64A => fct7_AMOMAXU_11
    | LR_D_00_64A      => fct7_LR_00      | LR_D_01_64A      => fct7_LR_01
    | LR_D_10_64A      => fct7_LR_10      | LR_D_11_64A      => fct7_LR_11
    | SC_D_00_64A      => fct7_SC_00      | SC_D_01_64A      => fct7_SC_01
    | SC_D_10_64A      => fct7_SC_10      | SC_D_11_64A      => fct7_SC_11
    | AMOSWAP_D_00_64A => fct7_AMOSWAP_00 | AMOSWAP_D_01_64A => fct7_AMOSWAP_01
    | AMOSWAP_D_10_64A => fct7_AMOSWAP_10 | AMOSWAP_D_11_64A => fct7_AMOSWAP_11
    | AMOADD_D_00_64A  => fct7_AMOADD_00  | AMOADD_D_01_64A  => fct7_AMOADD_01
    | AMOADD_D_10_64A  => fct7_AMOADD_10  | AMOADD_D_11_64A  => fct7_AMOADD_11
    | AMOXOR_D_00_64A  => fct7_AMOXOR_00  | AMOXOR_D_01_64A  => fct7_AMOXOR_01
    | AMOXOR_D_10_64A  => fct7_AMOXOR_10  | AMOXOR_D_11_64A  => fct7_AMOXOR_11
    | AMOAND_D_00_64A  => fct7_AMOAND_00  | AMOAND_D_01_64A  => fct7_AMOAND_01
    | AMOAND_D_10_64A  => fct7_AMOAND_10  | AMOAND_D_11_64A  => fct7_AMOAND_11
    | AMOOR_D_00_64A   => fct7_AMOOR_00   | AMOOR_D_01_64A   => fct7_AMOOR_01
    | AMOOR_D_10_64A   => fct7_AMOOR_10   | AMOOR_D_11_64A   => fct7_AMOOR_11
    | AMOMIN_D_00_64A  => fct7_AMOMIN_00  | AMOMIN_D_01_64A  => fct7_AMOMIN_01
    | AMOMIN_D_10_64A  => fct7_AMOMIN_10  | AMOMIN_D_11_64A  => fct7_AMOMIN_11
    | AMOMAX_D_00_64A  => fct7_AMOMAX_00  | AMOMAX_D_01_64A  => fct7_AMOMAX_01
    | AMOMAX_D_10_64A  => fct7_AMOMAX_10  | AMOMAX_D_11_64A  => fct7_AMOMAX_11
    | AMOMINU_D_00_64A => fct7_AMOMINU_00 | AMOMINU_D_01_64A => fct7_AMOMINU_01
    | AMOMINU_D_10_64A => fct7_AMOMINU_10 | AMOMINU_D_11_64A => fct7_AMOMINU_11
    | AMOMAXU_D_00_64A => fct7_AMOMAXU_00 | AMOMAXU_D_01_64A => fct7_AMOMAXU_01
    | AMOMAXU_D_10_64A => fct7_AMOMAXU_10 | AMOMAXU_D_11_64A => fct7_AMOMAXU_11
    end
  | RV32F_instruction x =>
    match x with
    | FADD_S_32F    => fct7_FADD_S   | FSUB_S_32F    => fct7_FSUB_S
    | FMUL_S_32F    => fct7_FMUL_S   | FDIV_S_32F    => fct7_FDIV_S
    | FSQRT_S_32F   => fct7_FSQRT_S  | FSGNJ_S_32F   => fct7_FSGNJ_S
    | FSGNJN_S_32F  => fct7_FSGNJ_S  | FSGNJX_S_32F  => fct7_FS
    | FMIN_S_32F    => fct7_FMIN_S   | FMAX_S_32F    => fct7_FMAX_S
    | FCVT_W_S_32F  => fct7_FCVT_W_S | FCVT_WU_S_32F => fct7_FCVT_W_S
    | FMV_X_W_32F   => fct7_FMV_X_W  | FEQ_S_32F     => fct7_FEQ_S
    | FLT_S_32F     => fct7_FEQ_S    | FLE_S_32F     => fct7_FEQ_S
    | FCLASS_S_32F  => fct7_FCLASS_S | FCVT_S_W_32F  => fct7_FCVT_S_W
    | FCVT_S_WU_32F => fct7_FCVT_S_W | FMV_W_X_32F   => fct7_FMV_W_X
    end
  | RV64F_instruction x =>
    match x with
    | FADD_S_64F    => fct7_FADD_S   | FSUB_S_64F    => fct7_FSUB_S
    | FMUL_S_64F    => fct7_FMUL_S   | FDIV_S_64F    => fct7_FDIV_S
    | FSQRT_S_64F   => fct7_FSQRT_S  | FSGNJ_S_64F   => fct7_FSGNJ_S
    | FSGNJN_S_64F  => fct7_FSGNJ_S  | FSGNJX_S_64F  => fct7_FSGNJ_S
    | FMIN_S_64F    => fct7_FMIN_S   | FMAX_S_64F    => fct7_FMAX_S
    | FCVT_W_S_64F  => fct7_FCVT_W_S | FCVT_WU_S_64F => fct7_FCVT_W_S
    | FMV_X_W_64F   => fct7_FMV_X_W  | FEQ_S_64F     => fct7_FEQ_S
    | FLT_S_64F     => fct7_FEQ_S    | FLE_S_64F     => fct7_FEQ_S
    | FCLASS_S_64F  => fct7_FCLASS_S | FCVT_S_W_64F  => fct7_FCLASS_S
    | FCVT_S_WU_64F => fct7_FCVT_S_W | FMV_W_X_64F   => fct7_FMV_W_X
    | FCVT_L_S_64F  => fct7_FCVT_W_S | FCVT_LU_S_64F => fct7_FCVT_W_S
    | FCVT_S_L_64F  => fct7_FCVT_S_W | FCVT_S_LU_64F => fct7_FCVT_S_W
    end
  | RV32D_instruction x =>
    match x with
    | FADD_D_32D   => fct7_FADD_D | FSUB_D_32D    => fct7_FSUB_D
    | FMUL_D_32D   => fct7_FMUL_D | FDIV_D_32D    => fct7_FDIV_D
    | FSQRT_D_32D  => fct7_ | FSGNJ_D_32D   => fct7_
    | FSGNJN_D_32D => fct7_ | FSGNJX_D_32D  => fct7_
    | FMIN_D_32D   => fct7_ | FMAX_D_32D    => fct7_
    | FCVT_S_D_32D => fct7_ | FCVT_D_S_32D  => fct7_
    | FEQ_D_32D    => fct7_ | FLT_D_32D     => fct7_
    | FLE_D_32D    => fct7_ | FCLASS_D_32D  => fct7_
    | FCVT_W_D_32D => fct7_ | FCVT_WU_D_32D => fct7_
    | FCVT_D_W_32D => fct7_ | FCVT_D_WU_32D => fct7_
    end
  | RV64D_instruction x =>
    match x with
    | FADD_D_64D    => fct7_ | FSUB_D_64D    => fct7_
    | FMUL_D_64D    => fct7_ | FDIV_D_64D    => fct7_
    | FSQRT_D_64D   => fct7_ | FSGNJ_D_64D   => fct7_
    | FSGNJN_D_64D  => fct7_ | FSGNJX_D_64D  => fct7_
    | FMIN_D_64D    => fct7_ | FMAX_D_64D    => fct7_
    | FCVT_S_D_64D  => fct7_ | FCVT_D_S_64D  => fct7_
    | FEQ_D_64D     => fct7_ | FLT_D_64D     => fct7_
    | FLE_D_64D     => fct7_ | FCLASS_D_64D  => fct7_
    | FCVT_W_D_64D  => fct7_ | FCVT_WU_D_64D => fct7_
    | FCVT_D_W_64D  => fct7_ | FCVT_D_WU_64D => fct7_
    | FCVT_L_D_64D  => fct7_ | FCVT_LU_D_64D => fct7_
    | FMV_X_D_64D   => fct7_ | FCVT_D_L_64D  => fct7_
    | FCVT_D_LU_64D => fct7_ | FMV_D_X_64D   => fct7_
    end
  | RV32Q_instruction x =>
    match x with
    | FADD_Q_32Q   => fct7_ | FSUB_Q_32Q    => fct7_
    | FMUL_Q_32Q   => fct7_ | FDIV_Q_32Q    => fct7_
    | FSQRT_Q_32Q  => fct7_ | FSGNJ_Q_32Q   => fct7_
    | FSGNJN_Q_32Q => fct7_ | FSGNJX_Q_32Q  => fct7_
    | FMIN_Q_32Q   => fct7_ | FMAX_Q_32Q    => fct7_
    | FCVT_S_Q_32Q => fct7_ | FCVT_Q_S_32Q  => fct7_
    | FCVT_D_Q_32Q => fct7_ | FCVT_Q_D_32Q  => fct7_
    | FEQ_Q_32Q    => fct7_ | FLT_Q_32Q     => fct7_
    | FLE_Q_32Q    => fct7_ | FCLASS_Q_32Q  => fct7_
    | FCVT_W_Q_32Q => fct7_ | FCVT_WU_Q_32Q => fct7_
    | FCVT_Q_W_32Q => fct7_ | FCVT_Q_WU_32Q => fct7_
    end
  | RV64Q_instruction x =>
    match x with
    | FADD_Q_64Q   => fct7_ | FSUB_Q_64Q    => fct7_
    | FMUL_Q_64Q   => fct7_ | FDIV_Q_64Q    => fct7_
    | FSQRT_Q_64Q  => fct7_ | FSGNJ_Q_64Q   => fct7_
    | FSGNJN_Q_64Q => fct7_ | FSGNJX_Q_64Q  => fct7_
    | FMIN_Q_64Q   => fct7_ | FMAX_Q_64Q    => fct7_
    | FCVT_S_Q_64Q => fct7_ | FCVT_Q_S_64Q  => fct7_
    | FCVT_D_Q_64Q => fct7_ | FCVT_Q_D_64Q  => fct7_
    | FEQ_Q_64Q    => fct7_ | FLT_Q_64Q     => fct7_
    | FLE_Q_64Q    => fct7_ | FCLASS_Q_64Q  => fct7_
    | FCVT_W_Q_64Q => fct7_ | FCVT_WU_Q_64Q => fct7_
    | FCVT_Q_W_64Q => fct7_ | FCVT_Q_WU_64Q => fct7_
    | FCVT_L_Q_64Q => fct7_ | FCVT_LU_Q_64Q => fct7_
    | FCVT_Q_L_64Q => fct7_ | FCVT_Q_LU_64Q => fct7_
    end
  end.

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

Inductive

(* Definition instruction_bin := bits_t 32. *)

(* Definition ex_instr : instruction_bin := *)
(*   Ob~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~1. *)

(* Definition get_first_bit (i : instruction_bin) := *)
(*   i[|5'd0| :+ 2]. *)

(* Definition get_subfield_value (s : subfield_properties) (i : bits_t 32) := *)
(*   UBinop (UBits2 USel) i (first_bit s). *)
