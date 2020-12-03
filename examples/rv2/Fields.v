Require Import MSetInterface.
Require Import Koika.Frontend Koika.Std.
Require Import Instructions.

Inductive instruction_type : Type :=
| RType
| R4Type
| IType
| SType
| BType
| UType
| JType.

Inductive instruction_field : Type :=
| opcode
| rd
| rs1
| rs2
| rs3
| funct2
| funct3
| funct7
| immI
| immS
| immB
| immU
| immJ.

Inductive instruction_field_type : Type :=
| identification_field
| data_field.

Definition classify_instruction_field (f : instruction_field) :=
  match f with
  | opcode => identification_field
  | rd     => data_field
  | rs1    => data_field
  | rs2    => data_field
  | rs3    => data_field
  | funct2 => identification_field
  | funct3 => identification_field
  | funct7 => identification_field
  | immI   => data_field
  | immS   => data_field
  | immB   => data_field
  | immU   => data_field
  | immJ   => data_field
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

Inductive funct3_type : Type :=
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

Definition funct3_bin (f : funct3_type) :=
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

Inductive funct7_type : Type :=
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

Definition funct7_bin (f : funct7_type) :=
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

Scheme Equality for instruction_field.

Module DecidableInstructionField <: DecidableType.
  Definition t := instruction_field.
  Definition eq := @eq instruction_field.
  Instance eq_equiv : @Equivalence instruction_field eq := eq_equivalence.
  Definition eq_dec := instruction_field_eq_dec.
End DecidableInstructionField.

Module FieldsSet <: WSetsOn DecidableInstructionField.
  Include WSetsOn DecidableInstructionField.
End FieldsSet.

Definition instruction_type_fields (t : instruction_type) :=
  match t with
  | RType =>
    (FieldsSet.add opcode
    (FieldsSet.add rd
    (FieldsSet.add funct3
    (FieldsSet.add rs1
    (FieldsSet.add rs2
    (FieldsSet.add funct7
    FieldsSet.empty))))))
  | R4Type =>
    (FieldsSet.add opcode
    (FieldsSet.add rd
    (FieldsSet.add funct3
    (FieldsSet.add rs1
    (FieldsSet.add rs2
    (FieldsSet.add funct2
    (FieldsSet.add rs3
    FieldsSet.empty)))))))
  | IType =>
    (FieldsSet.add opcode
    (FieldsSet.add rd
    (FieldsSet.add funct3
    (FieldsSet.add rs1
    (FieldsSet.add immI
    FieldsSet.empty)))))
  | SType =>
    (FieldsSet.add opcode
    (FieldsSet.add immS
    (FieldsSet.add funct3
    (FieldsSet.add rs1
    (FieldsSet.add rs2
    FieldsSet.empty)))))
  | BType =>
    (FieldsSet.add opcode
    (FieldsSet.add immB
    (FieldsSet.add funct3
    (FieldsSet.add rs1
    (FieldsSet.add rs2
    FieldsSet.empty)))))
  | UType =>
    (FieldsSet.add opcode
    (FieldsSet.add rd
    (FieldsSet.add immU
    FieldsSet.empty)))
  | JType =>
    (FieldsSet.add opcode
    (FieldsSet.add rd
    (FieldsSet.add immJ
    FieldsSet.empty)))
  end.

Definition get_instruction_type (i : instruction) :=
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

Record subfield_properties := {
  first_bit : nat;
  length : nat
}.

Record field_properties := {
  is_sign_extended : bool;
  field_subfields : list subfield_properties;
  shift : nat
}.

Definition get_field_properties (f : instruction_field) :=
  match f with
  | opcode => {|
      is_sign_extended := false;
      field_subfields  := {| first_bit := 0 ; length := 7  |}::[];
      shift            := 0
    |}
  | rd     => {|
      is_sign_extended := false;
      field_subfields  := {| first_bit := 7 ; length := 5 |}::[];
      shift            := 0
    |}
  | rs1    => {|
      is_sign_extended := false;  
      field_subfields  := {| first_bit := 15; length := 5  |}::[];
      shift            := 0
    |}
  | rs2    => {|
      is_sign_extended := false;
      field_subfields  := {| first_bit := 20; length := 5  |}::[];
      shift            := 0
    |}
  | rs3    => {|
      is_sign_extended := false;
      field_subfields  := {| first_bit := 27; length := 5  |}::[];
      shift            := 0
    |}
  | funct2 => {|
      is_sign_extended := false;
      field_subfields  := {| first_bit := 25; length := 2  |}::[];
      shift            := 0
    |}
  | funct3 => {|
      is_sign_extended := false;
      field_subfields  := {| first_bit := 12; length := 3  |}::[];
      shift            := 0
    |}
  | funct7 => {|
      is_sign_extended := false;
      field_subfields  := {| first_bit := 25; length := 7  |}::[];
      shift            := 0
    |}
  | immI   => {|
      is_sign_extended := true;
      field_subfields  := {| first_bit := 20; length := 12 |}::[];
      shift            := 0
    |}
  | immS   => {|
      is_sign_extended := true;
      field_subfields  :=
        {| first_bit := 25; length := 7 |}::
        {| first_bit := 7 ; length := 5 |}::[];
      shift            := 0
    |}
  | immB   => {|
      is_sign_extended := true;
      field_subfields  :=
        {| first_bit := 31; length := 1 |}::
        {| first_bit := 7 ; length := 1 |}::
        {| first_bit := 25; length := 6 |}::
        {| first_bit := 8 ; length := 4 |}::[];
      shift            := 1
    |}
  | immU   => {|
      is_sign_extended := false;
      field_subfields  := {| first_bit := 12; length := 20 |}::[];
      shift            := 12
    |}
  | immJ   => {|
      is_sign_extended := true;
      field_subfields  :=
        {| first_bit := 31; length := 1  |}::
        {| first_bit := 12; length := 8  |}::
        {| first_bit := 20; length := 1  |}::
        {| first_bit := 21; length := 10 |}::[];
      shift            := 1
    |}
  end.

Definition instruction_bin := bits_t 32.
