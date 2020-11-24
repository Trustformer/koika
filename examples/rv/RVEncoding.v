(*! Encoding-related constants !*)

(* This file defines constants used to identify instructions.
   Of all the encondings registered in this file, only those in the RV32I
   section are used in practice for the time being. *)

Require Import Koika.Frontend.

(* Mind the fact that many operations sharing the same name and encoding do not
   have the same effect depending on the width of the ISA (32, 64 or 128). See
   unpriviledged specification 1.3 (RISC-V ISA Overview) as of V20191214-draft
   for details.  *)

(* 1. RV32I *)
(* 1.1. R-type - opcode, funct3, funct7 *)
(* Operations *)
Definition opcode_OP   := Ob~0~1~1~0~0~1~1.
Definition funct3_ADD  := Ob~0~0~0.
Definition funct7_ADD  := Ob~0~0~0~0~0~0~0.
Definition funct3_SUB  := Ob~0~0~0.
Definition funct7_SUB  := Ob~0~1~0~0~0~0~0.
Definition funct3_SLL  := Ob~0~0~1.
Definition funct7_SLL  := Ob~0~0~0~0~0~0~0.
Definition funct3_SLT  := Ob~0~1~0.
Definition funct7_SLT  := Ob~0~0~0~0~0~0~0.
Definition funct3_SLTU := Ob~0~1~1.
Definition funct7_SLTU := Ob~0~0~0~0~0~0~0.
Definition funct3_XOR  := Ob~1~0~0.
Definition funct7_XOR  := Ob~0~0~0~0~0~0~0.
Definition funct3_SRL  := Ob~1~0~1.
Definition funct7_SRL  := Ob~0~0~0~0~0~0~0.
Definition funct3_SRA  := Ob~1~0~1.
Definition funct7_SRA  := Ob~0~1~0~0~0~0~0.
Definition funct3_OR   := Ob~1~1~0.
Definition funct7_OR   := Ob~0~0~0~0~0~0~0.
Definition funct3_AND  := Ob~1~1~1.
Definition funct7_AND  := Ob~0~0~0~0~0~0~0.

(* 1.2. I-type - opcode, funct3 *)
(* JALR *)
Definition opcode_JALR := Ob~1~1~0~0~1~1~1.
(* Uniquely identified by its opcode, no need to indicate the value of the
   funct3 field *)
(* Load *)
Definition opcode_LOAD := Ob~0~0~0~0~0~1~1.
Definition funct3_LB   := Ob~0~0~0.
Definition funct3_LH   := Ob~0~0~1.
Definition funct3_LW   := Ob~0~1~0.
Definition funct3_LBU  := Ob~1~0~0.
Definition funct3_LHU  := Ob~1~0~1.
(* Immediate operations *)
Definition opcode_OP_IMM := Ob~0~0~1~0~0~1~1.
Definition funct3_SLTI   := Ob~0~1~0.
Definition funct3_SLTIU  := Ob~0~1~1.
Definition funct3_ADDI   := Ob~0~0~0.
Definition funct3_XORI   := Ob~1~0~0.
Definition funct3_ORI    := Ob~1~1~0.
Definition funct3_ANDI   := Ob~1~1~1.
(* Immediate operations with funct6 *)
(* The RISC-V encoding of immediate shifts is a bit weird, since the number of
   bits required describe the magnitude of a shift are 5 for 32 bits, 6 for 64
   bits and 7 for 128 bits.
   The last x bits of the immediate field are used are used to store this
   information while the others are used to distinguish between SRLI and SRAI
   (SLLI has a different funct3).
   The reason why this is not cleaner is that there are nine operations sharing
   the same opcode, so funct3 is not enough to encode them all.
   Although a value for funct7 is given by the specification for RV32I, the
   first six bits of it are enough to discriminate between SXLI and SRAI, and
   remain the same between RV32I and RV64I. *)
(* also use opcode_OP_IMM *)
Definition funct3_SLLI := Ob~0~0~1.
Definition funct6_SLLI := Ob~0~0~0~0~0~0.
Definition funct3_SRLI := Ob~1~0~1.
Definition funct6_SRLI := Ob~0~0~0~0~0~0.
Definition funct3_SRAI := Ob~1~0~1.
Definition funct6_SRAI := Ob~0~1~0~0~0~0.
(* Memory *)
Definition opcode_MISC_MEM := Ob~0~0~0~1~1~1~1.
Definition funct3_FENCE    := Ob~0~0~0.

(* 1.3. S-type - opcode, funct3 *)
(* Store *)
Definition opcode_STORE := Ob~0~1~0~0~0~1~1.
Definition funct3_SB    := Ob~0~0~0.
Definition funct3_SH    := Ob~0~0~1.
Definition funct3_SW    := Ob~0~1~0.

(* 1.4. B-type - opcode, funct3 *)
(* Branch *)
Definition opcode_BRANCH := Ob~1~1~0~0~0~1~1.
Definition funct3_BEQ    := Ob~0~0~0.
Definition funct3_BNE    := Ob~0~0~1.
Definition funct3_BLT    := Ob~1~0~0.
Definition funct3_BGE    := Ob~1~0~1.
Definition funct3_BLTU   := Ob~1~1~0.
Definition funct3_BGEU   := Ob~1~1~1.

(* 1.5. U-type - opcode *)
Definition opcode_LUI   := Ob~0~1~1~0~1~1~1.
Definition opcode_AUIPC := Ob~0~0~1~0~1~1~1.

(* 1.6. J-type - opcode *)
Definition opcode_JAL := Ob~1~1~0~1~1~1~1.

(* 1.7. System (I-type with special interpretation) - opcode, funct3, funct12 *)
Definition opcode_SYSTEM  := Ob~1~1~1~0~0~1~1.
Definition funct3_PRIV    := Ob~0~0~0. (* Same for all system operations *)
Definition funct12_ECALL  := Ob~0~0~0~0~0~0~0~0~0~0~0~0.
Definition funct12_EBREAK := Ob~0~0~0~0~0~0~0~0~0~0~0~1.

(* 2. RV64I (in addition to RV32I) *)
(* 2.1. R-type - opcode, funct3, funct7 *)
(* Operations on 32 bits *)
Definition opcode_OP_32 := Ob~0~1~1~1~0~1~1.
Definition funct3_ADDW  := Ob~0~0~0.
Definition funct7_ADDW  := Ob~0~0~0~0~0~0~0.
Definition funct3_SUBW  := Ob~0~0~0.
Definition funct7_SUBW  := Ob~0~1~0~0~0~0~0.
Definition funct3_SLLW  := Ob~0~0~1.
Definition funct7_SLLW  := Ob~0~0~0~0~0~0~0.
Definition funct3_SRLW  := Ob~1~0~1.
Definition funct7_SRLW  := Ob~0~0~0~0~0~0~0.
Definition funct3_SRAW  := Ob~1~0~1.
Definition funct7_SRAW  := Ob~0~1~0~0~0~0~0.

(* 2.2. I-type - opcode, funct3 *)
(* Load *)
(* also use opcode_LOAD *)
Definition funct3_LWU := Ob~1~1~0.
Definition funct3_LD  := Ob~0~1~1.
(* Immediate operations on 32 bits *)
Definition opcode_OP_IMM_32 := Ob~0~0~1~1~0~1~1.
Definition funct3_ADDIW     := Ob~0~0~0.
(* Immediate operations on 32 bits with funct7 - funct7 should really not be
   required, the funct6 fields defined for RV32I could be used for the same
   effect *)
(* also use opcode_OP_IMM_32 *)
Definition funct3_SLLIW := Ob~0~0~1.
Definition funct7_SLLIW := Ob~0~0~0~0~0~0~0.
Definition funct3_SRLIW := Ob~1~0~1.
Definition funct7_SRLIW := Ob~0~0~0~0~0~0~0.
Definition funct3_SRAIW := Ob~1~0~1.
Definition funct7_SRAIW := Ob~0~1~0~0~0~0~0.

(* 2.3. S-type - opcode,  funct3 *)
(* Store *)
(* also uses opcode_STORE *)
Definition funct3_SD := Ob~0~1~1.

(* 3. RV32/RV64 Zifencei *)
(* 3.1. I-type - opcode, funct3 *)
(* Memory *)
(* also uses opcode_MISC_MEM *)
Definition funct3_FENCE_I := Ob~0~0~1.

(* 4. RV32/RV64 Ziscr *)
(* 4.1. I-type - opcode, funct3 *)
(* Control and Status Register *)
(* also use opcode_SYSTEM *)
Definition funct3_CSRRW  := Ob~0~0~1.
Definition funct3_CSRRS  := Ob~0~1~0.
Definition funct3_CSRRC  := Ob~0~1~1.
Definition funct3_CSRRWI := Ob~1~0~1.
Definition funct3_CSRRSI := Ob~1~1~0.
Definition funct3_CSRRCI := Ob~1~1~1.

(* 5. RV32M *)
(* 5.1. R-type - opcode, funct3, funct7 *)
(* Operations *)
(* also use opcode_OP *)
Definition funct3_MUL    := Ob~0~0~0.
Definition funct7_MUL    := Ob~0~0~0~0~0~0~1.
Definition funct3_MULH   := Ob~0~0~1.
Definition funct7_MULH   := Ob~0~0~0~0~0~0~1.
Definition funct3_MULHSU := Ob~0~1~0.
Definition funct7_MULHSU := Ob~0~0~0~0~0~0~1.
Definition funct3_MULHU  := Ob~0~1~1.
Definition funct7_MULHU  := Ob~0~0~0~0~0~0~1.
Definition funct3_DIV    := Ob~1~0~0.
Definition funct7_DIV    := Ob~0~0~0~0~0~0~1.
Definition funct3_DIVU   := Ob~1~0~1.
Definition funct7_DIVU   := Ob~0~0~0~0~0~0~1.
Definition funct3_REM    := Ob~1~1~0.
Definition funct7_REM    := Ob~0~0~0~0~0~0~1.
Definition funct3_REMU   := Ob~1~1~1.
Definition funct7_REMU   := Ob~0~0~0~0~0~0~1.

(* 6. RV64M (in addition to RV32M) *)
(* 6.1. R-type - opcode, funct3, funct7 *)
(* Operations on 32 bits *)
(* also use opcode_OP_32 *)
Definition funct3_MULW  := Ob~0~0~0.
Definition funct7_MULW  := Ob~0~0~0~0~0~0~1.
Definition funct3_DIVW  := Ob~1~0~0.
Definition funct7_DIVW  := Ob~0~0~0~0~0~0~1.
Definition funct3_DIVUW := Ob~1~0~1.
Definition funct7_DIVUW := Ob~0~0~0~0~0~0~1.
Definition funct3_REMW  := Ob~1~1~0.
Definition funct7_REMW  := Ob~0~0~0~0~0~0~1.
Definition funct3_REMUW := Ob~1~1~1.
Definition funct7_REMUW := Ob~0~0~0~0~0~0~1.

(* 7. RV32A *)
(* 7.1. R-type - opcode, funct3, funct5 (= first 5 bits of funct7) *)
(* Atomic operations *)
Definition opcode_AMO     := Ob~0~1~0~1~1~1~1.
Definition funct3_AMOW    := Ob~0~1~0. (* all of these ops. share this funct3 *)
Definition funct5_LR      := Ob~0~0~0~1~0.
Definition funct5_SC      := Ob~0~0~0~1~1.
Definition funct5_AMOSWAP := Ob~0~0~0~0~1.
Definition funct5_AMOADD  := Ob~0~0~0~0~0.
Definition funct5_AMOXOR  := Ob~0~0~1~0~0.
Definition funct5_AMOAND  := Ob~0~1~1~0~0.
Definition funct5_AMOOR   := Ob~0~1~0~0~0.
Definition funct5_AMOMIN  := Ob~1~0~0~0~0.
Definition funct5_AMOMAX  := Ob~1~0~1~0~0.
Definition funct5_AMOMINU := Ob~1~1~0~0~0.
Definition funct5_AMOMAXU := Ob~1~1~1~0~0.

(* 8. RV64A (in addition to RV32A) *)
(* 8.1. R-type - opcode, funct3, funct5 (= first 5 bits of funct7) *)
(* Atomic operations *)
(* also use opcode_AMO *)
Definition funct3_AMOD := Ob~0~1~1.
(* Same operations as RV32A but with the above funct3 *)

(* 9. RV32F *)
(* 9.1. R-type with a weird encoding - opcode, funct3, funct7 *)
Definition opcode_OP_FP    := Ob~1~0~1~0~0~1~1.
Definition funct7_FADD_S   := Ob~0~0~0~0~0~0~0.
Definition funct7_FSUB_S   := Ob~0~0~0~0~1~0~0.
Definition funct7_FMUL_S   := Ob~0~0~0~1~0~0~0.
Definition funct7_FDIV_S   := Ob~0~0~0~1~1~0~0.
Definition funct7_FSQRT_S  := Ob~0~1~0~1~1~0~0.
Definition funct7_FSGNJ_S  := Ob~0~0~1~0~0~0~0.
Definition funct3_FSGNJ_S  := Ob~0~0~0.
Definition funct3_FSGNJN_S := Ob~0~0~1.
Definition funct3_FSGNJX_S := Ob~0~1~0.
Definition funct7_FMIN_S   := Ob~0~0~1~0~1~0~0.
Definition funct3_FMIN_S   := Ob~0~0~0.
Definition funct3_FMAX_S   := Ob~0~0~1.
Definition funct7_FCVT_W_S := Ob~1~1~0~0~0~0~0.
Definition rs2_FCVT_W_S    := Ob~0~0~0~0~0.
Definition rs2_FCVT_WU_S   := Ob~0~0~0~0~1.
Definition funct7_FMV_X_W  := Ob~1~1~1~0~0~0~0.
Definition funct3_FMV_X_W  := Ob~0~0~0.
Definition funct7_FEQ_S    := Ob~1~0~1~0~0~0~0.
Definition funct3_FEQ_S    := Ob~0~1~0.
Definition funct3_FLT_S    := Ob~0~0~1.
Definition funct3_FLE_S    := Ob~0~0~0.
Definition funct7_FCLASS_S := Ob~1~1~1~0~0~0~0.
Definition funct3_FCLASS_S := Ob~0~0~1.
Definition funct7_FCVT_S_W := Ob~1~1~0~1~0~0~0.
Definition funct7_FMV_W_X  := Ob~1~1~1~1~0~0~0.

(* 9.2. R4-type - opcode *)
Definition opcode_MADD     := Ob~1~0~0~0~0~1~1.
Definition opcode_MSUB     := Ob~1~0~0~0~1~1~1.
Definition opcode_NMSUB    := Ob~1~0~0~1~0~1~1.
Definition opcode_NMADD    := Ob~1~0~0~1~1~1~1.

(* 9.3. I-type - opcode, funct3 *)
(* Load *)
Definition opcode_LOAD_FP := Ob~0~0~0~0~1~1~1.
Definition funct3_FLW     := Ob~0~1~0.

(* 9.4. S-type - opcode, funct3 *)
(* Store *)
Definition opcode_STORE_FP := Ob~0~1~0~0~1~1~1.
Definition funct3_FSW      := Ob~0~1~0.

(* 10. RV64F (in addition to RV32F) *)
Definition rs2_FCVT_L_S  := Ob~0~0~0~1~0.
Definition rs2_FCVT_LU_S := Ob~0~0~0~1~1.

(* 11. RV32D *)
(* 12. RV64D (in addition to RV32D) *)
(* 13. RV32Q *)
(* 14. RV64Q (in addition to RV32Q) *)

(* 15. Priviledged instructions *)
Definition funct12_URET := Ob~0~0~0~0~0~0~0~0~0~0~1~0.
Definition funct12_SRET := Ob~0~0~0~1~0~0~0~0~0~0~1~0.
Definition funct12_MRET := Ob~0~0~1~1~0~0~0~0~0~0~1~0.
Definition funct12_WFI  := Ob~0~0~0~1~0~0~0~0~0~1~0~1.

(* 16. Future (as of ISA V20191214-draft) *)
Definition funct7_SFENCE_VMA := Ob~0~0~0~1~0~0~1.
