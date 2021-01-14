Require Import Koika.Frontend.
Require Import Instructions IFields ITypes.

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
  forall (i : instruction), has_fct7 (get_instruction_i_type i) = true
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
