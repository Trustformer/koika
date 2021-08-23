(*! Definitions related to the fct7 instruction field !*)

Require Import Koika.Frontend.
Require Import rv.Instructions rv.IFields rv.ITypes rv.InstructionsOpcodes.

Inductive fct7_type :=
| fct7_0000000 | fct7_0000001 | fct7_0000010 | fct7_0000011 | fct7_0000100
| fct7_0000101 | fct7_0000110 | fct7_0000111 | fct7_0001000 | fct7_0001001
| fct7_0001010 | fct7_0001011 | fct7_0001100 | fct7_0001101 | fct7_0001110
| fct7_0001111 | fct7_0010000 | fct7_0010001 | fct7_0010010 | fct7_0010011
| fct7_0010100 | fct7_0010101 | fct7_0010111 | fct7_0100000 | fct7_0100001
| fct7_0100010 | fct7_0100011 | fct7_0101100 | fct7_0101101 | fct7_0101111
| fct7_0110000 | fct7_0110001 | fct7_0110010 | fct7_0110011 | fct7_1000000
| fct7_1000001 | fct7_1000010 | fct7_1000011 | fct7_1010000 | fct7_1010001
| fct7_1010010 | fct7_1010011 | fct7_1100000 | fct7_1100001 | fct7_1100010
| fct7_1100011 | fct7_1101000 | fct7_1101001 | fct7_1101011 | fct7_1110000
| fct7_1110001 | fct7_1110010 | fct7_1110011 | fct7_1111000 | fct7_1111001
| fct7_1111011.
Scheme Equality for fct7_type.

Definition fct7_bin (f : fct7_type) :=
  match f with
  | fct7_0000000 => Ob~0~0~0~0~0~0~0 | fct7_0000001 => Ob~0~0~0~0~0~0~1
  | fct7_0000010 => Ob~0~0~0~0~0~1~0 | fct7_0000011 => Ob~0~0~0~0~0~1~1
  | fct7_0000100 => Ob~0~0~0~0~1~0~0 | fct7_0000101 => Ob~0~0~0~0~1~0~1
  | fct7_0000110 => Ob~0~0~0~0~1~1~0 | fct7_0000111 => Ob~0~0~0~0~1~1~1
  | fct7_0001000 => Ob~0~0~0~1~0~0~0 | fct7_0001001 => Ob~0~0~0~1~0~0~1
  | fct7_0001010 => Ob~0~0~0~1~0~1~0 | fct7_0001011 => Ob~0~0~0~1~0~1~1
  | fct7_0001100 => Ob~0~0~0~1~1~0~0 | fct7_0001101 => Ob~0~0~0~1~1~0~1
  | fct7_0001110 => Ob~0~0~0~1~1~1~0 | fct7_0001111 => Ob~0~0~0~1~1~1~1
  | fct7_0010000 => Ob~0~0~1~0~0~0~0 | fct7_0010001 => Ob~0~0~1~0~0~0~1
  | fct7_0010010 => Ob~0~0~1~0~0~1~0 | fct7_0010011 => Ob~0~0~1~0~0~1~1
  | fct7_0010100 => Ob~0~0~1~0~1~0~0 | fct7_0010101 => Ob~0~0~1~0~1~0~1
  | fct7_0010111 => Ob~0~0~1~0~1~1~1 | fct7_0100000 => Ob~0~1~0~0~0~0~0
  | fct7_0100001 => Ob~0~1~0~0~0~0~1 | fct7_0100010 => Ob~0~1~0~0~0~1~0
  | fct7_0100011 => Ob~0~1~0~0~0~1~1 | fct7_0101100 => Ob~0~1~0~1~1~0~0
  | fct7_0101101 => Ob~0~1~0~1~1~0~1 | fct7_0101111 => Ob~0~1~0~1~1~1~1
  | fct7_0110000 => Ob~0~1~1~0~0~0~0 | fct7_0110001 => Ob~0~1~1~0~0~0~1
  | fct7_0110010 => Ob~0~1~1~0~0~1~0 | fct7_0110011 => Ob~0~1~1~0~0~1~1
  | fct7_1000000 => Ob~1~0~0~0~0~0~0 | fct7_1000001 => Ob~1~0~0~0~0~0~1
  | fct7_1000010 => Ob~1~0~0~0~0~1~0 | fct7_1000011 => Ob~1~0~0~0~0~1~1
  | fct7_1010000 => Ob~1~0~1~0~0~0~0 | fct7_1010001 => Ob~1~0~1~0~0~0~1
  | fct7_1010010 => Ob~1~0~1~0~0~1~0 | fct7_1010011 => Ob~1~0~1~0~0~1~1
  | fct7_1100000 => Ob~1~1~0~0~0~0~0 | fct7_1100001 => Ob~1~1~0~0~0~0~1
  | fct7_1100010 => Ob~1~1~0~0~0~1~0 | fct7_1100011 => Ob~1~1~0~0~0~1~1
  | fct7_1101000 => Ob~1~1~0~1~0~0~0 | fct7_1101001 => Ob~1~1~0~1~0~0~1
  | fct7_1101011 => Ob~1~1~0~1~0~1~1 | fct7_1110000 => Ob~1~1~1~0~0~0~0
  | fct7_1110001 => Ob~1~1~1~0~0~0~1 | fct7_1110010 => Ob~1~1~1~0~0~1~0
  | fct7_1110011 => Ob~1~1~1~0~0~1~1 | fct7_1111000 => Ob~1~1~1~1~0~0~0
  | fct7_1111001 => Ob~1~1~1~1~0~0~1 | fct7_1111011 => Ob~1~1~1~1~0~1~1
  end.

Definition instruction_fct7 :
  forall (i : instruction), has_fct7 (get_instruction_i_type i) = true
  -> fct7_type.
Proof.
refine (fun i =>
  match i with
  | ADD_32I           => fun _ => fct7_0000000
  | SUB_32I           => fun _ => fct7_0100000
  | SLL_32I           => fun _ => fct7_0000000
  | SLT_32I           => fun _ => fct7_0000000
  | SLTU_32I          => fun _ => fct7_0000000
  | XOR_32I           => fun _ => fct7_0000000
  | SRL_32I           => fun _ => fct7_0000000
  | SRA_32I           => fun _ => fct7_0100000
  | OR_32I            => fun _ => fct7_0000000
  | AND_32I           => fun _ => fct7_0000000
  | ADD_64I           => fun _ => fct7_0000000
  | SUB_64I           => fun _ => fct7_0100000
  | SLL_64I           => fun _ => fct7_0000000
  | SLT_64I           => fun _ => fct7_0000000
  | SLTU_64I          => fun _ => fct7_0000000
  | XOR_64I           => fun _ => fct7_0000000
  | SRL_64I           => fun _ => fct7_0000000
  | SRA_64I           => fun _ => fct7_0100000
  | OR_64I            => fun _ => fct7_0000000
  | AND_64I           => fun _ => fct7_0000000
  | ADDW_64I          => fun _ => fct7_0000000
  | SUBW_64I          => fun _ => fct7_0100000
  | SLLW_64I          => fun _ => fct7_0000000
  | SRLW_64I          => fun _ => fct7_0000000
  | SRAW_64I          => fun _ => fct7_0100000
  | MUL_32M           => fun _ => fct7_0000001
  | MULH_32M          => fun _ => fct7_0000001
  | MULHSU_32M        => fun _ => fct7_0000001
  | MULHU_32M         => fun _ => fct7_0000001
  | DIV_32M           => fun _ => fct7_0000001
  | DIVU_32M          => fun _ => fct7_0000001
  | REM_32M           => fun _ => fct7_0000001
  | REMU_32M          => fun _ => fct7_0000001
  | MUL_64M           => fun _ => fct7_0000001
  | MULH_64M          => fun _ => fct7_0000001
  | MULHSU_64M        => fun _ => fct7_0000001
  | MULHU_64M         => fun _ => fct7_0000001
  | DIV_64M           => fun _ => fct7_0000001
  | DIVU_64M          => fun _ => fct7_0000001
  | REM_64M           => fun _ => fct7_0000001
  | REMU_64M          => fun _ => fct7_0000001
  | MULW_64M          => fun _ => fct7_0000001
  | DIVW_64M          => fun _ => fct7_0000001
  | DIVUW_64M         => fun _ => fct7_0000001
  | REMW_64M          => fun _ => fct7_0000001
  | REMUW_64M         => fun _ => fct7_0000001
  | LR_W_00_32A       => fun _ => fct7_0001000
  | LR_W_01_32A       => fun _ => fct7_0001001
  | LR_W_10_32A       => fun _ => fct7_0001010
  | LR_W_11_32A       => fun _ => fct7_0001011
  | SC_W_00_32A       => fun _ => fct7_0001100
  | SC_W_01_32A       => fun _ => fct7_0001101
  | SC_W_10_32A       => fun _ => fct7_0001110
  | SC_W_11_32A       => fun _ => fct7_0001111
  | AMOSWAP_W_00_32A  => fun _ => fct7_0000100
  | AMOSWAP_W_01_32A  => fun _ => fct7_0000101
  | AMOSWAP_W_10_32A  => fun _ => fct7_0000110
  | AMOSWAP_W_11_32A  => fun _ => fct7_0000111
  | AMOADD_W_00_32A   => fun _ => fct7_0000000
  | AMOADD_W_01_32A   => fun _ => fct7_0000001
  | AMOADD_W_10_32A   => fun _ => fct7_0000010
  | AMOADD_W_11_32A   => fun _ => fct7_0000011
  | AMOXOR_W_00_32A   => fun _ => fct7_0010000
  | AMOXOR_W_01_32A   => fun _ => fct7_0010001
  | AMOXOR_W_10_32A   => fun _ => fct7_0010010
  | AMOXOR_W_11_32A   => fun _ => fct7_0010011
  | AMOAND_W_00_32A   => fun _ => fct7_0110000
  | AMOAND_W_01_32A   => fun _ => fct7_0110001
  | AMOAND_W_10_32A   => fun _ => fct7_0110010
  | AMOAND_W_11_32A   => fun _ => fct7_0110011
  | AMOOR_W_00_32A    => fun _ => fct7_0100000
  | AMOOR_W_01_32A    => fun _ => fct7_0100001
  | AMOOR_W_10_32A    => fun _ => fct7_0100010
  | AMOOR_W_11_32A    => fun _ => fct7_0100011
  | AMOMIN_W_00_32A   => fun _ => fct7_1000000
  | AMOMIN_W_01_32A   => fun _ => fct7_1000001
  | AMOMIN_W_10_32A   => fun _ => fct7_1000010
  | AMOMIN_W_11_32A   => fun _ => fct7_1000011
  | AMOMAX_W_00_32A   => fun _ => fct7_1010000
  | AMOMAX_W_01_32A   => fun _ => fct7_1010001
  | AMOMAX_W_10_32A   => fun _ => fct7_1010010
  | AMOMAX_W_11_32A   => fun _ => fct7_1010011
  | AMOMINU_W_00_32A  => fun _ => fct7_1100000
  | AMOMINU_W_01_32A  => fun _ => fct7_1100001
  | AMOMINU_W_10_32A  => fun _ => fct7_1100010
  | AMOMINU_W_11_32A  => fun _ => fct7_1100011
  | AMOMAXU_W_00_32A  => fun _ => fct7_1110000
  | AMOMAXU_W_01_32A  => fun _ => fct7_1110001
  | AMOMAXU_W_10_32A  => fun _ => fct7_1110010
  | AMOMAXU_W_11_32A  => fun _ => fct7_1110011
  | LR_W_00_64A       => fun _ => fct7_0001000
  | LR_W_01_64A       => fun _ => fct7_0001001
  | LR_W_10_64A       => fun _ => fct7_0001010
  | LR_W_11_64A       => fun _ => fct7_0001011
  | SC_W_00_64A       => fun _ => fct7_0001100
  | SC_W_01_64A       => fun _ => fct7_0001101
  | SC_W_10_64A       => fun _ => fct7_0001110
  | SC_W_11_64A       => fun _ => fct7_0001111
  | AMOSWAP_W_00_64A  => fun _ => fct7_0000100
  | AMOSWAP_W_01_64A  => fun _ => fct7_0000101
  | AMOSWAP_W_10_64A  => fun _ => fct7_0000110
  | AMOSWAP_W_11_64A  => fun _ => fct7_0000111
  | AMOADD_W_00_64A   => fun _ => fct7_0000000
  | AMOADD_W_01_64A   => fun _ => fct7_0000001
  | AMOADD_W_10_64A   => fun _ => fct7_0000010
  | AMOADD_W_11_64A   => fun _ => fct7_0000011
  | AMOXOR_W_00_64A   => fun _ => fct7_0010000
  | AMOXOR_W_01_64A   => fun _ => fct7_0010001
  | AMOXOR_W_10_64A   => fun _ => fct7_0010010
  | AMOXOR_W_11_64A   => fun _ => fct7_0010011
  | AMOAND_W_00_64A   => fun _ => fct7_0110000
  | AMOAND_W_01_64A   => fun _ => fct7_0110001
  | AMOAND_W_10_64A   => fun _ => fct7_0110010
  | AMOAND_W_11_64A   => fun _ => fct7_0110011
  | AMOOR_W_00_64A    => fun _ => fct7_0100000
  | AMOOR_W_01_64A    => fun _ => fct7_0100001
  | AMOOR_W_10_64A    => fun _ => fct7_0100010
  | AMOOR_W_11_64A    => fun _ => fct7_0100011
  | AMOMIN_W_00_64A   => fun _ => fct7_1000000
  | AMOMIN_W_01_64A   => fun _ => fct7_1000001
  | AMOMIN_W_10_64A   => fun _ => fct7_1000010
  | AMOMIN_W_11_64A   => fun _ => fct7_1000011
  | AMOMAX_W_00_64A   => fun _ => fct7_1010000
  | AMOMAX_W_01_64A   => fun _ => fct7_1010001
  | AMOMAX_W_10_64A   => fun _ => fct7_1010010
  | AMOMAX_W_11_64A   => fun _ => fct7_1010011
  | AMOMINU_W_00_64A  => fun _ => fct7_1100000
  | AMOMINU_W_01_64A  => fun _ => fct7_1100001
  | AMOMINU_W_10_64A  => fun _ => fct7_1100010
  | AMOMINU_W_11_64A  => fun _ => fct7_1100011
  | AMOMAXU_W_00_64A  => fun _ => fct7_1110000
  | AMOMAXU_W_01_64A  => fun _ => fct7_1110001
  | AMOMAXU_W_10_64A  => fun _ => fct7_1110010
  | AMOMAXU_W_11_64A  => fun _ => fct7_1110011
  | LR_D_00_64A       => fun _ => fct7_0001000
  | LR_D_01_64A       => fun _ => fct7_0001001
  | LR_D_10_64A       => fun _ => fct7_0001010
  | LR_D_11_64A       => fun _ => fct7_0001011
  | SC_D_00_64A       => fun _ => fct7_0001100
  | SC_D_01_64A       => fun _ => fct7_0001101
  | SC_D_10_64A       => fun _ => fct7_0001110
  | SC_D_11_64A       => fun _ => fct7_0001111
  | AMOSWAP_D_00_64A  => fun _ => fct7_0000100
  | AMOSWAP_D_01_64A  => fun _ => fct7_0000101
  | AMOSWAP_D_10_64A  => fun _ => fct7_0000110
  | AMOSWAP_D_11_64A  => fun _ => fct7_0000111
  | AMOADD_D_00_64A   => fun _ => fct7_0000000
  | AMOADD_D_01_64A   => fun _ => fct7_0000001
  | AMOADD_D_10_64A   => fun _ => fct7_0000010
  | AMOADD_D_11_64A   => fun _ => fct7_0000011
  | AMOXOR_D_00_64A   => fun _ => fct7_0010000
  | AMOXOR_D_01_64A   => fun _ => fct7_0010001
  | AMOXOR_D_10_64A   => fun _ => fct7_0010010
  | AMOXOR_D_11_64A   => fun _ => fct7_0010011
  | AMOAND_D_00_64A   => fun _ => fct7_0110000
  | AMOAND_D_01_64A   => fun _ => fct7_0110001
  | AMOAND_D_10_64A   => fun _ => fct7_0110010
  | AMOAND_D_11_64A   => fun _ => fct7_0110011
  | AMOOR_D_00_64A    => fun _ => fct7_0100000
  | AMOOR_D_01_64A    => fun _ => fct7_0100001
  | AMOOR_D_10_64A    => fun _ => fct7_0100010
  | AMOOR_D_11_64A    => fun _ => fct7_0100011
  | AMOMIN_D_00_64A   => fun _ => fct7_1000000
  | AMOMIN_D_01_64A   => fun _ => fct7_1000001
  | AMOMIN_D_10_64A   => fun _ => fct7_1000010
  | AMOMIN_D_11_64A   => fun _ => fct7_1000011
  | AMOMAX_D_00_64A   => fun _ => fct7_1010000
  | AMOMAX_D_01_64A   => fun _ => fct7_1010001
  | AMOMAX_D_10_64A   => fun _ => fct7_1010010
  | AMOMAX_D_11_64A   => fun _ => fct7_1010011
  | AMOMINU_D_00_64A  => fun _ => fct7_1100000
  | AMOMINU_D_01_64A  => fun _ => fct7_1100001
  | AMOMINU_D_10_64A  => fun _ => fct7_1100010
  | AMOMINU_D_11_64A  => fun _ => fct7_1100011
  | AMOMAXU_D_00_64A  => fun _ => fct7_1110000
  | AMOMAXU_D_01_64A  => fun _ => fct7_1110001
  | AMOMAXU_D_10_64A  => fun _ => fct7_1110010
  | AMOMAXU_D_11_64A  => fun _ => fct7_1110011
  | FADD_RNE_S_32F    => fun _ => fct7_0000000
  | FADD_RTZ_S_32F    => fun _ => fct7_0000000
  | FADD_RDN_S_32F    => fun _ => fct7_0000000
  | FADD_RUP_S_32F    => fun _ => fct7_0000000
  | FADD_RMM_S_32F    => fun _ => fct7_0000000
  | FADD_DYN_S_32F    => fun _ => fct7_0000000
  | FSUB_RNE_S_32F    => fun _ => fct7_0000100
  | FSUB_RTZ_S_32F    => fun _ => fct7_0000100
  | FSUB_RDN_S_32F    => fun _ => fct7_0000100
  | FSUB_RUP_S_32F    => fun _ => fct7_0000100
  | FSUB_RMM_S_32F    => fun _ => fct7_0000100
  | FSUB_DYN_S_32F    => fun _ => fct7_0000100
  | FMUL_RNE_S_32F    => fun _ => fct7_0001000
  | FMUL_RTZ_S_32F    => fun _ => fct7_0001000
  | FMUL_RDN_S_32F    => fun _ => fct7_0001000
  | FMUL_RUP_S_32F    => fun _ => fct7_0001000
  | FMUL_RMM_S_32F    => fun _ => fct7_0001000
  | FMUL_DYN_S_32F    => fun _ => fct7_0001000
  | FDIV_RNE_S_32F    => fun _ => fct7_0001100
  | FDIV_RTZ_S_32F    => fun _ => fct7_0001100
  | FDIV_RDN_S_32F    => fun _ => fct7_0001100
  | FDIV_RUP_S_32F    => fun _ => fct7_0001100
  | FDIV_RMM_S_32F    => fun _ => fct7_0001100
  | FDIV_DYN_S_32F    => fun _ => fct7_0001100
  | FSQRT_RNE_S_32F   => fun _ => fct7_0101100
  | FSQRT_RTZ_S_32F   => fun _ => fct7_0101100
  | FSQRT_RDN_S_32F   => fun _ => fct7_0101100
  | FSQRT_RUP_S_32F   => fun _ => fct7_0101100
  | FSQRT_RMM_S_32F   => fun _ => fct7_0101100
  | FSQRT_DYN_S_32F   => fun _ => fct7_0101100
  | FSGNJ_S_32F       => fun _ => fct7_0010000
  | FSGNJN_S_32F      => fun _ => fct7_0010000
  | FSGNJX_S_32F      => fun _ => fct7_0010000
  | FMIN_S_32F        => fun _ => fct7_0010100
  | FMAX_S_32F        => fun _ => fct7_0010100
  | FCVT_RNE_W_S_32F  => fun _ => fct7_1100000
  | FCVT_RTZ_W_S_32F  => fun _ => fct7_1100000
  | FCVT_RDN_W_S_32F  => fun _ => fct7_1100000
  | FCVT_RUP_W_S_32F  => fun _ => fct7_1100000
  | FCVT_RMM_W_S_32F  => fun _ => fct7_1100000
  | FCVT_DYN_W_S_32F  => fun _ => fct7_1100000
  | FCVT_RNE_WU_S_32F => fun _ => fct7_1100000
  | FCVT_RTZ_WU_S_32F => fun _ => fct7_1100000
  | FCVT_RDN_WU_S_32F => fun _ => fct7_1100000
  | FCVT_RUP_WU_S_32F => fun _ => fct7_1100000
  | FCVT_RMM_WU_S_32F => fun _ => fct7_1100000
  | FCVT_DYN_WU_S_32F => fun _ => fct7_1100000
  | FMV_X_W_32F       => fun _ => fct7_1110000
  | FEQ_S_32F         => fun _ => fct7_1010000
  | FLT_S_32F         => fun _ => fct7_1010000
  | FLE_S_32F         => fun _ => fct7_1010000
  | FCLASS_S_32F      => fun _ => fct7_1110000
  | FCVT_RNE_S_W_32F  => fun _ => fct7_1101000
  | FCVT_RTZ_S_W_32F  => fun _ => fct7_1101000
  | FCVT_RDN_S_W_32F  => fun _ => fct7_1101000
  | FCVT_RUP_S_W_32F  => fun _ => fct7_1101000
  | FCVT_RMM_S_W_32F  => fun _ => fct7_1101000
  | FCVT_DYN_S_W_32F  => fun _ => fct7_1101000
  | FCVT_RNE_S_WU_32F => fun _ => fct7_1101000
  | FCVT_RTZ_S_WU_32F => fun _ => fct7_1101000
  | FCVT_RDN_S_WU_32F => fun _ => fct7_1101000
  | FCVT_RUP_S_WU_32F => fun _ => fct7_1101000
  | FCVT_RMM_S_WU_32F => fun _ => fct7_1101000
  | FCVT_DYN_S_WU_32F => fun _ => fct7_1101000
  | FMV_W_X_32F       => fun _ => fct7_1111000
  | FADD_RNE_S_64F    => fun _ => fct7_0000000
  | FADD_RTZ_S_64F    => fun _ => fct7_0000000
  | FADD_RDN_S_64F    => fun _ => fct7_0000000
  | FADD_RUP_S_64F    => fun _ => fct7_0000000
  | FADD_RMM_S_64F    => fun _ => fct7_0000000
  | FADD_DYN_S_64F    => fun _ => fct7_0000000
  | FSUB_RNE_S_64F    => fun _ => fct7_0000100
  | FSUB_RTZ_S_64F    => fun _ => fct7_0000100
  | FSUB_RDN_S_64F    => fun _ => fct7_0000100
  | FSUB_RUP_S_64F    => fun _ => fct7_0000100
  | FSUB_RMM_S_64F    => fun _ => fct7_0000100
  | FSUB_DYN_S_64F    => fun _ => fct7_0000100
  | FMUL_RNE_S_64F    => fun _ => fct7_0001000
  | FMUL_RTZ_S_64F    => fun _ => fct7_0001000
  | FMUL_RDN_S_64F    => fun _ => fct7_0001000
  | FMUL_RUP_S_64F    => fun _ => fct7_0001000
  | FMUL_RMM_S_64F    => fun _ => fct7_0001000
  | FMUL_DYN_S_64F    => fun _ => fct7_0001000
  | FDIV_RNE_S_64F    => fun _ => fct7_0001100
  | FDIV_RTZ_S_64F    => fun _ => fct7_0001100
  | FDIV_RDN_S_64F    => fun _ => fct7_0001100
  | FDIV_RUP_S_64F    => fun _ => fct7_0001100
  | FDIV_RMM_S_64F    => fun _ => fct7_0001100
  | FDIV_DYN_S_64F    => fun _ => fct7_0001100
  | FSQRT_RNE_S_64F   => fun _ => fct7_0101100
  | FSQRT_RTZ_S_64F   => fun _ => fct7_0101100
  | FSQRT_RDN_S_64F   => fun _ => fct7_0101100
  | FSQRT_RUP_S_64F   => fun _ => fct7_0101100
  | FSQRT_RMM_S_64F   => fun _ => fct7_0101100
  | FSQRT_DYN_S_64F   => fun _ => fct7_0101100
  | FSGNJ_S_64F       => fun _ => fct7_0010000
  | FSGNJN_S_64F      => fun _ => fct7_0010000
  | FSGNJX_S_64F      => fun _ => fct7_0010000
  | FMIN_S_64F        => fun _ => fct7_0010100
  | FMAX_S_64F        => fun _ => fct7_0010100
  | FCVT_RNE_W_S_64F  => fun _ => fct7_1100000
  | FCVT_RTZ_W_S_64F  => fun _ => fct7_1100000
  | FCVT_RDN_W_S_64F  => fun _ => fct7_1100000
  | FCVT_RUP_W_S_64F  => fun _ => fct7_1100000
  | FCVT_RMM_W_S_64F  => fun _ => fct7_1100000
  | FCVT_DYN_W_S_64F  => fun _ => fct7_1100000
  | FCVT_RNE_WU_S_64F => fun _ => fct7_1100000
  | FCVT_RTZ_WU_S_64F => fun _ => fct7_1100000
  | FCVT_RDN_WU_S_64F => fun _ => fct7_1100000
  | FCVT_RUP_WU_S_64F => fun _ => fct7_1100000
  | FCVT_RMM_WU_S_64F => fun _ => fct7_1100000
  | FCVT_DYN_WU_S_64F => fun _ => fct7_1100000
  | FMV_X_W_64F       => fun _ => fct7_1110000
  | FEQ_S_64F         => fun _ => fct7_1010000
  | FLT_S_64F         => fun _ => fct7_1010000
  | FLE_S_64F         => fun _ => fct7_1010000
  | FCLASS_S_64F      => fun _ => fct7_1110000
  | FCVT_RNE_S_W_64F  => fun _ => fct7_1101000
  | FCVT_RTZ_S_W_64F  => fun _ => fct7_1101000
  | FCVT_RDN_S_W_64F  => fun _ => fct7_1101000
  | FCVT_RUP_S_W_64F  => fun _ => fct7_1101000
  | FCVT_RMM_S_W_64F  => fun _ => fct7_1101000
  | FCVT_DYN_S_W_64F  => fun _ => fct7_1101000
  | FCVT_RNE_S_WU_64F => fun _ => fct7_1101000
  | FCVT_RTZ_S_WU_64F => fun _ => fct7_1101000
  | FCVT_RDN_S_WU_64F => fun _ => fct7_1101000
  | FCVT_RUP_S_WU_64F => fun _ => fct7_1101000
  | FCVT_RMM_S_WU_64F => fun _ => fct7_1101000
  | FCVT_DYN_S_WU_64F => fun _ => fct7_1101000
  | FMV_W_X_64F       => fun _ => fct7_1111000
  | FCVT_RNE_L_S_64F  => fun _ => fct7_1100000
  | FCVT_RTZ_L_S_64F  => fun _ => fct7_1100000
  | FCVT_RDN_L_S_64F  => fun _ => fct7_1100000
  | FCVT_RUP_L_S_64F  => fun _ => fct7_1100000
  | FCVT_RMM_L_S_64F  => fun _ => fct7_1100000
  | FCVT_DYN_L_S_64F  => fun _ => fct7_1100000
  | FCVT_RNE_LU_S_64F => fun _ => fct7_1100000
  | FCVT_RTZ_LU_S_64F => fun _ => fct7_1100000
  | FCVT_RDN_LU_S_64F => fun _ => fct7_1100000
  | FCVT_RUP_LU_S_64F => fun _ => fct7_1100000
  | FCVT_RMM_LU_S_64F => fun _ => fct7_1100000
  | FCVT_DYN_LU_S_64F => fun _ => fct7_1100000
  | FCVT_RNE_S_L_64F  => fun _ => fct7_1101000
  | FCVT_RTZ_S_L_64F  => fun _ => fct7_1101000
  | FCVT_RDN_S_L_64F  => fun _ => fct7_1101000
  | FCVT_RUP_S_L_64F  => fun _ => fct7_1101000
  | FCVT_RMM_S_L_64F  => fun _ => fct7_1101000
  | FCVT_DYN_S_L_64F  => fun _ => fct7_1101000
  | FCVT_RNE_S_LU_64F => fun _ => fct7_1101000
  | FCVT_RTZ_S_LU_64F => fun _ => fct7_1101000
  | FCVT_RDN_S_LU_64F => fun _ => fct7_1101000
  | FCVT_RUP_S_LU_64F => fun _ => fct7_1101000
  | FCVT_RMM_S_LU_64F => fun _ => fct7_1101000
  | FCVT_DYN_S_LU_64F => fun _ => fct7_1101000
  | FADD_RNE_D_32D    => fun _ => fct7_0000001
  | FADD_RTZ_D_32D    => fun _ => fct7_0000001
  | FADD_RDN_D_32D    => fun _ => fct7_0000001
  | FADD_RUP_D_32D    => fun _ => fct7_0000001
  | FADD_RMM_D_32D    => fun _ => fct7_0000001
  | FADD_DYN_D_32D    => fun _ => fct7_0000001
  | FSUB_RNE_D_32D    => fun _ => fct7_0000101
  | FSUB_RTZ_D_32D    => fun _ => fct7_0000101
  | FSUB_RDN_D_32D    => fun _ => fct7_0000101
  | FSUB_RUP_D_32D    => fun _ => fct7_0000101
  | FSUB_RMM_D_32D    => fun _ => fct7_0000101
  | FSUB_DYN_D_32D    => fun _ => fct7_0000101
  | FMUL_RNE_D_32D    => fun _ => fct7_0001001
  | FMUL_RTZ_D_32D    => fun _ => fct7_0001001
  | FMUL_RDN_D_32D    => fun _ => fct7_0001001
  | FMUL_RUP_D_32D    => fun _ => fct7_0001001
  | FMUL_RMM_D_32D    => fun _ => fct7_0001001
  | FMUL_DYN_D_32D    => fun _ => fct7_0001001
  | FDIV_RNE_D_32D    => fun _ => fct7_0001101
  | FDIV_RTZ_D_32D    => fun _ => fct7_0001101
  | FDIV_RDN_D_32D    => fun _ => fct7_0001101
  | FDIV_RUP_D_32D    => fun _ => fct7_0001101
  | FDIV_RMM_D_32D    => fun _ => fct7_0001101
  | FDIV_DYN_D_32D    => fun _ => fct7_0001101
  | FSQRT_RNE_D_32D   => fun _ => fct7_0101101
  | FSQRT_RTZ_D_32D   => fun _ => fct7_0101101
  | FSQRT_RDN_D_32D   => fun _ => fct7_0101101
  | FSQRT_RUP_D_32D   => fun _ => fct7_0101101
  | FSQRT_RMM_D_32D   => fun _ => fct7_0101101
  | FSQRT_DYN_D_32D   => fun _ => fct7_0101101
  | FSGNJ_D_32D       => fun _ => fct7_0010001
  | FSGNJN_D_32D      => fun _ => fct7_0010001
  | FSGNJX_D_32D      => fun _ => fct7_0010001
  | FMIN_D_32D        => fun _ => fct7_0010101
  | FMAX_D_32D        => fun _ => fct7_0010101
  | FCVT_RNE_S_D_32D  => fun _ => fct7_0100000
  | FCVT_RTZ_S_D_32D  => fun _ => fct7_0100000
  | FCVT_RDN_S_D_32D  => fun _ => fct7_0100000
  | FCVT_RUP_S_D_32D  => fun _ => fct7_0100000
  | FCVT_RMM_S_D_32D  => fun _ => fct7_0100000
  | FCVT_DYN_S_D_32D  => fun _ => fct7_0100000
  | FCVT_RNE_D_S_32D  => fun _ => fct7_0100001
  | FCVT_RTZ_D_S_32D  => fun _ => fct7_0100001
  | FCVT_RDN_D_S_32D  => fun _ => fct7_0100001
  | FCVT_RUP_D_S_32D  => fun _ => fct7_0100001
  | FCVT_RMM_D_S_32D  => fun _ => fct7_0100001
  | FCVT_DYN_D_S_32D  => fun _ => fct7_0100001
  | FEQ_D_32D         => fun _ => fct7_1010001
  | FLT_D_32D         => fun _ => fct7_1010001
  | FLE_D_32D         => fun _ => fct7_1010001
  | FCLASS_D_32D      => fun _ => fct7_1110001
  | FCVT_RNE_W_D_32D  => fun _ => fct7_1100001
  | FCVT_RTZ_W_D_32D  => fun _ => fct7_1100001
  | FCVT_RDN_W_D_32D  => fun _ => fct7_1100001
  | FCVT_RUP_W_D_32D  => fun _ => fct7_1100001
  | FCVT_RMM_W_D_32D  => fun _ => fct7_1100001
  | FCVT_DYN_W_D_32D  => fun _ => fct7_1100001
  | FCVT_RNE_WU_D_32D => fun _ => fct7_1100001
  | FCVT_RTZ_WU_D_32D => fun _ => fct7_1100001
  | FCVT_RDN_WU_D_32D => fun _ => fct7_1100001
  | FCVT_RUP_WU_D_32D => fun _ => fct7_1100001
  | FCVT_RMM_WU_D_32D => fun _ => fct7_1100001
  | FCVT_DYN_WU_D_32D => fun _ => fct7_1100001
  | FCVT_RNE_D_W_32D  => fun _ => fct7_1101001
  | FCVT_RTZ_D_W_32D  => fun _ => fct7_1101001
  | FCVT_RDN_D_W_32D  => fun _ => fct7_1101001
  | FCVT_RUP_D_W_32D  => fun _ => fct7_1101001
  | FCVT_RMM_D_W_32D  => fun _ => fct7_1101001
  | FCVT_DYN_D_W_32D  => fun _ => fct7_1101001
  | FCVT_RNE_D_WU_32D => fun _ => fct7_1101001
  | FCVT_RTZ_D_WU_32D => fun _ => fct7_1101001
  | FCVT_RDN_D_WU_32D => fun _ => fct7_1101001
  | FCVT_RUP_D_WU_32D => fun _ => fct7_1101001
  | FCVT_RMM_D_WU_32D => fun _ => fct7_1101001
  | FCVT_DYN_D_WU_32D => fun _ => fct7_1101001
  | FADD_RNE_D_64D    => fun _ => fct7_0000001
  | FADD_RTZ_D_64D    => fun _ => fct7_0000001
  | FADD_RDN_D_64D    => fun _ => fct7_0000001
  | FADD_RUP_D_64D    => fun _ => fct7_0000001
  | FADD_RMM_D_64D    => fun _ => fct7_0000001
  | FADD_DYN_D_64D    => fun _ => fct7_0000001
  | FSUB_RNE_D_64D    => fun _ => fct7_0000101
  | FSUB_RTZ_D_64D    => fun _ => fct7_0000101
  | FSUB_RDN_D_64D    => fun _ => fct7_0000101
  | FSUB_RUP_D_64D    => fun _ => fct7_0000101
  | FSUB_RMM_D_64D    => fun _ => fct7_0000101
  | FSUB_DYN_D_64D    => fun _ => fct7_0000101
  | FMUL_RNE_D_64D    => fun _ => fct7_0001001
  | FMUL_RTZ_D_64D    => fun _ => fct7_0001001
  | FMUL_RDN_D_64D    => fun _ => fct7_0001001
  | FMUL_RUP_D_64D    => fun _ => fct7_0001001
  | FMUL_RMM_D_64D    => fun _ => fct7_0001001
  | FMUL_DYN_D_64D    => fun _ => fct7_0001001
  | FDIV_RNE_D_64D    => fun _ => fct7_0001101
  | FDIV_RTZ_D_64D    => fun _ => fct7_0001101
  | FDIV_RDN_D_64D    => fun _ => fct7_0001101
  | FDIV_RUP_D_64D    => fun _ => fct7_0001101
  | FDIV_RMM_D_64D    => fun _ => fct7_0001101
  | FDIV_DYN_D_64D    => fun _ => fct7_0001101
  | FSQRT_RNE_D_64D   => fun _ => fct7_0101101
  | FSQRT_RTZ_D_64D   => fun _ => fct7_0101101
  | FSQRT_RDN_D_64D   => fun _ => fct7_0101101
  | FSQRT_RUP_D_64D   => fun _ => fct7_0101101
  | FSQRT_RMM_D_64D   => fun _ => fct7_0101101
  | FSQRT_DYN_D_64D   => fun _ => fct7_0101101
  | FSGNJ_D_64D       => fun _ => fct7_0010001
  | FSGNJN_D_64D      => fun _ => fct7_0010001
  | FSGNJX_D_64D      => fun _ => fct7_0010001
  | FMIN_D_64D        => fun _ => fct7_0010101
  | FMAX_D_64D        => fun _ => fct7_0010101
  | FCVT_RNE_S_D_64D  => fun _ => fct7_0100000
  | FCVT_RTZ_S_D_64D  => fun _ => fct7_0100000
  | FCVT_RDN_S_D_64D  => fun _ => fct7_0100000
  | FCVT_RUP_S_D_64D  => fun _ => fct7_0100000
  | FCVT_RMM_S_D_64D  => fun _ => fct7_0100000
  | FCVT_DYN_S_D_64D  => fun _ => fct7_0100000
  | FCVT_RNE_D_S_64D  => fun _ => fct7_0100001
  | FCVT_RTZ_D_S_64D  => fun _ => fct7_0100001
  | FCVT_RDN_D_S_64D  => fun _ => fct7_0100001
  | FCVT_RUP_D_S_64D  => fun _ => fct7_0100001
  | FCVT_RMM_D_S_64D  => fun _ => fct7_0100001
  | FCVT_DYN_D_S_64D  => fun _ => fct7_0100001
  | FEQ_D_64D         => fun _ => fct7_1010001
  | FLT_D_64D         => fun _ => fct7_1010001
  | FLE_D_64D         => fun _ => fct7_1010001
  | FCLASS_D_64D      => fun _ => fct7_1110001
  | FCVT_RNE_W_D_64D  => fun _ => fct7_1100001
  | FCVT_RTZ_W_D_64D  => fun _ => fct7_1100001
  | FCVT_RDN_W_D_64D  => fun _ => fct7_1100001
  | FCVT_RUP_W_D_64D  => fun _ => fct7_1100001
  | FCVT_RMM_W_D_64D  => fun _ => fct7_1100001
  | FCVT_DYN_W_D_64D  => fun _ => fct7_1100001
  | FCVT_RNE_WU_D_64D => fun _ => fct7_1100001
  | FCVT_RTZ_WU_D_64D => fun _ => fct7_1100001
  | FCVT_RDN_WU_D_64D => fun _ => fct7_1100001
  | FCVT_RUP_WU_D_64D => fun _ => fct7_1100001
  | FCVT_RMM_WU_D_64D => fun _ => fct7_1100001
  | FCVT_DYN_WU_D_64D => fun _ => fct7_1100001
  | FCVT_RNE_D_W_64D  => fun _ => fct7_1101001
  | FCVT_RTZ_D_W_64D  => fun _ => fct7_1101001
  | FCVT_RDN_D_W_64D  => fun _ => fct7_1101001
  | FCVT_RUP_D_W_64D  => fun _ => fct7_1101001
  | FCVT_RMM_D_W_64D  => fun _ => fct7_1101001
  | FCVT_DYN_D_W_64D  => fun _ => fct7_1101001
  | FCVT_RNE_D_WU_64D => fun _ => fct7_1101001
  | FCVT_RTZ_D_WU_64D => fun _ => fct7_1101001
  | FCVT_RDN_D_WU_64D => fun _ => fct7_1101001
  | FCVT_RUP_D_WU_64D => fun _ => fct7_1101001
  | FCVT_RMM_D_WU_64D => fun _ => fct7_1101001
  | FCVT_DYN_D_WU_64D => fun _ => fct7_1101001
  | FCVT_RNE_L_D_64D  => fun _ => fct7_1100001
  | FCVT_RTZ_L_D_64D  => fun _ => fct7_1100001
  | FCVT_RDN_L_D_64D  => fun _ => fct7_1100001
  | FCVT_RUP_L_D_64D  => fun _ => fct7_1100001
  | FCVT_RMM_L_D_64D  => fun _ => fct7_1100001
  | FCVT_DYN_L_D_64D  => fun _ => fct7_1100001
  | FCVT_RNE_LU_D_64D => fun _ => fct7_1100001
  | FCVT_RTZ_LU_D_64D => fun _ => fct7_1100001
  | FCVT_RDN_LU_D_64D => fun _ => fct7_1100001
  | FCVT_RUP_LU_D_64D => fun _ => fct7_1100001
  | FCVT_RMM_LU_D_64D => fun _ => fct7_1100001
  | FCVT_DYN_LU_D_64D => fun _ => fct7_1100001
  | FMV_X_D_64D       => fun _ => fct7_1110001
  | FCVT_RNE_D_L_64D  => fun _ => fct7_1101001
  | FCVT_RTZ_D_L_64D  => fun _ => fct7_1101001
  | FCVT_RDN_D_L_64D  => fun _ => fct7_1101001
  | FCVT_RUP_D_L_64D  => fun _ => fct7_1101001
  | FCVT_RMM_D_L_64D  => fun _ => fct7_1101001
  | FCVT_DYN_D_L_64D  => fun _ => fct7_1101001
  | FCVT_RNE_D_LU_64D => fun _ => fct7_1101001
  | FCVT_RTZ_D_LU_64D => fun _ => fct7_1101001
  | FCVT_RDN_D_LU_64D => fun _ => fct7_1101001
  | FCVT_RUP_D_LU_64D => fun _ => fct7_1101001
  | FCVT_RMM_D_LU_64D => fun _ => fct7_1101001
  | FCVT_DYN_D_LU_64D => fun _ => fct7_1101001
  | FMV_D_X_64D       => fun _ => fct7_1111001
  | FADD_RNE_Q_32Q    => fun _ => fct7_0000011
  | FADD_RTZ_Q_32Q    => fun _ => fct7_0000011
  | FADD_RDN_Q_32Q    => fun _ => fct7_0000011
  | FADD_RUP_Q_32Q    => fun _ => fct7_0000011
  | FADD_RMM_Q_32Q    => fun _ => fct7_0000011
  | FADD_DYN_Q_32Q    => fun _ => fct7_0000011
  | FSUB_RNE_Q_32Q    => fun _ => fct7_0000111
  | FSUB_RTZ_Q_32Q    => fun _ => fct7_0000111
  | FSUB_RDN_Q_32Q    => fun _ => fct7_0000111
  | FSUB_RUP_Q_32Q    => fun _ => fct7_0000111
  | FSUB_RMM_Q_32Q    => fun _ => fct7_0000111
  | FSUB_DYN_Q_32Q    => fun _ => fct7_0000111
  | FMUL_RNE_Q_32Q    => fun _ => fct7_0001011
  | FMUL_RTZ_Q_32Q    => fun _ => fct7_0001011
  | FMUL_RDN_Q_32Q    => fun _ => fct7_0001011
  | FMUL_RUP_Q_32Q    => fun _ => fct7_0001011
  | FMUL_RMM_Q_32Q    => fun _ => fct7_0001011
  | FMUL_DYN_Q_32Q    => fun _ => fct7_0001011
  | FDIV_RNE_Q_32Q    => fun _ => fct7_0001111
  | FDIV_RTZ_Q_32Q    => fun _ => fct7_0001111
  | FDIV_RDN_Q_32Q    => fun _ => fct7_0001111
  | FDIV_RUP_Q_32Q    => fun _ => fct7_0001111
  | FDIV_RMM_Q_32Q    => fun _ => fct7_0001111
  | FDIV_DYN_Q_32Q    => fun _ => fct7_0001111
  | FSQRT_RNE_Q_32Q   => fun _ => fct7_0101111
  | FSQRT_RTZ_Q_32Q   => fun _ => fct7_0101111
  | FSQRT_RDN_Q_32Q   => fun _ => fct7_0101111
  | FSQRT_RUP_Q_32Q   => fun _ => fct7_0101111
  | FSQRT_RMM_Q_32Q   => fun _ => fct7_0101111
  | FSQRT_DYN_Q_32Q   => fun _ => fct7_0101111
  | FSGNJ_Q_32Q       => fun _ => fct7_0010011
  | FSGNJN_Q_32Q      => fun _ => fct7_0010011
  | FSGNJX_Q_32Q      => fun _ => fct7_0010011
  | FMIN_Q_32Q        => fun _ => fct7_0010111
  | FMAX_Q_32Q        => fun _ => fct7_0010111
  | FCVT_RNE_S_Q_32Q  => fun _ => fct7_0100000
  | FCVT_RTZ_S_Q_32Q  => fun _ => fct7_0100000
  | FCVT_RDN_S_Q_32Q  => fun _ => fct7_0100000
  | FCVT_RUP_S_Q_32Q  => fun _ => fct7_0100000
  | FCVT_RMM_S_Q_32Q  => fun _ => fct7_0100000
  | FCVT_DYN_S_Q_32Q  => fun _ => fct7_0100000
  | FCVT_RNE_Q_S_32Q  => fun _ => fct7_0100011
  | FCVT_RTZ_Q_S_32Q  => fun _ => fct7_0100011
  | FCVT_RDN_Q_S_32Q  => fun _ => fct7_0100011
  | FCVT_RUP_Q_S_32Q  => fun _ => fct7_0100011
  | FCVT_RMM_Q_S_32Q  => fun _ => fct7_0100011
  | FCVT_DYN_Q_S_32Q  => fun _ => fct7_0100011
  | FCVT_RNE_D_Q_32Q  => fun _ => fct7_0100001
  | FCVT_RTZ_D_Q_32Q  => fun _ => fct7_0100001
  | FCVT_RDN_D_Q_32Q  => fun _ => fct7_0100001
  | FCVT_RUP_D_Q_32Q  => fun _ => fct7_0100001
  | FCVT_RMM_D_Q_32Q  => fun _ => fct7_0100001
  | FCVT_DYN_D_Q_32Q  => fun _ => fct7_0100001
  | FCVT_RNE_Q_D_32Q  => fun _ => fct7_0100011
  | FCVT_RTZ_Q_D_32Q  => fun _ => fct7_0100011
  | FCVT_RDN_Q_D_32Q  => fun _ => fct7_0100011
  | FCVT_RUP_Q_D_32Q  => fun _ => fct7_0100011
  | FCVT_RMM_Q_D_32Q  => fun _ => fct7_0100011
  | FCVT_DYN_Q_D_32Q  => fun _ => fct7_0100011
  | FEQ_Q_32Q         => fun _ => fct7_1010011
  | FLT_Q_32Q         => fun _ => fct7_1010011
  | FLE_Q_32Q         => fun _ => fct7_1010011
  | FCLASS_Q_32Q      => fun _ => fct7_1110011
  | FCVT_RNE_W_Q_32Q  => fun _ => fct7_1100011
  | FCVT_RTZ_W_Q_32Q  => fun _ => fct7_1100011
  | FCVT_RDN_W_Q_32Q  => fun _ => fct7_1100011
  | FCVT_RUP_W_Q_32Q  => fun _ => fct7_1100011
  | FCVT_RMM_W_Q_32Q  => fun _ => fct7_1100011
  | FCVT_DYN_W_Q_32Q  => fun _ => fct7_1100011
  | FCVT_RNE_WU_Q_32Q => fun _ => fct7_1100011
  | FCVT_RTZ_WU_Q_32Q => fun _ => fct7_1100011
  | FCVT_RDN_WU_Q_32Q => fun _ => fct7_1100011
  | FCVT_RUP_WU_Q_32Q => fun _ => fct7_1100011
  | FCVT_RMM_WU_Q_32Q => fun _ => fct7_1100011
  | FCVT_DYN_WU_Q_32Q => fun _ => fct7_1100011
  | FCVT_RNE_Q_W_32Q  => fun _ => fct7_1101011
  | FCVT_RTZ_Q_W_32Q  => fun _ => fct7_1101011
  | FCVT_RDN_Q_W_32Q  => fun _ => fct7_1101011
  | FCVT_RUP_Q_W_32Q  => fun _ => fct7_1101011
  | FCVT_RMM_Q_W_32Q  => fun _ => fct7_1101011
  | FCVT_DYN_Q_W_32Q  => fun _ => fct7_1101011
  | FCVT_RNE_Q_WU_32Q => fun _ => fct7_1101011
  | FCVT_RTZ_Q_WU_32Q => fun _ => fct7_1101011
  | FCVT_RDN_Q_WU_32Q => fun _ => fct7_1101011
  | FCVT_RUP_Q_WU_32Q => fun _ => fct7_1101011
  | FCVT_RMM_Q_WU_32Q => fun _ => fct7_1101011
  | FCVT_DYN_Q_WU_32Q => fun _ => fct7_1101011
  | FADD_RNE_Q_64Q    => fun _ => fct7_0000011
  | FADD_RTZ_Q_64Q    => fun _ => fct7_0000011
  | FADD_RDN_Q_64Q    => fun _ => fct7_0000011
  | FADD_RUP_Q_64Q    => fun _ => fct7_0000011
  | FADD_RMM_Q_64Q    => fun _ => fct7_0000011
  | FADD_DYN_Q_64Q    => fun _ => fct7_0000011
  | FSUB_RNE_Q_64Q    => fun _ => fct7_0000111
  | FSUB_RTZ_Q_64Q    => fun _ => fct7_0000111
  | FSUB_RDN_Q_64Q    => fun _ => fct7_0000111
  | FSUB_RUP_Q_64Q    => fun _ => fct7_0000111
  | FSUB_RMM_Q_64Q    => fun _ => fct7_0000111
  | FSUB_DYN_Q_64Q    => fun _ => fct7_0000111
  | FMUL_RNE_Q_64Q    => fun _ => fct7_0001011
  | FMUL_RTZ_Q_64Q    => fun _ => fct7_0001011
  | FMUL_RDN_Q_64Q    => fun _ => fct7_0001011
  | FMUL_RUP_Q_64Q    => fun _ => fct7_0001011
  | FMUL_RMM_Q_64Q    => fun _ => fct7_0001011
  | FMUL_DYN_Q_64Q    => fun _ => fct7_0001011
  | FDIV_RNE_Q_64Q    => fun _ => fct7_0001111
  | FDIV_RTZ_Q_64Q    => fun _ => fct7_0001111
  | FDIV_RDN_Q_64Q    => fun _ => fct7_0001111
  | FDIV_RUP_Q_64Q    => fun _ => fct7_0001111
  | FDIV_RMM_Q_64Q    => fun _ => fct7_0001111
  | FDIV_DYN_Q_64Q    => fun _ => fct7_0001111
  | FSQRT_RNE_Q_64Q   => fun _ => fct7_0101111
  | FSQRT_RTZ_Q_64Q   => fun _ => fct7_0101111
  | FSQRT_RDN_Q_64Q   => fun _ => fct7_0101111
  | FSQRT_RUP_Q_64Q   => fun _ => fct7_0101111
  | FSQRT_RMM_Q_64Q   => fun _ => fct7_0101111
  | FSQRT_DYN_Q_64Q   => fun _ => fct7_0101111
  | FSGNJ_Q_64Q       => fun _ => fct7_0010011
  | FSGNJN_Q_64Q      => fun _ => fct7_0010011
  | FSGNJX_Q_64Q      => fun _ => fct7_0010011
  | FMIN_Q_64Q        => fun _ => fct7_0010111
  | FMAX_Q_64Q        => fun _ => fct7_0010111
  | FCVT_RNE_S_Q_64Q  => fun _ => fct7_0100000
  | FCVT_RTZ_S_Q_64Q  => fun _ => fct7_0100000
  | FCVT_RDN_S_Q_64Q  => fun _ => fct7_0100000
  | FCVT_RUP_S_Q_64Q  => fun _ => fct7_0100000
  | FCVT_RMM_S_Q_64Q  => fun _ => fct7_0100000
  | FCVT_DYN_S_Q_64Q  => fun _ => fct7_0100000
  | FCVT_RNE_Q_S_64Q  => fun _ => fct7_0100011
  | FCVT_RTZ_Q_S_64Q  => fun _ => fct7_0100011
  | FCVT_RDN_Q_S_64Q  => fun _ => fct7_0100011
  | FCVT_RUP_Q_S_64Q  => fun _ => fct7_0100011
  | FCVT_RMM_Q_S_64Q  => fun _ => fct7_0100011
  | FCVT_DYN_Q_S_64Q  => fun _ => fct7_0100011
  | FCVT_RNE_D_Q_64Q  => fun _ => fct7_0100001
  | FCVT_RTZ_D_Q_64Q  => fun _ => fct7_0100001
  | FCVT_RDN_D_Q_64Q  => fun _ => fct7_0100001
  | FCVT_RUP_D_Q_64Q  => fun _ => fct7_0100001
  | FCVT_RMM_D_Q_64Q  => fun _ => fct7_0100001
  | FCVT_DYN_D_Q_64Q  => fun _ => fct7_0100001
  | FCVT_RNE_Q_D_64Q  => fun _ => fct7_0100011
  | FCVT_RTZ_Q_D_64Q  => fun _ => fct7_0100011
  | FCVT_RDN_Q_D_64Q  => fun _ => fct7_0100011
  | FCVT_RUP_Q_D_64Q  => fun _ => fct7_0100011
  | FCVT_RMM_Q_D_64Q  => fun _ => fct7_0100011
  | FCVT_DYN_Q_D_64Q  => fun _ => fct7_0100011
  | FEQ_Q_64Q         => fun _ => fct7_1010011
  | FLT_Q_64Q         => fun _ => fct7_1010011
  | FLE_Q_64Q         => fun _ => fct7_1010011
  | FCLASS_Q_64Q      => fun _ => fct7_1110011
  | FCVT_RNE_W_Q_64Q  => fun _ => fct7_1100011
  | FCVT_RTZ_W_Q_64Q  => fun _ => fct7_1100011
  | FCVT_RDN_W_Q_64Q  => fun _ => fct7_1100011
  | FCVT_RUP_W_Q_64Q  => fun _ => fct7_1100011
  | FCVT_RMM_W_Q_64Q  => fun _ => fct7_1100011
  | FCVT_DYN_W_Q_64Q  => fun _ => fct7_1100011
  | FCVT_RNE_WU_Q_64Q => fun _ => fct7_1100011
  | FCVT_RTZ_WU_Q_64Q => fun _ => fct7_1100011
  | FCVT_RDN_WU_Q_64Q => fun _ => fct7_1100011
  | FCVT_RUP_WU_Q_64Q => fun _ => fct7_1100011
  | FCVT_RMM_WU_Q_64Q => fun _ => fct7_1100011
  | FCVT_DYN_WU_Q_64Q => fun _ => fct7_1100011
  | FCVT_RNE_Q_W_64Q  => fun _ => fct7_1101011
  | FCVT_RTZ_Q_W_64Q  => fun _ => fct7_1101011
  | FCVT_RDN_Q_W_64Q  => fun _ => fct7_1101011
  | FCVT_RUP_Q_W_64Q  => fun _ => fct7_1101011
  | FCVT_RMM_Q_W_64Q  => fun _ => fct7_1101011
  | FCVT_DYN_Q_W_64Q  => fun _ => fct7_1101011
  | FCVT_RNE_Q_WU_64Q => fun _ => fct7_1101011
  | FCVT_RTZ_Q_WU_64Q => fun _ => fct7_1101011
  | FCVT_RDN_Q_WU_64Q => fun _ => fct7_1101011
  | FCVT_RUP_Q_WU_64Q => fun _ => fct7_1101011
  | FCVT_RMM_Q_WU_64Q => fun _ => fct7_1101011
  | FCVT_DYN_Q_WU_64Q => fun _ => fct7_1101011
  | FCVT_RNE_L_Q_64Q  => fun _ => fct7_1100011
  | FCVT_RTZ_L_Q_64Q  => fun _ => fct7_1100011
  | FCVT_RDN_L_Q_64Q  => fun _ => fct7_1100011
  | FCVT_RUP_L_Q_64Q  => fun _ => fct7_1100011
  | FCVT_RMM_L_Q_64Q  => fun _ => fct7_1100011
  | FCVT_DYN_L_Q_64Q  => fun _ => fct7_1100011
  | FCVT_RNE_LU_Q_64Q => fun _ => fct7_1100011
  | FCVT_RTZ_LU_Q_64Q => fun _ => fct7_1100011
  | FCVT_RDN_LU_Q_64Q => fun _ => fct7_1100011
  | FCVT_RUP_LU_Q_64Q => fun _ => fct7_1100011
  | FCVT_RMM_LU_Q_64Q => fun _ => fct7_1100011
  | FCVT_DYN_LU_Q_64Q => fun _ => fct7_1100011
  | FCVT_RNE_Q_L_64Q  => fun _ => fct7_1101011
  | FCVT_RTZ_Q_L_64Q  => fun _ => fct7_1101011
  | FCVT_RDN_Q_L_64Q  => fun _ => fct7_1101011
  | FCVT_RUP_Q_L_64Q  => fun _ => fct7_1101011
  | FCVT_RMM_Q_L_64Q  => fun _ => fct7_1101011
  | FCVT_DYN_Q_L_64Q  => fun _ => fct7_1101011
  | FCVT_RNE_Q_LU_64Q => fun _ => fct7_1101011
  | FCVT_RTZ_Q_LU_64Q => fun _ => fct7_1101011
  | FCVT_RDN_Q_LU_64Q => fun _ => fct7_1101011
  | FCVT_RUP_Q_LU_64Q => fun _ => fct7_1101011
  | FCVT_RMM_Q_LU_64Q => fun _ => fct7_1101011
  | FCVT_DYN_Q_LU_64Q => fun _ => fct7_1101011
  | _                 => fun _ => False_rec _ _
  end); try reflexivity; simpl in e; inversion e.
Defined.

Definition maybe_instruction_fct7 (i : instruction) : option fct7_type :=
  match i with
  | ADD_32I           => Some fct7_0000000
  | SUB_32I           => Some fct7_0100000
  | SLL_32I           => Some fct7_0000000
  | SLT_32I           => Some fct7_0000000
  | SLTU_32I          => Some fct7_0000000
  | XOR_32I           => Some fct7_0000000
  | SRL_32I           => Some fct7_0000000
  | SRA_32I           => Some fct7_0100000
  | OR_32I            => Some fct7_0000000
  | AND_32I           => Some fct7_0000000
  | ADD_64I           => Some fct7_0000000
  | SUB_64I           => Some fct7_0100000
  | SLL_64I           => Some fct7_0000000
  | SLT_64I           => Some fct7_0000000
  | SLTU_64I          => Some fct7_0000000
  | XOR_64I           => Some fct7_0000000
  | SRL_64I           => Some fct7_0000000
  | SRA_64I           => Some fct7_0100000
  | OR_64I            => Some fct7_0000000
  | AND_64I           => Some fct7_0000000
  | ADDW_64I          => Some fct7_0000000
  | SUBW_64I          => Some fct7_0100000
  | SLLW_64I          => Some fct7_0000000
  | SRLW_64I          => Some fct7_0000000
  | SRAW_64I          => Some fct7_0100000
  | MUL_32M           => Some fct7_0000001
  | MULH_32M          => Some fct7_0000001
  | MULHSU_32M        => Some fct7_0000001
  | MULHU_32M         => Some fct7_0000001
  | DIV_32M           => Some fct7_0000001
  | DIVU_32M          => Some fct7_0000001
  | REM_32M           => Some fct7_0000001
  | REMU_32M          => Some fct7_0000001
  | MUL_64M           => Some fct7_0000001
  | MULH_64M          => Some fct7_0000001
  | MULHSU_64M        => Some fct7_0000001
  | MULHU_64M         => Some fct7_0000001
  | DIV_64M           => Some fct7_0000001
  | DIVU_64M          => Some fct7_0000001
  | REM_64M           => Some fct7_0000001
  | REMU_64M          => Some fct7_0000001
  | MULW_64M          => Some fct7_0000001
  | DIVW_64M          => Some fct7_0000001
  | DIVUW_64M         => Some fct7_0000001
  | REMW_64M          => Some fct7_0000001
  | REMUW_64M         => Some fct7_0000001
  | LR_W_00_32A       => Some fct7_0001000
  | LR_W_01_32A       => Some fct7_0001001
  | LR_W_10_32A       => Some fct7_0001010
  | LR_W_11_32A       => Some fct7_0001011
  | SC_W_00_32A       => Some fct7_0001100
  | SC_W_01_32A       => Some fct7_0001101
  | SC_W_10_32A       => Some fct7_0001110
  | SC_W_11_32A       => Some fct7_0001111
  | AMOSWAP_W_00_32A  => Some fct7_0000100
  | AMOSWAP_W_01_32A  => Some fct7_0000101
  | AMOSWAP_W_10_32A  => Some fct7_0000110
  | AMOSWAP_W_11_32A  => Some fct7_0000111
  | AMOADD_W_00_32A   => Some fct7_0000000
  | AMOADD_W_01_32A   => Some fct7_0000001
  | AMOADD_W_10_32A   => Some fct7_0000010
  | AMOADD_W_11_32A   => Some fct7_0000011
  | AMOXOR_W_00_32A   => Some fct7_0010000
  | AMOXOR_W_01_32A   => Some fct7_0010001
  | AMOXOR_W_10_32A   => Some fct7_0010010
  | AMOXOR_W_11_32A   => Some fct7_0010011
  | AMOAND_W_00_32A   => Some fct7_0110000
  | AMOAND_W_01_32A   => Some fct7_0110001
  | AMOAND_W_10_32A   => Some fct7_0110010
  | AMOAND_W_11_32A   => Some fct7_0110011
  | AMOOR_W_00_32A    => Some fct7_0100000
  | AMOOR_W_01_32A    => Some fct7_0100001
  | AMOOR_W_10_32A    => Some fct7_0100010
  | AMOOR_W_11_32A    => Some fct7_0100011
  | AMOMIN_W_00_32A   => Some fct7_1000000
  | AMOMIN_W_01_32A   => Some fct7_1000001
  | AMOMIN_W_10_32A   => Some fct7_1000010
  | AMOMIN_W_11_32A   => Some fct7_1000011
  | AMOMAX_W_00_32A   => Some fct7_1010000
  | AMOMAX_W_01_32A   => Some fct7_1010001
  | AMOMAX_W_10_32A   => Some fct7_1010010
  | AMOMAX_W_11_32A   => Some fct7_1010011
  | AMOMINU_W_00_32A  => Some fct7_1100000
  | AMOMINU_W_01_32A  => Some fct7_1100001
  | AMOMINU_W_10_32A  => Some fct7_1100010
  | AMOMINU_W_11_32A  => Some fct7_1100011
  | AMOMAXU_W_00_32A  => Some fct7_1110000
  | AMOMAXU_W_01_32A  => Some fct7_1110001
  | AMOMAXU_W_10_32A  => Some fct7_1110010
  | AMOMAXU_W_11_32A  => Some fct7_1110011
  | LR_W_00_64A       => Some fct7_0001000
  | LR_W_01_64A       => Some fct7_0001001
  | LR_W_10_64A       => Some fct7_0001010
  | LR_W_11_64A       => Some fct7_0001011
  | SC_W_00_64A       => Some fct7_0001100
  | SC_W_01_64A       => Some fct7_0001101
  | SC_W_10_64A       => Some fct7_0001110
  | SC_W_11_64A       => Some fct7_0001111
  | AMOSWAP_W_00_64A  => Some fct7_0000100
  | AMOSWAP_W_01_64A  => Some fct7_0000101
  | AMOSWAP_W_10_64A  => Some fct7_0000110
  | AMOSWAP_W_11_64A  => Some fct7_0000111
  | AMOADD_W_00_64A   => Some fct7_0000000
  | AMOADD_W_01_64A   => Some fct7_0000001
  | AMOADD_W_10_64A   => Some fct7_0000010
  | AMOADD_W_11_64A   => Some fct7_0000011
  | AMOXOR_W_00_64A   => Some fct7_0010000
  | AMOXOR_W_01_64A   => Some fct7_0010001
  | AMOXOR_W_10_64A   => Some fct7_0010010
  | AMOXOR_W_11_64A   => Some fct7_0010011
  | AMOAND_W_00_64A   => Some fct7_0110000
  | AMOAND_W_01_64A   => Some fct7_0110001
  | AMOAND_W_10_64A   => Some fct7_0110010
  | AMOAND_W_11_64A   => Some fct7_0110011
  | AMOOR_W_00_64A    => Some fct7_0100000
  | AMOOR_W_01_64A    => Some fct7_0100001
  | AMOOR_W_10_64A    => Some fct7_0100010
  | AMOOR_W_11_64A    => Some fct7_0100011
  | AMOMIN_W_00_64A   => Some fct7_1000000
  | AMOMIN_W_01_64A   => Some fct7_1000001
  | AMOMIN_W_10_64A   => Some fct7_1000010
  | AMOMIN_W_11_64A   => Some fct7_1000011
  | AMOMAX_W_00_64A   => Some fct7_1010000
  | AMOMAX_W_01_64A   => Some fct7_1010001
  | AMOMAX_W_10_64A   => Some fct7_1010010
  | AMOMAX_W_11_64A   => Some fct7_1010011
  | AMOMINU_W_00_64A  => Some fct7_1100000
  | AMOMINU_W_01_64A  => Some fct7_1100001
  | AMOMINU_W_10_64A  => Some fct7_1100010
  | AMOMINU_W_11_64A  => Some fct7_1100011
  | AMOMAXU_W_00_64A  => Some fct7_1110000
  | AMOMAXU_W_01_64A  => Some fct7_1110001
  | AMOMAXU_W_10_64A  => Some fct7_1110010
  | AMOMAXU_W_11_64A  => Some fct7_1110011
  | LR_D_00_64A       => Some fct7_0001000
  | LR_D_01_64A       => Some fct7_0001001
  | LR_D_10_64A       => Some fct7_0001010
  | LR_D_11_64A       => Some fct7_0001011
  | SC_D_00_64A       => Some fct7_0001100
  | SC_D_01_64A       => Some fct7_0001101
  | SC_D_10_64A       => Some fct7_0001110
  | SC_D_11_64A       => Some fct7_0001111
  | AMOSWAP_D_00_64A  => Some fct7_0000100
  | AMOSWAP_D_01_64A  => Some fct7_0000101
  | AMOSWAP_D_10_64A  => Some fct7_0000110
  | AMOSWAP_D_11_64A  => Some fct7_0000111
  | AMOADD_D_00_64A   => Some fct7_0000000
  | AMOADD_D_01_64A   => Some fct7_0000001
  | AMOADD_D_10_64A   => Some fct7_0000010
  | AMOADD_D_11_64A   => Some fct7_0000011
  | AMOXOR_D_00_64A   => Some fct7_0010000
  | AMOXOR_D_01_64A   => Some fct7_0010001
  | AMOXOR_D_10_64A   => Some fct7_0010010
  | AMOXOR_D_11_64A   => Some fct7_0010011
  | AMOAND_D_00_64A   => Some fct7_0110000
  | AMOAND_D_01_64A   => Some fct7_0110001
  | AMOAND_D_10_64A   => Some fct7_0110010
  | AMOAND_D_11_64A   => Some fct7_0110011
  | AMOOR_D_00_64A    => Some fct7_0100000
  | AMOOR_D_01_64A    => Some fct7_0100001
  | AMOOR_D_10_64A    => Some fct7_0100010
  | AMOOR_D_11_64A    => Some fct7_0100011
  | AMOMIN_D_00_64A   => Some fct7_1000000
  | AMOMIN_D_01_64A   => Some fct7_1000001
  | AMOMIN_D_10_64A   => Some fct7_1000010
  | AMOMIN_D_11_64A   => Some fct7_1000011
  | AMOMAX_D_00_64A   => Some fct7_1010000
  | AMOMAX_D_01_64A   => Some fct7_1010001
  | AMOMAX_D_10_64A   => Some fct7_1010010
  | AMOMAX_D_11_64A   => Some fct7_1010011
  | AMOMINU_D_00_64A  => Some fct7_1100000
  | AMOMINU_D_01_64A  => Some fct7_1100001
  | AMOMINU_D_10_64A  => Some fct7_1100010
  | AMOMINU_D_11_64A  => Some fct7_1100011
  | AMOMAXU_D_00_64A  => Some fct7_1110000
  | AMOMAXU_D_01_64A  => Some fct7_1110001
  | AMOMAXU_D_10_64A  => Some fct7_1110010
  | AMOMAXU_D_11_64A  => Some fct7_1110011
  | FADD_RNE_S_32F    => Some fct7_0000000
  | FADD_RTZ_S_32F    => Some fct7_0000000
  | FADD_RDN_S_32F    => Some fct7_0000000
  | FADD_RUP_S_32F    => Some fct7_0000000
  | FADD_RMM_S_32F    => Some fct7_0000000
  | FADD_DYN_S_32F    => Some fct7_0000000
  | FSUB_RNE_S_32F    => Some fct7_0000100
  | FSUB_RTZ_S_32F    => Some fct7_0000100
  | FSUB_RDN_S_32F    => Some fct7_0000100
  | FSUB_RUP_S_32F    => Some fct7_0000100
  | FSUB_RMM_S_32F    => Some fct7_0000100
  | FSUB_DYN_S_32F    => Some fct7_0000100
  | FMUL_RNE_S_32F    => Some fct7_0001000
  | FMUL_RTZ_S_32F    => Some fct7_0001000
  | FMUL_RDN_S_32F    => Some fct7_0001000
  | FMUL_RUP_S_32F    => Some fct7_0001000
  | FMUL_RMM_S_32F    => Some fct7_0001000
  | FMUL_DYN_S_32F    => Some fct7_0001000
  | FDIV_RNE_S_32F    => Some fct7_0001100
  | FDIV_RTZ_S_32F    => Some fct7_0001100
  | FDIV_RDN_S_32F    => Some fct7_0001100
  | FDIV_RUP_S_32F    => Some fct7_0001100
  | FDIV_RMM_S_32F    => Some fct7_0001100
  | FDIV_DYN_S_32F    => Some fct7_0001100
  | FSQRT_RNE_S_32F   => Some fct7_0101100
  | FSQRT_RTZ_S_32F   => Some fct7_0101100
  | FSQRT_RDN_S_32F   => Some fct7_0101100
  | FSQRT_RUP_S_32F   => Some fct7_0101100
  | FSQRT_RMM_S_32F   => Some fct7_0101100
  | FSQRT_DYN_S_32F   => Some fct7_0101100
  | FSGNJ_S_32F       => Some fct7_0010000
  | FSGNJN_S_32F      => Some fct7_0010000
  | FSGNJX_S_32F      => Some fct7_0010000
  | FMIN_S_32F        => Some fct7_0010100
  | FMAX_S_32F        => Some fct7_0010100
  | FCVT_RNE_W_S_32F  => Some fct7_1100000
  | FCVT_RTZ_W_S_32F  => Some fct7_1100000
  | FCVT_RDN_W_S_32F  => Some fct7_1100000
  | FCVT_RUP_W_S_32F  => Some fct7_1100000
  | FCVT_RMM_W_S_32F  => Some fct7_1100000
  | FCVT_DYN_W_S_32F  => Some fct7_1100000
  | FCVT_RNE_WU_S_32F => Some fct7_1100000
  | FCVT_RTZ_WU_S_32F => Some fct7_1100000
  | FCVT_RDN_WU_S_32F => Some fct7_1100000
  | FCVT_RUP_WU_S_32F => Some fct7_1100000
  | FCVT_RMM_WU_S_32F => Some fct7_1100000
  | FCVT_DYN_WU_S_32F => Some fct7_1100000
  | FMV_X_W_32F       => Some fct7_1110000
  | FEQ_S_32F         => Some fct7_1010000
  | FLT_S_32F         => Some fct7_1010000
  | FLE_S_32F         => Some fct7_1010000
  | FCLASS_S_32F      => Some fct7_1110000
  | FCVT_RNE_S_W_32F  => Some fct7_1101000
  | FCVT_RTZ_S_W_32F  => Some fct7_1101000
  | FCVT_RDN_S_W_32F  => Some fct7_1101000
  | FCVT_RUP_S_W_32F  => Some fct7_1101000
  | FCVT_RMM_S_W_32F  => Some fct7_1101000
  | FCVT_DYN_S_W_32F  => Some fct7_1101000
  | FCVT_RNE_S_WU_32F => Some fct7_1101000
  | FCVT_RTZ_S_WU_32F => Some fct7_1101000
  | FCVT_RDN_S_WU_32F => Some fct7_1101000
  | FCVT_RUP_S_WU_32F => Some fct7_1101000
  | FCVT_RMM_S_WU_32F => Some fct7_1101000
  | FCVT_DYN_S_WU_32F => Some fct7_1101000
  | FMV_W_X_32F       => Some fct7_1111000
  | FADD_RNE_S_64F    => Some fct7_0000000
  | FADD_RTZ_S_64F    => Some fct7_0000000
  | FADD_RDN_S_64F    => Some fct7_0000000
  | FADD_RUP_S_64F    => Some fct7_0000000
  | FADD_RMM_S_64F    => Some fct7_0000000
  | FADD_DYN_S_64F    => Some fct7_0000000
  | FSUB_RNE_S_64F    => Some fct7_0000100
  | FSUB_RTZ_S_64F    => Some fct7_0000100
  | FSUB_RDN_S_64F    => Some fct7_0000100
  | FSUB_RUP_S_64F    => Some fct7_0000100
  | FSUB_RMM_S_64F    => Some fct7_0000100
  | FSUB_DYN_S_64F    => Some fct7_0000100
  | FMUL_RNE_S_64F    => Some fct7_0001000
  | FMUL_RTZ_S_64F    => Some fct7_0001000
  | FMUL_RDN_S_64F    => Some fct7_0001000
  | FMUL_RUP_S_64F    => Some fct7_0001000
  | FMUL_RMM_S_64F    => Some fct7_0001000
  | FMUL_DYN_S_64F    => Some fct7_0001000
  | FDIV_RNE_S_64F    => Some fct7_0001100
  | FDIV_RTZ_S_64F    => Some fct7_0001100
  | FDIV_RDN_S_64F    => Some fct7_0001100
  | FDIV_RUP_S_64F    => Some fct7_0001100
  | FDIV_RMM_S_64F    => Some fct7_0001100
  | FDIV_DYN_S_64F    => Some fct7_0001100
  | FSQRT_RNE_S_64F   => Some fct7_0101100
  | FSQRT_RTZ_S_64F   => Some fct7_0101100
  | FSQRT_RDN_S_64F   => Some fct7_0101100
  | FSQRT_RUP_S_64F   => Some fct7_0101100
  | FSQRT_RMM_S_64F   => Some fct7_0101100
  | FSQRT_DYN_S_64F   => Some fct7_0101100
  | FSGNJ_S_64F       => Some fct7_0010000
  | FSGNJN_S_64F      => Some fct7_0010000
  | FSGNJX_S_64F      => Some fct7_0010000
  | FMIN_S_64F        => Some fct7_0010100
  | FMAX_S_64F        => Some fct7_0010100
  | FCVT_RNE_W_S_64F  => Some fct7_1100000
  | FCVT_RTZ_W_S_64F  => Some fct7_1100000
  | FCVT_RDN_W_S_64F  => Some fct7_1100000
  | FCVT_RUP_W_S_64F  => Some fct7_1100000
  | FCVT_RMM_W_S_64F  => Some fct7_1100000
  | FCVT_DYN_W_S_64F  => Some fct7_1100000
  | FCVT_RNE_WU_S_64F => Some fct7_1100000
  | FCVT_RTZ_WU_S_64F => Some fct7_1100000
  | FCVT_RDN_WU_S_64F => Some fct7_1100000
  | FCVT_RUP_WU_S_64F => Some fct7_1100000
  | FCVT_RMM_WU_S_64F => Some fct7_1100000
  | FCVT_DYN_WU_S_64F => Some fct7_1100000
  | FMV_X_W_64F       => Some fct7_1110000
  | FEQ_S_64F         => Some fct7_1010000
  | FLT_S_64F         => Some fct7_1010000
  | FLE_S_64F         => Some fct7_1010000
  | FCLASS_S_64F      => Some fct7_1110000
  | FCVT_RNE_S_W_64F  => Some fct7_1101000
  | FCVT_RTZ_S_W_64F  => Some fct7_1101000
  | FCVT_RDN_S_W_64F  => Some fct7_1101000
  | FCVT_RUP_S_W_64F  => Some fct7_1101000
  | FCVT_RMM_S_W_64F  => Some fct7_1101000
  | FCVT_DYN_S_W_64F  => Some fct7_1101000
  | FCVT_RNE_S_WU_64F => Some fct7_1101000
  | FCVT_RTZ_S_WU_64F => Some fct7_1101000
  | FCVT_RDN_S_WU_64F => Some fct7_1101000
  | FCVT_RUP_S_WU_64F => Some fct7_1101000
  | FCVT_RMM_S_WU_64F => Some fct7_1101000
  | FCVT_DYN_S_WU_64F => Some fct7_1101000
  | FMV_W_X_64F       => Some fct7_1111000
  | FCVT_RNE_L_S_64F  => Some fct7_1100000
  | FCVT_RTZ_L_S_64F  => Some fct7_1100000
  | FCVT_RDN_L_S_64F  => Some fct7_1100000
  | FCVT_RUP_L_S_64F  => Some fct7_1100000
  | FCVT_RMM_L_S_64F  => Some fct7_1100000
  | FCVT_DYN_L_S_64F  => Some fct7_1100000
  | FCVT_RNE_LU_S_64F => Some fct7_1100000
  | FCVT_RTZ_LU_S_64F => Some fct7_1100000
  | FCVT_RDN_LU_S_64F => Some fct7_1100000
  | FCVT_RUP_LU_S_64F => Some fct7_1100000
  | FCVT_RMM_LU_S_64F => Some fct7_1100000
  | FCVT_DYN_LU_S_64F => Some fct7_1100000
  | FCVT_RNE_S_L_64F  => Some fct7_1101000
  | FCVT_RTZ_S_L_64F  => Some fct7_1101000
  | FCVT_RDN_S_L_64F  => Some fct7_1101000
  | FCVT_RUP_S_L_64F  => Some fct7_1101000
  | FCVT_RMM_S_L_64F  => Some fct7_1101000
  | FCVT_DYN_S_L_64F  => Some fct7_1101000
  | FCVT_RNE_S_LU_64F => Some fct7_1101000
  | FCVT_RTZ_S_LU_64F => Some fct7_1101000
  | FCVT_RDN_S_LU_64F => Some fct7_1101000
  | FCVT_RUP_S_LU_64F => Some fct7_1101000
  | FCVT_RMM_S_LU_64F => Some fct7_1101000
  | FCVT_DYN_S_LU_64F => Some fct7_1101000
  | FADD_RNE_D_32D    => Some fct7_0000001
  | FADD_RTZ_D_32D    => Some fct7_0000001
  | FADD_RDN_D_32D    => Some fct7_0000001
  | FADD_RUP_D_32D    => Some fct7_0000001
  | FADD_RMM_D_32D    => Some fct7_0000001
  | FADD_DYN_D_32D    => Some fct7_0000001
  | FSUB_RNE_D_32D    => Some fct7_0000101
  | FSUB_RTZ_D_32D    => Some fct7_0000101
  | FSUB_RDN_D_32D    => Some fct7_0000101
  | FSUB_RUP_D_32D    => Some fct7_0000101
  | FSUB_RMM_D_32D    => Some fct7_0000101
  | FSUB_DYN_D_32D    => Some fct7_0000101
  | FMUL_RNE_D_32D    => Some fct7_0001001
  | FMUL_RTZ_D_32D    => Some fct7_0001001
  | FMUL_RDN_D_32D    => Some fct7_0001001
  | FMUL_RUP_D_32D    => Some fct7_0001001
  | FMUL_RMM_D_32D    => Some fct7_0001001
  | FMUL_DYN_D_32D    => Some fct7_0001001
  | FDIV_RNE_D_32D    => Some fct7_0001101
  | FDIV_RTZ_D_32D    => Some fct7_0001101
  | FDIV_RDN_D_32D    => Some fct7_0001101
  | FDIV_RUP_D_32D    => Some fct7_0001101
  | FDIV_RMM_D_32D    => Some fct7_0001101
  | FDIV_DYN_D_32D    => Some fct7_0001101
  | FSQRT_RNE_D_32D   => Some fct7_0101101
  | FSQRT_RTZ_D_32D   => Some fct7_0101101
  | FSQRT_RDN_D_32D   => Some fct7_0101101
  | FSQRT_RUP_D_32D   => Some fct7_0101101
  | FSQRT_RMM_D_32D   => Some fct7_0101101
  | FSQRT_DYN_D_32D   => Some fct7_0101101
  | FSGNJ_D_32D       => Some fct7_0010001
  | FSGNJN_D_32D      => Some fct7_0010001
  | FSGNJX_D_32D      => Some fct7_0010001
  | FMIN_D_32D        => Some fct7_0010101
  | FMAX_D_32D        => Some fct7_0010101
  | FCVT_RNE_S_D_32D  => Some fct7_0100000
  | FCVT_RTZ_S_D_32D  => Some fct7_0100000
  | FCVT_RDN_S_D_32D  => Some fct7_0100000
  | FCVT_RUP_S_D_32D  => Some fct7_0100000
  | FCVT_RMM_S_D_32D  => Some fct7_0100000
  | FCVT_DYN_S_D_32D  => Some fct7_0100000
  | FCVT_RNE_D_S_32D  => Some fct7_0100001
  | FCVT_RTZ_D_S_32D  => Some fct7_0100001
  | FCVT_RDN_D_S_32D  => Some fct7_0100001
  | FCVT_RUP_D_S_32D  => Some fct7_0100001
  | FCVT_RMM_D_S_32D  => Some fct7_0100001
  | FCVT_DYN_D_S_32D  => Some fct7_0100001
  | FEQ_D_32D         => Some fct7_1010001
  | FLT_D_32D         => Some fct7_1010001
  | FLE_D_32D         => Some fct7_1010001
  | FCLASS_D_32D      => Some fct7_1110001
  | FCVT_RNE_W_D_32D  => Some fct7_1100001
  | FCVT_RTZ_W_D_32D  => Some fct7_1100001
  | FCVT_RDN_W_D_32D  => Some fct7_1100001
  | FCVT_RUP_W_D_32D  => Some fct7_1100001
  | FCVT_RMM_W_D_32D  => Some fct7_1100001
  | FCVT_DYN_W_D_32D  => Some fct7_1100001
  | FCVT_RNE_WU_D_32D => Some fct7_1100001
  | FCVT_RTZ_WU_D_32D => Some fct7_1100001
  | FCVT_RDN_WU_D_32D => Some fct7_1100001
  | FCVT_RUP_WU_D_32D => Some fct7_1100001
  | FCVT_RMM_WU_D_32D => Some fct7_1100001
  | FCVT_DYN_WU_D_32D => Some fct7_1100001
  | FCVT_RNE_D_W_32D  => Some fct7_1101001
  | FCVT_RTZ_D_W_32D  => Some fct7_1101001
  | FCVT_RDN_D_W_32D  => Some fct7_1101001
  | FCVT_RUP_D_W_32D  => Some fct7_1101001
  | FCVT_RMM_D_W_32D  => Some fct7_1101001
  | FCVT_DYN_D_W_32D  => Some fct7_1101001
  | FCVT_RNE_D_WU_32D => Some fct7_1101001
  | FCVT_RTZ_D_WU_32D => Some fct7_1101001
  | FCVT_RDN_D_WU_32D => Some fct7_1101001
  | FCVT_RUP_D_WU_32D => Some fct7_1101001
  | FCVT_RMM_D_WU_32D => Some fct7_1101001
  | FCVT_DYN_D_WU_32D => Some fct7_1101001
  | FADD_RNE_D_64D    => Some fct7_0000001
  | FADD_RTZ_D_64D    => Some fct7_0000001
  | FADD_RDN_D_64D    => Some fct7_0000001
  | FADD_RUP_D_64D    => Some fct7_0000001
  | FADD_RMM_D_64D    => Some fct7_0000001
  | FADD_DYN_D_64D    => Some fct7_0000001
  | FSUB_RNE_D_64D    => Some fct7_0000101
  | FSUB_RTZ_D_64D    => Some fct7_0000101
  | FSUB_RDN_D_64D    => Some fct7_0000101
  | FSUB_RUP_D_64D    => Some fct7_0000101
  | FSUB_RMM_D_64D    => Some fct7_0000101
  | FSUB_DYN_D_64D    => Some fct7_0000101
  | FMUL_RNE_D_64D    => Some fct7_0001001
  | FMUL_RTZ_D_64D    => Some fct7_0001001
  | FMUL_RDN_D_64D    => Some fct7_0001001
  | FMUL_RUP_D_64D    => Some fct7_0001001
  | FMUL_RMM_D_64D    => Some fct7_0001001
  | FMUL_DYN_D_64D    => Some fct7_0001001
  | FDIV_RNE_D_64D    => Some fct7_0001101
  | FDIV_RTZ_D_64D    => Some fct7_0001101
  | FDIV_RDN_D_64D    => Some fct7_0001101
  | FDIV_RUP_D_64D    => Some fct7_0001101
  | FDIV_RMM_D_64D    => Some fct7_0001101
  | FDIV_DYN_D_64D    => Some fct7_0001101
  | FSQRT_RNE_D_64D   => Some fct7_0101101
  | FSQRT_RTZ_D_64D   => Some fct7_0101101
  | FSQRT_RDN_D_64D   => Some fct7_0101101
  | FSQRT_RUP_D_64D   => Some fct7_0101101
  | FSQRT_RMM_D_64D   => Some fct7_0101101
  | FSQRT_DYN_D_64D   => Some fct7_0101101
  | FSGNJ_D_64D       => Some fct7_0010001
  | FSGNJN_D_64D      => Some fct7_0010001
  | FSGNJX_D_64D      => Some fct7_0010001
  | FMIN_D_64D        => Some fct7_0010101
  | FMAX_D_64D        => Some fct7_0010101
  | FCVT_RNE_S_D_64D  => Some fct7_0100000
  | FCVT_RTZ_S_D_64D  => Some fct7_0100000
  | FCVT_RDN_S_D_64D  => Some fct7_0100000
  | FCVT_RUP_S_D_64D  => Some fct7_0100000
  | FCVT_RMM_S_D_64D  => Some fct7_0100000
  | FCVT_DYN_S_D_64D  => Some fct7_0100000
  | FCVT_RNE_D_S_64D  => Some fct7_0100001
  | FCVT_RTZ_D_S_64D  => Some fct7_0100001
  | FCVT_RDN_D_S_64D  => Some fct7_0100001
  | FCVT_RUP_D_S_64D  => Some fct7_0100001
  | FCVT_RMM_D_S_64D  => Some fct7_0100001
  | FCVT_DYN_D_S_64D  => Some fct7_0100001
  | FEQ_D_64D         => Some fct7_1010001
  | FLT_D_64D         => Some fct7_1010001
  | FLE_D_64D         => Some fct7_1010001
  | FCLASS_D_64D      => Some fct7_1110001
  | FCVT_RNE_W_D_64D  => Some fct7_1100001
  | FCVT_RTZ_W_D_64D  => Some fct7_1100001
  | FCVT_RDN_W_D_64D  => Some fct7_1100001
  | FCVT_RUP_W_D_64D  => Some fct7_1100001
  | FCVT_RMM_W_D_64D  => Some fct7_1100001
  | FCVT_DYN_W_D_64D  => Some fct7_1100001
  | FCVT_RNE_WU_D_64D => Some fct7_1100001
  | FCVT_RTZ_WU_D_64D => Some fct7_1100001
  | FCVT_RDN_WU_D_64D => Some fct7_1100001
  | FCVT_RUP_WU_D_64D => Some fct7_1100001
  | FCVT_RMM_WU_D_64D => Some fct7_1100001
  | FCVT_DYN_WU_D_64D => Some fct7_1100001
  | FCVT_RNE_D_W_64D  => Some fct7_1101001
  | FCVT_RTZ_D_W_64D  => Some fct7_1101001
  | FCVT_RDN_D_W_64D  => Some fct7_1101001
  | FCVT_RUP_D_W_64D  => Some fct7_1101001
  | FCVT_RMM_D_W_64D  => Some fct7_1101001
  | FCVT_DYN_D_W_64D  => Some fct7_1101001
  | FCVT_RNE_D_WU_64D => Some fct7_1101001
  | FCVT_RTZ_D_WU_64D => Some fct7_1101001
  | FCVT_RDN_D_WU_64D => Some fct7_1101001
  | FCVT_RUP_D_WU_64D => Some fct7_1101001
  | FCVT_RMM_D_WU_64D => Some fct7_1101001
  | FCVT_DYN_D_WU_64D => Some fct7_1101001
  | FCVT_RNE_L_D_64D  => Some fct7_1100001
  | FCVT_RTZ_L_D_64D  => Some fct7_1100001
  | FCVT_RDN_L_D_64D  => Some fct7_1100001
  | FCVT_RUP_L_D_64D  => Some fct7_1100001
  | FCVT_RMM_L_D_64D  => Some fct7_1100001
  | FCVT_DYN_L_D_64D  => Some fct7_1100001
  | FCVT_RNE_LU_D_64D => Some fct7_1100001
  | FCVT_RTZ_LU_D_64D => Some fct7_1100001
  | FCVT_RDN_LU_D_64D => Some fct7_1100001
  | FCVT_RUP_LU_D_64D => Some fct7_1100001
  | FCVT_RMM_LU_D_64D => Some fct7_1100001
  | FCVT_DYN_LU_D_64D => Some fct7_1100001
  | FMV_X_D_64D       => Some fct7_1110001
  | FCVT_RNE_D_L_64D  => Some fct7_1101001
  | FCVT_RTZ_D_L_64D  => Some fct7_1101001
  | FCVT_RDN_D_L_64D  => Some fct7_1101001
  | FCVT_RUP_D_L_64D  => Some fct7_1101001
  | FCVT_RMM_D_L_64D  => Some fct7_1101001
  | FCVT_DYN_D_L_64D  => Some fct7_1101001
  | FCVT_RNE_D_LU_64D => Some fct7_1101001
  | FCVT_RTZ_D_LU_64D => Some fct7_1101001
  | FCVT_RDN_D_LU_64D => Some fct7_1101001
  | FCVT_RUP_D_LU_64D => Some fct7_1101001
  | FCVT_RMM_D_LU_64D => Some fct7_1101001
  | FCVT_DYN_D_LU_64D => Some fct7_1101001
  | FMV_D_X_64D       => Some fct7_1111001
  | FADD_RNE_Q_32Q    => Some fct7_0000011
  | FADD_RTZ_Q_32Q    => Some fct7_0000011
  | FADD_RDN_Q_32Q    => Some fct7_0000011
  | FADD_RUP_Q_32Q    => Some fct7_0000011
  | FADD_RMM_Q_32Q    => Some fct7_0000011
  | FADD_DYN_Q_32Q    => Some fct7_0000011
  | FSUB_RNE_Q_32Q    => Some fct7_0000111
  | FSUB_RTZ_Q_32Q    => Some fct7_0000111
  | FSUB_RDN_Q_32Q    => Some fct7_0000111
  | FSUB_RUP_Q_32Q    => Some fct7_0000111
  | FSUB_RMM_Q_32Q    => Some fct7_0000111
  | FSUB_DYN_Q_32Q    => Some fct7_0000111
  | FMUL_RNE_Q_32Q    => Some fct7_0001011
  | FMUL_RTZ_Q_32Q    => Some fct7_0001011
  | FMUL_RDN_Q_32Q    => Some fct7_0001011
  | FMUL_RUP_Q_32Q    => Some fct7_0001011
  | FMUL_RMM_Q_32Q    => Some fct7_0001011
  | FMUL_DYN_Q_32Q    => Some fct7_0001011
  | FDIV_RNE_Q_32Q    => Some fct7_0001111
  | FDIV_RTZ_Q_32Q    => Some fct7_0001111
  | FDIV_RDN_Q_32Q    => Some fct7_0001111
  | FDIV_RUP_Q_32Q    => Some fct7_0001111
  | FDIV_RMM_Q_32Q    => Some fct7_0001111
  | FDIV_DYN_Q_32Q    => Some fct7_0001111
  | FSQRT_RNE_Q_32Q   => Some fct7_0101111
  | FSQRT_RTZ_Q_32Q   => Some fct7_0101111
  | FSQRT_RDN_Q_32Q   => Some fct7_0101111
  | FSQRT_RUP_Q_32Q   => Some fct7_0101111
  | FSQRT_RMM_Q_32Q   => Some fct7_0101111
  | FSQRT_DYN_Q_32Q   => Some fct7_0101111
  | FSGNJ_Q_32Q       => Some fct7_0010011
  | FSGNJN_Q_32Q      => Some fct7_0010011
  | FSGNJX_Q_32Q      => Some fct7_0010011
  | FMIN_Q_32Q        => Some fct7_0010111
  | FMAX_Q_32Q        => Some fct7_0010111
  | FCVT_RNE_S_Q_32Q  => Some fct7_0100000
  | FCVT_RTZ_S_Q_32Q  => Some fct7_0100000
  | FCVT_RDN_S_Q_32Q  => Some fct7_0100000
  | FCVT_RUP_S_Q_32Q  => Some fct7_0100000
  | FCVT_RMM_S_Q_32Q  => Some fct7_0100000
  | FCVT_DYN_S_Q_32Q  => Some fct7_0100000
  | FCVT_RNE_Q_S_32Q  => Some fct7_0100011
  | FCVT_RTZ_Q_S_32Q  => Some fct7_0100011
  | FCVT_RDN_Q_S_32Q  => Some fct7_0100011
  | FCVT_RUP_Q_S_32Q  => Some fct7_0100011
  | FCVT_RMM_Q_S_32Q  => Some fct7_0100011
  | FCVT_DYN_Q_S_32Q  => Some fct7_0100011
  | FCVT_RNE_D_Q_32Q  => Some fct7_0100001
  | FCVT_RTZ_D_Q_32Q  => Some fct7_0100001
  | FCVT_RDN_D_Q_32Q  => Some fct7_0100001
  | FCVT_RUP_D_Q_32Q  => Some fct7_0100001
  | FCVT_RMM_D_Q_32Q  => Some fct7_0100001
  | FCVT_DYN_D_Q_32Q  => Some fct7_0100001
  | FCVT_RNE_Q_D_32Q  => Some fct7_0100011
  | FCVT_RTZ_Q_D_32Q  => Some fct7_0100011
  | FCVT_RDN_Q_D_32Q  => Some fct7_0100011
  | FCVT_RUP_Q_D_32Q  => Some fct7_0100011
  | FCVT_RMM_Q_D_32Q  => Some fct7_0100011
  | FCVT_DYN_Q_D_32Q  => Some fct7_0100011
  | FEQ_Q_32Q         => Some fct7_1010011
  | FLT_Q_32Q         => Some fct7_1010011
  | FLE_Q_32Q         => Some fct7_1010011
  | FCLASS_Q_32Q      => Some fct7_1110011
  | FCVT_RNE_W_Q_32Q  => Some fct7_1100011
  | FCVT_RTZ_W_Q_32Q  => Some fct7_1100011
  | FCVT_RDN_W_Q_32Q  => Some fct7_1100011
  | FCVT_RUP_W_Q_32Q  => Some fct7_1100011
  | FCVT_RMM_W_Q_32Q  => Some fct7_1100011
  | FCVT_DYN_W_Q_32Q  => Some fct7_1100011
  | FCVT_RNE_WU_Q_32Q => Some fct7_1100011
  | FCVT_RTZ_WU_Q_32Q => Some fct7_1100011
  | FCVT_RDN_WU_Q_32Q => Some fct7_1100011
  | FCVT_RUP_WU_Q_32Q => Some fct7_1100011
  | FCVT_RMM_WU_Q_32Q => Some fct7_1100011
  | FCVT_DYN_WU_Q_32Q => Some fct7_1100011
  | FCVT_RNE_Q_W_32Q  => Some fct7_1101011
  | FCVT_RTZ_Q_W_32Q  => Some fct7_1101011
  | FCVT_RDN_Q_W_32Q  => Some fct7_1101011
  | FCVT_RUP_Q_W_32Q  => Some fct7_1101011
  | FCVT_RMM_Q_W_32Q  => Some fct7_1101011
  | FCVT_DYN_Q_W_32Q  => Some fct7_1101011
  | FCVT_RNE_Q_WU_32Q => Some fct7_1101011
  | FCVT_RTZ_Q_WU_32Q => Some fct7_1101011
  | FCVT_RDN_Q_WU_32Q => Some fct7_1101011
  | FCVT_RUP_Q_WU_32Q => Some fct7_1101011
  | FCVT_RMM_Q_WU_32Q => Some fct7_1101011
  | FCVT_DYN_Q_WU_32Q => Some fct7_1101011
  | FADD_RNE_Q_64Q    => Some fct7_0000011
  | FADD_RTZ_Q_64Q    => Some fct7_0000011
  | FADD_RDN_Q_64Q    => Some fct7_0000011
  | FADD_RUP_Q_64Q    => Some fct7_0000011
  | FADD_RMM_Q_64Q    => Some fct7_0000011
  | FADD_DYN_Q_64Q    => Some fct7_0000011
  | FSUB_RNE_Q_64Q    => Some fct7_0000111
  | FSUB_RTZ_Q_64Q    => Some fct7_0000111
  | FSUB_RDN_Q_64Q    => Some fct7_0000111
  | FSUB_RUP_Q_64Q    => Some fct7_0000111
  | FSUB_RMM_Q_64Q    => Some fct7_0000111
  | FSUB_DYN_Q_64Q    => Some fct7_0000111
  | FMUL_RNE_Q_64Q    => Some fct7_0001011
  | FMUL_RTZ_Q_64Q    => Some fct7_0001011
  | FMUL_RDN_Q_64Q    => Some fct7_0001011
  | FMUL_RUP_Q_64Q    => Some fct7_0001011
  | FMUL_RMM_Q_64Q    => Some fct7_0001011
  | FMUL_DYN_Q_64Q    => Some fct7_0001011
  | FDIV_RNE_Q_64Q    => Some fct7_0001111
  | FDIV_RTZ_Q_64Q    => Some fct7_0001111
  | FDIV_RDN_Q_64Q    => Some fct7_0001111
  | FDIV_RUP_Q_64Q    => Some fct7_0001111
  | FDIV_RMM_Q_64Q    => Some fct7_0001111
  | FDIV_DYN_Q_64Q    => Some fct7_0001111
  | FSQRT_RNE_Q_64Q   => Some fct7_0101111
  | FSQRT_RTZ_Q_64Q   => Some fct7_0101111
  | FSQRT_RDN_Q_64Q   => Some fct7_0101111
  | FSQRT_RUP_Q_64Q   => Some fct7_0101111
  | FSQRT_RMM_Q_64Q   => Some fct7_0101111
  | FSQRT_DYN_Q_64Q   => Some fct7_0101111
  | FSGNJ_Q_64Q       => Some fct7_0010011
  | FSGNJN_Q_64Q      => Some fct7_0010011
  | FSGNJX_Q_64Q      => Some fct7_0010011
  | FMIN_Q_64Q        => Some fct7_0010111
  | FMAX_Q_64Q        => Some fct7_0010111
  | FCVT_RNE_S_Q_64Q  => Some fct7_0100000
  | FCVT_RTZ_S_Q_64Q  => Some fct7_0100000
  | FCVT_RDN_S_Q_64Q  => Some fct7_0100000
  | FCVT_RUP_S_Q_64Q  => Some fct7_0100000
  | FCVT_RMM_S_Q_64Q  => Some fct7_0100000
  | FCVT_DYN_S_Q_64Q  => Some fct7_0100000
  | FCVT_RNE_Q_S_64Q  => Some fct7_0100011
  | FCVT_RTZ_Q_S_64Q  => Some fct7_0100011
  | FCVT_RDN_Q_S_64Q  => Some fct7_0100011
  | FCVT_RUP_Q_S_64Q  => Some fct7_0100011
  | FCVT_RMM_Q_S_64Q  => Some fct7_0100011
  | FCVT_DYN_Q_S_64Q  => Some fct7_0100011
  | FCVT_RNE_D_Q_64Q  => Some fct7_0100001
  | FCVT_RTZ_D_Q_64Q  => Some fct7_0100001
  | FCVT_RDN_D_Q_64Q  => Some fct7_0100001
  | FCVT_RUP_D_Q_64Q  => Some fct7_0100001
  | FCVT_RMM_D_Q_64Q  => Some fct7_0100001
  | FCVT_DYN_D_Q_64Q  => Some fct7_0100001
  | FCVT_RNE_Q_D_64Q  => Some fct7_0100011
  | FCVT_RTZ_Q_D_64Q  => Some fct7_0100011
  | FCVT_RDN_Q_D_64Q  => Some fct7_0100011
  | FCVT_RUP_Q_D_64Q  => Some fct7_0100011
  | FCVT_RMM_Q_D_64Q  => Some fct7_0100011
  | FCVT_DYN_Q_D_64Q  => Some fct7_0100011
  | FEQ_Q_64Q         => Some fct7_1010011
  | FLT_Q_64Q         => Some fct7_1010011
  | FLE_Q_64Q         => Some fct7_1010011
  | FCLASS_Q_64Q      => Some fct7_1110011
  | FCVT_RNE_W_Q_64Q  => Some fct7_1100011
  | FCVT_RTZ_W_Q_64Q  => Some fct7_1100011
  | FCVT_RDN_W_Q_64Q  => Some fct7_1100011
  | FCVT_RUP_W_Q_64Q  => Some fct7_1100011
  | FCVT_RMM_W_Q_64Q  => Some fct7_1100011
  | FCVT_DYN_W_Q_64Q  => Some fct7_1100011
  | FCVT_RNE_WU_Q_64Q => Some fct7_1100011
  | FCVT_RTZ_WU_Q_64Q => Some fct7_1100011
  | FCVT_RDN_WU_Q_64Q => Some fct7_1100011
  | FCVT_RUP_WU_Q_64Q => Some fct7_1100011
  | FCVT_RMM_WU_Q_64Q => Some fct7_1100011
  | FCVT_DYN_WU_Q_64Q => Some fct7_1100011
  | FCVT_RNE_Q_W_64Q  => Some fct7_1101011
  | FCVT_RTZ_Q_W_64Q  => Some fct7_1101011
  | FCVT_RDN_Q_W_64Q  => Some fct7_1101011
  | FCVT_RUP_Q_W_64Q  => Some fct7_1101011
  | FCVT_RMM_Q_W_64Q  => Some fct7_1101011
  | FCVT_DYN_Q_W_64Q  => Some fct7_1101011
  | FCVT_RNE_Q_WU_64Q => Some fct7_1101011
  | FCVT_RTZ_Q_WU_64Q => Some fct7_1101011
  | FCVT_RDN_Q_WU_64Q => Some fct7_1101011
  | FCVT_RUP_Q_WU_64Q => Some fct7_1101011
  | FCVT_RMM_Q_WU_64Q => Some fct7_1101011
  | FCVT_DYN_Q_WU_64Q => Some fct7_1101011
  | FCVT_RNE_L_Q_64Q  => Some fct7_1100011
  | FCVT_RTZ_L_Q_64Q  => Some fct7_1100011
  | FCVT_RDN_L_Q_64Q  => Some fct7_1100011
  | FCVT_RUP_L_Q_64Q  => Some fct7_1100011
  | FCVT_RMM_L_Q_64Q  => Some fct7_1100011
  | FCVT_DYN_L_Q_64Q  => Some fct7_1100011
  | FCVT_RNE_LU_Q_64Q => Some fct7_1100011
  | FCVT_RTZ_LU_Q_64Q => Some fct7_1100011
  | FCVT_RDN_LU_Q_64Q => Some fct7_1100011
  | FCVT_RUP_LU_Q_64Q => Some fct7_1100011
  | FCVT_RMM_LU_Q_64Q => Some fct7_1100011
  | FCVT_DYN_LU_Q_64Q => Some fct7_1100011
  | FCVT_RNE_Q_L_64Q  => Some fct7_1101011
  | FCVT_RTZ_Q_L_64Q  => Some fct7_1101011
  | FCVT_RDN_Q_L_64Q  => Some fct7_1101011
  | FCVT_RUP_Q_L_64Q  => Some fct7_1101011
  | FCVT_RMM_Q_L_64Q  => Some fct7_1101011
  | FCVT_DYN_Q_L_64Q  => Some fct7_1101011
  | FCVT_RNE_Q_LU_64Q => Some fct7_1101011
  | FCVT_RTZ_Q_LU_64Q => Some fct7_1101011
  | FCVT_RDN_Q_LU_64Q => Some fct7_1101011
  | FCVT_RUP_Q_LU_64Q => Some fct7_1101011
  | FCVT_RMM_Q_LU_64Q => Some fct7_1101011
  | FCVT_DYN_Q_LU_64Q => Some fct7_1101011
  | _                 => None
  end.
