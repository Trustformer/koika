(*! Definitions related to the rs2 instruction field !*)
Require Import Koika.Frontend.
Require Import rv.Instructions rv.IFields rv.ITypes rv.InstructionsOpcodes.

Inductive rs2_type := rs2_00 | rs2_01 | rs2_10 | rs2_11.
Scheme Equality for rs2_type. (* TODO check if useful *)
Definition rs2_bin (r : rs2_type) :=
  match r with
  | rs2_00 => Ob~0~0~0~0~0
  | rs2_01 => Ob~0~0~0~0~1
  | rs2_10 => Ob~0~0~0~1~0
  | rs2_11 => Ob~0~0~0~1~1
  end.

Definition has_fixed_rs2 (i : instruction) : bool :=
  match i with
  | LR_W_00_32A       => true | LR_W_01_32A       => true
  | LR_W_10_32A       => true | LR_W_11_32A       => true
  | LR_W_00_64A       => true | LR_W_01_64A       => true
  | LR_W_10_64A       => true | LR_W_11_64A       => true
  | LR_D_00_64A       => true | LR_D_01_64A       => true
  | LR_D_10_64A       => true | LR_D_11_64A       => true
  | FSQRT_RNE_S_32F   => true | FSQRT_RTZ_S_32F   => true
  | FSQRT_RDN_S_32F   => true | FSQRT_RUP_S_32F   => true
  | FSQRT_RMM_S_32F   => true | FSQRT_DYN_S_32F   => true
  | FCVT_RNE_W_S_32F  => true | FCVT_RTZ_W_S_32F  => true
  | FCVT_RDN_W_S_32F  => true | FCVT_RUP_W_S_32F  => true
  | FCVT_RMM_W_S_32F  => true | FCVT_DYN_W_S_32F  => true
  | FCVT_RNE_WU_S_32F => true | FCVT_RTZ_WU_S_32F => true
  | FCVT_RDN_WU_S_32F => true | FCVT_RUP_WU_S_32F => true
  | FCVT_RMM_WU_S_32F => true | FCVT_DYN_WU_S_32F => true
  | FMV_X_W_32F       => true | FCLASS_S_32F      => true
  | FCVT_RNE_S_W_32F  => true | FCVT_RTZ_S_W_32F  => true
  | FCVT_RDN_S_W_32F  => true | FCVT_RUP_S_W_32F  => true
  | FCVT_RMM_S_W_32F  => true | FCVT_DYN_S_W_32F  => true
  | FCVT_RNE_S_WU_32F => true | FCVT_RTZ_S_WU_32F => true
  | FCVT_RDN_S_WU_32F => true | FCVT_RUP_S_WU_32F => true
  | FCVT_RMM_S_WU_32F => true | FCVT_DYN_S_WU_32F => true
  | FMV_W_X_32F       => true | FSQRT_RNE_S_64F   => true
  | FSQRT_RTZ_S_64F   => true | FSQRT_RDN_S_64F   => true
  | FSQRT_RUP_S_64F   => true | FSQRT_RMM_S_64F   => true
  | FSQRT_DYN_S_64F   => true | FCVT_RNE_W_S_64F  => true
  | FCVT_RTZ_W_S_64F  => true | FCVT_RDN_W_S_64F  => true
  | FCVT_RUP_W_S_64F  => true | FCVT_RMM_W_S_64F  => true
  | FCVT_DYN_W_S_64F  => true | FCVT_RNE_WU_S_64F => true
  | FCVT_RTZ_WU_S_64F => true | FCVT_RDN_WU_S_64F => true
  | FCVT_RUP_WU_S_64F => true | FCVT_RMM_WU_S_64F => true
  | FCVT_DYN_WU_S_64F => true | FMV_X_W_64F       => true
  | FCLASS_S_64F      => true | FCVT_RNE_S_W_64F  => true
  | FCVT_RTZ_S_W_64F  => true | FCVT_RDN_S_W_64F  => true
  | FCVT_RUP_S_W_64F  => true | FCVT_RMM_S_W_64F  => true
  | FCVT_DYN_S_W_64F  => true | FCVT_RNE_S_WU_64F => true
  | FCVT_RTZ_S_WU_64F => true | FCVT_RDN_S_WU_64F => true
  | FCVT_RUP_S_WU_64F => true | FCVT_RMM_S_WU_64F => true
  | FCVT_DYN_S_WU_64F => true | FMV_W_X_64F       => true
  | FCVT_RNE_L_S_64F  => true | FCVT_RTZ_L_S_64F  => true
  | FCVT_RDN_L_S_64F  => true | FCVT_RUP_L_S_64F  => true
  | FCVT_RMM_L_S_64F  => true | FCVT_DYN_L_S_64F  => true
  | FCVT_RNE_LU_S_64F => true | FCVT_RTZ_LU_S_64F => true
  | FCVT_RDN_LU_S_64F => true | FCVT_RUP_LU_S_64F => true
  | FCVT_RMM_LU_S_64F => true | FCVT_DYN_LU_S_64F => true
  | FCVT_RNE_S_L_64F  => true | FCVT_RTZ_S_L_64F  => true
  | FCVT_RDN_S_L_64F  => true | FCVT_RUP_S_L_64F  => true
  | FCVT_RMM_S_L_64F  => true | FCVT_DYN_S_L_64F  => true
  | FCVT_RNE_S_LU_64F => true | FCVT_RTZ_S_LU_64F => true
  | FCVT_RDN_S_LU_64F => true | FCVT_RUP_S_LU_64F => true
  | FCVT_RMM_S_LU_64F => true | FCVT_DYN_S_LU_64F => true
  | FSQRT_RNE_D_32D   => true | FSQRT_RTZ_D_32D   => true
  | FSQRT_RDN_D_32D   => true | FSQRT_RUP_D_32D   => true
  | FSQRT_RMM_D_32D   => true | FSQRT_DYN_D_32D   => true
  | FCVT_RNE_S_D_32D  => true | FCVT_RTZ_S_D_32D  => true
  | FCVT_RDN_S_D_32D  => true | FCVT_RUP_S_D_32D  => true
  | FCVT_RMM_S_D_32D  => true | FCVT_DYN_S_D_32D  => true
  | FCVT_RNE_D_S_32D  => true | FCVT_RTZ_D_S_32D  => true
  | FCVT_RDN_D_S_32D  => true | FCVT_RUP_D_S_32D  => true
  | FCVT_RMM_D_S_32D  => true | FCVT_DYN_D_S_32D  => true
  | FCLASS_D_32D      => true | FCVT_RNE_W_D_32D  => true
  | FCVT_RTZ_W_D_32D  => true | FCVT_RDN_W_D_32D  => true
  | FCVT_RUP_W_D_32D  => true | FCVT_RMM_W_D_32D  => true
  | FCVT_DYN_W_D_32D  => true | FCVT_RNE_WU_D_32D => true
  | FCVT_RTZ_WU_D_32D => true | FCVT_RDN_WU_D_32D => true
  | FCVT_RUP_WU_D_32D => true | FCVT_RMM_WU_D_32D => true
  | FCVT_DYN_WU_D_32D => true | FCVT_RNE_D_W_32D  => true
  | FCVT_RTZ_D_W_32D  => true | FCVT_RDN_D_W_32D  => true
  | FCVT_RUP_D_W_32D  => true | FCVT_RMM_D_W_32D  => true
  | FCVT_DYN_D_W_32D  => true | FCVT_RNE_D_WU_32D => true
  | FCVT_RTZ_D_WU_32D => true | FCVT_RDN_D_WU_32D => true
  | FCVT_RUP_D_WU_32D => true | FCVT_RMM_D_WU_32D => true
  | FCVT_DYN_D_WU_32D => true | FSQRT_RNE_D_64D   => true
  | FSQRT_RTZ_D_64D   => true | FSQRT_RDN_D_64D   => true
  | FSQRT_RUP_D_64D   => true | FSQRT_RMM_D_64D   => true
  | FSQRT_DYN_D_64D   => true | FCVT_RNE_S_D_64D  => true
  | FCVT_RTZ_S_D_64D  => true | FCVT_RDN_S_D_64D  => true
  | FCVT_RUP_S_D_64D  => true | FCVT_RMM_S_D_64D  => true
  | FCVT_DYN_S_D_64D  => true | FCVT_RNE_D_S_64D  => true
  | FCVT_RTZ_D_S_64D  => true | FCVT_RDN_D_S_64D  => true
  | FCVT_RUP_D_S_64D  => true | FCVT_RMM_D_S_64D  => true
  | FCVT_DYN_D_S_64D  => true | FCLASS_D_64D      => true
  | FCVT_RNE_W_D_64D  => true | FCVT_RTZ_W_D_64D  => true
  | FCVT_RDN_W_D_64D  => true | FCVT_RUP_W_D_64D  => true
  | FCVT_RMM_W_D_64D  => true | FCVT_DYN_W_D_64D  => true
  | FCVT_RNE_WU_D_64D => true | FCVT_RTZ_WU_D_64D => true
  | FCVT_RDN_WU_D_64D => true | FCVT_RUP_WU_D_64D => true
  | FCVT_RMM_WU_D_64D => true | FCVT_DYN_WU_D_64D => true
  | FCVT_RNE_D_W_64D  => true | FCVT_RTZ_D_W_64D  => true
  | FCVT_RDN_D_W_64D  => true | FCVT_RUP_D_W_64D  => true
  | FCVT_RMM_D_W_64D  => true | FCVT_DYN_D_W_64D  => true
  | FCVT_RNE_D_WU_64D => true | FCVT_RTZ_D_WU_64D => true
  | FCVT_RDN_D_WU_64D => true | FCVT_RUP_D_WU_64D => true
  | FCVT_RMM_D_WU_64D => true | FCVT_DYN_D_WU_64D => true
  | FCVT_RNE_L_D_64D  => true | FCVT_RTZ_L_D_64D  => true
  | FCVT_RDN_L_D_64D  => true | FCVT_RUP_L_D_64D  => true
  | FCVT_RMM_L_D_64D  => true | FCVT_DYN_L_D_64D  => true
  | FCVT_RNE_LU_D_64D => true | FCVT_RTZ_LU_D_64D => true
  | FCVT_RDN_LU_D_64D => true | FCVT_RUP_LU_D_64D => true
  | FCVT_RMM_LU_D_64D => true | FCVT_DYN_LU_D_64D => true
  | FMV_X_D_64D       => true | FCVT_RNE_D_L_64D  => true
  | FCVT_RTZ_D_L_64D  => true | FCVT_RDN_D_L_64D  => true
  | FCVT_RUP_D_L_64D  => true | FCVT_RMM_D_L_64D  => true
  | FCVT_DYN_D_L_64D  => true | FCVT_RNE_D_LU_64D => true
  | FCVT_RTZ_D_LU_64D => true | FCVT_RDN_D_LU_64D => true
  | FCVT_RUP_D_LU_64D => true | FCVT_RMM_D_LU_64D => true
  | FCVT_DYN_D_LU_64D => true | FMV_D_X_64D       => true
  | FSQRT_RNE_Q_32Q   => true | FSQRT_RTZ_Q_32Q   => true
  | FSQRT_RDN_Q_32Q   => true | FSQRT_RUP_Q_32Q   => true
  | FSQRT_RMM_Q_32Q   => true | FSQRT_DYN_Q_32Q   => true
  | FCVT_RNE_S_Q_32Q  => true | FCVT_RTZ_S_Q_32Q  => true
  | FCVT_RDN_S_Q_32Q  => true | FCVT_RUP_S_Q_32Q  => true
  | FCVT_RMM_S_Q_32Q  => true | FCVT_DYN_S_Q_32Q  => true
  | FCVT_RNE_Q_S_32Q  => true | FCVT_RTZ_Q_S_32Q  => true
  | FCVT_RDN_Q_S_32Q  => true | FCVT_RUP_Q_S_32Q  => true
  | FCVT_RMM_Q_S_32Q  => true | FCVT_DYN_Q_S_32Q  => true
  | FCVT_RNE_D_Q_32Q  => true | FCVT_RTZ_D_Q_32Q  => true
  | FCVT_RDN_D_Q_32Q  => true | FCVT_RUP_D_Q_32Q  => true
  | FCVT_RMM_D_Q_32Q  => true | FCVT_DYN_D_Q_32Q  => true
  | FCVT_RNE_Q_D_32Q  => true | FCVT_RTZ_Q_D_32Q  => true
  | FCVT_RDN_Q_D_32Q  => true | FCVT_RUP_Q_D_32Q  => true
  | FCVT_RMM_Q_D_32Q  => true | FCVT_DYN_Q_D_32Q  => true
  | FCLASS_Q_32Q      => true | FCVT_RNE_W_Q_32Q  => true
  | FCVT_RTZ_W_Q_32Q  => true | FCVT_RDN_W_Q_32Q  => true
  | FCVT_RUP_W_Q_32Q  => true | FCVT_RMM_W_Q_32Q  => true
  | FCVT_DYN_W_Q_32Q  => true | FCVT_RNE_WU_Q_32Q => true
  | FCVT_RTZ_WU_Q_32Q => true | FCVT_RDN_WU_Q_32Q => true
  | FCVT_RUP_WU_Q_32Q => true | FCVT_RMM_WU_Q_32Q => true
  | FCVT_DYN_WU_Q_32Q => true | FCVT_RNE_Q_W_32Q  => true
  | FCVT_RTZ_Q_W_32Q  => true | FCVT_RDN_Q_W_32Q  => true
  | FCVT_RUP_Q_W_32Q  => true | FCVT_RMM_Q_W_32Q  => true
  | FCVT_DYN_Q_W_32Q  => true | FCVT_RNE_Q_WU_32Q => true
  | FCVT_RTZ_Q_WU_32Q => true | FCVT_RDN_Q_WU_32Q => true
  | FCVT_RUP_Q_WU_32Q => true | FCVT_RMM_Q_WU_32Q => true
  | FCVT_DYN_Q_WU_32Q => true | FSQRT_RNE_Q_64Q   => true
  | FSQRT_RTZ_Q_64Q   => true | FSQRT_RDN_Q_64Q   => true
  | FSQRT_RUP_Q_64Q   => true | FSQRT_RMM_Q_64Q   => true
  | FSQRT_DYN_Q_64Q   => true | FCVT_RNE_S_Q_64Q  => true
  | FCVT_RTZ_S_Q_64Q  => true | FCVT_RDN_S_Q_64Q  => true
  | FCVT_RUP_S_Q_64Q  => true | FCVT_RMM_S_Q_64Q  => true
  | FCVT_DYN_S_Q_64Q  => true | FCVT_RNE_Q_S_64Q  => true
  | FCVT_RTZ_Q_S_64Q  => true | FCVT_RDN_Q_S_64Q  => true
  | FCVT_RUP_Q_S_64Q  => true | FCVT_RMM_Q_S_64Q  => true
  | FCVT_DYN_Q_S_64Q  => true | FCVT_RNE_D_Q_64Q  => true
  | FCVT_RTZ_D_Q_64Q  => true | FCVT_RDN_D_Q_64Q  => true
  | FCVT_RUP_D_Q_64Q  => true | FCVT_RMM_D_Q_64Q  => true
  | FCVT_DYN_D_Q_64Q  => true | FCVT_RNE_Q_D_64Q  => true
  | FCVT_RTZ_Q_D_64Q  => true | FCVT_RDN_Q_D_64Q  => true
  | FCVT_RUP_Q_D_64Q  => true | FCVT_RMM_Q_D_64Q  => true
  | FCVT_DYN_Q_D_64Q  => true | FCLASS_Q_64Q      => true
  | FCVT_RNE_W_Q_64Q  => true | FCVT_RTZ_W_Q_64Q  => true
  | FCVT_RDN_W_Q_64Q  => true | FCVT_RUP_W_Q_64Q  => true
  | FCVT_RMM_W_Q_64Q  => true | FCVT_DYN_W_Q_64Q  => true
  | FCVT_RNE_WU_Q_64Q => true | FCVT_RTZ_WU_Q_64Q => true
  | FCVT_RDN_WU_Q_64Q => true | FCVT_RUP_WU_Q_64Q => true
  | FCVT_RMM_WU_Q_64Q => true | FCVT_DYN_WU_Q_64Q => true
  | FCVT_RNE_Q_W_64Q  => true | FCVT_RTZ_Q_W_64Q  => true
  | FCVT_RDN_Q_W_64Q  => true | FCVT_RUP_Q_W_64Q  => true
  | FCVT_RMM_Q_W_64Q  => true | FCVT_DYN_Q_W_64Q  => true
  | FCVT_RNE_Q_WU_64Q => true | FCVT_RTZ_Q_WU_64Q => true
  | FCVT_RDN_Q_WU_64Q => true | FCVT_RUP_Q_WU_64Q => true
  | FCVT_RMM_Q_WU_64Q => true | FCVT_DYN_Q_WU_64Q => true
  | FCVT_RNE_L_Q_64Q  => true | FCVT_RTZ_L_Q_64Q  => true
  | FCVT_RDN_L_Q_64Q  => true | FCVT_RUP_L_Q_64Q  => true
  | FCVT_RMM_L_Q_64Q  => true | FCVT_DYN_L_Q_64Q  => true
  | FCVT_RNE_LU_Q_64Q => true | FCVT_RTZ_LU_Q_64Q => true
  | FCVT_RDN_LU_Q_64Q => true | FCVT_RUP_LU_Q_64Q => true
  | FCVT_RMM_LU_Q_64Q => true | FCVT_DYN_LU_Q_64Q => true
  | FCVT_RNE_Q_L_64Q  => true | FCVT_RTZ_Q_L_64Q  => true
  | FCVT_RDN_Q_L_64Q  => true | FCVT_RUP_Q_L_64Q  => true
  | FCVT_RMM_Q_L_64Q  => true | FCVT_DYN_Q_L_64Q  => true
  | FCVT_RNE_Q_LU_64Q => true | FCVT_RTZ_Q_LU_64Q => true
  | FCVT_RDN_Q_LU_64Q => true | FCVT_RUP_Q_LU_64Q => true
  | FCVT_RMM_Q_LU_64Q => true | FCVT_DYN_Q_LU_64Q => true
  | _ => false
end.

Definition instruction_fixed_rs2 :
  forall (i : instruction), has_fixed_rs2 i = true -> rs2_type.
Proof.
  refine (fun i =>
    match i with
    | LR_W_00_32A       => fun _ => rs2_00
    | LR_W_01_32A       => fun _ => rs2_00
    | LR_W_10_32A       => fun _ => rs2_00
    | LR_W_11_32A       => fun _ => rs2_00
    | LR_W_00_64A       => fun _ => rs2_00
    | LR_W_01_64A       => fun _ => rs2_00
    | LR_W_10_64A       => fun _ => rs2_00
    | LR_W_11_64A       => fun _ => rs2_00
    | LR_D_00_64A       => fun _ => rs2_00
    | LR_D_01_64A       => fun _ => rs2_00
    | LR_D_10_64A       => fun _ => rs2_00
    | LR_D_11_64A       => fun _ => rs2_00
    | FSQRT_RNE_S_32F   => fun _ => rs2_00
    | FSQRT_RTZ_S_32F   => fun _ => rs2_00
    | FSQRT_RDN_S_32F   => fun _ => rs2_00
    | FSQRT_RUP_S_32F   => fun _ => rs2_00
    | FSQRT_RMM_S_32F   => fun _ => rs2_00
    | FSQRT_DYN_S_32F   => fun _ => rs2_00
    | FCVT_RNE_W_S_32F  => fun _ => rs2_00
    | FCVT_RTZ_W_S_32F  => fun _ => rs2_00
    | FCVT_RDN_W_S_32F  => fun _ => rs2_00
    | FCVT_RUP_W_S_32F  => fun _ => rs2_00
    | FCVT_RMM_W_S_32F  => fun _ => rs2_00
    | FCVT_DYN_W_S_32F  => fun _ => rs2_00
    | FCVT_RNE_WU_S_32F => fun _ => rs2_01
    | FCVT_RTZ_WU_S_32F => fun _ => rs2_01
    | FCVT_RDN_WU_S_32F => fun _ => rs2_01
    | FCVT_RUP_WU_S_32F => fun _ => rs2_01
    | FCVT_RMM_WU_S_32F => fun _ => rs2_01
    | FCVT_DYN_WU_S_32F => fun _ => rs2_01
    | FMV_X_W_32F       => fun _ => rs2_00
    | FCLASS_S_32F      => fun _ => rs2_00
    | FCVT_RNE_S_W_32F  => fun _ => rs2_00
    | FCVT_RTZ_S_W_32F  => fun _ => rs2_00
    | FCVT_RDN_S_W_32F  => fun _ => rs2_00
    | FCVT_RUP_S_W_32F  => fun _ => rs2_00
    | FCVT_RMM_S_W_32F  => fun _ => rs2_00
    | FCVT_DYN_S_W_32F  => fun _ => rs2_00
    | FCVT_RNE_S_WU_32F => fun _ => rs2_01
    | FCVT_RTZ_S_WU_32F => fun _ => rs2_01
    | FCVT_RDN_S_WU_32F => fun _ => rs2_01
    | FCVT_RUP_S_WU_32F => fun _ => rs2_01
    | FCVT_RMM_S_WU_32F => fun _ => rs2_01
    | FCVT_DYN_S_WU_32F => fun _ => rs2_01
    | FMV_W_X_32F       => fun _ => rs2_00
    | FSQRT_RNE_S_64F   => fun _ => rs2_00
    | FSQRT_RTZ_S_64F   => fun _ => rs2_00
    | FSQRT_RDN_S_64F   => fun _ => rs2_00
    | FSQRT_RUP_S_64F   => fun _ => rs2_00
    | FSQRT_RMM_S_64F   => fun _ => rs2_00
    | FSQRT_DYN_S_64F   => fun _ => rs2_00
    | FCVT_RNE_W_S_64F  => fun _ => rs2_00
    | FCVT_RTZ_W_S_64F  => fun _ => rs2_00
    | FCVT_RDN_W_S_64F  => fun _ => rs2_00
    | FCVT_RUP_W_S_64F  => fun _ => rs2_00
    | FCVT_RMM_W_S_64F  => fun _ => rs2_00
    | FCVT_DYN_W_S_64F  => fun _ => rs2_00
    | FCVT_RNE_WU_S_64F => fun _ => rs2_01
    | FCVT_RTZ_WU_S_64F => fun _ => rs2_01
    | FCVT_RDN_WU_S_64F => fun _ => rs2_01
    | FCVT_RUP_WU_S_64F => fun _ => rs2_01
    | FCVT_RMM_WU_S_64F => fun _ => rs2_01
    | FCVT_DYN_WU_S_64F => fun _ => rs2_01
    | FMV_X_W_64F       => fun _ => rs2_00
    | FCLASS_S_64F      => fun _ => rs2_00
    | FCVT_RNE_S_W_64F  => fun _ => rs2_00
    | FCVT_RTZ_S_W_64F  => fun _ => rs2_00
    | FCVT_RDN_S_W_64F  => fun _ => rs2_00
    | FCVT_RUP_S_W_64F  => fun _ => rs2_00
    | FCVT_RMM_S_W_64F  => fun _ => rs2_00
    | FCVT_DYN_S_W_64F  => fun _ => rs2_00
    | FCVT_RNE_S_WU_64F => fun _ => rs2_01
    | FCVT_RTZ_S_WU_64F => fun _ => rs2_01
    | FCVT_RDN_S_WU_64F => fun _ => rs2_01
    | FCVT_RUP_S_WU_64F => fun _ => rs2_01
    | FCVT_RMM_S_WU_64F => fun _ => rs2_01
    | FCVT_DYN_S_WU_64F => fun _ => rs2_01
    | FMV_W_X_64F       => fun _ => rs2_00
    | FCVT_RNE_L_S_64F  => fun _ => rs2_10
    | FCVT_RTZ_L_S_64F  => fun _ => rs2_10
    | FCVT_RDN_L_S_64F  => fun _ => rs2_10
    | FCVT_RUP_L_S_64F  => fun _ => rs2_10
    | FCVT_RMM_L_S_64F  => fun _ => rs2_10
    | FCVT_DYN_L_S_64F  => fun _ => rs2_10
    | FCVT_RNE_LU_S_64F => fun _ => rs2_11
    | FCVT_RTZ_LU_S_64F => fun _ => rs2_11
    | FCVT_RDN_LU_S_64F => fun _ => rs2_11
    | FCVT_RUP_LU_S_64F => fun _ => rs2_11
    | FCVT_RMM_LU_S_64F => fun _ => rs2_11
    | FCVT_DYN_LU_S_64F => fun _ => rs2_11
    | FCVT_RNE_S_L_64F  => fun _ => rs2_10
    | FCVT_RTZ_S_L_64F  => fun _ => rs2_10
    | FCVT_RDN_S_L_64F  => fun _ => rs2_10
    | FCVT_RUP_S_L_64F  => fun _ => rs2_10
    | FCVT_RMM_S_L_64F  => fun _ => rs2_10
    | FCVT_DYN_S_L_64F  => fun _ => rs2_10
    | FCVT_RNE_S_LU_64F => fun _ => rs2_11
    | FCVT_RTZ_S_LU_64F => fun _ => rs2_11
    | FCVT_RDN_S_LU_64F => fun _ => rs2_11
    | FCVT_RUP_S_LU_64F => fun _ => rs2_11
    | FCVT_RMM_S_LU_64F => fun _ => rs2_11
    | FCVT_DYN_S_LU_64F => fun _ => rs2_11
    | FSQRT_RNE_D_32D   => fun _ => rs2_00
    | FSQRT_RTZ_D_32D   => fun _ => rs2_00
    | FSQRT_RDN_D_32D   => fun _ => rs2_00
    | FSQRT_RUP_D_32D   => fun _ => rs2_00
    | FSQRT_RMM_D_32D   => fun _ => rs2_00
    | FSQRT_DYN_D_32D   => fun _ => rs2_00
    | FCVT_RNE_S_D_32D  => fun _ => rs2_01
    | FCVT_RTZ_S_D_32D  => fun _ => rs2_01
    | FCVT_RDN_S_D_32D  => fun _ => rs2_01
    | FCVT_RUP_S_D_32D  => fun _ => rs2_01
    | FCVT_RMM_S_D_32D  => fun _ => rs2_01
    | FCVT_DYN_S_D_32D  => fun _ => rs2_01
    | FCVT_RNE_D_S_32D  => fun _ => rs2_00
    | FCVT_RTZ_D_S_32D  => fun _ => rs2_00
    | FCVT_RDN_D_S_32D  => fun _ => rs2_00
    | FCVT_RUP_D_S_32D  => fun _ => rs2_00
    | FCVT_RMM_D_S_32D  => fun _ => rs2_00
    | FCVT_DYN_D_S_32D  => fun _ => rs2_00
    | FCLASS_D_32D      => fun _ => rs2_00
    | FCVT_RNE_W_D_32D  => fun _ => rs2_00
    | FCVT_RTZ_W_D_32D  => fun _ => rs2_00
    | FCVT_RDN_W_D_32D  => fun _ => rs2_00
    | FCVT_RUP_W_D_32D  => fun _ => rs2_00
    | FCVT_RMM_W_D_32D  => fun _ => rs2_00
    | FCVT_DYN_W_D_32D  => fun _ => rs2_00
    | FCVT_RNE_WU_D_32D => fun _ => rs2_01
    | FCVT_RTZ_WU_D_32D => fun _ => rs2_01
    | FCVT_RDN_WU_D_32D => fun _ => rs2_01
    | FCVT_RUP_WU_D_32D => fun _ => rs2_01
    | FCVT_RMM_WU_D_32D => fun _ => rs2_01
    | FCVT_DYN_WU_D_32D => fun _ => rs2_01
    | FCVT_RNE_D_W_32D  => fun _ => rs2_00
    | FCVT_RTZ_D_W_32D  => fun _ => rs2_00
    | FCVT_RDN_D_W_32D  => fun _ => rs2_00
    | FCVT_RUP_D_W_32D  => fun _ => rs2_00
    | FCVT_RMM_D_W_32D  => fun _ => rs2_00
    | FCVT_DYN_D_W_32D  => fun _ => rs2_00
    | FCVT_RNE_D_WU_32D => fun _ => rs2_01
    | FCVT_RTZ_D_WU_32D => fun _ => rs2_01
    | FCVT_RDN_D_WU_32D => fun _ => rs2_01
    | FCVT_RUP_D_WU_32D => fun _ => rs2_01
    | FCVT_RMM_D_WU_32D => fun _ => rs2_01
    | FCVT_DYN_D_WU_32D => fun _ => rs2_01
    | FSQRT_RNE_D_64D   => fun _ => rs2_00
    | FSQRT_RTZ_D_64D   => fun _ => rs2_00
    | FSQRT_RDN_D_64D   => fun _ => rs2_00
    | FSQRT_RUP_D_64D   => fun _ => rs2_00
    | FSQRT_RMM_D_64D   => fun _ => rs2_00
    | FSQRT_DYN_D_64D   => fun _ => rs2_00
    | FCVT_RNE_S_D_64D  => fun _ => rs2_01
    | FCVT_RTZ_S_D_64D  => fun _ => rs2_01
    | FCVT_RDN_S_D_64D  => fun _ => rs2_01
    | FCVT_RUP_S_D_64D  => fun _ => rs2_01
    | FCVT_RMM_S_D_64D  => fun _ => rs2_01
    | FCVT_DYN_S_D_64D  => fun _ => rs2_01
    | FCVT_RNE_D_S_64D  => fun _ => rs2_00
    | FCVT_RTZ_D_S_64D  => fun _ => rs2_00
    | FCVT_RDN_D_S_64D  => fun _ => rs2_00
    | FCVT_RUP_D_S_64D  => fun _ => rs2_00
    | FCVT_RMM_D_S_64D  => fun _ => rs2_00
    | FCVT_DYN_D_S_64D  => fun _ => rs2_00
    | FCLASS_D_64D      => fun _ => rs2_00
    | FCVT_RNE_W_D_64D  => fun _ => rs2_00
    | FCVT_RTZ_W_D_64D  => fun _ => rs2_00
    | FCVT_RDN_W_D_64D  => fun _ => rs2_00
    | FCVT_RUP_W_D_64D  => fun _ => rs2_00
    | FCVT_RMM_W_D_64D  => fun _ => rs2_00
    | FCVT_DYN_W_D_64D  => fun _ => rs2_00
    | FCVT_RNE_WU_D_64D => fun _ => rs2_01
    | FCVT_RTZ_WU_D_64D => fun _ => rs2_01
    | FCVT_RDN_WU_D_64D => fun _ => rs2_01
    | FCVT_RUP_WU_D_64D => fun _ => rs2_01
    | FCVT_RMM_WU_D_64D => fun _ => rs2_01
    | FCVT_DYN_WU_D_64D => fun _ => rs2_01
    | FCVT_RNE_D_W_64D  => fun _ => rs2_00
    | FCVT_RTZ_D_W_64D  => fun _ => rs2_00
    | FCVT_RDN_D_W_64D  => fun _ => rs2_00
    | FCVT_RUP_D_W_64D  => fun _ => rs2_00
    | FCVT_RMM_D_W_64D  => fun _ => rs2_00
    | FCVT_DYN_D_W_64D  => fun _ => rs2_00
    | FCVT_RNE_D_WU_64D => fun _ => rs2_01
    | FCVT_RTZ_D_WU_64D => fun _ => rs2_01
    | FCVT_RDN_D_WU_64D => fun _ => rs2_01
    | FCVT_RUP_D_WU_64D => fun _ => rs2_01
    | FCVT_RMM_D_WU_64D => fun _ => rs2_01
    | FCVT_DYN_D_WU_64D => fun _ => rs2_01
    | FCVT_RNE_L_D_64D  => fun _ => rs2_10
    | FCVT_RTZ_L_D_64D  => fun _ => rs2_10
    | FCVT_RDN_L_D_64D  => fun _ => rs2_10
    | FCVT_RUP_L_D_64D  => fun _ => rs2_10
    | FCVT_RMM_L_D_64D  => fun _ => rs2_10
    | FCVT_DYN_L_D_64D  => fun _ => rs2_10
    | FCVT_RNE_LU_D_64D => fun _ => rs2_11
    | FCVT_RTZ_LU_D_64D => fun _ => rs2_11
    | FCVT_RDN_LU_D_64D => fun _ => rs2_11
    | FCVT_RUP_LU_D_64D => fun _ => rs2_11
    | FCVT_RMM_LU_D_64D => fun _ => rs2_11
    | FCVT_DYN_LU_D_64D => fun _ => rs2_11
    | FMV_X_D_64D       => fun _ => rs2_00
    | FCVT_RNE_D_L_64D  => fun _ => rs2_10
    | FCVT_RTZ_D_L_64D  => fun _ => rs2_10
    | FCVT_RDN_D_L_64D  => fun _ => rs2_10
    | FCVT_RUP_D_L_64D  => fun _ => rs2_10
    | FCVT_RMM_D_L_64D  => fun _ => rs2_10
    | FCVT_DYN_D_L_64D  => fun _ => rs2_10
    | FCVT_RNE_D_LU_64D => fun _ => rs2_11
    | FCVT_RTZ_D_LU_64D => fun _ => rs2_11
    | FCVT_RDN_D_LU_64D => fun _ => rs2_11
    | FCVT_RUP_D_LU_64D => fun _ => rs2_11
    | FCVT_RMM_D_LU_64D => fun _ => rs2_11
    | FCVT_DYN_D_LU_64D => fun _ => rs2_11
    | FMV_D_X_64D       => fun _ => rs2_00
    | FSQRT_RNE_Q_32Q   => fun _ => rs2_00
    | FSQRT_RTZ_Q_32Q   => fun _ => rs2_00
    | FSQRT_RDN_Q_32Q   => fun _ => rs2_00
    | FSQRT_RUP_Q_32Q   => fun _ => rs2_00
    | FSQRT_RMM_Q_32Q   => fun _ => rs2_00
    | FSQRT_DYN_Q_32Q   => fun _ => rs2_00
    | FCVT_RNE_S_Q_32Q  => fun _ => rs2_11
    | FCVT_RTZ_S_Q_32Q  => fun _ => rs2_11
    | FCVT_RDN_S_Q_32Q  => fun _ => rs2_11
    | FCVT_RUP_S_Q_32Q  => fun _ => rs2_11
    | FCVT_RMM_S_Q_32Q  => fun _ => rs2_11
    | FCVT_DYN_S_Q_32Q  => fun _ => rs2_11
    | FCVT_RNE_Q_S_32Q  => fun _ => rs2_00
    | FCVT_RTZ_Q_S_32Q  => fun _ => rs2_00
    | FCVT_RDN_Q_S_32Q  => fun _ => rs2_00
    | FCVT_RUP_Q_S_32Q  => fun _ => rs2_00
    | FCVT_RMM_Q_S_32Q  => fun _ => rs2_00
    | FCVT_DYN_Q_S_32Q  => fun _ => rs2_00
    | FCVT_RNE_D_Q_32Q  => fun _ => rs2_11
    | FCVT_RTZ_D_Q_32Q  => fun _ => rs2_11
    | FCVT_RDN_D_Q_32Q  => fun _ => rs2_11
    | FCVT_RUP_D_Q_32Q  => fun _ => rs2_11
    | FCVT_RMM_D_Q_32Q  => fun _ => rs2_11
    | FCVT_DYN_D_Q_32Q  => fun _ => rs2_11
    | FCVT_RNE_Q_D_32Q  => fun _ => rs2_01
    | FCVT_RTZ_Q_D_32Q  => fun _ => rs2_01
    | FCVT_RDN_Q_D_32Q  => fun _ => rs2_01
    | FCVT_RUP_Q_D_32Q  => fun _ => rs2_01
    | FCVT_RMM_Q_D_32Q  => fun _ => rs2_01
    | FCVT_DYN_Q_D_32Q  => fun _ => rs2_01
    | FCLASS_Q_32Q      => fun _ => rs2_00
    | FCVT_RNE_W_Q_32Q  => fun _ => rs2_00
    | FCVT_RTZ_W_Q_32Q  => fun _ => rs2_00
    | FCVT_RDN_W_Q_32Q  => fun _ => rs2_00
    | FCVT_RUP_W_Q_32Q  => fun _ => rs2_00
    | FCVT_RMM_W_Q_32Q  => fun _ => rs2_00
    | FCVT_DYN_W_Q_32Q  => fun _ => rs2_00
    | FCVT_RNE_WU_Q_32Q => fun _ => rs2_01
    | FCVT_RTZ_WU_Q_32Q => fun _ => rs2_01
    | FCVT_RDN_WU_Q_32Q => fun _ => rs2_01
    | FCVT_RUP_WU_Q_32Q => fun _ => rs2_01
    | FCVT_RMM_WU_Q_32Q => fun _ => rs2_01
    | FCVT_DYN_WU_Q_32Q => fun _ => rs2_01
    | FCVT_RNE_Q_W_32Q  => fun _ => rs2_00
    | FCVT_RTZ_Q_W_32Q  => fun _ => rs2_00
    | FCVT_RDN_Q_W_32Q  => fun _ => rs2_00
    | FCVT_RUP_Q_W_32Q  => fun _ => rs2_00
    | FCVT_RMM_Q_W_32Q  => fun _ => rs2_00
    | FCVT_DYN_Q_W_32Q  => fun _ => rs2_00
    | FCVT_RNE_Q_WU_32Q => fun _ => rs2_01
    | FCVT_RTZ_Q_WU_32Q => fun _ => rs2_01
    | FCVT_RDN_Q_WU_32Q => fun _ => rs2_01
    | FCVT_RUP_Q_WU_32Q => fun _ => rs2_01
    | FCVT_RMM_Q_WU_32Q => fun _ => rs2_01
    | FCVT_DYN_Q_WU_32Q => fun _ => rs2_01
    | FSQRT_RNE_Q_64Q   => fun _ => rs2_00
    | FSQRT_RTZ_Q_64Q   => fun _ => rs2_00
    | FSQRT_RDN_Q_64Q   => fun _ => rs2_00
    | FSQRT_RUP_Q_64Q   => fun _ => rs2_00
    | FSQRT_RMM_Q_64Q   => fun _ => rs2_00
    | FSQRT_DYN_Q_64Q   => fun _ => rs2_00
    | FCVT_RNE_S_Q_64Q  => fun _ => rs2_11
    | FCVT_RTZ_S_Q_64Q  => fun _ => rs2_11
    | FCVT_RDN_S_Q_64Q  => fun _ => rs2_11
    | FCVT_RUP_S_Q_64Q  => fun _ => rs2_11
    | FCVT_RMM_S_Q_64Q  => fun _ => rs2_11
    | FCVT_DYN_S_Q_64Q  => fun _ => rs2_11
    | FCVT_RNE_Q_S_64Q  => fun _ => rs2_00
    | FCVT_RTZ_Q_S_64Q  => fun _ => rs2_00
    | FCVT_RDN_Q_S_64Q  => fun _ => rs2_00
    | FCVT_RUP_Q_S_64Q  => fun _ => rs2_00
    | FCVT_RMM_Q_S_64Q  => fun _ => rs2_00
    | FCVT_DYN_Q_S_64Q  => fun _ => rs2_00
    | FCVT_RNE_D_Q_64Q  => fun _ => rs2_11
    | FCVT_RTZ_D_Q_64Q  => fun _ => rs2_11
    | FCVT_RDN_D_Q_64Q  => fun _ => rs2_11
    | FCVT_RUP_D_Q_64Q  => fun _ => rs2_11
    | FCVT_RMM_D_Q_64Q  => fun _ => rs2_11
    | FCVT_DYN_D_Q_64Q  => fun _ => rs2_11
    | FCVT_RNE_Q_D_64Q  => fun _ => rs2_01
    | FCVT_RTZ_Q_D_64Q  => fun _ => rs2_01
    | FCVT_RDN_Q_D_64Q  => fun _ => rs2_01
    | FCVT_RUP_Q_D_64Q  => fun _ => rs2_01
    | FCVT_RMM_Q_D_64Q  => fun _ => rs2_01
    | FCVT_DYN_Q_D_64Q  => fun _ => rs2_01
    | FCLASS_Q_64Q      => fun _ => rs2_00
    | FCVT_RNE_W_Q_64Q  => fun _ => rs2_00
    | FCVT_RTZ_W_Q_64Q  => fun _ => rs2_00
    | FCVT_RDN_W_Q_64Q  => fun _ => rs2_00
    | FCVT_RUP_W_Q_64Q  => fun _ => rs2_00
    | FCVT_RMM_W_Q_64Q  => fun _ => rs2_00
    | FCVT_DYN_W_Q_64Q  => fun _ => rs2_00
    | FCVT_RNE_WU_Q_64Q => fun _ => rs2_01
    | FCVT_RTZ_WU_Q_64Q => fun _ => rs2_01
    | FCVT_RDN_WU_Q_64Q => fun _ => rs2_01
    | FCVT_RUP_WU_Q_64Q => fun _ => rs2_01
    | FCVT_RMM_WU_Q_64Q => fun _ => rs2_01
    | FCVT_DYN_WU_Q_64Q => fun _ => rs2_01
    | FCVT_RNE_Q_W_64Q  => fun _ => rs2_00
    | FCVT_RTZ_Q_W_64Q  => fun _ => rs2_00
    | FCVT_RDN_Q_W_64Q  => fun _ => rs2_00
    | FCVT_RUP_Q_W_64Q  => fun _ => rs2_00
    | FCVT_RMM_Q_W_64Q  => fun _ => rs2_00
    | FCVT_DYN_Q_W_64Q  => fun _ => rs2_00
    | FCVT_RNE_Q_WU_64Q => fun _ => rs2_01
    | FCVT_RTZ_Q_WU_64Q => fun _ => rs2_01
    | FCVT_RDN_Q_WU_64Q => fun _ => rs2_01
    | FCVT_RUP_Q_WU_64Q => fun _ => rs2_01
    | FCVT_RMM_Q_WU_64Q => fun _ => rs2_01
    | FCVT_DYN_Q_WU_64Q => fun _ => rs2_01
    | FCVT_RNE_L_Q_64Q  => fun _ => rs2_10
    | FCVT_RTZ_L_Q_64Q  => fun _ => rs2_10
    | FCVT_RDN_L_Q_64Q  => fun _ => rs2_10
    | FCVT_RUP_L_Q_64Q  => fun _ => rs2_10
    | FCVT_RMM_L_Q_64Q  => fun _ => rs2_10
    | FCVT_DYN_L_Q_64Q  => fun _ => rs2_10
    | FCVT_RNE_LU_Q_64Q => fun _ => rs2_11
    | FCVT_RTZ_LU_Q_64Q => fun _ => rs2_11
    | FCVT_RDN_LU_Q_64Q => fun _ => rs2_11
    | FCVT_RUP_LU_Q_64Q => fun _ => rs2_11
    | FCVT_RMM_LU_Q_64Q => fun _ => rs2_11
    | FCVT_DYN_LU_Q_64Q => fun _ => rs2_11
    | FCVT_RNE_Q_L_64Q  => fun _ => rs2_10
    | FCVT_RTZ_Q_L_64Q  => fun _ => rs2_10
    | FCVT_RDN_Q_L_64Q  => fun _ => rs2_10
    | FCVT_RUP_Q_L_64Q  => fun _ => rs2_10
    | FCVT_RMM_Q_L_64Q  => fun _ => rs2_10
    | FCVT_DYN_Q_L_64Q  => fun _ => rs2_10
    | FCVT_RNE_Q_LU_64Q => fun _ => rs2_11
    | FCVT_RTZ_Q_LU_64Q => fun _ => rs2_11
    | FCVT_RDN_Q_LU_64Q => fun _ => rs2_11
    | FCVT_RUP_Q_LU_64Q => fun _ => rs2_11
    | FCVT_RMM_Q_LU_64Q => fun _ => rs2_11
    | FCVT_DYN_Q_LU_64Q => fun _ => rs2_11
    | _                 => fun _ => False_rec _ _
  end); try reflexivity; simpl in e; inversion e.
Defined.
