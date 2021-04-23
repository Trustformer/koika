(*! Definitions related to the fct2 instruction field !*)

Require Import Koika.Frontend.
Require Import rv.Instructions rv.IFields rv.ITypes rv.InstructionsOpcodes.

Inductive fct2_type := fct2_00 | fct2_01 | fct2_11.

Definition fct2_bin (f : fct2_type) :=
  match f with
  | fct2_00 => Ob~0~0 | fct2_01 => Ob~0~1 | fct2_11 => Ob~1~1
  end.
Scheme Equality for fct2_type.

Definition instruction_fct2 :
  forall (i : instruction), has_fct2 (get_instruction_i_type i) = true
  -> fct2_type.
Proof.
refine (fun i =>
  match i with
  | FMADD_RNE_S_32F    => fun _ => fct2_00
  | FMADD_RTZ_S_32F    => fun _ => fct2_00
  | FMADD_RDN_S_32F    => fun _ => fct2_00
  | FMADD_RUP_S_32F    => fun _ => fct2_00
  | FMADD_RMM_S_32F    => fun _ => fct2_00
  | FMADD_DYN_S_32F    => fun _ => fct2_00
  | FMSUB_RNE_S_32F    => fun _ => fct2_00
  | FMSUB_RTZ_S_32F    => fun _ => fct2_00
  | FMSUB_RDN_S_32F    => fun _ => fct2_00
  | FMSUB_RUP_S_32F    => fun _ => fct2_00
  | FMSUB_RMM_S_32F    => fun _ => fct2_00
  | FMSUB_DYN_S_32F    => fun _ => fct2_00
  | FNMSUB_RNE_S_32F   => fun _ => fct2_00
  | FNMSUB_RTZ_S_32F   => fun _ => fct2_00
  | FNMSUB_RDN_S_32F   => fun _ => fct2_00
  | FNMSUB_RUP_S_32F   => fun _ => fct2_00
  | FNMSUB_RMM_S_32F   => fun _ => fct2_00
  | FNMSUB_DYN_S_32F   => fun _ => fct2_00
  | FNMADD_RNE_S_32F   => fun _ => fct2_00
  | FNMADD_RTZ_S_32F   => fun _ => fct2_00
  | FNMADD_RDN_S_32F   => fun _ => fct2_00
  | FNMADD_RUP_S_32F   => fun _ => fct2_00
  | FNMADD_RMM_S_32F   => fun _ => fct2_00
  | FNMADD_DYN_S_32F   => fun _ => fct2_00
  | FMADD_RNE_S_64F    => fun _ => fct2_00
  | FMADD_RTZ_S_64F    => fun _ => fct2_00
  | FMADD_RDN_S_64F    => fun _ => fct2_00
  | FMADD_RUP_S_64F    => fun _ => fct2_00
  | FMADD_RMM_S_64F    => fun _ => fct2_00
  | FMADD_DYN_S_64F    => fun _ => fct2_00
  | FMSUB_RNE_S_64F    => fun _ => fct2_00
  | FMSUB_RTZ_S_64F    => fun _ => fct2_00
  | FMSUB_RDN_S_64F    => fun _ => fct2_00
  | FMSUB_RUP_S_64F    => fun _ => fct2_00
  | FMSUB_RMM_S_64F    => fun _ => fct2_00
  | FMSUB_DYN_S_64F    => fun _ => fct2_00
  | FNMSUB_RNE_S_64F   => fun _ => fct2_00
  | FNMSUB_RTZ_S_64F   => fun _ => fct2_00
  | FNMSUB_RDN_S_64F   => fun _ => fct2_00
  | FNMSUB_RUP_S_64F   => fun _ => fct2_00
  | FNMSUB_RMM_S_64F   => fun _ => fct2_00
  | FNMSUB_DYN_S_64F   => fun _ => fct2_00
  | FNMADD_RNE_S_64F   => fun _ => fct2_00
  | FNMADD_RTZ_S_64F   => fun _ => fct2_00
  | FNMADD_RDN_S_64F   => fun _ => fct2_00
  | FNMADD_RUP_S_64F   => fun _ => fct2_00
  | FNMADD_RMM_S_64F   => fun _ => fct2_00
  | FNMADD_DYN_S_64F   => fun _ => fct2_00
  | FMADD_RNE_D_32D    => fun _ => fct2_01
  | FMADD_RTZ_D_32D    => fun _ => fct2_01
  | FMADD_RDN_D_32D    => fun _ => fct2_01
  | FMADD_RUP_D_32D    => fun _ => fct2_01
  | FMADD_RMM_D_32D    => fun _ => fct2_01
  | FMADD_DYN_D_32D    => fun _ => fct2_01
  | FMSUB_RNE_D_32D    => fun _ => fct2_01
  | FMSUB_RTZ_D_32D    => fun _ => fct2_01
  | FMSUB_RDN_D_32D    => fun _ => fct2_01
  | FMSUB_RUP_D_32D    => fun _ => fct2_01
  | FMSUB_RMM_D_32D    => fun _ => fct2_01
  | FMSUB_DYN_D_32D    => fun _ => fct2_01
  | FNMSUB_RNE_D_32D   => fun _ => fct2_01
  | FNMSUB_RTZ_D_32D   => fun _ => fct2_01
  | FNMSUB_RDN_D_32D   => fun _ => fct2_01
  | FNMSUB_RUP_D_32D   => fun _ => fct2_01
  | FNMSUB_RMM_D_32D   => fun _ => fct2_01
  | FNMSUB_DYN_D_32D   => fun _ => fct2_01
  | FNMADD_RNE_D_32D   => fun _ => fct2_01
  | FNMADD_RTZ_D_32D   => fun _ => fct2_01
  | FNMADD_RDN_D_32D   => fun _ => fct2_01
  | FNMADD_RUP_D_32D   => fun _ => fct2_01
  | FNMADD_RMM_D_32D   => fun _ => fct2_01
  | FNMADD_DYN_D_32D   => fun _ => fct2_01
  | FMADD_RNE_D_64D    => fun _ => fct2_01
  | FMADD_RTZ_D_64D    => fun _ => fct2_01
  | FMADD_RDN_D_64D    => fun _ => fct2_01
  | FMADD_RUP_D_64D    => fun _ => fct2_01
  | FMADD_RMM_D_64D    => fun _ => fct2_01
  | FMADD_DYN_D_64D    => fun _ => fct2_01
  | FMSUB_RNE_D_64D    => fun _ => fct2_01
  | FMSUB_RTZ_D_64D    => fun _ => fct2_01
  | FMSUB_RDN_D_64D    => fun _ => fct2_01
  | FMSUB_RUP_D_64D    => fun _ => fct2_01
  | FMSUB_RMM_D_64D    => fun _ => fct2_01
  | FMSUB_DYN_D_64D    => fun _ => fct2_01
  | FNMSUB_RNE_D_64D   => fun _ => fct2_01
  | FNMSUB_RTZ_D_64D   => fun _ => fct2_01
  | FNMSUB_RDN_D_64D   => fun _ => fct2_01
  | FNMSUB_RUP_D_64D   => fun _ => fct2_01
  | FNMSUB_RMM_D_64D   => fun _ => fct2_01
  | FNMSUB_DYN_D_64D   => fun _ => fct2_01
  | FNMADD_RNE_D_64D   => fun _ => fct2_01
  | FNMADD_RTZ_D_64D   => fun _ => fct2_01
  | FNMADD_RDN_D_64D   => fun _ => fct2_01
  | FNMADD_RUP_D_64D   => fun _ => fct2_01
  | FNMADD_RMM_D_64D   => fun _ => fct2_01
  | FNMADD_DYN_D_64D   => fun _ => fct2_01
  | FMADD_RNE_Q_32Q    => fun _ => fct2_11
  | FMADD_RTZ_Q_32Q    => fun _ => fct2_11
  | FMADD_RDN_Q_32Q    => fun _ => fct2_11
  | FMADD_RUP_Q_32Q    => fun _ => fct2_11
  | FMADD_RMM_Q_32Q    => fun _ => fct2_11
  | FMADD_DYN_Q_32Q    => fun _ => fct2_11
  | FMSUB_RNE_Q_32Q    => fun _ => fct2_11
  | FMSUB_RTZ_Q_32Q    => fun _ => fct2_11
  | FMSUB_RDN_Q_32Q    => fun _ => fct2_11
  | FMSUB_RUP_Q_32Q    => fun _ => fct2_11
  | FMSUB_RMM_Q_32Q    => fun _ => fct2_11
  | FMSUB_DYN_Q_32Q    => fun _ => fct2_11
  | FNMSUB_RNE_Q_32Q   => fun _ => fct2_11
  | FNMSUB_RTZ_Q_32Q   => fun _ => fct2_11
  | FNMSUB_RDN_Q_32Q   => fun _ => fct2_11
  | FNMSUB_RUP_Q_32Q   => fun _ => fct2_11
  | FNMSUB_RMM_Q_32Q   => fun _ => fct2_11
  | FNMSUB_DYN_Q_32Q   => fun _ => fct2_11
  | FNMADD_RNE_Q_32Q   => fun _ => fct2_11
  | FNMADD_RTZ_Q_32Q   => fun _ => fct2_11
  | FNMADD_RDN_Q_32Q   => fun _ => fct2_11
  | FNMADD_RUP_Q_32Q   => fun _ => fct2_11
  | FNMADD_RMM_Q_32Q   => fun _ => fct2_11
  | FNMADD_DYN_Q_32Q   => fun _ => fct2_11
  | FMADD_RNE_Q_64Q    => fun _ => fct2_11
  | FMADD_RTZ_Q_64Q    => fun _ => fct2_11
  | FMADD_RDN_Q_64Q    => fun _ => fct2_11
  | FMADD_RUP_Q_64Q    => fun _ => fct2_11
  | FMADD_RMM_Q_64Q    => fun _ => fct2_11
  | FMADD_DYN_Q_64Q    => fun _ => fct2_11
  | FMSUB_RNE_Q_64Q    => fun _ => fct2_11
  | FMSUB_RTZ_Q_64Q    => fun _ => fct2_11
  | FMSUB_RDN_Q_64Q    => fun _ => fct2_11
  | FMSUB_RUP_Q_64Q    => fun _ => fct2_11
  | FMSUB_RMM_Q_64Q    => fun _ => fct2_11
  | FMSUB_DYN_Q_64Q    => fun _ => fct2_11
  | FNMSUB_RNE_Q_64Q   => fun _ => fct2_11
  | FNMSUB_RTZ_Q_64Q   => fun _ => fct2_11
  | FNMSUB_RDN_Q_64Q   => fun _ => fct2_11
  | FNMSUB_RUP_Q_64Q   => fun _ => fct2_11
  | FNMSUB_RMM_Q_64Q   => fun _ => fct2_11
  | FNMSUB_DYN_Q_64Q   => fun _ => fct2_11
  | FNMADD_RNE_Q_64Q   => fun _ => fct2_11
  | FNMADD_RTZ_Q_64Q   => fun _ => fct2_11
  | FNMADD_RDN_Q_64Q   => fun _ => fct2_11
  | FNMADD_RUP_Q_64Q   => fun _ => fct2_11
  | FNMADD_RMM_Q_64Q   => fun _ => fct2_11
  | FNMADD_DYN_Q_64Q   => fun _ => fct2_11
  | _                  => fun _ => False_rec _ _
  end); try reflexivity; simpl in e; inversion e.
Defined.
