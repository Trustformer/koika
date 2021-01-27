Require Import Koika.Frontend.
Require Import rv.Instructions rv.IFields rv.ITypes rv.InstructionsOpcodes.

Inductive fct2_type := fct2_F | fct2_D | fct2_Q.

Definition fct2_bin (f : fct2_type) :=
  match f with
  | fct2_F => Ob~0~0 | fct2_D => Ob~0~1 | fct2_Q => Ob~1~1
  end.

Definition instruction_fct2 :
  forall (i : instruction), has_fct2 (get_instruction_i_type i) = true
  -> fct2_type.
Proof.
refine (fun i =>
  match i with
  | FMADD_RNE_S_32F    => fun _ => fct2_F
  | FMADD_RTZ_S_32F    => fun _ => fct2_F
  | FMADD_RDN_S_32F    => fun _ => fct2_F
  | FMADD_RUP_S_32F    => fun _ => fct2_F
  | FMADD_RMM_S_32F    => fun _ => fct2_F
  | FMADD_DYN_S_32F    => fun _ => fct2_F
  | FMSUB_RNE_S_32F    => fun _ => fct2_F
  | FMSUB_RTZ_S_32F    => fun _ => fct2_F
  | FMSUB_RDN_S_32F    => fun _ => fct2_F
  | FMSUB_RUP_S_32F    => fun _ => fct2_F
  | FMSUB_RMM_S_32F    => fun _ => fct2_F
  | FMSUB_DYN_S_32F    => fun _ => fct2_F
  | FNMSUB_RNE_S_32F   => fun _ => fct2_F
  | FNMSUB_RTZ_S_32F   => fun _ => fct2_F
  | FNMSUB_RDN_S_32F   => fun _ => fct2_F
  | FNMSUB_RUP_S_32F   => fun _ => fct2_F
  | FNMSUB_RMM_S_32F   => fun _ => fct2_F
  | FNMSUB_DYN_S_32F   => fun _ => fct2_F
  | FNMADD_RNE_S_32F   => fun _ => fct2_F
  | FNMADD_RTZ_S_32F   => fun _ => fct2_F
  | FNMADD_RDN_S_32F   => fun _ => fct2_F
  | FNMADD_RUP_S_32F   => fun _ => fct2_F
  | FNMADD_RMM_S_32F   => fun _ => fct2_F
  | FNMADD_DYN_S_32F   => fun _ => fct2_F
  | FMADD_RNE_S_64F    => fun _ => fct2_F
  | FMADD_RTZ_S_64F    => fun _ => fct2_F
  | FMADD_RDN_S_64F    => fun _ => fct2_F
  | FMADD_RUP_S_64F    => fun _ => fct2_F
  | FMADD_RMM_S_64F    => fun _ => fct2_F
  | FMADD_DYN_S_64F    => fun _ => fct2_F
  | FMSUB_RNE_S_64F    => fun _ => fct2_F
  | FMSUB_RTZ_S_64F    => fun _ => fct2_F
  | FMSUB_RDN_S_64F    => fun _ => fct2_F
  | FMSUB_RUP_S_64F    => fun _ => fct2_F
  | FMSUB_RMM_S_64F    => fun _ => fct2_F
  | FMSUB_DYN_S_64F    => fun _ => fct2_F
  | FNMSUB_RNE_S_64F   => fun _ => fct2_F
  | FNMSUB_RTZ_S_64F   => fun _ => fct2_F
  | FNMSUB_RDN_S_64F   => fun _ => fct2_F
  | FNMSUB_RUP_S_64F   => fun _ => fct2_F
  | FNMSUB_RMM_S_64F   => fun _ => fct2_F
  | FNMSUB_DYN_S_64F   => fun _ => fct2_F
  | FNMADD_RNE_S_64F   => fun _ => fct2_F
  | FNMADD_RTZ_S_64F   => fun _ => fct2_F
  | FNMADD_RDN_S_64F   => fun _ => fct2_F
  | FNMADD_RUP_S_64F   => fun _ => fct2_F
  | FNMADD_RMM_S_64F   => fun _ => fct2_F
  | FNMADD_DYN_S_64F   => fun _ => fct2_F
  | FMADD_RNE_D_32D    => fun _ => fct2_D
  | FMADD_RTZ_D_32D    => fun _ => fct2_D
  | FMADD_RDN_D_32D    => fun _ => fct2_D
  | FMADD_RUP_D_32D    => fun _ => fct2_D
  | FMADD_RMM_D_32D    => fun _ => fct2_D
  | FMADD_DYN_D_32D    => fun _ => fct2_D
  | FMSUB_RNE_D_32D    => fun _ => fct2_D
  | FMSUB_RTZ_D_32D    => fun _ => fct2_D
  | FMSUB_RDN_D_32D    => fun _ => fct2_D
  | FMSUB_RUP_D_32D    => fun _ => fct2_D
  | FMSUB_RMM_D_32D    => fun _ => fct2_D
  | FMSUB_DYN_D_32D    => fun _ => fct2_D
  | FNMSUB_RNE_D_32D   => fun _ => fct2_D
  | FNMSUB_RTZ_D_32D   => fun _ => fct2_D
  | FNMSUB_RDN_D_32D   => fun _ => fct2_D
  | FNMSUB_RUP_D_32D   => fun _ => fct2_D
  | FNMSUB_RMM_D_32D   => fun _ => fct2_D
  | FNMSUB_DYN_D_32D   => fun _ => fct2_D
  | FNMADD_RNE_D_32D   => fun _ => fct2_D
  | FNMADD_RTZ_D_32D   => fun _ => fct2_D
  | FNMADD_RDN_D_32D   => fun _ => fct2_D
  | FNMADD_RUP_D_32D   => fun _ => fct2_D
  | FNMADD_RMM_D_32D   => fun _ => fct2_D
  | FNMADD_DYN_D_32D   => fun _ => fct2_D
  | FMADD_RNE_D_64D    => fun _ => fct2_D
  | FMADD_RTZ_D_64D    => fun _ => fct2_D
  | FMADD_RDN_D_64D    => fun _ => fct2_D
  | FMADD_RUP_D_64D    => fun _ => fct2_D
  | FMADD_RMM_D_64D    => fun _ => fct2_D
  | FMADD_DYN_D_64D    => fun _ => fct2_D
  | FMSUB_RNE_D_64D    => fun _ => fct2_D
  | FMSUB_RTZ_D_64D    => fun _ => fct2_D
  | FMSUB_RDN_D_64D    => fun _ => fct2_D
  | FMSUB_RUP_D_64D    => fun _ => fct2_D
  | FMSUB_RMM_D_64D    => fun _ => fct2_D
  | FMSUB_DYN_D_64D    => fun _ => fct2_D
  | FNMSUB_RNE_D_64D   => fun _ => fct2_D
  | FNMSUB_RTZ_D_64D   => fun _ => fct2_D
  | FNMSUB_RDN_D_64D   => fun _ => fct2_D
  | FNMSUB_RUP_D_64D   => fun _ => fct2_D
  | FNMSUB_RMM_D_64D   => fun _ => fct2_D
  | FNMSUB_DYN_D_64D   => fun _ => fct2_D
  | FNMADD_RNE_D_64D   => fun _ => fct2_D
  | FNMADD_RTZ_D_64D   => fun _ => fct2_D
  | FNMADD_RDN_D_64D   => fun _ => fct2_D
  | FNMADD_RUP_D_64D   => fun _ => fct2_D
  | FNMADD_RMM_D_64D   => fun _ => fct2_D
  | FNMADD_DYN_D_64D   => fun _ => fct2_D
  | FMADD_RNE_Q_32Q    => fun _ => fct2_Q
  | FMADD_RTZ_Q_32Q    => fun _ => fct2_Q
  | FMADD_RDN_Q_32Q    => fun _ => fct2_Q
  | FMADD_RUP_Q_32Q    => fun _ => fct2_Q
  | FMADD_RMM_Q_32Q    => fun _ => fct2_Q
  | FMADD_DYN_Q_32Q    => fun _ => fct2_Q
  | FMSUB_RNE_Q_32Q    => fun _ => fct2_Q
  | FMSUB_RTZ_Q_32Q    => fun _ => fct2_Q
  | FMSUB_RDN_Q_32Q    => fun _ => fct2_Q
  | FMSUB_RUP_Q_32Q    => fun _ => fct2_Q
  | FMSUB_RMM_Q_32Q    => fun _ => fct2_Q
  | FMSUB_DYN_Q_32Q    => fun _ => fct2_Q
  | FNMSUB_RNE_Q_32Q   => fun _ => fct2_Q
  | FNMSUB_RTZ_Q_32Q   => fun _ => fct2_Q
  | FNMSUB_RDN_Q_32Q   => fun _ => fct2_Q
  | FNMSUB_RUP_Q_32Q   => fun _ => fct2_Q
  | FNMSUB_RMM_Q_32Q   => fun _ => fct2_Q
  | FNMSUB_DYN_Q_32Q   => fun _ => fct2_Q
  | FNMADD_RNE_Q_32Q   => fun _ => fct2_Q
  | FNMADD_RTZ_Q_32Q   => fun _ => fct2_Q
  | FNMADD_RDN_Q_32Q   => fun _ => fct2_Q
  | FNMADD_RUP_Q_32Q   => fun _ => fct2_Q
  | FNMADD_RMM_Q_32Q   => fun _ => fct2_Q
  | FNMADD_DYN_Q_32Q   => fun _ => fct2_Q
  | FMADD_RNE_Q_64Q    => fun _ => fct2_Q
  | FMADD_RTZ_Q_64Q    => fun _ => fct2_Q
  | FMADD_RDN_Q_64Q    => fun _ => fct2_Q
  | FMADD_RUP_Q_64Q    => fun _ => fct2_Q
  | FMADD_RMM_Q_64Q    => fun _ => fct2_Q
  | FMADD_DYN_Q_64Q    => fun _ => fct2_Q
  | FMSUB_RNE_Q_64Q    => fun _ => fct2_Q
  | FMSUB_RTZ_Q_64Q    => fun _ => fct2_Q
  | FMSUB_RDN_Q_64Q    => fun _ => fct2_Q
  | FMSUB_RUP_Q_64Q    => fun _ => fct2_Q
  | FMSUB_RMM_Q_64Q    => fun _ => fct2_Q
  | FMSUB_DYN_Q_64Q    => fun _ => fct2_Q
  | FNMSUB_RNE_Q_64Q   => fun _ => fct2_Q
  | FNMSUB_RTZ_Q_64Q   => fun _ => fct2_Q
  | FNMSUB_RDN_Q_64Q   => fun _ => fct2_Q
  | FNMSUB_RUP_Q_64Q   => fun _ => fct2_Q
  | FNMSUB_RMM_Q_64Q   => fun _ => fct2_Q
  | FNMSUB_DYN_Q_64Q   => fun _ => fct2_Q
  | FNMADD_RNE_Q_64Q   => fun _ => fct2_Q
  | FNMADD_RTZ_Q_64Q   => fun _ => fct2_Q
  | FNMADD_RDN_Q_64Q   => fun _ => fct2_Q
  | FNMADD_RUP_Q_64Q   => fun _ => fct2_Q
  | FNMADD_RMM_Q_64Q   => fun _ => fct2_Q
  | FNMADD_DYN_Q_64Q   => fun _ => fct2_Q
  | _                  => fun _ => False_rec _ _
  end); try reflexivity; simpl in e; inversion e.
Defined.
