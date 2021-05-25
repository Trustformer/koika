(*! Definitions related to the opcode instruction field !*)

Require Import Koika.Frontend.
Require Import rv.Instructions rv.IFields rv.ITypes.

Definition opc_OP        := Ob~0~1~1~0~0~1~1.
Definition opc_JALR      := Ob~1~1~0~0~1~1~1.
Definition opc_LOAD      := Ob~0~0~0~0~0~1~1.
Definition opc_OP_IMM    := Ob~0~0~1~0~0~1~1.
Definition opc_MISC_MEM  := Ob~0~0~0~1~1~1~1.
Definition opc_STORE     := Ob~0~1~0~0~0~1~1.
Definition opc_BRANCH    := Ob~1~1~0~0~0~1~1.
Definition opc_LUI       := Ob~0~1~1~0~1~1~1.
Definition opc_AUIPC     := Ob~0~0~1~0~1~1~1.
Definition opc_JAL       := Ob~1~1~0~1~1~1~1.
Definition opc_SYSTEM    := Ob~1~1~1~0~0~1~1.
Definition opc_OP_32     := Ob~0~1~1~1~0~1~1.
Definition opc_OP_IMM_32 := Ob~0~0~1~1~0~1~1.
Definition opc_AMO       := Ob~0~1~0~1~1~1~1.
Definition opc_OP_FP     := Ob~1~0~1~0~0~1~1.
Definition opc_MADD      := Ob~1~0~0~0~0~1~1.
Definition opc_MSUB      := Ob~1~0~0~0~1~1~1.
Definition opc_NMSUB     := Ob~1~0~0~1~0~1~1.
Definition opc_NMADD     := Ob~1~0~0~1~1~1~1.
Definition opc_LOAD_FP   := Ob~0~0~0~0~1~1~1.
Definition opc_STORE_FP  := Ob~0~1~0~0~1~1~1.

Definition get_opcode_i_type (o : opcode_name) : i_type :=
  match o with
  | opc_OP        => RType  | opc_JALR     => IType  | opc_LOAD     => IType
  | opc_OP_IMM    => IType  | opc_MISC_MEM => IType  | opc_STORE    => SType
  | opc_BRANCH    => BType  | opc_LUI      => UType  | opc_AUIPC    => UType
  | opc_JAL       => JType  | opc_SYSTEM   => IType  | opc_OP_32    => RType
  | opc_OP_IMM_32 => IType  | opc_AMO      => RType  | opc_OP_FP    => RType
  | opc_MADD      => R4Type | opc_MSUB     => R4Type | opc_NMSUB    => R4Type
  | opc_NMADD     => R4Type | opc_LOAD_FP  => IType  | opc_STORE_FP => SType
  end.

Definition get_instruction_i_type (i : instruction) : i_type :=
  get_opcode_i_type (instruction_opcode i).
