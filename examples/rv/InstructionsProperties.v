Require Import List.
Import ListNotations.

Require Import Koika.Frontend.

Require Import rv.Instructions rv.IFields rv.ITypes rv.InstructionsOpcodes.

(* Types for efficiently tracking the presence of elements *)
(* TODO use sets instead *)
Record present_i_types := {
  RType_present : bool; R4Type_present : bool; IType_present : bool;
  SType_present : bool; BType_present  : bool; UType_present : bool;
  JType_present : bool;
}.

Record present_i_fields := {
  opcode_present : bool; fct2_present : bool; fct3_present : bool;
  fct7_present   : bool; rs1_present  : bool; rs2_present  : bool;
  rs3_present    : bool; rd_present   : bool; immI_present : bool;
  immS_present   : bool; immB_present : bool; immU_present : bool;
  immJ_present   : bool;
}.

Record present_opcodes := {
  opc_OP_present        : bool; opc_JALR_present    : bool;
  opc_LOAD_present      : bool; opc_OP_IMM_present  : bool;
  opc_MISC_MEM_present  : bool; opc_STORE_present   : bool;
  opc_BRANCH_present    : bool; opc_LUI_present     : bool;
  opc_AUIPC_present     : bool; opc_JAL_present     : bool;
  opc_SYSTEM_present    : bool; opc_OP_32_present   : bool;
  opc_OP_IMM_32_present : bool; opc_AMO_present     : bool;
  opc_OP_FP_present     : bool; opc_MADD_present    : bool;
  opc_MSUB_present      : bool; opc_NMSUB_present   : bool;
  opc_NMADD_present     : bool; opc_LOAD_FP_present : bool;
  opc_STORE_FP_present  : bool
}.

(* Types present in a list of instructions *)
Definition get_present_i_types_from_instructions
  (instructions : list instruction)
: present_i_types :=
  let all_absent := {|
    RType_present := false; R4Type_present := false; IType_present := false;
    SType_present := false; BType_present  := false; UType_present := false;
    JType_present := false;
  |} in
  fold_left (fun p i =>
    match (get_instruction_i_type i) with
    | RType => {|
        RType_present := true           ; R4Type_present := R4Type_present p;
        IType_present := IType_present p; SType_present  := SType_present  p;
        BType_present := BType_present p; UType_present  := UType_present  p;
        JType_present := JType_present p;
      |}
    | R4Type => {|
        RType_present := RType_present p; R4Type_present := true;
        IType_present := IType_present p; SType_present  := SType_present p;
        BType_present := BType_present p; UType_present  := UType_present p;
        JType_present := JType_present p;
      |}
    | IType => {|
        RType_present := RType_present p; R4Type_present := R4Type_present p;
        IType_present := true           ; SType_present  := SType_present  p;
        BType_present := BType_present p; UType_present  := UType_present  p;
        JType_present := JType_present p;
      |}
    | SType => {|
        RType_present := RType_present p; R4Type_present := R4Type_present p;
        IType_present := IType_present p; SType_present  := true;
        BType_present := BType_present p; UType_present  := UType_present  p;
        JType_present := JType_present p;
      |}
    | BType => {|
        RType_present := RType_present p; R4Type_present := R4Type_present p;
        IType_present := IType_present p; SType_present  := SType_present  p;
        BType_present := true           ; UType_present  := UType_present  p;
        JType_present := JType_present p;
      |}
    | UType => {|
        RType_present := RType_present p; R4Type_present := R4Type_present p;
        IType_present := IType_present p; SType_present  := SType_present  p;
        BType_present := BType_present p; UType_present  := true;
        JType_present := JType_present p;
      |}
    | JType => {|
        RType_present := RType_present p; R4Type_present := R4Type_present p;
        IType_present := IType_present p; SType_present  := SType_present  p;
        BType_present := BType_present p; UType_present  := UType_present  p;
        JType_present := true;
      |}
    end
  ) instructions all_absent.

(* List of types from present_i_types *)
Definition check_i_type_presence (present_types : present_i_types) (t : i_type)
: option i_type :=
  match t with
  | RType  => if (RType_present  present_types) then Some t else None
  | R4Type => if (R4Type_present present_types) then Some t else None
  | IType  => if (IType_present  present_types) then Some t else None
  | SType  => if (SType_present  present_types) then Some t else None
  | BType  => if (BType_present  present_types) then Some t else None
  | UType  => if (UType_present  present_types) then Some t else None
  | JType  => if (JType_present  present_types) then Some t else None
  end.

Definition get_i_types_from_present_i_types (present_types : present_i_types)
: list i_type :=
  let all_types := RType::R4Type::IType::SType::BType::UType::JType::[] in
  let after := map (check_i_type_presence present_types) all_types in
  fold_left (fun p t =>
    match t with
    | Some x => x::p
    | None => p
    end
  ) after [].

(* Fields present in a list of types *)
Definition get_present_i_fields_from_i_type (type : i_type)
: present_i_fields :=
  {|
    opcode_present := has_opcode type; fct2_present := has_fct2 type;
    fct3_present   := has_fct3   type; fct7_present := has_fct7 type;
    rs1_present    := has_rs1    type; rs2_present  := has_rs2  type;
    rs3_present    := has_rs3    type; rd_present   := has_rd   type;
    immI_present   := has_immI   type; immS_present := has_immS type;
    immB_present   := has_immB   type; immU_present := has_immU type;
    immJ_present   := has_immJ   type;
  |}.

Definition merge_present_i_fields (fp1 fp2 : present_i_fields)
: present_i_fields :=
  {|
    opcode_present := opcode_present fp1 || opcode_present fp2;
    fct2_present   := fct2_present   fp1 || fct2_present   fp2;
    fct3_present   := fct3_present   fp1 || fct3_present   fp2;
    fct7_present   := fct7_present   fp1 || fct7_present   fp2;
    rs1_present    := rs1_present    fp1 || rs1_present    fp2;
    rs2_present    := rs2_present    fp1 || rs2_present    fp2;
    rs3_present    := rs3_present    fp1 || rs3_present    fp2;
    rd_present     := rd_present     fp1 || rd_present     fp2;
    immI_present   := immI_present   fp1 || immI_present   fp2;
    immS_present   := immS_present   fp1 || immS_present   fp2;
    immB_present   := immB_present   fp1 || immB_present   fp2;
    immU_present   := immU_present   fp1 || immU_present   fp2;
    immJ_present   := immJ_present   fp1 || immJ_present   fp2;
  |}.

Definition get_present_i_fields_from_i_types (types : list i_type)
: present_i_fields :=
  let no_i_fields := {|
    opcode_present := false; fct2_present := false; fct3_present := false;
    fct7_present   := false; rs1_present  := false; rs2_present  := false;
    rs3_present    := false; rd_present   := false; immI_present := false;
    immS_present   := false; immB_present := false; immU_present := false;
    immJ_present   := false;
  |} in
  fold_left
    (fun p t => merge_present_i_fields p (get_present_i_fields_from_i_type t))
    types no_i_fields.

(* List of fields from present_i_fields *)
Definition check_i_field_presence
  (present_fields : present_i_fields) (f : i_field)
: option i_field :=
  match f with
  | opcode => if (opcode_present present_fields) then Some f else None
  | fct2   => if (fct2_present   present_fields) then Some f else None
  | fct3   => if (fct3_present   present_fields) then Some f else None
  | fct7   => if (fct7_present   present_fields) then Some f else None
  | rs1    => if (rs1_present    present_fields) then Some f else None
  | rs2    => if (rs2_present    present_fields) then Some f else None
  | rs3    => if (rs3_present    present_fields) then Some f else None
  | rd     => if (rd_present     present_fields) then Some f else None
  | immI   => if (immI_present   present_fields) then Some f else None
  | immS   => if (immS_present   present_fields) then Some f else None
  | immB   => if (immB_present   present_fields) then Some f else None
  | immU   => if (immU_present   present_fields) then Some f else None
  | immJ   => if (immJ_present   present_fields) then Some f else None
  end.

Definition get_i_fields_list_from_present_i_fields
  (present_fields : present_i_fields)
: list i_field :=
  let all_i_fields :=
    opcode::fct2::fct3::fct7::rs1::rs2::rs3::rd::immI::immS::immB::immU::immJ::
    []
  in
  let after := map (check_i_field_presence present_fields) all_i_fields in
  fold_left (fun p f =>
    match f with
    | Some f => f::p
    | None => p
    end
  ) after [].

(* List of fields from list of instructions *)
Definition get_i_fields_list_from_instructions (instrs : list instruction)
: list i_field :=
  get_i_fields_list_from_present_i_fields (get_present_i_fields_from_i_types (
    get_i_types_from_present_i_types (
      get_present_i_types_from_instructions instrs
    )
  )).

(* List of possible information fields values from instructions *)
Definition get_present_opcodes_from_instructions (instrs : list instruction)
: present_opcodes :=
  let all_absent := {|
    opc_OP_present        := false; opc_JALR_present    := false;
    opc_LOAD_present      := false; opc_OP_IMM_present  := false;
    opc_MISC_MEM_present  := false; opc_STORE_present   := false;
    opc_BRANCH_present    := false; opc_LUI_present     := false;
    opc_AUIPC_present     := false; opc_JAL_present     := false;
    opc_SYSTEM_present    := false; opc_OP_32_present   := false;
    opc_OP_IMM_32_present := false; opc_AMO_present     := false;
    opc_OP_FP_present     := false; opc_MADD_present    := false;
    opc_MSUB_present      := false; opc_NMSUB_present   := false;
    opc_NMADD_present     := false; opc_LOAD_FP_present := false;
    opc_STORE_FP_present  := false
  |} in
  fold_left (fun p i =>
    match (instruction_opcode i) with
    | opc_OP =>
      {|
        opc_OP_present        := true;
        opc_JALR_present      := opc_JALR_present      p;
        opc_LOAD_present      := opc_LOAD_present      p;
        opc_OP_IMM_present    := opc_OP_IMM_present    p;
        opc_MISC_MEM_present  := opc_MISC_MEM_present  p;
        opc_STORE_present     := opc_STORE_present     p;
        opc_BRANCH_present    := opc_BRANCH_present    p;
        opc_LUI_present       := opc_LUI_present       p;
        opc_AUIPC_present     := opc_AUIPC_present     p;
        opc_JAL_present       := opc_JAL_present       p;
        opc_SYSTEM_present    := opc_SYSTEM_present    p;
        opc_OP_32_present     := opc_OP_32_present     p;
        opc_OP_IMM_32_present := opc_OP_IMM_32_present p;
        opc_AMO_present       := opc_AMO_present       p;
        opc_OP_FP_present     := opc_OP_FP_present     p;
        opc_MADD_present      := opc_MADD_present      p;
        opc_MSUB_present      := opc_MSUB_present      p;
        opc_NMSUB_present     := opc_NMSUB_present     p;
        opc_NMADD_present     := opc_NMADD_present     p;
        opc_LOAD_FP_present   := opc_LOAD_FP_present   p;
        opc_STORE_FP_present  := opc_STORE_FP_present  p
      |}
    | opc_JALR =>
      {|
        opc_OP_present        := opc_OP_present        p;
        opc_JALR_present      := true;
        opc_LOAD_present      := opc_LOAD_present      p;
        opc_OP_IMM_present    := opc_OP_IMM_present    p;
        opc_MISC_MEM_present  := opc_MISC_MEM_present  p;
        opc_STORE_present     := opc_STORE_present     p;
        opc_BRANCH_present    := opc_BRANCH_present    p;
        opc_LUI_present       := opc_LUI_present       p;
        opc_AUIPC_present     := opc_AUIPC_present     p;
        opc_JAL_present       := opc_JAL_present       p;
        opc_SYSTEM_present    := opc_SYSTEM_present    p;
        opc_OP_32_present     := opc_OP_32_present     p;
        opc_OP_IMM_32_present := opc_OP_IMM_32_present p;
        opc_AMO_present       := opc_AMO_present       p;
        opc_OP_FP_present     := opc_OP_FP_present     p;
        opc_MADD_present      := opc_MADD_present      p;
        opc_MSUB_present      := opc_MSUB_present      p;
        opc_NMSUB_present     := opc_NMSUB_present     p;
        opc_NMADD_present     := opc_NMADD_present     p;
        opc_LOAD_FP_present   := opc_LOAD_FP_present   p;
        opc_STORE_FP_present  := opc_STORE_FP_present  p
      |}
    | opc_LOAD =>
      {|
        opc_OP_present        := opc_OP_present        p;
        opc_JALR_present      := opc_JALR_present      p;
        opc_LOAD_present      := true;
        opc_OP_IMM_present    := opc_OP_IMM_present    p;
        opc_MISC_MEM_present  := opc_MISC_MEM_present  p;
        opc_STORE_present     := opc_STORE_present     p;
        opc_BRANCH_present    := opc_BRANCH_present    p;
        opc_LUI_present       := opc_LUI_present       p;
        opc_AUIPC_present     := opc_AUIPC_present     p;
        opc_JAL_present       := opc_JAL_present       p;
        opc_SYSTEM_present    := opc_SYSTEM_present    p;
        opc_OP_32_present     := opc_OP_32_present     p;
        opc_OP_IMM_32_present := opc_OP_IMM_32_present p;
        opc_AMO_present       := opc_AMO_present       p;
        opc_OP_FP_present     := opc_OP_FP_present     p;
        opc_MADD_present      := opc_MADD_present      p;
        opc_MSUB_present      := opc_MSUB_present      p;
        opc_NMSUB_present     := opc_NMSUB_present     p;
        opc_NMADD_present     := opc_NMADD_present     p;
        opc_LOAD_FP_present   := opc_LOAD_FP_present   p;
        opc_STORE_FP_present  := opc_STORE_FP_present  p
      |}
    | opc_OP_IMM =>
      {|
        opc_OP_present        := opc_OP_present        p;
        opc_JALR_present      := opc_JALR_present      p;
        opc_LOAD_present      := opc_LOAD_present      p;
        opc_OP_IMM_present    := true;
        opc_MISC_MEM_present  := opc_MISC_MEM_present  p;
        opc_STORE_present     := opc_STORE_present     p;
        opc_BRANCH_present    := opc_BRANCH_present    p;
        opc_LUI_present       := opc_LUI_present       p;
        opc_AUIPC_present     := opc_AUIPC_present     p;
        opc_JAL_present       := opc_JAL_present       p;
        opc_SYSTEM_present    := opc_SYSTEM_present    p;
        opc_OP_32_present     := opc_OP_32_present     p;
        opc_OP_IMM_32_present := opc_OP_IMM_32_present p;
        opc_AMO_present       := opc_AMO_present       p;
        opc_OP_FP_present     := opc_OP_FP_present     p;
        opc_MADD_present      := opc_MADD_present      p;
        opc_MSUB_present      := opc_MSUB_present      p;
        opc_NMSUB_present     := opc_NMSUB_present     p;
        opc_NMADD_present     := opc_NMADD_present     p;
        opc_LOAD_FP_present   := opc_LOAD_FP_present   p;
        opc_STORE_FP_present  := opc_STORE_FP_present  p
      |}
    | opc_MISC_MEM =>
      {|
        opc_OP_present        := opc_OP_present        p;
        opc_JALR_present      := opc_JALR_present      p;
        opc_LOAD_present      := opc_LOAD_present      p;
        opc_OP_IMM_present    := opc_OP_IMM_present    p;
        opc_MISC_MEM_present  := true;
        opc_STORE_present     := opc_STORE_present     p;
        opc_BRANCH_present    := opc_BRANCH_present    p;
        opc_LUI_present       := opc_LUI_present       p;
        opc_AUIPC_present     := opc_AUIPC_present     p;
        opc_JAL_present       := opc_JAL_present       p;
        opc_SYSTEM_present    := opc_SYSTEM_present    p;
        opc_OP_32_present     := opc_OP_32_present     p;
        opc_OP_IMM_32_present := opc_OP_IMM_32_present p;
        opc_AMO_present       := opc_AMO_present       p;
        opc_OP_FP_present     := opc_OP_FP_present     p;
        opc_MADD_present      := opc_MADD_present      p;
        opc_MSUB_present      := opc_MSUB_present      p;
        opc_NMSUB_present     := opc_NMSUB_present     p;
        opc_NMADD_present     := opc_NMADD_present     p;
        opc_LOAD_FP_present   := opc_LOAD_FP_present   p;
        opc_STORE_FP_present  := opc_STORE_FP_present  p
      |}
    | opc_STORE =>
      {|
        opc_OP_present        := opc_OP_present        p;
        opc_JALR_present      := opc_JALR_present      p;
        opc_LOAD_present      := opc_LOAD_present      p;
        opc_OP_IMM_present    := opc_OP_IMM_present    p;
        opc_MISC_MEM_present  := opc_MISC_MEM_present  p;
        opc_STORE_present     := true;
        opc_BRANCH_present    := opc_BRANCH_present    p;
        opc_LUI_present       := opc_LUI_present       p;
        opc_AUIPC_present     := opc_AUIPC_present     p;
        opc_JAL_present       := opc_JAL_present       p;
        opc_SYSTEM_present    := opc_SYSTEM_present    p;
        opc_OP_32_present     := opc_OP_32_present     p;
        opc_OP_IMM_32_present := opc_OP_IMM_32_present p;
        opc_AMO_present       := opc_AMO_present       p;
        opc_OP_FP_present     := opc_OP_FP_present     p;
        opc_MADD_present      := opc_MADD_present      p;
        opc_MSUB_present      := opc_MSUB_present      p;
        opc_NMSUB_present     := opc_NMSUB_present     p;
        opc_NMADD_present     := opc_NMADD_present     p;
        opc_LOAD_FP_present   := opc_LOAD_FP_present   p;
        opc_STORE_FP_present  := opc_STORE_FP_present  p
      |}
    | opc_BRANCH =>
      {|
        opc_OP_present        := opc_OP_present        p;
        opc_JALR_present      := opc_JALR_present      p;
        opc_LOAD_present      := opc_LOAD_present      p;
        opc_OP_IMM_present    := opc_OP_IMM_present    p;
        opc_MISC_MEM_present  := opc_MISC_MEM_present  p;
        opc_STORE_present     := opc_STORE_present     p;
        opc_BRANCH_present    := true;
        opc_LUI_present       := opc_LUI_present       p;
        opc_AUIPC_present     := opc_AUIPC_present     p;
        opc_JAL_present       := opc_JAL_present       p;
        opc_SYSTEM_present    := opc_SYSTEM_present    p;
        opc_OP_32_present     := opc_OP_32_present     p;
        opc_OP_IMM_32_present := opc_OP_IMM_32_present p;
        opc_AMO_present       := opc_AMO_present       p;
        opc_OP_FP_present     := opc_OP_FP_present     p;
        opc_MADD_present      := opc_MADD_present      p;
        opc_MSUB_present      := opc_MSUB_present      p;
        opc_NMSUB_present     := opc_NMSUB_present     p;
        opc_NMADD_present     := opc_NMADD_present     p;
        opc_LOAD_FP_present   := opc_LOAD_FP_present   p;
        opc_STORE_FP_present  := opc_STORE_FP_present  p
      |}
    | opc_LUI =>
      {|
        opc_OP_present        := opc_OP_present        p;
        opc_JALR_present      := opc_JALR_present      p;
        opc_LOAD_present      := opc_LOAD_present      p;
        opc_OP_IMM_present    := opc_OP_IMM_present    p;
        opc_MISC_MEM_present  := opc_MISC_MEM_present  p;
        opc_STORE_present     := opc_STORE_present     p;
        opc_BRANCH_present    := opc_BRANCH_present    p;
        opc_LUI_present       := true;
        opc_AUIPC_present     := opc_AUIPC_present     p;
        opc_JAL_present       := opc_JAL_present       p;
        opc_SYSTEM_present    := opc_SYSTEM_present    p;
        opc_OP_32_present     := opc_OP_32_present     p;
        opc_OP_IMM_32_present := opc_OP_IMM_32_present p;
        opc_AMO_present       := opc_AMO_present       p;
        opc_OP_FP_present     := opc_OP_FP_present     p;
        opc_MADD_present      := opc_MADD_present      p;
        opc_MSUB_present      := opc_MSUB_present      p;
        opc_NMSUB_present     := opc_NMSUB_present     p;
        opc_NMADD_present     := opc_NMADD_present     p;
        opc_LOAD_FP_present   := opc_LOAD_FP_present   p;
        opc_STORE_FP_present  := opc_STORE_FP_present  p
      |}
    | opc_AUIPC =>
      {|
        opc_OP_present        := opc_OP_present        p;
        opc_JALR_present      := opc_JALR_present      p;
        opc_LOAD_present      := opc_LOAD_present      p;
        opc_OP_IMM_present    := opc_OP_IMM_present    p;
        opc_MISC_MEM_present  := opc_MISC_MEM_present  p;
        opc_STORE_present     := opc_STORE_present     p;
        opc_BRANCH_present    := opc_BRANCH_present    p;
        opc_LUI_present       := opc_LUI_present       p;
        opc_AUIPC_present     := true;
        opc_JAL_present       := opc_JAL_present       p;
        opc_SYSTEM_present    := opc_SYSTEM_present    p;
        opc_OP_32_present     := opc_OP_32_present     p;
        opc_OP_IMM_32_present := opc_OP_IMM_32_present p;
        opc_AMO_present       := opc_AMO_present       p;
        opc_OP_FP_present     := opc_OP_FP_present     p;
        opc_MADD_present      := opc_MADD_present      p;
        opc_MSUB_present      := opc_MSUB_present      p;
        opc_NMSUB_present     := opc_NMSUB_present     p;
        opc_NMADD_present     := opc_NMADD_present     p;
        opc_LOAD_FP_present   := opc_LOAD_FP_present   p;
        opc_STORE_FP_present  := opc_STORE_FP_present  p
      |}
    | opc_JAL =>
      {|
        opc_OP_present        := opc_OP_present        p;
        opc_JALR_present      := opc_JALR_present      p;
        opc_LOAD_present      := opc_LOAD_present      p;
        opc_OP_IMM_present    := opc_OP_IMM_present    p;
        opc_MISC_MEM_present  := opc_MISC_MEM_present  p;
        opc_STORE_present     := opc_STORE_present     p;
        opc_BRANCH_present    := opc_BRANCH_present    p;
        opc_LUI_present       := opc_LUI_present       p;
        opc_AUIPC_present     := opc_AUIPC_present     p;
        opc_JAL_present       := true;
        opc_SYSTEM_present    := opc_SYSTEM_present    p;
        opc_OP_32_present     := opc_OP_32_present     p;
        opc_OP_IMM_32_present := opc_OP_IMM_32_present p;
        opc_AMO_present       := opc_AMO_present       p;
        opc_OP_FP_present     := opc_OP_FP_present     p;
        opc_MADD_present      := opc_MADD_present      p;
        opc_MSUB_present      := opc_MSUB_present      p;
        opc_NMSUB_present     := opc_NMSUB_present     p;
        opc_NMADD_present     := opc_NMADD_present     p;
        opc_LOAD_FP_present   := opc_LOAD_FP_present   p;
        opc_STORE_FP_present  := opc_STORE_FP_present  p
      |}
    | opc_SYSTEM =>
      {|
        opc_OP_present        := opc_OP_present        p;
        opc_JALR_present      := opc_JALR_present      p;
        opc_LOAD_present      := opc_LOAD_present      p;
        opc_OP_IMM_present    := opc_OP_IMM_present    p;
        opc_MISC_MEM_present  := opc_MISC_MEM_present  p;
        opc_STORE_present     := opc_STORE_present     p;
        opc_BRANCH_present    := opc_BRANCH_present    p;
        opc_LUI_present       := opc_LUI_present       p;
        opc_AUIPC_present     := opc_AUIPC_present     p;
        opc_JAL_present       := opc_JAL_present       p;
        opc_SYSTEM_present    := true;
        opc_OP_32_present     := opc_OP_32_present     p;
        opc_OP_IMM_32_present := opc_OP_IMM_32_present p;
        opc_AMO_present       := opc_AMO_present       p;
        opc_OP_FP_present     := opc_OP_FP_present     p;
        opc_MADD_present      := opc_MADD_present      p;
        opc_MSUB_present      := opc_MSUB_present      p;
        opc_NMSUB_present     := opc_NMSUB_present     p;
        opc_NMADD_present     := opc_NMADD_present     p;
        opc_LOAD_FP_present   := opc_LOAD_FP_present   p;
        opc_STORE_FP_present  := opc_STORE_FP_present  p
      |}
    | opc_OP_32 =>
      {|
        opc_OP_present        := opc_OP_present        p;
        opc_JALR_present      := opc_JALR_present      p;
        opc_LOAD_present      := opc_LOAD_present      p;
        opc_OP_IMM_present    := opc_OP_IMM_present    p;
        opc_MISC_MEM_present  := opc_MISC_MEM_present  p;
        opc_STORE_present     := opc_STORE_present     p;
        opc_BRANCH_present    := opc_BRANCH_present    p;
        opc_LUI_present       := opc_LUI_present       p;
        opc_AUIPC_present     := opc_AUIPC_present     p;
        opc_JAL_present       := opc_JAL_present       p;
        opc_SYSTEM_present    := opc_SYSTEM_present    p;
        opc_OP_32_present     := true;
        opc_OP_IMM_32_present := opc_OP_IMM_32_present p;
        opc_AMO_present       := opc_AMO_present       p;
        opc_OP_FP_present     := opc_OP_FP_present     p;
        opc_MADD_present      := opc_MADD_present      p;
        opc_MSUB_present      := opc_MSUB_present      p;
        opc_NMSUB_present     := opc_NMSUB_present     p;
        opc_NMADD_present     := opc_NMADD_present     p;
        opc_LOAD_FP_present   := opc_LOAD_FP_present   p;
        opc_STORE_FP_present  := opc_STORE_FP_present  p
      |}
    | opc_OP_IMM_32 =>
      {|
        opc_OP_present        := opc_OP_present        p;
        opc_JALR_present      := opc_JALR_present      p;
        opc_LOAD_present      := opc_LOAD_present      p;
        opc_OP_IMM_present    := opc_OP_IMM_present    p;
        opc_MISC_MEM_present  := opc_MISC_MEM_present  p;
        opc_STORE_present     := opc_STORE_present     p;
        opc_BRANCH_present    := opc_BRANCH_present    p;
        opc_LUI_present       := opc_LUI_present       p;
        opc_AUIPC_present     := opc_AUIPC_present     p;
        opc_JAL_present       := opc_JAL_present       p;
        opc_SYSTEM_present    := opc_SYSTEM_present    p;
        opc_OP_32_present     := opc_OP_32_present     p;
        opc_OP_IMM_32_present := true;
        opc_AMO_present       := opc_AMO_present       p;
        opc_OP_FP_present     := opc_OP_FP_present     p;
        opc_MADD_present      := opc_MADD_present      p;
        opc_MSUB_present      := opc_MSUB_present      p;
        opc_NMSUB_present     := opc_NMSUB_present     p;
        opc_NMADD_present     := opc_NMADD_present     p;
        opc_LOAD_FP_present   := opc_LOAD_FP_present   p;
        opc_STORE_FP_present  := opc_STORE_FP_present  p
      |}
    | opc_AMO =>
      {|
        opc_OP_present        := opc_OP_present        p;
        opc_JALR_present      := opc_JALR_present      p;
        opc_LOAD_present      := opc_LOAD_present      p;
        opc_OP_IMM_present    := opc_OP_IMM_present    p;
        opc_MISC_MEM_present  := opc_MISC_MEM_present  p;
        opc_STORE_present     := opc_STORE_present     p;
        opc_BRANCH_present    := opc_BRANCH_present    p;
        opc_LUI_present       := opc_LUI_present       p;
        opc_AUIPC_present     := opc_AUIPC_present     p;
        opc_JAL_present       := opc_JAL_present       p;
        opc_SYSTEM_present    := opc_SYSTEM_present    p;
        opc_OP_32_present     := opc_OP_32_present     p;
        opc_OP_IMM_32_present := opc_OP_IMM_32_present p;
        opc_AMO_present       := true;
        opc_OP_FP_present     := opc_OP_FP_present     p;
        opc_MADD_present      := opc_MADD_present      p;
        opc_MSUB_present      := opc_MSUB_present      p;
        opc_NMSUB_present     := opc_NMSUB_present     p;
        opc_NMADD_present     := opc_NMADD_present     p;
        opc_LOAD_FP_present   := opc_LOAD_FP_present   p;
        opc_STORE_FP_present  := opc_STORE_FP_present  p
      |}
    | opc_OP_FP =>
      {|
        opc_OP_present        := opc_OP_present        p;
        opc_JALR_present      := opc_JALR_present      p;
        opc_LOAD_present      := opc_LOAD_present      p;
        opc_OP_IMM_present    := opc_OP_IMM_present    p;
        opc_MISC_MEM_present  := opc_MISC_MEM_present  p;
        opc_STORE_present     := opc_STORE_present     p;
        opc_BRANCH_present    := opc_BRANCH_present    p;
        opc_LUI_present       := opc_LUI_present       p;
        opc_AUIPC_present     := opc_AUIPC_present     p;
        opc_JAL_present       := opc_JAL_present       p;
        opc_SYSTEM_present    := opc_SYSTEM_present    p;
        opc_OP_32_present     := opc_OP_32_present     p;
        opc_OP_IMM_32_present := opc_OP_IMM_32_present p;
        opc_AMO_present       := opc_AMO_present       p;
        opc_OP_FP_present     := true;
        opc_MADD_present      := opc_MADD_present      p;
        opc_MSUB_present      := opc_MSUB_present      p;
        opc_NMSUB_present     := opc_NMSUB_present     p;
        opc_NMADD_present     := opc_NMADD_present     p;
        opc_LOAD_FP_present   := opc_LOAD_FP_present   p;
        opc_STORE_FP_present  := opc_STORE_FP_present  p
      |}
    | opc_MADD =>
      {|
        opc_OP_present        := opc_OP_present        p;
        opc_JALR_present      := opc_JALR_present      p;
        opc_LOAD_present      := opc_LOAD_present      p;
        opc_OP_IMM_present    := opc_OP_IMM_present    p;
        opc_MISC_MEM_present  := opc_MISC_MEM_present  p;
        opc_STORE_present     := opc_STORE_present     p;
        opc_BRANCH_present    := opc_BRANCH_present    p;
        opc_LUI_present       := opc_LUI_present       p;
        opc_AUIPC_present     := opc_AUIPC_present     p;
        opc_JAL_present       := opc_JAL_present       p;
        opc_SYSTEM_present    := opc_SYSTEM_present    p;
        opc_OP_32_present     := opc_OP_32_present     p;
        opc_OP_IMM_32_present := opc_OP_IMM_32_present p;
        opc_AMO_present       := opc_AMO_present       p;
        opc_OP_FP_present     := opc_OP_FP_present     p;
        opc_MADD_present      := true;
        opc_MSUB_present      := opc_MSUB_present      p;
        opc_NMSUB_present     := opc_NMSUB_present     p;
        opc_NMADD_present     := opc_NMADD_present     p;
        opc_LOAD_FP_present   := opc_LOAD_FP_present   p;
        opc_STORE_FP_present  := opc_STORE_FP_present  p
      |}
    | opc_MSUB =>
      {|
        opc_OP_present        := opc_OP_present        p;
        opc_JALR_present      := opc_JALR_present      p;
        opc_LOAD_present      := opc_LOAD_present      p;
        opc_OP_IMM_present    := opc_OP_IMM_present    p;
        opc_MISC_MEM_present  := opc_MISC_MEM_present  p;
        opc_STORE_present     := opc_STORE_present     p;
        opc_BRANCH_present    := opc_BRANCH_present    p;
        opc_LUI_present       := opc_LUI_present       p;
        opc_AUIPC_present     := opc_AUIPC_present     p;
        opc_JAL_present       := opc_JAL_present       p;
        opc_SYSTEM_present    := opc_SYSTEM_present    p;
        opc_OP_32_present     := opc_OP_32_present     p;
        opc_OP_IMM_32_present := opc_OP_IMM_32_present p;
        opc_AMO_present       := opc_AMO_present       p;
        opc_OP_FP_present     := opc_OP_FP_present     p;
        opc_MADD_present      := opc_MADD_present      p;
        opc_MSUB_present      := true;
        opc_NMSUB_present     := opc_NMSUB_present     p;
        opc_NMADD_present     := opc_NMADD_present     p;
        opc_LOAD_FP_present   := opc_LOAD_FP_present   p;
        opc_STORE_FP_present  := opc_STORE_FP_present  p
      |}
    | opc_NMSUB =>
      {|
        opc_OP_present        := opc_OP_present        p;
        opc_JALR_present      := opc_JALR_present      p;
        opc_LOAD_present      := opc_LOAD_present      p;
        opc_OP_IMM_present    := opc_OP_IMM_present    p;
        opc_MISC_MEM_present  := opc_MISC_MEM_present  p;
        opc_STORE_present     := opc_STORE_present     p;
        opc_BRANCH_present    := opc_BRANCH_present    p;
        opc_LUI_present       := opc_LUI_present       p;
        opc_AUIPC_present     := opc_AUIPC_present     p;
        opc_JAL_present       := opc_JAL_present       p;
        opc_SYSTEM_present    := opc_SYSTEM_present    p;
        opc_OP_32_present     := opc_OP_32_present     p;
        opc_OP_IMM_32_present := opc_OP_IMM_32_present p;
        opc_AMO_present       := opc_AMO_present       p;
        opc_OP_FP_present     := opc_OP_FP_present     p;
        opc_MADD_present      := opc_MADD_present      p;
        opc_MSUB_present      := opc_MSUB_present      p;
        opc_NMSUB_present     := true;
        opc_NMADD_present     := opc_NMADD_present     p;
        opc_LOAD_FP_present   := opc_LOAD_FP_present   p;
        opc_STORE_FP_present  := opc_STORE_FP_present  p
      |}
    | opc_NMADD =>
      {|
        opc_OP_present        := opc_OP_present        p;
        opc_JALR_present      := opc_JALR_present      p;
        opc_LOAD_present      := opc_LOAD_present      p;
        opc_OP_IMM_present    := opc_OP_IMM_present    p;
        opc_MISC_MEM_present  := opc_MISC_MEM_present  p;
        opc_STORE_present     := opc_STORE_present     p;
        opc_BRANCH_present    := opc_BRANCH_present    p;
        opc_LUI_present       := opc_LUI_present       p;
        opc_AUIPC_present     := opc_AUIPC_present     p;
        opc_JAL_present       := opc_JAL_present       p;
        opc_SYSTEM_present    := opc_SYSTEM_present    p;
        opc_OP_32_present     := opc_OP_32_present     p;
        opc_OP_IMM_32_present := opc_OP_IMM_32_present p;
        opc_AMO_present       := opc_AMO_present       p;
        opc_OP_FP_present     := opc_OP_FP_present     p;
        opc_MADD_present      := opc_MADD_present      p;
        opc_MSUB_present      := opc_MSUB_present      p;
        opc_NMSUB_present     := opc_NMSUB_present     p;
        opc_NMADD_present     := true;
        opc_LOAD_FP_present   := opc_LOAD_FP_present   p;
        opc_STORE_FP_present  := opc_STORE_FP_present  p
      |}
    | opc_LOAD_FP =>
      {|
        opc_OP_present        := opc_OP_present        p;
        opc_JALR_present      := opc_JALR_present      p;
        opc_LOAD_present      := opc_LOAD_present      p;
        opc_OP_IMM_present    := opc_OP_IMM_present    p;
        opc_MISC_MEM_present  := opc_MISC_MEM_present  p;
        opc_STORE_present     := opc_STORE_present     p;
        opc_BRANCH_present    := opc_BRANCH_present    p;
        opc_LUI_present       := opc_LUI_present       p;
        opc_AUIPC_present     := opc_AUIPC_present     p;
        opc_JAL_present       := opc_JAL_present       p;
        opc_SYSTEM_present    := opc_SYSTEM_present    p;
        opc_OP_32_present     := opc_OP_32_present     p;
        opc_OP_IMM_32_present := opc_OP_IMM_32_present p;
        opc_AMO_present       := opc_AMO_present       p;
        opc_OP_FP_present     := opc_OP_FP_present     p;
        opc_MADD_present      := opc_MADD_present      p;
        opc_MSUB_present      := opc_MSUB_present      p;
        opc_NMSUB_present     := opc_NMSUB_present     p;
        opc_NMADD_present     := opc_NMADD_present     p;
        opc_LOAD_FP_present   := true;
        opc_STORE_FP_present  := opc_STORE_FP_present  p
      |}
    | opc_STORE_FP =>
      {|
        opc_OP_present        := opc_OP_present        p;
        opc_JALR_present      := opc_JALR_present      p;
        opc_LOAD_present      := opc_LOAD_present      p;
        opc_OP_IMM_present    := opc_OP_IMM_present    p;
        opc_MISC_MEM_present  := opc_MISC_MEM_present  p;
        opc_STORE_present     := opc_STORE_present     p;
        opc_BRANCH_present    := opc_BRANCH_present    p;
        opc_LUI_present       := opc_LUI_present       p;
        opc_AUIPC_present     := opc_AUIPC_present     p;
        opc_JAL_present       := opc_JAL_present       p;
        opc_SYSTEM_present    := opc_SYSTEM_present    p;
        opc_OP_32_present     := opc_OP_32_present     p;
        opc_OP_IMM_32_present := opc_OP_IMM_32_present p;
        opc_AMO_present       := opc_AMO_present       p;
        opc_OP_FP_present     := opc_OP_FP_present     p;
        opc_MADD_present      := opc_MADD_present      p;
        opc_MSUB_present      := opc_MSUB_present      p;
        opc_NMSUB_present     := opc_NMSUB_present     p;
        opc_NMADD_present     := opc_NMADD_present     p;
        opc_LOAD_FP_present   := opc_LOAD_FP_present   p;
        opc_STORE_FP_present  := true
      |}
    end
  ) instrs all_absent.

Definition check_opcode_presence (opcodes : present_opcodes) (o : opcode_name)
: option opcode_name :=
  match o with
  | opc_OP        => if (opc_OP_present        opcodes) then Some o else None
  | opc_JALR      => if (opc_JALR_present      opcodes) then Some o else None
  | opc_LOAD      => if (opc_LOAD_present      opcodes) then Some o else None
  | opc_OP_IMM    => if (opc_OP_IMM_present    opcodes) then Some o else None
  | opc_MISC_MEM  => if (opc_MISC_MEM_present  opcodes) then Some o else None
  | opc_STORE     => if (opc_STORE_present     opcodes) then Some o else None
  | opc_BRANCH    => if (opc_BRANCH_present    opcodes) then Some o else None
  | opc_LUI       => if (opc_LUI_present       opcodes) then Some o else None
  | opc_AUIPC     => if (opc_AUIPC_present     opcodes) then Some o else None
  | opc_JAL       => if (opc_JAL_present       opcodes) then Some o else None
  | opc_SYSTEM    => if (opc_SYSTEM_present    opcodes) then Some o else None
  | opc_OP_32     => if (opc_OP_32_present     opcodes) then Some o else None
  | opc_OP_IMM_32 => if (opc_OP_IMM_32_present opcodes) then Some o else None
  | opc_AMO       => if (opc_AMO_present       opcodes) then Some o else None
  | opc_OP_FP     => if (opc_OP_FP_present     opcodes) then Some o else None
  | opc_MADD      => if (opc_MADD_present      opcodes) then Some o else None
  | opc_MSUB      => if (opc_MSUB_present      opcodes) then Some o else None
  | opc_NMSUB     => if (opc_NMSUB_present     opcodes) then Some o else None
  | opc_NMADD     => if (opc_NMADD_present     opcodes) then Some o else None
  | opc_LOAD_FP   => if (opc_LOAD_FP_present   opcodes) then Some o else None
  | opc_STORE_FP  => if (opc_STORE_FP_present  opcodes) then Some o else None
  end.

Definition get_opcodes_from_present_opcodes (opcodes : present_opcodes)
: list opcode_name :=
  let all_opcodes := opc_OP::opc_JALR::opc_LOAD::opc_OP_IMM::opc_MISC_MEM::
    opc_STORE::opc_BRANCH::opc_LUI::opc_AUIPC::opc_JAL::opc_SYSTEM::opc_OP_32::
    opc_OP_IMM_32::opc_AMO::opc_OP_FP::opc_MADD::opc_MSUB::opc_NMSUB::
    opc_NMADD::opc_LOAD_FP::opc_STORE_FP::[]
  in
  let after := map (check_opcode_presence opcodes) all_opcodes in
  fold_left (fun p t =>
    match t with
    | Some x => x::p
    | None => p
    end
  ) after [].

Definition get_opcodes_from_instructions_list (instrs : list instruction)
: list opcode_name :=
  get_opcodes_from_present_opcodes (
    get_present_opcodes_from_instructions instrs
  ).

Definition get_opcodes_bin_from_opcodes (opcodes : list opcode_name)
: list (bits_t 7) :=
  map (opcode_bin) opcodes.

Definition get_rs1_users (instrs : list instruction) : list instruction :=
  filter (fun i => has_rs1 (get_instruction_i_type i)) instrs.

Definition get_rs2_users (instrs : list instruction) : list instruction :=
  filter (fun i => has_rs2 (get_instruction_i_type i)) instrs.

Definition get_rs3_users (instrs : list instruction) : list instruction :=
  filter (fun i => has_rs3 (get_instruction_i_type i)) instrs.

Definition get_fct2_users (instrs : list instruction) : list instruction :=
  filter (fun i => has_fct2 (get_instruction_i_type i)) instrs.

Definition get_fct3_users (instrs : list instruction) : list instruction :=
  filter (fun i => has_fct3 (get_instruction_i_type i)) instrs.

Definition get_fct7_users (instrs : list instruction) : list instruction :=
  filter (fun i => has_fct7 (get_instruction_i_type i)) instrs.

Definition get_rd_users (instrs : list instruction) : list instruction :=
  filter (fun i => has_rd (get_instruction_i_type i)) instrs.

Definition get_i_type_from_opcode (o : opcode_name) : i_type :=
  match o with
  | opc_OP        => RType  | opc_JALR     => IType  | opc_LOAD     => IType
  | opc_OP_IMM    => IType  | opc_MISC_MEM => IType  | opc_STORE    => SType
  | opc_BRANCH    => BType  | opc_LUI      => UType  | opc_AUIPC    => UType
  | opc_JAL       => JType  | opc_SYSTEM   => IType  | opc_OP_32    => RType
  | opc_OP_IMM_32 => IType  | opc_AMO      => RType  | opc_OP_FP    => RType
  | opc_MADD      => R4Type | opc_MSUB     => R4Type | opc_NMSUB    => R4Type
  | opc_NMADD     => R4Type | opc_LOAD_FP  => IType  | opc_STORE_FP => SType
  end.
