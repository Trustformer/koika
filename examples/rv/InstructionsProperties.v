(*! Definition of functions helpful for filtering instructions !*)

Require Import List.
Import ListNotations.

Require Import Koika.Frontend.

Require Import rv.Instructions rv.IFields rv.ITypes rv.InstructionsOpcodes
rv.InstructionsFct2 rv.InstructionsFct3 rv.InstructionsFct7.

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

Definition optional_prepend :
  forall {A : Type} (f : A -> bool) (i : A)
  (l : {r : list A | forall v : A, In v r -> f v = true}),
  {r : list A | forall v : A, In v r -> f v = true}.
Proof.
  intros.
  remember (f i) as j.
  destruct j.
  - exists (i::(proj1_sig l)). destruct l. simpl. intros. destruct H.
    + now subst.
    + now apply (e v).
  - assumption.
Defined.

(* TODO useless, replace with standard library equivalent *)
Definition custom_filter :
  forall {A : Type} (f : A -> bool) (input : list A),
  {r : list A | forall v : A, In v r -> f v = true}.
Proof.
  refine (fun A f input =>
    let helper := (
      fix helper_f
        {A : Type} (f : A -> bool) (i : list A)
        (o : {r : list A | forall v : A, In v r -> f v = true})
        : {r : list A | forall v : A, In v r -> f v = true}
      :=
        match i with
        | []   => o
        | h::t => helper_f f t (optional_prepend f h o)
        end
    ) in helper f input (exist _ [] _)
  ). easy.
Defined.

Definition to_list_of_dependents :
  forall {A : Type} {f : A -> bool}
  (l : {r : list A | forall v : A, In v r -> f v = true}),
  list {x : A | f x = true}.
Proof.
  refine (
    fun A f l =>
      let helper := (
        fix helper_f {A : Type} (f : A -> bool)
          (i : list A) (p : forall v : A, In v i -> f v = true)
          (o : list {x : A | f x = true}) : list {x : A | f x = true}
        := (
        match i as m return (i = m -> list {x : A | f x = true}) with
          | []   => fun _ => o
          | h::t => fun _ => helper_f f t _ ((exist _ h _)::o)
          end
        ) (eq_refl i)
      ) in helper f (proj1_sig l) (proj2_sig l) []
  ); try intros; apply p; rewrite e; simpl.
  - right. trivial.
  - left. trivial.
Defined.

Definition remove_dups {A : Set} (l : list A) (eq : A -> A -> bool) : list A :=
  (fix helper_f i acc :=
    match i with
    | []   => acc
    | h::t =>
        if (existsb (eq h) t) then
          helper_f t acc
        else
          helper_f t (h::acc)
    end
  ) l [].

(* TODO refactor *)
Definition get_fcts3 (o : opcode_name) (instrs : list instruction)
  : list fct3_type
:=
  let i := filter (fun i => opcode_name_beq (instruction_opcode i) o) instrs in
  (* All instructions sharing the same opcode also share the same type, so the
     following line might seem pointless. The thing is, Coq does not know this
     and has to be persuaded that each instruction in the list has an fct3 field
     for dependent typing reasons.
  *)
  let i_fcts3 :=
    custom_filter (fun i => has_fct3 (get_instruction_i_type i)) i
  in
  let i3 := to_list_of_dependents i_fcts3 in
  remove_dups
    (map (fun x => instruction_fct3 (proj1_sig x) (proj2_sig x)) i3)
    fct3_type_beq
.

Definition get_fcts2 (o : opcode_name) (f3 : fct3_type)
  (instrs : list instruction) : list fct2_type
:=
  let same_opcode :=
    (filter (fun i => (opcode_name_beq (instruction_opcode i) o)) instrs)
  in
  (* This is pointless and will be removed eventually through dependent
     typing
  *)
  let same_opcode_and_fct3_present := to_list_of_dependents (
    custom_filter (fun i => has_fct3 (get_instruction_i_type i)) same_opcode
  ) in
  let same_opcode_same_fct3_dependent := filter
    (fun i => fct3_type_beq (instruction_fct3 (proj1_sig i) (proj2_sig i)) f3)
    same_opcode_and_fct3_present
  in
  let same_opcode_same_fct3 :=
    map (fun i => proj1_sig i) same_opcode_same_fct3_dependent
  in
  let matching_and_fct2_present_dependent := custom_filter
    (fun i => has_fct2 (get_instruction_i_type i)) same_opcode_same_fct3
  in
  let matching_and_fct2_present :=
    to_list_of_dependents matching_and_fct2_present_dependent
  in
  remove_dups
    (
      map (fun x => instruction_fct2 (proj1_sig x) (proj2_sig x))
        matching_and_fct2_present
    )
    fct2_type_beq
  .

Definition get_fcts7 (o : opcode_name) (f3 : fct3_type)
  (instrs : list instruction) : list fct7_type
:=
  let same_opcode :=
    (filter (fun i => (opcode_name_beq (instruction_opcode i) o)) instrs)
  in
  (* This is pointless and will be removed eventually through dependent
     typing
  *)
  let same_opcode_and_fct3_present := to_list_of_dependents (
    custom_filter (fun i => has_fct3 (get_instruction_i_type i)) same_opcode
  ) in
  let same_opcode_same_fct3_dependent := filter
    (fun i => fct3_type_beq (instruction_fct3 (proj1_sig i) (proj2_sig i)) f3)
    same_opcode_and_fct3_present
  in
  let same_opcode_same_fct3 :=
    map (fun i => proj1_sig i) same_opcode_same_fct3_dependent
  in
  let matching_and_fct7_present_dependent := custom_filter
    (fun i => has_fct7 (get_instruction_i_type i)) same_opcode_same_fct3
  in
  let matching_and_fct7_present :=
    to_list_of_dependents matching_and_fct7_present_dependent
  in
  remove_dups
    (
      map (fun x => instruction_fct7 (proj1_sig x) (proj2_sig x))
      matching_and_fct7_present
    )
    fct7_type_beq
  .

Definition get_imm_fields_from_instructions (instrs : list instruction) :=
  let all_present_fields := get_i_fields_list_from_instructions instrs in
  filter (fun i =>
    match i with
    | immI => true
    | immS => true
    | immB => true
    | immU => true
    | immJ => true
    | _    => false
    end
  ) all_present_fields
.

Definition get_fcts3_in_instructions (instrs : list instruction)
  : list fct3_type
:=
  let fct3_present_dependent :=
    custom_filter (fun i => has_fct3 (get_instruction_i_type i)) instrs
  in
  let fct3_present := to_list_of_dependents fct3_present_dependent in
  remove_dups
    (map (fun x => instruction_fct3 (proj1_sig x) (proj2_sig x)) fct3_present)
    fct3_type_beq
.

Definition filter_by_fct3 (instrs : list instruction) (f3 : fct3_type)
  : list instruction
:=
  let fct3_present_dependent :=
    custom_filter (fun i => has_fct3 (get_instruction_i_type i)) instrs
  in
  let fct3_present := to_list_of_dependents fct3_present_dependent in
  let same_fct3 := filter
    (fun i => fct3_type_beq (instruction_fct3 (proj1_sig i) (proj2_sig i)) f3)
    fct3_present
  in
  map (
    fun (x : {i : instruction | has_fct3 (get_instruction_i_type i) = true})
      => proj1_sig x
  ) same_fct3.

Definition get_fcts7_in_instructions
  (instrs : list instruction) (f3 : fct3_type) : list fct7_type
:=
  let fct3_present_dependent :=
    custom_filter (fun i => has_fct3 (get_instruction_i_type i)) instrs
  in
  let fct3_present := to_list_of_dependents fct3_present_dependent in
  let same_fct3 := map
    (fun
      (x : {i : instruction | has_fct3 (get_instruction_i_type i) = true}) =>
        proj1_sig x
    ) (
      filter (fun x =>
        fct3_type_beq (instruction_fct3 (proj1_sig x) (proj2_sig x)) f3
      ) fct3_present
    )
  in
  let fct7_present_dependent :=
    custom_filter (fun i => has_fct7 (get_instruction_i_type i)) same_fct3
  in
  let fct7_present := to_list_of_dependents fct7_present_dependent in
  remove_dups
    (map (fun x => instruction_fct7 (proj1_sig x) (proj2_sig x)) fct7_present)
    fct7_type_beq
.

Definition filter_by_fct3_and_fct7 (instrs : list instruction) (f3 : fct3_type)
  (f7 : fct7_type) : list instruction
:=
  let instrs3 := filter_by_fct3 instrs f3 in
  let fct7_present_dependent :=
    custom_filter (fun i => has_fct7 (get_instruction_i_type i)) instrs3
  in
  let fct7_present := to_list_of_dependents fct7_present_dependent in
  let same_fct7 := filter
    (fun i => fct7_type_beq (instruction_fct7 (proj1_sig i) (proj2_sig i)) f7)
    fct7_present
  in
  map (
    fun (x : {i : instruction | has_fct7 (get_instruction_i_type i) = true})
      => proj1_sig x
  ) same_fct7.

(* Decoding *)
Definition get_field_sublist (b : list bool) (first length : nat) :=
  firstn length (skipn first b).

Scheme Equality for list.

Definition get_opcode (b : list bool) : option opcode_name :=
  let candidates :=  [
    opc_OP    ; opc_JALR  ; opc_LOAD     ; opc_OP_IMM; opc_MISC_MEM;
    opc_STORE ; opc_BRANCH; opc_LUI      ; opc_AUIPC ; opc_JAL     ;
    opc_SYSTEM; opc_OP_32 ; opc_OP_IMM_32; opc_AMO   ; opc_OP_FP   ;
    opc_MADD  ; opc_MSUB  ; opc_NMSUB    ; opc_NMADD ; opc_LOAD_FP ;
    opc_STORE_FP
  ] in
  let sub_b := firstn 7 b in
  let matching := List.filter (
    fun x => list_beq bool (bool_eq) sub_b (vect_to_list (opcode_bin x))
  ) candidates in
  match matching with
  | h1::h2::t => None (* Should never happen *)
  | h::t      => Some h
  | nil       => None
  end.
Definition get_fct2 (b : list bool) : option fct2_type :=
  let candidates :=  [fct2_00; fct2_01; fct2_11] in
  let sub_b := firstn 2 (skipn 25 b) in
  let matching := List.filter (
    fun x => list_beq bool (bool_eq) sub_b (vect_to_list (fct2_bin x))
  ) candidates in
  match matching with
  | h1::h2::t => None (* Should never happen *)
  | h::t      => Some h
  | nil       => None
  end.
Definition get_fct3 (b : list bool) : option fct3_type :=
  let candidates :=  [
    fct3_000; fct3_001; fct3_010; fct3_011; fct3_100; fct3_101; fct3_110;
    fct3_111
  ] in
  let sub_b := firstn 3 (skipn 12 b) in
  let matching := List.filter (
    fun x => list_beq bool (bool_eq) sub_b (vect_to_list (fct3_bin x))
  ) candidates in
  match matching with
  | h1::h2::t => None (* Should never happen *)
  | h::t      => Some h
  | nil       => None
  end.
Definition get_fct7 (b : list bool) : option fct7_type :=
  let candidates :=  [
    fct7_0000000; fct7_0000001; fct7_0000010; fct7_0000011; fct7_0000100;
    fct7_0000101; fct7_0000110; fct7_0000111; fct7_0001000; fct7_0001001;
    fct7_0001010; fct7_0001011; fct7_0001100; fct7_0001101; fct7_0001110;
    fct7_0001111; fct7_0010000; fct7_0010001; fct7_0010010; fct7_0010011;
    fct7_0010100; fct7_0010101; fct7_0010111; fct7_0100000; fct7_0100001;
    fct7_0100010; fct7_0100011; fct7_0101100; fct7_0101101; fct7_0101111;
    fct7_0110000; fct7_0110001; fct7_0110010; fct7_0110011; fct7_1000000;
    fct7_1000001; fct7_1000010; fct7_1000011; fct7_1010000; fct7_1010001;
    fct7_1010010; fct7_1010011; fct7_1100000; fct7_1100001; fct7_1100010;
    fct7_1100011; fct7_1101000; fct7_1101001; fct7_1101011; fct7_1110000;
    fct7_1110001; fct7_1110010; fct7_1110011; fct7_1111000; fct7_1111001;
    fct7_1111011
  ] in
  let sub_b := firstn 7 (skipn 25 b) in
  let matching := List.filter (
    fun x => list_beq bool (bool_eq) sub_b (vect_to_list (fct7_bin x))
  ) candidates in
  match matching with
  | h1::h2::t => None (* Should never happen *)
  | h::t      => Some h
  | nil       => None
  end.

Compute get_fct3 (
  vect_to_list
  (Ob~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~1~1~0~0~0~1~1)
).

Definition filter_by_opcode (o : opcode_name) (instrs : list instruction)
  : list instruction
:= List.filter (fun i => opcode_name_beq o (instruction_opcode i)) instrs.
Definition filter_by_fct2_decode (fct2 : fct2_type) (instrs : list instruction)
  : list instruction
:=
  List.filter (fun i =>
    match maybe_instruction_fct2 i with
    | Some x => fct2_type_beq fct2 x
    | None   => false
    end
  ) instrs.
Definition filter_by_fct3_decode (fct3 : fct3_type) (instrs : list instruction)
  : list instruction
:=
  List.filter (fun i =>
    match maybe_instruction_fct3 i with
    | Some x => fct3_type_beq fct3 x
    | None   => false
    end
  ) instrs.
Definition filter_by_fct7_decode (fct7 : fct7_type) (instrs : list instruction)
  : list instruction
:=
  List.filter (fun i =>
    match maybe_instruction_fct7 i with
    | Some x => fct7_type_beq fct7 x
    | None   => false
    end
  ) instrs.

(* Definition decode_helper (b : list bool) (instrs : list instruction) *)
(*   : list instruction *)
(* := *)
(*   let opc      := get_opcode b in *)
(*   let fct2     := get_fct2 b in *)
(*   let fct3     := get_fct3 b in *)
(*   let fct7     := get_fct7 b in *)
(*   let instrs_0 := match o *)
(*   let type     := get_opcode_i_type opc in *)
(*   let instrs_1 := filter_by_opcode opc instrs in *)
(*   let instrs_2 := *)
(*     if (has_fct3 type) then *)
(*       filter_by_fct3_decode fct3 instrs_1 *)
(*     else instrs_1 *)
(*   in *)
(*   let instrs_3 := *)
(*     if (has_fct7 type) then filter_by_fct7_decode fct7 instrs_2 else instrs_2 *)
(*   in *)
(*   if (has_fct2 type) then filter_by_fct2_decode fct2 instrs_3 else instrs_3. *)

(* Definition decode (b : bits_t 32) (instrs : list instruction) : instruction := *)
(*   let bits := vect_to_list b in. *)

(* Compute get_opcode ( *)
(*   vect_to_list *)
(*   (Ob~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~1~1~0~0~0~1~1) *)
(* ). *)

(* TODO refactor *)
(* Definition filter_by_opcode (o : opcode_name) (instrs : list instruction) *)
(*   : list instruction *)
(* := List.filter (fun i => opcode_name_beq o (instruction_opcode i)) instrs. *)

(* Definition decode_helper (b : list bool) (instrs : list instruction) *)
(*   : list instruction *)
(* := *)
(*   let opc      := get_opcode b in *)
(*   let type     := get_opcode_i_type opc in *)
(*   let instrs_1 := filter_by_opcode opc instrs in *)
(*   let type     := get_i_type_from_opcode opc in *)
(*   let instrs_2 := if (has_fct3) then filter_by_fct3 b instrs_1 else instrs_1 in *)
(*   let instrs_3 := if (has_fct7) then filter_by_fct7 b instrs_2 else instrs_2 in *)
(*   if (has_fct2) then filter_by_fct2 b instrs_3 else instrs_3. *)

(* Definition decode (b : bits_t 32) (instrs : list instruction) : instruction := *)
(*   let bits := vect_to_list b in. *)
