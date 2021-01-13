Require Import List.
Require Import Instructions IFields ITypes.

Definition get_i_field_information_quantity (f : i_field) :=
  let fp := get_i_field_properties f in
  let sfs := i_field_subfields fp in
  (shift fp) + (fold_left (fun c sfp => c + length sfp) sfs 0).

Definition get_instructions_types (instructions : list instruction)
: list i_type :=
  map (get_i_type) instructions.

Record present_types := {
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

Definition get_present_types (instructions : list instruction)
: present_types :=
  let all_absent := {|
    RType_present := false; R4Type_present := false; IType_present := false;
    SType_present := false; BType_present  := false; UType_present := false;
    JType_present := false;
  |} in
  fold_left (fun p i =>
    match (get_i_type i) with
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

Definition get_type_present_i_fields (type : i_type)
: i_field_presence :=
  {|
    opcode_present := has_opcode type; fct2_present := has_fct2 type;
    fct3_present   := has_fct3   type; fct7_present := has_fct7 type;
    rs1_present    := has_rs1    type; rs2_present  := has_rs2  type;
    rs3_present    := has_rs3    type; rd_present   := has_rd   type;
    immI_present   := has_immI   type; immS_present := has_immS type;
    immB_present   := has_immB   type; immU_present := has_immU type;
    immJ_present   := has_immJ   type;
  |}.

Definition merge_i_fields_presence (fp1 fp2 : i_field_presence)
: i_field_presence :=
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

Definition get_type (present_types : type_presence) (t : i_type)
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

Definition get_types_list (present_types : type_presence)
: list i_type :=
  let all_types := RType::R4Type::IType::SType::BType::UType::JType::[] in
  let after := map (get_type present_types) all_types in
  fold_left (fun p t =>
    match t with
    | Some x => x::p
    | None => p
    end
  ) after [].

Definition get_i_field (present_i_fields : i_field_presence) (f : i_field)
: option i_field :=
  match f with
  | opcode => if (opcode_present present_i_fields) then Some f else None
  | fct2   => if (fct2_present   present_i_fields) then Some f else None
  | fct3   => if (fct3_present   present_i_fields) then Some f else None
  | fct7   => if (fct7_present   present_i_fields) then Some f else None
  | rs1    => if (rs1_present    present_i_fields) then Some f else None
  | rs2    => if (rs2_present    present_i_fields) then Some f else None
  | rs3    => if (rs3_present    present_i_fields) then Some f else None
  | rd     => if (rd_present     present_i_fields) then Some f else None
  | immI   => if (immI_present   present_i_fields) then Some f else None
  | immS   => if (immS_present   present_i_fields) then Some f else None
  | immB   => if (immB_present   present_i_fields) then Some f else None
  | immU   => if (immU_present   present_i_fields) then Some f else None
  | immJ   => if (immJ_present   present_i_fields) then Some f else None
  end.

Definition get_i_fields_list (present_i_fields : i_field_presence)
: list i_field :=
  let all_i_fields :=
    opcode::fct2::fct3::fct7::rs1::rs2::rs3::rd::immI::immS::immB::immU::immJ::
    []
  in
  let after := map (get_i_field present_i_fields) all_i_fields in
  fold_left (fun p f =>
    match f with
    | Some f => f::p
    | None => p
    end
  ) after [].

Definition get_present_i_fields_ISA (instructions : list instruction)
: (i_field_presence) :=
  let present_types_list := get_types_list (get_present_types instructions) in
  let no_i_fields := {|
    opcode_present := false; fct2_present := false; fct3_present := false;
    fct7_present   := false; rs1_present  := false; rs2_present  := false;
    rs3_present    := false; rd_present   := false; immI_present := false;
    immS_present   := false; immB_present := false; immU_present := false;
    immJ_present   := false;
  |} in
  fold_left
    (fun p t => merge_i_fields_presence p (get_present_i_fields_type t))
    present_types_list no_i_fields.

Definition get_i_field_name (f : i_field) :=
  match f with
  | opcode => "opcode" | fct2   => "fct2" | fct3   => "fct3" | fct7   => "fct7"
  | rs1    => "rs1"    | rs2    => "rs2"  | rs3    => "rs3"  | rd     => "rd"
  | immI   => "immI"   | immS   => "immS" | immB   => "immB" | immU   => "immU"
  | immJ   => "immJ"
  end.

Definition get_i_fields_formatted_for_struct (instrs : list instruction) :=
  fold_left (fun l f =>
      (get_i_field_name f, bits_t (get_i_field_information_quantity f))::l
    ) (get_i_fields_list (get_present_i_fields_ISA instrs)) [].

Definition get_inst_i_field (instrs : list instruction) :=
  let present_i_fields := get_present_i_fields_ISA instrs in
{|
  struct_name   := "instFields";
  struct_i_fields := get_i_fields_formatted_for_struct instrs;
|}.

(* Definition inst_i_field := get_inst_i_field instrs. *)

(* Context {reg_t : Type}. *)
(* Definition getFields : UInternalFunction reg_t empty_ext_fn_t := *)
(*   {{ *)
(*   fun getFields (inst : bits_t 32) : struct_t inst_i_field => *)
(*     struct inst_i_field {} *)
(*       if false then funct3 := inst[|5`d12| :+ 3]; *)
(*       funct7 := inst[|5`d25| :+ 7]; *)
(*       funct5 := inst[|5`d27| :+ 5]; *)
(*       funct2 := inst[|5`d25| :+ 2]; *)
(*       rd     := inst[|5`d7|  :+ 5]; *)
(*       rs1    := inst[|5`d15| :+ 5]; *)
(*       rs2    := inst[|5`d20| :+ 5]; *)
(*       rs3    := inst[|5`d27| :+ 5]; *)
(*       immI   := {signExtend 12 20}(inst[|5`d20| :+ 12]); *)
(*       immS   := {signExtend 12 20}(inst[|5`d25| :+ 7] ++ inst[|5`d7| :+ 5]); *)
(*       immB   := {signExtend 13 19}( *)
(*         inst[|5`d31|] ++ inst[|5`d7|] ++ inst[|5`d25| :+ 6] *)
(*         ++ inst[|5`d8| :+ 4] ++ |1`d0| *)
(*       ); *)
(*       immU := (inst[|5`d12| :+ 20] ++ |12`d0|); *)
(*       immJ := {signExtend 21 11}( *)
(*         inst[|5`d31|] ++ inst[|5`d12| :+ 8] ++ inst[|5`d20|] *)
(*         ++ inst[|5`d21| :+ 10] ++ |1`d0| *)
(*       ); *)
(*       csr := (inst[|5`d20| :+ 12]) *)
(* }}. *)


(* Definition example_ISA := {| *)
(*   ISA_memory_model  := RVWMO; *)
(*   ISA_base_standard := RV32I; *)
(*   ISA_extensions    := []; *)
(* |}. *)
(* Definition instrs := ISA_instructions_set example_ISA. *)

(* Compute inst_i_field. *)
(* Compute get_i_fields_list (get_present_i_fields_ISA instrs). *)
(* Compute get_present_i_fields_ISA instrs. *)
(* Compute get_instructions_types instrs. *)
(* Compute get_present_types instrs. *)
