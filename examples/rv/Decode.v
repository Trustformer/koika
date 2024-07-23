Require Import List.
Import ListNotations.
Require Import Koika.Utils.Vect.
Require Import rv.IFields rv.InstructionsOpcodes rv.InstructionsFct2
  rv.InstructionsFct3 rv.InstructionsFct7 rv.Instructions
  rv.InstructionsProperties rv.ITypes.

Definition get_field_sublist (instr : list bool) (sp: subfield_properties)
: list bool :=
  firstn (subfield_length sp) (skipn (BinNat.N.to_nat (first_bit sp)) instr).

Fixpoint gen_shift_list (n: nat) : list bool :=
  match n with
  | 0 => []
  | S n' => false::(gen_shift_list n')
  end.

Definition get_field (f: i_field) (instr: list bool) :=
  let props := get_i_field_properties f in
  let bits :=
    List.concat (
      (List.map (get_field_sublist instr) (i_field_subfields props))
      ++ [gen_shift_list (shift props)]
    )
  in
  if is_sign_extended props then
    (gen_shift_list (32 - (List.length bits))) ++ bits
  else bits.

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
    fun x => list_beq bool Bool.eqb sub_b (vect_to_list (opcode_bin x))
  ) candidates in
  match matching with
  | h1::h2::t => None (* Should never happen *)
  | h::_      => Some h
  | nil       => None
  end.

Definition get_fct2 (b : list bool) : option fct2_type :=
  let candidates :=  [fct2_00; fct2_01; fct2_11] in
  let sub_b := firstn 2 (skipn 25 b) in
  let matching := List.filter (
    fun x => list_beq bool (Bool.eqb) sub_b (vect_to_list (fct2_bin x))
  ) candidates in
  match matching with
  | h1::h2::t => None (* Should never happen *)
  | h::_      => Some h
  | nil       => None
  end.

Definition get_fct3 (b : list bool) : option fct3_type :=
  let candidates :=  [
    fct3_000; fct3_001; fct3_010; fct3_011; fct3_100; fct3_101; fct3_110;
    fct3_111
  ] in
  let sub_b := firstn 3 (skipn 12 b) in
  let matching := List.filter (
    fun x => list_beq bool (Bool.eqb) sub_b (vect_to_list (fct3_bin x))
  ) candidates in
  match matching with
  | h1::h2::t => None (* Should never happen *)
  | h::_      => Some h
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
    fun x => list_beq bool (Bool.eqb) sub_b (vect_to_list (fct7_bin x))
  ) candidates in
  match matching with
  | h1::h2::t => None (* Should never happen *)
  | h::_      => Some h
  | nil       => None
  end.

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

Definition bits_to_opcode (bs: list bool) : option opcode_name :=
  match bs with
  | [false; true ; true ; false; false; true; true] => Some opc_OP
  | [true ; true ; false; false; true ; true; true] => Some opc_JALR
  | [false; false; false; false; false; true; true] => Some opc_LOAD
  | [false; false; true ; false; false; true; true] => Some opc_OP_IMM
  | [false; false; false; true ; true ; true; true] => Some opc_MISC_MEM
  | [false; true ; false; false; false; true; true] => Some opc_STORE
  | [true ; true ; false; false; false; true; true] => Some opc_BRANCH
  | [false; true ; true ; false; true ; true; true] => Some opc_LUI
  | [false; false; true ; false; true ; true; true] => Some opc_AUIPC
  | [true ; true ; false; true ; true ; true; true] => Some opc_JAL
  | [true ; true ; true ; false; false; true; true] => Some opc_SYSTEM
  | [false; true ; true ; true ; false; true; true] => Some opc_OP_32
  | [false; false; true ; true ; false; true; true] => Some opc_OP_IMM_32
  | [false; true ; false; true ; true ; true; true] => Some opc_AMO
  | [true ; false; true ; false; false; true; true] => Some opc_OP_FP
  | [true ; false; false; false; false; true; true] => Some opc_MADD
  | [true ; false; false; false; true ; true; true] => Some opc_MSUB
  | [true ; false; false; true ; false; true; true] => Some opc_NMSUB
  | [true ; false; false; true ; true ; true; true] => Some opc_NMADD
  | [false; false; false; false; true ; true; true] => Some opc_LOAD_FP
  | [false; true ; false; false; true ; true; true] => Some opc_STORE_FP
  | _ => None
  end.

Require Import Coq.Strings.String.

Definition get_imm_name (b : list bool) : option string :=
  let opcode := bits_to_opcode (get_field opcode b) in
  let type   := option_map get_i_type_from_opcode opcode in
  match type with
  | Some IType  => Some "ImmI"%string
  | Some SType  => Some "ImmS"%string
  | Some BType  => Some "ImmB"%string
  | Some UType  => Some "ImmU"%string
  | Some JType  => Some "ImmJ"%string
  | _           => None
  end.
