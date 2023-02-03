(*! Implementation of our RISC-V core !*)
Require Import List.
Import ListNotations.

Require Import Koika.Frontend Koika.Std.
Require Import rv.RVEncoding rv.Scoreboard rv.ShadowStack.

Require Import rv.ISA rv.Instructions rv.ITypes rv.IFields rv.StructsBuilding
  rv.InstructionsFct2 rv.InstructionsFct3 rv.InstructionsFct7
  rv.InstructionsOpcodes rv.InstructionsProperties rv.ModuleInstructions.

(* The ISA defined hereafter is used to parameterize the Kôika module *)
Definition isa : ISA := {|
  ISA_memory_model := RVWMO; ISA_base_standard := RV32I; ISA_extensions := []
|}.

Section RVHelpers.
  Definition instructions := (ISA_instructions_set isa).
  Context {reg_t: Type}.

  Definition imm_type := {|
    enum_name        := "immType";
    enum_members     := ["ImmI"; "ImmS"; "ImmB"; "ImmU"; "ImmJ"];
    enum_bitpatterns := vect_map (Bits.of_nat 3) [0; 1; 2; 3; 4]
  |}%vect.

  Definition decoded_sig := {|
    struct_name   := "decodedInst";
    struct_fields := ("valid_rs1", bits_t 1) :: ("valid_rs2", bits_t 1)
      :: ("valid_rd", bits_t 1) :: ("legal", bits_t 1) :: ("inst", bits_t 32)
      :: ("immediateType", maybe (enum_t imm_type)) :: nil
  |}.

  Definition inst_field := get_inst_fields_struct_from_ISA isa.

  Definition getFields `{finite_reg: FiniteType reg_t}
  : UInternalFunction reg_t empty_ext_fn_t := {|
    int_name    := "getFields";
    int_argspec := [prod_of_argsig
      {| arg_name := "inst"; arg_type := bits_t 32 |}
    ];
    int_retSig  := struct_t inst_field;
    int_body    :=
      USugar (UStructInit inst_field (
        fold_left (fun a f =>
          let fp            := get_i_field_properties f in
          let merge_actions := (fun a1 a2 => UBinop (UBits2 UConcat) a1 a2) in
          (* To get the final value of some fields, the result of slice_actions
             has to be shifted.
             For instance, the immJ field is only ever used for the JAL
             instruction. Its value is shifted to increase its reach in exchange
             for coarser controls.
             Since the value is built through concatenation, the shift has to be
             applied first.
           *)
          let manage_shift := (
            match shift fp with
            | 0 => None
            | x => Some (USugar (UConstBits (Bits.of_N x 0)))
            end
          ) in
          (* slice_actions returns an action that fetches the data from every
             subfield of the current field.
             For instance, opcode only has a single subfield, whereas the final
             value of immB is built by stitching together several uncontiguous
             sections of the bitcode of an instruction.
             See IFields.v for more details.
           *)
          let slice_actions : uaction reg_t empty_ext_fn_t := (
            let get_single_slice := (fun sp =>
              UBinop (UBits2 (UIndexedSlice (subfield_length sp))) {{ inst }}
              (USugar (UConstBits (Bits.of_N 5 (first_bit sp))))
            ) in
            let option_slices := fold_right (fun c a =>
              match a with
              | None   => Some (get_single_slice c)
              | Some x => Some (merge_actions (get_single_slice c) x)
              end
            ) manage_shift (i_field_subfields (get_i_field_properties f))
            in
            match option_slices with
            | None   => USugar USkip
            | Some x => x
            end
          ) in
          (* Some fields have to be extended to 32/64 bits before use *)
          let manage_sign_extension := (fun action =>
            match is_sign_extended fp with
            | true =>
              let base_info_qtt := get_i_field_base_information_quantity f in
              USugar (UCallModule id Lift_self
                (signExtend base_info_qtt (32 - base_info_qtt)) [action]
              )
            | false => action
            end
          ) in
          let field_action := manage_sign_extension (slice_actions) in
          (get_i_field_name f, field_action) :: a
        ) (get_i_fields_list_from_instructions instructions)
        []
      ))
  |}.

  (* TODO add fixed fields verification *)
  Definition isLegalInstruction `{finite_reg: FiniteType reg_t}
  : UInternalFunction reg_t empty_ext_fn_t := {|
    int_name    := "isLegalInstruction";
    int_argspec := [("inst", bits_t 32)];
    int_retSig  := bits_t 1;
    int_body    :=
      let opcodes := get_opcodes_from_instructions_list instructions in
      (* Helper functions *)
      let generate_fct2_match (o : opcode_name) (f3 : fct3_type)
        : uaction reg_t empty_ext_fn_t
      := (
        UBind "__reserved__matchPattern" {{ get(fields, funct2) }} (
          USugar (
            USwitch {{__reserved__matchPattern}} (USugar (UConstBits Ob~0))
            (map
              (fun f => (USugar (UConstBits (fct2_bin f)), {{ Ob~1 }}))
              (get_fcts2 o f3 instructions)
      )))) in
      let generate_fct7_match (o : opcode_name) (f3 : fct3_type)
        : uaction reg_t empty_ext_fn_t
      := (
        UBind "__reserved__matchPattern" {{ get(fields, funct7) }} (
          USugar (
            USwitch {{__reserved__matchPattern}} (USugar (UConstBits Ob~0))
            (map
              (fun f => (USugar (UConstBits (fct7_bin f)), {{ Ob~1 }}))
              (get_fcts7 o f3 instructions)
      )))) in
      let generate_fct3_match (o : opcode_name)
        : uaction reg_t empty_ext_fn_t
      := (
        UBind "__reserved__matchPattern" {{ get(fields, funct3) }} (
          USugar (
            USwitch {{__reserved__matchPattern}} (USugar (UConstBits Ob~0))
            (map (fun f =>
              (USugar (UConstBits (fct3_bin f)), (
                if (has_fct2 (get_opcode_i_type o)) then generate_fct2_match o f
                (* fct2 and fct7 are mutually exclusive. *)
                else (if (has_fct7 (get_opcode_i_type o)) then
                  generate_fct7_match o f
                else {{ Ob~1 }}
              )))) (get_fcts3 o instructions)
      )))) in
      (* Contents of the function start here *)
      UBind "fields" (USugar (UCallModule
        (fun x : reg_t => x) (fun x : empty_ext_fn_t => x) getFields [{{inst}}]
      ))
      (
        (* For each possible value of opcode, if the value is not used by any
           instruction, return invalid, else test if the combination of the
           opcode and the data of the funct3 field is legal *)
        UBind "__reserved__matchPattern" {{ get(fields, opcode) }} (
          USugar (
            USwitch {{__reserved__matchPattern}} (USugar (UConstBits Ob~0))
            (map (fun o =>
              (USugar (UConstBits (opcode_bin o)), (
                (* (fct2 or fct7) implies fct3, so checking for those happens
                   in generate_fct3_match *)
                if (has_fct3 (get_opcode_i_type o)) then generate_fct3_match o
                else {{ Ob~1 }}
        ))) opcodes))))
  |}.

  (* TODO only analyze useful bits - for instance, the last two bits of the
     opcode are always 11 and can thus be safely ignored *)
  Definition getImmediateType
    `{finite_reg: FiniteType reg_t}
  : UInternalFunction reg_t empty_ext_fn_t := {|
    int_name    := "getImmediateType";
    int_argspec := [("inst", bits_t 32)];
    int_retSig  := maybe (enum_t imm_type);
    int_body    := UBind "__reserved__matchPattern"
      (UBinop (UBits2 (UIndexedSlice 7)) {{inst}} {{|5`d0|}})
      (USugar (USwitch
        {{__reserved__matchPattern}}
        {{{invalid (enum_t imm_type)} ()}}
        (
          let opcodes := get_opcodes_from_instructions_list instructions in
          map (fun o => (
            USugar (UConstBits (opcode_bin o)),
            USugar (UStructInit {|
              struct_name   := "maybe_immType";
              struct_fields := [("valid", bits_t 1); ("data", enum_t imm_type)]
            |}
              [
                ("valid", USugar (UConstBits Ob~1));
                ("data", (
                  match o with
                  | opc_JALR      => {{ enum imm_type {ImmI} }}
                  | opc_LOAD      => {{ enum imm_type {ImmI} }}
                  | opc_OP_IMM    => {{ enum imm_type {ImmI} }}
                  | opc_MISC_MEM  => {{ enum imm_type {ImmI} }}
                  | opc_STORE     => {{ enum imm_type {ImmS} }}
                  | opc_BRANCH    => {{ enum imm_type {ImmB} }}
                  | opc_LUI       => {{ enum imm_type {ImmU} }}
                  | opc_AUIPC     => {{ enum imm_type {ImmU} }}
                  | opc_JAL       => {{ enum imm_type {ImmJ} }}
                  | opc_SYSTEM    => {{ enum imm_type {ImmI} }}
                  | opc_OP_IMM_32 => {{ enum imm_type {ImmI} }}
                  | opc_LOAD_FP   => {{ enum imm_type {ImmI} }}
                  | opc_STORE_FP  => {{ enum imm_type {ImmS} }}
                  (* Default value, TODO doesn't use invalid *)
                  | _             => {{ enum imm_type {ImmI} }}
                  end
      ))]))) opcodes)))
  |}.

  Definition usesRS1 : UInternalFunction reg_t empty_ext_fn_t := {|
    int_name    := "usesRS1";
    int_argspec := [prod_of_argsig
      {| arg_name := "inst"; arg_type := bits_t 32 |}
    ];
    int_retSig  := bits_t 1;
    int_body    := UBind "__reserved__matchPattern"
      (UBinop (UBits2 (UIndexedSlice 7)) {{inst}} {{|5`d0|}})
      (USugar (USwitch {{__reserved__matchPattern}} {{Ob~0}}
      (
        let rs1_opcodes := get_opcodes_from_instructions_list (
          get_rs1_users instructions
        ) in
        map (fun o =>
          (USugar (UConstBits (opcode_bin o)), {{Ob~1}})
        ) rs1_opcodes
      )
    ))
  |}.

  Definition usesRS2 : UInternalFunction reg_t empty_ext_fn_t := {|
    int_name    := "usesRS2";
    int_argspec := [prod_of_argsig
      {| arg_name := "inst"; arg_type := bits_t 32 |}
    ];
    int_retSig  := bits_t 1;
    int_body    := UBind "__reserved__matchPattern"
      (UBinop (UBits2 (UIndexedSlice 7)) {{inst}} {{|5`d0|}})
      (USugar (USwitch {{__reserved__matchPattern}} {{Ob~0}}
      (
        let rs2_opcodes := get_opcodes_from_instructions_list (
          get_rs2_users instructions
        ) in
        map
          (fun o => (USugar (UConstBits (opcode_bin o)), {{Ob~1}}))
          rs2_opcodes
      )
    ))
  |}.

  Definition usesRD : UInternalFunction reg_t empty_ext_fn_t := {|
    int_name := "usesRD";
    int_argspec := [prod_of_argsig
      {| arg_name := "inst"; arg_type := bits_t 32 |}
    ];
    int_retSig := bits_t 1;
    int_body := UBind "__reserved__matchPattern"
      (UBinop (UBits2 (UIndexedSlice 7)) {{inst}} {{|5`d0|}})
      (USugar (USwitch {{__reserved__matchPattern}} {{Ob~0}}
      (
        let rd_opcodes := get_opcodes_from_instructions_list (
          get_rd_users instructions
        ) in
        map (fun o =>
          (USugar (UConstBits (opcode_bin o)), {{Ob~1}})
        ) rd_opcodes
      )
    ))
  |}.

  Definition decode_fun
    `{finite_reg: FiniteType reg_t}
  : UInternalFunction reg_t empty_ext_fn_t := {{
    fun decode_fun (arg_inst : bits_t 32) : struct_t decoded_sig =>
      struct decoded_sig {
        valid_rs1     := usesRS1(arg_inst);
        valid_rs2     := usesRS2(arg_inst);
        valid_rd      := usesRD(arg_inst);
        legal         := isLegalInstruction(arg_inst);
        inst          := arg_inst;
        immediateType := getImmediateType(arg_inst)
      }
  }}.

  Definition getImmediate `{finite_reg: FiniteType reg_t}
  : UInternalFunction reg_t empty_ext_fn_t := {|
    int_name := "getImmediate";
    int_argspec := [prod_of_argsig
      {| arg_name := "dInst"; arg_type := struct_t decoded_sig |}
    ];
    int_retSig := bits_t 32;
    int_body :=
      UBind "imm_type_v" {{ get(dInst, immediateType) }}
      (
        UIf
          (UBinop (UEq false) {{ get(imm_type_v, valid) }}
            (USugar (UConstBits Ob~1)))
          (UBind "fields" {{ getFields(get(dInst, inst)) }}
            (
              UBind "__reserved__matchPattern" {{ get(imm_type_v, data) }}
                (USugar (USwitch {{ __reserved__matchPattern  }} {{ |32`d0| }}
                (
                  map
                    (fun i =>
                      match i with
                      | immI =>
                        ({{ enum imm_type {ImmI} }}, {{ get(fields, immI) }})
                      | immS =>
                        ({{ enum imm_type {ImmS} }}, {{ get(fields, immS) }})
                      | immB =>
                        ({{ enum imm_type {ImmB} }}, {{ get(fields, immB) }})
                      | immU =>
                        ({{ enum imm_type {ImmU} }}, {{ get(fields, immU) }})
                      | immJ =>
                        ({{ enum imm_type {ImmJ} }}, {{ get(fields, immJ) }})
                      (* should never happen *)
                      | _ => ({{ Ob~0 }}, {{ Ob~0 }})
                      end
                    )
                    (get_imm_fields_from_instructions instructions)
                )))
            )
          )
          {{ |32`d0| }}
      )
  |}.

  (* TODO find a cleaner way to manage shamt *)
  Definition get_semantics_binop_32 (i : instruction)
    : uaction reg_t empty_ext_fn_t
  :=
    match i with
    | ADDI_32I  => {{ a + b }}
    | SLTI_32I  => {{ zeroExtend(a <s b, 32) }}
    | SLTIU_32I => {{ zeroExtend(a < b, 32) }}
    | XORI_32I  => {{ a ^ b }}
    | ORI_32I   => {{ a || b }}
    | ANDI_32I  => {{ a && b }}
    | SLLI_32I  => {{ a << shamt }}
    | SRLI_32I  => {{ a >> shamt }}
    | SRAI_32I  => {{ a >>> shamt }}
    | ADD_32I   => {{ a + b }}
    | SUB_32I   => {{ a - b }}
    | SLL_32I   => {{ a << shamt }}
    | SLT_32I   => {{ zeroExtend(a <s b, 32) }}
    | SLTU_32I  => {{ zeroExtend(a < b, 32) }}
    | XOR_32I   => {{ a ^ b }}
    | SRL_32I   => {{ a >> shamt }}
    | SRA_32I   => {{ a >>> shamt }}
    | OR_32I    => {{ a || b }}
    | AND_32I   => {{ a && b }}
    | _         => USugar (USkip) (* TODO rm through dep. types, i_type *)
    end.

  Definition alu32 : UInternalFunction reg_t empty_ext_fn_t := {{
    fun alu32 (funct3 : bits_t 3) (funct7 : bits_t 7) (a : bits_t 32)
      (b : bits_t 32) : bits_t 32
    =>
    let shamt := b[Ob~0~0~0~0~0 :+ 5] in
      let inst_30 := funct7[|3`d5|] in
      match funct3 with
      | #funct3_ADD =>
        if (inst_30 == Ob~1) then
          a - b
        else
          a + b
      | #funct3_SLL  => a << shamt
      | #funct3_SLT  => zeroExtend(a <s b, 32)
      | #funct3_SLTU => zeroExtend(a < b, 32)
      | #funct3_XOR  => a ^ b
      | #funct3_SRL  => if (inst_30 == Ob~1) then a >>> shamt else a >> shamt
      | #funct3_OR   => a || b
      | #funct3_AND  => a && b
      return default: #(Bits.of_nat 32 0)
      end
  }}.

  (* TODO number of required arguments could vary depending on extensions *)
  Definition alu32B : UInternalFunction reg_t empty_ext_fn_t := {|
    int_name := "alu32";
    int_argspec := [
      ("funct3", bits_t 3); ("funct7", bits_t 7); ("a", bits_t 32);
      ("b", bits_t 32)
    ];
    int_retSig := bits_t 32;
    int_body := (
      let binops := filter (fun i =>
        (opcode_name_beq (instruction_opcode i) opc_OP)
        || (opcode_name_beq (instruction_opcode i) opc_OP_32)
        || (opcode_name_beq (instruction_opcode i) opc_OP_IMM)
        || (opcode_name_beq (instruction_opcode i) opc_OP_IMM_32)
        || (opcode_name_beq (instruction_opcode i) opc_OP_FP)
      ) instructions in
      let fcts3 : list fct3_type := get_fcts3_in_instructions binops in
      (
        UBind "shamt"
          (UBinop (UBits2 (UIndexedSlice 5)) {{ b }} {{ Ob~0~0~0~0~0 }})
        (
        UBind "__reserved__matchPattern" {{ funct3 }} (USugar (
          USwitch {{ __reserved__matchPattern }} {{ |32`d0| }} (
            map (fun i =>
              match (filter_by_fct3 binops i) with
              | [h]  =>
                (USugar (UConstBits (fct3_bin i)), get_semantics_binop_32 h)
              | _::_ => (
                USugar (UConstBits (fct3_bin i)),
                (UBind "__reserved__matchPattern" {{ funct7 }} (USugar (
                  USwitch {{ __reserved__matchPattern }} {{ |32`d0| }} (
                    let fcts7 := get_fcts7_in_instructions binops i in
                    map (fun j =>
                      match (filter_by_fct3_and_fct7 binops i j) with
                      | [h] => (
                        USugar (UConstBits (fct7_bin j)),
                        get_semantics_binop_32 h
                      )
                      | _   =>
                        (* Impossible case *)
                        (USugar (UConstBits (fct7_bin j)), {{ |32`d0| }})
                      end
                    ) fcts7
                  )
                )))
              )
              | _    =>
                (* Impossible case *)
                (USugar (UConstBits (fct3_bin i)), {{ |32`d0| }})
              end
            )
            fcts3
            )
          )
        ))
      )
    )
  |}.

  Definition execALU32
    `{finite_reg: FiniteType reg_t}
  : UInternalFunction reg_t empty_ext_fn_t := {{
    fun execALU32 (inst : bits_t 32) (rs1_val : bits_t 32) (rs2_val : bits_t 32)
      (imm_val : bits_t 32) (pc : bits_t 32) : bits_t 32
    =>
      let isLUI   := (inst[|5`d2|] == Ob~1) && (inst[|5`d5|] == Ob~1) in
      let isAUIPC := (inst[|5`d2|] == Ob~1) && (inst[|5`d5|] == Ob~0) in
      let isIMM   := (inst[|5`d5|] == Ob~0) in
      let rd_val  := |32`d0| in (
        if (isLUI) then set rd_val := imm_val
        else if (isAUIPC) then set rd_val := (pc + imm_val)
        else
          let alu_src1 := rs1_val in
          let alu_src2 := if isIMM then imm_val else rs2_val in
          let funct3   := get(getFields(inst), funct3) in
          let funct7   := get(getFields(inst), funct7) in
          let opcode   := get(getFields(inst), opcode) in
          if ((funct3 == #funct3_ADD) && isIMM) || (opcode == #opcode_BRANCH)
          then
            (* Replace the instruction by an add *)
            (set funct7 := #funct7_ADD)
          else
            pass;
            set rd_val := alu32(funct3, funct7, alu_src1, alu_src2));
            rd_val
  }}.

  Definition control_result := {|
    struct_name   := "control_result";
    struct_fields := ("nextPC", bits_t 32) :: ("taken", bits_t 1) :: nil
  |}.

  Definition execControl32 `{finite_reg: FiniteType reg_t}
  : UInternalFunction reg_t empty_ext_fn_t := {{
    fun execControl32 (inst : bits_t 32) (rs1_val : bits_t 32)
      (rs2_val : bits_t 32) (imm_val : bits_t 32) (pc : bits_t 32)
      : struct_t control_result
    =>
      let isControl := inst[|5`d4| :+ 3] == Ob~1~1~0 in
      let isJAL     := (inst[|5`d2|] == Ob~1) && (inst[|5`d3|] == Ob~1) in
      let isJALR    := (inst[|5`d2|] == Ob~1) && (inst[|5`d3|] == Ob~0) in
      let incPC     := pc + |32`d4| in
      let funct3    := get(getFields(inst), funct3) in
      let taken     := Ob~1 in (* for JAL and JALR *)
      let nextPC    := incPC in
      if (!isControl) then
        set taken  := Ob~0;
        set nextPC := incPC
      else
        if (isJAL) then
          set taken  := Ob~1;
          set nextPC := (pc + imm_val)
        else
          if (isJALR) then
            set taken  := Ob~1;
            set nextPC := ((rs1_val + imm_val) && !|32`d1|)
          else ((
            set taken :=
              match (funct3) with
              | #funct3_BEQ  => (rs1_val == rs2_val)
              | #funct3_BNE  => rs1_val != rs2_val
              | #funct3_BLT  => rs1_val <s rs2_val
              | #funct3_BGE  => !(rs1_val <s rs2_val)
              | #funct3_BLTU => (rs1_val < rs2_val)
              | #funct3_BGEU => !(rs1_val < rs2_val)
              return default: Ob~0
              end
            );
            if (taken) then set nextPC := (pc + imm_val)
            else set nextPC := incPC);
    struct control_result {taken := taken; nextPC := nextPC}
  }}.
End RVHelpers.

Module Type RVParams.
  Parameter NREGS: nat.
  Parameter WIDTH: nat.
  Parameter HAS_SHADOW_STACK: bool.
End RVParams.

Module RVCore (RVP: RVParams) (ShadowStack: ShadowStackInterface).
  Import ListNotations.
  Import RVP.

  Definition mem_req := {|
    struct_name   := "mem_req";
    struct_fields :=
      [("byte_en", bits_t 4); ("addr", bits_t 32); ("data", bits_t 32)]
  |}.

  Definition mem_resp := {|
    struct_name   := "mem_resp";
    struct_fields :=
      [("byte_en", bits_t 4); ("addr", bits_t 32); ("data", bits_t 32)]
  |}.

  Definition fetch_bookkeeping := {|
    struct_name   := "fetch_bookkeeping";
    struct_fields :=
      [("pc", bits_t 32); ("ppc", bits_t 32); ("epoch", bits_t 1)]
  |}.

  Definition decode_bookkeeping := {|
    struct_name   := "decode_bookkeeping";
    struct_fields := [
      ("pc", bits_t 32); ("ppc", bits_t 32); ("epoch", bits_t 1);
      ("dInst", struct_t decoded_sig); ("rval1", bits_t 32);
      ("rval2", bits_t 32)
    ]
  |}.

  Definition execute_bookkeeping := {|
    struct_name   := "execute_bookkeeping";
    struct_fields := [
      ("isUnsigned", bits_t 1); ("size", bits_t 2); ("offset", bits_t 2);
      ("newrd", bits_t 32); ("dInst", struct_t decoded_sig)
    ]
  |}.

  (* Specialize interfaces *)
  Module FifoMemReq <: Fifo.
    Definition T:= struct_t mem_req.
  End FifoMemReq.
  Module MemReq := Fifo1Bypass FifoMemReq.

  Module FifoMemResp <: Fifo.
    Definition T:= struct_t mem_resp.
  End FifoMemResp.
  Module MemResp := Fifo1 FifoMemResp.

  Module FifoUART <: Fifo.
    Definition T:= bits_t 8.
  End FifoUART.
  Module UARTReq  := Fifo1Bypass FifoUART.
  Module UARTResp := Fifo1 FifoUART.

  Module FifoFetch <: Fifo.
    Definition T:= struct_t fetch_bookkeeping.
  End FifoFetch.
  Module fromFetch     := Fifo1 FifoFetch.
  Module waitFromFetch := Fifo1 FifoFetch.

  Module FifoDecode <: Fifo.
    Definition T:= struct_t decode_bookkeeping.
  End FifoDecode.
  Module fromDecode := Fifo1 FifoDecode.

  Module FifoExecute <: Fifo.
    Definition T:= struct_t execute_bookkeeping.
  End FifoExecute.
  Module fromExecute := Fifo1 FifoExecute.

  Module RfParams <: RfPow2_sig.
    Definition idx_sz      := log2 NREGS.
    Definition T           := bits_t 32.
    Definition init        := Bits.zeroes 32.
    Definition read_style  := Scoreboard.read_style 32.
    Definition write_style := Scoreboard.write_style.
  End RfParams.
  Module Rf := RfPow2 RfParams.

  Module ScoreboardParams <: Scoreboard_sig.
    Definition idx_sz   := log2 NREGS.
    Definition maxScore := 3.
  End ScoreboardParams.
  Module Scoreboard := Scoreboard ScoreboardParams.

  (* Declare state *)
  Inductive reg_t :=
  | toIMem (state: MemReq.reg_t)
  | fromIMem (state: MemResp.reg_t)
  | toDMem (state: MemReq.reg_t)
  | fromDMem (state: MemResp.reg_t)
  | f2d (state: fromFetch.reg_t)
  | f2dprim (state: waitFromFetch.reg_t)
  | d2e (state: fromDecode.reg_t)
  | e2w (state: fromExecute.reg_t)
  | rf (state: Rf.reg_t)
  | sstack (state: ShadowStack.reg_t)
  | scoreboard (state: Scoreboard.reg_t)
  | cycle_count
  | instr_count
  | pc
  | epoch
  | sstack_activated
  | on_off
  | halt.

  (* State type *)
  Definition R idx :=
    match idx with
    | toIMem r         => MemReq.R r
    | fromIMem r       => MemResp.R r
    | toDMem r         => MemReq.R r
    | fromDMem r       => MemResp.R r
    | f2d r            => fromFetch.R r
    | f2dprim r        => waitFromFetch.R r
    | d2e r            => fromDecode.R r
    | e2w r            => fromExecute.R r
    | rf r             => Rf.R r
    | scoreboard r     => Scoreboard.R r
    | sstack r         => ShadowStack.R r
    | pc               => bits_t 32
    | cycle_count      => bits_t 32
    | instr_count      => bits_t 32
    | epoch            => bits_t 1
    | sstack_activated => bits_t 1
    | on_off           => bits_t 1
    | halt             => bits_t 1
    end.

  (* Initial values *)
  Definition r idx : R idx :=
    match idx with
    | rf s             => Rf.r s
    | toIMem s         => MemReq.r s
    | fromIMem s       => MemResp.r s
    | toDMem s         => MemReq.r s
    | fromDMem s       => MemResp.r s
    | f2d s            => fromFetch.r s
    | f2dprim s        => waitFromFetch.r s
    | d2e s            => fromDecode.r s
    | e2w s            => fromExecute.r s
    | scoreboard s     => Scoreboard.r s
    | sstack s         => ShadowStack.r s
    | pc               => Bits.zero
    | cycle_count      => Bits.zero
    | instr_count      => Bits.zero
    | epoch            => Bits.zero
    | sstack_activated => if (HAS_SHADOW_STACK) then Bits.one else Bits.zero
    | on_off           => Bits.zero
    | halt             => Bits.zero
    end.

  (* External functions, used to model memory *)
  Inductive memory := imem | dmem.

  Inductive ext_fn_t :=
  (* Send a read or write to memory *)
  | ext_mem (m: memory)
  (* Read from host *)
  | ext_uart_read
  (* Write to host *)
  | ext_uart_write
  (* Set led *)
  | ext_led
  (* Get host id *)
  | ext_host_id
  (* Stop execution *)
  | ext_finish.

  Definition mem_input := {|
    struct_name   := "mem_input";
    struct_fields := [
      ("get_ready", bits_t 1); ("put_valid", bits_t 1);
      ("put_request", struct_t mem_req)
    ]
  |}.

  Definition mem_output := {|
    struct_name   := "mem_output";
    struct_fields := [
      ("get_valid", bits_t 1); ("put_ready", bits_t 1);
      ("get_response", struct_t mem_resp)
    ]
  |}.

  Definition uart_input   := maybe (bits_t 8).
  Definition uart_output  := maybe (bits_t 8).
  Definition led_input    := maybe (bits_t 1).
  Definition finish_input := maybe (bits_t 8).

  Definition host_id :=
    {| enum_name        := "hostID";
       enum_members     := ["FPGA"; "NoHost"; "Verilator"; "Cuttlesim"];
       enum_bitpatterns := vect_map (Bits.of_nat 8) [128; 8; 1; 0]
    |}%vect.

  Definition Sigma (fn: ext_fn_t) :=
    match fn with
    | ext_mem _      => {$ struct_t mem_input ~> struct_t mem_output $}
    | ext_uart_read  => {$ bits_t 1 ~> uart_output $}
    | ext_uart_write => {$ uart_input ~> bits_t 1 $}
    | ext_led        => {$ led_input ~> bits_t 1 $}
    | ext_host_id    => {$ bits_t 1 ~> enum_t host_id $}
    | ext_finish     => {$ finish_input ~> bits_t 1 $}
    end.

  Definition update_on_off : uaction reg_t ext_fn_t := {{
    write1(on_off, read0(on_off)+Ob~1)
  }}.

  Definition end_execution : uaction reg_t ext_fn_t := {{
    let res := extcall ext_finish (struct (Maybe (bits_t 8)) {
      valid := read0(halt); data := |8`d1|
    }) in pass
  }}.

  Definition fetch : uaction reg_t ext_fn_t := {{
    if (read0(halt) == Ob~1) then fail else pass;
    let pc  := read1(pc) in
    let req := struct mem_req {
      byte_en := |4`d0|; (* Load *)
      addr    := pc;
      data    := |32`d0|
    } in
    let fetch_bookkeeping := struct fetch_bookkeeping {
      pc    := pc;
      ppc   := pc + |32`d4|;
      epoch := read1(epoch)
    } in
    toIMem.(MemReq.enq)(req);
    write1(pc, pc + |32`d4|);
    f2d.(fromFetch.enq)(fetch_bookkeeping)
  }}.

  Definition wait_imem : uaction reg_t ext_fn_t := {{
    if (read0(halt) == Ob~1) then fail else pass;
    let fetched_bookkeeping := f2d.(fromFetch.deq)() in
    f2dprim.(waitFromFetch.enq)(fetched_bookkeeping)
  }}.

  Definition sliceReg : UInternalFunction reg_t empty_ext_fn_t := {{
    fun sliceReg (idx: bits_t 5) : bits_t (log2 NREGS) =>
      idx[|3`d0| :+ log2 NREGS]
  }}.

  (* This rule is interesting because maybe we want to write it differently than
     Bluespec if we care about simulation performance. Moreover, we could read
     unconditionally to avoid potential muxing on the input, TODO check if it
     changes anything. *)
  Definition decode
    `{finite_reg: FiniteType reg_t}
    `{finite_reg_sstack: FiniteType ShadowStack.reg_t}
  : uaction reg_t ext_fn_t := {{
    if (read0(halt) == Ob~1) then fail else pass;
    let instr               := fromIMem.(MemResp.deq)() in
    let instr               := get(instr,data) in
    let fetched_bookkeeping := f2dprim.(waitFromFetch.deq)() in
    let decodedInst         := decode_fun(instr) in
    when (get(fetched_bookkeeping, epoch) == read1(epoch)) do (
      let rs1_idx := get(getFields(instr), rs1) in
      let rs2_idx := get(getFields(instr), rs2) in
      let score1  := scoreboard.(Scoreboard.search)(sliceReg(rs1_idx)) in
      let score2  := scoreboard.(Scoreboard.search)(sliceReg(rs2_idx)) in
      guard (score1 == Ob~0~0 && score2 == Ob~0~0);
      (
        when (get(decodedInst, valid_rd)) do
          let rd_idx := get(getFields(instr), rd) in
          scoreboard.(Scoreboard.insert)(sliceReg(rd_idx))
      );
      let rs1 := rf.(Rf.read_1)(sliceReg(rs1_idx)) in
      let rs2 := rf.(Rf.read_1)(sliceReg(rs2_idx)) in
      let decode_bookkeeping := struct decode_bookkeeping {
        pc    := get(fetched_bookkeeping, pc);
        ppc   := get(fetched_bookkeeping, ppc);
        epoch := get(fetched_bookkeeping, epoch);
        dInst := decodedInst;
        rval1 := rs1;
        rval2 := rs2
      } in
      d2e.(fromDecode.enq)(decode_bookkeeping)
    )
  }}.

  (* Useful for debugging *)
  Arguments Var {pos_t var_t fn_name_t reg_t ext_fn_t R Sigma sig} k {tau m}
  : assert.

  Definition isMemoryInst : UInternalFunction reg_t empty_ext_fn_t := {{
    fun isMemoryInst (dInst: struct_t decoded_sig) : bits_t 1 =>
      (get(dInst,inst)[|5`d6|] == Ob~0)
      && (get(dInst,inst)[|5`d3| :+ 2] == Ob~0~0)
  }}.

  Definition isControlInst : UInternalFunction reg_t empty_ext_fn_t := {{
    fun isControlInst (dInst: struct_t decoded_sig) : bits_t 1 =>
      get(dInst,inst)[|5`d4| :+ 3] == Ob~1~1~0
  }}.

  Definition isJALXInst : UInternalFunction reg_t empty_ext_fn_t := {{
    fun isJALXInst (dInst : struct_t decoded_sig) : bits_t 1 =>
      get(dInst, inst)[|5`d4| :+ 3] == Ob~1~1~0
      && get(dInst, inst)[|5`d0| :+ 3] == Ob~1~1~1
  }}.

  Definition execute_1
    `{finite_reg: FiniteType reg_t}
    `{finite_reg_sstack: FiniteType ShadowStack.reg_t}
  : uaction reg_t ext_fn_t := {{(
    let fInst      := get(dInst, inst) in
    let funct3     := get(getFields(fInst), funct3) in
    let rd_val     := get(dInst, inst)[|5`d7| :+ 5] in
    let rs1_val    := get(decoded_bookkeeping, rval1) in
    let rs2_val    := get(decoded_bookkeeping, rval2) in
    let imm        := getImmediate(dInst) in
    let pc         := get(decoded_bookkeeping, pc) in
    let data       := execALU32(fInst, rs1_val, rs2_val, imm, pc) in
    let isUnsigned := Ob~0 in
    let size       := funct3[|2`d0| :+ 2] in
    let addr       := rs1_val + imm in (* ((rs1_val + imm) && !|32`d1|) in *)
    let offset     := addr[|5`d0| :+ 2] in
    if isMemoryInst(dInst) then
      let shift_amount := offset ++ |3`d0| in
      let is_write     := fInst[|5`d5|] == Ob~1 in
      let byte_en      :=
        if is_write then
          match size with
          | Ob~0~0 => Ob~0~0~0~1
          | Ob~0~1 => Ob~0~0~1~1
          | Ob~1~0 => Ob~1~1~1~1
          return default: fail(4)
          end << offset
        else Ob~0~0~0~0 in
      set data       := rs2_val << shift_amount;
      set addr       := addr[|5`d2| :+ 30] ++ |2`d0|;
      set isUnsigned := funct3[|2`d2|];
      toDMem.(MemReq.enq)(struct mem_req {
        byte_en := byte_en; addr := addr; data := data
      })
    else if (isControlInst(dInst)) then
      (* See table 2.1. of the unprivileged ISA specification for details *)
      set data := (pc + |32`d4|); (* For jump and link *)
      let has_sstack := read0(sstack_activated) in
      if (has_sstack) then (
        let res := Ob~0 in
        let rs1 := get(dInst, inst)[|5`d15| :+ 5] in
        (
          if ((get(dInst, inst)[|5`d0| :+ 7] == Ob~1~1~0~1~1~1~1) (* JAL with rd = x1 (ra) or x5 (t0) *)
            && (rd_val == |5`d1| || rd_val == |5`d5|))
          then set res := sstack.(ShadowStack.push)(data)
          else if (get(dInst, inst)[|5`d0| :+ 7] == Ob~1~1~0~0~1~1~1) then ( (* JALR *)
            if (rd_val == |5`d1| || rd_val == |5`d5|) then
              if (rd_val == rs1 || (rs1 != |5`d1| && rs1 != |5`d5|)) then (
                set res := sstack.(ShadowStack.push)(data)
              ) else (
                set res := sstack.(ShadowStack.pop)(addr);
                set res := res || sstack.(ShadowStack.push)(data)
              )
            else if (rs1 == |5`d1| || rs1 == |5`d5|) then
              set res := sstack.(ShadowStack.pop)(addr)
            else pass
          )
          else pass
        );
        write0(halt, res)
      )
      else pass
    else pass;
    let controlResult := execControl32(fInst, rs1_val, rs2_val, imm, pc) in
    let nextPc        := get(controlResult,nextPC) in
    if nextPc != get(decoded_bookkeeping, ppc) then
      write0(epoch, read0(epoch)+Ob~1);
      write0(pc, nextPc)
    else
      pass;
    let execute_bookkeeping := struct execute_bookkeeping {
      isUnsigned := isUnsigned;
      size       := size;
      offset     := offset;
      newrd      := data;
      dInst      := get(decoded_bookkeeping, dInst)
    } in
    e2w.(fromExecute.enq)(execute_bookkeeping)
  )}}.

  Definition execute
    `{finite_reg: FiniteType reg_t}
    `{finite_reg_sstack: FiniteType ShadowStack.reg_t}
  : uaction reg_t ext_fn_t := {{
    if (read0(halt) == Ob~1) then fail else pass;
    let decoded_bookkeeping := d2e.(fromDecode.deq)() in
    if get(decoded_bookkeeping, epoch) == read0(epoch) then
      (* By then we guarantee that this instruction is correct-path *)
      let dInst := get(decoded_bookkeeping, dInst) in
      if get(dInst, legal) == Ob~0 then
        (* Always say that we had a misprediction in this case for simplicity *)
        write0(epoch, read0(epoch)+Ob~1);
        write0(pc, |32`d0|)
      else ( ` execute_1 ` )
    else
      pass
  }}.

  Definition writeback
    `{finite_reg: FiniteType reg_t}
    `{finite_reg_sstack: FiniteType ShadowStack.reg_t}
  : uaction reg_t ext_fn_t := {{
    if (read0(halt) == Ob~1) then fail else pass;
    let execute_bookkeeping := e2w.(fromExecute.deq)() in
    let dInst               := get(execute_bookkeeping, dInst) in
    let data                := get(execute_bookkeeping, newrd) in
    let fields              := getFields(get(dInst, inst)) in
    write0(instr_count, read0(instr_count)+|32`d1|);
    if isMemoryInst(dInst) then (* Write_val *)
      (* Byte enable shifting back *)
      let resp     := fromDMem.(MemResp.deq)() in
      let mem_data := get(resp,data) in
      set mem_data := mem_data >> (get(execute_bookkeeping,offset) ++ Ob~0~0~0);
      match (
        get(execute_bookkeeping,isUnsigned)++get(execute_bookkeeping,size)
      ) with
      | Ob~0~0~0 => set data := {signExtend 8  24}(mem_data[|5`d0| :+ 8])
      | Ob~0~0~1 => set data := {signExtend 16 16}(mem_data[|5`d0| :+ 16])
      | Ob~1~0~0 => set data := zeroExtend(mem_data[|5`d0| :+ 8],32)
      | Ob~1~0~1 => set data := zeroExtend(mem_data[|5`d0| :+ 16],32)
      | Ob~0~1~0 => set data := mem_data (* Load Word *)
      return default: fail (* Load Double or Signed Word *)
      end
    else pass;
    if get(dInst, valid_rd) then
      let rd_idx := get(fields, rd) in
      scoreboard.(Scoreboard.remove)(sliceReg(rd_idx));
      if (rd_idx == |5`d0|) then pass
      else rf.(Rf.write_0)(sliceReg(rd_idx), data)
    else pass
  }}.

  Definition MMIO_UART_ADDRESS :=
    Ob~0~1~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0.
  Definition MMIO_LED_ADDRESS :=
    Ob~0~1~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~1~0~0.
  Definition MMIO_EXIT_ADDRESS :=
    Ob~0~1~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~1~0~0~0~0~0~0~0~0~0~0~0~0.
  Definition MMIO_HOST_ID_ADDRESS :=
    Ob~0~1~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~1~0~0~0~0~0~0~0~0~0~1~0~0.

  Definition memoryBus (m: memory) : UInternalFunction reg_t ext_fn_t := {{
    fun memoryBus (get_ready: bits_t 1) (put_valid: bits_t 1)
      (put_request: struct_t mem_req) : struct_t mem_output
    =>
      `match m with
      | imem => {{
          extcall (ext_mem m) (struct mem_input {
            get_ready   := get_ready;
            put_valid   := put_valid;
            put_request := put_request
          })
        }}
      | dmem => {{
        let addr     := get(put_request, addr) in
        let byte_en  := get(put_request, byte_en) in
        let is_write := byte_en == Ob~1~1~1~1 in

        let is_uart       := addr == #MMIO_UART_ADDRESS in
        let is_uart_read  := is_uart && !is_write in
        let is_uart_write := is_uart && is_write in

        let is_led       := addr == #MMIO_LED_ADDRESS in
        let is_led_write := is_led && is_write in

        let is_finish       := addr == #MMIO_EXIT_ADDRESS in
        let is_finish_write := is_finish && is_write in

        let is_host_id := addr == #MMIO_HOST_ID_ADDRESS in
        let is_host_id_read := is_host_id && !is_write in

        let is_mem := !is_uart && !is_led && !is_finish && !is_host_id in

        if is_uart_write then
          let char    := get(put_request, data)[|5`d0| :+ 8] in
          let may_run := get_ready && put_valid && is_uart_write in
          let ready   := extcall ext_uart_write (struct (Maybe (bits_t 8)) {
            valid := may_run; data := char
          }) in
          struct mem_output {
            get_valid    := may_run && ready;
            put_ready    := may_run && ready;
            get_response := struct mem_resp {
              byte_en := byte_en; addr := addr; data := |32`d0|
            }
          }
        else if is_uart_read then
          let may_run  := get_ready && put_valid && is_uart_read in
          let opt_char := extcall ext_uart_read (may_run) in
          let ready    := get(opt_char, valid) in
          struct mem_output {
            get_valid    := may_run && ready;
            put_ready    := may_run && ready;
            get_response := struct mem_resp {
              byte_en := byte_en; addr := addr;
              data := zeroExtend(get(opt_char, data), 32)
            }
          }
        else if is_led then
          let on      := get(put_request, data)[|5`d0|] in
          let may_run := get_ready && put_valid && is_led_write in
          let current := extcall ext_led (struct (Maybe (bits_t 1)) {
            valid := may_run; data := on
          }) in
          let ready := Ob~1 in
          struct mem_output {
            get_valid    := may_run && ready;
            put_ready    := may_run && ready;
            get_response := struct mem_resp {
              byte_en := byte_en;
              addr    := addr;
              data    := zeroExtend(current, 32)
            }
          }
        else if is_finish then
          let char     := get(put_request, data)[|5`d0| :+ 8] in
          let may_run  := get_ready && put_valid && is_finish_write in
          let response := extcall ext_finish (struct (Maybe (bits_t 8)) {
            valid := may_run; data := char
          }) in
          let ready := Ob~1 in
          struct mem_output {
            get_valid    := may_run && ready;
            put_ready    := may_run && ready;
            get_response := struct mem_resp {
              byte_en := byte_en; addr := addr; data := zeroExtend(response, 32)
            }
          }
        else if is_host_id then
          let may_run := get_ready && put_valid && is_host_id_read in
          let response := pack(extcall ext_host_id (Ob~1)) in
          let ready := Ob~1 in
          struct mem_output {
            get_valid := may_run && ready;
            put_ready := may_run && ready;
            get_response := struct mem_resp {
              byte_en := byte_en; addr := addr; data := zeroExtend(response, 32)
            }
          }
        else
          extcall (ext_mem m) (struct mem_input {
            get_ready   := get_ready && is_mem;
            put_valid   := put_valid && is_mem;
            put_request := put_request
          })
      }}
      end`
  }}.

  Definition mem
    (m: memory) `{finite_reg: FiniteType reg_t}
    `{finite_reg_sstack: FiniteType ShadowStack.reg_t}
  : uaction reg_t ext_fn_t :=
    let fromMem :=
      match m with
      | imem => fromIMem
      | dmem => fromDMem
      end
    in
    let toMem :=
      match m with
      | imem => toIMem
      | dmem => toDMem
      end
    in
    {{
      if (read0(halt) == Ob~1) then fail else pass;
      let get_ready       := fromMem.(MemResp.can_enq)() in
      let put_request_opt := toMem.(MemReq.peek)() in
      let put_request     := get(put_request_opt, data) in
      let put_valid       := get(put_request_opt, valid) in
      let mem_out := {memoryBus m}(get_ready, put_valid, put_request) in (
        when (get_ready && get(mem_out, get_valid)) do
          fromMem.(MemResp.enq)(get(mem_out, get_response))
      );
      (
        when (put_valid && get(mem_out, put_ready)) do
          ignore(toMem.(MemReq.deq)())
      )
    }}.

  Definition tick : uaction reg_t ext_fn_t := {{
    if (read0(halt) == Ob~1) then fail else pass;
    write0(cycle_count, read0(cycle_count) + |32`d1|)
  }}.

  Existing Instance ShadowStack.Show_reg_t.
  Instance Show_reg_t : Show reg_t := _.
  Instance Show_ext_fn_t : Show ext_fn_t := _.

  Definition rv_ext_fn_sim_specs fn := {|
    efs_name := show fn;
    efs_method :=
      match fn with
      | ext_finish => true
      | _          => false
      end
  |}.

  Definition rv_ext_fn_rtl_specs fn := {|
    efr_name     := show fn;
    efr_internal :=
      match fn with
      | ext_host_id | ext_finish => true
      | _ => false
      end
  |}.
End RVCore.

Inductive rv_rules_t :=
| Fetch
| Decode
| Execute
| Writeback
| WaitImem
| Imem
| Dmem
| Tick
| UpdateOnOff
| EndExecution.

Definition rv_external (rl: rv_rules_t) := false.

Module Type Core.
  Parameter _reg_t              : Type.
  Parameter _ext_fn_t           : Type.
  Parameter R                   : _reg_t -> type.
  Parameter Sigma               : _ext_fn_t -> ExternalSignature.
  Parameter r                   : forall reg, R reg.
  Parameter rv_rules            : rv_rules_t -> rule R Sigma.
  Parameter FiniteType_reg_t    : FiniteType _reg_t.
  Parameter Show_reg_t          : Show _reg_t.
  Parameter Show_ext_fn_t       : Show _ext_fn_t.
  Parameter rv_ext_fn_sim_specs : _ext_fn_t -> ext_fn_sim_spec.
  Parameter rv_ext_fn_rtl_specs : _ext_fn_t -> ext_fn_rtl_spec.
End Core.
