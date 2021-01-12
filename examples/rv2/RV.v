Require Import Koika.Frontend.
Require Import Koika.Std.

Require Import ISA.
Require Import Instructions.

Section RVHelpers.
  Context {reg_t : Type}.

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

  Definition inst_field := {|
    struct_name   := "instFields";
    struct_fields := ("opcode", bits_t 7) :: ("funct3", bits_t 3) :: nil
  |}.

  Definition getFields : UInternalFunction reg_t empty_ext_fn_t := {{
    fun getFields (inst : bits_t 32) : struct_t inst_field =>
      struct inst_field {
        opcode := inst[|5`d0 | :+ 7];
        funct3 := inst[|5`d12| :+ 3]
      }
  }}.
End RVHelpers.

Module Type RVParameters.
  Parameter REGISTERS_COUNT : nat.
  Parameter REGISTERS_WIDTH : nat.
End RVParameters.

Module RV (Parameters : RVParameters).
  Import Parameters.

  Definition mem_req := {|
    struct_name   := "mem_req";
    struct_fields := [
      ("byte_en", bits_t 4); ("addr", bits_t 32); ("data", bits_t 32)
    ]
  |}.

  Definition mem_resp := {|
    struct_name   := "mem_resp";
    struct_fields := [
      ("byte_en", bits_t 4); ("addr", bits_t 32); ("data", bits_t 32)
    ]
  |}.

  Definition fetch_bookkeeping := {|
    struct_name   := "fetch_bookkeeping";
    struct_fields := [
      ("pc", bits_t 32); ("ppc", bits_t 32); ("epoch", bits_t 1)
    ]
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
    Definition T := struct_t mem_req.
  End FifoMemReq.
  Module MemReq := Fifo1Bypass FifoMemReq.

  Module FifoMemResp <: Fifo.
    Definition T := struct_t mem_resp.
  End FifoMemResp.
  Module MemResp := Fifo1 FifoMemResp.

  Module FifoUART <: Fifo.
    Definition T := bits_t 8.
  End FifoUART.
  Module UARTReq  := Fifo1Bypass FifoUART.
  Module UARTResp := Fifo1 FifoUART.

  Module FifoFetch <: Fifo.
    Definition T := struct_t fetch_bookkeeping.
  End FifoFetch.
  Module fromFetch     := Fifo1 FifoFetch.
  Module waitFromFetch := Fifo1 FifoFetch.

  Module FifoDecode <: Fifo.
    Definition T := struct_t decode_bookkeeping.
  End FifoDecode.
  Module fromDecode := Fifo1 FifoDecode.

  Module FifoExecute <: Fifo.
    Definition T := struct_t execute_bookkeeping.
  End FifoExecute.
  Module fromExecute := Fifo1 FifoExecute.

  Module RfParams <: RfPow2_sig.
    Definition idx_sz      := log2 REGISTERS_COUNT.
    Definition T           := bits_t 32.
    Definition init        := Bits.zeroes 32.
    Definition read_style  := Scoreboard.read_style 32.
    Definition write_style := Scoreboard.write_style.
  End RfParams.
  Module Rf := RfPow2 RfParams.

  (* State *)
  Inductive reg_t :=
  | toIMem   (state : MemReq.reg_t       )
  | fromIMem (state : MemResp.reg_t      )
  | toDMem   (state : MemReq.reg_t       )
  | fromDMem (state : MemResp.reg_t      )
  | f2d      (state : fromFetch.reg_t    )
  | f2dprim  (state : waitFromFetch.reg_t)
  | d2e      (state : fromDecode.reg_t   )
  | e2w      (state : fromExecute.reg_t  )
  | rf       (state : Rf.reg_t           )
  | cycle_count
  | instr_count
  | pc
  | epoch.

  (* State type *)
  Definition R idx :=
    match idx with
    | toIMem    r => MemReq.R        r
    | fromIMem  r => MemResp.R       r
    | toDMem    r => MemReq.R        r
    | fromDMem  r => MemResp.R       r
    | f2d       r => fromFetch.R     r
    | f2dprim   r => waitFromFetch.R r
    | d2e       r => fromDecode.R    r
    | e2w       r => fromExecute.R   r
    | rf        r => Rf.R            r
    | pc          => bits_t 32
    | cycle_count => bits_t 32
    | instr_count => bits_t 32
    | epoch       => bits_t 1
    end.

  (* Initial values *)
  Definition r idx : R idx :=
    match idx with
    | rf        s => Rf.r            s
    | toIMem    s => MemReq.r        s
    | fromIMem  s => MemResp.r       s
    | toDMem    s => MemReq.r        s
    | fromDMem  s => MemResp.r       s
    | f2d       s => fromFetch.r     s
    | f2dprim   s => waitFromFetch.r s
    | d2e       s => fromDecode.r    s
    | e2w       s => fromExecute.r   s
    | pc          => Bits.zero
    | cycle_count => Bits.zero
    | instr_count => Bits.zero
    | epoch       => Bits.zero
    end.

  (* External functions, used to model memory *)
  Inductive memory := imem | dmem.
End RV.

Module Type Core.
  Parameter _reg_t              : Type.
  Parameter _ext_fn_t           : Type.
  Parameter R                   : _reg_t -> type. (* State *)
  Parameter Sigma               : _ext_fn_t -> ExternalSignature.
  Parameter r                   : forall reg, R reg. (* Initial state *)
  Parameter rv_rules            : rv_rules_t -> rule R Sigma.
  Parameter FiniteType_reg_t    : FiniteType _reg_t.
  Parameter Show_reg_t          : Show _reg_t.
  Parameter Show_ext_fn_t       : Show _ext_fn_t.
  Parameter rv_ext_fn_sim_specs : _ext_fn_t -> ext_fn_sim_spec.
  Parameter rv_ext_fn_rtl_specs : _ext_fn_t -> ext_fn_rtl_spec.
End Core.
