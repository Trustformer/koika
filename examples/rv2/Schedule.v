(*! Definition of a pipelined schedule !*)

Require Import Koika.Frontend.
(* Require Import RV. *)

Inductive rv_rules_t :=
| Fetch | Decode | Execute | Writeback | WaitImem | Imem | Dmem | StepMultiplier
| Tick.

Definition fetch : uaction reg_t ext_fn_t := {{
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

(* This rule is interesting because maybe we want to write it differently than
   Bluespec if we care about simulation performance. Moreover, we could read
   unconditionally to avoid potential muxing on the input.
   TODO Check if it changes anything.
*)
Definition decode : uaction reg_t ext_fn_t := {{
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

Definition execute : uaction reg_t ext_fn_t := {{
  let decoded_bookkeeping := d2e.(fromDecode.deq)() in
  if get(decoded_bookkeeping, epoch) == read0(epoch) then
    (* By then we guarantee that this instruction is correct-path *)
    let dInst := get(decoded_bookkeeping, dInst) in
    if get(dInst, legal) == Ob~0 then
      (* Always say that we had a misprediction in this case for simplicity *)
      write0(epoch, read0(epoch)+Ob~1);
      write0(pc, |32`d0|)
    else (
      let fInst      := get(dInst, inst) in
      let funct3     := get(getFields(fInst), funct3) in
      let rs1_val    := get(decoded_bookkeeping, rval1) in
      let rs2_val    := get(decoded_bookkeeping, rval2) in
      (* Use the multiplier module or the ALU *)
      let imm        := getImmediate(dInst) in
      let pc         := get(decoded_bookkeeping, pc) in
      let data       := execALU32(fInst, rs1_val, rs2_val, imm, pc) in
      let isUnsigned := Ob~0 in
      let size       := funct3[|2`d0| :+ 2] in
      let addr       := rs1_val + imm in
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
        set addr       := addr[|5`d2| :+ 30 ] ++ |2`d0|;
        set isUnsigned := funct3[|2`d2|];
        toDMem.(MemReq.enq)(struct mem_req {
          byte_en := byte_en; addr := addr; data := data
        })
      else if (isControlInst(dInst)) then
        set data := (pc + |32`d4|) (* For jump and link *)
      else if (isMultiplyInst(dInst)) then
        mulState.(Multiplier.enq)(rs1_val, rs2_val)
      else
        pass;
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
    )
  else
    pass
}}.

Definition writeback : uaction reg_t ext_fn_t := {{
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
  else if isMultiplyInst(dInst) then
    set data := mulState.(Multiplier.deq)()[|6`d0| :+ 32]
  else
    pass;
  if get(dInst,valid_rd) then
    let rd_idx := get(fields, rd) in
    scoreboard.(Scoreboard.remove)(sliceReg(rd_idx));
    if (rd_idx == |5`d0|) then
      pass
    else
      rf.(Rf.write_0)(sliceReg(rd_idx), data)
  else
    pass
}}.

Definition wait_imem : uaction reg_t ext_fn_t := {{
  let fetched_bookkeeping := f2d.(fromFetch.deq)() in
  f2dprim.(waitFromFetch.enq)(fetched_bookkeeping)
}}.

Definition rv_schedule : scheduler :=
  Writeback |> Execute |> StepMultiplier |> Decode |> WaitImem |> Fetch |> Imem
    |> Dmem |> Tick    |> done.

Module Package (C : RV).
  Import C.
  Existing Instance Show_reg_t.
  Existing Instance Show_ext_fn_t.
  Existing Instance FiniteType_reg_t.

  Definition circuits :=
    compile_scheduler rv_rules rv_external rv_schedule.

  Definition koika_package := {|
    koika_reg_types     := R;
    koika_reg_init      := r;
    koika_ext_fn_types  := Sigma;
    koika_rules         := rv_rules;
    koika_rule_external := rv_external;
    koika_scheduler     := rv_schedule;
    koika_module_name   := "RV"
  |}.

  Definition package := {|
    ip_koika := koika_package;
    ip_sim   := {|
      sp_ext_fn_specs := rv_ext_fn_sim_specs;
      sp_prelude      := None
    |};
    ip_verilog := {| vp_ext_fn_specs := rv_ext_fn_rtl_specs |}
  |}.
End Package.
