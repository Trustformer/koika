(*! Proofs about our RISC-V implementation !*)
Require Import Coq.Program.Equality.
Require Import Koika.Frontend.
Require Export rv.Decode rv.Instructions rv.ShadowStack rv.RVCore rv.rv32
  rv.rv32i.
Require Import Koika.SimpleForm.SimpleForm.
Require Import Koika.SimpleForm.Interpretation.
Require Import Koika.SimpleForm.Operations.
Require Import Koika.SimpleForm.Tactics.
Require Import Koika.KoikaForm.Desugaring.DesugaredSyntax.
Require Import Koika.BitsToLists.
Require Import Koika.KoikaForm.SimpleVal.


Definition drules rule :=
  match uaction_to_daction (desugar_action tt (RV32I.rv_urules rule)) with
  | Some d => d
  | None => DFail unit_t
  end.

#[local]
  Instance eq_dec_reg: EqDec RV32I.reg_t := EqDec_FiniteType.

Definition ext_Sigma := RV32I.Sigma.

Definition sf :=
  schedule_to_simple_form RV32I.R (Sigma := ext_Sigma) drules rv_schedule.

Definition sact := sact (reg_t:=RV32I.reg_t) (ext_fn_t:=RV32I.ext_fn_t).

Definition and : sact -> sact -> sact := SBinop (UBits2 UAnd).
Definition or : sact -> sact -> sact := SBinop (UBits2 UOr).
Definition add : sact -> sact -> sact := SBinop (UBits2 UPlus).
Definition equal : sact -> sact -> sact := SBinop (UEq false).
Definition neq : sact -> sact -> sact := SBinop (UEq true).
Definition eqb a b := equal a (SConst (Bits b)).
Definition neqb a b := neq a (SConst (Bits b)).
Definition gf f a : sact := SUnop (UStruct1 (UGetField f)) a.
Definition not : sact -> sact := SUnop (UBits1 UNot).

Definition andl :=  fun l => List.fold_left (fun acc elt => and acc elt) l (SConst (Bits [true])).

Definition sact_nomispred : sact :=
  equal (gf "epoch" (SReg (RV32I.d2e RV32I.fromDecode.data0))) (SReg RV32I.epoch).

Definition sact_sstack_empty : sact :=
  equal (SReg (RV32I.sstack RV32I.ShadowStack.size))
    (SConst (@val_of_value
               (bits_t RV32I.ShadowStack.index_sz)
               (Bits.of_nat (RV32I.ShadowStack.index_sz) 0))).

Definition sact_sstack_full : sact :=
  equal
    (SReg (RV32I.sstack (RV32I.ShadowStack.size)))
    (SConst (@val_of_value
               (bits_t RV32I.ShadowStack.index_sz)
               (Bits.of_nat (RV32I.ShadowStack.index_sz) RV32I.ShadowStack.capacity))).

Definition sact_is_call_instruction instr : sact :=
  let opcode_ctrl := SUnop (UBits1 (USlice 4 3)) instr in
  let opcode_rest := SUnop (UBits1 (USlice 0 4)) instr in
  let rs1 := SUnop (UBits1 (USlice 15 5)) instr in
  let rd := SUnop (UBits1 (USlice 7 5)) instr in
  and (equal opcode_ctrl (SConst (Bits (rev [true; true; false]))))
    (or
       (and (equal opcode_rest (SConst (Bits (rev [true; true; true; true]))))
          (or (equal rd (SConst (Bits (rev [false; false; false; false; true]))))
             (equal rd (SConst (Bits (rev [false; false; true; false; true])))))
       )
       (and (equal opcode_rest (SConst (Bits (rev [false; true; true; true]))))
          (or (equal rd (SConst (Bits (rev [false; false; false; false; true]))))
             (equal rd (SConst (Bits (rev [false; false; true; false; true])))))
       )
    ).

Definition uid s a : sact := SUnop (UConv (UId s)) a.

Definition sact_return_address : sact :=
  let data := SReg (RV32I.d2e RV32I.fromDecode.data0) in
  let rs1 := gf "rval1" data in
  let dInst := gf "dInst" data in
  let inst := gf "inst" dInst in
  let imm := uid "imm_sra" (SUnop (UBits1 (USlice 20 12)) inst) in
  and (add rs1 (SUnop (UBits1 (USExt 32)) imm))
    (not (SConst (Bits (vect_to_list (Bits.of_N 32 1))))).

Definition consistent_imm_type: sact :=
  let dInstr := (gf "dInst" (SReg (RV32I.d2e RV32I.fromDecode.data0))) in
  let instr := gf "inst" dInstr in
  let immt := gf "immediateType" dInstr in
  let opcode_ctrl := SUnop (UBits1 (USlice 4 3)) instr in
  let opcode_rest := SUnop (UBits1 (USlice 0 4)) instr in
  let impl p q := or (not p) q in
  let is_immI :=
    and (eqb (gf "valid" immt) [true])
      (eqb (gf "data" immt) [false; false; false]) in
  let is_jalr :=
    and (eqb opcode_ctrl ( rev [true; true; false]))
      (eqb opcode_rest ( rev [false; true; true; true])) in
  impl is_jalr is_immI.


Fixpoint switch (discr: sact) (branches: list (sact * sact)) (default: sact) : sact :=
  match branches with
  | [] => default
  | (exp,act)::r =>
      SIf (equal discr exp) act (switch discr r default)
  end.

Lemma switch_wt:
  let wt :=       wt_sact RV32I.R (Sigma:=ext_Sigma) (vars sf) in
  forall t1 t2 discr branches default,
    wt discr t1 ->
    Forall (fun '(a,b) => wt a t1 /\ wt b t2) branches ->
    wt default t2 ->
    wt (switch discr branches default) t2.
Proof.
  induction 2; simpl; intros; eauto.
  destr_in H0. subst.
  econstructor. econstructor. eauto. apply H0. constructor. apply H0. apply IHForall. auto.
Qed.

Definition idx_switch n sz (discr: sact) (bodies: index sz -> sact) default :=
  let branches := List.map (fun idx =>
                              (SConst (Bits (vect_to_list (Bits.of_index n idx))), bodies idx))
                    (vect_to_list (all_indices _)) in
  switch discr branches (* (SConst (Bits (repeat false sz))) *) default.


Lemma idx_switch_wt:
  let wt :=       wt_sact RV32I.R (Sigma:=ext_Sigma) (vars sf) in
  forall n sz t2 discr branches default,
    wt discr (bits_t n) ->
    (forall idx, wt (branches idx) t2) ->
    wt default t2 ->
    wt (idx_switch n sz discr branches default) t2.
Proof.
  intros. eapply switch_wt. apply H.
  rewrite Forall_forall. intros (k,v).
  rewrite in_map_iff. intros (idx & EQ & IN). inv EQ.
  split; auto.
  2: apply H0.
  constructor. constructor. rewrite vect_to_list_length. auto.
  apply H1.
Qed.

Definition sact_sstack_top_address : sact :=
  let idx_raw := SBinop (UBits2 UMinus) (SReg ((RV32I.sstack RV32I.ShadowStack.size)))
                   (SConst (Bits (vect_to_list (Bits.of_N (log2 (RV32I.ShadowStack.capacity + 1)) 1)))) in
  idx_switch (log2 (RV32I.ShadowStack.capacity + 1)) _ idx_raw (fun idx => SReg ((RV32I.sstack (RV32I.ShadowStack.stack idx))))
    (SConst (Bits (repeat false 32))).

Definition sact_is_ret_instruction instr : sact :=
  let opcode_ctrl := SUnop (UBits1 (USlice 4 3)) instr in
  let opcode_rest := SUnop (UBits1 (USlice 0 4)) instr in
  let rs1 := SUnop (UBits1 (USlice 15 5)) instr in
  let rd := SUnop (UBits1 (USlice 7 5)) instr in
  and (eqb opcode_ctrl (rev [true; true; false]))
    (and (eqb opcode_rest (rev [false; true; true; true]))
       (or
          (and
             (or (eqb rd (rev [false; false; false; false; true]))
                (eqb rd (rev [false; false; true; false; true])))
             (and
                (neq rd rs1)
                (or
                   (eqb rs1 (rev [false; false; false; false; true]))
                   (eqb rs1 (rev [false; false; true; false; true]))))
          )
          (and
             (and (neqb rd (rev [false; false; false; false; true]))
                (neqb rd (rev [false; false; true; false; true])))
             (or
                (eqb rs1 (rev [false; false; false; false; true]))
                (eqb rs1 (rev [false; false; true; false; true])))
          )
    )).

Definition sact_sstack_push : sact :=
  let str := SReg (RV32I.d2e RV32I.fromDecode.data0) in
  let dInst := gf "dInst" str in
  let inst := gf "inst" dInst in
  sact_is_call_instruction inst.

Definition sact_sstack_pop : sact :=
  let str := SReg (RV32I.d2e RV32I.fromDecode.data0) in
  let dInst := gf "dInst" str in
  let inst := gf "inst" dInst in
  sact_is_ret_instruction inst.

Definition sact_sstack_underflow : sact :=
  let v2 := (gf "dInst" (SReg (RV32I.d2e RV32I.fromDecode.data0))) in
  let l := [
      sact_nomispred;
      sact_sstack_empty;
      sact_sstack_pop;
      eqb (SReg RV32I.sstack_activated) ( [true]);
      eqb (SReg RV32I.halt) ( [false]);
      eqb (SReg (RV32I.d2e RV32I.fromDecode.valid0)) ([true]);
      eqb (gf "legal" v2) ( [true]);
      eqb (SReg (RV32I.e2w RV32I.fromExecute.valid0)) ( [false])
    ] in
  List.fold_left (fun acc elt => and acc elt) l (SConst (Bits [true])).


Definition sact_sstack_overflow : sact :=
  let v2 := (gf "dInst" (SReg (RV32I.d2e RV32I.fromDecode.data0))) in
  let l := [
      sact_nomispred;
      sact_sstack_full;
      sact_sstack_push;
      not (sact_sstack_pop);
      eqb (SReg RV32I.sstack_activated) ( [true]);
      eqb (SReg RV32I.halt) ( [false]);
      eqb (SReg (RV32I.d2e RV32I.fromDecode.valid0)) ([true]);
      eqb (gf "legal" v2) ( [true]);
      eqb (SReg (RV32I.e2w RV32I.fromExecute.valid0)) ( [false])
    ] in
  List.fold_left (fun acc elt => and acc elt) l (SConst (Bits [true])).

Definition sact_sstack_violation: sact :=
  let v2 := (gf "dInst" (SReg (RV32I.d2e RV32I.fromDecode.data0))) in
  let imm := (gf "immediateType" v2) in
  andl [
      sact_nomispred;
      not sact_sstack_empty;
      sact_sstack_pop;
      neq sact_sstack_top_address sact_return_address;
      eqb (SReg RV32I.sstack_activated) ( [true]);
      eqb (SReg RV32I.halt) ( [false]);
      eqb (SReg (RV32I.d2e RV32I.fromDecode.valid0)) ([true]);
      eqb (gf "legal" v2) ( [true]);
      eqb (SReg (RV32I.e2w RV32I.fromExecute.valid0)) ( [false]);
      eqb (gf "valid" imm) [true];
      eqb (gf "data" imm) [false;false;false]
    ].

Definition no_stack_violation : sact :=
  let underflow := andl [sact_nomispred; sact_sstack_empty; sact_sstack_pop] in
  let overflow  := andl [sact_nomispred; sact_sstack_full; sact_sstack_push] in
  let violation := andl [sact_nomispred; not sact_sstack_empty; sact_sstack_pop; neq sact_sstack_top_address sact_return_address] in
  andl [not underflow; not overflow; not violation; consistent_imm_type].

Definition add_ok fv : sact :=
  let final_e2w_data := fv (RV32I.e2w RV32I.fromExecute.data0) in
  let final_e2w_valid := fv (RV32I.e2w RV32I.fromExecute.valid0) in
 
  let fromDec := (SReg (RV32I.d2e RV32I.fromDecode.data0)) in
  let dInst := gf "dInst" fromDec in
  let instr := gf "inst" dInst in
  let opcode := uid "mon_opcode" (SUnop (UBits1 (USlice 0 7)) instr) in
  let fct3 := SUnop (UBits1 (USlice 12 3)) instr in
  let fct7 := SUnop (UBits1 (USlice 25 7)) instr in
  let is_add :=
    and (eqb opcode (rev [false; true; true; false; false; true; true]))
      (and (eqb fct3 [false; false; false])
         (eqb fct7 [false;false;false;false;false;false;false]))
  in
  let expected_result :=
    add (gf "rval1" fromDec) (gf "rval2" fromDec) in
  andl [
      sact_nomispred;
      is_add;
      eqb (SReg RV32I.halt) ( [false]);
      eqb (SReg (RV32I.d2e RV32I.fromDecode.valid0)) ([true]);
      eqb (gf "legal" dInst) ( [true]);
      eqb (SReg (RV32I.e2w RV32I.fromExecute.valid0)) ( [false]);
      not (and (equal (gf "newrd" (SVar final_e2w_data)) expected_result)
             (eqb (SVar final_e2w_valid) [true] ))
    ].


Definition decode_consistent_imm_type (fv: RV32I.reg_t -> positive): sact :=

  let dInstr := gf "dInst" (SVar (fv (RV32I.d2e RV32I.fromDecode.data0))) in
  let instr := gf "inst" dInstr in
  let immt := gf "immediateType" dInstr in
  let opcode := SUnop (UBits1 (USlice 0 7)) instr in
  let impl p q := or (not p) q in
  let is_immI :=
    and (eqb (gf "valid" immt) [true])
      (eqb (gf "data" immt) [false; false; false]) in
  let is_jalr :=
    eqb opcode [true; true; true; false; false; true; true]
  in
  andl [
      eqb (SReg (RV32I.d2e RV32I.fromDecode.valid0)) [false];
      eqb (SVar (fv (RV32I.d2e RV32I.fromDecode.valid0))) [true];
      is_jalr;
      not (is_immI)
    ].

