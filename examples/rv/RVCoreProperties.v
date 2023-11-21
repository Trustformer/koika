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


#[local] Instance eq_dec_reg: EqDec RV32I.reg_t := EqDec_FiniteType.

Section ShadowStackProperties.
  Context {REnv : Env RV32I.reg_t}.
  Variable ctx : env_t REnv (fun _ => val).

  Definition drules rule :=
    match uaction_to_daction (desugar_action tt (RV32I.rv_urules rule)) with
    | Some d => d
    | None => DFail unit_t
    end.

  Definition eql (l1 l2: list bool) : bool := list_beq bool Bool.eqb l1 l2.

  Lemma eql_iff:
    forall l1 l2,
      eql l1 l2 = true <-> l1 = l2.
  Proof.
    unfold eql.
    induction l1; simpl; intros; eauto.
    - destruct l2; try congruence. tauto. intuition congruence.
    - destruct l2; try congruence. intuition congruence.
      rewrite andb_true_iff. rewrite eqb_true_iff. rewrite IHl1. intuition congruence.
  Qed.

    Lemma eql_iff_false:
      forall l1 l2,
        eql l1 l2 = false <-> l1 <> l2.
    Proof.
      intros.
      destruct (eql l1 l2) eqn:?.
      apply eql_iff in Heqb. subst. intuition congruence.
      split; auto. intros _ EQ. subst.
      generalize (eql_iff l2 l2). intros (A & B).
      rewrite B in Heqb. congruence. auto.
    Qed.

    Lemma list_eqb_false:
      forall l1 l2,
        list_eqb Bool.eqb l1 l2 = false -> l1 <> l2.
    Proof.
      induction l1; simpl; intros; eauto; destruct l2; intuition try congruence.
      rewrite andb_false_iff in H. destruct H.
      apply eqb_false_iff in H. inv H0. congruence.
      inv H0. eauto.
    Qed.


    Lemma eql_list_eqb:
      forall l1 l2,
        eql l1 l2 = list_eqb Bool.eqb l1 l2.
    Proof. reflexivity. Qed.



    (* Propositions about the initial state *)
  Definition no_mispred (ctx: env_t REnv (fun _ : RV32I.reg_t => val))
    : Prop :=
      forall v,
      getenv REnv ctx (RV32I.d2e (RV32I.fromDecode.data0)) =
        Struct (RV32I.decode_bookkeeping) v ->
      get_field_struct (struct_fields RV32I.decode_bookkeeping) v "epoch" =
      Some (getenv REnv ctx (RV32I.epoch)).

    Definition sstack_empty (ctx: env_t REnv (fun _ : RV32I.reg_t => val))
    : Prop :=
      getenv REnv ctx (RV32I.sstack (RV32I.ShadowStack.size))
      = @val_of_value
        (bits_t RV32I.ShadowStack.index_sz)
        (Bits.of_nat (RV32I.ShadowStack.index_sz) 0).

    Definition sstack_full (ctx: env_t REnv (fun _ : RV32I.reg_t => val))
    : Prop :=
      getenv REnv ctx (RV32I.sstack (RV32I.ShadowStack.size))
      = @val_of_value
        (bits_t RV32I.ShadowStack.index_sz)
        (Bits.of_nat (RV32I.ShadowStack.index_sz) RV32I.ShadowStack.capacity).

    (* XXX Note that both a pop and a push can happen for the same instruction *)

    (* This function is defined in a way that mirrors RVCore.v *)
    Definition is_call_instruction (instr: bits_t 32) : bool :=
      let bits := vect_to_list (bits_of_value instr) in
      let opcode_ctrl := List.firstn 3 (List.skipn 4 bits) in
      let opcode_rest := List.firstn 4 (List.skipn 0 bits) in
      let rs1 := List.firstn 5 (List.skipn 15 bits) in
      let rd := List.firstn 5 (List.skipn 7 bits) in
      (eql opcode_ctrl (rev [true; true; false]))
      && (
        (
          (eql opcode_rest (rev [true; true; true; true]))
          && (
            (eql rd (rev [false; false; false; false; true]))
            || (eql rd (rev [false; false; true; false; true]))))
        || (
          (eql opcode_rest (rev [false; true; true; true]))
          && (
            (eql rd (rev [false; false; false; false; true]))
            || (eql rd (rev [false; false; true; false; true]))))).

    Definition sstack_push (ctx: env_t REnv (fun _ : RV32I.reg_t => val))
    : Prop :=
      forall v w b,
      getenv REnv ctx (RV32I.d2e (RV32I.fromDecode.data0))
      = Struct (RV32I.decode_bookkeeping) v
      -> get_field_struct (struct_fields RV32I.decode_bookkeeping) v "dInst"
      = Some (Struct (decoded_sig) w)
      -> get_field_struct (struct_fields decoded_sig) w "inst" = Some (Bits b)
      -> is_call_instruction (Bits.of_N 32 (Bits.to_N (vect_of_list b))) = true.

    Definition is_ret_instruction (instr: bits_t 32) : bool :=
      let bits := (vect_to_list (bits_of_value instr)) in
      let opcode_ctrl := List.firstn 3 (List.skipn 4 bits) in
      let opcode_rest := List.firstn 4 (List.skipn 0 bits) in
      let rs1 := List.firstn 5 (List.skipn 15 bits) in
      let rd := List.firstn 5 (List.skipn 7 bits) in
      (eql opcode_ctrl [false; true; true])
      && (eql opcode_rest [true; true; true; false])
      && (
          (
            (
              (eql rd (rev [false; false; false; false; true])
               || (eql rd (rev [false; false; true; false; true])))
              && (negb (eql rd rs1))
              && (
                  (eql rs1 (rev [false; false; false; false; true]))
                  || (eql rs1 (rev [false; false; true; false; true]))))
            || (
                (negb (eql rd (rev [false; false; false; false; true])))
                && (negb (eql rd (rev [false; false; true; false; true])))
                && (
                    (eql rs1 (rev [false; false; false; false; true]))
                    || (eql rs1 (rev [false; false; true; false; true])))))).

    Definition sstack_pop (ctx: env_t REnv (fun _ : RV32I.reg_t => val))
    : Prop :=
      forall v w b,
      getenv REnv ctx (RV32I.d2e (RV32I.fromDecode.data0))
      = Struct (RV32I.decode_bookkeeping) v
      -> get_field_struct (struct_fields RV32I.decode_bookkeeping) v "dInst"
      = Some (Struct (decoded_sig) w)
      -> get_field_struct (struct_fields decoded_sig) w "inst" = Some (Bits b)
      -> is_ret_instruction (Bits.of_N 32 (Bits.to_N (vect_of_list b))) = true.

    (* TODO should never return None, simplify? *)
    Definition ret_address (ctx: env_t REnv (fun _ : RV32I.reg_t => val))
    : option (bits_t 32) :=
      let data := getenv REnv ctx (RV32I.d2e (RV32I.fromDecode.data0)) in
      match data with
      | Struct _ lv =>
        let rs1 :=
          get_field_struct (struct_fields RV32I.decode_bookkeeping) lv "rval1"
        in
        let dInst :=
          get_field_struct (struct_fields RV32I.decode_bookkeeping) lv "dInst"
        in
        match rs1, dInst with
        | Some rs1_val, Some (Struct (decoded_sig) dInst) =>
          let inst :=
            get_field_struct (struct_fields rv.RVCore.decoded_sig) dInst "inst"
          in
          match inst with
          | Some inst_val =>
            let bits :=
              Bits.to_N (
                Bits.and
                  (Bits.of_N
                    (Datatypes.length ((ubits_of_value rs1_val)))
                    (Bits.to_N
                      (Bits.of_list (ubits_of_value rs1_val))
                      + Bits.to_N (
                        Bits.of_list (
                          List.skipn 20 (ubits_of_value inst_val) ++
                          List.repeat (List.last (ubits_of_value inst_val) true) 20
                    )))
                  )
                  (Vect.Bits.neg (Bits.of_N (
                    Datatypes.length (ubits_of_value rs1_val)) 1)
                  )
              ) in
            Some (Bits.of_N 32 bits)
          | None => None
          end
        | _, _ => None
        end
      | _ => None
      end.

    Definition sstack_top_address (ctx: env_t REnv (fun _ : RV32I.reg_t => val))
    : option (bits_t 32) :=
      let index_raw := getenv REnv ctx (RV32I.sstack RV32I.ShadowStack.size) in
      let index_nat := pred (Bits.to_nat (vect_of_list (ubits_of_value index_raw))) in
      let index := index_of_nat (pow2 RV32I.ShadowStack.index_sz) index_nat in
      match index with
      | Some x =>
        let data_raw :=
          (getenv REnv ctx (RV32I.sstack (RV32I.ShadowStack.stack x))) in
        Some (Bits.of_N 32 (Bits.to_N (vect_of_list (ubits_of_value data_raw))))
      | _ => None
      end.


    Definition sstack_underflow (ctx: env_t REnv (fun _ : RV32I.reg_t => val))
    : Prop :=
      no_mispred ctx /\ sstack_empty ctx /\ sstack_pop ctx.
    Definition sstack_overflow (ctx: env_t REnv (fun _ : RV32I.reg_t => val))
    : Prop :=
      no_mispred ctx /\ sstack_full ctx /\ (not (sstack_pop ctx))
      /\ sstack_push ctx.
    Definition sstack_address_violation
      (ctx: env_t REnv (fun _ : RV32I.reg_t => val))
    : Prop :=
      no_mispred ctx /\ ~ sstack_empty ctx /\ sstack_pop ctx
      /\ sstack_top_address ctx <> ret_address ctx.

    Definition sstack_violation (ctx: env_t REnv (fun _ : RV32I.reg_t => val))
    : Prop :=
      sstack_underflow ctx \/ sstack_overflow ctx
      \/ sstack_address_violation ctx.

    (* (* Final state *) *)
    (* Definition halt_set (ext_Sigma : RV32I.ext_fn_t -> ExternalSignature) (ext_sigma : RV32I.ext_fn_t -> val -> val) (ctx: env_t REnv (fun _ : RV32I.reg_t => val)) : Prop := *)
    (*   getenv REnv (interp_cycle ctx ext_sigma (sf ext_Sigma)) RV32I.halt = Bits [true]. *)
End ShadowStackProperties.
