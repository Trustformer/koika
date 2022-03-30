(*! Proofs about the behavior of our basic shadow stack mechanism !*)
Require Import Coq.Program.Equality.
Require Import Koika.BitsToLists Koika.Frontend Koika.UntypedSemantics
  Koika.UntypedIndSemantics Koika.UntypedIndTactics.
Require Import Koika.SimpleFormInterpretation.
Require Import rv.ShadowStack rv.RVCore rv.rv32 rv.rv32i.
(* Require Import rv.RVCoreNoShadowStack rv.rv32NoShadowStack *)
(*   rv.rv32iNoShadowStack. *)
Require Import SimpleForm SimpleVal.

Import Coq.Lists.List.ListNotations.
Scheme Equality for list.

(* We mostly reason on the instruction that is currently entering the execute
   stage. All the information available about it is in the d2e structure
   (decode to execute buffer). *)
Section ShadowStackProperties.
  Context {REnv : Env RV32I.reg_t}.
  Context (ext_sigma : RV32I.ext_fn_t -> val -> val).
  Context (ext_Sigma : RV32I.ext_fn_t -> ExternalSignature).

  Hypothesis wt_sigma: forall (ufn : RV32I.ext_fn_t) (vc : val),
      wt_val (arg1Sig (ext_Sigma ufn)) vc ->
      wt_val (retSig (ext_Sigma ufn)) (ext_sigma ufn vc).

  Definition drules rule :=
    match uaction_to_daction (desugar_action tt (RV32I.rv_urules rule)) with
    | Some d => d
    | None => DFail unit_t
    end.

  Hypothesis rules_wt:
    forall rule : rv_rules_t,
    exists t : type, wt_daction (Sigma:=ext_Sigma) (R:=RV32I.R) unit string string [] (drules rule) t.

  Definition schedule := rv_schedule.
  Definition eql (l1 l2: list bool) : bool := list_beq bool Bool.eqb l1 l2.

  (* Propositions about the initial state *)
  Definition no_mispred
    (ctx: env_t REnv (fun _ : RV32I.reg_t => val))
  : Prop :=
    forall v,
    getenv REnv ctx (RV32I.d2e (RV32I.fromDecode.data0)) =
      Struct (RV32I.decode_bookkeeping) v ->
    get_field_struct (struct_fields RV32I.decode_bookkeeping) v "epoch" =
    Some (getenv REnv ctx (RV32I.epoch)).

  Definition stack_empty
    (ctx: env_t REnv (fun _ : RV32I.reg_t => val))
  : Prop :=
    getenv REnv ctx (RV32I.stack (RV32I.ShadowStack.size))
    = @val_of_value
      (bits_t RV32I.ShadowStack.index_sz)
      (Bits.of_nat (RV32I.ShadowStack.index_sz) 0).

  Definition stack_full
    (ctx: env_t REnv (fun _ : RV32I.reg_t => val))
  : Prop :=
    getenv REnv ctx (RV32I.stack (RV32I.ShadowStack.size))
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
    (eql opcode_ctrl [true; true; false])
    && (
      (
        (eql opcode_rest [true; true; true; true])
        && (
          (eql rd [false; false; false; false; true])
          || (eql rd [false; false; true; false; true])))
      || (
        (eql opcode_rest [false; true; true; true])
        && (
          (eql rd [false; false; false; false; true])
          || (eql rd [false; false; true; false; true])))).

  (* This function is defined in a way that mirrors RVCore.v *)
  Definition is_ret_instruction (instr: bits_t 32) : bool :=
    let bits := vect_to_list (bits_of_value instr) in
    let opcode_ctrl := List.firstn 3 (List.skipn 4 bits) in
    let opcode_rest := List.firstn 4 (List.skipn 0 bits) in
    let rs1 := List.firstn 5 (List.skipn 15 bits) in
    let rd := List.firstn 5 (List.skipn 7 bits) in
    (eql opcode_ctrl [true; true; false])
    && (eql opcode_rest [false; true; true; true])
    && (
      (
        (
          (eql rd [false; false; false; false; true])
          || (eql rd [false; false; true; false; true]))
        && (negb (eql rd rs1))
        && (
          (eql rs1 [false; false; false; false; true])
          || (eql rs1 [false; false; true; false; true])))
      || (
        (negb (eql rd [false; false; false; false; true]))
        && (eql rd [false; false; true; false; true])
        && (
          (eql rs1 [false; false; false; false; true])
          || (eql rs1 [false; false; true; false; true])))).

  Definition stack_push
    (ctx: env_t REnv (fun _ : RV32I.reg_t => val))
  : Prop :=
    forall v w b,
    getenv REnv ctx (RV32I.d2e (RV32I.fromDecode.data0)) =
      Struct (RV32I.decode_bookkeeping) v ->
    get_field_struct (struct_fields RV32I.decode_bookkeeping) v "dInst" =
      Some (Struct (decoded_sig) w) ->
    get_field_struct (struct_fields decoded_sig) w "inst" =
      Some (Bits b) ->
    is_call_instruction (Bits.of_N 32 (Bits.to_N (vect_of_list b))) = true.

  Definition stack_pop
    (ctx: env_t REnv (fun _ : RV32I.reg_t => val))
  : Prop :=
    forall v w b,
    getenv REnv ctx (RV32I.d2e (RV32I.fromDecode.data0)) =
      Struct (RV32I.decode_bookkeeping) v ->
    get_field_struct (struct_fields RV32I.decode_bookkeeping) v "dInst" =
      Some (Struct (decoded_sig) w) ->
    get_field_struct (struct_fields decoded_sig) w "inst" =
      Some (Bits b) ->
    is_ret_instruction (Bits.of_N 32 (Bits.to_N (vect_of_list b))) = true.

  (* TODO should never return None, simplify? *)
  Definition stack_push_address
    (ctx: env_t REnv (fun _ : RV32I.reg_t => val))
  : option (bits_t 32) :=
    let data := getenv REnv ctx (RV32I.d2e (RV32I.fromDecode.data0)) in
    match data with
    | Struct _ lv =>
      let v :=
        get_field_struct (struct_fields RV32I.decode_bookkeeping) lv "pc"
      in
      match v with
      | Some w =>
        let uw := ubits_of_value w in
        let addr_val := (Bits.to_N (vect_of_list uw) + 4)%N in
        Some (Bits.of_N 32 addr_val)
      | _ => None
      end
    | _ => None
    end.

  (* TODO should never return None, simplify? *)
  Definition stack_top_address
    (ctx: env_t REnv (fun _ : RV32I.reg_t => val))
  : option (bits_t 32) :=
    let index_raw := getenv REnv ctx (RV32I.stack RV32I.ShadowStack.size) in
    let index_nat := Bits.to_nat (vect_of_list (ubits_of_value index_raw)) in
    let index := index_of_nat (pow2 RV32I.ShadowStack.index_sz) index_nat in
    match index with
    | Some x =>
      let data_raw :=
        (getenv REnv ctx (RV32I.stack (RV32I.ShadowStack.stack x))) in
      Some (Bits.of_N 32 (Bits.to_N (vect_of_list (ubits_of_value data_raw))))
    | None => None
    end.

  Definition stack_underflow
    (ctx: env_t REnv (fun _ : RV32I.reg_t => val))
  : Prop := no_mispred ctx /\ stack_empty ctx /\ stack_pop ctx.
  Definition stack_overflow
    (ctx: env_t REnv (fun _ : RV32I.reg_t => val))
  : Prop :=
    no_mispred ctx /\ stack_full ctx /\ (not (stack_pop ctx)) /\ stack_push ctx.
  Definition stack_address_violation
    (ctx: env_t REnv (fun _ : RV32I.reg_t => val))
  : Prop :=
    no_mispred ctx /\ stack_push ctx /\ stack_top_address ctx <> stack_push_address ctx.

  Definition stack_violation
    (ctx: env_t REnv (fun _ : RV32I.reg_t => val))
  : Prop :=
    stack_underflow ctx \/ stack_overflow ctx \/ stack_address_violation ctx.

  (* Final state *)
  Definition halt_set
    (ctx: env_t REnv (fun _ : RV32I.reg_t => val))
  : Prop :=
    forall ctx',
    UntypedIndSemantics.interp_cycle
      RV32I.rv_urules ctx ext_sigma schedule ctx' ->
    getenv REnv ctx' RV32I.halt = @val_of_value (bits_t 1) Ob~1.

  Fixpoint interp_n_cycles
    n (ctx: env_t REnv (fun _ : RV32I.reg_t => val))
  : env_t REnv (fun _ : RV32I.reg_t => val) :=
    match n with
    | O => ctx
    | S n' => interp_n_cycles n' (
        UntypedSemantics.interp_cycle RV32I.rv_urules ctx ext_sigma schedule
      )
    end.

  (* Fixpoint interp_n_cycles_no_shadow_stack *)
  (*   n (ctx: env_t REnv (fun _ : RV32I.reg_t => val)) *)
  (* : env_t REnv (fun _ : RV32I.reg_t => val) := *)
  (*   match n with *)
  (*   | O => ctx *)
  (*   | S n' => interp_n_cycles n' ( *)
  (*       UntypedSemantics.interp_cycle RV32I.rv_urules ctx ext_sigma schedule *)
  (*     ) *)
  (*   end. *)

  (* Definition is_sink_state *)
  (*   (ctx: env_t REnv (fun _ : RV32I.reg_t => val)) *)
  (* : Prop := *)
  (*   forall n ctx', interp_n_cycles n ctx' = ctx. *)

  (* Main lemmas *)
  (* Lemma halt_leads_to_a_sink_state: *)
  (*   forall (ctx: env_t REnv (fun _ : RV32I.reg_t => val)), *)
  (*   halt_set ctx -> is_sink_state ctx. *)
  (* Proof. *)
  (* Qed. *)

  Ltac destr_in H :=
    match type of H with
    | context[match ?a with _ => _ end] => destruct a eqn:?
    end.

  Ltac destr :=
    match goal with
    |- context[match ?a with _ => _ end] => destruct a eqn:?; try congruence
    end.

  Definition is_write_halt
    (reg_t ext_fn_t: Type)
    (ua: uaction pos_t var_t fn_name_t reg_t ext_fn_t)
    (fR: reg_t -> RV32I.reg_t) (fSigma: ext_fn_t -> RV32I.ext_fn_t)
  : bool :=
    match ua with
    | UWrite _ r _ =>
      match (fR r) with
      | RV32I.halt => true
      | _ => false
      end
    | _ => false
    end.
  

  Set Typeclasses Debug.
  Instance eq_dec_reg: EqDec RV32I.reg_t := EqDec_FiniteType.
  Existing Instance etaRuleInformationRaw.

  Ltac inv H := inversion H; try subst; clear H.


  Definition simplify_sf  sf ctx :=
    {|
      final_values := final_values sf;
      vars := Maps.PTree.map (fun _ '(t,a) => (t, simplify_sact (REnv:=REnv) (reg_t:=RV32I.reg_t) ctx ext_sigma a)) (vars sf)

    |}.

  Definition halt_set2 ctx :=
    forall sf n,
      remove_vars_for_var (simplify_sf (schedule_to_simple_form RV32I.R (Sigma:=ext_Sigma)
                                           drules schedule) ctx) RV32I.halt = Some sf ->
      list_assoc (final_values sf) RV32I.halt = Some n ->
      SimpleForm.interp_sact REnv ctx (vars sf) (sigma:=ext_sigma) (SVar n) (Bits [true]).


  Lemma wt_sact_simplify_sact:
    forall vvs ctx
           (WTRENV: Wt.wt_renv RV32I.R REnv ctx) a t,
      (* wt_vvs RV32I.R (Sigma:=ext_Sigma) (vars sf) -> *)
      wt_sact RV32I.R (Sigma:=ext_Sigma) vvs a t ->
      wt_sact RV32I.R (Sigma:=ext_Sigma) vvs (simplify_sact ctx ext_sigma a) t.
  Proof.
    induction a; simpl; intros; eauto.
    - inv H. destr. 2: econstructor; eauto.
      repeat destr; try now (econstructor; eauto). subst. eauto. eauto.
    - inv H. destr; try now econstructor; eauto.
      repeat destr; try now (econstructor; eauto). subst. inv H4. econstructor. econstructor.
      eapply eval_sact_no_vars_wt in Heqo. 4: apply IHa; eauto. inv Heqo. reflexivity.
      auto. auto.
    - inv H. destr; try now econstructor; eauto.
      destr; try now (econstructor; eauto).
      + inv H6.
        destruct (eval_sact_no_vars ctx ext_sigma (simplify_sact ctx ext_sigma a1)) eqn:?.
        generalize (eval_sact_no_vars_wt RV32I.R ext_Sigma ctx ext_sigma (wt_sigma:=wt_sigma)
                                         WTRENV _ _ _ (IHa1 _ H3) _ Heqo). intro WT1. inv WT1.
        * destruct (eval_sact_no_vars ctx ext_sigma (simplify_sact ctx ext_sigma a2)) eqn:?.
          generalize (eval_sact_no_vars_wt RV32I.R ext_Sigma ctx ext_sigma (wt_sigma:=wt_sigma)
                                           WTRENV _ _ _ (IHa2 _ H5) _ Heqo0). intro WT2. inv WT2.
          repeat destr; repeat econstructor; eauto.
          repeat destr; repeat econstructor; eauto.
        * destruct (eval_sact_no_vars ctx ext_sigma (simplify_sact ctx ext_sigma a2)) eqn:?.
          generalize (eval_sact_no_vars_wt RV32I.R ext_Sigma ctx ext_sigma (wt_sigma:=wt_sigma)
                                           WTRENV _ _ _ (IHa2 _ H5) _ Heqo0). intro WT2. inv WT2.
          repeat destr; repeat econstructor; eauto.
          repeat destr; repeat econstructor; eauto.
      + inv H6.
        destruct (eval_sact_no_vars ctx ext_sigma (simplify_sact ctx ext_sigma a1)) eqn:?.
        generalize (eval_sact_no_vars_wt RV32I.R ext_Sigma ctx ext_sigma (wt_sigma:=wt_sigma)
                                         WTRENV _ _ _ (IHa1 _ H3) _ Heqo). intro WT1. inv WT1.
        * destruct (eval_sact_no_vars ctx ext_sigma (simplify_sact ctx ext_sigma a2)) eqn:?.
          generalize (eval_sact_no_vars_wt RV32I.R ext_Sigma ctx ext_sigma (wt_sigma:=wt_sigma)
                                           WTRENV _ _ _ (IHa2 _ H5) _ Heqo0). intro WT2. inv WT2.
          repeat destr; repeat econstructor; eauto.
          repeat destr; repeat econstructor; eauto.
        * destruct (eval_sact_no_vars ctx ext_sigma (simplify_sact ctx ext_sigma a2)) eqn:?.
          generalize (eval_sact_no_vars_wt RV32I.R ext_Sigma ctx ext_sigma (wt_sigma:=wt_sigma)
                                           WTRENV _ _ _ (IHa2 _ H5) _ Heqo0). intro WT2. inv WT2.
          repeat destr; repeat econstructor; eauto.
          repeat destr; repeat econstructor; eauto.
    - inv H. econstructor. eauto.
  Qed.

  Lemma wt_sact_simplify_vars:
    forall vvs ctx
           (WTRENV: Wt.wt_renv RV32I.R REnv ctx) a t,
      (* wt_vvs RV32I.R (Sigma:=ext_Sigma) (vars sf) -> *)
      wt_sact RV32I.R (Sigma:=ext_Sigma) vvs a t ->
      wt_sact RV32I.R (Sigma:=ext_Sigma) (Maps.PTree.map (fun _ '(t,a) => (t, simplify_sact ctx ext_sigma a )) vvs) a t.
  Proof.
    induction a; simpl; intros; eauto.
    - inv H. econstructor; eauto.
      rewrite Maps.PTree.gmap. setoid_rewrite H1. reflexivity.
    - inv H; econstructor; eauto.
    - inv H. econstructor; eauto.
    - inv H. econstructor; eauto.
    - inv H. econstructor; eauto.
    - inv H. econstructor; eauto.
    - inv H. econstructor; eauto.
  Qed.

  Lemma wt_vvs_simplify_sf:
    forall sf ctx
           (WTRENV: Wt.wt_renv RV32I.R REnv ctx),
      wt_vvs RV32I.R (Sigma:=ext_Sigma) (vars sf) ->
      wt_vvs RV32I.R (Sigma:=ext_Sigma) (vars (simplify_sf sf ctx)).
  Proof.
    red; intros. simpl in H0.
    rewrite Maps.PTree.gmap in H0.
    unfold option_map in H0; repeat destr_in H0; inv H0.
    eapply H in Heqo. simpl.
    eapply wt_sact_simplify_vars. auto.
    eapply wt_sact_simplify_sact; eauto.
  Qed.

  Lemma vsv_simplify_sf:
    forall sf ctx,
      vvs_smaller_variables (vars sf) ->
      vvs_smaller_variables (vars (simplify_sf sf ctx)).
  Proof.
    red; intros. simpl in H0.
    rewrite Maps.PTree.gmap in H0.
    unfold option_map in H0; repeat destr_in H0; inv H0.
    eapply H in Heqo. eapply Heqo.


    Lemma var_in_sact_simplify_sact:
      forall ctx s v,
        var_in_sact (simplify_sact (REnv:=REnv) ctx ext_sigma s) v ->
        var_in_sact s v.
    Proof.
      intros ctx s v VIS.
      apply var_in_sact_ok in VIS.
      eapply var_in_sact_ok_inv. apply RV32I.R. apply ext_Sigma.
      revert s v VIS.
      induction s; simpl; intros; eauto.
      - rewrite ! in_app_iff. repeat destr_in VIS; eauto.
        + simpl in VIS. rewrite ! in_app_iff in VIS. intuition eauto.
        + simpl in VIS. rewrite ! in_app_iff in VIS. intuition eauto.
        + simpl in VIS. rewrite ! in_app_iff in VIS. intuition eauto.
        + simpl in VIS. rewrite ! in_app_iff in VIS. intuition eauto.
        + simpl in VIS. rewrite ! in_app_iff in VIS. intuition eauto.
        + simpl in VIS. rewrite ! in_app_iff in VIS. intuition eauto.
        + simpl in VIS. rewrite ! in_app_iff in VIS. intuition eauto.
      - repeat destr_in VIS; eauto. inv VIS.
      - rewrite ! in_app_iff. repeat destr_in VIS; eauto.
        all: try (simpl in VIS; rewrite ! in_app_iff in VIS; intuition eauto).
        all: try now (inv VIS).
        Unshelve. apply RV32I.R.
    Qed.
    eapply var_in_sact_simplify_sact. eauto.
  Qed.

  Lemma stack_violation_results_in_halt:
    (* forall (env_bf env_af: @UREnv RV32I.reg_t REnv), *)
    (* (env_af = SimpleFormInterpretation.interp_cycle env_bf ext_sigma ) -> True. *)
    forall ctx
           (WTRENV: Wt.wt_renv RV32I.R REnv ctx)
           (NoHalt: (getenv REnv ctx RV32I.halt) = Bits [false])
           (Valid: getenv REnv ctx (RV32I.d2e RV32I.fromDecode.valid0) = Bits [true])
           (Legal:
             forall v v2,
               getenv REnv ctx (RV32I.d2e RV32I.fromDecode.data0) =
                 Struct RV32I.decode_bookkeeping v ->
               get_field_struct (struct_fields RV32I.decode_bookkeeping) v "dInst" = Some (Struct decoded_sig v2) ->
               get_field_struct (struct_fields decoded_sig) v2 "legal" = Some (Bits [true]))

    ,
    stack_violation ctx -> halt_set2 ctx.
  Proof.
    intros ctx WTRENV NoHalt Valid Legal SV.
    unfold halt_set2. intros sf n SF HALT.
    unfold stack_violation in SV.
    unfold stack_underflow, stack_overflow, stack_address_violation in SV.

    generalize (WTRENV (RV32I.d2e RV32I.fromDecode.data0)). intro WTdata0. simpl in WTdata0.
    inv WTdata0.
    assert (NMP: no_mispred ctx) by intuition.
    symmetry in H0. specialize (NMP _ H0).
    generalize (WTRENV RV32I.epoch). intro WTepoch. simpl in WTepoch.
    apply Sact.wt_val_bool in WTepoch. destruct WTepoch as (? & WTepoch). rewrite WTepoch in NMP.

    assert (WTsize:= WTRENV (RV32I.stack RV32I.ShadowStack.size)). simpl in WTsize. inv WTsize.
    change (log2 5) with 3 in H3.
    destruct bs. simpl in H3; lia.
    destruct bs. simpl in H3; lia.
    destruct bs. simpl in H3; lia.
    destruct bs. 2: simpl in H3; lia. clear H3.
    symmetry in H2. simpl in H1.
    
    Ltac invtypes := repeat match goal with
           | H: Forall2 _ [] _ |- _ => inv H
           | H: Forall2 _ (_::_) _ |- _ =>
               inv H
           | H: wt_val (bits_t 1) _ |- _ => apply Sact.wt_val_bool in H; destruct H; subst
                            end.
    invtypes.
    inv H6.
    simpl in H1. invtypes.
    simpl in NMP. inv NMP.

    assert (EQse:
        stack_empty ctx <->
        b = false /\ b0 = false /\ b1 = false
           ).
    unfold stack_empty. rewrite H2. simpl. cbv. intuition congruence.

    inv H11.
    assert (EQspop: stack_pop ctx <-> is_ret_instruction
                                        (Bits.of_N 32 (Bits.to_N (Bits.of_list bs))) = true).
    unfold stack_pop. rewrite H0.
    split. intro A. eapply A. eauto. simpl. eauto. simpl. auto.
    intros IRI v w b2 EQ1 EQ2 EQ3. inv EQ1; simpl in EQ2; inv EQ2; simpl in EQ3; inv EQ3. auto.

    assert (EQspush: stack_push ctx <-> is_call_instruction
                                        (Bits.of_N 32 (Bits.to_N (Bits.of_list bs))) = true).
    unfold stack_push. rewrite H0.
    split. intro A. eapply A. eauto. simpl. eauto. simpl. auto.
    intros ICI v w b2 EQ1 EQ2 EQ3. inv EQ1; simpl in EQ2; inv EQ2; simpl in EQ3; inv EQ3. auto.

    assert (EQsf:
             stack_full ctx <->
               b = false /\ b0 = false /\ b1 = true
           ).
    unfold stack_full. rewrite H2. simpl. cbv. intuition congruence.
    inv H4.
    assert (EQpa: stack_push_address ctx =
              Some (Bits.of_N 32 (Bits.to_N (Bits.of_list bs0) + 4)%N)
           ).
    {
      unfold stack_push_address.
      rewrite H0. simpl. auto.
    }
    assert (Bits.to_nat Ob~b1~b0~b < pow2 RV32I.ShadowStack.index_sz).
    change (Bits.to_nat Ob~b1~b0~b < pow2 3). simpl.
    apply Bits.to_nat_bounded.
    edestruct @index_of_nat_bounded as (idx & EQidx). apply H.

    assert (WTtop:= WTRENV (RV32I.stack (RV32I.ShadowStack.stack idx))). simpl in WTtop.
    inv WTtop.

    assert (EQta: stack_top_address ctx =
                    Some (Bits.of_N 32 (Bits.to_N (Bits.of_list bs1)))
           ).
    {
      unfold stack_top_address.
      rewrite H2. simpl ubits_of_value.
      simpl Bits.of_list.
      setoid_rewrite EQidx. rewrite <- H6. reflexivity.
    }

    move SV at bottom.
    assert (CONDS:
             stack_empty ctx /\ stack_pop ctx
             \/ stack_push ctx /\ ((stack_full ctx /\ ~ stack_pop ctx) \/ stack_top_address ctx <> stack_push_address ctx)).
    now intuition. clear SV.
    rewrite EQse, EQspop, EQspush, EQsf, EQpa, EQta in CONDS.
    clear EQse EQspop EQspush EQsf EQpa EQta.
    move Legal at bottom.
    specialize (fun w => Legal _ w H0). simpl in Legal.
    specialize (Legal _ eq_refl). simpl in Legal. inv Legal.


    Ltac replacereg H sf :=
      let sf2 := fresh "sf" in
      match type of H with
        getenv _ _ ?r = ?v =>
          set (sf2 := replace_reg sf r v)
      | ?v = getenv _ _ ?r =>
          set (sf2 := replace_reg sf r v)
      end.
    replacereg NoHalt sf.
    replacereg Valid sf0.
    replacereg H0 sf1.
    replacereg WTepoch sf2.
    replacereg H2 sf3.

    assert (interp_sact (sigma:=ext_sigma) REnv ctx (vars sf4) (SVar n) (Bits [true])).
    Set Printing Depth 20.
    Time native_compute in SF. injection SF. clear SF. intro A.
    subst sf.
    Time native_compute in sf4.
    clear sf0 sf1 sf2 sf3.

    set (ks:= PosSort.sort (map fst (Maps.PTree.elements (vars sf4)))).
    native_compute in ks.
    set (ks2 := firstn 21 ks). native_compute in ks2. clear ks.

    set (ip := snd (fold_left
                 (fun '(sf0, l) (var : positive) =>
                    let '(sf1, l1) := simplify_var ctx ext_sigma sf0 var in (sf1, l1 ++ l)) ks2 (sf4,[]))).

    Eval native_compute in Maps.PTree.get 117 (vars sf4).
    Time Eval native_compute in match ip with l => List.length l end.

    Eval native_compute in Maps.PTree.get 849 (vars sf4).

    set (sf5 := simplify_sf sf4 ctx).
    Time native_compute in sf5.
    Time Eval native_compute in vvs_size (vars sf4) 2000.
    Time Eval native_compute in vvs_size (vars sf5) 2000.
    native_compute in H1. apply Some_inj in H1. subst n.
    Time Eval native_compute in List.length (Maps.PTree.elements (vars sf2)).
    
    
    set (sf2 := replace_reg sf RV32I.halt (Bits [false])).
    set (sf3 := replace_reg sf2 )
    fold sf2 in H1.



    Set Printing Depth 20.
    Time native_compute in H0. injection H0. clear H0. intro A. subst sf.
    native_compute in H1. apply Some_inj in H1. subst n.
    Time Eval native_compute in List.length (Maps.PTree.elements (vars sf2)).





    unfold stack_violation in H.
    unfold stack_underflow, stack_overflow, stack_address_violation in H.

    assert (NMP: no_mispred ctx) by intuition.

    generalize (WTRENV (RV32I.d2e RV32I.fromDecode.data0)). intro WTdata0. simpl in WTdata0.
    inv WTdata0.
    symmetry in H1. specialize (NMP _ H1).
    generalize (WTRENV RV32I.epoch). intro WTepoch. simpl in WTepoch.
    apply Sact.wt_val_bool in WTepoch. destruct WTepoch as (? & WTepoch). rewrite WTepoch in NMP.

    assert (WTsize:= WTRENV (RV32I.stack RV32I.ShadowStack.size)). simpl in WTsize. inv WTsize.
    change (log2 5) with 3 in H4.
    destruct bs. simpl in H4; lia.
    destruct bs. simpl in H4; lia.
    destruct bs. simpl in H4; lia.
    destruct bs. 2: simpl in H4; lia. clear H4.
    symmetry in H3. simpl in H2.
    Ltac invtypes := repeat match goal with
           | H: Forall2 _ [] _ |- _ => inv H
           | H: Forall2 _ (_::_) _ |- _ =>
               inv H
           | H: wt_val (bits_t 1) _ |- _ => apply Sact.wt_val_bool in H; destruct H; subst
                            end.
    invtypes.
    inv H7.
    simpl in H2. invtypes.
    simpl in NMP. inv NMP.

    assert (EQse:
        stack_empty ctx <->
        b = false /\ b0 = false /\ b1 = false
           ).
    unfold stack_empty. rewrite H3. simpl. cbv. intuition congruence.

    inv H12.
    assert (EQspop: stack_pop ctx <-> is_ret_instruction
                                        (Bits.of_N 32 (Bits.to_N (Bits.of_list bs))) = true).
    unfold stack_pop. rewrite H1.
    split. intro A. eapply A. eauto. simpl. eauto. simpl. auto.
    intros. inv H6. simpl in H7. inv H7. simpl in H10. inv H10. auto.

    assert (EQspush: stack_push ctx <-> is_call_instruction
                                        (Bits.of_N 32 (Bits.to_N (Bits.of_list bs))) = true).
    unfold stack_push. rewrite H1.
    split. intro A. eapply A. eauto. simpl. eauto. simpl. auto.
    intros. inv H6. simpl in H7. inv H7. simpl in H10. inv H10. auto.

    assert (EQsf:
             stack_full ctx <->
               b = false /\ b0 = false /\ b1 = true
           ).
    unfold stack_full. rewrite H3. simpl. cbv. intuition congruence.
    inv H5.
    assert (EQpa: stack_push_address ctx =
              Some (Bits.of_N 32 (Bits.to_N (Bits.of_list bs0) + 4)%N)
           ).
    {
      unfold stack_push_address.
      rewrite H1. simpl. auto.
    }
    assert (Bits.to_nat Ob~b1~b0~b < pow2 RV32I.ShadowStack.index_sz).
    change (Bits.to_nat Ob~b1~b0~b < pow2 3). simpl.
    apply Bits.to_nat_bounded.
    edestruct @index_of_nat_bounded as (idx & EQidx). apply H0.

    assert (WTtop:= WTRENV (RV32I.stack (RV32I.ShadowStack.stack idx))). simpl in WTtop.
    inv WTtop.

    assert (EQta: stack_top_address ctx =
                    Some (Bits.of_N 32 (Bits.to_N (Bits.of_list bs1)))
           ).
    {
      unfold stack_top_address.
      rewrite H3. simpl ubits_of_value.
      simpl Bits.of_list.
      setoid_rewrite EQidx. rewrite <- H7. reflexivity.
    }

    move H at bottom.
    assert (CONDS:
             stack_empty ctx /\ stack_pop ctx
             \/ stack_push ctx /\ ((stack_full ctx /\ ~ stack_pop ctx) \/ stack_top_address ctx <> stack_push_address ctx)).
    now intuition. clear H.
    rewrite EQse, EQspop, EQspush, EQsf, EQpa, EQta in CONDS.
    clear EQse EQspop EQspush EQsf EQpa EQta.
    move Legal at bottom.
    specialize (fun w => Legal _ w H1). simpl in Legal.
    specialize (Legal _ eq_refl). simpl in Legal. inv Legal.

    
    econstructor.
    native_compute. exact eq_refl.
    econstructor.
    econstructor. native_compute. exact eq_refl.
    

    







    edestruct @schedule_to_simple_form_ok as (WTVVS & VSV & _).
    apply wt_sigma. apply WTRENV. instantiate (1:=schedule). repeat constructor. reflexivity.
    apply rules_wt. apply WTRENV.
    assert (WTVVS2: wt_vvs RV32I.R (Sigma:=ext_Sigma) (vars sf2)).
    eapply wt_vvs_simplify_sf. apply WTRENV. eauto.
    assert (VSV2 : vvs_smaller_variables (vars sf2)).
    eapply vsv_simplify_sf. eauto.
    Time native_compute in sf2.
    native_compute in H1. apply Some_inj in H1. subst n.
    econstructor.
    native_compute. exact eq_refl.
    Set Printing Depth 20.

    Eval native_compute in Maps.PTree.get 1788 (vars sf2).
    Eval native_compute in Maps.PTree.get 991 (vars sf2).
    Eval native_compute in Maps.PTree.get 13 (vars sf2).

    set (sf3 :=inlining_pass sf2).

    set (sf3 := replace_all_occurrences sf2 )
    (* set (vv :=fold_left *)
    (*             (fun (t : Maps.PTree.t (type * sact)) (n : positive) => *)
    (*                match Maps.PTree.get n (vars sf2) with *)
    (*                | Some v => Maps.PTree.set n v t *)
    (*                | None => t *)
    (*                end) (reachable_vars_aux (vars sf2) 1789 [] 1790) *)
    (*             (Maps.PTree.empty (type * sact))). *)
    (* Time native_compute in vv. *)


    (* Time Eval native_compute in List.length (Maps.PTree.elements vv). *)

    (* Time Eval native_compute in List.length (Maps.PTree.elements (vars sf2)). *)
    (* Time Eval native_compute in List.length (Maps.PTree.elements (vars (remove_vars sf2))). *)

    (* remove_vars *)
    econstructor.
    econstructor. native_compute; reflexivity.
    econstructor. econstructor.
    econstructor. native_compute; reflexivity.
    econstructor.
    constructor. simpl.
    rewrite NoHalt. transitivity (Some (Bits [false])).
    clear. destruct val_eq_dec. inv e. auto. reflexivity.
    econstructor.
    econstructor.
    econstructor. native_compute; reflexivity.
    econstructor.
    rewrite Valid. simpl. reflexivity.
    instantiate (1:=Bits[false]). 2: simpl; reflexivity. 2: reflexivity.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    native_compute; reflexivity.
    econstructor.
    native_compute; reflexivity.
    econstructor. rewrite H2. simpl. reflexivity.
    econstructor.
    native_compute; reflexivity.
    econstructor. rewrite WTepoch. simpl.
    instantiate (1:=Bits [true]). clear. destr; auto.
    instantiate (1:=Bits [false]). 2: reflexivity.
    {
      econstructor.
      econstructor. econstructor. econstructor.
      econstructor. native_compute; reflexivity.
      econstructor. econstructor. native_compute; reflexivity.
      econstructor. native_compute; reflexivity.
      econstructor. rewrite H2; simpl. reflexivity.
      simpl; reflexivity. constructor.
      simpl. clear. destruct val_eq_dec; try congruence. eauto.
      simpl. eauto.
      instantiate (1:=Bits[false]). 2: reflexivity.
      econstructor. econstructor. econstructor.
      econstructor. econstructor. econstructor.
      econstructor. econstructor. native_compute; reflexivity.
      econstructor. native_compute; reflexivity.
      econstructor. econstructor. native_compute; reflexivity.
      econstructor. native_compute; reflexivity.
      econstructor. rewrite H2. simpl; eauto.
      simpl; eauto. econstructor. simpl. eauto. constructor.
      Eval native_compute in Bits.to_nat Ob~0~0~1~1~0.
      assert (is_ret_instruction (Bits.of_N 32 (Bits.to_N (Bits.of_list bs))) = true \/
                is_call_instruction (Bits.of_N 32 (Bits.to_N (Bits.of_list bs))) = true).
      { clear - CONDS. intuition. }
      {
        instantiate (1:=Bits [true]). clear -H H3.
        assert (eql (firstn 3 (skipn 4 (vect_to_list (bits_of_value (tau:=bits_t 32) (Bits.of_N 32 (Bits.to_N (Bits.of_list bs))))))) [true; true; false] = true).
        unfold is_ret_instruction, is_call_instruction in H.
        repeat rewrite andb_true_iff in H.
        intuition. clear H.
        Lemma eql_eq:
          forall l1 l2,
            eql l1 l2 = true -> l1 = l2.
        Proof.
          induction l1; simpl; intros; eauto.
          destruct l2; congruence.
          destruct l2. congruence.
          rewrite andb_true_iff in H. destruct H. apply eqb_prop in H. subst. f_equal. eauto.
        Qed.
        apply eql_eq in H0.
        Set Printing Depth 40.
        rewrite <- (Bits.to_N_rew _ H3) in H0.
        rewrite Bits.of_N_to_N in H0.
        simpl bits_of_value in H0.
        rewrite vect_to_list_eq_rect in H0.
        rewrite vect_to_list_of_list in H0.
        simpl in H0.
        destruct bs. congruence.
        destruct bs. congruence.
        destruct bs. congruence.
        destruct bs. congruence.
        destruct bs. congruence.
        destruct bs. congruence.
        destruct bs. congruence.
        inv H0. simpl. destruct val_eq_dec; try congruence.
      }
      econstructor. econstructor.
      econstructor. econstructor.
      native_compute; reflexivity.
      econstructor. native_compute; reflexivity.
      Set Printing Depth 20.
      econstructor. econstructor.
      native_compute; reflexivity.
      econstructor. native_compute; reflexivity.
      econstructor.
      rewrite H2; simpl; eauto. simpl; eauto. constructor.
      simpl. eauto. constructor. simpl.
      change (Bits.to_nat Ob~0~0~0~1~1) with 3%nat.
      instantiate (1:=Bits [false]).
      Set Printing Depth 100.
      rewrite H3. simpl.
      assert (is_ret_instruction (Bits.of_N 32 (Bits.to_N (Bits.of_list bs))) = true \/
                is_call_instruction (Bits.of_N 32 (Bits.to_N (Bits.of_list bs))) = true).
      { clear - CONDS. intuition. }
      Set Printing Depth 20.
      {
        clear -H H3.
        assert (eql (firstn 3 (skipn 4 (vect_to_list (bits_of_value (tau:=bits_t 32) (Bits.of_N 32 (Bits.to_N (Bits.of_list bs))))))) [true; true; false] = true).
        unfold is_ret_instruction, is_call_instruction in H.
        repeat rewrite andb_true_iff in H.
        intuition. clear H.
        apply eql_eq in H0.
        rewrite <- (Bits.to_N_rew _ H3) in H0.
        rewrite Bits.of_N_to_N in H0.
        simpl bits_of_value in H0.
        rewrite vect_to_list_eq_rect in H0.
        rewrite vect_to_list_of_list in H0.
        simpl in H0.
        destruct bs. congruence.
        destruct bs. congruence.
        destruct bs. congruence.
        destruct bs. congruence.
        destruct bs. congruence.
        destruct bs. congruence.
        destruct bs. congruence.
        inv H0. simpl. destruct val_eq_dec; try congruence.
      }
      simpl; reflexivity.
    }
    simpl orb.
    cbv iota.
    econstructor.
    native_compute; reflexivity.
    econstructor.
    econstructor.
    native_compute; reflexivity.
    econstructor. econstructor.
    econstructor.
    native_compute; reflexivity.
    econstructor.
    native_compute; reflexivity.
    econstructor. rewrite H2. simpl. reflexivity.
    econstructor.
    native_compute; reflexivity.
    econstructor. rewrite WTepoch.
    instantiate (1:=true). clear. simpl; destr; auto.
    cbv iota.
    econstructor. native_compute; reflexivity.
    econstructor.
    econstructor. native_compute; reflexivity.
    econstructor. econstructor.
    econstructor. native_compute; reflexivity.
    econstructor.
    econstructor. native_compute; reflexivity.
    econstructor. native_compute; reflexivity.
    econstructor. rewrite H2. simpl. reflexivity.
    simpl. reflexivity. constructor.
    simpl. instantiate (1:= negb x0).
    clear. destr. clear Heqs. inv e. reflexivity. clear Heqs.
    destruct x0; simpl; congruence.
    AAA
    rewrite H2. simpl. reflexivity.
    econstructor.
    native_compute; reflexivity.
    econstructor. rewrite WTepoch. simpl.
    
    simpl.
    Eval native_compute in Maps.PTree.get 96 (vars sf2).



    
    AAA
    simpl.
    dependent destruction H0. dependent destruction H0.
    dependent destruction H0. dependent destruction H0.
    dependent destruction H1. dependent destruction H1.
    dependent destruction H2. dependent destruction H2.
    dependent destruction H3. dependent destruction H3.
    dependent destruction H4. dependent destruction H4.
    dependent destruction H5. dependent destruction H5.
    dependent destruction H6. dependent destruction H6.
    dependent destruction H7. dependent destruction H7.
    dependent destruction H8. dependent destruction H8.
    dependent destruction H9. dependent destruction H9.
    move l1 before l0. move l2 before l1. move l3 before l2. move l4 before l3.
    move l5 before l4. move l6 before l5. move l7 before l6. move l8 before l7.
    move l9 before l8.
    dependent destruction H10.

    (* update_on_off *)
    unfold RV32I.update_on_off in H0.
    dependent destruction H0.
    invert_full H0.

    (* writeback *)
    unfold RV32I.writeback in H1.
    dependent destruction H1.
    invert_full H0.
    simpl in H38. injection H38 as H38.
    destruct (getenv REnv ctx RV32I.halt). cbn in H40.
    destruct (val_eq_dec (Bits sz v0) (Bits 1 [true])) in H40.
    subst.
  Qed.

  Lemma no_stack_violation_behaves_as_if_no_stack:
    forall (ctx: env_t REnv (fun _ : RV32I.reg_t => val)),
    not (stack_violation ctx) ->
    interp_n_cycles 1 ctx = interp_n_cycles_no_shadow_stack 1 ctx.
  Proof.
  Qed.

  (* Main theorem *)
  Theorem shadow_stack_ok:
    stack_violation_results_in_halt /\ halt_leads_to_a_sink_state
    /\ no_stack_violation_behaves_as_if_no_stack.
  Proof.
  Qed.
End ShadowStackProperties.
