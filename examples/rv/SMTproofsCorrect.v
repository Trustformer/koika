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
Require Import RVCoreProperties.
Require Import SMTproofs.

Section RVProofs.
  Context (ext_sigma : RV32I.ext_fn_t -> val -> val).
  Context (ext_Sigma : RV32I.ext_fn_t -> ExternalSignature).
  Context {REnv : Env RV32I.reg_t}.
  Variable ctx : env_t REnv (fun _ => val).
  Hypothesis WTRENV: Wt.wt_renv RV32I.R REnv ctx.

  Hypothesis wt_sigma: forall (ufn : RV32I.ext_fn_t) (vc : val),
    wt_val (arg1Sig (ext_Sigma ufn)) vc
    -> wt_val (retSig (ext_Sigma ufn)) (ext_sigma ufn vc).

  Hypothesis rules_wt:
    forall rule : rv_rules_t, exists t : type,
    wt_daction (Sigma:=ext_Sigma) (R:=RV32I.R) unit string string []
      (drules rule) t.

  Lemma no_mispred_ok:
    no_mispred ctx ->
    interp_sact (sigma:=ext_sigma) REnv ctx (vars sf) (sact_nomispred) (Bits [true]).
  Proof.
    intros. red in H.
    unfold sact_nomispred.
    generalize (WTRENV (RV32I.d2e RV32I.fromDecode.data0)). intro A. inv A.
    symmetry in H1.
    specialize (H _ H1).
    inv H2. inv H6. inv H7. inv H8. inv H9. inv H10. inv H11.
    econstructor. econstructor. econstructor. rewrite H1. simpl. eauto.
    econstructor. simpl. rewrite val_beq_true. auto.
  Qed.

  Lemma no_mispred_ok':
    interp_sact (sigma:=ext_sigma) REnv ctx (vars sf) (sact_nomispred) (Bits [true]) ->
    no_mispred ctx.
  Proof.
    intros. inv H. inv H3. inv H5.  inv H1. 
    generalize (WTRENV (RV32I.d2e RV32I.fromDecode.data0)). intro A. inv A.
    inv H1. inv H7. inv H8. inv H9. inv H10. inv H11. inv H12.
    rewrite <- H0 in H4. simpl in H4. inv H4.
    red. rewrite <- H0. intros v A. inv A. simpl. simpl in H6. destr_in H6.
    apply val_beq_correct in Heqb. subst. reflexivity.
    inv H6.
  Qed.

  Lemma sstack_empty_ok:
    sstack_empty ctx ->
    interp_sact (sigma:=ext_sigma) REnv ctx (vars sf) (sact_sstack_empty) (Bits [true]).
  Proof.
    intros. red in H.
    unfold sact_sstack_empty.
    econstructor. econstructor. econstructor.
    rewrite H. simpl. auto.
  Qed.


  Lemma sstack_full_ok:
    sstack_full ctx ->
    interp_sact (sigma:=ext_sigma) REnv ctx (vars sf) (sact_sstack_full) (Bits [true]).
  Proof.
    intros. red in H.
    unfold sact_sstack_full.
    econstructor. econstructor. econstructor.
    rewrite H. simpl. auto.
  Qed.


  Lemma is_call_instruction_ok: forall bv,
      is_call_instruction bv = true ->
      interp_sact (sigma:=ext_sigma) REnv ctx (vars sf) (sact_is_call_instruction (SConst (@val_of_value (bits_t 32) bv))) (Bits [true]).
  Proof.
    intros. unfold is_call_instruction in H.
    repeat rewrite ! andb_true_iff, !orb_true_iff in H. destruct H as (A & B).
    unfold sact_is_call_instruction.

    assert (forall n m, n + m <= 32 ->
                   interp_sact (sigma:=ext_sigma) REnv ctx (vars sf)
                     (SUnop (UBits1 (USlice n m)) (SConst (val_of_value bv)))
                     (Bits (firstn m (skipn n (vect_to_list (bits_of_value bv)))))
           ).
    {
      intros.
      econstructor. constructor. simpl.
      rewrite firstn_length. rewrite skipn_length. rewrite vect_to_list_length.
      replace (m - Init.Nat.min m (32 - n)) with O by lia.
      simpl. rewrite app_nil_r. auto.
    }
    econstructor. econstructor. apply H. lia. constructor.
    apply eql_iff in A. rewrite A. simpl. eauto.
    rewrite ! eql_iff in B. clear A.
    destruct B as [(B & [C|C])|(B & [C|C])];
      unfold or, and, equal, not;
      repeat
        match goal with
        | |- interp_sact (sigma:=ext_sigma) _ _ _ (SBinop (UBits2 _) _ _) _ => econstructor
        | |- interp_sact (sigma:=ext_sigma) _ _ _ (SBinop (UEq _) _ _) _ => econstructor
        | |- interp_sact (sigma:=ext_sigma) _ _ _ (SConst _) _ => econstructor
        | |- interp_sact (sigma:=ext_sigma) _ _ _ (SUnop (UBits1 (USlice _ _)) _) _ => apply H
        | HH: @Logic.eq (list bool) ?a (rev _) |- context [?a] => rewrite HH; simpl
        | |- Some _ = Some _ => eauto
        | |- _ <= 32 => lia
        end; simpl; eauto.
    simpl. auto.
  Qed.


  Lemma if_bool_true_false:
    forall b: bool, (if b then true else false) = b.
  Proof. destruct b; reflexivity. Qed.

  Lemma if_bool_false_true:
    forall b: bool, (if b then false else true) = negb b.
  Proof. destruct b; reflexivity. Qed.

  Lemma if_else_false_eq_true:
    forall (b:bool) x,
      (if b then x else false) = true <-> b && x = true.
  Proof.
    destruct b; simpl; tauto.
  Qed.


  Lemma is_call_instruction_ok_falase: forall bv,
      is_call_instruction bv = false ->
      interp_sact (sigma:=ext_sigma) REnv ctx (vars sf) (sact_is_call_instruction (SConst (@val_of_value (bits_t 32) bv))) (Bits [false]).
  Proof.
    destruct bv.
    do 30 destruct vtl. vm_compute.
    intros.
    eapply eval_sact_no_vars_interp.
    simpl.
    destr_in x.
    - rewrite !if_bool_true_false in *. rewrite !if_bool_false_true in *.
      repeat rewrite ? if_else_false_eq_true, ? andb_true_iff, ?negb_true_iff in *.
      destruct Heqb as (? & ? & ?); subst.
      destruct vhd, vhd0, vhd1, vhd2; simpl; try congruence.
      destruct vhd6, vhd7, vhd8, vhd9, vhd10; simpl in *; congruence.
      destruct vhd6, vhd7, vhd8, vhd9, vhd10; simpl in *; congruence.
      destruct vhd6, vhd7, vhd8, vhd9, vhd10; simpl in *; congruence.
      destruct vhd6, vhd7, vhd8, vhd9, vhd10; simpl in *; congruence.
      destruct vhd6, vhd7, vhd8, vhd9, vhd10; simpl in *; congruence.
      destruct vhd6, vhd7, vhd8, vhd9, vhd10; simpl in *; congruence.
      destruct vhd6, vhd7, vhd8, vhd9, vhd10; simpl in *; congruence.
      destruct vhd6, vhd7, vhd8, vhd9, vhd10; simpl in *; congruence.
      destruct vhd6, vhd7, vhd8, vhd9, vhd10; simpl in *; congruence.
      destruct vhd6, vhd7, vhd8, vhd9, vhd10; simpl in *; congruence.
      destruct vhd6, vhd7, vhd8, vhd9, vhd10; simpl in *; congruence.
      destruct vhd6, vhd7, vhd8, vhd9, vhd10; simpl in *; congruence.
      destruct vhd6, vhd7, vhd8, vhd9, vhd10; simpl in *; congruence.
      destruct vhd6, vhd7, vhd8, vhd9, vhd10; simpl in *; congruence.
      destruct vhd6, vhd7, vhd8, vhd9, vhd10; simpl in *; congruence.
      destruct vhd6, vhd7, vhd8, vhd9, vhd10; simpl in *; congruence.
    - rewrite !if_bool_true_false in *. rewrite !if_bool_false_true in *.
      destruct vhd3, vhd4, vhd5; simpl in *; try congruence;
        (destruct vhd, vhd0, vhd1, vhd2; simpl; try congruence;
          (destruct vhd6, vhd7, vhd8, vhd9, vhd10; simpl in *; congruence)).
  Qed.

  Lemma interp_and:
    forall a ba b bb,
      interp_sact (sigma:=ext_sigma) REnv ctx (vars sf) a (Bits [ba]) ->
      interp_sact (sigma:=ext_sigma) REnv ctx (vars sf) b (Bits [bb]) ->
      interp_sact (sigma:=ext_sigma) REnv ctx (vars sf) (SBinop (UBits2 UAnd) a b) (Bits [ba && bb]).
  Proof.
    intros. econstructor; eauto.
  Qed.

  Lemma interp_or:
    forall a ba b bb,
      interp_sact (sigma:=ext_sigma) REnv ctx (vars sf) a (Bits [ba]) ->
      interp_sact (sigma:=ext_sigma) REnv ctx (vars sf) b (Bits [bb]) ->
      interp_sact (sigma:=ext_sigma) REnv ctx (vars sf) (SBinop (UBits2 UOr) a b) (Bits [ba || bb]).
  Proof.
    intros. econstructor; eauto.
  Qed.


  Lemma is_ret_instruction_ok: forall bv,
      interp_sact (sigma:=ext_sigma) REnv ctx (vars sf) (sact_is_ret_instruction (SConst (@val_of_value (bits_t 32) bv))) (Bits [is_ret_instruction bv]).
  Proof.
    intros. (* eapply eval_sact_no_vars_interp. *)
    unfold sact_is_ret_instruction, is_ret_instruction.
    assert (SLICE: forall n m, n + m <= 32 ->
                          interp_sact (sigma:=ext_sigma) REnv ctx (vars sf)
                            (SUnop (UBits1 (USlice n m)) (SConst (val_of_value bv)))
                            (Bits (firstn m (skipn n (vect_to_list (bits_of_value bv)))))
           ).
    {
      intros.
      econstructor. constructor. simpl.
      rewrite firstn_length. rewrite skipn_length. rewrite vect_to_list_length.
      replace (m - Init.Nat.min m (32 - n)) with O by lia.
      simpl. rewrite app_nil_r. auto.
    }
    rewrite <- andb_assoc.
    apply interp_and.
    econstructor. apply SLICE. lia. constructor. simpl. now destr.
    apply interp_and.
    econstructor. apply SLICE. lia. constructor. simpl. now destr.
    apply interp_or. rewrite <- andb_assoc.
    apply interp_and.
    apply interp_or.
    econstructor. apply SLICE. lia. constructor.  Opaque firstn skipn eql. simpl. rewrite <- eql_list_eqb. now destr.
    econstructor. apply SLICE. lia. constructor.  Opaque firstn skipn eql. simpl. rewrite <- eql_list_eqb. now destr.
    apply interp_and.
    econstructor. apply SLICE. lia. apply SLICE. lia. Opaque firstn skipn eql. simpl. rewrite <- eql_list_eqb. now destr.
    apply interp_or.
    econstructor. apply SLICE. lia. constructor.  Opaque firstn skipn eql. simpl. rewrite <- eql_list_eqb. now destr.
    econstructor. apply SLICE. lia. constructor.  Opaque firstn skipn eql. simpl. rewrite <- eql_list_eqb. now destr.
    apply interp_and.
    apply interp_and.
    econstructor. apply SLICE. lia. constructor. Opaque firstn skipn eql. simpl. rewrite <- eql_list_eqb. now destr.
    econstructor. apply SLICE. lia. constructor. Opaque firstn skipn eql. simpl. rewrite <- eql_list_eqb. now destr.
    apply interp_or.
    econstructor. apply SLICE. lia. constructor.  Opaque firstn skipn eql. simpl. rewrite <- eql_list_eqb. now destr.
    econstructor. apply SLICE. lia. constructor.  Opaque firstn skipn eql. simpl. rewrite <- eql_list_eqb. now destr.
  Qed.


  Lemma is_call_instruction_ok2: forall bv,
      interp_sact (sigma:=ext_sigma) REnv ctx (vars sf) (sact_is_call_instruction (SConst (@val_of_value (bits_t 32) bv))) (Bits [is_call_instruction bv]).
  Proof.
    intros.
    unfold sact_is_call_instruction, is_call_instruction.
    assert (SLICE: forall n m, n + m <= 32 ->
                          interp_sact (sigma:=ext_sigma) REnv ctx (vars sf)
                            (SUnop (UBits1 (USlice n m)) (SConst (val_of_value bv)))
                            (Bits (firstn m (skipn n (vect_to_list (bits_of_value bv)))))
           ).
    {
      intros.
      econstructor. constructor. simpl.
      rewrite firstn_length. rewrite skipn_length. rewrite vect_to_list_length.
      replace (m - Init.Nat.min m (32 - n)) with O by lia.
      simpl. rewrite app_nil_r. auto.
    }
    apply interp_and.
    econstructor. apply SLICE. lia. constructor. simpl. rewrite <-eql_list_eqb. now destr.
    apply interp_or; apply interp_and.
    Opaque firstn skipn eql.
    econstructor. apply SLICE. lia. constructor. simpl. rewrite <- eql_list_eqb. now destr.
    apply interp_or.
    econstructor. apply SLICE. lia. constructor. simpl. rewrite <- eql_list_eqb. now destr.
    econstructor. apply SLICE. lia. constructor. simpl. rewrite <- eql_list_eqb. now destr.
    econstructor. apply SLICE. lia. constructor. simpl. rewrite <- eql_list_eqb. now destr.
    apply interp_or.
    econstructor. apply SLICE. lia. constructor. simpl. rewrite <- eql_list_eqb. now destr.
    econstructor. apply SLICE. lia. constructor. simpl. rewrite <- eql_list_eqb. now destr.
  Qed.

  Lemma is_ret_instruction_ext:
    forall sa sb,
      (forall x,
          interp_sact (sigma:=ext_sigma) REnv ctx (vars sf) sa x ->
          interp_sact (sigma:=ext_sigma) REnv ctx (vars sf) sb x
      ) ->
      forall x,
        interp_sact (sigma:=ext_sigma) REnv ctx (vars sf) (sact_is_ret_instruction sa) x ->
        interp_sact (sigma:=ext_sigma) REnv ctx (vars sf) (sact_is_ret_instruction sb) x.
  Proof.
    intros.
    unfold sact_is_ret_instruction in *.
    repeat unfold and, eqb, or, neq, neqb, equal in *.
    repeat match goal with
           | H: interp_sact (sigma:=ext_sigma) _ _ _ (SUnop _ _) _ |- _ =>
               inv H
           | H: interp_sact (sigma:=ext_sigma) _ _ _ (SBinop (UBits2 _) _ _) _ |- _ =>
               inv H
           | H: interp_sact (sigma:=ext_sigma) _ _ _ (SBinop (UEq _) _ _) _ |- _ =>
               inv H
           end.

    repeat match goal with
           | HH1: interp_sact (sigma:=ext_sigma) _ _ _ sa _,
               HH2: interp_sact (sigma:=ext_sigma) _ _ _ sa _|- _ =>
               generalize (interp_sact_determ REnv ctx _ _ _ HH1 _ HH2); let x := fresh in intro x; subst; clear HH1
           end.
    repeat match goal with
           | HH: interp_sact (sigma:=ext_sigma) _ _ _ sa _ |- _ =>
               apply H in HH
           end.
    repeat match goal with
           | |-    interp_sact (sigma:=ext_sigma) _ _ _ (SUnop _ _) _  => econstructor; eauto
           | |- interp_sact (sigma:=ext_sigma) _ _ _ (SBinop (UBits2 _) _ _) _ =>
               econstructor; eauto
           | |- interp_sact (sigma:=ext_sigma) _ _ _ (SBinop (UEq _) _ _) _ =>
               econstructor; eauto
           end;

      repeat match goal with
        | H: interp_sact (sigma:=ext_sigma) _ _ _ (SConst _) _ |- _ =>
            inv H
        end;
      repeat match goal with
        | H1: ?a = _, H2: ?a = _ |- _ => rewrite H1 in H2; inv H2 end.
    all: auto.
  Qed.

  Lemma sstack_pop_ok:
    sstack_pop ctx ->
    interp_sact (sigma:=ext_sigma) REnv ctx (vars sf) (sact_sstack_pop) (Bits [true]).
  Proof.
    intros.
    unfold sact_sstack_pop, sstack_pop.
    red in H.
    generalize (WTRENV (RV32I.d2e RV32I.fromDecode.data0)). intro A. inv A.
    inv H1. inv H2. inv H6. inv H7. inv H8. inv H9. inv H10. inv H11. symmetry in H3.
    inv H6. inv H1. inv H11. inv H12. inv H13. inv H14. inv H15. inv H16.
    specialize (fun w b => H _ w b H3). simpl in H.
    specialize (fun b => H _ b eq_refl). simpl in H.
    inv H12.
    specialize (H _ eq_refl).

    eapply is_ret_instruction_ext.
    2:{
      rewrite <- H. apply is_ret_instruction_ok.
    }
    intros. inv H0.
    econstructor. econstructor. econstructor. rewrite H3. simpl. eauto. simpl.
    rewrite <- (Bits.to_N_rew _ H1).
    setoid_rewrite Bits.of_N_to_N.
    rewrite vect_to_list_eq_rect. rewrite vect_to_list_of_list. auto.
  Qed.

  Lemma sstack_pop_ok':
    interp_sact (sigma:=ext_sigma) REnv ctx (vars sf) (sact_sstack_pop) (Bits [true]) ->
    sstack_pop ctx.
  Proof.
    intros.
    unfold sact_sstack_pop, sstack_pop.
    assert (SLICE: forall (bv: type_denote (bits_t 32)) n m sa x,
               n + m <= 32 ->
               interp_sact (sigma:=ext_sigma) REnv ctx (vars sf) sa ( (val_of_value bv)) ->
               interp_sact (sigma:=ext_sigma) REnv ctx (vars sf)
                 (SUnop (UBits1 (USlice n m)) sa)
                 x ->
               x = (Bits (firstn m (skipn n (vect_to_list (bits_of_value bv)))))
           ).
    {
      intros. inv H2. exploit @interp_sact_determ. apply H1. apply H5. intros <-. inv H7.
      rewrite firstn_length. rewrite skipn_length. rewrite vect_to_list_length.
      replace (m - Init.Nat.min m (32 - n)) with O by lia.
      simpl. rewrite app_nil_r. auto.
    }

    intros v w b REG GFS GFS2. simpl in GFS. repeat destr_in GFS; inv GFS.
    simpl in GFS2. repeat destr_in GFS2; inv GFS2.

    assert(X:interp_sact (sigma:=ext_sigma) REnv ctx (vars sf)
               (SUnop (UStruct1 (UGetField "inst"))
                  (SUnop (UStruct1 (UGetField "dInst")) (SReg (RV32I.d2e RV32I.fromDecode.data0)))) 
               (val_of_value (tau:=bits_t (Datatypes.length b)) (vect_of_list b))).
    {
      econstructor. econstructor. econstructor. rewrite REG. simpl. eauto. simpl; eauto.
      rewrite vect_to_list_of_list. auto.
    }
    unfold sact_sstack_pop in H.
    eapply is_ret_instruction_ext in H.
    exploit is_ret_instruction_ok. intros A.
    exploit @interp_sact_determ. apply H. apply A. intro B. inv B. rewrite H1. reflexivity.
    intros x A.
    exploit @interp_sact_determ. apply A. apply X. intros ->.
    cut (Datatypes.length b = 32). intro LEN.
    replace (Bits.to_N (sz:=Datatypes.length b) (Bits.of_list b)) with
      (Bits.to_N (sz:=32) (rew [Bits.bits] LEN in (Bits.of_list b))).
    2: apply (Bits.to_N_rew _ LEN).
    rewrite Bits.of_N_to_N.
    unfold val_of_value.
    rewrite vect_to_list_eq_rect. rewrite vect_to_list_of_list. constructor.

    exploit WTRENV. rewrite REG. intro WT; inv WT. inv H2. inv H6. inv H7. inv H8. inv H9. inv H6.
    inv H7. inv H11. inv H12. inv H13. inv H14. inv H12. auto.
  Qed.

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



  Lemma switch_interp:
    forall discr bodies cond body bodies2 default v,
    Forall (fun '(cond,_) => interp_sact (sigma:=ext_sigma) REnv ctx (vars sf) (equal discr cond) (Bits [false])) bodies ->
    interp_sact (sigma:=ext_sigma) REnv ctx (vars sf) (equal discr cond) (Bits [true]) ->
    interp_sact (sigma:=ext_sigma) REnv ctx (vars sf) body v ->
    interp_sact (sigma:=ext_sigma) REnv ctx (vars sf) (switch discr (bodies ++ (cond,body) :: bodies2) default) v.
  Proof.
    induction bodies.
    - intros. simpl app. simpl switch.
      econstructor. eauto. cbv iota. auto.
    - intros. inv H. destruct a. simpl switch.
      econstructor. eauto. cbv iota. apply IHbodies; auto.
  Qed.

  Lemma idx_switch_interp:
    forall n sz (GE: pow2 n >= sz) discr bodies default idx v,
    interp_sact (sigma:=ext_sigma) REnv ctx (vars sf) discr ((Bits (vect_to_list (Bits.of_index n idx)))) ->
    interp_sact (sigma:=ext_sigma) REnv ctx (vars sf) (bodies idx) v ->
    interp_sact (sigma:=ext_sigma) REnv ctx (vars sf) (idx_switch n sz discr bodies default) v.
  Proof.
    intros.
    edestruct (in_split idx (vect_to_list (all_indices sz))) as (l1 & l2 & EQ).
    rewrite <- vect_to_list_In. apply vect_to_list_In. apply member_In. apply all_indices_surjective.
    unfold idx_switch. rewrite EQ.
    rewrite map_app. simpl map.
    eapply switch_interp.
    generalize (all_indices_NoDup sz). unfold vect_NoDup. rewrite EQ.
    intros.
    cut (Forall (fun i => i <> idx) l1).
    rewrite Forall_map.
    apply Forall_impl.
    {
      intros.
      econstructor. eauto. econstructor.
      simpl. destr.
      apply list_eqb_correct in Heqb. 2: apply eqb_true_iff.
      apply vect_to_list_inj in Heqb.
      unfold Bits.of_index in Heqb.
      apply (f_equal Bits.to_nat) in Heqb.
      rewrite ! Bits.to_nat_of_nat in Heqb.
      2-3: eapply lt_le_trans; [apply index_to_nat_bounded | lia].
      apply index_to_nat_injective in Heqb. congruence.
    }
    apply NoDup_remove in H1. destruct H1 as (_ & H1).
    rewrite Forall_forall; intros. intro; subst. apply H1. apply in_app_iff. auto.
    econstructor. eauto. constructor. simpl.
    rewrite list_eqb_refl. 2: apply eqb_reflx. auto. auto.
  Qed.

  Lemma sact_sstack_top_address_ok:
    forall bs x,
      ~ sstack_empty ctx ->
      sstack_top_address ctx = Some bs ->
      interp_sact (sigma:=ext_sigma) REnv ctx (vars sf) sact_sstack_top_address x ->
      x = Bits (vect_to_list bs).
  Proof.
    intros bs x NOTEMPTY H H0.
    unfold sstack_top_address in H. destr_in H; inv H.
    generalize (WTRENV (RV32I.sstack RV32I.ShadowStack.size)). intro A. inv A.
    rewrite <- H1 in Heqo.
    change (log2 8) with 3 in H2.
    destruct bs; simpl in H2; try congruence.
    destruct bs; simpl in H2; try congruence.
    destruct bs; simpl in H2; try congruence.
    destruct bs; simpl in H2; try congruence.
    exploit @interp_sact_determ. apply H0.
    eapply idx_switch_interp. lia. econstructor. constructor. constructor. simpl. rewrite <- H1.
    instantiate (1:=i). simpl.

    destruct b, b0, b1; simpl in Heqo; inv Heqo; simpl; try reflexivity.
    unfold sstack_empty in NOTEMPTY. rewrite <- H1 in NOTEMPTY. vm_compute in NOTEMPTY. congruence.
    econstructor. intro; subst.

    clear - WTRENV.
    generalize (WTRENV (RV32I.sstack (RV32I.ShadowStack.stack i))). intro A. inv A.
    clear H0. simpl.
    rewrite <- (Bits.to_N_rew _ H1).
    setoid_rewrite Bits.of_N_to_N.
    rewrite vect_to_list_eq_rect. rewrite vect_to_list_of_list. auto.
  Qed.

  Definition consistent_imm_type :=
    forall v2
      (GET: BitsToLists.get_field (getenv REnv ctx (RV32I.d2e RV32I.fromDecode.data0)) "dInst" = Some v2
      )
        inst_v (InstV: BitsToLists.get_field v2 "inst" = Some (Bits inst_v))
        (eqn: Datatypes.length inst_v = 32)
        (IRI: RVCoreProperties.is_ret_instruction (rew [Bits.bits] eqn in (vect_of_list inst_v)) = true),
          BitsToLists.get_field v2 "immediateType"
          = Some
              (Struct
                (Std.Maybe (enum_t imm_type))
                [Bits [true]; Enum imm_type [false; false; false]]).

  Ltac invForall2 :=
    repeat match goal with
             H: Forall2 _ _ _ |- _ => inv H
           end.


  Lemma interp_eqb_ext_l:
    forall a a' b
      (IB: forall x,
          interp_sact (sigma:=ext_sigma) REnv ctx (vars sf) a' x ->
           interp_sact (sigma:=ext_sigma) REnv ctx (vars sf) a x
      )
      x,
    interp_sact (sigma:=ext_sigma) REnv ctx (vars sf) (equal a' b) x ->
    interp_sact (sigma:=ext_sigma) REnv ctx (vars sf) (equal a b) x.
  Proof.
    intros.
    inv H. apply IB in H3. econstructor; eauto.
  Qed.

  Lemma interp_unop_ext:
    forall a a' ufn
      (IB: forall x,
          interp_sact (sigma:=ext_sigma) REnv ctx (vars sf) a' x ->
          interp_sact (sigma:=ext_sigma) REnv ctx (vars sf) a x
      )
      x,
    interp_sact (sigma:=ext_sigma) REnv ctx (vars sf) (SUnop ufn a') x ->
    interp_sact (sigma:=ext_sigma) REnv ctx (vars sf) (SUnop ufn a) x.
  Proof.
    intros.
    inv H. econstructor; eauto.
  Qed.


  Lemma interp_eqb_r:
    forall a b c
      (IB: interp_sact (sigma:=ext_sigma) REnv ctx (vars sf) b (Bits c))
      x,
    interp_sact (sigma:=ext_sigma) REnv ctx (vars sf) (eqb a c) x ->
    interp_sact (sigma:=ext_sigma) REnv ctx (vars sf) (equal a b) x.
  Proof.
    intros.
    inv H. inv H5. econstructor; eauto.
  Qed.

  (* Lemma consistent_imm: *)
  (*   consistent_imm_type -> *)
  (*   interp_sact (sigma:=ext_sigma) REnv ctx (vars sf) (SMTproofs.consistent_imm_type) (Bits [true]). *)
  (* Proof. *)
  (*   unfold consistent_imm_type, SMTproofs.consistent_imm_type. *)
  (*   intros. *)
  (*   generalize (WTRENV (RV32I.d2e RV32I.fromDecode.data0)). intro. *)
  (*   inv H0. rewrite <- H2 in H. *)
  (*   invForall2. *)
  (*   specialize (H _ eq_refl). *)
  (*   inv H6. invForall2. inv H13. invForall2. *)
  (*   inv H12. *)
  (*   specialize (H _ eq_refl H1). *)
  (*   simpl in H. *)
  (*   generalize (is_ret_instruction_ok (rew [Bits.bits] H1 in Bits.of_list bs)). intro A. *)
  (*   inv A. *)
  (*   repeat rewrite vect_to_list_eq_rect in H16. *)
  (*   repeat rewrite vect_to_list_eq_rect in H18. *)
  (*   rewrite vect_to_list_of_list in *. *)
  (*   inv H18. *)
  (*   econstructor. econstructor. econstructor. eauto. *)
  (*   eapply interp_eqb_ext_l. apply interp_unop_ext. *)
  (*   intros. econstructor. *)
  (*   econstructor. econstructor. rewrite <- H2. simpl. eauto. *)
  (*   simpl. revert H0. instantiate (1 := SConst (Bits bs)). intro. inv H0. auto. *)
  (*   eauto. *)

  (*   eapply interp_eqb_ext_l. apply interp_unop_ext. *)
  (*   intros. econstructor. *)
  (*   econstructor. econstructor. rewrite <- H2. simpl. eauto. *)
  (*   simpl. revert H0. instantiate (1 := SConst (Bits bs)). intro. inv H0. auto. *)
  (*   eauto. *)


  (* Qed. *)


End RVProofs.
