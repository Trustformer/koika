(*! Proofs about our RISC-V implementation !*)
Require Import Coq.Program.Equality.
Require Import Koika.BitsToLists Koika.Frontend Koika.Logs
  Koika.ProgramTactics Koika.SimpleTypedSemantics Koika.Std Koika.UntypedLogs
  UntypedIndSemantics Koika.UntypedSemantics.
Require Export rv.Instructions rv.ShadowStack rv.RVCore rv.rv32 rv.rv32i.
Require Import Koika.SimpleForm Koika.SimpleFormInterpretation.
(* Require Import Koika.SimpleFormInterpretationb Koika.SimpleFormb. *)
Require Import SimpleVal.

Ltac destr_in H :=
  match type of H with
  | context[match ?a with _ => _ end] => destruct a eqn:?
  end.

Ltac destr :=
  match goal with
  |- context[match ?a with _ => _ end] => destruct a eqn:?; try congruence
  end.

Ltac inv H := inversion H; try subst; clear H.

Module RVProofs.
  Context (ext_sigma : RV32I.ext_fn_t -> val -> val).
  Context (ext_Sigma : RV32I.ext_fn_t -> ExternalSignature).
  Context {REnv : Env RV32I.reg_t}.

  Check (desugar_action tt (RV32I.rv_urules Fetch)).
  Definition drules rule :=
    match uaction_to_daction (desugar_action tt (RV32I.rv_urules rule)) with
    | Some d => d
    | None => DFail unit_t
    end.

  Set Typeclasses Debug.
  Instance eq_dec_reg: EqDec RV32I.reg_t := EqDec_FiniteType.
  Existing Instance etaRuleInformationRaw.


  Section test1.
    Variable REnv: Env RV32I.reg_t.
    Variable ctx : env_t REnv (fun _ => val).
    Hypothesis WTRENV: Wt.wt_renv RV32I.R REnv ctx.

    Hypothesis wt_sigma: forall (ufn : RV32I.ext_fn_t) (vc : val),
        wt_val (arg1Sig (ext_Sigma ufn)) vc ->
        wt_val (retSig (ext_Sigma ufn)) (ext_sigma ufn vc).

    Hypothesis rules_wt:
      forall rule : rv_rules_t,
      exists t : type, wt_daction (Sigma:=ext_Sigma) (R:=RV32I.R) unit string string [] (drules rule) t.

    (* Lemma update_on_off_failure: *)
    (*   forall nid r2v vss sched_rir rir r2v' nid' , *)
    (*     get_rule_information RV32I.R (Sigma:=ext_Sigma) (drules UpdateOnOff) nid r2v vss sched_rir = *)
    (*       (rir, r2v', nid') -> *)
    (*     wf_state  (Sigma:=ext_Sigma) RV32I.R [] [] r2v vss init_rir nid -> *)
    (*     forall r2v0 nid0, *)
    (*     wf_state RV32I.R (Sigma:=ext_Sigma) [] [] r2v0 (rir_vars sched_rir) sched_rir nid0 -> *)
    (*     vvs_grows (rir_vars sched_rir) vss -> *)
    (*     interp_sact REnv (sigma:=ext_sigma) ctx (rir_vars sched_rir) *)
    (*                   (uor *)
    (*                      (rir_has_write0 sched_rir RV32I.on_off) *)
    (*                      (rir_has_write1 sched_rir RV32I.on_off)) (Bits [false]) -> *)
    (*       interp_sact REnv (sigma:=ext_sigma) ctx (rir_vars rir) *)
    (*                   (rir_failure_cond rir) (Bits [false]). *)
    (* Proof. *)
    (*   intros nid r2v vss sched_rir rir r2v' nid' GRI WFS r2v0 nid0 WFR VG ONOFFNoWrite. *)
    (*   unfold get_rule_information in GRI. *)
    (*   repeat destr_in GRI. inv GRI. simpl. *)
    (*   cbn in Heqp. *)
    (*   edestruct (@wfs_r2v_vvs) as (y & GET1 & z & GET2). apply WFS. *)
    (*   rewrite GET1 in Heqp. *)
    (*   inv Heqp. *)
    (*   apply interp_uor_false2. *)
    (*   apply interp_uor_false2. *)
    (*   eapply vvs_grows_interp_sact. eapply vvs_grows_set. apply WFS. lia. *)
    (*   eapply vvs_grows_interp_sact. 2: apply ONOFFNoWrite. auto. *)
    (*   repeat constructor. *)
    (*   econstructor. constructor. unfold or_conds. simpl. *)
    (*   instantiate (1:=Bits [false]). 2: reflexivity. *)
    (*   change (rir_has_write1 (add_read0 init_rir const_true RV32I.on_off) RV32I.on_off) *)
    (*     with (rir_has_write1 (ext_fn_t:=RV32I.ext_fn_t) init_rir RV32I.on_off). *)
    (*   econstructor. *)
    (*   instantiate (1:=Bits [false]). *)
    (*   2: instantiate (1:=Bits [false]). *)
    (*   3: reflexivity. *)
    (*   econstructor. econstructor. *)
    (*   unfold rir_has_write1, init_rir. simpl. econstructor. reflexivity. *)
    (*   Sact.exploit @wt_rir_has_write0. apply WFR. *)
    (*   Sact.exploit @wt_rir_has_write1. apply WFR. *)
    (*   inv ONOFFNoWrite. *)
    (*   intros WT1 WT2. *)
    (*   Sact.exploit @interp_sact_wt. apply wt_sigma. apply WTRENV. 4: apply WT1. 1-3: apply WFR. *)
    (*   apply H4. intro WTv1. *)
    (*   Sact.exploit @interp_sact_wt. apply wt_sigma. apply WTRENV. 4: apply WT2. 1-3: apply WFR. *)
    (*   apply H2. intro WTv2. *)
    (*   apply Sact.wt_val_bool in WTv1. *)
    (*   apply Sact.wt_val_bool in WTv2. *)
    (*   destruct WTv1, WTv2. subst. simpl in H5. inv H5. *)
    (*   apply orb_false_iff in H0. destruct H0; subst. *)
    (*   eapply vvs_grows_interp_sact. 2: apply H4. *)
    (*   eapply vvs_grows_trans. eauto. eapply vvs_grows_set. apply WFS. lia. *)
    (* Qed. *)

    Definition simplify_sf  sf ctx :=
      {|
        final_values := final_values sf;
        vars := Maps.PTree.map (fun _ '(t,a) => (t, simplify_sact (REnv:=REnv) (reg_t:=RV32I.reg_t) ctx ext_sigma a)) (vars sf)

      |}.
    
    Lemma fail_schedule:
      forall ss1,
        (remove_vars_for_var (schedule_to_simple_form
                                  RV32I.R (Sigma:=ext_Sigma) drules
                                  (UpdateOnOff |> Writeback |> Execute (* |> Decode |> WaitImem *)
                                               (* |> Fetch |> Imem |> Dmem |> Tick *)
                                               (* |> EndExecution  *)|> done)) RV32I.halt) = Some ss1 ->
        let ss := simplify_sf ss1 ctx in
        forall n t s,
        list_assoc (final_values ss) RV32I.halt = Some n ->
        Maps.PTree.get n (vars ss) = Some (t,s) ->
        do_eval_sact ctx ext_sigma (vars ss) s = Some (Bits [true])
    .
    Proof.
      intros.
      Set Printing Depth 20.
      Time native_compute in H. injection H. clear H.
      intro A.
      subst ss1.
      Time native_compute in ss.
      Eval native_compute in List.length (Maps.PTree.elements (vars ss)).
      native_compute in H0.
      apply Some_inj in H0. subst n.
      native_compute in H1.
      apply Some_inj in H1.
      apply pair_inj in H1. destruct H1 as (_ & EQs). subst s.
      cut (eval_sact ctx ext_sigma (vars ss) (SIf (SVar 1788) (SVar 96) (SVar 1758)) 4100 = Some (Bits [true])).
      intro B; unfold do_eval_sact; rewrite <- B; f_equal. 
      Eval native_compute in
        Maps.PTree.fold (fun acc k a =>
                           (k, regs_in_sact_aux (snd a) [])::acc
                        ) (vars ss) [].
      Eval native_compute in useful_regs_for_var ss 1789.

      set (ss2 := simplify_sf {| final_values := final_values ss; vars := replace_reg_in_vars (vars ss) RV32I.halt (Bits [true]) |} ctx).
      native_compute in ss2.
      replace ss with ss2 by admit. clear ss. rename ss2 into ss.
      
      

      native_compute in ss2.
      replace ss with ss2 by admit. clear ss. rename ss2 into ss.
      

      Lemma eval_sact_if:
        forall ext_fn_t P sigma vvs c t f fuel,
          (* wt_sact R (Sigma:=Sigma) vvs c (bits_t 1) -> *)
          P (eval_sact ctx sigma vvs t fuel) ->
          P (eval_sact ctx sigma vvs f fuel) ->
          P (eval_sact ctx sigma vvs (SIf (ext_fn_t:=ext_fn_t) c t f) (S fuel)).
      Proof.
      Admitted.
      change 10186 with (S 10185).
      apply eval_sact_if.
      change 10185 with (S 10184).
      simpl. auto.
      admit.
      change 10185 with (S 10184).
      unfold eval_sact. fold (eval_sact ctx ext_sigma (vars ss2)).
      native_compute Maps.PTree.get. unfold opt_bind.
      Time Eval native_compute in Maps.PTree.get 992 (vars ss2).
      Time Eval native_compute in Maps.PTree.get 93 (vars ss2).      
      Time Eval native_compute in Maps.PTree.get 991 (vars ss2).      
      Time Eval native_compute in Maps.PTree.get 49 (vars ss2).
      Eval native_compute in List.length (Maps.PTree.elements (vars ss2)).
      set (ip:= inlining_pass ctx ext_sigma ss2).
      Time native_compute in ip.
      assert (eval_sact ctx ext_sigma (vars ss) (SIf (SVar 1788) (SVar 96) (SVar 1758)) 20 = Some (Bits [false])).
      rewrite <- A; native_compute.
      destr.
      native_compute in H1. inv H1.
      simpl.
      

      set (regs:= useful_regs_for_var ss 1789).
      Time native_compute in regs.

      assert (Forall (fun x => wt_val (RV32I.R x) (getenv REnv ctx x)) regs).
      rewrite Forall_forall; intros. apply WTRENV. unfold regs in H.
      repeat match goal with
             | H: Forall _ [] |- _ => clear H
             | H: Forall _ (_::_) |- _ =>
                 let a := fresh "a" in
                 let b := fresh "b" in
                 let c := fresh "c" in
                 let d := fresh "d" in
                 let e := fresh "e" in
                 inversion H as [|a b c d e]; subst a b; simpl in c; clear H
             | H: wt_val (bits_t 1) _ |- _ => apply Sact.wt_val_bool in H; destruct H; subst
             end.

      assert (do_eval_sact ctx ext_sigma (vars ss)
                           (match Maps.PTree.get 1789 (vars ss) with
                            | Some (_,s) => s
                            | None => const_false
                            end) = Some (Bits [false])
             ).
      unfold do_eval_sact.
      Eval native_compute in (Pos.to_nat (Pos.succ (max_var (vars ss))) +
     vvs_size (vars ss) (Pos.succ (max_var (vars ss))) +
     size_sact
       match Maps.PTree.get 1789 (vars ss) with
       | Some (_, s0) => s0
       | None => const_false
       end) .
      change (eval_sact ctx ext_sigma (vars ss)
                        match Maps.PTree.get 1789 (vars ss) with
                        | Some (_, s0) => s0
                        | None => const_false
                        end
                        4100 = Some (Bits [false])).
      rewrite (interp_sact_replace_reg_sact_vars _ _ _ _ _ H4).
      rewrite (interp_sact_replace_reg_sact_vars _ _ _ _ _ H3).
      rewrite (interp_sact_replace_reg_sact_vars _ _ _ _ _ H2).
      rewrite (interp_sact_replace_reg_sact_vars _ _ _ _ _ H1).
      Time native_compute.

      assert (WT := WTRENV RV32I.halt). simpl in WTHALT.


      set (ks := PosSort.sort (map fst (Maps.PTree.elements (vars ss)))).
      Time native_compute in ks.
      set (ss2 :=
             fst (fold_left
                    (fun '(sf0, l) (var : positive) =>
                       let '(sf1, l1) := simplify_var ctx ext_sigma sf0 var in (sf1, l1 ++ l)) ks
                    (ss, []) )).
      Time native_compute in ss2.
      Eval native_compute in list_assoc (final_values ss) RV32I.halt.
      Eval native_compute in Maps.PTree.get 1789 (vars ss).
      Eval native_compute in
        (option_map (fun '(_,a) => InstructionsProperties.remove_dups (vars_in_sact a) Pos.eqb) (Maps.PTree.get 1788 (vars ss))
        ).
      

      set (ip:= inlining_pass ctx ext_sigma ss).
      Time native_compute in ip.

        schedule_to_simple_form RV32I.R (Sigma:=ext_Sigma) drules (Writeback |> done).
      
      cbn in Heqp.
      edestruct (@wfs_r2v_vvs) as (y & GET1 & z & GET2). apply WFS.
      rewrite GET1 in Heqp.
      inv Heqp.
      apply interp_uor_false2.
      apply interp_uor_false2.
      eapply vvs_grows_interp_sact. eapply vvs_grows_set. apply WFS. lia.
      eapply vvs_grows_interp_sact. 2: apply ONOFFNoWrite. auto.
      repeat constructor.
      econstructor. constructor. unfold or_conds. simpl.
      instantiate (1:=Bits [false]). 2: reflexivity.
      change (rir_has_write1 (add_read0 init_rir const_true RV32I.on_off) RV32I.on_off)
        with (rir_has_write1 (ext_fn_t:=RV32I.ext_fn_t) init_rir RV32I.on_off).
      econstructor.
      instantiate (1:=Bits [false]).
      2: instantiate (1:=Bits [false]).
      3: reflexivity.
      econstructor. econstructor.
      unfold rir_has_write1, init_rir. simpl. econstructor. reflexivity.
      Sact.exploit @wt_rir_has_write0. apply WFR.
      Sact.exploit @wt_rir_has_write1. apply WFR.
      inv ONOFFNoWrite.
      intros WT1 WT2.
      Sact.exploit @interp_sact_wt. apply wt_sigma. apply WTRENV. 4: apply WT1. 1-3: apply WFR.
      apply H4. intro WTv1.
      Sact.exploit @interp_sact_wt. apply wt_sigma. apply WTRENV. 4: apply WT2. 1-3: apply WFR.
      apply H2. intro WTv2.
      apply Sact.wt_val_bool in WTv1.
      apply Sact.wt_val_bool in WTv2.
      destruct WTv1, WTv2. subst. simpl in H5. inv H5.
      apply orb_false_iff in H0. destruct H0; subst.
      eapply vvs_grows_interp_sact. 2: apply H4.
      eapply vvs_grows_trans. eauto. eapply vvs_grows_set. apply WFS. lia.
    Qed.

        

    Goal
      let s := schedule_to_simple_form (Sigma:=ext_Sigma) RV32I.R drules (Tick |> done) in
      (Maps.PTree.get 278%positive (vars s)) = None.
      intros.
      Time native_compute in s.
      set (r:= remove_vars s).
      Time native_compute in r.
      replace (vars s) with (vars r) by admit.
      clear s.
      Eval native_compute in list_assoc  (final_values r) RV32I.cycle_count.
      Eval native_compute in Maps.PTree.get 102 (vars r).
      Eval native_compute in Maps.PTree.get 101 (vars r).
      (*      = Some (bits_t 1, SIf (SVar 901) (SVar 96) (SVar 871)) *)
      Eval native_compute in option_map (fun '(_,a) => simplify_sact ctx a) (Maps.PTree.get 101 (vars r)).
      Eval native_compute in Maps.PTree.get 90 (vars r).
      Eval native_compute in Maps.PTree.get 100 (vars r).

      Eval native_compute in option_map (fun '(_,a) => simplify_sact ctx a) (Maps.PTree.get 96 (vars r)).

      Eval native_compute in
        option_map (fun s =>do_eval_sact ctx ext_sigma (vars r) s)
                   (option_map (fun '(_,a) => simplify_sact ctx a) (Maps.PTree.get 13 (vars r))).
      Eval native_compute in option_map (fun '(_,a) => simplify_sact ctx a) (Maps.PTree.get 114 (vars r)).
      assert (WTHALT := WTRENV RV32I.halt). simpl in WTHALT.
      assert (WTVALID0 := WTRENV (RV32I.d2e RV32I.fromDecode.valid0)). simpl in WTVALID0.
      assert (WTDATA0 := WTRENV (RV32I.d2e RV32I.fromDecode.data0)). simpl in WTDATA0.
      Ltac minv := repeat match goal with
             | H: Forall2 _ (_::_) _ |- _ => inv H
             | H: Forall2 _ [] _ |- _ => inv H
             | H: wt_val (bits_t 1) _ |- _ => apply Sact.wt_val_bool in H; destruct H as (? & H); subst
             | H: wt_val _ _ |- _ => inv H;[idtac]
                          end.
      minv. inv H1. minv.
      
      set (vv := replace_all_occurrences_in_vars (vars r) 96 (Bits [x0])).
      Time native_compute in vv.
      replace (vars r) with (vv) by admit. clear r.
      Eval native_compute in option_map (fun '(_,a) => a) (Maps.PTree.get 901 vv).

      Eval native_compute in simplify_sact ctx
                                           (SBinop (UBits2 UAnd)
                                                   (SBinop (UEq false) (SConst (Bits [x0])) (SConst (Bits [true])))
                                                   (SVar 12)).
      Eval native_compute in val_eq_dec (Bits [x0]) (Bits [true]).
      Eval native_compute in eval_sact_no_vars ctx ext_sigma (SBinop (UEq false) (SConst (Bits [x0])) (SConst (Bits [true]))).
      (*      = Some
         (SBinop (UBits2 UOr)
            (SBinop (UEq false) (SVar 96) (SConst (Bits [true])))
            (SBinop (UBits2 UOr) (SUnop (UBits1 UNot) (SVar 14))
               (SBinop (UBits2 UAnd)
                  (SBinop (UEq false)
                     (SUnop (UStruct1 (UGetField "epoch")) (SVar 104))
                     (SVar 93))
                  (SBinop (UBits2 UAnd)
                     (SUnop (UBits1 UNot)
                        (SBinop (UEq false)
                           (SUnop (UStruct1 (UGetField "legal")) (SVar 108))
                           (SConst (Bits [false]))))
                     (SBinop (UBits2 UOr)
                        (SBinop (UBits2 UOr)
                           (SBinop (UBits2 UAnd)
                              (SBinop (UBits2 UAnd)
                                 (SBinop (UEq false)
                                    (SBinop (UBits2 USel)
                                       (SUnop (UStruct1 (UGetField "inst"))
                                          (SVar 243))
                                       (SConst
                                          (Bits
                                             [false; true; true; false;
                                             false])))
                                    (SConst (Bits [false])))
                                 (SBinop (UEq false)
                                    (SBinop (UBits2 (UIndexedSlice 2))
                                       (SUnop (UStruct1 (UGetField "inst"))
                                          (SVar 243))
                                       (SConst
                                          (Bits
                                             [true; true; false; false;
                                             false])))
                                    (SConst (Bits [false; false]))))
                              (SBinop (UBits2 UOr)
                                 (SBinop (UBits2 UAnd) 
                                    (SVar 248)
                                    (SBinop (UBits2 UAnd)
                                       (SUnop (UBits1 UNot)
                                          (SBinop 
                                             (UEq false) 
                                             (SVar 252)
                                             (SConst (Bits [false; false]))))
                                       (SBinop (UBits2 UAnd)
                                          (SUnop (UBits1 UNot)
                                             (SBinop 
                                                (UEq false) 
                                                (SVar 252)
                                                (SConst (Bits [true; false]))))
                                          (SUnop (UBits1 UNot)
                                             (SBinop 
                                                (UEq false) 
                                                (SVar 252)
                                                (SConst (Bits [false; true])))))))
                                 (SUnop (UBits1 UNot)
                                    (SUnop (UBits1 UNot) (SVar 6)))))
                           (SBinop (UBits2 UAnd)
                              (SUnop (UBits1 UNot)
                                 (SBinop (UBits2 UAnd)
                                    (SBinop (UEq false)
                                       (SBinop (UBits2 USel)
                                          (SUnop
                                             (UStruct1 (UGetField "inst"))
                                             (SVar 243))
                                          (SConst
                                             (Bits
                                                [false; true; true; false;
                                                false])))
                                       (SConst (Bits [false])))
                                    (SBinop (UEq false)
                                       (SBinop (UBits2 (UIndexedSlice 2))
                                          (SUnop
                                             (UStruct1 (UGetField "inst"))
                                             (SVar 243))
                                          (SConst
                                             (Bits
                                                [true; true; false; false;
                                                false])))
                                       (SConst (Bits [false; false])))))
                              (SBinop (UBits2 UAnd)
                                 (SBinop (UEq false)
                                    (SBinop (UBits2 (UIndexedSlice 3))
                                       (SUnop (UStruct1 (UGetField "inst"))
                                          (SVar 272))
                                       (SConst
                                          (Bits
                                             [false; false; true; false;
                                             false])))
                                    (SConst (Bits [false; true; true])))
                                 (SBinop (UBits2 UAnd)
                                    (SUnop (UBits1 UNot)
                                       (SBinop (UBits2 UAnd)
                                          (SBinop 
                                             (UEq false)
                                             (SBinop
                                                (UBits2 (UIndexedSlice 7))
                                                (SUnop
                                                 (UStruct1 (UGetField "inst"))
                                                 (SVar 108))
                                                (SConst
                                                 (Bits
                                                 [false; false; false; false;
                                                 false])))
                                             (SConst
                                                (Bits
                                                 [true; true; true; true;
                                                 false; true; true])))
                                          (SBinop 
                                             (UBits2 UOr)
                                             (SBinop 
                                                (UEq false) 
                                                (SVar 121)
                                                (SConst
                                                 (Bits
                                                 [true; false; false; false;
                                                 false])))
                                             (SBinop 
                                                (UEq false) 
                                                (SVar 121)
                                                (SConst
                                                 (Bits
                                                 [true; false; true; false;
                                                 false]))))))
                                    (SBinop (UBits2 UAnd)
                                       (SBinop (UEq false)
                                          (SBinop 
                                             (UBits2 (UIndexedSlice 7))
                                             (SUnop
                                                (UStruct1 (UGetField "inst"))
                                                (SVar 108))
                                             (SConst
                                                (Bits
                                                 [false; false; false; false;
                                                 false])))
                                          (SConst
                                             (Bits
                                                [true; true; true; false;
                                                false; true; true])))
                                       (SBinop (UBits2 UOr)
                                          (SBinop 
                                             (UBits2 UAnd)
                                             (SBinop 
                                                (UBits2 UOr)
                                                (SBinop 
                                                 (UEq false) 
                                                 (SVar 121)
                                                 (SConst
                                                 (Bits
                                                 [true; false; false; false;
                                                 false])))
                                                (SBinop 
                                                 (UEq false) 
                                                 (SVar 121)
                                                 (SConst
                                                 (Bits
                                                 [true; false; true; false;
                                                 false]))))
                                             (SBinop 
                                                (UBits2 UOr)
                                                (SBinop 
                                                 (UBits2 UAnd)
                                                 (SBinop 
                                                 (UBits2 UOr)
                                                 (SBinop 
                                                 (UEq false) 
                                                 (SVar 121) 
                                                 (SVar 278))
                                                 (SBinop 
                                                 (UBits2 UAnd)
                                                 (SBinop 
                                                 (UEq true) 
                                                 (SVar 278)
                                                 (SConst
                                                 (Bits
                                                 [true; false; false; false;
                                                 false])))
                                                 (SBinop 
                                                 (UEq true) 
                                                 (SVar 278)
                                                 (SConst
                                                 (Bits
                                                 [true; false; true; false;
                                                 false])))))
                                                 (SBinop 
                                                 (UBits2 UAnd)
                                                 (SUnop 
                                                 (UBits1 UNot)
                                                 (SBinop 
                                                 (UEq false) 
                                                 (SVar 367)
                                                 (SConst
                                                 (Bits [false; false; true]))))
                                                 (SBinop 
                                                 (UBits2 UOr)
                                                 (SBinop 
                                                 (UBits2 UOr)
                                                 (SBinop 
                                                 (UBits2 UAnd)
                                                 (SBinop 
                                                 (UEq false) 
                                                 (SVar 371)
                                                 (SConst
                                                 (Bits [false; false; false])))
                                                 (SBinop 
                                                 (UBits2 UAnd) 
                                                 (SVar 374) 
                                                 (SVar 290)))
                                                 (SBinop 
                                                 (UBits2 UOr)
                                                 (SBinop 
                                                 (UBits2 UAnd)
                                                 (SBinop 
                                                 (UEq false) 
                                                 (SVar 371)
                                                 (SConst
                                                 (Bits [true; false; false])))
                                                 (SBinop 
                                                 (UBits2 UAnd) 
                                                 (SVar 380) 
                                                 (SVar 296)))
                                                 (SBinop 
                                                 (UBits2 UOr)
                                                 (SBinop 
                                                 (UBits2 UAnd)
                                                 (SBinop 
                                                 (UEq false) 
                                                 (SVar 371)
                                                 (SConst (Bits ...)))
                                                 (SBinop 
                                                 (UBits2 UAnd) 
                                                 (SVar 386) 
                                                 (SVar 302)))
                                                 (SBinop 
                                                 (UBits2 UOr)
                                                 (SBinop 
                                                 (UBits2 UAnd)
                                                 (SBinop 
                                                 (UEq false) 
                                                 (SVar 371) 
                                                 (SConst ...))
                                                 (SBinop 
                                                 (UBits2 UAnd) 
                                                 (SVar 392) 
                                                 (SVar 308)))
                                                 (SBinop 
                                                 (UBits2 UOr)
                                                 (SBinop 
                                                 (UBits2 UAnd)
                                                 (SBinop ... ... ...)
                                                 (SBinop ... ... ...))
                                                 (SBinop 
                                                 (UBits2 UOr)
                                                 (SBinop ... ... ...)
                                                 (SBinop ... ... ...)))))))
                                                 (SBinop 
                                                 (UBits2 UAnd) 
                                                 (SVar 370) 
                                                 (SVar 286)))))
                                                (SBinop 
                                                 (UBits2 UAnd)
                                                 (SUnop 
                                                 (UBits1 UNot)
                                                 (SBinop 
                                                 (UBits2 UOr)
                                                 (SBinop 
                                                 (UEq false) 
                                                 (SVar 121) 
                                                 (SVar 278))
                                                 (SBinop 
                                                 (UBits2 UAnd)
                                                 (SBinop 
                                                 (UEq true) 
                                                 (SVar 278)
                                                 (SConst
                                                 (Bits
                                                 [true; false; false; false;
                                                 false])))
                                                 (SBinop 
                                                 (UEq true) 
                                                 (SVar 278)
                                                 (SConst
                                                 (Bits
                                                 [true; false; true; false;
                                                 false]))))))
                                                 (SBinop 
                                                 (UBits2 UOr)
                                                 (SBinop 
                                                 (UBits2 UAnd)
                                                 (SUnop 
                                                 (UBits1 UNot)
                                                 (SBinop 
                                                 (UEq false) 
                                                 (SVar 442)
                                                 (SConst
                                                 (Bits [false; false; false]))))
                                                 (SBinop 
                                                 (UBits2 UAnd)
                                                 (SUnop 
                                                 (UBits1 UNot)
                                                 (SBinop 
                                                 (UEq true) 
                                                 (SVar 487) 
                                                 (SVar 441)))
                                                 (SBinop 
                                                 (UBits2 UAnd) 
                                                 (SVar 490)
                                                 (SBinop 
                                                 (UBits2 UOr) 
                                                 (SVar 286) 
                                                 (SVar 370)))))
                                                 (SBinop 
                                                 (UBits2 UAnd)
                                                 (SUnop 
                                                 (UBits1 UNot)
                                                 (SBinop 
                                                 (UEq false) 
                                                 (SVar 498)
                                                 (SConst
                                                 (Bits [false; false; true]))))
                                                 (SBinop 
                                                 (UBits2 UOr)
                                                 (SBinop 
                                                 (UBits2 UOr)
                                                 (SBinop 
                                                 (UBits2 UAnd)
                                                 (SBinop 
                                                 (UEq false) 
                                                 (SVar 502)
                                                 (SConst
                                                 (Bits [false; false; false])))
                                                 (SBinop 
                                                 (UBits2 UAnd) 
                                                 (SVar 505)
                                                 (SBinop 
                                                 (UBits2 UOr) 
                                                 (SVar 290) 
                                                 (SVar 374))))
                                                 (SBinop 
                                                 (UBits2 UOr)
                                                 (SBinop 
                                                 (UBits2 UAnd)
                                                 (SBinop 
                                                 (UEq false) 
                                                 (SVar 502)
                                                 (SConst (Bits ...)))
                                                 (SBinop 
                                                 (UBits2 UAnd) 
                                                 (SVar 511)
                                                 (SBinop 
                                                 (UBits2 UOr) 
                                                 (SVar 296) 
                                                 (SVar 380))))
                                                 (SBinop 
                                                 (UBits2 UOr)
                                                 (SBinop 
                                                 (UBits2 UAnd)
                                                 (SBinop 
                                                 (UEq false) 
                                                 (SVar 502) 
                                                 (SConst ...))
                                                 (SBinop 
                                                 (UBits2 UAnd) 
                                                 (SVar 517)
                                                 (SBinop ... ... ...)))
                                                 (SBinop 
                                                 (UBits2 UOr)
                                                 (SBinop 
                                                 (UBits2 UAnd)
                                                 (SBinop ... ... ...)
                                                 (SBinop ... ... ...))
                                                 (SBinop 
                                                 (UBits2 UOr)
                                                 (SBinop ... ... ...)
                                                 (SBinop ... ... ...))))))
                                                 (SBinop 
                                                 (UBits2 UAnd) 
                                                 (SVar 501)
                                                 (SBinop 
                                                 (UBits2 UOr)
                                                 (SBinop 
                                                 (UBits2 UOr) 
                                                 (SVar 286) 
                                                 (SVar 370)) 
                                                 (SVar 490)))))))))
                                          (SBinop 
                                             (UBits2 UAnd)
                                             (SUnop 
                                                (UBits1 UNot)
                                                (SBinop 
                                                 (UBits2 UOr)
                                                 (SBinop 
                                                 (UEq false) 
                                                 (SVar 121)
                                                 (SConst
                                                 (Bits
                                                 [true; false; false; false;
                                                 false])))
                                                 (SBinop 
                                                 (UEq false) 
                                                 (SVar 121)
                                                 (SConst
                                                 (Bits
                                                 [true; false; true; false;
                                                 false])))))
                                             (SBinop 
                                                (UBits2 UAnd)
                                                (SBinop 
                                                 (UBits2 UOr)
                                                 (SBinop 
                                                 (UEq false) 
                                                 (SVar 278)
                                                 (SConst
                                                 (Bits
                                                 [true; false; false; false;
                                                 false])))
                                                 (SBinop 
                                                 (UEq false) 
                                                 (SVar 278)
                                                 (SConst
                                                 (Bits
                                                 [true; false; true; false;
                                                 false]))))
                                                (SBinop 
                                                 (UBits2 UAnd)
                                                 (SUnop 
                                                 (UBits1 UNot)
                                                 (SBinop 
                                                 (UEq false) 
                                                 (SVar 595)
                                                 (SConst
                                                 (Bits [false; false; false]))))
                                                 (SBinop 
                                                 (UBits2 UAnd)
                                                 (SUnop 
                                                 (UBits1 UNot)
                                                 (SBinop 
                                                 (UEq true) 
                                                 (SVar 640) 
                                                 (SVar 594)))
                                                 (SBinop 
                                                 (UBits2 UAnd) 
                                                 (SVar 643)
                                                 (SBinop 
                                                 (UBits2 UOr)
                                                 (SBinop 
                                                 (UBits2 UOr)
                                                 (SBinop 
                                                 (UBits2 UOr) 
                                                 (SVar 286) 
                                                 (SVar 370)) 
                                                 (SVar 490)) 
                                                 (SVar 501)))))))))))))
                        (SBinop (UBits2 UOr)
                           (SBinop (UBits2 UAnd)
                              (SBinop (UEq true) (SVar 824)
                                 (SUnop (UStruct1 (UGetField "ppc"))
                                    (SVar 104)))
                              (SBinop (UBits2 UOr)
                                 (SBinop (UBits2 UAnd) (SVar 826) (SVar 110))
                                 (SBinop (UBits2 UAnd) (SVar 826) (SVar 110))))
                           (SUnop (UBits1 UNot)
                              (SUnop (UBits1 UNot) (SVar 16)))))))))
     : option sact
 *)

      Time native_compute in r2.
      
      intros. cbn in H.
          simplify_sact ctx (rir_failure_cond rir) = const_false.
    
      intros.
      Time native_compute in ir2v.
      Time native_compute in H. clear ir2v.

      injection H. clear. intros _ H0 H1.
      rewrite <- H1.
      Time native_compute.

      Time Eval (rewrite <- H1; native_compute) in (Maps.PTree.get 278%positive (rir_vars rir)).
      (* set (ir2v := (init_r2v (ext_fn_t:=RV32I.ext_fn_t) REnv ctx RV32I.R xH)). *)
      (* native_compute in ir2v. *)
      (* set (r2v := fst (fst ir2v)). *)
      (* native_compute in r2v. *)
      (* set (vvs := snd (fst ir2v)). *)
      (* set (nid :=  (snd ir2v)). *)
      (* native_compute in vvs. *)
      (* native_compute in nid. clear ir2v. *)

      (* (* set (r := get_rule_information_aux (Sigma:=ext_Sigma) RV32I.R (drules Execute) [] [] r2v vvs const_true (RecordSet.set rir_vars (fun _ => vvs) init_rir) init_rir nid). *) *)
      (* (* Time native_compute in r. *) *)

      intros.
      Opaque getenv.
      assert (WTHALT := WTRENV RV32I.halt). simpl in WTHALT.
      edestruct (Sact.wt_val_bool _ WTHALT) as (? & HALT).
      assert (WTVALID0 := WTRENV (RV32I.d2e RV32I.fromDecode.valid0)). simpl in WTVALID0.
      edestruct (Sact.wt_val_bool _ WTVALID0) as (? & VALID0).
      assert (WTDATA0 := WTRENV (RV32I.d2e RV32I.fromDecode.data0)). simpl in WTDATA0.
      inv WTDATA0. simpl in H2. inv H2. inv H6. inv H7. inv H8. inv H9. inv H10.
      inv H11. inv H6. simpl in H2. inv H2.
      repeat match goal with
             | H: Forall2 _ (_::_) _ |- _ => inv H
             | H: Forall2 _ [] _ |- _ => inv H
             | H: wt_val (bits_t 1) _ |- _ => apply Sact.wt_val_bool in H; destruct H as (? & H); subst
             end.

      replace ctx with (create ContextEnv (fun r => Sact.val_of_type (RV32I.R r))) in *.
      Transparent getenv.
      Time native_compute in WTHALT.
      Time native_compute in ir2v.
      rewrite (interp_sact_replace_reg_sact_vars _ _ _ _ _ HALT).
      rewrite (interp_sact_replace_reg_sact_vars _ _ _ _ _ VALID0).
      rewrite (interp_sact_replace_reg_sact_vars _ _ _ _ _ (eq_sym H1)).
      Time native_compute.
      Time cbv in H. inv H.
      cbv.

      

      Lemma
        eval_sact ctx ext_sigma vvs s fuel =
          eval_sact ctx ext_sigma (vvs) s fuel =

      dependent rewrite WTVALID0; dependent rewrite <- H1.
      cbv.
      assert (HALT: exists b, getenv REnv ctx RV32I.halt = Bits [b]) by admit.
      destruct HALT as (b & HALT).
      assert (VALID: exists b, getenv REnv ctx (RV32I.d2e RV32I.fromDecode.valid0) = Bits [b]) by admit.
      destruct VALID as (?b & VALID).
      assert (DATA: exists pc ppc epoch dinst rv1 rv2,
                 getenv REnv ctx (RV32I.d2e RV32I.fromDecode.data0) =
                   Struct RV32I.decode_bookkeeping [Bits pc; Bits ppc; Bits epoch; dinst; rv1; rv2]) by admit.
      destruct DATA as (? & ? & ? & ? & ? & ? & DATA).
      rewrite HALT, VALID, DATA in *.
      cbv.
      dependent rewrite DATA.

      set (r := get_rule_information (Sigma:=ext_Sigma) RV32I.R
                                     (drules Execute)
                                     (snd ir2v) (fst (fst ir2v)) (snd (fst ir2v))
                                     (RecordSet.set rir_vars (fun _ => (snd (fst ir2v))) init_rir)).
      Time cbv in r.
      set (f := let '(rir, _, _) := r in eval_sact ext_sigma (rir_vars rir) (rir_failure_cond rir) 20).
      Time cbv in f.
      assert (HALT: exists b, getenv REnv ctx RV32I.halt = Bits [b]) by admit.
      destruct HALT as (b & HALT).
      revert f. dependent rewrite HALT.
      assert (VALID: exists b, getenv REnv ctx (RV32I.d2e RV32I.fromDecode.valid0) = Bits [b]) by admit.
      destruct VALID as (?b & VALID).
      dependent rewrite VALID.
      assert (DATA: exists pc ppc epoch dinst rv1 rv2,
                 getenv REnv ctx (RV32I.d2e RV32I.fromDecode.data0) =
                   Struct RV32I.decode_bookkeeping [Bits pc; Bits ppc; Bits epoch; dinst; rv1; rv2]) by admit.
      destruct DATA as (? & ? & ? & ? & ? & ? & DATA).
      dependent rewrite DATA.
      simpl. cbv.
      
        in f.
      set (r := get_rule_information (Sigma:=ext_Sigma) RV32I.R (drules Execute)
                                     (snd ir2v) (fst (fst ir2v)) (snd (fst ir2v))
                                     (RecordSet.set rir_vars (fun _ => (snd (fst ir2v))) init_rir)).
      Time native_compute in r.
      set (f := let '(rir, _, _) := r in eval_sact ext_sigma (rir_vars rir) (rir_failure_cond rir) 20).
      Time native_compute in f.
      set (r := get_rir_scheduler' (Sigma:=ext_Sigma) (* REnv ctx *) RV32I.R
                                   (RecordSet.set rir_vars (fun _ => snd (fst ir2v)) init_rir)
                                   (fst (fst ir2v))
                                   drules (snd ir2v) (Execute |> done)).
      Time native_compute in r.

      set (r := get_rir_scheduler (Sigma:=ext_Sigma) REnv ctx RV32I.R drules (Execute |> done)).

      set (r := schedule_to_simple_form (Sigma:=ext_Sigma) REnv ctx RV32I.R drules (Execute |> done)).
      Time native_compute in r.
      Eval native_compute in (List.length (Maps.PTree.elements (vars r))).
      set (l := reachable_vars_aux (vars r) 902%positive [] 903%nat).
      Time native_compute in l.
    (*   Time native_compute in l. *)
    (*   set (l2 := filter *)
    (* (fun p : positive => *)
    (*  if in_dec Pos.eq_dec p l then false else true) *)
    (* (map fst (Maps.PTree.elements (vars r)))). *)
    (*   Time native_compute in l2. *)

    (*   set (vv := fold_left (fun t n => Maps.PTree.remove n t) l2 (vars r)). *)
    (*   Time native_compute in vv. *)
    (*   Set NativeCompute Profiling. *)
    (*   Eval native_compute in list_assoc (final_values r) RV32I.halt. *)
    (*   Eval native_compute in Maps.PTree.get 902%positive vv. *)
    (*   Eval native_compute in max_var vv. *)
    (*   Eval native_compute in vvs_size vv (Pos.succ (max_var vv)). *)
    (*   set (ks := PosSort.sort (map fst (Maps.PTree.elements (vars r)))). *)
    (*   Time native_compute in ks. *)
    (*   Time Eval native_compute in snd (simplify_var ext_sigma r 9%positive). *)
       set (t :=
             fold_left
               (fun t n =>
                  match Maps.PTree.get n (vars r) with
                  | Some v =>
                      Maps.PTree.set n v t
                  | None => t
                  end
               )
               l (Maps.PTree.empty _)
          ).
      Time native_compute in t.
      clear r l.
      Eval native_compute in vvs_size t 932%positive.
      Eval native_compute in Maps.PTree.get 902%positive t.
      Eval native_compute in Maps.PTree.get 901%positive t.

      set (t2 := Maps.PTree.map (fun k '(t,a) => (t, simplify_sact a)) t).
      Time native_compute in t2. clear t.
      Eval native_compute in (Maps.PTree.get 902%positive t2).
      Eval native_compute in (Maps.PTree.get 871%positive t2).

      Eval native_compute in Maps.PTree.get 902%positive t.
      Eval native_compute in Maps.PTree.get 902%positive t.
      Eval native_compute in Maps.PTree.get 902%positive t.
      Eval native_compute in Maps.PTree.get 902%positive t.
      Eval native_compute in Maps.PTree.get 902%positive t.
      Eval native_compute in eval_sact ext_sigma t (SVar 902%positive) 20.
        with
          Some n =>
            do_eval_sact ext_sigma vv (SVar n)
        | _ => None
        end.

             fold_left () r).
      Set Typeclasses Debug.
      Time Eval native_compute in List.length (useful_vars r).
      Time native_compute in r2.
      Eval native_compute in (List.length (Maps.PTree.elements (vars r2))).
    (* Time Eval native_compute in *)
    (*   let ir2v := init_r2v (ext_fn_t:=RV32I.ext_fn_t) REnv ctx RV32I.R O in *)
    (*   let '(r2v, vvs, nid) := ir2v in *)
    (*   let '(rir, r2v, nid) := get_rule_information_aux RV32I.R (drules Execute) [] [] r2v vvs const_true (RecordSet.set rir_vars (fun _ => vvs) init_rir) init_rir nid in nid. *)
    Abort.
  End test1.


  Inductive mreg := A | B.
  Instance fin_mreg: FiniteType mreg.
  Proof.
    refine
      {|
        finite_index:= fun x => match x with A => 0 | B => 1 end%nat;
        finite_elements:= [A;B];
      |}.
    intros; destr; reflexivity.
    repeat constructor; simpl; auto. intuition.
  Defined.
  Instance eqdec_mreg: EqDec mreg := EqDec_FiniteType.

  Fixpoint make_big_uact (n: nat) : daction (pos_t:=pos_t) (var_t:=string) (fn_name_t:=string) (reg_t:=mreg) (ext_fn_t:=RV32I.ext_fn_t):=
    match n with
      O => DVar "hello"
    | S n => DIf (make_big_uact n)(make_big_uact n) (make_big_uact n)
    end.

  Definition mbu n := DBind "hello" (DConst (tau:=bits_t 1) (vect_of_list [true]))
                            (make_big_uact n).

  Definition mreg_R (r: mreg) := bits_t 1.

  Section test2.
    Variable REnv: Env mreg.
    Variable ctx : env_t REnv (fun _ => val).

    Goal False.

      set (ir2v := (init_r2v (ext_fn_t:=RV32I.ext_fn_t) REnv ctx mreg_R O)).
      native_compute in ir2v.
      set (r2v := fst (fst ir2v)).
      native_compute in r2v.
      set (vvs := snd (fst ir2v)).
      set (nid :=  (snd ir2v)).
      native_compute in vvs.
      native_compute in nid. clear ir2v.

      set (r := get_rule_information_aux (Sigma:=ext_Sigma) mreg_R (mbu 3) [] [] r2v vvs const_true (RecordSet.set rir_vars (fun _ => vvs) init_rir) init_rir nid).
      Time native_compute in r.
    Time Eval native_compute in
      let ir2v := init_r2v (ext_fn_t:=RV32I.ext_fn_t) REnv ctx mreg_R O in
      let '(r2v, vvs, nid) := ir2v in
      let '(res, env, r2v, vvs, failure, rir, nid, t) := get_rule_information_aux mreg_R (mbu 3) [] [] r2v vvs const_true (RecordSet.set rir_vars (fun _ => vvs) init_rir) init_rir nid in nid.
    Abort.
  End test2.


  Definition cycle (r: env_t ContextEnv (fun _ : RV32I.reg_t => val)) :=
    UntypedSemantics.interp_dcycle drules r ext_sigma rv_schedule.

  Definition env_type := env_t REnv RV32I.R.
  Definition initial_env := create REnv RV32I.r.

  Definition CEnv := @ContextEnv RV32I.reg_t RV32I.FiniteType_reg_t.
  Definition initial_context_env := CEnv.(create) (RV32I.r).

  Definition f_init := fun x => val_of_value (initial_context_env.[x]).

  Theorem osef : initial_context_env.[RV32I.on_off] = Ob~0.
  Proof. trivial. Qed.

  Definition initial_context_env_val := ContextEnv.(create) (f_init).
  Theorem osef2 : initial_context_env_val.[RV32I.on_off] = @val_of_value (bits_t 1) Ob~0.
  Proof. trivial. Qed.

  (* TODO *)
  Definition state_step_1 := cycle initial_context_env_val .

  Lemma log_app_empty_r:
    forall {V} (l: @_ULog V _ REnv), log_app l log_empty = l.
  Proof.
    unfold log_app. unfold map2.
    intros.
    etransitivity.
    2: apply create_getenv_id.
    apply create_funext. intros. unfold log_empty.
    rewrite getenv_create. rewrite app_nil_r. auto.
  Qed.


  Theorem tick_preserves_on_off :
    forall ctx ctx' (WT:  Wt.wt_renv RV32I.R REnv ctx),
    UntypedSemantics.interp_dcycle drules ctx ext_sigma (Tick |> done) = ctx' ->
    getenv REnv ctx' RV32I.on_off = getenv REnv ctx RV32I.on_off.
  Proof.
    intros; subst.
    Set Typeclasses Debug.
    erewrite (normal_form_ok (reg_t_eq_dec:=EqDec_FiniteType) RV32I.R ext_Sigma ctx ext_sigma).
    edestruct (@getenv_interp_cycle _ _ _ _ EqDec_FiniteType REnv RV32I.R ext_Sigma ctx ext_sigma wt_sigma _ drules (Tick |> done)) with (k:=RV32I.on_off)
      as (n & s0 & t & GET1 & GET2 & EVAL). repeat constructor. auto. apply rules_wt.
    revert GET1 GET2 EVAL.
    set (s := (schedule_to_simple_form REnv ctx RV32I.R drules (Tick |> done))).
    intros.
    cbv in s. cbv in GET1. inv GET1.
    cbv in GET2. inv GET2. simpl in EVAL. inv EVAL. setoid_rewrite <- H0. reflexivity.
    repeat constructor. auto. apply rules_wt.
    Unshelve. apply wt_sigma.
  Qed.
    (* set (n:= list_assoc (final_values s) RV32I.on_off). cbv in n. *)
    (* unfold n. *)
    (* set (i:= inlining_pass ext_sigma s). *)
    (* set (v := list_assoc (vars s) 94%nat). cbv in v. *)
    (* cbv in i. *)
    (* unfold inlining_pass. *)
    (* Time native_compute. *)
    (* rewrite interp_cycleb_ok with (reg_eqb:=beq_dec). *)
    (* rewrite schedule_to_simple_formb_ok with (reg_eqb:=beq_dec). *)
    (* unfold interp_cycleb. rewrite getenv_create. *)
    (* (* Time Eval vm_compute in (get_rir_schedulerb beq_dec REnv ctx RV32I.R drules (Tick |> done)). *) *)
    (* (* (* Finished transaction in 7.272 secs (7.269u,0.s) (successful) *) *) *)
    (* Time Eval native_compute in (get_rir_scheduler REnv ctx RV32I.R drules (Tick |> done)). *)
    (* (* Finished transaction in 17.762 secs (3.527u,0.144s) (successful) *) *)
    (* (* Time Eval vm_compute in (get_rir_scheduler REnv ctx RV32I.R drules (Tick |> done)). *) *)
    (* (* (* Finished transaction in 7.387 secs (7.349u,0.035s) (successful) *) *) *)
    (* (* Time Eval native_compute in (get_rir_scheduler REnv ctx RV32I.R drules (Tick |> done)). *) *)
    (* (* Finished transaction in 5.597 secs (2.607u,0.119s) (successful) *) *)

    (* Eval compute in drules Tick. *)
    (* set (ir2v := init_r2v (ext_fn_t:=RV32I.ext_fn_t) REnv ctx RV32I.R O). *)
    (* Time Eval native_compute in match ir2v with (_,_,nid) => nid end . *)

    (* Time Eval native_compute in *)
    (*   let '(r2v, vvs, nid) := ir2v in *)
    (*   let '(rir, r2v, nid) := get_rir_scheduler' RV32I.R (RecordSet.set rir_vars (fun _ => vvs) init_rir) r2v drules nid (Execute |> done) in *)
    (*   List.length (rir_vars rir). *)


    (* Time Eval native_compute in *)
    (*   let '(r2v, vvs, nid) := ir2v in *)
    (*   let '(rir, r2v, nid) := get_rir_scheduler' RV32I.R (RecordSet.set rir_vars (fun _ => vvs) init_rir) r2v drules nid (Execute |> done) in *)
    (*   let useful_vars := *)
    (*     fold_left (fun visited rpn => *)
    (*                  match rpn with *)
    (*                    ((r,inr tt),n) => *)
    (*                      reachable_vars_aux (rir_vars rir) n visited n *)
    (*                  | _ => visited *)
    (*                  end) r2v [] in *)
    (*   (List.length useful_vars, List.length (rir_vars rir)). *)

    (*   | None => [] *)
    (*   end. *)
    


    (* Opaque getenv. *)
    (* Time Eval cbv in ir2v. *)
    (* set (rir := get_rir_scheduler (Sigma:=ext_Sigma) REnv ctx RV32I.R drules ( *)
    (*                                 Writeback |> done *)

    (*     )). *)
    (* Time Eval native_compute in rir. *)
    
    (* set (sfb := schedule_to_simple_form (Sigma:=ext_Sigma) beq_dec REnv ctx RV32I.R drules (Tick |> done)). *)
    (* (* Time Eval vm_compute in sfb. *) *)
    (* (* Finished transaction in 7.048 secs (7.043u,0.003s) (successful) *) *)
    (* Time Eval native_compute in sfb. *)
    (* (* Finished transaction in 2.676 secs (2.357u,0.084s) (successful) *) *)
    (* set (sf := schedule_to_simple_form (Sigma:=ext_Sigma) REnv ctx RV32I.R drules (Tick |> done)). *)
    (* Time Eval vm_compute in sf. *)
    (* (* Finished transaction in 7.146 secs (7.134u,0.011s) (successful) *) *)
    (* (* Time Eval native_compute in sf. *) *)
    (* (* Finished transaction in 2.644 secs (2.367u,0.084s) (successful) *) *)

    (* Time Eval native_compute in (inlining_passb ext_sigma sfb). (* 24.761 *) *)
    (* Time Eval native_compute in (inlining_pass ext_sigma sf). (* 26.321 *) *)

    (* Time Eval vm_compute in Mergesort.NatSort.sort (map fst (vars sfb)). *)
    (* Time Eval vm_compute in Mergesort.NatSort.sort (map fst (vars sf)). *)

    (* Time Eval native_compute in Mergesort.NatSort.sort (map fst (vars sfb)). *)
    (* Time Eval native_compute in Mergesort.NatSort.sort (map fst (vars sf)). *)



    (* Time Eval native_compute in list_assocb beq_dec (final_values sfb) RV32I.on_off. *)
    (* Time Eval native_compute in list_assocb Nat.eqb (vars sfb) 94%nat. *)
    (* Time Eval native_compute in RV32I.rv_urules Tick. *)

    (* Opaque val_eq_dec. *)
    (* Time Eval native_compute in *)
    (*   (match list_assocb beq_dec (final_values sfb) RV32I.cycle_count with *)
    (*    | Some n => match list_assocb Nat.eqb (vars sfb) n with *)
    (*                | Some (t,v) => Some v(* eval_sact ext_sigma (vars sfb) v n *) *)
    (*                | None => None *)
    (*                end *)
    (*    | None => None *)
    (*    end). *)

    (* Time Eval native_compute in reachable_vars_aux (vars sf) 94%nat [] 94%nat. *)

  (*   Eval vm_compute in Nat.eq_dec 0 91. *)
  (*   Eval vm_compute in eq_dec (RV32I.pc) (RV32I.pc). *)
  (*   SimpleForm.get_rir_scheduler REnv ctx RV32I.R drules (Tick |> done). *)
  (*   compute in sf. *)
  (*   compute. *)
  (*   intros ctx ctx' A. *)
  (*   inv A. inv H. inv H0. *)
  (*   inv H4. *)
  (*   - inv H0. *)
  (*     simpl RV32I.rv_urules in H. *)
  (*     unfold RV32I.tick in H. *)
  (*     dependent destruction H. *)
  (*     dependent destruction H. *)
  (*     dependent destruction H. *)
  (*     dependent destruction H. *)
  (*     dependent destruction H. *)
  (*     dependent destruction H0. *)
  (*     dependent destruction H2. *)
  (*     dependent destruction H2. *)
  (*     dependent destruction H2_. *)
  (*     dependent destruction H2_0. *)
  (*     assert (action_log' = (log_cons RV32I.halt {| kind := Logs.LogRead; port := P0; val := Bits 0 [] |} log_empty)). *)
  (*     { *)
  (*       clear - H1. *)
  (*       destruct val_eq_dec; simpl in *. *)
  (*       dependent destruction H1. *)
  (*       dependent destruction H1. *)
  (*       auto. *)
  (*     } *)
  (*     subst. clear. *)
  (*     unfold commit_update. *)
  (*     rewrite getenv_create. *)
  (*     unfold latest_write. unfold log_find. *)
  (*     rewrite SemanticProperties.find_none_notb. auto. intros. *)
  (*     rewrite log_app_empty_r in H. *)
  (*     unfold log_cons in H. *)
  (*     rewrite get_put_neq in H by congruence. *)
  (*     rewrite get_put_neq in H by congruence. *)
  (*     rewrite get_put_neq in H by congruence. *)
  (*     setoid_rewrite getenv_create in H. easy. *)
  (*   - inv H0. unfold commit_update. *)
  (*     rewrite getenv_create. *)
  (*     unfold latest_write. unfold log_find. *)
  (*     rewrite SemanticProperties.find_none_notb. auto. intros. *)
  (*     setoid_rewrite getenv_create in H0. easy. *)
  (* Qed. *)

  Lemma getenv_ulogapp:
    forall (V reg_t: Type) (REnv: Env reg_t) (l l': UntypedLogs._ULog) idx,
    REnv.(getenv) (@UntypedLogs.log_app V reg_t REnv l l') idx =
    REnv.(getenv) l idx ++ REnv.(getenv) l' idx.
  Proof.
    intros.
    unfold log_app, map2; intros; rewrite getenv_create; reflexivity.
  Qed.

  Lemma find_latest_write_top:
    forall (V reg_t : Type) (REnv : Env reg_t) (l l' : UntypedLogs._ULog) x px xval,
    @UntypedLogs.latest_write V reg_t REnv (UntypedLogs.log_app
      (UntypedLogs.log_cons x {| kind := Logs.LogWrite; port := px; val := xval |} l) l'
    ) x = Some xval.
  Proof.
    intros.
    unfold latest_write.
    unfold log_find.
    unfold RLog. (* Effects invisible without Set Printing All but required *)
    rewrite getenv_ulogapp.
    unfold log_cons.
    rewrite get_put_eq.
    simpl.
    reflexivity.
  Qed.

  (* Lemma registers_contents_match_type: *)
  (*   forall x y reg_t, *)
  (*   reg_t sz *)
  (*   getenv REnv ctx RV32I.cycle_count = y -> *)

  (*   ) *)
  (*   Bits (type_sz (RV32I.R RV32I.cycle_count)) y *)

  Theorem tick_overwrites_cycle_count:
    forall ctx ctx' (WT:  Wt.wt_renv RV32I.R REnv ctx),
      interp_dcycle drules ctx ext_sigma (Tick |> done) = ctx' ->
    getenv REnv ctx RV32I.halt = @val_of_value (bits_t 1) Ob~0 ->
    getenv REnv ctx RV32I.cycle_count <> getenv REnv ctx' RV32I.cycle_count.
  Proof.
    intros.
    intros; subst.
    erewrite (normal_form_ok (reg_t_eq_dec:=EqDec_FiniteType) RV32I.R ext_Sigma ctx ext_sigma).
    edestruct (@getenv_interp_cycle _ _ _ _ EqDec_FiniteType REnv RV32I.R ext_Sigma ctx ext_sigma wt_sigma _ drules (Tick |> done)) with (k:=RV32I.cycle_count)
      as (n & s0 & t & GET1 & GET2 & EVAL). repeat constructor. auto. apply rules_wt.
    revert GET1 GET2 EVAL.
    set (s := (schedule_to_simple_form REnv ctx RV32I.R drules (Tick |> done))).
    intros.
    Opaque getenv.
    cbv in s. cbv in GET1. inv GET1.
    cbv in GET2. inv GET2. simpl in EVAL.
    rewrite H0 in EVAL.
    destruct val_eq_dec. inv e.
    revert EVAL.
    generalize (getenv REnv ctx RV32I.cycle_count).
    intro v.
    fold (@R val RV32I.reg_t). simpl. destr; try congruence. clear. intro A; inv A.
    clear.
    intro A; inv A.
  Admitted.

  Variable decode_opcode : list bool -> instruction.
  Variable decode_rd : list bool -> RV32I.Rf.reg_t.
  Variable decode_rs1 : list bool -> RV32I.Rf.reg_t.
  Variable decode_imm : list bool -> val.

  Definition val_add (v1 v2: val) :=
    match v1, v2 with
    | Bits l1, Bits l2 => Some (Bits l1)
    | _, _ => None
    end.

  Goal
  forall (ctx : env_t REnv (fun _ : RV32I.reg_t => val)),
    getenv REnv ctx (RV32I.d2e RV32I.fromDecode.valid0) = Bits [true].
  Proof.
    intros.
    


  Goal
    forall ctx (WT:  Wt.wt_renv RV32I.R REnv ctx) bits_instr rs1 rd vimm,
      getenv REnv ctx RV32I.halt = Bits [false] ->
      getenv REnv ctx (RV32I.d2e RV32I.fromDecode.data0) = Bits bits_instr ->
      getenv REnv ctx (RV32I.d2e RV32I.fromDecode.valid0) = Bits [true] ->
      decode_opcode bits_instr = ADDI_32I ->
      decode_rd bits_instr = rd ->
      decode_rs1 bits_instr = rs1 ->
      decode_imm bits_instr = vimm ->
      (* UntypedIndSemantics.interp_rule ctx ext_sigma l RV32I.execute l' -> *)
      forall ctx' ,
      interp_dcycle drules ctx ext_sigma (Execute |> done) = ctx' ->
      Some (getenv REnv ctx' (RV32I.rf rd)) = val_add (getenv REnv ctx (RV32I.rf rs1)) vimm.
  Proof.
    intros ctx WT bits_instr rs1 rd vimm NoHalt BitsInstr InstrValid Opcode RD RS1 IMM ctx' IR. subst.
    erewrite (normal_form_ok (reg_t_eq_dec:=EqDec_FiniteType) RV32I.R ext_Sigma ctx ext_sigma).
    edestruct (@getenv_interp_cycle _ _ _ _ EqDec_FiniteType REnv RV32I.R ext_Sigma ctx ext_sigma wt_sigma _ drules (Execute |> done)) with (k:=RV32I.rf (decode_rd bits_instr))
      as (n & s0 & t & GET1 & GET2 & EVAL). repeat constructor. auto. apply rules_wt.
    revert GET1 GET2 EVAL.
    set (s:=schedule_to_simple_form REnv ctx RV32I.R drules (Execute |> done)).
    set (ic := interp_cycle ctx ext_sigma s).
    set (r:=RV32I.rf (decode_rd bits_instr)).
    intros. native_compute in s.
    Time Eval native_compute in (map (fun '(n,(t,a)) => (n, size_sact a)) (vars s)).
    native_compute in r. native_compute in GET1.
    dependent destruction IR.
    dependent destruction H.
    dependent destruction H.
    destruct b.
    - dependent destruction H0.
    - dependent destruction H0.
      dependent destruction H1.
      dependent destruction H1_.
      dependent destruction H0. simpl in *.
      dependent destruction H1_.
      dependent destruction H1_1.
      dependent destruction H1_1_1.
      dependent destruction H1_1_1_1.
      dependent destruction H1_1_1_1.
      dependent destruction H.
      simpl in *.
      dependent destruction H1_1_1_1.
      simpl in *.
      dependent destruction H.
  Admitted.

  (* Goal *)
  (*   forall ctx bits_instr rs1 rd vimm ctx', *)
  (*     getenv REnv ctx RV32I.halt = Bits 1 [false] -> *)
  (*     getenv REnv ctx (RV32I.d2e RV32I.fromDecode.data0) = Bits 32 bits_instr -> *)
  (*     getenv REnv ctx (RV32I.d2e RV32I.fromDecode.valid0) = Bits 1 [true] -> *)
  (*     decode_opcode bits_instr = ADDI_32I -> *)
  (*     decode_rd bits_instr = rd -> *)
  (*     decode_rs1 bits_instr = rs1 -> *)
  (*     decode_imm bits_instr = Bits 12 vimm -> *)
  (*     UntypedIndSemantics.interp_cycle RV32I.rv_urules ctx ext_sigma rv_schedule ctx' -> *)
  (*     UntypedIndSemantics.interp_cycle RV32I.rv_urules ctx ext_sigma (Execute |> done) ctx' -> *)
  (*     getenv REnv ctx' rd = getenv REnv ctx rs1 + vimm. *)
