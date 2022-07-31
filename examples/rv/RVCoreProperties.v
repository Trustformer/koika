(*! Proofs about our RISC-V implementation !*)
Require Import Coq.Program.Equality.
Require Import Koika.BitsToLists Koika.Frontend Koika.Logs
  Koika.ProgramTactics Koika.SimpleTypedSemantics Koika.Std Koika.UntypedLogs
  UntypedIndSemantics Koika.UntypedSemantics Koika.DesugaredSyntax.
Require Export rv.Instructions rv.ShadowStack rv.RVCore rv.rv32 rv.rv32i.
Require Import Koika.SimpleForm Koika.SimpleFormInterpretation.
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

Lemma falso : False. Admitted.
Ltac cheat := elim falso.

Module RVProofs.
  Context (ext_sigma : RV32I.ext_fn_t -> val -> val).
  Context (ext_Sigma : RV32I.ext_fn_t -> ExternalSignature).
  Context {REnv : Env RV32I.reg_t}.

  Definition drules rule :=
    match uaction_to_daction (desugar_action tt (RV32I.rv_urules rule)) with
    | Some d => d
    | None => DFail unit_t
    end.

  (* Set Typeclasses Debug. *)
  Instance eq_dec_reg: EqDec RV32I.reg_t := EqDec_FiniteType.
  Existing Instance etaRuleInformationRaw.

  Section test1.
  Variable REnv: Env RV32I.reg_t.
  Variable ctx : env_t REnv (fun _ => val).
  Hypothesis WTRENV: Wt.wt_renv RV32I.R REnv ctx.

    Hypothesis wt_sigma: forall (ufn : RV32I.ext_fn_t) (vc : val),
      wt_val (arg1Sig (ext_Sigma ufn)) vc
      -> wt_val (retSig (ext_Sigma ufn)) (ext_sigma ufn vc).

    Hypothesis rules_wt:
      forall rule : rv_rules_t, exists t : type,
      wt_daction (Sigma:=ext_Sigma) (R:=RV32I.R) unit string string []
        (drules rule) t.

    Definition sf :=
      schedule_to_simple_form RV32I.R (Sigma := ext_Sigma) drules rv_schedule.

    Lemma wt_env : Wt.wt_renv RV32I.R REnv ctx.
    Proof. eauto. Qed.
    Lemma rv_schedule_good : good_scheduler rv_schedule.
    Proof. unfold rv_schedule. repeat constructor. Qed.
    Lemma sf_def :
      schedule_to_simple_form RV32I.R (Sigma := ext_Sigma) drules rv_schedule
      = sf.
    Proof. unfold sf. reflexivity. Qed.
    Lemma tret :
      forall r : rv_rules_t, exists tret : type,
      wt_daction
        (R := RV32I.R) (Sigma := ext_Sigma) unit string string [] (drules r)
        tret.
    Proof. eauto. Qed.
    Lemma wt_renv : Wt.wt_renv RV32I.R REnv ctx.
    Proof. eauto. Qed.

    (* TODO useless in this form *)
    Lemma specialize_g
      {A : Set} {P : A -> Prop} (fa: forall x, P x) (x : A) : P x.
    Proof. eauto. Qed.

    Ltac sf_wf_finish :=
      lazymatch goal with
      | H : list_assoc (final_values sf) _ = _ |- _ =>
        econstructor; vm_compute in H; inversion H; vm_compute; auto
      end.

    Ltac sf_wf_branch :=
      lazymatch goal with
      | a : index _ |- _ =>
        destruct a;
        lazymatch goal with
        | a' : index _ |- _ => sf_wf_branch
        | H : list_assoc (final_values sf) _ = _ |- _ => sf_wf_finish
        end
      | H : list_assoc (final_values sf) _ = _ |- _ => sf_wf_finish
      end.

    Lemma fv_toIMem_RV32I_MemReq_data0 :
      list_assoc (final_values sf) (RV32I.toIMem RV32I.MemReq.data0) = Some 2969%positive.
    Proof. vm_compute. easy. Qed.
    Lemma fv_toIMem_RV32I_MemReq_valid0 :
      list_assoc (final_values sf) (RV32I.toIMem RV32I.MemReq.valid0)
      = Some 3009%positive.
    Proof. vm_compute. easy. Qed.
    Lemma fv_fromIMem_RV32I_MemResp_data0 :
      list_assoc (final_values sf) (RV32I.fromIMem RV32I.MemResp.data0)
      = Some 3008%positive.
    Proof. vm_compute. easy. Qed.
    Lemma fv_fromIMem_RV32I_MemResp_valid0 :
      list_assoc (final_values sf) (RV32I.fromIMem RV32I.MemResp.valid0)
      = Some 3007%positive.
    Proof. vm_compute. easy. Qed.
    Lemma fv_toDMem_RV32I_MemReq_data0 :
      list_assoc (final_values sf) (RV32I.toDMem RV32I.MemReq.data0)
      = Some 1819%positive.
    Proof. vm_compute. easy. Qed.
    Lemma fv_toDMem_RV32I_MemReq_valid0 :
      list_assoc (final_values sf) (RV32I.toDMem RV32I.MemReq.valid0)
      = Some 3098%positive.
    Proof. vm_compute. easy. Qed.
    Lemma fv_fromDMem_RV32I_MemResp_data0 :
      list_assoc (final_values sf) (RV32I.fromDMem RV32I.MemResp.data0)
      = Some 3097%positive.
    Proof. vm_compute. easy. Qed.
    Lemma fv_fromDMem_RV32I_MemResp_valid0 :
      list_assoc (final_values sf) (RV32I.fromDMem RV32I.MemResp.valid0)
      = Some 3096%positive.
    Proof. vm_compute. easy. Qed.
    Lemma fv_f2d_RV32I_fromFetch_data0 :
      list_assoc (final_values sf) (RV32I.f2d RV32I.fromFetch.data0)
      = Some 2966%positive.
    Proof. vm_compute. easy. Qed.
    Lemma fv_f2d_RV32I_fromFetch_valid0 :
      list_assoc (final_values sf) (RV32I.f2d RV32I.fromFetch.valid0)
      = Some 2965%positive.
    Proof. vm_compute. easy. Qed.
    Lemma fv_f2dprim_RV32I_waitFromFetch_data0 :
      list_assoc (final_values sf) (RV32I.f2dprim RV32I.waitFromFetch.data0)
      = Some 2941%positive.
    Proof. vm_compute. easy. Qed.
    Lemma fv_f2dprim_RV32I_waitFromFetch_valid0 :
      list_assoc (final_values sf) (RV32I.f2dprim RV32I.waitFromFetch.valid0)
      = Some 2940%positive.
    Proof. vm_compute. easy. Qed.
    Lemma fv_d2e_RV32I_fromDecode_data0 :
      list_assoc (final_values sf) (RV32I.d2e RV32I.fromDecode.data0)
      = Some 2920%positive.
    Proof. vm_compute. easy. Qed.
    Lemma fv_d2e_RV32I_fromDecode_valid0 :
      list_assoc (final_values sf) (RV32I.d2e RV32I.fromDecode.valid0)
      = Some 2919%positive.
    Proof. vm_compute. easy. Qed.
    Lemma fv_e2w_RV32I_fromExecute_data0 :
      list_assoc (final_values sf) (RV32I.e2w RV32I.fromExecute.data0)
      = Some 1814%positive.
    Proof. vm_compute. easy. Qed.
    Lemma fv_e2w_RV32I_fromExecute_valid0 :
      list_assoc (final_values sf) (RV32I.e2w RV32I.fromExecute.valid0)
      = Some 1813%positive.
    Proof. vm_compute. easy. Qed.
    Lemma fv_rf_RV32I_Rf_rData_thisone :
      list_assoc (final_values sf) (RV32I.rf (RV32I.Rf.rData thisone))
      = Some 978%positive.
    Proof. vm_compute. easy. Qed.
    Lemma fv_rf_RV32I_Rf_rData_anotherone_thisone :
      list_assoc (final_values sf) ((RV32I.rf (RV32I.Rf.rData (anotherone thisone))))
      = Some 976%positive.
    Proof. vm_compute. easy. Qed.
    Lemma fv_rf_RV32I_Rf_rData_anotherone_anotherone_thisone :
      list_assoc (final_values sf) (RV32I.rf (RV32I.Rf.rData (anotherone (anotherone thisone))))
      = Some 974%positive.
    Proof. vm_compute. easy. Qed.
    Lemma fv_rf_RV32I_Rf_rData_anotherone_anotherone_anotherone_anotherone_thisone :
      list_assoc (final_values sf) (RV32I.rf (RV32I.Rf.rData (anotherone (anotherone (anotherone thisone)))))
      = Some 972%positive.
    Proof. vm_compute. easy. Qed.
    Lemma fv_rf_RV32I_Rf_rData_anotherone_anotherone_anotherone_anotherone_anotherone_thisone :
      list_assoc (final_values sf) (RV32I.rf (RV32I.Rf.rData (anotherone (anotherone (anotherone (anotherone thisone))))))
      = Some 970%positive.
    Proof. vm_compute. easy. Qed.
    Lemma fv_rf_RV32I_Rf_rData_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_thisone :
      list_assoc (final_values sf) (RV32I.rf (RV32I.Rf.rData (anotherone (anotherone (anotherone (anotherone (anotherone thisone)))))))
      = Some 968%positive.
    Proof. vm_compute. easy. Qed.
    Lemma fv_rf_RV32I_Rf_rData_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_thisone :
      list_assoc (final_values sf) (RV32I.rf (RV32I.Rf.rData (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone thisone))))))))
      = Some 966%positive.
    Proof. vm_compute. easy. Qed.
    Lemma fv_rf_RV32I_Rf_rData_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_thisone :
      list_assoc (final_values sf) (RV32I.rf (RV32I.Rf.rData (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone thisone)))))))))
      = Some 964%positive.
    Proof. vm_compute. easy. Qed.
    Lemma fv_rf_RV32I_Rf_rData_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_thisone :
      list_assoc (final_values sf) (RV32I.rf (RV32I.Rf.rData (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone thisone))))))))))
      = Some 962%positive.
    Proof. vm_compute. easy. Qed.
    Lemma fv_rf_RV32I_Rf_rData_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_thisone :
      list_assoc (final_values sf) (RV32I.rf (RV32I.Rf.rData (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone thisone)))))))))))
      = Some 960%positive.
    Proof. vm_compute. easy. Qed.
    Lemma fv_rf_RV32I_Rf_rData_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_thisone :
      list_assoc (final_values sf) (RV32I.rf (RV32I.Rf.rData (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone thisone))))))))))))
      = Some 958%positive.
    Proof. vm_compute. easy. Qed.
    Lemma fv_rf_RV32I_Rf_rData_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_thisone :
      list_assoc (final_values sf) (RV32I.rf (RV32I.Rf.rData (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone thisone)))))))))))))
      = Some 956%positive.
    Proof. vm_compute. easy. Qed.
    Lemma fv_rf_RV32I_Rf_rData_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_thisone :
      list_assoc (final_values sf) (RV32I.rf (RV32I.Rf.rData (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone thisone))))))))))))))
      = Some 954%positive.
    Proof. vm_compute. easy. Qed.
    Lemma fv_rf_RV32I_Rf_rData_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_thisone :
      list_assoc (final_values sf) (RV32I.rf (RV32I.Rf.rData (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone thisone)))))))))))))))
      = Some 952%positive.
    Proof. vm_compute. easy. Qed.
    Lemma fv_rf_RV32I_Rf_rData_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_thisone :
      list_assoc (final_values sf) (RV32I.rf (RV32I.Rf.rData (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone thisone))))))))))))))))
      = Some 950%positive.
    Proof. vm_compute. easy. Qed.
    Lemma fv_rf_RV32I_Rf_rData_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_thisone :
      list_assoc (final_values sf) (RV32I.rf (RV32I.Rf.rData (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone thisone)))))))))))))))))
      = Some 948%positive.
    Proof. vm_compute. easy. Qed.
    Lemma fv_rf_RV32I_Rf_rData_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_thisone :
      list_assoc (final_values sf) (RV32I.rf (RV32I.Rf.rData (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone thisone))))))))))))))))))
      = Some 946%positive.
    Proof. vm_compute. easy. Qed.
    Lemma fv_rf_RV32I_Rf_rData_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_thisone :
      list_assoc (final_values sf) (RV32I.rf (RV32I.Rf.rData (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone thisone)))))))))))))))))))
      = Some 944%positive.
    Proof. vm_compute. easy. Qed.
    Lemma fv_rf_RV32I_Rf_rData_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_thisone :
      list_assoc (final_values sf) (RV32I.rf (RV32I.Rf.rData (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone thisone))))))))))))))))))))
      = Some 942%positive.
    Proof. vm_compute. easy. Qed.
    Lemma fv_rf_RV32I_Rf_rData_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_thisone :
      list_assoc (final_values sf) (RV32I.rf (RV32I.Rf.rData (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone thisone)))))))))))))))))))))
      = Some 940%positive.
    Proof. vm_compute. easy. Qed.
    Lemma fv_rf_RV32I_Rf_rData_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_thisone :
      list_assoc (final_values sf) (RV32I.rf (RV32I.Rf.rData (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone thisone))))))))))))))))))))))
      = Some 938%positive.
    Proof. vm_compute. easy. Qed.
    Lemma fv_rf_RV32I_Rf_rData_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_thisone :
      list_assoc (final_values sf) (RV32I.rf (RV32I.Rf.rData (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone thisone)))))))))))))))))))))))
      = Some 936%positive.
    Proof. vm_compute. easy. Qed.
    Lemma fv_rf_RV32I_Rf_rData_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_thisone :
      list_assoc (final_values sf) (RV32I.rf (RV32I.Rf.rData (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone thisone))))))))))))))))))))))))
      = Some 934%positive.
    Proof. vm_compute. easy. Qed.
    Lemma fv_rf_RV32I_Rf_rData_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_thisone :
      list_assoc (final_values sf) (RV32I.rf (RV32I.Rf.rData (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone thisone)))))))))))))))))))))))))
      = Some 932%positive.
    Proof. vm_compute. easy. Qed.
    Lemma fv_rf_RV32I_Rf_rData_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_thisone :
      list_assoc (final_values sf) (RV32I.rf (RV32I.Rf.rData (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone thisone))))))))))))))))))))))))))
      = Some 930%positive.
    Proof. vm_compute. easy. Qed.
    Lemma fv_rf_RV32I_Rf_rData_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_thisone :
      list_assoc (final_values sf) (RV32I.rf (RV32I.Rf.rData (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone thisone)))))))))))))))))))))))))))
      = Some 928%positive.
    Proof. vm_compute. easy. Qed.
    Lemma fv_rf_RV32I_Rf_rData_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_thisone :
      list_assoc (final_values sf) (RV32I.rf (RV32I.Rf.rData (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone thisone))))))))))))))))))))))))))))
      = Some 926%positive.
    Proof. vm_compute. easy. Qed.
    Lemma fv_rf_RV32I_Rf_rData_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_thisone :
      list_assoc (final_values sf) (RV32I.rf (RV32I.Rf.rData (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone thisone)))))))))))))))))))))))))))))
      = Some 924%positive.
    Proof. vm_compute. easy. Qed.
    Lemma fv_rf_RV32I_Rf_rData_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_thisone :
      list_assoc (final_values sf) (RV32I.rf (RV32I.Rf.rData (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone thisone))))))))))))))))))))))))))))))
      = Some 922%positive.
    Proof. vm_compute. easy. Qed.
    Lemma fv_rf_RV32I_Rf_rData_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_thisone :
      list_assoc (final_values sf) (RV32I.rf (RV32I.Rf.rData (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone thisone)))))))))))))))))))))))))))))))
      = Some 920%positive.
    Proof. vm_compute. easy. Qed.
    Lemma fv_rf_RV32I_Rf_rData_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_thisone :
      list_assoc (final_values sf) (RV32I.rf (RV32I.Rf.rData (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone thisone))))))))))))))))))))))))))))))))
      = Some 918%positive.
    Proof. vm_compute. easy. Qed.
    Lemma fv_rf_RV32I_Rf_rData_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_thisone :
      list_assoc (final_values sf) (RV32I.rf (RV32I.Rf.rData (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone thisone)))))))))))))))))))))))))))))))))
      = Some 916%positive.
    Proof. vm_compute. easy. Qed.
    Lemma fv_stack_RV32I_ShadowStack_size :
      list_assoc (final_values sf) (RV32I.stack RV32I.ShadowStack.size)
      = Some 1811%positive.
    Proof. vm_compute. easy. Qed.
    Lemma fv_stack_RV32I_ShadowStack_stack_thisone :
      list_assoc
        (final_values sf)
        (RV32I.stack (RV32I.ShadowStack.stack (
          (@thisone (index (Init.Nat.pred (2^RV32I.ShadowStack.index_sz)))))
         ))
      = Some 1809%positive.
    Proof. vm_compute. easy. Qed.
    Lemma fv_stack_RV32I_ShadowStack_stack_anotherone_thisone :
      list_assoc
        (final_values sf)
        (RV32I.stack (RV32I.ShadowStack.stack (
          @anotherone
            (index (Init.Nat.pred (2 ^ RV32I.ShadowStack.index_sz)))
            (@thisone (index
              (0 + 0*2^0 + 1*2^1 + 1*2^Nat.log2 (Nat.pred (RV32I.ShadowStack.capacity + 1)))
           )))
        ))
      = Some 1807%positive.
    Proof. vm_compute. easy. Qed.
    Lemma fv_stack_RV32I_ShadowStack_stack_anotherone_anotherone_thisone :
      list_assoc
        (final_values sf)
        (RV32I.stack (RV32I.ShadowStack.stack (
          (@anotherone
            (index
              (Init.Nat.pred
                (Nat.pow (S (S O))
                  (Nat.log2_up
                    (Init.Nat.add RV32I.ShadowStack.capacity (S O))))))
            (@anotherone
              (index
                (Nat.add
                  (Nat.add
                    (Nat.add O (Nat.mul O (Nat.pow (S (S O)) O)))
                    (Nat.mul (S O) (Nat.pow (S (S O)) (S O))))
                  (Nat.mul
                    (S O)
                    (Nat.pow
                      (S (S O))
                      (Nat.log2 (Nat.pred
                        (Init.Nat.add RV32I.ShadowStack.capacity (S O))))))))
               (@thisone
                  (index
                     (Nat.add
                        (Nat.add
                           (Nat.add O
                              (Nat.mul (S O) (Nat.pow (S (S O)) O)))
                           (Nat.mul O (Nat.pow (S (S O)) (S O))))
                        (Nat.mul (S O)
                           (Nat.pow (S (S O))
                              (Nat.log2
                                 (Nat.pred
                                    (Init.Nat.add
                                       RV32I.ShadowStack.capacity
                                       (S O))))))))))))))
      = Some 1805%positive.
    Proof. vm_compute. easy. Qed.

    Lemma fv_stack_RV32I_ShadowStack_stack_anotherone_anotherone_anotherone_thisone :
      list_assoc
        (final_values sf)
        (RV32I.stack (RV32I.ShadowStack.stack (
          @anotherone (index (Init.Nat.pred (2^RV32I.ShadowStack.index_sz))) (anotherone (anotherone thisone))))
        )
      = Some 1803%positive.
    Proof. vm_compute. easy. Qed.
    Lemma fv_stack_RV32I_ShadowStack_stack_anotherone_anotherone_anotherone_anotherone_thisone :
      list_assoc
        (final_values sf)
        (RV32I.stack (RV32I.ShadowStack.stack (
          @anotherone (index (Init.Nat.pred (2^RV32I.ShadowStack.index_sz))) (anotherone (anotherone (anotherone thisone)))))
        )
      = Some 1801%positive.
    Proof. vm_compute. easy. Qed.
    Lemma fv_stack_RV32I_ShadowStack_stack_anotherone_anotherone_anotherone_anotherone_anotherone_thisone :
      list_assoc
        (final_values sf)
        (RV32I.stack (RV32I.ShadowStack.stack (
          @anotherone (index (Init.Nat.pred (2^RV32I.ShadowStack.index_sz))) (anotherone (anotherone (anotherone (anotherone thisone))))))
        )
      = Some 1799%positive.
    Proof. vm_compute. easy. Qed.
    Lemma fv_stack_RV32I_ShadowStack_stack_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_thisone :
      list_assoc
        (final_values sf)
        (RV32I.stack (RV32I.ShadowStack.stack (
          @anotherone (index (Init.Nat.pred (2^RV32I.ShadowStack.index_sz))) (anotherone (anotherone (anotherone (anotherone (anotherone thisone)))))))
        )
      = Some 1797%positive.
    Proof. vm_compute. easy. Qed.
    Lemma fv_stack_RV32I_ShadowStack_stack_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_thisone :
      list_assoc
        (final_values sf)
        (RV32I.stack (RV32I.ShadowStack.stack (
          @anotherone (index (Init.Nat.pred (2^RV32I.ShadowStack.index_sz))) (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone thisone))))))))
        )
      = Some 1795%positive.
    Proof. vm_compute. easy. Qed.
    Lemma fv_scoreboard_RV32I_Scoreboard_Scores_RV32I_Scoreboard_Rf_rData_thisone :
      list_assoc (final_values sf) (RV32I.scoreboard ((RV32I.Scoreboard.Scores (RV32I.Scoreboard.Rf.rData thisone))))
      = Some 2918%positive.
    Proof. vm_compute. easy. Qed.
    Lemma fv_scoreboard_RV32I_Scoreboard_Scores_RV32I_Scoreboard_Rf_rData_anotherone_thisone :
      list_assoc (final_values sf) (RV32I.scoreboard ((RV32I.Scoreboard.Scores (RV32I.Scoreboard.Rf.rData (anotherone thisone)))))
      = Some 2917%positive.
    Proof. vm_compute. easy. Qed.
    Lemma fv_scoreboard_RV32I_Scoreboard_Scores_RV32I_Scoreboard_Rf_rData_anotherone_anotherone_thisone :
      list_assoc (final_values sf) (RV32I.scoreboard ((RV32I.Scoreboard.Scores (RV32I.Scoreboard.Rf.rData (anotherone (anotherone thisone))))))
      = Some 2916%positive.
    Proof. vm_compute. easy. Qed.
    Lemma fv_scoreboard_RV32I_Scoreboard_Scores_RV32I_Scoreboard_Rf_rData_anotherone_anotherone_anotherone_thisone :
      list_assoc (final_values sf) (RV32I.scoreboard ((RV32I.Scoreboard.Scores (RV32I.Scoreboard.Rf.rData (anotherone (anotherone (anotherone thisone)))))))
      = Some 2915%positive.
    Proof. vm_compute. easy. Qed.
    Lemma fv_scoreboard_RV32I_Scoreboard_Scores_RV32I_Scoreboard_Rf_rData_anotherone_anotherone_anotherone_anotherone_thisone :
      list_assoc (final_values sf) (RV32I.scoreboard ((RV32I.Scoreboard.Scores (RV32I.Scoreboard.Rf.rData (anotherone (anotherone (anotherone (anotherone thisone))))))))
      = Some 2914%positive.
    Proof. vm_compute. easy. Qed.
    Lemma fv_scoreboard_RV32I_Scoreboard_Scores_RV32I_Scoreboard_Rf_rData_anotherone_anotherone_anotherone_anotherone_anotherone_thisone :
      list_assoc (final_values sf) (RV32I.scoreboard ((RV32I.Scoreboard.Scores (RV32I.Scoreboard.Rf.rData (anotherone (anotherone (anotherone (anotherone (anotherone thisone)))))))))
      = Some 2913%positive.
    Proof. vm_compute. easy. Qed.
    Lemma fv_scoreboard_RV32I_Scoreboard_Scores_RV32I_Scoreboard_Rf_rData_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_thisone :
      list_assoc (final_values sf) (RV32I.scoreboard ((RV32I.Scoreboard.Scores (RV32I.Scoreboard.Rf.rData (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone thisone))))))))))
      = Some 2912%positive.
    Proof. vm_compute. easy. Qed.
    Lemma fv_scoreboard_RV32I_Scoreboard_Scores_RV32I_Scoreboard_Rf_rData_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_thisone :
      list_assoc (final_values sf) (RV32I.scoreboard ((RV32I.Scoreboard.Scores (RV32I.Scoreboard.Rf.rData (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone thisone)))))))))))
      = Some 2911%positive.
    Proof. vm_compute. easy. Qed.
    Lemma fv_scoreboard_RV32I_Scoreboard_Scores_RV32I_Scoreboard_Rf_rData_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_thisone :
      list_assoc (final_values sf) (RV32I.scoreboard ((RV32I.Scoreboard.Scores (RV32I.Scoreboard.Rf.rData (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone thisone))))))))))))
      = Some 2910%positive.
    Proof. vm_compute. easy. Qed.
    Lemma fv_scoreboard_RV32I_Scoreboard_Scores_RV32I_Scoreboard_Rf_rData_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_thisone :
      list_assoc (final_values sf) (RV32I.scoreboard ((RV32I.Scoreboard.Scores (RV32I.Scoreboard.Rf.rData (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone thisone)))))))))))))
      = Some 2909%positive.
    Proof. vm_compute. easy. Qed.
    Lemma fv_scoreboard_RV32I_Scoreboard_Scores_RV32I_Scoreboard_Rf_rData_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_thisone :
      list_assoc (final_values sf) (RV32I.scoreboard ((RV32I.Scoreboard.Scores (RV32I.Scoreboard.Rf.rData (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone thisone))))))))))))))
      = Some 2908%positive.
    Proof. vm_compute. easy. Qed.
    Lemma fv_scoreboard_RV32I_Scoreboard_Scores_RV32I_Scoreboard_Rf_rData_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_thisone :
      list_assoc (final_values sf) (RV32I.scoreboard ((RV32I.Scoreboard.Scores (RV32I.Scoreboard.Rf.rData (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone thisone)))))))))))))))
      = Some 2907%positive.
    Proof. vm_compute. easy. Qed.
    Lemma fv_scoreboard_RV32I_Scoreboard_Scores_RV32I_Scoreboard_Rf_rData_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_thisone :
      list_assoc (final_values sf) (RV32I.scoreboard ((RV32I.Scoreboard.Scores (RV32I.Scoreboard.Rf.rData (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone thisone))))))))))))))))
      = Some 2906%positive.
    Proof. vm_compute. easy. Qed.
    Lemma fv_scoreboard_RV32I_Scoreboard_Scores_RV32I_Scoreboard_Rf_rData_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_thisone :
      list_assoc (final_values sf) (RV32I.scoreboard ((RV32I.Scoreboard.Scores (RV32I.Scoreboard.Rf.rData (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone thisone)))))))))))))))))
      = Some 2905%positive.
    Proof. vm_compute. easy. Qed.
    Lemma fv_scoreboard_RV32I_Scoreboard_Scores_RV32I_Scoreboard_Rf_rData_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_thisone :
      list_assoc (final_values sf) (RV32I.scoreboard ((RV32I.Scoreboard.Scores (RV32I.Scoreboard.Rf.rData (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone thisone))))))))))))))))))
      = Some 2904%positive.
    Proof. vm_compute. easy. Qed.
    Lemma fv_scoreboard_RV32I_Scoreboard_Scores_RV32I_Scoreboard_Rf_rData_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_thisone :
      list_assoc (final_values sf) (RV32I.scoreboard ((RV32I.Scoreboard.Scores (RV32I.Scoreboard.Rf.rData (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone thisone)))))))))))))))))))
      = Some 2903%positive.
    Proof. vm_compute. easy. Qed.
    Lemma fv_scoreboard_RV32I_Scoreboard_Scores_RV32I_Scoreboard_Rf_rData_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_thisone :
      list_assoc (final_values sf) (RV32I.scoreboard ((RV32I.Scoreboard.Scores (RV32I.Scoreboard.Rf.rData (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone thisone))))))))))))))))))))
      = Some 2902%positive.
    Proof. vm_compute. easy. Qed.
    Lemma fv_scoreboard_RV32I_Scoreboard_Scores_RV32I_Scoreboard_Rf_rData_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_thisone :
      list_assoc (final_values sf) (RV32I.scoreboard ((RV32I.Scoreboard.Scores (RV32I.Scoreboard.Rf.rData (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone thisone)))))))))))))))))))))
      = Some 2901%positive.
    Proof. vm_compute. easy. Qed.
    Lemma fv_scoreboard_RV32I_Scoreboard_Scores_RV32I_Scoreboard_Rf_rData_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_thisone :
      list_assoc (final_values sf) (RV32I.scoreboard ((RV32I.Scoreboard.Scores (RV32I.Scoreboard.Rf.rData (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone thisone))))))))))))))))))))))
      = Some 2900%positive.
    Proof. vm_compute. easy. Qed.
    Lemma fv_scoreboard_RV32I_Scoreboard_Scores_RV32I_Scoreboard_Rf_rData_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_thisone :
      list_assoc (final_values sf) (RV32I.scoreboard ((RV32I.Scoreboard.Scores (RV32I.Scoreboard.Rf.rData (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone thisone)))))))))))))))))))))))
      = Some 2899%positive.
    Proof. vm_compute. easy. Qed.
    Lemma fv_scoreboard_RV32I_Scoreboard_Scores_RV32I_Scoreboard_Rf_rData_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_thisone :
      list_assoc (final_values sf) (RV32I.scoreboard ((RV32I.Scoreboard.Scores (RV32I.Scoreboard.Rf.rData (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone thisone))))))))))))))))))))))))
      = Some 2898%positive.
    Proof. vm_compute. easy. Qed.
    Lemma fv_scoreboard_RV32I_Scoreboard_Scores_RV32I_Scoreboard_Rf_rData_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_thisone :
      list_assoc (final_values sf) (RV32I.scoreboard ((RV32I.Scoreboard.Scores (RV32I.Scoreboard.Rf.rData (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone thisone)))))))))))))))))))))))))
      = Some 2897%positive.
    Proof. vm_compute. easy. Qed.
    Lemma fv_scoreboard_RV32I_Scoreboard_Scores_RV32I_Scoreboard_Rf_rData_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_thisone :
      list_assoc (final_values sf) (RV32I.scoreboard ((RV32I.Scoreboard.Scores (RV32I.Scoreboard.Rf.rData (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone thisone))))))))))))))))))))))))))
      = Some 2896%positive.
    Proof. vm_compute. easy. Qed.
    Lemma fv_scoreboard_RV32I_Scoreboard_Scores_RV32I_Scoreboard_Rf_rData_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_thisone :
      list_assoc (final_values sf) (RV32I.scoreboard ((RV32I.Scoreboard.Scores (RV32I.Scoreboard.Rf.rData (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone thisone)))))))))))))))))))))))))))
      = Some 2895%positive.
    Proof. vm_compute. easy. Qed.
    Lemma fv_scoreboard_RV32I_Scoreboard_Scores_RV32I_Scoreboard_Rf_rData_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_thisone :
      list_assoc (final_values sf) (RV32I.scoreboard ((RV32I.Scoreboard.Scores (RV32I.Scoreboard.Rf.rData (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone thisone))))))))))))))))))))))))))))
      = Some 2894%positive.
    Proof. vm_compute. easy. Qed.
    Lemma fv_scoreboard_RV32I_Scoreboard_Scores_RV32I_Scoreboard_Rf_rData_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_thisone :
      list_assoc (final_values sf) (RV32I.scoreboard ((RV32I.Scoreboard.Scores (RV32I.Scoreboard.Rf.rData (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone thisone)))))))))))))))))))))))))))))
      = Some 2893%positive.
    Proof. vm_compute. easy. Qed.
    Lemma fv_scoreboard_RV32I_Scoreboard_Scores_RV32I_Scoreboard_Rf_rData_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_thisone :
      list_assoc (final_values sf) (RV32I.scoreboard ((RV32I.Scoreboard.Scores (RV32I.Scoreboard.Rf.rData (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone thisone))))))))))))))))))))))))))))))
      = Some 2892%positive.
    Proof. vm_compute. easy. Qed.
    Lemma fv_scoreboard_RV32I_Scoreboard_Scores_RV32I_Scoreboard_Rf_rData_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_thisone :
      list_assoc (final_values sf) (RV32I.scoreboard ((RV32I.Scoreboard.Scores (RV32I.Scoreboard.Rf.rData (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone thisone)))))))))))))))))))))))))))))))
      = Some 2891%positive.
    Proof. vm_compute. easy. Qed.
    Lemma fv_scoreboard_RV32I_Scoreboard_Scores_RV32I_Scoreboard_Rf_rData_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_thisone :
      list_assoc (final_values sf) (RV32I.scoreboard ((RV32I.Scoreboard.Scores (RV32I.Scoreboard.Rf.rData (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone thisone))))))))))))))))))))))))))))))))
      = Some 2890%positive.
    Proof. vm_compute. easy. Qed.
    Lemma fv_scoreboard_RV32I_Scoreboard_Scores_RV32I_Scoreboard_Rf_rData_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_thisone :
      list_assoc (final_values sf) (RV32I.scoreboard ((RV32I.Scoreboard.Scores (RV32I.Scoreboard.Rf.rData (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone thisone)))))))))))))))))))))))))))))))))
      = Some 2889%positive.
    Proof. vm_compute. easy. Qed.
    Lemma fv_scoreboard_RV32I_Scoreboard_Scores_RV32I_Scoreboard_Rf_rData_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_thisone :
      list_assoc (final_values sf) (RV32I.scoreboard ((RV32I.Scoreboard.Scores (RV32I.Scoreboard.Rf.rData (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone thisone))))))))))))))))))))))))))))))))))
      = Some 2888%positive.
    Proof. vm_compute. easy. Qed.
    Lemma fv_scoreboard_RV32I_Scoreboard_Scores_RV32I_Scoreboard_Rf_rData_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_anotherone_thisone :
      list_assoc (final_values sf) (RV32I.scoreboard ((RV32I.Scoreboard.Scores (RV32I.Scoreboard.Rf.rData (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone (anotherone thisone)))))))))))))))))))))))))))))))))))
      = Some 2887%positive.
    Proof. vm_compute. easy. Qed.
    Lemma fv_cycle_count :
      list_assoc (final_values sf) (RV32I.cycle_count)
      = Some 3104%positive.
    Proof. vm_compute. easy. Qed.
    Lemma fv_instr_count :
      list_assoc (final_values sf) (RV32I.instr_count)
      = Some 850%positive.
    Proof. vm_compute. easy. Qed.
    Lemma fv_pc :
      list_assoc (final_values sf) (RV32I.pc)
      = Some 2964%positive.
    Proof. vm_compute. easy. Qed.
    Lemma fv_epoch :
      list_assoc (final_values sf) (RV32I.epoch)
      = Some 1791%positive.
    Proof. vm_compute. easy. Qed.
    Lemma fv_debug :
      list_assoc (final_values sf) (RV32I.debug)
      = Some 3110%positive.
    Proof. vm_compute. easy. Qed.
    Lemma fv_on_off :
      list_assoc (final_values sf) (RV32I.on_off)
      = Some 99%positive.
    Proof. vm_compute. easy. Qed.
    Lemma fv_halt :
      list_assoc (final_values sf) (RV32I.halt)
      = Some 1789%positive.
    Proof. vm_compute. easy. Qed.

    Theorem sf_wf : wf_sf RV32I.R ext_Sigma sf.
    Proof.
      set (sok :=
        schedule_to_simple_form_ok (sigma := ext_sigma) (wt_sigma := wt_sigma)
          REnv ctx RV32I.R wt_env drules rv_schedule rv_schedule_good sf
          sf_def tret wt_renv
      ).
      destruct sok.
      destruct H0.
      destruct H1.
      constructor.
      - assumption.
      - assumption.
      - intros.
        destruct reg.
        + destruct state; econstructor.
          * rewrite fv_toIMem_RV32I_MemReq_data0 in H3. inversion H3. vm_compute. auto.
          * rewrite fv_toIMem_RV32I_MemReq_valid0 in H3. inversion H3. vm_compute. auto.
        + destruct state; econstructor.
          * rewrite fv_fromIMem_RV32I_MemResp_data0 in H3. inversion H3. vm_compute. auto.
          * rewrite fv_fromIMem_RV32I_MemResp_valid0 in H3. inversion H3. vm_compute. auto.
        + destruct state; econstructor.
          * rewrite fv_toDMem_RV32I_MemReq_data0 in H3. inversion H3. vm_compute. auto.
          * rewrite fv_toDMem_RV32I_MemReq_valid0 in H3. inversion H3. vm_compute. auto.
        + destruct state; econstructor.
          * rewrite fv_fromDMem_RV32I_MemResp_data0 in H3. inversion H3. vm_compute. auto.
          * rewrite fv_fromDMem_RV32I_MemResp_valid0 in H3. inversion H3. vm_compute. auto.
        + destruct state; econstructor.
          * rewrite fv_f2d_RV32I_fromFetch_data0 in H3. inversion H3. vm_compute. auto.
          * rewrite fv_f2d_RV32I_fromFetch_valid0 in H3. inversion H3. vm_compute. auto.
        + destruct state; econstructor.
          * rewrite fv_f2dprim_RV32I_waitFromFetch_data0 in H3. inversion H3. vm_compute. auto.
          * rewrite fv_f2dprim_RV32I_waitFromFetch_valid0 in H3. inversion H3. vm_compute. auto.
        + destruct state; econstructor.
          * rewrite fv_d2e_RV32I_fromDecode_data0 in H3. inversion H3. vm_compute. auto.
          * rewrite fv_d2e_RV32I_fromDecode_valid0 in H3. inversion H3. vm_compute. auto.
        + destruct state; econstructor.
          * rewrite fv_e2w_RV32I_fromExecute_data0 in H3. inversion H3. vm_compute. auto.
          * rewrite fv_e2w_RV32I_fromExecute_valid0 in H3. inversion H3. vm_compute. auto.
        + cheat.
        + destruct state.
          * econstructor. rewrite fv_stack_RV32I_ShadowStack_size in H3. inversion H3. vm_compute. auto.
          * destruct n. econstructor. rewrite fv_stack_RV32I_ShadowStack_stack_thisone in H3. inversion H3. vm_compute. auto.
            destruct a. econstructor. rewrite fv_stack_RV32I_ShadowStack_stack_anotherone_thisone in H3. inversion H3. vm_compute. auto.
            destruct a. econstructor. rewrite fv_stack_RV32I_ShadowStack_stack_anotherone_anotherone_thisone in H3. inversion H3. vm_compute. auto.
            cheat.
        + cheat.
        + rewrite fv_cycle_count in H3. inversion H3. econstructor. vm_compute. auto.
        + rewrite fv_instr_count in H3. inversion H3. econstructor. vm_compute. auto.
        + rewrite fv_pc in H3. inversion H3. econstructor. vm_compute. auto.
        + rewrite fv_epoch in H3. inversion H3. econstructor. vm_compute. auto.
        + rewrite fv_debug in H3. inversion H3. econstructor. vm_compute. auto.
        + rewrite fv_on_off in H3. inversion H3. econstructor. vm_compute. auto.
        + rewrite fv_halt in H3. inversion H3. econstructor. vm_compute. auto.
        (* + sf_wf_branch. *)
        (* + destruct state. sf_wf_branch. *)
        (* + destruct state. sf_wf_finish. sf_wf_branch. *)
        (* + destruct state. destruct state. sf_wf_branch. *)
      (* Qed. TODO Validation is way too slow! vm_compute related? *)
      Qed.

    Ltac eautosfwf :=
      lazymatch goal with
      | |- prune_irrelevant _ _ = Some _ =>
        unfold prune_irrelevant; vm_compute list_assoc; eauto
      | RV: getenv REnv ctx RV32I.halt = Bits [true],
        WTRENV : Wt.wt_renv RV32I.R REnv ctx
        |- wf_sf RV32I.R ext_Sigma (replace_reg _ _ _) =>
        apply (wf_replace_reg _ _ _ WTRENV _ _ _ RV); eautosfwf
      | |- wf_sf RV32I.R ext_Sigma (simplify_sf _ _ _) =>
        apply wf_sf_simplify_sf; eautosfwf
      | |- wf_sf RV32I.R ext_Sigma (prune_irrelevant_aux _ _ _) =>
        eapply wf_sf_prune_irrelevant_aux; vm_compute list_assoc; eautosfwf
      | |- wf_sf RV32I.R ext_Sigma (collapse_sf _) =>
        eapply wf_collapse_sf; eautosfwf
      | |- wf_sf RV32I.R ext_Sigma sf => apply sf_wf
      | |- wf_sf _ _ _ => apply sf_wf
      | _ => eauto
      end.

    Ltac isolate_sf :=
      lazymatch goal with
      | |- getenv _ (interp_cycle _ _ ?x) _ = _ => set (sf := x)
      end.

    Ltac get_var x sf :=
      set (var_val := Maps.PTree.get (Pos.of_nat x) (vars sf));
      vm_compute in var_val.

    Lemma fail_schedule:
      forall (HALT_TRUE: getenv REnv ctx RV32I.halt = Bits [true]),
      getenv REnv (interp_cycle ctx ext_sigma sf) RV32I.halt = Bits [true].
    Proof.
      intros.
      erewrite <- replace_reg_interp_cycle_ok; eautosfwf.
      erewrite <- simplify_sf_interp_cycle_ok; eautosfwf.
      erewrite <- prune_irrelevant_interp_cycle_ok; eautosfwf.
      erewrite <- collapse_prune_ok; eautosfwf.
      erewrite <- simplify_sf_interp_cycle_ok; eautosfwf.
      erewrite <- prune_irrelevant_interp_cycle_ok; eautosfwf.
      erewrite <- collapse_prune_ok; eautosfwf.
      erewrite <- simplify_sf_interp_cycle_ok; eautosfwf.
      eapply getenv_interp; eautosfwf; vm_compute; eauto.
    Qed.

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
