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
        apply (wf_sf_replace_reg _ _ _ WTRENV _ _ _ RV); eautosfwf
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
    Ltac replace_reg := erewrite replace_reg_interp_cycle_ok; eautosfwf.
    Ltac simplify := erewrite simplify_sf_interp_cycle_ok; eautosfwf.
    Ltac prune := erewrite prune_irrelevant_interp_cycle_ok; eautosfwf.
    Ltac collapse := erewrite collapse_prune_interp_cycle_ok; eautosfwf.
    Ltac finish := eapply getenv_interp; eautosfwf; vm_compute; eauto.

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
      replace_reg. simplify. prune. collapse. simplify.
      prune. collapse. simplify.
      finish.
    Qed.

  Definition cycle (r: env_t ContextEnv (fun _ : RV32I.reg_t => val)) :=
    UntypedSemantics.interp_dcycle drules r ext_sigma rv_schedule.

  Definition env_type := env_t REnv RV32I.R.
  Definition initial_env := create REnv RV32I.r.

  Definition CEnv := @ContextEnv RV32I.reg_t RV32I.FiniteType_reg_t.
  Definition initial_context_env := CEnv.(create) (RV32I.r).

  Definition f_init := fun x => val_of_value (initial_context_env.[x]).
