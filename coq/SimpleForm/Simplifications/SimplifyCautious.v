Require Import Koika.KoikaForm.Untyped.UntypedSemantics.
Require Import Koika.SimpleForm.Interpretation.
Require Import Koika.SimpleForm.Operations.
Require Import Koika.BitsToLists.
Require Import Koika.KoikaForm.SimpleVal.
Require Import Koika.KoikaForm.Types.
Require Import Koika.SimpleForm.SimpleForm.
Require Import Koika.Utils.EqDec.
Require Import Koika.Utils.Maps.
Require Import Koika.Utils.Environments.

Section SimplifyCautious.
  Context {pos_t reg_t ext_fn_t rule_name_t: Type}.
  Context {reg_t_eq_dec: EqDec reg_t}.
  Context {ext_fn_t_eq_dec: EqDec ext_fn_t}.
  Context {REnv: Env reg_t}.
  Context (R: reg_t -> type).
  Context (Sigma: ext_fn_t -> ExternalSignature).
  Local Definition ext_funs_defs := forall f: ext_fn_t, val -> val.
  Local Definition UREnv := REnv.(env_t) (fun _ => val).
  Context (r: UREnv).
  Context (sigma: ext_funs_defs).
  Local Definition sact := sact (ext_fn_t := ext_fn_t) (reg_t := reg_t).
  Local Definition eval_sact := eval_sact r sigma.
  Local Definition wf_sf := wf_sf R Sigma.
  Hypothesis WTRENV: Wt.wt_renv R REnv r.
  Context {
    wt_sigma:
    forall ufn vc, wt_val (arg1Sig (Sigma ufn)) vc
    -> wt_val (retSig (Sigma ufn)) (sigma ufn vc)
  }.

  Fixpoint simplify_sact_cautious (ua: sact) : sact :=
    match ua with
    | SIf (SConst (Bits [true])) tb fb => simplify_sact_cautious tb
    | SIf (SConst (Bits [false])) tb fb => simplify_sact_cautious fb
    | SIf cond tb fb =>
      SIf
        (simplify_sact_cautious cond) (simplify_sact_cautious tb)
        (simplify_sact_cautious fb)
    | SBinop (PrimUntyped.UBits2 PrimUntyped.UAnd) (SConst (Bits [true])) ua2 =>
      (simplify_sact_cautious ua2)
    | SBinop (PrimUntyped.UBits2 PrimUntyped.UAnd) ua1 (SConst (Bits [true])) =>
      (simplify_sact_cautious ua1)
    | SBinop (PrimUntyped.UBits2 PrimUntyped.UAnd) (SConst (Bits [false])) _ =>
      SConst (Bits [false])
    | SBinop (PrimUntyped.UBits2 PrimUntyped.UAnd) _ (SConst (Bits [false])) =>
      SConst (Bits [false])
    | SBinop (PrimUntyped.UBits2 PrimUntyped.UOr) (SConst (Bits [true])) _ =>
      SConst (Bits [true])
    | SBinop (PrimUntyped.UBits2 PrimUntyped.UOr) _ (SConst (Bits [true])) =>
      SConst (Bits [true])
    | SBinop (PrimUntyped.UBits2 PrimUntyped.UOr) (SConst (Bits [false])) ua2 =>
      (simplify_sact_cautious ua2)
    | SBinop (PrimUntyped.UBits2 PrimUntyped.UOr) ua1 (SConst (Bits [false])) =>
      (simplify_sact_cautious ua1)
    | SBinop _ (SConst _) (SConst _) =>
      match eval_sact_no_vars r sigma ua with
      | Some r => SConst r
      | None => ua
      end
    | SBinop (PrimUntyped.UEq b) a1 a2 =>
      SBinop (PrimUntyped.UEq b) (simplify_sact_cautious a1) (simplify_sact_cautious a2)
    | SBinop ufn a1 a2 =>
      SBinop ufn (simplify_sact_cautious a1) (simplify_sact_cautious a2)
    | SUnop (PrimUntyped.UBits1 UNot) (SConst (Bits [false])) => SConst (Bits [true])
    | SUnop (PrimUntyped.UBits1 UNot) (SConst (Bits [true])) => SConst (Bits [false])
    | SUnop _ (SConst _) =>
      match eval_sact_no_vars r sigma ua with
      | Some r => SConst r
      | None => ua
      end
    | SUnop ufn a => SUnop ufn (simplify_sact_cautious a)
    | SExternalCall ufn a => SExternalCall ufn (simplify_sact_cautious a)
    | _ => ua
    end.

  Definition simplify_sf_cautious (sf: simple_form) := {|
    final_values := final_values sf;
    vars :=
      Maps.PTree.map (fun _ '(t, a) => (t, simplify_sact_cautious a)) (vars sf)
  |}.

  Lemma simplify_sf_cautious_wt_sact_ok':
    forall sf s t (WTS: wt_sact (Sigma := Sigma) R (vars sf) s t),
    wt_sact (Sigma := Sigma) R (vars (simplify_sf_cautious sf)) s t.
  Proof.
    intros.
    induction WTS; econstructor; eauto.
    unfold simplify_sf_cautious.
    setoid_rewrite Maps.PTree.gmap.
    unfold option_map. setoid_rewrite H. easy.
  Qed.

  Lemma wt_simplify_sact_cautious:
    forall vss a t,
    wt_sact R (Sigma:=Sigma) vss a t
    -> wt_sact R (Sigma:=Sigma) vss (simplify_sact_cautious a) t.
  Proof.
  Admitted.

  Lemma simplify_sact_cautious_wt_sact_ok':
    forall vvs a t (WTS: wt_sact (Sigma := Sigma) R vvs a t),
    wt_sact (Sigma := Sigma) R vvs (simplify_sact_cautious a) t.
  Proof. apply wt_simplify_sact_cautious. Qed.

  Lemma simplify_sf_cautious_wtvvs_ok':
    forall sf (WTVVS: wt_vvs (Sigma := Sigma) R (vars sf)),
    wt_vvs (Sigma := Sigma) R (vars (simplify_sf_cautious sf)).
  Proof.
    intros. unfold wt_vvs. intros.
    apply simplify_sf_cautious_wt_sact_ok'.
    unfold simplify_sf_cautious in H.
    simpl in H.
    rewrite Maps.PTree.gmap in H. unfold option_map in H.
    destr_in H. destruct p.
    - apply Some_inj in H. apply pair_inj in H. destruct H. subst t0.
      inv H0. apply simplify_sact_cautious_wt_sact_ok'; eauto.
    - easy.
  Qed.

  Lemma simplify_sact_cautious_var_in_sact_ok':
    forall s v (VIS: var_in_sact (simplify_sact_cautious s) v),
    var_in_sact s v.
  Proof.
  Admitted.

  Lemma simplify_sf_cautious_vvssv_ok':
    forall sf (VVSSV: vvs_smaller_variables (vars sf)),
    vvs_smaller_variables (vars (simplify_sf_cautious sf)).
  Proof.
    intros.
    unfold vvs_smaller_variables in *. intros.
    unfold simplify_sf_cautious in H. simpl in H.
    rewrite Maps.PTree.gmap in H. unfold option_map in H.
    destr_in H. destruct p.
    - apply Some_inj in H. apply pair_inj in H. destruct H. subst t0.
      eapply VVSSV; eauto. inv H1.
      apply simplify_sact_cautious_var_in_sact_ok'. eauto.
    - easy.
  Qed.

  Lemma wf_sf_simplify_sf_cautious:
    forall sf, wf_sf sf -> wf_sf (simplify_sf_cautious sf).
  Proof.
    destruct 1; constructor.
    eapply simplify_sf_cautious_wtvvs_ok'; eauto.
    eapply simplify_sf_cautious_vvssv_ok'; eauto.
    simpl. intros.
    eapply wf_sf_final in H.
    eapply simplify_sf_cautious_wt_sact_ok'. auto.
  Qed.

  Lemma simplify_sact_cautious_correct:
    forall vvs (WTV: wt_vvs R (Sigma:=Sigma) vvs) n a res t,
    wt_sact (Sigma:=Sigma) R vvs a t
    -> eval_sact vvs a n = Some res
    -> eval_sact vvs (simplify_sact_cautious a) n = Some res.
  Proof.
  Admitted.

  Lemma simplify_sact_cautious_interp_sact_ok':
    forall a v vvs (WTVVS: wt_vvs (Sigma := Sigma) R vvs) t
      (WTS: wt_sact (Sigma := Sigma) R vvs a t)
      (VVSSV: vvs_smaller_variables vvs),
    interp_sact (sigma := sigma) REnv r vvs a v
    -> interp_sact (sigma := sigma) REnv r vvs (simplify_sact_cautious a) v.
  Proof.
    intros.
    eapply interp_sact_do_eval_sact in H; eauto.
    unfold do_eval_sact in H.
    eapply eval_sact_interp_sact.
    erewrite simplify_sact_cautious_correct; eauto.
  Qed.

  Lemma simplify_sf_cautious_interp_sact_ok':
    forall sf a v (WTVVS: wt_vvs (Sigma := Sigma) R (vars sf))
      (VVSSV: vvs_smaller_variables (vars sf))
      (EV_INIT: interp_sact (sigma := sigma) REnv r (vars sf) a v),
    interp_sact (sigma := sigma) REnv r (vars (simplify_sf_cautious sf)) a v.
  Proof.
    intros.
    induction EV_INIT; try (econstructor; eauto; fail).
    econstructor.
    - unfold simplify_sf_cautious. setoid_rewrite Maps.PTree.gmap.
      unfold option_map. setoid_rewrite H.
      f_equal.
    - eapply simplify_sact_cautious_interp_sact_ok'; eauto.
      + apply simplify_sf_cautious_wtvvs_ok'. eauto.
      + apply simplify_sf_cautious_wt_sact_ok'. eauto.
      + apply simplify_sf_cautious_vvssv_ok'. eauto.
  Qed.

  Lemma simplify_sf_cautious_interp_cycle_ok:
    forall reg sf,
    wf_sf sf
    -> getenv REnv (interp_cycle r sigma sf) reg
    = getenv REnv (interp_cycle r sigma (simplify_sf_cautious sf)) reg.
  Proof.
  Admitted.
End SimplifyCautious.
