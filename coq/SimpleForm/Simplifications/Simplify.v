Require Import Koika.SimpleForm.SimpleFormInterpretation.
Require Import Koika.SimpleForm.SimpleFormOperations.
Require Import Koika.BitsToLists.
Require Import Koika.KoikaForm.SimpleVal.
Require Import Koika.KoikaForm.Types.
Require Import Koika.SimpleForm.SimpleForm.
Require Import Koika.Utils.EqDec.
Require Import Koika.Utils.Maps.
Require Import Koika.Utils.Environments.

Section Simplify.
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

  Definition simplify_sf (sf: simple_form) := {|
    final_values := final_values sf;
    vars := simplify_vars r sigma (vars sf)
  |}.

  Lemma sf_eq_simplify_sf sf:
    wf_sf sf -> sf_eq R Sigma r sigma sf (simplify_sf sf).
  Proof.
    unfold simplify_sf. intros. inv H. constructor; auto.
    intros. simpl.
    split; intros.
    eapply simplify_vars_interp_sact_ok'; eauto.
    inversion H1. subst.
    unfold simplify_vars in H3. rewrite PTree.gmap in H3.
    unfold option_map in H3. repeat destr_in H3; inv H3.
    eapply simplify_vars_interp_sact_ok; eauto.
    econstructor. eauto.
    simpl. intros.
    eapply simplify_vars_wt_sact_ok'; eauto.
    eapply simplify_vars_wt_sact_ok; eauto.
  Qed.

  Lemma wf_sf_simplify_sf: forall sf, wf_sf sf -> wf_sf (simplify_sf sf).
  Proof.
    destruct 1; constructor.
    eapply simplify_vars_wtvvs_ok'; eauto.
    eapply simplify_vars_vvssv_ok'; eauto.
    simpl. intros.
    eapply wf_sf_final in H.
    eapply simplify_vars_wt_sact_ok'. auto.
  Qed.

  Lemma simplify_sf_interp_cycle_ok:
    forall reg sf,
    wf_sf sf ->
    getenv REnv (interp_cycle r sigma sf) reg
    = getenv REnv (interp_cycle r sigma (simplify_sf sf)) reg.
  Proof.
    intros.
    eapply sf_eq_interp_cycle_ok; eauto.
    - apply wf_sf_simplify_sf; auto.
    - apply sf_eq_simplify_sf. auto.
  Qed.
End Simplify.
