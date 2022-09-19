Require Import Koika.SimpleForm.SimpleFormInterpretation.
Require Import Koika.SimpleForm.SimpleFormOperations.
Require Import Koika.BitsToLists.
Require Import Koika.KoikaForm.SimpleVal.
Require Import Koika.KoikaForm.Types.
Require Import Koika.SimpleForm.SimpleForm.
Require Import Koika.Utils.EqDec.
Require Import Koika.Utils.Maps.
Require Import Koika.Utils.Environments.

Section Prune.
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

  Definition prune_irrelevant_aux (sf: @simple_form reg_t ext_fn_t) reg v := {|
    final_values := [(reg, v)];
    vars := filter_ptree (vars sf) (PTree.empty _) (useful_vars_for_var sf v)
  |}.

  Definition prune_irrelevant (sf: simple_form) reg :=
    match list_assoc (final_values sf) reg with
    | Some v => Some (prune_irrelevant_aux sf reg v)
    | None => None
    end.

  Lemma wf_sf_prune_irrelevant_aux:
    forall sf reg v,
    list_assoc (final_values sf) reg = Some v
    -> wf_sf sf
    -> wf_sf (prune_irrelevant_aux sf reg v).
  Proof.
    intros.
    eapply wf_sf_filter_ptree. 5: reflexivity.
    eapply nodup_reachable_vars_aux; eauto. apply H0. constructor.
    intros; eapply reachable_vars_aux_ok. eauto. eauto. 2: reflexivity.
    apply H0. simpl; easy. lia. eauto. eauto. eauto. auto.
    simpl. intros. destr_in H1; inv H1. rewrite H. split; auto.
  Qed.

  Lemma sf_eqf_prune_irrelevant_aux:
    forall sf reg v,
    list_assoc (final_values sf) reg = Some v
    -> wf_sf sf
    -> sf_eq_restricted
         R Sigma r sigma [reg] sf (prune_irrelevant_aux sf reg v).
  Proof.
    intros. eapply sf_eqr_filter. 6: reflexivity.
    apply nodup_reachable_vars_aux; eauto. apply H0. constructor.
    intros; eapply reachable_vars_aux_ok; eauto. apply H0. reflexivity.
    easy. auto.
    simpl. intros ? [|[]]. subst.
    destr.
    simpl. intros. repeat destr_in H1; inv H1. split; auto.
  Qed.

  Lemma prune_irrelevant_interp_cycle_ok:
    forall
      reg sf sf' (WF: wf_sf sf) (PRUNE: prune_irrelevant sf reg = Some sf'),
    getenv REnv (interp_cycle r sigma sf) reg
    = getenv REnv (interp_cycle r sigma sf') reg.
  Proof.
    intros.
    unfold prune_irrelevant in PRUNE. destr_in PRUNE; inv PRUNE.
    eapply sf_eqr_interp_cycle_ok; eauto.
    - eapply wf_sf_prune_irrelevant_aux; eauto.
    - eapply sf_eqf_prune_irrelevant_aux; eauto.
    - simpl; auto.
  Qed.
End Prune.
