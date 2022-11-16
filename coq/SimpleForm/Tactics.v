Require Import Koika.BitsToLists.
Require Import Koika.Utils.Environments.
Require Import Koika.SimpleForm.Direction.
Require Import Koika.SimpleForm.SimpleForm.
Require Import Koika.SimpleForm.Operations.
Require Import Koika.SimpleForm.Simplifications.Simplifications.
Require Import Koika.KoikaForm.SimpleVal.
Require Import Koika.SimpleForm.Wt.
Require Import Koika.SimpleForm.Interpretation.
Require Import Koika.SimpleForm.Operations.

Ltac update_wfsf :=
  let wfsf := fresh "wfsf" in
  lazymatch goal with
  | RV: getenv ?REnv ?ctx ?rg = ?vl, WTRENV: Wt.wt_renv ?R ?REnv ?ctx,
    WFSF': wf_sf ?R ?ext_Sigma ?sf'
    |-
      getenv ?REnv (interp_cycle ?ctx ?ext_sigma (replace_reg ?sf' ?rg ?vl)) _
      = _
    =>
    assert (wf_sf R ext_Sigma (replace_reg sf' rg vl)) as wfsf by
    (eapply (wf_sf_replace_reg R ext_Sigma ctx WTRENV rg vl sf' RV WFSF'));
    clear WFSF'
  | VS: var_simpl ?R ?ext_Sigma ?ctx ?ext_sigma (vars ?sf) ?var ?newv,
      WTRENV: Wt.wt_renv ?R ?REnv ?ctx,
        WFSF': wf_sf ?R ?ext_Sigma ?sf'
    |-
      getenv ?REnv (interp_cycle ?ctx ?ext_sigma (replace_var ?sf' ?var ?newv)) _
      = _
    =>
    assert (wf_sf R ext_Sigma (replace_var sf' var newv)) as wfsf by
    (eapply (wf_sf_replace_var R ext_Sigma ctx ext_sigma var newv sf' VS WFSF'));
    clear WFSF'
  | FV: get_field (getenv ?REnv ?ctx ?str) ?f = Some ?fv,
    WTRENV: Wt.wt_renv ?R ?REnv ?ctx, WFSF': wf_sf ?R ?ext_Sigma ?sf',
    WTSIGMA:
      forall (ufn : ?ext_fn_t) (vc : val),
      wt_val (arg1Sig (?ext_Sigma ufn)) vc
      -> wt_val (retSig (?ext_Sigma ufn)) (?ext_sigma ufn vc)
    |-
      getenv
        ?REnv (interp_cycle ?ctx ?ext_sigma (replace_field ?str ?sf' ?f ?fv)) _
      = _
    =>
    assert (wf_sf R ext_Sigma (replace_field str sf' f fv)) as wfsf by (
    eapply (
      wf_sf_replace_field
        (wt_sigma := WTSIGMA) R ext_Sigma ctx ext_sigma WTRENV sf' str f fv FV
        WFSF'
    )); clear WFSF'
  | WTRENV: Wt.wt_renv ?R ?REnv ?ctx, WFSF': wf_sf ?R ?ext_Sigma ?sf',
    WT_SIGMA:
      forall (ufn : ?ext_fn_t) (vc : val),
      wt_val (arg1Sig (?ext_Sigma ufn)) vc
      -> wt_val (retSig (?ext_Sigma ufn)) (?ext_sigma ufn vc)
    |- getenv
        ?REnv (interp_cycle ?ctx ?ext_sigma (simplify_sf ?ctx ?ext_sigma ?sf'))
        ?rg
       = _
    =>
    assert (wf_sf R ext_Sigma (simplify_sf ctx ext_sigma sf')) as wfsf by
    (intros; eapply (
       wf_sf_simplify_sf
         (wt_sigma := WT_SIGMA) (REnv := REnv) R ext_Sigma ctx ext_sigma WTRENV
         sf' WFSF'
    ); eauto); clear WFSF'
  | WTRENV: Wt.wt_renv ?R ?REnv ?ctx, WFSF': wf_sf ?R ?ext_Sigma ?sf',
    WT_SIGMA:
      forall (ufn : ?ext_fn_t) (vc : val),
      wt_val (arg1Sig (?ext_Sigma ufn)) vc
      -> wt_val (retSig (?ext_Sigma ufn)) (?ext_sigma ufn vc)
    |- getenv ?REnv
         (interp_cycle ?ctx ?ext_sigma
           (simplify_sf_targeted ?ctx ?ext_sigma ?sf' ?e)
         ) ?rg
       = _
    =>
    assert (
      forall x, wf_sf R ext_Sigma (simplify_sf_targeted ctx ext_sigma sf' x)
    ) as wfsf by (
      intro; apply (
        wf_sf_simplify_sf_targeted
          (wt_sigma := WT_SIGMA) (REnv := REnv) R ext_Sigma ctx ext_sigma WTRENV
          sf' WFSF'
      )
    ); clear WFSF'
  | WTRENV: Wt.wt_renv ?R ?REnv ?ctx, WFSF': wf_sf ?R ?ext_Sigma ?sf'
    |- getenv ?REnv (interp_cycle ?ctx ?ext_sigma (collapse_sf ?sf')) ?rg = _
    =>
    assert (wf_sf R ext_Sigma (collapse_sf sf')) as wfsf by (
      eapply (wf_collapse_sf R ext_Sigma sf' WFSF')
    ); clear WFSF'
  | WTRENV: Wt.wt_renv ?R ?REnv ?ctx, WFSF': wf_sf ?R ?ext_Sigma ?sf'
    |- getenv ?REnv
         (interp_cycle ?ctx ?ext_sigma (prune_irrelevant_aux ?sf' ?rg ?l)) ?rg
       = _
    =>
    let lassoc := fresh "lassoc" in
    assert (list_assoc (final_values sf') rg = Some l)
      as lassoc by (vm_compute list_assoc; reflexivity);
    assert (wf_sf R ext_Sigma (prune_irrelevant_aux sf' rg l)) as wfsf
    by (eapply (wf_sf_prune_irrelevant_aux R ext_Sigma sf' rg l lassoc WFSF'));
    clear WFSF'; clear lassoc
  | |- _ => idtac "update_wf_sf failed"
  end; move wfsf at top.

Ltac exploit_reg H :=
  match goal with
  | WTRENV : Wt.wt_renv ?R ?REnv ?ctx,
    wt_sigma : (
      forall (ufn : ?ext_fn_t) (vc : val),
      wt_val (arg1Sig (?ext_Sigma ufn)) vc
      -> wt_val (retSig (?ext_Sigma ufn)) (?ext_sigma ufn vc))
    |- _ =>
      rewrite
        (replace_reg_interp_cycle_ok (wt_sigma := wt_sigma) _ _ _ _ WTRENV H);
        eauto; update_wfsf
  end.
Ltac exploit_regs :=
  repeat (match goal with
  | H: getenv ?REnv ?ctx ?reg = _,
    WTRENV : Wt.wt_renv ?R ?REnv ?ctx,
    wt_sigma : (
      forall (ufn : ?ext_fn_t) (vc : val),
      wt_val (arg1Sig (?ext_Sigma ufn)) vc
      -> wt_val (retSig (?ext_Sigma ufn)) (?ext_sigma ufn vc))
    |- _ =>
      rewrite
        (replace_reg_interp_cycle_ok (wt_sigma := wt_sigma) _ _ _ _ WTRENV H);
        eauto; update_wfsf; clear H
  end).

Ltac exploit_field H :=
  match goal with
  | WTRENV : Wt.wt_renv ?R ?REnv ?ctx,
    WFSF: wf_sf ?R ?ext_Sigma ?sf,
    wt_sigma : (
      forall (ufn : ?ext_fn_t) (vc : val),
      wt_val (arg1Sig (?ext_Sigma ufn)) vc
      -> wt_val (retSig (?ext_Sigma ufn)) (?ext_sigma ufn vc))
    |- _ =>
      rewrite
        (replace_field_interp_cycle_ok
          (wt_sigma := wt_sigma) _ _ _ _ WTRENV WFSF H);
      eauto; update_wfsf
  end.
Ltac exploit_fields :=
  (* TODO Manage imbricated fields *)
  repeat (match goal with
  | H: get_field (getenv ?REnv ?ctx ?reg) ?name = _,
    WTRENV : Wt.wt_renv ?R ?REnv ?ctx,
    WFSF: wf_sf ?R ?ext_Sigma ?sf,
    wt_sigma : (
      forall (ufn : ?ext_fn_t) (vc : val),
      wt_val (arg1Sig (?ext_Sigma ufn)) vc
      -> wt_val (retSig (?ext_Sigma ufn)) (?ext_sigma ufn vc))
    |- _ =>
      rewrite
        (replace_field_interp_cycle_ok
          (wt_sigma := wt_sigma) _ _ _ _ WTRENV WFSF H);
      eauto; update_wfsf; clear H
  end).

Ltac exploit_hypotheses := exploit_regs; exploit_fields.

Ltac simplify := erewrite simplify_sf_interp_cycle_ok; eauto; update_wfsf.
Ltac prune :=
  erewrite prune_irrelevant_interp_cycle_ok;
    try (unfold prune_irrelevant; vm_compute list_assoc); eauto; update_wfsf.
Ltac collapse := erewrite collapse_interp_cycle_ok; eauto; update_wfsf.


Ltac exploit_var idx newv :=
  match goal with
  | WTRENV : Wt.wt_renv ?R ?REnv ?ctx,
    WFSF: wf_sf ?R ?ext_Sigma ?sf,
    wt_sigma : (
      forall (ufn : ?ext_fn_t) (vc : val),
      wt_val (arg1Sig (?ext_Sigma ufn)) vc
      -> wt_val (retSig (?ext_Sigma ufn)) (?ext_sigma ufn vc))
    |- _ =>
      let vs := fresh "VS" in
      assert (vs: var_simpl R ext_Sigma ctx ext_sigma (vars sf) idx newv);
      [|
        rewrite (replace_var_interp_cycle_ok
                   (wt_sigma:=wt_sigma) _ _ _ _ WTRENV WFSF vs); update_wfsf
        ]
  end.

Goal
  forall
    {reg_t} {ext_fn_t} {reg_t_eq_dec: EqDec reg_t} {REnv: Env reg_t}
    R Sigma REnv r sigma,
    wt_renv R REnv r ->
    (forall (ufn : ext_fn_t) (vc : val), wt_val (arg1Sig (Sigma ufn)) vc -> wt_val (retSig (Sigma ufn)) (sigma ufn vc)) ->
    forall sf rr,
      wf_sf R Sigma sf ->
      getenv REnv (interp_cycle r sigma sf) rr = Bits [].
Proof.
  intros.
  exploit_var 1%positive uconstr:(SConst (Bits [])).
Abort.



(* Ltac auto_destr_next *)

Ltac finish :=
  simplify; eapply getenv_interp;
  lazymatch goal with
  | |- list_assoc _ _ = _ => vm_compute list_assoc; reflexivity
  | |- Maps.PTree.get _ _ = _ => vm_compute Maps.PTree.get; reflexivity
  | |- _ => eauto
  end.

Ltac full_pass := simplify; prune; collapse.
Ltac crusher strength :=
  exploit_hypotheses;
  lazymatch strength with
  | 0 => idtac | 1 => do 1 full_pass | 2 => do 2 full_pass | 3 => do 3 full_pass
  | 4 => do 4 full_pass | 5 => do 5 full_pass | 6 => do 6 full_pass
  | 7 => do 7 full_pass | 8 => do 8 full_pass | 9 => do 9 full_pass
  | 10 => do 10 full_pass | 11 => do 11 full_pass | 12 => do 12 full_pass
  | 13 => do 13 full_pass | 14 => do 14 full_pass | 15 => do 15 full_pass
  | 16 => do 16 full_pass | 17 => do 17 full_pass | 18 => do 18 full_pass
  | 19 => do 19 full_pass | 20 => do 20 full_pass
  | _ => fail "max strength = 20"
  end;
  finish.

Ltac isolate_sf :=
  let name := fresh "sf" in
  lazymatch goal with
  | |- getenv _ (interp_cycle _ _ ?x) _ = _ => set (name := x)
  end.

Ltac isolate_sf_named name :=
  lazymatch goal with
  | |- getenv _ (interp_cycle _ _ ?x) _ = _ => set (name := x)
  end.

Ltac simplify_careful :=
  lazymatch goal with
  | OLD_SF: SimpleForm.simple_form, OLD_WFSF: wf_sf _ _ _
    |- getenv ?REnv (interp_cycle ?ctx ?ext_sigma (_ _)) ?rg = _
      => isolate_sf;
         lazymatch goal with
         | |- getenv ?REnv (interp_cycle ?ctx ?ext_sigma ?new_sf) ?rg = _
           => fold new_sf in OLD_WFSF; unfold OLD_SF in new_sf; clear OLD_SF
         end
  | |- getenv ?REnv (interp_cycle ?ctx ?ext_sigma (_ _)) ?rg = _
      => isolate_sf
  | _ => idtac
  end;
  simplify_careful_t; update_wfsf;
  let new_sf := fresh "sf" in
  isolate_sf_named new_sf;
  lazymatch goal with
  | WTRENV: Wt.wt_renv ?R ?REnv ?ctx,
    OLD_SF: SimpleForm.simple_form, NEW_SF: SimpleForm.simple_form,
    OLD_WFSF:
      forall x : Maps.PTree.t (list Direction.position),
      wf_sf
        ?R ?ext_Sigma
        (SimplifyTargeted.simplify_sf_targeted ?ctx ?ext_sigma _ x),
    WT_SIGMA:
      forall (ufn : ?ext_fn_t) (vc : val),
      wt_val (arg1Sig (?ext_Sigma ufn)) vc
      -> wt_val (retSig (?ext_Sigma ufn)) (?ext_sigma ufn vc)
    |- getenv ?REnv (interp_cycle ?ctx ?ext_sigma _) ?rg = _
    =>
    let wfsf := fresh "wfsf" in
    assert (wf_sf R ext_Sigma new_sf) as wfsf by apply OLD_WFSF; clear OLD_WFSF;
    unfold OLD_SF in NEW_SF; clear OLD_SF; vm_compute in new_sf
  | _ => idtac "ERROR: could not apply simplify_careful"; fail
  end.

Ltac full_pass_c := simplify_careful; collapse; prune.
Ltac crusher_c strength :=
  exploit_hypotheses;
  lazymatch strength with
  | 0 => idtac | 1 => do 1 full_pass_c | 2 => do 2 full_pass_c
  | 3 => do 3 full_pass_c | 4 => do 4 full_pass_c | 5 => do 5 full_pass_c
  | 6 => do 6 full_pass_c | 7 => do 7 full_pass_c | 8 => do 8 full_pass_c
  | 9 => do 9 full_pass_c | 10 => do 10 full_pass_c | 11 => do 11 full_pass_c
  | 12 => do 12 full_pass_c | 13 => do 13 full_pass_c | 14 => do 14 full_pass_c
  | 15 => do 15 full_pass_c | 16 => do 16 full_pass_c | 17 => do 17 full_pass_c
  | 18 => do 18 full_pass_c | 19 => do 19 full_pass_c | 20 => do 20 full_pass_c
  | _ => fail "max strength = 20"
  end;
  finish.
