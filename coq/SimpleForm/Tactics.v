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

(* returns val, [exempted] *)
Ltac simplify_tac r sigma H pos :=
  lazymatch H with
  | @SIf ?rt ?eft ?c ?t ?f =>
    let c_ret := simplify_tac r sigma c (branch1::pos) in
    let new_c := (eval vm_compute in (fst c_ret)) in
    let ec := (eval vm_compute in (snd c_ret)) in
    let t_ret := simplify_tac r sigma t (branch2::pos) in
    let new_t := (eval vm_compute in (fst t_ret)) in
    let et := (eval vm_compute in (snd t_ret)) in
    let f_ret := simplify_tac r sigma t (branch3::pos) in
    let new_f := (eval vm_compute in (fst f_ret)) in
    let ef := (eval vm_compute in (snd f_ret)) in
    match eval vm_compute in (eval_sact_no_vars r sigma new_c) with
    | Some (Bits [true]) => eval vm_compute in (new_t, ec ++ et)
    | Some (Bits [false]) => eval vm_compute in (new_f, ec ++ ef)
    | _ =>
      eval vm_compute in (
        SIf (reg_t := rt) (ext_fn_t := eft) new_c new_t new_f,
        pos :: ec ++ et ++ ef
      )
    end
  | @SUnop ?rt ?eft ?fn ?arg =>
    let a_ret := simplify_tac r sigma arg (branch1::pos) in
    let new_a := (eval vm_compute in (fst a_ret)) in
    let ea := (eval vm_compute in (snd a_ret)) in
    let res := (
      eval vm_compute in (eval_sact_no_vars r sigma (SUnop fn new_a))
    ) in
    match res with
    | Some ?x => (eval vm_compute in (SConst (reg_t := rt) (ext_fn_t := eft) x, ea))
    | _ => eval vm_compute in (SUnop (reg_t := rt) (ext_fn_t := eft) fn new_a, pos :: ea)
    end
  | @SBinop ?rt ?eft ?fn ?arg1 ?arg2 =>
    let a1_ret := simplify_tac r sigma arg1 (branch1::pos) in
    let new_a1 := (eval vm_compute in (fst a1_ret)) in
    let ea1 := (eval vm_compute in (snd a1_ret)) in
    let a2_ret := simplify_tac r sigma arg2 (branch2::pos) in
    let new_a2 := (eval vm_compute in (fst a2_ret)) in
    let ea2 := (eval vm_compute in (snd a2_ret)) in
    let res := (
      eval vm_compute in (eval_sact_no_vars r sigma (SBinop (reg_t := rt) (ext_fn_t := eft) fn new_a1 new_a2))
    ) in
    lazymatch res with
    | Some ?x =>
      eval vm_compute in
        (SConst (reg_t := rt) (ext_fn_t := eft) x, ea1 ++ ea2)
    | _ =>
      eval vm_compute in
        (SBinop (reg_t := rt) (ext_fn_t := eft) fn new_a1 new_a2,
         pos :: ea1 ++ ea2)
    end
  | @SExternalCall ?rt ?eft ?fn ?arg =>
    let a_ret := simplify_tac r sigma arg (branch1::pos) in
    let new_a := (eval vm_compute in (fst a_ret)) in
    let ea := (eval vm_compute in (snd a_ret)) in
    let res := (
      eval vm_compute in (eval_sact_no_vars r sigma (SExternalCall fn new_a))
    ) in
    match res with
    | Some ?x =>
        eval vm_compute in
          (SConst (reg_t := rt) (ext_fn_t := eft) x, ea)
    | _ => eval vm_compute in (SUnop new_a, pos :: ea)
    end
  | @SReg ?rt ?eft ?idx =>
    eval vm_compute in (H, (@nil Direction.position))
  | @SVar ?rt ?eft ?v =>
    eval vm_compute in (H, (@nil Direction.position))
  | @SConst ?rt ?eft ?c =>
    eval vm_compute in (H, (@nil Direction.position))
  | _ => idtac "nop2 " H
  end.

Ltac apply_option r sigma i :=
  lazymatch i with
  | (_, (_, ?x)) =>
    let stac := simplify_tac r sigma x (@nil Direction.direction) in
    eval vm_compute in (snd stac)
  | _ => idtac "nope" i
  end.

Ltac apply_to_list r sigma l :=
  lazymatch l with
  | [] => eval vm_compute in (@nil (list Direction.position))
  | ?h :: ?t =>
    let simpl_h := apply_option r sigma h in
    let simpl_t := apply_to_list r sigma t in
    eval vm_compute in (simpl_h::simpl_t)
  end.

(* Maps.PTree.elements map *)
Ltac apply_to_map r sigma m :=
  let m_l := eval vm_compute in (Maps.PTree.elements m) in
  apply_to_list r sigma m_l.

Ltac simplify_targeted protected :=
  erewrite simplify_sf_targeted_interp_cycle_ok with (e := protected); eauto.

Ltac simplify_top :=
  lazymatch goal with
  | |- getenv ?REnv (interp_cycle ?ctx ?ext_sigma ?sf) _ = _ =>
    let map := constr:(vars sf) in
    let protected := apply_to_map ctx ext_sigma map in
    let sz := (eval vm_compute in (List.length protected)) in
    simplify_targeted protected
  end.

Ltac update_wfsf :=
  let wfsf := fresh "wfsf" in
  let lassoc := fresh "lassoc" in
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
    |- getenv ?REnv
         (interp_cycle ?ctx ?ext_sigma (simplify_sf ?ctx ?ext_sigma ?sf')) ?rg
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
    assert (forall x, wf_sf R ext_Sigma (simplify_sf_targeted ctx ext_sigma sf' x))
      as wfsf by
    (intro; apply (
      wf_sf_simplify_sf_targeted
        (wt_sigma := WT_SIGMA) (REnv := REnv)
        R ext_Sigma ctx ext_sigma WTRENV
        sf' WFSF'
    )); clear WFSF'
  | WTRENV: Wt.wt_renv ?R ?REnv ?ctx, WFSF': wf_sf ?R ?ext_Sigma ?sf',
    WT_SIGMA:
      forall (ufn : ?ext_fn_t) (vc : val),
      wt_val (arg1Sig (?ext_Sigma ufn)) vc
      -> wt_val (retSig (?ext_Sigma ufn)) (?ext_sigma ufn vc)
    |- getenv ?REnv
         (interp_cycle ?ctx ?ext_sigma
           (simplify_sf_cautious ?ctx ?ext_sigma ?sf')) ?rg
       = _
    =>
    assert (wf_sf R ext_Sigma (simplify_sf_cautious ctx ext_sigma sf')) as wfsf by
    (eapply (
        wf_sf_simplify_sf_cautious
          (wt_sigma := WT_SIGMA) (REnv := REnv) R ext_Sigma ctx ext_sigma WTRENV
          sf' WFSF'
    )); clear WFSF'
  | WTRENV: Wt.wt_renv ?R ?REnv ?ctx, WFSF': wf_sf ?R ?ext_Sigma ?sf'
    |- getenv ?REnv
         (interp_cycle ?ctx ?ext_sigma
           (prune_irrelevant_aux (collapse_sf ?sf') ?rg ?l)
         ) ?rg = _
    =>
    assert (list_assoc (final_values (collapse_sf sf')) rg = Some l)
      as lassoc by (vm_compute list_assoc; reflexivity);
    assert (wf_sf R ext_Sigma (prune_irrelevant_aux (collapse_sf sf') rg l))
    as wfsf by (eapply (
      wf_sf_prune_irrelevant_aux
        R ext_Sigma (collapse_sf sf') rg l lassoc
        (wf_collapse_sf R ext_Sigma sf' WFSF')
    )); clear WFSF'; clear lassoc
  | WTRENV: Wt.wt_renv ?R ?REnv ?ctx, WFSF': wf_sf ?R ?ext_Sigma ?sf'
    |- getenv ?REnv
         (interp_cycle ?ctx ?ext_sigma (prune_irrelevant_aux ?sf' ?rg ?l)) ?rg
       = _
    =>
    (* TODO also keep a single live version of lassoc *)
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
Ltac simplify_careful := simplify_top; update_wfsf.
Ltac simplify_cautious :=
  erewrite simplify_sf_cautious_interp_cycle_ok; eauto; update_wfsf.
Ltac prune :=
  erewrite prune_irrelevant_interp_cycle_ok;
    try (unfold prune_irrelevant; vm_compute list_assoc); eauto; update_wfsf.
Ltac collapse :=
  erewrite collapse_prune_interp_cycle_ok;
  lazymatch goal with
  | |- _ =>
    try (unfold prune_irrelevant; vm_compute list_assoc; eauto); try eauto
  end; update_wfsf.

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

Ltac get_var x sf :=
  let name := fresh "var_val" in
  set (name := (Maps.PTree.get (Pos.of_nat x) (vars sf)));
  vm_compute in name.
