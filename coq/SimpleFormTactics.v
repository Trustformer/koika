Require Import Koika.BitsToLists Koika.Environments Koika.SimpleForm
  Koika.SimpleFormInterpretation Koika.SimpleVal Koika.Wt.

(* TODO unclear name, rename *)
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
    set (wfsf := wf_sf_replace_reg R ext_Sigma ctx WTRENV rg vl sf' RV WFSF');
    unfold WFSF' in wfsf; clear WFSF'
  | FV: get_field (getenv ?REnv ?ctx ?str) ?f = Some ?fv,
    WTRENV: Wt.wt_renv ?R ?REnv ?ctx, WFSF': wf_sf ?R ?ext_Sigma ?sf'
    |-
     getenv
       ?REnv (interp_cycle ?ctx ?ext_sigma (replace_field ?sf' ?str ?f ?fv)) _
     = _
    =>
    set (
      wfsf := wf_sf_replace_field R ext_Sigma ctx WTRENV sf' str f fv FV WFSF');
    unfold WFSF' in wfsf; clear WFSF'
  | WTRENV: Wt.wt_renv ?R ?REnv ?ctx, WFSF': wf_sf ?R ?ext_Sigma ?sf',
    WT_SIGMA:
      forall (ufn : ?ext_fn_t) (vc : val),
      wt_val (arg1Sig (?ext_Sigma ufn)) vc
      -> wt_val (retSig (?ext_Sigma ufn)) (?ext_sigma ufn vc)
    |- getenv ?REnv
         (interp_cycle ?ctx ?ext_sigma (simplify_sf ?ctx ?ext_sigma ?sf')) ?rg
       = _
    =>
    set (
      wfsf :=
        wf_sf_simplify_sf
          (wt_sigma := WT_SIGMA) (REnv := REnv) R ext_Sigma ctx ext_sigma WTRENV
          sf' WFSF'
    ); unfold WFSF' in wfsf; clear WFSF'
  | WTRENV: Wt.wt_renv ?R ?REnv ?ctx, WFSF': wf_sf ?R ?ext_Sigma ?sf'
    |- getenv ?REnv
         (interp_cycle ?ctx ?ext_sigma
           (prune_irrelevant_aux (collapse_sf ?sf') ?rg ?l)
         ) ?rg = _
    =>
    assert (list_assoc (final_values (collapse_sf sf')) rg = Some l)
      as lassoc by (vm_compute list_assoc; reflexivity);
    set (
      wfsf :=
        wf_sf_prune_irrelevant_aux
          R ext_Sigma (collapse_sf sf') rg l lassoc
          (wf_collapse_sf R ext_Sigma sf' WFSF')
    );
    unfold WFSF' in wfsf; clear WFSF'
  | WTRENV: Wt.wt_renv ?R ?REnv ?ctx, WFSF': wf_sf ?R ?ext_Sigma ?sf'
    |- getenv ?REnv
         (interp_cycle ?ctx ?ext_sigma (prune_irrelevant_aux ?sf' ?rg ?l)) ?rg
       = _
    =>
    (* TODO also keep a single live version of lassoc *)
    assert (list_assoc (final_values sf') rg = Some l)
      as lassoc by (vm_compute list_assoc; reflexivity);
    set (wfsf := wf_sf_prune_irrelevant_aux R ext_Sigma sf' rg l lassoc WFSF');
    unfold WFSF' in wfsf; clear WFSF'
    (* ; clear lassoc *)
  | |- _ => idtac
  end.

Ltac replace_reg :=
  erewrite replace_reg_interp_cycle_ok; eauto; update_wfsf.
(* TODO replace all regs *)
(* TODO is_concrete test *)
Ltac replace_field :=
  erewrite replace_field_interp_cycle_ok; eauto; update_wfsf.
Ltac simplify :=
  erewrite simplify_sf_interp_cycle_ok; eauto; update_wfsf.
Ltac prune :=
  erewrite prune_irrelevant_interp_cycle_ok;
    try (unfold prune_irrelevant; vm_compute list_assoc); eauto; update_wfsf.
Ltac collapse :=
  erewrite collapse_prune_interp_cycle_ok;
  lazymatch goal with
  | |- _ =>
    try (unfold prune_irrelevant; vm_compute list_assoc; eauto); try eauto
  end; update_wfsf.

Ltac finish :=
  simplify; eapply getenv_interp;
  lazymatch goal with
  | |- list_assoc _ _ = _ => vm_compute list_assoc; reflexivity
  | |- Maps.PTree.get _ _ = _ => vm_compute Maps.PTree.get; reflexivity
  | |- _ => eauto
  end.

Ltac full_pass := simplify; prune; collapse.
Ltac crusher strength :=
  replace_reg;
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
  set (name := Maps.PTree.get (Pos.of_nat x) (vars sf));
  vm_compute in name.

(* Ltac show_binding v := *)
(*   let name := fresh "binding" in *)
(*   set (name := ). *)
