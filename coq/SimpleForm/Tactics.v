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
  | SO: subact_ok ?R ?ext_Sigma ?ctx ?ext_sigma (vars ?sf) ?positions ?needle ?rep,
      WTRENV: Wt.wt_renv ?R ?REnv ?ctx,
        WFSF': wf_sf ?R ?ext_Sigma ?sf'
    |-
      getenv ?REnv (interp_cycle ?ctx ?ext_sigma (replace_subact ?sf' ?positions ?rep)) _
      = _
    =>
    assert (wf_sf R ext_Sigma (replace_subact sf' positions rep)) as wfsf by
    (eapply (wf_sf_replace_subact' R ext_Sigma ctx ext_sigma sf' positions needle rep SO WFSF'));
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
           (simplify_sf_targeted ?sf' ?e)
         ) ?rg
       = _
    =>
    assert (
      forall x, wf_sf R ext_Sigma (simplify_sf_targeted sf' x)
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
  end; try move wfsf at top.

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
  lazymatch goal with
  | WTRENV : Wt.wt_renv ?R ?REnv ?ctx,
    WFSF: wf_sf ?R ?ext_Sigma ?sf,
    wt_sigma : (
      forall (ufn : ?ext_fn_t) (vc : val),
      wt_val (arg1Sig (?ext_Sigma ufn)) vc
      -> wt_val (retSig (?ext_Sigma ufn)) (?ext_sigma ufn vc))
    |- _ =>
    let vs := fresh "VS" in
    assert (vs: var_simpl R ext_Sigma ctx ext_sigma (vars sf) idx newv);
    [| rewrite (
         replace_var_interp_cycle_ok (wt_sigma:=wt_sigma) _ _ _ _ WTRENV WFSF vs
       );
       update_wfsf ]
  end.

Ltac exploit_subact :=
  match goal with
  | WTRENV : Wt.wt_renv ?R ?REnv ?ctx,
    WFSF: wf_sf ?R ?ext_Sigma ?sf,
    SO: subact_ok
        ?R ?ext_Sigma ?ctx ?ext_sigma (vars ?sf) ?positions ?needle ?rep,
    wt_sigma : (
      forall (ufn : ?ext_fn_t) (vc : val),
      wt_val (arg1Sig (?ext_Sigma ufn)) vc
      -> wt_val (retSig (?ext_Sigma ufn)) (?ext_sigma ufn vc))
    |- _ =>
      rewrite (
        replace_subact_interp_cycle_ok'
          (wt_sigma:=wt_sigma) _ _ _ _ WTRENV _ WFSF _ _ _ SO
      ); update_wfsf
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
        (SimplifyTargeted.simplify_sf_targeted _ x),
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

Ltac search_subterm needle haystack pos orig_haystack Ppos :=
  match haystack with
  | ?x => match needle with
            x => let res := constr:(ssprop_one pos needle orig_haystack Ppos) in
                 eval vm_compute in res
          end
  | SVar ?x => let res := constr:(ssprop_nil needle orig_haystack pos) in
                 eval vm_compute in res
  | SConst ?x => let res := constr:(ssprop_nil needle orig_haystack pos) in
                 eval vm_compute in res
  | SReg ?x => let res := constr:(ssprop_nil needle orig_haystack pos) in
                 eval vm_compute in res
  | SUnop ?ufn ?a =>
      let p := search_subterm needle a (Direction.branch1 :: pos) orig_haystack (subact_at_pos_unop1 _ _ _ _ Ppos) in
      eval vm_compute in (existT _ _ (sprop_unop needle pos _ _ (projT2 p)))
  | SExternalCall ?ufn ?a =>
      let p := search_subterm needle a (Direction.branch1 :: pos) orig_haystack (subact_at_pos_extcall1 _ _ _ _ Ppos) in
      eval vm_compute in (existT _ _ (sprop_unop needle pos _ _ (projT2 p)))
  | SBinop ?ufn ?a ?b =>
      let p1 := search_subterm needle a (Direction.branch1 :: pos) orig_haystack (subact_at_pos_binop1 _ _ _ _ _ Ppos) in
      let p2 := search_subterm needle b (Direction.branch2 :: pos) orig_haystack (subact_at_pos_binop2 _ _ _ _ _ Ppos) in
      eval vm_compute in
        (existT _ _ (sprop_binop needle pos _ _ _ (projT2 p1) (projT2 p2)))
  | SIf ?a ?b ?c =>
      let p1 := search_subterm needle a (Direction.branch1 :: pos) orig_haystack (subact_at_pos_if1 _ _ _ _ _ Ppos) in
      let p2 := search_subterm needle b (Direction.branch2 :: pos) orig_haystack (subact_at_pos_if2 _ _ _ _ _ Ppos) in
      let p3 := search_subterm needle c (Direction.branch3 :: pos) orig_haystack (subact_at_pos_if3 _ _ _ _ _ Ppos) in
      eval vm_compute in
        (existT _ _ (sprop_if needle pos _ _ _ _ (projT2 p1) (projT2 p2) (projT2 p3)))
  end.


Ltac ssearch needle haystack :=
  let hs := eval vm_compute in haystack in
  let res :=
    search_subterm needle hs ([]: list Direction.direction) hs (subact_at_pos_rev_refl hs) in
  res.


Goal forall (reg_t ext_fn_t: Type) (uext:ext_fn_t), False.
  intros.
  let l := ssearch (SConst (reg_t:=reg_t) (ext_fn_t:=ext_fn_t) (Bits [true]))
             (SConst (Bits [true]) : (@sact reg_t ext_fn_t)) in
  idtac l;
  let t := (type of l) in idtac t.

  let l := ssearch (SConst (reg_t:=reg_t) (ext_fn_t:=ext_fn_t) (Bits [true]))
             (SVar 12%positive : ((@sact reg_t ext_fn_t))) in
  idtac l;
  let t := (type of l) in idtac t.

  let l := ssearch (SConst (reg_t:=reg_t) (ext_fn_t:=ext_fn_t) (Bits [true]))
             (SUnop (PrimUntyped.UBits1 PrimUntyped.UNot) (SVar 12%positive : ((@sact reg_t ext_fn_t)))) in
  idtac l;
  let t := (type of l) in idtac t.


 (*  Set Ltac Backtrace. *)

 (* let p := search_subterm (SConst (reg_t:=reg_t) (ext_fn_t:=ext_fn_t) (Bits [true])) (SVar 12%positive : ((@sact reg_t ext_fn_t))) (Direction.branch1 :: []) (SUnop (PrimUntyped.UBits1 PrimUntyped.UNot) (SVar 12%positive : ((@sact reg_t ext_fn_t)))) (@subact_at_pos_unop1 reg_t ext_fn_t _ _ (PrimUntyped.UBits1 PrimUntyped.UNot) (SVar 12%positive : ((@sact reg_t ext_fn_t))) (subact_at_pos_rev_refl _)) in idtac p. *)

  let l := ssearch (SConst (reg_t:=reg_t) (ext_fn_t:=ext_fn_t) (Bits [true]))
             (SUnop (PrimUntyped.UBits1 PrimUntyped.UNot) (SVar 12%positive : ((@sact reg_t ext_fn_t)))) in
  idtac l;
  let t := (type of l) in idtac t.

  let l := ssearch (SConst (reg_t:=reg_t) (ext_fn_t:=ext_fn_t) (Bits [true]))
             (SBinop (PrimUntyped.UBits2 PrimUntyped.UAnd)
                (SConst (reg_t:=reg_t) (ext_fn_t:=ext_fn_t) (Bits [true]))
                (SVar 12%positive : ((@sact reg_t ext_fn_t)))) in
  let t := (type of l) in idtac t.


  let l := ssearch (SConst (reg_t:=reg_t) (ext_fn_t:=ext_fn_t) (Bits [true]))
             (SExternalCall uext (SIf
                       (SUnop (PrimUntyped.UBits1 PrimUntyped.UNot) (SBinop (PrimUntyped.UBits2 PrimUntyped.UAnd)
                   (SConst (reg_t:=reg_t) (ext_fn_t:=ext_fn_t) (Bits [true]))
                   (SVar 12%positive : ((@sact reg_t ext_fn_t)))))
                (SConst (Bits [true]))
                (SConst (Bits [false]))))
               in
  let t := (type of l) in idtac t.


Abort.

Ltac ssearch_in_elems needle l :=
  lazymatch l with
  | [] => eval vm_compute in (ssearch_in_elemsT_nil needle)
  | (?kk, (?tt, ?x))::?r =>
      let ps := ssearch needle x in
      let pss := ssearch_in_elems needle r in
      eval vm_compute in
        (ssearch_in_elemsT_cons needle r kk tt _ _ pss ps)
  end.


Goal forall (reg_t ext_fn_t: Type) (uext:ext_fn_t), False.
  intros.
    Import PrimUntyped.

    set (vars :=
           Maps.PTree.set 1%positive (bits_t 1, SConst (reg_t:=reg_t) (ext_fn_t:=ext_fn_t) (Bits [true]))
             (Maps.PTree.set 2%positive (bits_t 1, SUnop (UBits1 UNot) (SConst (reg_t:=reg_t) (ext_fn_t:=ext_fn_t) (Bits [true])))
                (Maps.PTree.set 3%positive (bits_t 1, SBinop (UBits2 UAnd)
           (SConst (reg_t:=reg_t) (ext_fn_t:=ext_fn_t) (Bits [true]))
           (SConst (reg_t:=reg_t) (ext_fn_t:=ext_fn_t) (Bits [true]))
                   ) (Maps.PTree.set 4%positive (bits_t 1,
(SExternalCall uext (SIf
                       (SUnop (UBits1 UNot) (SBinop (PrimUntyped.UBits2 PrimUntyped.UAnd)
                   (SConst (reg_t:=reg_t) (ext_fn_t:=ext_fn_t) (Bits [true]))
                   (SVar 12%positive : ((@sact reg_t ext_fn_t)))))
                (SConst (Bits [true]))
                (SConst (Bits [false]))))
                        ) (Maps.PTree.empty _)))
             )
        ).

    Set Ltac Backtrace.

    let vars := eval vm_compute in (Maps.PTree.elements vars) in
      let res := ssearch_in_elems (SConst (reg_t:=reg_t) (ext_fn_t:=ext_fn_t) (Bits [true]))
                   vars in
      let t := type of res in idtac t.
Abort.


Ltac ssearch_in_vars needle t H :=
  let vars := eval vm_compute in (Maps.PTree.elements t) in
    let res := ssearch_in_elems needle vars in
    let res := eval vm_compute in res in
      let x := eval vm_compute in (projT1 res) in
        let P := eval vm_compute in (projT2 res) in
          let positions := fresh "positions" in
          set (positions := x);
          assert
            (H :
              Forall2
                (fun '(k, (ty, a)) '(k1, ps) =>
                   k = k1 /\ (fun '(_, a) ps => ReplaceSubact.search_subterm_propP needle a [] ps) (ty, a) ps)
                (Maps.PTree.elements t) positions) by exact P.


Ltac get_subact_ok needle vars rep t :=
  match goal with
  | WTRENV : Wt.wt_renv ?R ?REnv ?ctx,
      WFSF: wf_sf ?R ?ext_Sigma ?sf,
        wt_sigma : (
                     forall (ufn : ?ext_fn_t) (vc : val),
                       wt_val (arg1Sig (?ext_Sigma ufn)) vc
                       -> wt_val (retSig (?ext_Sigma ufn)) (?ext_sigma ufn vc))
    |- _ =>
      let H := fresh in
      ssearch_in_vars needle vars H;
      generalize (ReplaceSubact.subact_ok_ltac (REnv:=REnv) R ext_Sigma ctx ext_sigma _ _ _ H rep t); clear H
  end.


Ltac ssearch_in_var needle t k rep ty :=
  match goal with
  | WTRENV : Wt.wt_renv ?R ?REnv ?ctx,
      WFSF: wf_sf ?R ?ext_Sigma ?sf,
        wt_sigma : (
                     forall (ufn : ?ext_fn_t) (vc : val),
                       wt_val (arg1Sig (?ext_Sigma ufn)) vc
                       -> wt_val (retSig (?ext_Sigma ufn)) (?ext_sigma ufn vc))
    |- _ =>
      let res := eval vm_compute in (Maps.PTree.get k t) in
        match res with
          Some (?itt, ?ix) =>
            let res := ssearch needle ix in
            let x := eval vm_compute in (projT1 res) in
              let P := eval vm_compute in (projT2 res) in
                let positions := fresh "positions" in
                set (positions := x);
                set (HP := P);
                (* let H := fresh in *)
                (* assert *)
                (*   (H : ReplaceSubact.search_subterm_propP needle x [] positions) by exact P; *)
                generalize (fun pf =>
                              ReplaceSubact.subact_ok_ltac_1var
                                (REnv:=REnv) R ext_Sigma ctx ext_sigma
                                t _ k itt _ positions pf HP rep ty); clear HP
        end
  end.


(* match goal with *)
(*   | WTRENV:Wt.wt_renv ?R ?REnv ?ctx, *)
(*     WFSF:wf_sf ?R ?ext_Sigma ?sf, *)
(*     wt_sigma:forall (ufn : ?ext_fn_t) (vc : val), *)
(*              wt_val (arg1Sig (?ext_Sigma ufn)) vc -> *)
(*              wt_val (retSig (?ext_Sigma ufn)) (?ext_sigma ufn vc) *)
(*     |- _ => *)
(*       let res := eval vm_compute in (Maps.PTree.get 1788%positive (vars sf1)) in *)
(*         match res with *)
(*         | Some (?itt, ?ix) => *)
(*             let res := ssearch (@SBinop RV32I.reg_t RV32I.ext_fn_t (UEq false) *)
(*                              (SConst (Bits [x0])) *)
(*                              (SConst (Bits [x0])) *)
(*                            ) ix in *)
(*             let x := eval vm_compute in (projT1 res) in *)
(*             let P := eval vm_compute in (projT2 res) in *)
(*             let positions := fresh "positions" in *)
(*             set (positions := x); *)
(*             set (HP := P); *)
(*                generalize *)
(*                 (fun pf => *)
(*                  ReplaceSubact.subact_ok_ltac_1var R ext_Sigma ctx ext_sigma *)
(*                    (vars sf1) _ 1788%positive itt _ positions pf HP) *)
(*         end *)
(* end. *)

Goal forall (reg_t ext_fn_t: Type) (uext: ext_fn_t), False.
  intros.
    set (k0:= true: bool).
    Import PrimUntyped.

        set (vars :=
           Maps.PTree.set 1%positive (bits_t 1, SConst (reg_t:=reg_t) (ext_fn_t:=ext_fn_t) (Bits [true]))
             (Maps.PTree.set 2%positive (bits_t 1, SUnop (UBits1 UNot) (SConst (reg_t:=reg_t) (ext_fn_t:=ext_fn_t) (Bits [true])))
                (Maps.PTree.set 3%positive (bits_t 1, SBinop (UBits2 UAnd)
           (SConst (reg_t:=reg_t) (ext_fn_t:=ext_fn_t) (Bits [true]))
           (SConst (reg_t:=reg_t) (ext_fn_t:=ext_fn_t) (Bits [true]))
                   ) (Maps.PTree.set 4%positive (bits_t 1,
(SExternalCall uext (SIf
                (SBinop (PrimUntyped.UBits2 PrimUntyped.UAnd)
                   (SConst (reg_t:=reg_t) (ext_fn_t:=ext_fn_t) (Bits [true]))
                   (SVar 12%positive : ((@sact reg_t ext_fn_t))))
                (SConst (Bits [true]))
                (SConst (Bits [false]))))
                        ) (Maps.PTree.empty _)))
             )
        ).

    Set Ltac Backtrace.

    (* let vars := eval vm_compute in (Maps.PTree.elements vars) in *)
    (*   let res := ssearch_in_elems (SConst (reg_t:=reg_t) (ext_fn_t:=ext_fn_t) (Bits [true])) *)
    (*           vars in idtac res. *)


    ssearch_in_vars (SConst (reg_t:=reg_t) (ext_fn_t:=ext_fn_t) (Bits [true]))
              vars A.

    (* ssearch_in_var  (SConst (reg_t:=reg_t) (ext_fn_t:=ext_fn_t) (Bits [true])) *)
    (*   vars 2%positive *)
    (*   (SConst (reg_t:=reg_t) (ext_fn_t:=ext_fn_t) (Bits [true])) (bits_t 1). *)

    let l := ssearch (SConst (reg_t:=reg_t) (ext_fn_t:=ext_fn_t) (Bits [true]))
               (SConst (Bits [true]) : ((@sact reg_t ext_fn_t))) in idtac l.

    (* let l := *)
    (*   ssearch_in_elems (SConst (reg_t:=reg_t) (ext_fn_t:=ext_fn_t) (Bits [true])) *)
    (*                    ([(1%positive, (bits_t 1, SConst (Bits [true])))] : list (prod positive (prod type ((@sact reg_t ext_fn_t))))) *)
    (* in idtac l. *)


    set (hs := (SConst (reg_t:=reg_t) (ext_fn_t:=ext_fn_t) (Bits [true]))).

    let l := ssearch
      (SConst (reg_t:=reg_t) (ext_fn_t:=ext_fn_t) (Bits [true]))
        hs in idtac l.

    set (hs2 := (SUnop (UBits1 UNot) (SConst (reg_t:=reg_t) (ext_fn_t:=ext_fn_t) (Bits [true])))).
    let l := ssearch
      (SConst (reg_t:=reg_t) (ext_fn_t:=ext_fn_t) (Bits [true]))
        hs2 in idtac l.

    set (hs3 := (SBinop (UBits2 UAnd)
           (SConst (reg_t:=reg_t) (ext_fn_t:=ext_fn_t) (Bits [true]))
           (SConst (reg_t:=reg_t) (ext_fn_t:=ext_fn_t) (Bits [true]))
        )).
    let l := ssearch
      (SConst (reg_t:=reg_t) (ext_fn_t:=ext_fn_t) (Bits [true])) hs3
    in idtac l.

    let x := ssearch
               (SConst (reg_t:=reg_t) (ext_fn_t:=ext_fn_t) (Bits [k0]))
                 (SVar (reg_t:=reg_t) (ext_fn_t:=ext_fn_t) (12%positive))
    in
    idtac x.
Abort.


