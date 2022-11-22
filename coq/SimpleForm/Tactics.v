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

Section SAP.
  Variables reg_t ext_fn_t: Type.
Lemma subact_at_pos_refl: forall (x: sact (reg_t:=reg_t) (ext_fn_t:=ext_fn_t)),
    subact_at_position x [] = Some x.
Proof.
  induction x; simpl; intros; reflexivity.
Qed.

Lemma subact_at_pos_rev_refl: forall (x: sact (reg_t:=reg_t) (ext_fn_t:=ext_fn_t)),
    subact_at_position x (List.rev []) = Some x.
Proof.
  intros; simpl; eapply subact_at_pos_refl.
Qed.


Lemma subact_at_pos_trans:
  forall (s: sact (reg_t:=reg_t) (ext_fn_t:=ext_fn_t)) p1 s1 p2 s2,
    subact_at_position s p1 = Some s1 ->
    subact_at_position s1 p2 = Some s2 ->
    subact_at_position s (p1 ++ p2) = Some s2.
Proof.
  induction s; simpl; intros;
    repeat destr_in H; inv H; simpl in *; eauto.
Qed.

Lemma subact_at_pos_unop1:
  forall (s: @sact reg_t ext_fn_t) pos ufn a,
    subact_at_position s (List.rev pos) = Some (SUnop ufn a) ->
    subact_at_position s (List.rev (branch1 :: pos)) = Some a.
Proof.
  intros. simpl. erewrite subact_at_pos_trans. 2: eauto. eauto. simpl.
  apply subact_at_pos_refl.
Qed.

Lemma subact_at_pos_extcall1:
  forall (s: @sact reg_t ext_fn_t) pos ufn a,
    subact_at_position s (List.rev pos) = Some (SExternalCall ufn a) ->
    subact_at_position s (List.rev (branch1 :: pos)) = Some a.
Proof.
  intros. simpl. erewrite subact_at_pos_trans. 2: eauto. eauto. simpl.
  apply subact_at_pos_refl.
Qed.

Lemma subact_at_pos_binop1:
  forall (s: @sact reg_t ext_fn_t) pos ufn a1 a2,
    subact_at_position s (List.rev pos) = Some (SBinop ufn a1 a2) ->
    subact_at_position s (List.rev (branch1 :: pos)) = Some a1.
Proof.
  intros. simpl. erewrite subact_at_pos_trans. 2: eauto. eauto. simpl.
  apply subact_at_pos_refl.
Qed.

Lemma subact_at_pos_binop2:
  forall (s: @sact reg_t ext_fn_t) pos ufn a1 a2,
    subact_at_position s (List.rev pos) = Some (SBinop ufn a1 a2) ->
    subact_at_position s (List.rev (branch2 :: pos)) = Some a2.
Proof.
  intros. simpl. erewrite subact_at_pos_trans. 2: eauto. eauto. simpl.
  apply subact_at_pos_refl.
Qed.


Lemma subact_at_pos_if1:
  forall (s: @sact reg_t ext_fn_t) pos a1 a2 a3,
    subact_at_position s (List.rev pos) = Some (SIf a1 a2 a3) ->
    subact_at_position s (List.rev (branch1 :: pos)) = Some a1.
Proof.
  intros. simpl. erewrite subact_at_pos_trans. 2: eauto. eauto. simpl.
  apply subact_at_pos_refl.
Qed.

Lemma subact_at_pos_if2:
  forall (s: @sact reg_t ext_fn_t) pos a1 a2 a3,
    subact_at_position s (List.rev pos) = Some (SIf a1 a2 a3) ->
    subact_at_position s (List.rev (branch2 :: pos)) = Some a2.
Proof.
  intros. simpl. erewrite subact_at_pos_trans. 2: eauto. eauto. simpl.
  apply subact_at_pos_refl.
Qed.

Lemma subact_at_pos_if3:
  forall (s: @sact reg_t ext_fn_t) pos a1 a2 a3,
    subact_at_position s (List.rev pos) = Some (SIf a1 a2 a3) ->
    subact_at_position s (List.rev (branch3 :: pos)) = Some a3.
Proof.
  intros. simpl. erewrite subact_at_pos_trans. 2: eauto. eauto. simpl.
  apply subact_at_pos_refl.
Qed.


Ltac search_subterm needle haystack pos orig_haystack Ppos :=
  match haystack with
  | ?x => match needle with
            x => eval vm_compute in
              (existT _ [pos] (Forall_cons pos Ppos (@Forall_nil _ (fun v => subact_at_position orig_haystack (List.rev v) = Some needle))))
          end
  | SVar ?x => eval vm_compute in
      (existT _ _ (@Forall_nil _ (fun v => subact_at_position orig_haystack (List.rev v) = Some needle)))
  | SConst ?x =>  eval vm_compute in
      (existT _ _ (@Forall_nil _ (fun v => subact_at_position orig_haystack (List.rev v) = Some needle)))
  | SReg ?x =>  eval vm_compute in
      (existT _ _ (@Forall_nil _ (fun v => subact_at_position orig_haystack (List.rev v) = Some needle)))
  | SUnop ?ufn ?a =>
      search_subterm needle a (Direction.branch1 :: pos) orig_haystack (subact_at_pos_unop1 _ _ _ _ Ppos)
  | SExternalCall ?ufn ?a =>
      search_subterm needle a (Direction.branch1 :: pos) orig_haystack (subact_at_pos_extcall1 _ _ _ _ Ppos)
  | SBinop ?ufn ?a ?b =>
      let p1 := search_subterm needle a (Direction.branch1 :: pos) orig_haystack (subact_at_pos_binop1 _ _ _ _ _ Ppos) in
      let p2 := search_subterm needle b (Direction.branch2 :: pos) orig_haystack (subact_at_pos_binop2 _ _ _ _ _ Ppos) in
      eval vm_compute in (existT _ _ (proj2 (@Forall_app _ _ _ _) (conj (projT2 p1) (projT2 p2))))
  | SIf ?a ?b ?c =>
      let p1 := search_subterm needle a (Direction.branch1 :: pos) orig_haystack (subact_at_pos_if1 _ _ _ _ _ Ppos) in
      let p2 := search_subterm needle b (Direction.branch2 :: pos) orig_haystack (subact_at_pos_if2 _ _ _ _ _ Ppos) in
      let p3 := search_subterm needle c (Direction.branch3 :: pos) orig_haystack (subact_at_pos_if3 _ _ _ _ _ Ppos) in
      eval vm_compute in
        (existT _ _ (proj2 (@Forall_app _ _ _ _) (conj (projT2 p1) (proj2 (@Forall_app _ _ _ _) (conj (projT2 p2) (projT2 p3))))))
  end.


Ltac ssearch needle haystack :=
  let hs := eval vm_compute in haystack in
  let res :=
    search_subterm needle hs ([]: list Direction.direction) hs (subact_at_pos_rev_refl hs) in
  res.

Definition ptree_forall {A: Type} (P: positive -> A -> Prop) (t: Maps.PTree.t A) :=
  forall k v, Maps.PTree.get k t = Some v -> P k v.

Lemma ptree_set_prop {A: Type} (t: Maps.PTree.t A) P
  (FA: ptree_forall P t)
  k v
  (PKV: P k v):
  ptree_forall P (Maps.PTree.set k v t).
Proof.
  unfold ptree_forall in *.
  intros.
  rewrite Maps.PTree.gsspec in H. destr_in H; eauto. inv H. auto.
Qed.

Lemma ptree_forall_empty {A: Type} P:
  ptree_forall P (Maps.PTree.empty A).
Proof.
  unfold ptree_forall. intros. rewrite Maps.PTree.gempty in H. congruence.
Qed.

Ltac ssearch_in_elems needle l :=
  lazymatch l with
  | [] => eval vm_compute in (existT (A:=list (positive * list position))
                                (fun v =>
                                   Forall2 (fun '(k, (t, a)) '(k1, ps) =>
                                              k = k1 /\
                                              Forall (fun p => subact_at_position a (rev p) = Some needle) ps
                                     ) l v
                                ) _ (Forall2_nil _)
                             )
  | (?kk, (?tt, ?x))::?r =>
      let ps := ssearch needle x in
      let pss := ssearch_in_elems needle r in
      eval vm_compute in
        (existT (A:=list (positive * list position))
           _ _ (@Forall2_cons _ _ (fun '(k, (t, a)) '(k1,Ps) =>
                                     k = k1 /\
                                       Forall (fun p => subact_at_position a (rev p) = Some needle) Ps
                                     ) (kk,(tt,x)) (kk,(projT1 ps)) _ _ (conj eq_refl (projT2 ps)) (projT2 pss)))
  end.

Fixpoint ptree_of_elements {A: Type} (l: list (positive * A)) :=
  match l with
    [] => Maps.PTree.empty A
  | (k,v)::r => Maps.PTree.set k v (ptree_of_elements r)
  end.


Lemma forall2_elems:
  forall {A B: Type}
         (l1: list (positive * A))
         (l2: list (positive * B)) P,
    Forall2 (fun '(k, a) '(k1,v) => k = k1 /\ P a v) l1 l2 ->
    NoDup (List.map fst l1) ->
    let res := ptree_of_elements l2 in
    forall k ps a,
      In (k, a) l1 ->
      Maps.PTree.get k res = Some ps ->
      P a ps.
Proof.
  induction 1; simpl; intros; eauto. easy.
  destr_in H3.
  rewrite Maps.PTree.gsspec in H3.
  destruct x. destruct H. subst. simpl in H1. inv H1.
  destr_in H3.
  - inv H3. destruct H2 as [C|C]. inv C. auto.
    elim H6. change p with (fst (p, a)). apply in_map. auto.
  - destruct H2. inv H. congruence.
    eauto.
Qed.


Lemma forall2_elems':
  forall {A B: Type}
         (l1: Maps.PTree.t A)
         (l2: list (positive * B)) P,
    Forall2 (fun '(k, a) '(k1,v) => k = k1 /\ P a v) (Maps.PTree.elements l1) l2 ->
    let res := ptree_of_elements l2 in
    forall k ps a,
      Maps.PTree.get k l1 = Some a ->
      Maps.PTree.get k res = Some ps ->
      P a ps.
Proof.
  intros.
  eapply forall2_elems; eauto.
  apply Maps.PTree.elements_keys_norepet.
  apply Maps.PTree.elements_correct; auto.
Qed.


Lemma forall2_elems'':
  forall {A B C: Type}
         (l1: Maps.PTree.t (C * A))
         (l2: list (positive * B)) P,
    Forall2 (fun '(k, (t, a)) '(k1,v) => k = k1 /\ P a v) (Maps.PTree.elements l1) l2 ->
    let res := ptree_of_elements l2 in
    forall k ps t a,
      Maps.PTree.get k l1 = Some (t, a) ->
      Maps.PTree.get k res = Some ps ->
      P a ps.
Proof.
  intros.
  eapply forall2_elems' with (P0:=fun '(t,a) v => P a v) in H0. eauto.
  2: eauto.
  eapply Forall2_impl. eauto. simpl. intros. destruct x. destruct p0,y. destruct H4. subst. split; auto.
Qed.


Ltac ssearch_in_vars needle t :=
  let vars := eval vm_compute in (Maps.PTree.elements t) in
    let res := ssearch_in_elems needle vars in
    let res := eval vm_compute in res in
      let x := eval vm_compute in (projT1 res) in
        let P := eval vm_compute in (projT2 res) in
          let H := fresh in
          assert (H: Forall2 (fun '(k, (ty,a)) '(k1,ps) =>
                             k = k1 /\
                               (fun '(_,a) ps => Forall (fun p => subact_at_position a (rev p) = Some needle) ps) (ty,a) ps
                    )
                       (Maps.PTree.elements t) x) by (exact P);
          let H2 := fresh in
          assert (H2 := forall2_elems'' _ _ _ H); clear H.


Goal False.
    set (k0:= true: bool).
    Import PrimUntyped.

    set (vars :=
           Maps.PTree.set 1%positive (bits_t 1, SConst (reg_t:=reg_t) (ext_fn_t:=ext_fn_t) (Bits [true]))
             (Maps.PTree.set 2%positive (bits_t 1, SUnop (UBits1 UNot) (SConst (reg_t:=reg_t) (ext_fn_t:=ext_fn_t) (Bits [true])))
                (Maps.PTree.set 3%positive (bits_t 1, SBinop (UBits2 UAnd)
           (SConst (reg_t:=reg_t) (ext_fn_t:=ext_fn_t) (Bits [true]))
           (SConst (reg_t:=reg_t) (ext_fn_t:=ext_fn_t) (Bits [true]))
                   ) (Maps.PTree.empty _))
             )
        ).

    Set Ltac Backtrace.

    ssearch_in_vars (SConst (reg_t:=reg_t) (ext_fn_t:=ext_fn_t) (Bits [true]))
              vars.

    let l := ssearch (SConst (reg_t:=reg_t) (ext_fn_t:=ext_fn_t) (Bits [true]))
               (SConst (Bits [true]) : (@sact reg_t ext_fn_t)) in idtac l.

    let l :=
      ssearch_in_elems (SConst (reg_t:=reg_t) (ext_fn_t:=ext_fn_t) (Bits [true]))
                       ([(1%positive, (bits_t 1, SConst (Bits [true])))] : list (prod positive (prod type (@sact reg_t ext_fn_t))))
    in idtac l.


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

End SAP.
