Require Import Koika.SimpleForm.Interpretation.
Require Import Koika.SimpleForm.Operations.
Require Import Koika.BitsToLists.
Require Import Koika.KoikaForm.SimpleVal.
Require Import Koika.KoikaForm.Types.
Require Import Koika.SimpleForm.Direction.
Require Import Koika.SimpleForm.SimpleForm.
Require Import Koika.Utils.EqDec.
Require Import Koika.Utils.Maps.
Require Import Koika.Utils.Environments.

Section ReplaceSubact.
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
  Local Definition wt_sact := @wt_sact _ _ R Sigma.
  Local Definition interp_sact := @interp_sact _ _ _ r sigma.
  Local Definition wf_sf := wf_sf R Sigma.
  Hypothesis WTRENV: Wt.wt_renv R REnv r.
  Context {
    wt_sigma:
    forall ufn vc, wt_val (arg1Sig (Sigma ufn)) vc
    -> wt_val (retSig (Sigma ufn)) (sigma ufn vc)
  }.

  Fixpoint subact_at_position
    (s: sact) (p: position) : option sact :=
    match p with
      [] => Some s
    | branch1::p =>
        match s with
        | SUnop ufn a => subact_at_position a p
        | SBinop ufn a b => subact_at_position a p
        | SExternalCall ufn a => subact_at_position a p
        | SIf a b c => subact_at_position a p
        | _ => None
        end
    | branch2::p =>
        match s with
        | SBinop ufn a b => subact_at_position b p
        | SIf a b c => subact_at_position b p
        | _ => None
        end
    | branch3::p =>
        match s with
        | SIf a b c => subact_at_position c p
        | _ => None
        end
    end.

  Fixpoint replace_at_position
    (s: sact) (p: position) (v: sact) : sact :=
    match p with
      [] => v
    | branch1::p =>
        match s with
        | SUnop ufn a =>
            let a := replace_at_position a p v in  (SUnop ufn a)
        | SBinop ufn a b =>
            let a := replace_at_position a p v in  (SBinop ufn a b)
        | SExternalCall ufn a =>
            let a := replace_at_position a p v in  (SExternalCall ufn a)
        | SIf a b c =>
            let a := replace_at_position a p v in  (SIf a b c)
        | _ => s
        end
    | branch2::p =>
        match s with
        | SBinop ufn a b =>
            let b := replace_at_position b p v in  (SBinop ufn a b)
        | SIf a b c =>
            let b := replace_at_position b p v in  (SIf a b c)
        | _ => s
        end
    | branch3::p =>
        match s with
        | SIf a b c =>
            let c := replace_at_position c p v in  (SIf a b c)
        | _ => s
        end
    end.

  Definition replace_at_positions s ps v :=
    fold_left (fun acc pos => replace_at_position acc pos v) ps s.

  Definition replace_subact_in_vars (vars: PTree.t (type * sact)) (positions: PTree.t (list position))
    (v: sact)  :=
    PTree.map
      (fun k '(t, ua) =>
         let poss := match PTree.get k positions with Some l => l | _ => [] end in
         (t, replace_at_positions ua poss v))
      vars.

    Definition replace_subact (sf: simple_form) (positions: PTree.t (list position))
    (v: sact) : simple_form :=
    {|
      final_values := final_values sf;
      vars := replace_subact_in_vars (vars sf) positions v
    |}.

    Lemma wt_unop_determ:
      forall u t t1,
        wt_unop u t t1 ->
        forall t2,
        wt_unop u t t2 ->
        t1 = t2.
    Proof.
      intros.
      inv H; inv H0; auto. congruence. congruence.
    Qed.

    Lemma wt_binop_determ:
      forall u t t' t1,
        wt_binop u t t' t1 ->
        forall t2,
        wt_binop u t t' t2 ->
        t1 = t2.
    Proof.
      intros.
      inv H; inv H0; auto.
    Qed.

    Lemma wt_sact_determ:
      forall vvs s t1,
        wt_sact vvs s t1 ->
        forall t2,
        wt_sact vvs s t2 ->
        t1 = t2.
    Proof.
      induction 1; simpl; intros; eauto.
      - inv H0. congruence.
      - inv H0. eapply wt_val_determ; eauto.
      - inv H2. eauto.
      - inv H1; eauto. apply IHwt_sact in H4. subst.
        eapply wt_unop_determ; eauto.
      - inv H2; eauto.
        apply IHwt_sact1 in H6.
        apply IHwt_sact2 in H8.
        subst. eapply wt_binop_determ; eauto.
      - inv H0. auto.
      - inv H. auto.
    Qed.

    Lemma wt_sact_replace_at_position:
      forall vvs s p subact
             (SAP: subact_at_position s p = Some subact)
             t (WT: wt_sact vvs s t) rep tn,
        wt_sact vvs subact tn ->
        wt_sact vvs rep tn ->
        wt_sact vvs (replace_at_position s p rep) t.
    Proof.
      induction s; simpl; intros; eauto.
      -  repeat destr_in SAP; inv SAP.
         exploit wt_sact_determ. apply WT. apply H. intros ->. auto.
      - repeat destr_in SAP; inv SAP.
        exploit wt_sact_determ. apply WT. apply H. intros ->. auto.
      - repeat destr_in SAP; inv SAP.
        + exploit wt_sact_determ. apply WT. apply H. intros ->. auto.
        + inv WT. econstructor; eauto. eapply IHs1; eauto.
        + inv WT. econstructor; eauto. eapply IHs2; eauto.
        + inv WT. econstructor; eauto. eapply IHs3; eauto.
      - repeat destr_in SAP; inv SAP.
        + exploit wt_sact_determ. apply WT. apply H. intros ->. auto.
        + inv WT. econstructor; eauto. eapply IHs; eauto.
      - repeat destr_in SAP; inv SAP.
        + exploit wt_sact_determ. apply WT. apply H. intros ->. auto.
        + inv WT. econstructor; eauto. eapply IHs1; eauto.
        + inv WT. econstructor; eauto. eapply IHs2; eauto.
      - repeat destr_in SAP; inv SAP.
        + exploit wt_sact_determ. apply WT. apply H. intros ->. auto.
        + inv WT. econstructor; eauto. eapply IHs; eauto.
      - repeat destr_in SAP; inv SAP.
        exploit wt_sact_determ. apply WT. apply H. intros ->. auto.
    Qed.

    Inductive prefix {A:Type}: list A -> list A -> Prop :=
    | prefix_nil_l: forall l, prefix [] l
    | prefix_cons: forall d l1 l2,
        prefix l1 l2 ->
        prefix (d::l1) (d::l2).

    Inductive no_prefix : list position -> Prop :=
    | no_prefix_nil: no_prefix []
    | no_prefix_cons:
      forall p l,
        (forall p', In p' l -> ~ prefix p p' /\ ~ prefix p' p) ->
        no_prefix l ->
        no_prefix (p::l).


    Lemma no_prefix_subact_at_position_same:
      forall p s v p',
        ~ prefix p p' ->
        ~ prefix p' p ->
        subact_at_position (replace_at_position s p v) p' = subact_at_position s p'.
    Proof.
      induction p; simpl; intros; eauto.
      elim H. constructor.
      destruct p'. elim H0. constructor.
      destruct s; simpl.
      - repeat destr; simpl; auto.
      - repeat destr; simpl; auto.
      - repeat destr; simpl; auto.
        eapply IHp.
        intro P; apply H; constructor; auto.
        intro P; apply H0; constructor; auto.
        eapply IHp.
        intro P; apply H; constructor; auto.
        intro P; apply H0; constructor; auto.
        eapply IHp.
        intro P; apply H; constructor; auto.
        intro P; apply H0; constructor; auto.
      - repeat destr; simpl; auto.
        eapply IHp.
        intro P; apply H; constructor; auto.
        intro P; apply H0; constructor; auto.
      - repeat destr; simpl; auto.
        eapply IHp.
        intro P; apply H; constructor; auto.
        intro P; apply H0; constructor; auto.
        eapply IHp.
        intro P; apply H; constructor; auto.
        intro P; apply H0; constructor; auto.
      - repeat destr; simpl; auto.
        eapply IHp.
        intro P; apply H; constructor; auto.
        intro P; apply H0; constructor; auto.
      - repeat destr; simpl; auto.
    Qed.

    Lemma wt_sact_replace_at_positions:
      forall vvs ps (NP: no_prefix ps) s tn subact
             (POSOK: forall
                 p (IN: In p ps),
                 subact_at_position s p = Some subact)
             (WWT: wt_sact vvs subact tn)
             t
             (WT: wt_sact vvs s t) rep
             (WTrep: wt_sact vvs rep tn),
        wt_sact vvs (replace_at_positions s ps rep) t.
    Proof.
      induction 1; simpl; intros; eauto.
      eapply IHNP.
      - intros.
        erewrite no_prefix_subact_at_position_same. eauto.
        eapply H; eauto.
        eapply H; eauto.
      - eauto.
      - eapply wt_sact_replace_at_position; eauto.
      - eauto.
    Qed.

    Lemma wt_sact_replace_at_positions_in_vars:
      forall vvs positions
             (NP: forall k ps, positions ! k = Some ps -> no_prefix ps)
             subact
             (POSOK: forall k t s ps,
                 positions ! k = Some ps ->
                 vvs ! k = Some (t, s) ->
                 forall p (IN: In p ps),
                   subact_at_position s p = Some subact)
             tn (WWT: wt_sact vvs subact tn)
             rep (WTrep: wt_sact vvs rep tn)
             s t
             (WT: wt_sact vvs s t),
        wt_sact (replace_subact_in_vars vvs positions rep) s t.
    Proof.
      intros vvs positions NP subact POSOK tn WWT rep WTrep.
      induction 1; simpl; intros; eauto.
      - econstructor.
        setoid_rewrite PTree.gmap. setoid_rewrite H. simpl. eauto.
      - econstructor; eauto.
      - econstructor; eauto.
      - econstructor; eauto.
      - econstructor; eauto.
      - econstructor; eauto.
      - econstructor; eauto.
    Qed.

    Lemma interp_sact_replace_at_position:
      forall vvs,
        wt_vvs (Sigma:=Sigma) R vvs ->
        vvs_smaller_variables vvs ->
        forall a0 p subact tn rep,
          subact_at_position a0 p = Some subact ->
          wt_sact vvs subact tn ->
          wt_sact vvs rep tn ->
          (forall ov : val, interp_sact vvs subact ov <-> interp_sact vvs rep ov) ->
      forall t v,
        wt_sact vvs a0 t ->
        interp_sact vvs a0 v ->
        interp_sact vvs (replace_at_position a0 p rep) v.
    Proof.
      induction a0; simpl; intros; eauto.
      - repeat destr_in H1; inv H1. apply H4; auto.
      - repeat destr_in H1; inv H1. apply H4; auto.
      - inv H5. repeat destr_in H1; inv H1.
        + apply H4; auto.
        + inv H6; econstructor; eauto. eapply IHa0_1; eauto.
        + inv H6. econstructor; eauto. destr. eapply IHa0_2; eauto.
        + inv H6; econstructor; eauto. destr. eapply IHa0_3; eauto.
      - inv H5. repeat destr_in H1; inv H1.
        + apply H4; auto.
        + inv H6; econstructor; eauto. eapply IHa0; eauto.
      - inv H5. repeat destr_in H1; inv H1.
        + apply H4; auto.
        + inv H6; econstructor; eauto. eapply IHa0_1; eauto.
        + inv H6. econstructor; eauto. eapply IHa0_2; eauto.
      - inv H5. repeat destr_in H1; inv H1.
        + apply H4; auto.
        + inv H6; econstructor; eauto. eapply IHa0; eauto.
      - inv H5. repeat destr_in H1; inv H1. apply H4; auto.
    Qed.


    Lemma interp_sact_replace_at_position':
      forall vvs,
        wt_vvs (Sigma:=Sigma) R vvs ->
        vvs_smaller_variables vvs ->
        forall a0 p subact tn rep,
          subact_at_position a0 p = Some subact ->
          wt_sact vvs subact tn ->
          wt_sact vvs rep tn ->
          (forall ov : val, interp_sact vvs subact ov <-> interp_sact vvs rep ov) ->
      forall t v,
        wt_sact vvs a0 t ->
        interp_sact vvs (replace_at_position a0 p rep) v ->
        interp_sact vvs a0 v.
    Proof.
      induction a0; simpl; intros; eauto.
      - repeat destr_in H1; inv H1. apply H4; auto.
      - repeat destr_in H1; inv H1. apply H4; auto.
      - inv H5. repeat destr_in H1; inv H1.
        + apply H4; auto.
        + inv H6; econstructor; eauto. eapply IHa0_1; eauto.
        + inv H6. econstructor; eauto. destr. eapply IHa0_2; eauto.
        + inv H6; econstructor; eauto. destr. eapply IHa0_3; eauto.
      - inv H5. repeat destr_in H1; inv H1.
        + apply H4; auto.
        + inv H6; econstructor; eauto. eapply IHa0; eauto.
      - inv H5. repeat destr_in H1; inv H1.
        + apply H4; auto.
        + inv H6; econstructor; eauto. eapply IHa0_1; eauto.
        + inv H6. econstructor; eauto. eapply IHa0_2; eauto.
      - inv H5. repeat destr_in H1; inv H1.
        + apply H4; auto.
        + inv H6; econstructor; eauto. eapply IHa0; eauto.
      - inv H5. repeat destr_in H1; inv H1. apply H4; auto.
    Qed.


    Lemma interp_sact_replace_at_position_iff:
      forall vvs,
        wt_vvs (Sigma:=Sigma) R vvs ->
        vvs_smaller_variables vvs ->
        forall a0 p subact tn rep,
          subact_at_position a0 p = Some subact ->
          wt_sact vvs subact tn ->
          wt_sact vvs rep tn ->
          (forall ov : val, interp_sact vvs subact ov <-> interp_sact vvs rep ov) ->
      forall t v,
        wt_sact vvs a0 t ->
        interp_sact vvs (replace_at_position a0 p rep) v <->
        interp_sact vvs a0 v.
    Proof.
      split; intros.
      eapply interp_sact_replace_at_position'; eauto.
      eapply interp_sact_replace_at_position; eauto.
    Qed.


    Lemma interp_sact_replace_at_positions:
      forall vvs,
        wt_vvs (Sigma:=Sigma) R vvs ->
        vvs_smaller_variables vvs ->
        forall subact tn rep,
          wt_sact vvs subact tn ->
          wt_sact vvs rep tn ->
          (forall ov : val, interp_sact vvs subact ov <-> interp_sact vvs rep ov) ->
      forall ps a0 t v,
        wt_sact vvs a0 t ->
        (forall p : position, In p ps -> subact_at_position a0 p = Some subact) ->
        no_prefix ps ->
        interp_sact vvs a0 v <->
          interp_sact vvs (replace_at_positions a0 ps rep) v.
    Proof.
      induction ps; simpl; intros; eauto. tauto.
      rewrite <- IHps.
      rewrite interp_sact_replace_at_position_iff; eauto. tauto.
      eapply wt_sact_replace_at_position; eauto.
      - inv H6.
        intros.
        rewrite no_prefix_subact_at_position_same. eauto. apply H9. auto.
        apply H9; auto.
      - inv H6; auto.
    Qed.

    Lemma wt_vvs_replace_subact_in_vars:
      forall vvs positions v
             (WTVVS: wt_vvs (Sigma := Sigma) R vvs)
             tt subact
             (OLDTYPE: wt_sact  vvs subact tt)
             (NEWTYPE: wt_sact  vvs v tt)
             (SUBACT: forall ps p k t a,
                 vvs ! k = Some (t, a) ->
                 positions ! k = Some ps ->
                 In p ps ->
                 subact_at_position a p = Some subact
             )
             (NP: forall ps k, positions ! k = Some ps -> no_prefix ps)
      ,
        wt_vvs (Sigma:=Sigma) R (replace_subact_in_vars vvs positions v).
    Proof.
      intros.
      unfold wt_vvs. intros.
      setoid_rewrite Maps.PTree.gmap in H. unfold option_map in H.
      destr_in H. 2: inv H. destr_in H. inv H.
      destr.
      intros; eapply wt_sact_replace_at_positions; eauto.
      eapply wt_sact_replace_at_positions_in_vars; eauto.
      eapply wt_sact_replace_at_positions_in_vars; eauto.
      eapply WTVVS; eauto.
      eapply wt_sact_replace_at_positions_in_vars; eauto.
      simpl.
      eapply wt_sact_replace_at_positions_in_vars; eauto.
      eapply WTVVS; eauto.
    Qed.

    Lemma var_in_sact_replace_at_position:
      forall a p b v,
        var_in_sact (replace_at_position a p b) v ->
        var_in_sact a v \/ var_in_sact b v.
    Proof.
      induction a; simpl; intros; eauto.
      - repeat destr_in H; eauto.
      - repeat destr_in H; eauto.
      - repeat destr_in H; eauto.
        inv H.
        edestruct IHa1; eauto. left; eapply var_in_if_cond; eauto.
        left; eapply var_in_if_true; eauto.
        left; eapply var_in_if_false; eauto.
        inv H.
        left; eapply var_in_if_cond; eauto.
        edestruct IHa2; eauto. left; eapply var_in_if_true; eauto.
        left; eapply var_in_if_false; eauto.
        inv H.
        left; eapply var_in_if_cond; eauto.
        left; eapply var_in_if_true; eauto.
        edestruct IHa3; eauto. left; eapply var_in_if_false; eauto.
      - repeat destr_in H; eauto.
        inv H.
        edestruct IHa; eauto. left; eapply var_in_sact_unop; eauto.
      - repeat destr_in H; eauto.
        inv H.
        edestruct IHa1; eauto. left; eapply var_in_sact_binop_1; eauto.
        left; eapply var_in_sact_binop_2; eauto.
        inv H.
        left; eapply var_in_sact_binop_1; eauto.
        edestruct IHa2; eauto. left; eapply var_in_sact_binop_2; eauto.
      - repeat destr_in H; eauto.
        inv H.
        edestruct IHa; eauto. left; eapply var_in_sact_external; eauto.
      - repeat destr_in H; eauto.
    Qed.

    Lemma var_in_sact_replace_at_positions:
      forall ps a b v,
        var_in_sact (replace_at_positions a ps b) v ->
        var_in_sact a v \/ var_in_sact b v.
    Proof.
      induction ps; simpl; intros; eauto.
      eapply IHps in H. destruct H; auto.
      edestruct var_in_sact_replace_at_position; eauto.
    Qed.

    Lemma vsv_replace_subact_in_vars:
      forall vvs positions v
             (VSV: vvs_smaller_variables vvs)
             tt subact
             (OLDTYPE: wt_sact  vvs subact tt)
             (NEWTYPE: wt_sact  vvs v tt)
             (SUBACT: forall ps p k t a,
                 vvs ! k = Some (t, a) ->
                 positions ! k = Some ps ->
                 In p ps ->
                 subact_at_position a p = Some subact
             )
             (SMALLER: forall var, var_in_sact v var -> var_in_sact subact var)
      ,
        vvs_smaller_variables (replace_subact_in_vars vvs positions v).
    Proof.
      intros.
      red. intros.
      setoid_rewrite Maps.PTree.gmap in H. unfold option_map in H.
      destr_in H. 2: inv H. inv H. destr_in H2. inv H2.
      edestruct var_in_sact_replace_at_positions. eauto. eapply VSV; eauto.
      eapply SMALLER in H.
      destr_in H0.
      2:{
        simpl in *. eauto.
      }
      destruct l. simpl in H0; eauto.
      exploit SUBACT; eauto. left; reflexivity. intro EQ.

      Lemma subact_at_position_var_in_sact:
        forall s p s' v,
          subact_at_position s p = Some s' ->
          var_in_sact s' v ->
          var_in_sact s v.
      Proof.
        induction s; simpl; intros; eauto; repeat destr_in H; inv H; eauto.
        eapply var_in_if_cond; eauto.
        eapply var_in_if_true; eauto.
        eapply var_in_if_false; eauto.
        eapply var_in_sact_unop; eauto.
        eapply var_in_sact_binop_1; eauto.
        eapply var_in_sact_binop_2; eauto.
        eapply var_in_sact_external; eauto.
      Qed.
      eapply subact_at_position_var_in_sact in EQ. eapply VSV in EQ. 2: eauto. apply EQ. auto.
    Qed.

    Lemma interp_sact_var_iff:
      forall vvs var vv t s,
        vvs ! var = Some (t,s) ->
        interp_sact vvs (SVar var) vv <-> interp_sact vvs s vv.
    Proof.
      split.
      intro A; inv A. rewrite H in H1; inv H1. apply H2.
      intros; econstructor; eauto.
    Qed.

  Lemma interp_sact_replace_subact:
    forall vvs positions
           (NP: forall k ps, positions ! k = Some ps -> no_prefix ps)
           subact
           (POSOK: forall k t s ps,
               positions ! k = Some ps ->
               vvs ! k = Some (t, s) ->
               forall p (IN: In p ps),
                 subact_at_position s p = Some subact)
           tn (WWT: wt_sact vvs subact tn)
           rep (WTrep: wt_sact vvs rep tn)
           (WTvvs: wt_vvs (Sigma:=Sigma) R  vvs)
           (VSV: vvs_smaller_variables vvs)
           (SAME1: forall ov,
               interp_sact vvs subact ov <-> interp_sact vvs rep ov)
           (SMALLER: forall var, var_in_sact rep var -> var_in_sact subact var)
           a n (LT: forall v, reachable_var vvs a v -> (v < n)%positive)
           t
           (WT: wt_sact vvs a t),
    forall vv,
      interp_sact vvs a vv <->
        interp_sact (replace_subact_in_vars vvs positions rep) a vv.
  Proof.
    intros vvs positions NP subact POSOK tn WWT rep WTrep WTvvs VSV SAME1 SMALLER a n.
    change n with (projT1 (existT (fun _ => sact) n a)).
    change a with (projT2 (existT (fun _ => sact) n a)) at 1 3 4 5.
    generalize (existT (fun _ => sact) n a).
    clear n a. intro s. pattern s.
    eapply well_founded_induction.
    apply wf_order_sact. clear s.
    intros x IH BELOW t WTs vv.
    assert (
      IH2:
        forall a0,
        size_sact a0 < size_sact (projT2 x)
        -> (forall v0, reachable_var vvs a0 v0 -> (v0 < projT1 x)%positive)
        ->
          forall t
                 (WT: wt_sact vvs a0 t),
            forall vv,
      interp_sact  vvs a0 vv <->
        interp_sact (replace_subact_in_vars vvs positions rep) a0 vv
    ). {
      intros. eapply (IH (existT _ (projT1 x) a0)).
      red. destruct x. apply Relation_Operators.right_lex. simpl in H.  auto.
      simpl. auto. simpl. auto. simpl. eauto.
    }
    destruct x; simpl in *.
    destruct s; simpl in *.
    - inv WTs.
      
      rewrite interp_sact_var_iff. 2: eauto.
      rewrite interp_sact_var_iff. 2: setoid_rewrite PTree.gmap; setoid_rewrite H0; simpl; eauto.
      destr. 2: simpl. destruct l.
      simpl.

      {
        eapply (IH (existT _ var s)). red. apply Relation_Operators.left_lex. apply BELOW. constructor.
        simpl. eapply reachable_var_aux_below_get; eauto.
        simpl. eapply WTvvs; eauto.
      }
      2:{
        eapply (IH (existT _ var s)). red. apply Relation_Operators.left_lex. apply BELOW. constructor.
        simpl. eapply reachable_var_aux_below_get; eauto.
        simpl. eapply WTvvs; eauto.
      }
      erewrite <- interp_sact_replace_at_positions; eauto.
      eapply (IH (existT _ var s)); simpl; eauto.
      red. apply Relation_Operators.left_lex. apply BELOW. econstructor.
      apply (reachable_var_aux_below_get _ VSV _ _ _ H0). eapply WTvvs; eauto.
      eapply wt_vvs_replace_subact_in_vars. 4: intros; eapply POSOK; eauto. all: eauto.
      eapply vsv_replace_subact_in_vars. 4: intros; eapply POSOK; eauto. all: eauto.
      2: eapply wt_sact_replace_at_positions_in_vars; eauto.
      intros; eapply wt_sact_replace_at_positions_in_vars. 2: eapply POSOK; eauto.
      all: eauto.

      2: intros; eapply wt_sact_replace_at_positions_in_vars. 3: eapply POSOK; eauto. all: eauto. 2: eapply WTvvs; eauto.

      intros.
      exploit POSOK; eauto. left; reflexivity. intro SAP.
      generalize (fun v => subact_at_position_var_in_sact _ _ _ v SAP). intro SAPVIS.

      erewrite <- (IH (existT _ var subact)); simpl; eauto.
      2: red. 2: eapply Relation_Operators.left_lex. 2: apply BELOW. 2: constructor.
      erewrite <- (IH (existT _ var rep)); simpl; eauto.
      red. eapply Relation_Operators.left_lex. apply BELOW. constructor.

      intros.


      Lemma sap_reach:
        forall (vvs: PTree.t (type * sact)) a1 a2,
          forall v, reachable_var vvs a1 v -> 
          (forall v, var_in_sact a1 v -> var_in_sact a2 v) ->
          reachable_var vvs a2 v.
      Proof.
        induction 1; simpl; intros; eauto.
        - eapply var_in_sact_reachable; eauto. apply H. constructor.
        - trim (H1 x). constructor. eapply reachable_vars_in_sact2. 2: eauto. auto. auto.
        - eapply IHreachable_var.  intros; eapply H0.  eapply var_in_if_cond; eauto.
        - eapply IHreachable_var.  intros; eapply H0.  eapply var_in_if_true; eauto.
        - eapply IHreachable_var.  intros; eapply H0.  eapply var_in_if_false; eauto.
        - eapply IHreachable_var.  intros; eapply H0.  eapply var_in_sact_binop_1; eauto.
        - eapply IHreachable_var.  intros; eapply H0.  eapply var_in_sact_binop_2; eauto.
        - eapply IHreachable_var.  intros; eapply H0.  eapply var_in_sact_unop; eauto.
        - eapply IHreachable_var.  intros; eapply H0.  eapply var_in_sact_external; eauto.
      Qed.

      eapply sap_reach in H; eauto.
      eapply sap_reach in H; eauto.
      eapply reachable_var_aux_below_get; eauto.
      intros.
      eapply sap_reach in H; eauto.
      eapply reachable_var_aux_below_get; eauto.
    - intros. split; intro A; inv A; econstructor.
    - inv WTs.
      intros.
      split; intro A; inv A.
      + econstructor.
        eapply (IH2 s1). lia. intros; eapply BELOW. eapply reachable_var_if_cond; eauto. eauto. eauto.
        eapply (IH2 (if b then s2 else s3)).
        destr; lia. intros; eapply BELOW. destr_in H. eapply reachable_var_if_true; eauto.
        eapply reachable_var_if_false; eauto.
        destr; eauto. eauto.
      + econstructor.
        eapply (IH2 s1). lia. intros; eapply BELOW. eapply reachable_var_if_cond; eauto. eauto. eauto.
        eapply (IH2 (if b then s2 else s3)).
        destr; lia. intros; eapply BELOW. destr_in H. eapply reachable_var_if_true; eauto.
        eapply reachable_var_if_false; eauto.
        destr; eauto. eauto.
    - inv WTs; intros.
      split; intro A; inv A; econstructor; eauto.
      eapply (IH2 s). lia. intros; eapply BELOW. eapply reachable_var_unop; eauto. eauto. eauto.
      eapply (IH2 s). lia. intros; eapply BELOW. eapply reachable_var_unop; eauto. eauto. eauto.
    - inv WTs; intros.
      split; intro A; inv A; econstructor; eauto.
      eapply (IH2 s1). lia. intros; eapply BELOW. eapply reachable_var_binop1; eauto. eauto. eauto.
      eapply (IH2 s2). lia. intros; eapply BELOW. eapply reachable_var_binop2; eauto. eauto. eauto.
      eapply (IH2 s1). lia. intros; eapply BELOW. eapply reachable_var_binop1; eauto. eauto. eauto.
      eapply (IH2 s2). lia. intros; eapply BELOW. eapply reachable_var_binop2; eauto. eauto. eauto.
    - inv WTs; intros.
      split; intro A; inv A; econstructor; eauto.
      eapply (IH2 s). lia. intros; eapply BELOW. eapply reachable_var_externalCall; eauto. eauto. eauto.
      eapply (IH2 s). lia. intros; eapply BELOW. eapply reachable_var_externalCall; eauto. eauto. eauto.
    - intros. split; intro A; inv A; econstructor.
  Qed.

  Lemma interp_sact_replace_subact_iff:
    forall vvs positions
           (NP: forall k ps, positions ! k = Some ps -> no_prefix ps)
           subact
           (POSOK: forall k t s ps,
               positions ! k = Some ps ->
               vvs ! k = Some (t, s) ->
               forall p (IN: In p ps),
                 subact_at_position s p = Some subact)
           tn (WWT: wt_sact vvs subact tn)
           rep (WTrep: wt_sact vvs rep tn)
           (WTvvs: wt_vvs (Sigma:=Sigma) R  vvs)
           (VSV: vvs_smaller_variables vvs)
           (SAME1: forall ov,
               interp_sact vvs subact ov <-> interp_sact vvs rep ov)
           (SMALLER: forall var, var_in_sact rep var -> var_in_sact subact var)
           a
           t
           (WT: wt_sact vvs a t),
    forall vv,
      interp_sact vvs a vv <->
        interp_sact (replace_subact_in_vars vvs positions rep) a vv.
  Proof.
    intros; eapply interp_sact_replace_subact; eauto.
    intros; eapply reachable_var_aux_below; eauto.
    intros. eapply wt_sact_valid_vars; eauto. apply vvs_range_max_var.
  Qed.

  Lemma interp_sact_replace_subact':
    forall vvs
           (WTvvs: wt_vvs R  vvs)
           (VSV: vvs_smaller_variables vvs)
           idx v
           (SAME1: forall ov,
               interp_sact (sigma:=sigma) REnv r vvs (SVar idx) ov <->
                 interp_sact (sigma:=sigma) REnv r vvs v ov
           )
           (SMALLER: forall var, reachable_var vvs v var -> (var < idx)%positive)
           (tt : type)
           (OLDTYPE : wt_sact R  vvs (SVar idx) tt)
           (NEWTYPE : wt_sact R  vvs v tt)
           a t
           (WT: wt_sact  R vvs a t),
    forall vv,
      interp_sact (sigma:=sigma) REnv r vvs a vv <->
        interp_sact (sigma:=sigma) REnv r (replace_subact_in_vars vvs idx v) a vv.
  Proof.
    intros.
    eapply interp_sact_replace_subact; eauto.
    eapply reachable_var_aux_below. eauto.
    eapply wt_sact_valid_vars; eauto. apply vvs_range_max_var.
  Qed.


  Lemma wf_sf_replace_subact':
    forall reg val sf
           tt (OLDTYPE: wt_sact  R (vars sf) (SVar reg) tt)
           (NEWTYPE: wt_sact  R (vars sf) val tt)
           (SMALLER:   forall var : positive, reachable_var (vars sf) val var -> (var < reg)%positive),
      wf_sf sf -> wf_sf (replace_subact sf reg val).
  Proof.
    intros reg val sf tt OLDTYPE NEWTYPE SMALLER WF.
    destruct WF.
    split.
    - simpl. eapply wt_vvs_replace_subact_in_vars; eauto.
    - eapply vsv_replace_subact_in_vars; eauto.
    - simpl. intros. eapply wt_sact_replace_subact_in_vars; eauto.
  Qed.

  Lemma interp_sact_change_vvs:
    forall vvs1 (VSV1: vvs_smaller_variables vvs1)
           vvs2 (VSV2: vvs_smaller_variables vvs2) a v
           (IS: interp_sact (sigma:=sigma) REnv r vvs1 a v)
           t (WT1: wt_sact  R vvs1 a t)
           (WT2: wt_sact  R vvs2 a t)
           (SMALLER: forall var, reachable_var vvs1 a var -> vvs1 ! var = vvs2 ! var),
      interp_sact (sigma:=sigma) REnv r vvs2 a v.
  Proof.
    intros.
    eapply interp_eval. 6: apply IS. all: eauto.
    exists O; intros. eapply eval_sact_reachable. intros; eapply SMALLER. auto.
  Qed.

  Lemma replace_subact_interp_rev':
    forall sf idx v
           (WFSF: wf_sf sf)
           (INTERP:
             forall oldv,
               interp_sact (sigma:=sigma) REnv r (vars sf) (SVar idx) oldv ->
               interp_sact (sigma:=sigma) REnv r (vars sf) v oldv
           )
           tt (OLDTYPE: wt_sact  R (vars sf) (SVar idx) tt),
        forall oldv,
          interp_sact (sigma:=sigma) REnv r (vars sf) v oldv ->
          interp_sact (sigma:=sigma) REnv r (vars sf) (SVar idx) oldv.
  Proof.
    intros.
    edestruct @wt_sact_interp' as (vv & IS & WTV). 6: apply OLDTYPE. all: eauto. apply WFSF. apply WFSF.
    eapply wt_sact_valid_vars; eauto. apply vvs_range_max_var.
    eapply INTERP in IS as IS2.
    exploit @interp_sact_determ. apply H. apply IS2. intro; subst. congruence.
  Qed.

  Lemma replace_subact_interp_rev:
    forall sf idx v
           (WFSF: wf_sf sf)
           (INTERP:
             forall oldv,
               interp_sact (sigma:=sigma) REnv r (vars sf) (SVar idx) oldv ->
               interp_sact (sigma:=sigma) REnv r (vars sf) v oldv
           )
           tt (OLDTYPE: wt_sact  R (vars sf) (SVar idx) tt),
        forall oldv,
          interp_sact (sigma:=sigma) REnv r (vars sf) v oldv <->
          interp_sact (sigma:=sigma) REnv r (vars sf) (SVar idx) oldv.
  Proof.
    intros.
    split; intros; eauto.
    eapply replace_subact_interp_rev'; eauto.
  Qed.

  Lemma sf_eq_replace_subact:
    forall sf idx v
           (WFSF: wf_sf sf)
           (INTERP:
             forall oldv,
               interp_sact (sigma:=sigma) REnv r (vars sf) (SVar idx) oldv ->
               interp_sact (sigma:=sigma) REnv r (vars sf) v oldv
           )
           (SMALLER: forall var, reachable_var (vars sf) v var -> (var < idx)%positive)
           tt (OLDTYPE: wt_sact  R (vars sf) (SVar idx) tt)
           (NEWTYPE: wt_sact  R (vars sf) v tt),
      sf_eq R Sigma r sigma sf (replace_subact sf idx v).
  Proof.
    intros.
    split.
    - reflexivity.
    - intros. eapply interp_sact_replace_subact'; eauto. apply WFSF. apply WFSF.
      intros; symmetry; eapply replace_subact_interp_rev; eauto.
    - simpl. intros.
      split.
      intros; eapply wt_sact_replace_subact_in_vars; eauto.
      intro A; inv A.
      setoid_rewrite PTree.gmap in H1. unfold option_map in H1.
      destr_in H1; inv H1. destr_in H2. inv H2. econstructor; eauto.
  Qed.

  Lemma replace_subact_interp_cycle_ok':
    forall
      {reg} {idx} {sf} {v}
      (WFSF: wf_sf sf)
      (INTERP:
        forall oldv,
          interp_sact (sigma:=sigma) REnv r (vars sf) (SVar idx) oldv ->
          interp_sact (sigma:=sigma) REnv r (vars sf) v oldv
      )
      (SMALLER: forall var, reachable_var (vars sf) v var -> (var < idx)%positive)
      tt (OLDTYPE: wt_sact  R (vars sf) (SVar idx) tt)
      (NEWTYPE: wt_sact  R (vars sf) v tt),
    getenv REnv (interp_cycle r sigma sf) reg
    = getenv REnv (interp_cycle r sigma (replace_subact sf idx v)) reg.
  Proof.
    intros.
    eapply sf_eq_interp_cycle_ok; eauto.
    - eapply wf_sf_replace_subact' in WFSF; eauto.
    - eapply sf_eq_replace_subact; eauto.
  Qed.

  Record var_simpl vvs idx v :=
    {
      vs_interp:
      forall oldv,
        interp_sact (sigma:=sigma) REnv r vvs (SVar idx) oldv ->
        interp_sact (sigma:=sigma) REnv r vvs v oldv;
      vs_smaller:
      forall var, reachable_var vvs v var -> ((var < idx)%positive);
      vs_type: type;
      vs_oldtype: wt_sact  R vvs (SVar idx) vs_type;
      vs_newtype: wt_sact  R vvs v vs_type
    }.

  Lemma wf_sf_replace_subact:
    forall reg val sf
           (VS: var_simpl (vars sf) reg val),
      wf_sf sf -> wf_sf (replace_subact sf reg val).
  Proof.
    intros reg val sf VS WFSF; inv VS; eapply wf_sf_replace_subact'; eauto.
  Qed.


  Lemma replace_subact_interp_cycle_ok:
    forall
      {reg} {idx} {sf} {v}
      (WFSF: wf_sf sf)
      (VS: var_simpl (vars sf) idx v),
    getenv REnv (interp_cycle r sigma sf) reg
    = getenv REnv (interp_cycle r sigma (replace_subact sf idx v)) reg.
  Proof.
    intros. destruct VS.
    eapply replace_subact_interp_cycle_ok'; eauto.
  Qed.

End ReplaceSubact.
