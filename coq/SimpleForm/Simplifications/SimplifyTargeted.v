Require Import Koika.KoikaForm.Untyped.UntypedSemantics.
Require Import Koika.SimpleForm.Interpretation.
Require Import Koika.SimpleForm.Direction.
Require Import Koika.SimpleForm.Operations.
Require Import Koika.SimpleForm.Simplifications.Simplify.
Require Import Koika.BitsToLists.
Require Import Koika.KoikaForm.SimpleVal.
Require Import Koika.KoikaForm.Types.
Require Import Koika.SimpleForm.SimpleForm.
Require Import Koika.Utils.EqDec.
Require Import Koika.Utils.Maps.
Require Import Koika.Utils.Environments.
Require Import Coq.Logic.FunctionalExtensionality.

Section SimplifyTargeted.
  Context {reg_t ext_fn_t: Type}.
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

  Definition exempted (pos: position) (exemptions: list position) :=
    List.existsb (position_beq pos) exemptions.

  Fixpoint simplify_sact_targeted_aux
    (ua: sact) (e: list position) (pos: position)
  : sact :=
    match ua with
    | SIf cond tb fb =>
      let cond' :=
        simplify_sact_targeted_aux cond e (pos++[branch1]) in
      if (exempted pos e) then
        SIf
          cond'
          (simplify_sact_targeted_aux tb e (pos++[branch2]))
          (simplify_sact_targeted_aux fb e (pos++[branch3]))
      else
        match eval_sact_no_vars r sigma cond' with
        | Some (Bits [true]) => simplify_sact_targeted_aux tb e (pos++[branch2])
        | Some (Bits [false]) =>
          simplify_sact_targeted_aux fb e (pos++[branch3])
        | _ =>
          SIf
            cond' (simplify_sact_targeted_aux tb e (pos++[branch2]))
            (simplify_sact_targeted_aux fb e (pos++[branch3]))
        end
    | SBinop ufn a1 a2 =>
      if (exempted pos e) then
        SBinop
          ufn (simplify_sact_targeted_aux a1 e (pos++[branch1]))
          (simplify_sact_targeted_aux a2 e (pos++[branch2]))
      else
        let a1' := simplify_sact_targeted_aux a1 e (pos++[branch1]) in
        match ufn with
        | PrimUntyped.UBits2 PrimUntyped.UAnd =>
          match eval_sact_no_vars r sigma a1' with
          | Some (Bits [false]) => const_false
          | Some (Bits [true]) =>
            simplify_sact_targeted_aux a2 e (pos++[branch2])
          | _ =>
            let a2' := simplify_sact_targeted_aux a2 e (pos++[branch2]) in
            match eval_sact_no_vars r sigma a2' with
            | Some (Bits [false]) => const_false
            | Some (Bits [true]) => a1'
            | _ => SBinop ufn a1' a2'
            end
          end
        | PrimUntyped.UBits2 PrimUntyped.UOr =>
          match eval_sact_no_vars r sigma a1' with
          | Some (Bits [true]) => const_true
          | Some (Bits [false]) =>
            simplify_sact_targeted_aux a2 e (pos++[branch2])
          | _ =>
            let a2' := simplify_sact_targeted_aux a2 e (pos++[branch2]) in
            match eval_sact_no_vars r sigma a2' with
            | Some (Bits [true]) => const_true
            | Some (Bits [false]) => a1'
            | _ => SBinop ufn a1' a2'
            end
          end
        | fn =>
          let a2' := simplify_sact_targeted_aux a2 e (pos++[branch2]) in
          match
            eval_sact_no_vars r sigma a1', eval_sact_no_vars r sigma a2'
          with
          | Some x, Some y =>
            match sigma2 fn x y with
            | Some r => SConst r
            | None => SBinop ufn a1' a2'
            end
          | _, _ => SBinop ufn a1' a2'
          end
        end
    | SUnop ufn a =>
      if (exempted pos e) then
        SUnop ufn (simplify_sact_targeted_aux a e (pos++[branch1]))
      else
        let a := simplify_sact_targeted_aux a e (pos++[branch1]) in
        match eval_sact_no_vars r sigma a with
        | Some x =>
          match sigma1 ufn x with
          | Some r => SConst r
          | None => SUnop ufn a
          end
        | None => SUnop ufn a
        end
    | SExternalCall ufn a =>
      SExternalCall ufn (simplify_sact_targeted_aux a e (pos++[branch1]))
    | SVar _ | SReg _ | SConst _ => ua
    end.

  Definition simplify_sact_targeted (ua: sact) (exemptions: list position)
  : sact :=
    simplify_sact_targeted_aux ua exemptions [].

  Definition simplify_sf_targeted
    (sf: simple_form) (exemptions: list (list position))
  := {|
    final_values := final_values sf;
    vars :=
      fst (
        PTree.fold
        (fun
          (acc: ((PTree.tree (type * SimpleForm.sact)) * list (list position)))
          elt (val: (type * SimpleForm.sact))
        =>
          let '(tree, acc_exs) := acc in
          let exs: list position := List.hd [] acc_exs in
          let res := simplify_sact_targeted (snd val) exs in
          (PTree.set elt (fst val, res) tree, tl exemptions))
        (vars sf)
        (PTree.empty (type * SimpleForm.sact), exemptions))
    |}.

  Lemma simplify_targeted_no_exemptions_pos_irrelevant:
    forall a p1 p2,
    simplify_sact_targeted_aux a [] p1 = simplify_sact_targeted_aux a [] p2.
  Proof.
    induction a; intros; eauto; simpl.
    - erewrite IHa1. erewrite IHa2. erewrite IHa3. eauto.
    - erewrite IHa. eauto.
    - erewrite IHa1. erewrite IHa2. eauto.
    - erewrite IHa. eauto.
  Qed.

  Lemma sact_simplify_targeted_no_exemptions_eq_simplify :
    forall a,
    simplify_sact_targeted a [] = simplify_sact r sigma a.
  Proof.
    induction a; eauto.
    - unfold simplify_sact_targeted in *. simpl.
      erewrite simplify_targeted_no_exemptions_pos_irrelevant in IHa1.
      erewrite simplify_targeted_no_exemptions_pos_irrelevant in IHa2.
      erewrite simplify_targeted_no_exemptions_pos_irrelevant in IHa3.
      rewrite IHa1, IHa2, IHa3. eauto.
    - unfold simplify_sact_targeted in *. simpl.
      erewrite simplify_targeted_no_exemptions_pos_irrelevant in IHa.
      rewrite IHa. eauto.
    - unfold simplify_sact_targeted in *. simpl.
      erewrite simplify_targeted_no_exemptions_pos_irrelevant in IHa1.
      erewrite simplify_targeted_no_exemptions_pos_irrelevant in IHa2.
      rewrite IHa1, IHa2. eauto.
    - unfold simplify_sact_targeted in *. simpl.
      erewrite simplify_targeted_no_exemptions_pos_irrelevant in IHa.
      rewrite IHa. eauto.
  Qed.

  Lemma simplify_targeted_no_exemptions_eq_simplify :
    forall sf,
    simplify_sf_targeted sf [] = simplify_sf r sigma sf.
  Proof.
    intros.
    destruct sf.
    unfold simplify_sf, simplify_sf_targeted.
    simpl. f_equal.
    unfold simplify_vars.
    f_equal.
    (* apply functional_extensionality; intro. *)
    (* apply functional_extensionality; intro. *)
    (* destruct x0. simpl. *)
    (* f_equal. *)
    (* destruct (Pos.to_nat x); *)
    (*   apply sact_simplify_targeted_no_exemptions_eq_simplify. *)
  Admitted.

  Lemma simplify_unop_targeted_cases:
    forall e p ufn a a',
    simplify_sact_targeted_aux (SUnop ufn a) e p = a'
    -> forall ta tr vss, wt_unop ufn ta tr
    -> wt_sact (Sigma:=Sigma) R vss a ta
    -> (
      exists b x,
      eval_sact_no_vars
        r sigma (simplify_sact_targeted_aux a e (p ++ [branch1]))
      = Some b
      /\ sigma1 ufn b = Some x
      /\ a' = SConst x)
    \/ a' = SUnop ufn (simplify_sact_targeted_aux a e (p ++ [branch1])).
  Proof.
    intros. unfold simplify_sact_targeted in H. simpl in H. simpl.
    subst. destr; eauto. destr; eauto. destr; eauto.
    left. exists v, v0. split; auto.
  Qed.

  Lemma simplify_bnop_targeted_cases:
    forall ufn a1 a2 a' e p,
    simplify_sact_targeted_aux (SBinop ufn a1 a2) e p = a'
    -> a' = SBinop ufn (simplify_sact_targeted_aux a1 e (p ++ [branch1])) (simplify_sact_targeted_aux a2 e (p ++ [branch2]))
    \/ (ufn = PrimUntyped.UBits2 PrimUntyped.UAnd
      /\ ((eval_sact_no_vars r sigma (simplify_sact_targeted_aux a1 e (p ++ [branch1])) = Some (Bits [true])
        /\ a' = simplify_sact_targeted_aux a2 e (p ++ [branch2]))
        \/ (eval_sact_no_vars r sigma (simplify_sact_targeted_aux a1 e (p ++ [branch1])) = Some (Bits [false])
          /\ a' = const_false)
        \/ (eval_sact_no_vars r sigma (simplify_sact_targeted_aux a2 e (p ++ [branch2])) = Some (Bits [true])
            /\ a' = simplify_sact_targeted_aux a1 e (p ++ [branch1]))
        \/ (eval_sact_no_vars r sigma (simplify_sact_targeted_aux a2 e (p ++ [branch2])) = Some (Bits [false])
            /\ a' = const_false)))
    \/ (ufn = PrimUntyped.UBits2 PrimUntyped.UOr
        /\ ((eval_sact_no_vars r sigma (simplify_sact_targeted_aux a1 e (p ++ [branch1])) = Some (Bits [true])
             /\ a' = const_true)
            \/ (eval_sact_no_vars r sigma (simplify_sact_targeted_aux a1 e (p ++ [branch1])) = Some (Bits [false])
                /\ a' = simplify_sact_targeted_aux a2 e (p ++ [branch2]))
            \/ (eval_sact_no_vars r sigma (simplify_sact_targeted_aux a2 e (p ++ [branch2])) = Some (Bits [true])
                /\ a' = const_true)
            \/ (eval_sact_no_vars r sigma (simplify_sact_targeted_aux a2 e (p ++ [branch2])) = Some (Bits [false])
                /\ a' = simplify_sact_targeted_aux a1 e (p ++ [branch1]))))
  \/ (
    exists v1 v2 v,
    eval_sact_no_vars r sigma (simplify_sact_targeted_aux a1 e (p ++ [branch1])) = Some v1
    /\ eval_sact_no_vars r sigma (simplify_sact_targeted_aux a2 e (p ++ [branch2])) = Some v2
    /\ sigma2 ufn v1 v2 = Some v
    /\ a' = SConst v).
  Proof.
    intros. unfold simplify_sact_targeted in H. simpl in H. subst.
    repeat destr; intuition eauto; repeat right; do 3 eexists; repeat split;
      eauto.
  Qed.

  Lemma simplify_sact_targeted_correct:
    forall vvs (WTV: wt_vvs R (Sigma:=Sigma) vvs) n a res t e p,
    wt_sact (Sigma:=Sigma) R vvs a t
    -> eval_sact vvs a n = Some res
    -> eval_sact vvs (simplify_sact_targeted_aux a e p) n = Some res.
  Proof.
    unfold simplify_sact_targeted.
    induction n; intros a res t e p WT EVAL; eauto.
    simpl in EVAL.
    unfold opt_bind in EVAL.
    repeat destr_in EVAL; inv EVAL; auto.
    - simpl. rewrite Heqo; eauto.
    - inv WT.
      destruct (exempted p e) eqn:eq.
      + simpl. rewrite eq.
        generalize (IHn _ _ _ e (p ++ [branch1]) H3 Heqo); intros.
        rewrite H. simpl.
        generalize (IHn _ _ _ e (p ++ [branch2]) H5 H0); intros.
        rewrite H1. rewrite H0. reflexivity.
      + rewrite H0. simpl. rewrite eq.
        destruct (
          eval_sact_no_vars
            r sigma (simplify_sact_targeted_aux s1 e (p ++ [branch1]))
        ) eqn:?.
        * eapply eval_sact_eval_sact_no_vars in Heqo0; eauto. subst.
          transitivity (
            eval_sact
              vvs (simplify_sact_targeted_aux s2 e (p ++ [branch2])) (S n)
          ); eauto.
          exploit IHn. 2: apply H0. eauto. intro ES.
          exploit (
            eval_sact_more_fuel (reg_t := reg_t) (ext_fn_t := ext_fn_t)
            (REnv := REnv)
          ).
          apply ES.
          2: intro ES'; rewrite ES'. lia. eauto.
        * erewrite IHn. 2-3: eauto. simpl.
          erewrite IHn; eauto.
    - inv WT. simpl.
      destruct (exempted p e) eqn:eq.
      + generalize (IHn _ _ _ e (p ++ [branch1]) H3 Heqo); intros.
        rewrite H. simpl.
        generalize (IHn _ _ _ e (p ++ [branch3]) H6 H0); intros.
        rewrite H1. rewrite H0. reflexivity.
      + destruct (
          eval_sact_no_vars
            r sigma (simplify_sact_targeted_aux s1 e (p ++ [branch1]))
        ) eqn:?.
        eapply eval_sact_eval_sact_no_vars in Heqo0; eauto. subst.
        transitivity (
          eval_sact
            vvs (simplify_sact_targeted_aux s3 e (p ++ [branch3])) (S n)
        ). reflexivity.
        exploit IHn. 2: apply H0. eauto. intro ES.
        exploit (
          eval_sact_more_fuel (reg_t := reg_t) (ext_fn_t := ext_fn_t)
          (REnv := REnv)
        ).
        apply ES.
        2: intro ES'; rewrite ES'. lia. eauto.
        erewrite IHn. 2-3: eauto. simpl.
        erewrite IHn; eauto.
    - inv WT.
      edestruct (simplify_unop_targeted_cases e p ufn1 s _ eq_refl) as
        [(b & vv & EQ & ESNV & EQ')|EQ]; eauto.
      + rewrite EQ'. simpl.
        exploit (
          eval_sact_eval_sact_no_vars (reg_t := reg_t) (ext_fn_t := ext_fn_t)
          (REnv := REnv)
        ).
        2: eauto. eapply IHn. eauto. eauto.
        intros ->.
        simpl. auto.
      + rewrite EQ. simpl. erewrite IHn; simpl; eauto.
    - inv WT.
      exploit (
        eval_sact_wt (reg_t := reg_t) (ext_fn_t := ext_fn_t) (REnv := REnv)
      ).
      5: apply Heqo. all: eauto.
      exploit (
        eval_sact_wt (reg_t := reg_t) (ext_fn_t := ext_fn_t) (REnv := REnv)
      ).
      5: apply Heqo0. all: eauto.
      intros WTv2 WTv1.
      exploit Wt.wt_binop_sigma1. eauto. eauto. eauto. eauto. intro WTres.
      eapply IHn in Heqo; eauto.
      eapply IHn in Heqo0; eauto.
      destruct (simplify_bnop_targeted_cases ufn2 s1 s2 _ e p eq_refl) as
        [EQ|[(ufneq & [(ESNV & EQ)|[(ESNV & EQ)|[(ESNV & EQ)|(ESNV & EQ)]]])
            |[(ufneq & [(ESNV & EQ)|[(ESNV & EQ)|[(ESNV & EQ)|(ESNV & EQ)]]])|
        (v1 & v2 & vv & ESNV1 & ESNV2 & SIGMA & EQ)]]]; rewrite EQ; clear EQ.
      + simpl. rewrite Heqo, Heqo0.  reflexivity.
      + exploit (
          eval_sact_eval_sact_no_vars (reg_t := reg_t) (ext_fn_t := ext_fn_t)
          (REnv := REnv)
        ).
        apply Heqo. apply ESNV. intros ->.
        inv WTv1. inv H6.
        apply Sact.wt_val_bool in WTv2.
        apply Sact.wt_val_bool in WTres.
        destruct WTv2, WTres. subst.
        unfold eval_sact.
        erewrite eval_sact_more_fuel. 2: eauto. simpl. auto. lia.
      + exploit (
          eval_sact_eval_sact_no_vars (reg_t := reg_t) (ext_fn_t := ext_fn_t)
          (REnv := REnv)
        ). apply Heqo. apply ESNV. intros ->.
        inv WTv1. inv H6.
        apply Sact.wt_val_bool in WTv2.
        apply Sact.wt_val_bool in WTres.
        destruct WTv2, WTres. subst.
        simpl. auto.
      + exploit (
          eval_sact_eval_sact_no_vars (reg_t := reg_t) (ext_fn_t := ext_fn_t)
          (REnv := REnv)
        ). 2: apply ESNV. eauto. intros ->.
        inv WTv2. inv H6.
        apply Sact.wt_val_bool in WTv1.
        apply Sact.wt_val_bool in WTres.
        destruct WTv1, WTres. subst.
        unfold eval_sact.
        erewrite eval_sact_more_fuel. 2: eauto. simpl.
        rewrite andb_true_r; auto. lia.
      + exploit (
          eval_sact_eval_sact_no_vars (reg_t := reg_t) (ext_fn_t := ext_fn_t)
          (REnv := REnv)
        ). 2: apply ESNV. eauto. intros ->.
        inv WTv2. inv H6.
        apply Sact.wt_val_bool in WTv1.
        apply Sact.wt_val_bool in WTres.
        destruct WTv1, WTres. subst.
        simpl. rewrite andb_false_r; auto.
      + exploit (
          eval_sact_eval_sact_no_vars (reg_t := reg_t) (ext_fn_t := ext_fn_t)
          (REnv := REnv)
        ). 2: apply ESNV. eauto. intros ->.
        inv WTv1. inv H6.
        apply Sact.wt_val_bool in WTv2.
        apply Sact.wt_val_bool in WTres.
        destruct WTv2, WTres. subst. simpl; auto.
      + exploit (
          eval_sact_eval_sact_no_vars (reg_t := reg_t) (ext_fn_t := ext_fn_t)
          (REnv := REnv)
        ). 2: apply ESNV. eauto. intros ->.
        inv WTv1. inv H6.
        apply Sact.wt_val_bool in WTv2.
        apply Sact.wt_val_bool in WTres.
        destruct WTv2, WTres. subst.
        unfold eval_sact.
        erewrite eval_sact_more_fuel. 2: eauto. simpl. auto. lia.
      + exploit (
          eval_sact_eval_sact_no_vars (reg_t := reg_t) (ext_fn_t := ext_fn_t)
          (REnv := REnv)
        ). 2: apply ESNV. eauto. intros ->.
        inv WTv2. inv H6.
        apply Sact.wt_val_bool in WTv1.
        apply Sact.wt_val_bool in WTres.
        destruct WTv1, WTres. subst. simpl. rewrite orb_true_r; auto.
      + exploit (
          eval_sact_eval_sact_no_vars (reg_t := reg_t) (ext_fn_t := ext_fn_t)
          (REnv := REnv)
        ). 2: apply ESNV. eauto. intros ->.
        inv WTv2. inv H6.
        apply Sact.wt_val_bool in WTv1.
        apply Sact.wt_val_bool in WTres.
        destruct WTv1, WTres. subst.
        unfold eval_sact.
        erewrite eval_sact_more_fuel. 2: eauto. simpl.
        rewrite orb_false_r; auto. lia.
      + exploit (
          eval_sact_eval_sact_no_vars (reg_t := reg_t) (ext_fn_t := ext_fn_t)
          (REnv := REnv)
        ). 2: apply ESNV1. eauto. intros ->.
        exploit (
          eval_sact_eval_sact_no_vars (reg_t := reg_t) (ext_fn_t := ext_fn_t)
          (REnv := REnv)
        ). 2: apply ESNV2. eauto. intros ->.
        rewrite H0 in SIGMA. inv SIGMA. simpl. eauto.
    - simpl. inv WT;  erewrite IHn; simpl; eauto.
  Qed.

  Lemma simpl_sact_targeted_aux_some_p1_p2:
    forall e a p1 p2 v1 v2,
    eval_sact_no_vars r sigma (simplify_sact_targeted_aux a e p1) = Some v1
    -> eval_sact_no_vars r sigma (simplify_sact_targeted_aux a e p2) = Some v2
    -> v1 = v2.
  Proof.
    induction a; intros; simpl in *.
    - inv H.
    - inv H0. inv H. reflexivity.
    - destr_in H; destr_in H0; simpl in *.
      + destruct (eval_sact_no_vars r sigma (simplify_sact_targeted_aux a1 e (p1 ++ [branch1]))) eqn:eq1, (eval_sact_no_vars r sigma (simplify_sact_targeted_aux a1 e (p2 ++ [branch1]))) eqn:eq2.
        * assert (v = v0) by (apply (IHa1 _ _ _ _ eq1 eq2)). subst.
          destruct v0; try inv H0.
          simpl in *.
          destruct v.
          ** inv H2.
          ** simpl in *. destruct v.
             *** destruct b; eauto.
             *** inv H2.
        * simpl in *. inv H0.
        * simpl in *. inv H.
        * simpl in *. inv H.
      + destruct (eval_sact_no_vars r sigma (simplify_sact_targeted_aux a1 e (p1 ++ [branch1]))) eqn:eq1, (eval_sact_no_vars r sigma (simplify_sact_targeted_aux a1 e (p2 ++ [branch1]))) eqn:eq2; simpl in *.
        * assert (v = v0) by (apply (IHa1 _ _ _ _ eq1 eq2)). subst.
          destruct v0; simpl in *.
          ** destruct v; try easy. destruct b.
             *** destruct v; try easy. eapply IHa2; eauto.
             *** destruct v; try easy. eapply IHa3; eauto.
          ** destruct v; try easy.
          ** destruct v; try easy.
          ** destruct v; try easy.
        * rewrite eq2 in H0. simpl in *. inv H0.
        * inv H.
        * inv H.
      + destruct (eval_sact_no_vars r sigma (simplify_sact_targeted_aux a1 e (p1 ++ [branch1]))) eqn:eq1, (eval_sact_no_vars r sigma (simplify_sact_targeted_aux a1 e (p2 ++ [branch1]))) eqn:eq2; simpl in *.
        * assert (v = v0) by (apply (IHa1 _ _ _ _ eq1 eq2)). subst.
          destruct v0; simpl in *.
          ** destruct v; try easy. destruct b.
             *** destruct v; try easy. eapply IHa2; eauto.
             *** destruct v; try easy. eapply IHa3; eauto.
          ** destruct v; try easy.
          ** destruct v; try easy.
          ** destruct v; try easy.
        * inv H0.
        * rewrite eq1 in H. simpl in *. inv H.
        * inv H0.
      + destruct (eval_sact_no_vars r sigma (simplify_sact_targeted_aux a1 e (p1 ++ [branch1]))) eqn:eq1, (eval_sact_no_vars r sigma (simplify_sact_targeted_aux a1 e (p2 ++ [branch1]))) eqn:eq2; simpl in *.
        * assert (v = v0) by (apply (IHa1 _ _ _ _ eq1 eq2)). subst.
          destruct v0; simpl in *.
          ** destruct v; try easy.
             *** simpl in *. rewrite eq1 in H. rewrite eq2 in H0.
                 simpl in *. inv H0.
             *** simpl in *. destruct b.
                 **** destruct v.
                      { eapply IHa2; eauto. }
                      { simpl in *. rewrite eq1 in H. rewrite eq2 in H0.
                        simpl in *. inv H0. }
                 **** destruct v.
                      { eapply IHa3; eauto. }
                      { simpl in *. rewrite eq1 in H. rewrite eq2 in H0.
                        simpl in *. inv H0. }
          ** simpl in *. rewrite eq1 in H. rewrite eq2 in H0.
             simpl in *. inv H0.
          ** simpl in *. rewrite eq1 in H. rewrite eq2 in H0.
             simpl in *. inv H0.
          ** simpl in *. rewrite eq1 in H. rewrite eq2 in H0.
             simpl in *. inv H0.
        * rewrite eq2 in H0. simpl in *. inv H0.
        * rewrite eq1 in H. simpl in *. inv H.
        * rewrite eq1 in H. simpl in *. inv H.
    - destruct (exempted p1 e), (exempted p2 e); simpl in *.
      + destruct (eval_sact_no_vars r sigma (simplify_sact_targeted_aux a e (p1 ++ [branch1]))) eqn:eq1, (eval_sact_no_vars r sigma (simplify_sact_targeted_aux a e (p2 ++ [branch1]))) eqn:eq2; simpl in *; try easy.
        assert (v = v0) by (apply (IHa _ _ _ _ eq1 eq2)). subst.
        rewrite H in H0. inv H0. reflexivity.
      + destruct (eval_sact_no_vars r sigma (simplify_sact_targeted_aux a e (p1 ++ [branch1]))) eqn:eq1, (eval_sact_no_vars r sigma (simplify_sact_targeted_aux a e (p2 ++ [branch1]))) eqn:eq2; simpl in *; try easy.
        * assert (v = v0) by (apply (IHa _ _ _ _ eq1 eq2)). subst.
          rewrite H in H0. inv H0. reflexivity.
        * rewrite eq2 in H0. simpl in *. easy.
      + destruct (eval_sact_no_vars r sigma (simplify_sact_targeted_aux a e (p1 ++ [branch1]))) eqn:eq1, (eval_sact_no_vars r sigma (simplify_sact_targeted_aux a e (p2 ++ [branch1]))) eqn:eq2; simpl in *; try easy.
        * assert (v = v0) by (apply (IHa _ _ _ _ eq1 eq2)). subst.
          rewrite H0 in H. inv H. reflexivity.
        * rewrite eq1 in H. simpl in *. easy.
      + destruct (eval_sact_no_vars r sigma (simplify_sact_targeted_aux a e (p1 ++ [branch1]))) eqn:eq1, (eval_sact_no_vars r sigma (simplify_sact_targeted_aux a e (p2 ++ [branch1]))) eqn:eq2; simpl in *; try easy.
        * assert (v = v0) by (apply (IHa _ _ _ _ eq1 eq2)). subst.
          destr_in H; simpl in *. inv H0. inv H. reflexivity.
          rewrite eq1 in H. simpl in *. rewrite H in Heqo. inv Heqo.
        * rewrite eq2 in H0. simpl in *. inv H0.
        * rewrite eq1 in H. simpl in *. inv H.
        * rewrite eq1 in H. simpl in *. inv H.
    - destruct (exempted p1 e), (exempted p2 e); simpl in *.
      + destruct (eval_sact_no_vars r sigma (simplify_sact_targeted_aux a1 e (p1 ++ [branch1]))) eqn:eq1, (eval_sact_no_vars r sigma (simplify_sact_targeted_aux a1 e (p2 ++ [branch1]))) eqn:eq2; simpl in *; try easy;
        destruct (eval_sact_no_vars r sigma (simplify_sact_targeted_aux a2 e (p1 ++ [branch2]))) eqn:eq1b, (eval_sact_no_vars r sigma (simplify_sact_targeted_aux a2 e (p2 ++ [branch2]))) eqn:eq2b; simpl in *; try easy.
        * assert (v = v0) by (apply (IHa1 _ _ _ _ eq1 eq2)). subst.
          assert (v3 = v4) by (apply (IHa2 _ _ _ _ eq1b eq2b)). subst.
          destruct ufn2; simpl in *.
          ** destr_in H0; destr_in H0; inv H; inv H0; reflexivity.
          ** destr_in H0; try destr_in H0; inv H; inv H0; reflexivity.
          ** destr_in H0; try destr_in H0; inv H; inv H0; rewrite H2 in H1; inv H1; reflexivity.
          ** repeat destr_in H0; inv H0.
             *** destruct (take_drop pos v); simpl in *.
                 **** destruct p; destruct l0; inv H2. inv H. reflexivity.
                 **** inv H.
             *** inv H. reflexivity.
      + destruct (eval_sact_no_vars r sigma (simplify_sact_targeted_aux a1 e (p1 ++ [branch1]))) eqn:eq1, (eval_sact_no_vars r sigma (simplify_sact_targeted_aux a1 e (p2 ++ [branch1]))) eqn:eq2; simpl in *; try easy;
        destruct (eval_sact_no_vars r sigma (simplify_sact_targeted_aux a2 e (p1 ++ [branch2]))) eqn:eq1b, (eval_sact_no_vars r sigma (simplify_sact_targeted_aux a2 e (p2 ++ [branch2]))) eqn:eq2b; simpl in *; try easy.
        * assert (v = v0) by (apply (IHa1 _ _ _ _ eq1 eq2)). subst.
          assert (v3 = v4) by (apply (IHa2 _ _ _ _ eq1b eq2b)). subst.
          destruct ufn2; simpl in *.
          ** destr_in H0; try destr_in Heqo; try easy; destr_in Heqo; destr_in H; inv H; inv Heqo; simpl in H0; inv H0; eauto.
             *** apply val_beq_bits_implies_eq in Heqb1. inv Heqb1. apply val_beq_false in Heqb0. easy.
             *** apply val_beq_bits_implies_eq in Heqb1. inv Heqb1. apply val_beq_false in Heqb0. easy.
          ** destruct fn eqn:eqfn; simpl in *; subst; try easy.
             *** destruct v0 eqn:eqv0; try easy; subst.
                 destruct v eqn:eqv; try easy; destruct v4 eqn:eqv4; try easy.
                 **** destruct v0; simpl in *.
                      ++ rewrite eq2 in H0. rewrite eq2b in H0. simpl in H0.
                         rewrite H in H0. inv H0. reflexivity.
                      ++ destr_in H0; destr_in H0; subst.
  Admitted.

  Lemma wt_simplify_sact_targeted:
    forall vss a t,
    wt_sact R (Sigma:=Sigma) vss a t
    -> forall e p, wt_sact R (Sigma:=Sigma) vss (simplify_sact_targeted_aux a e p) t.
  Proof.
    induction 1; simpl; intros; eauto.
    - econstructor; eauto.
    - econstructor; eauto.
    - destruct (exempted p e).
      constructor; eauto.
      destr.
      exploit (
        eval_sact_no_vars_wt
          (reg_t := reg_t) (ext_fn_t := ext_fn_t) (REnv := REnv)
      ).
      eauto. eauto. 2: eauto. eauto.
      intro WT. apply Sact.wt_val_bool in WT. destruct WT; subst.
      destr; eauto.
      econstructor; eauto.
    - assert (
        wt_sact
          (Sigma:=Sigma) R vss
          match
            eval_sact_no_vars r sigma (simplify_sact_targeted_aux a e p)
          with
          | Some x =>
            match sigma1 ufn x with
            | Some r => SConst r
            | None =>
              SUnop ufn (simplify_sact_targeted_aux a e (p ++ [branch1]))
            end
          | None => SUnop ufn (simplify_sact_targeted_aux a e (p ++ [branch1]))
          end t'
      ). {
        destr.
        exploit (
          eval_sact_no_vars_wt
            (reg_t := reg_t) (ext_fn_t := ext_fn_t) (REnv := REnv)
        ).
        eauto. eauto. 2: eauto. eauto.
        intro WT.
        destr.
        econstructor; eauto.
        eapply Wt.wt_unop_sigma1; eauto.
        econstructor; eauto.
        econstructor; eauto.
      }
      destruct (exempted p e) eqn:eq.
      + destr_in H1.
        * destr_in H1; econstructor; eauto; eauto.
        * econstructor; eauto; eauto.
      + destr; auto.
        * repeat destr_in H1.
          ** exploit IHwt_sact. intro.
             repeat destr_in H1.
  Admitted.

  Lemma simplify_sact_wt_sact_targeted_ok':
    forall vvs a t (WTS: wt_sact (Sigma := Sigma) R vvs a t) e,
    wt_sact (Sigma := Sigma) R vvs (simplify_sact_targeted a e) t.
  Proof. intros. apply wt_simplify_sact_targeted. eauto. Qed.

  Lemma simplify_sact_targeted_reachable_vars_ok:
    forall vvs v s e p (RV: reachable_var vvs (simplify_sact_targeted_aux s e p) v),
    reachable_var vvs s v.
  Proof.
    induction s; intros; simpl in *; eauto.
    - repeat (destr_in RV); eauto;
        try (
          inv RV;
          try (eapply reachable_var_if_cond; eauto; fail);
          try (eapply reachable_var_if_true; eauto; fail);
          try (eapply reachable_var_if_false; eauto; fail);
          fail); subst.
      + econstructor.
        unfold simplify_sact_targeted in *. simpl in *.
  Admitted.

  Lemma simplify_sact_targeted_interp_sact_ok':
    forall a v vvs (WTVVS: wt_vvs (Sigma := Sigma) R vvs) t e
      (WTS: wt_sact (Sigma := Sigma) R vvs a t)
      (VVSSV: vvs_smaller_variables vvs),
    interp_sact (sigma := sigma) REnv r vvs a v
    -> interp_sact (sigma := sigma) REnv r vvs (simplify_sact_targeted a e) v.
  Proof.
    intros.
    eapply interp_sact_do_eval_sact in H; eauto.
    unfold do_eval_sact in H.
    eapply eval_sact_interp_sact.
    unfold simplify_sact_targeted.
    erewrite simplify_sact_targeted_correct; eauto.
  Qed.

  Lemma simplify_sact_targeted_var_in_sact_ok':
    forall s v e (VIS: var_in_sact (simplify_sact_targeted s e) v),
    var_in_sact s v.
  Proof.
    unfold simplify_sact_targeted.
    intros.
    induction s; try (eauto; fail).
    - simpl in VIS. repeat (destr_in VIS); try (
        inv VIS; try (apply var_in_if_cond; eauto; fail);
        try (apply var_in_if_true; eauto; fail);
        try (apply var_in_if_false; eauto; fail);
        fail).
  Admitted.

  Lemma simplify_sact_targeted_interp_sact_ok:
    forall
      vvs (WTVVS: wt_vvs (Sigma := Sigma) R vvs)
      (VVSSV: vvs_smaller_variables vvs) a v e
      (EV_INIT:
        interp_sact (sigma := sigma) REnv r vvs (simplify_sact_targeted a e) v)
      t (WTS: wt_sact (Sigma := Sigma) R vvs a t),
    interp_sact (sigma := sigma) REnv r vvs a v.
  Proof.
    unfold simplify_sact_targeted. induction a; simpl; intros; eauto; inv WTS.
  Admitted.

  Lemma sf_eq_simplify_sf_targeted sf:
    forall e,
    wf_sf sf -> sf_eq R Sigma r sigma sf (simplify_sf_targeted sf e).
  Proof.
  Admitted.

  Lemma wf_sf_simplify_sf_targeted:
    forall sf, wf_sf sf -> forall e, wf_sf (simplify_sf_targeted sf e).
  Proof.
  Admitted.

  Lemma simplify_sf_targeted_interp_cycle_ok:
    forall reg sf e,
    wf_sf sf
    -> getenv REnv (interp_cycle r sigma sf) reg
    = getenv REnv (interp_cycle r sigma (simplify_sf_targeted sf e)) reg.
  Proof.
    intros.
    eapply sf_eq_interp_cycle_ok; eauto.
    - apply wf_sf_simplify_sf_targeted; auto.
    - apply sf_eq_simplify_sf_targeted. auto.
  Qed.
End SimplifyTargeted.
