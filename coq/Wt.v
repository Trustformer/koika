Require Import BitsToLists.
Require Import TypeInference.
Require Import Desugaring.
Require Import UntypedIndSemantics.
Require Import Coq.Program.Equality.
Require Import SimpleVal.

Fixpoint size_uaction
         {pos_t var_t fn_name_t reg_t ext_fn_t: Type}
         (ua: Syntax.uaction pos_t var_t fn_name_t reg_t ext_fn_t) {struct ua}
  : nat :=
  match ua  with
  | UError err => 0
  | UFail tau => 0
  | UVar var => 0
  | UConst cst => 0
  | UAssign v ex => 1 + size_uaction ex
  | USeq a1 a2 => 1 + size_uaction a1 + size_uaction a2
  | UBind v ex body => 1 + size_uaction ex + size_uaction body
  | UIf cond tbranch fbranch =>
    1 + size_uaction cond + size_uaction tbranch + size_uaction fbranch
  | URead port idx => 0
  | UWrite port idx value => 1 + size_uaction value
  | UUnop ufn1 arg1 => 1 + size_uaction arg1
  | UBinop ufn2 arg1 arg2 => 1 + size_uaction arg1 + size_uaction arg2
  | UExternalCall ufn arg => 1 + size_uaction arg
  | UInternalCall ufn args =>
    1 + size_uaction (int_body ufn) + list_sum (map size_uaction args)
  | UAPos p e => 1 + size_uaction e
  | USugar s => 1 + size_sugar s
  end
with size_sugar
       {pos_t var_t fn_name_t reg_t ext_fn_t: Type}
       (s: usugar pos_t var_t fn_name_t reg_t ext_fn_t) {struct s}
     : nat :=
       match s with
       | UErrorInAst => 0
       | USkip => 0
       | UConstBits _ => 0
       | UConstString _ => 0
       | UConstEnum _ _ => 0
       | UProgn l => 1 + list_sum (map size_uaction l)
       | ULet bindings body =>
         1 + size_uaction body
         + list_sum (map (fun '(_, a) => size_uaction a) bindings)
       | UWhen cond body => size_uaction cond + size_uaction body
       | USwitch cond default branches =>
         1 + size_uaction cond + size_uaction default
         + list_sum
             (map (fun '(a,b) => S (size_uaction a + size_uaction b)) branches)
       | UStructInit sig l => 1 + list_sum (map (fun '(_, a) => size_uaction a) l)
       | UArrayInit tay l => 1 + list_sum (map size_uaction l)
       | UCallModule fR fSigma fn args =>
         1 + size_uaction (int_body fn) + list_sum (map size_uaction args)
       end.

Section WT.
  Variables pos_t fn_name_t: Type.
  Variable var_t: Type.
  Context {eq_dec_var_t: EqDec var_t}.
  (* Variable ext_fn_t: Type. *)
  (* Variable reg_t: Type. *)
  (* Variable R : reg_t -> type. *)
  (* Variable Sigma: ext_fn_t -> ExternalSignature. *)

  Lemma cast_action'_eq:
    forall
      (p: pos_t) (sig: tsig var_t) (tau1 tau2: type)
      {reg_t ext_fn_t: Type}
      (R: reg_t -> type)
      (Sigma: ext_fn_t -> ExternalSignature)
      (a: TypedSyntax.action pos_t var_t fn_name_t R Sigma sig tau1)
      (e: error_message var_t fn_name_t) a',
      TypeInference.cast_action' R Sigma p tau2 a e = Success a' ->
      exists p : tau1 = tau2, a' = eq_rect _ _ a _ p.
  Proof.
    unfold TypeInference.cast_action'. intros.
    destr_in H. subst.
    unfold eq_rect_r in H. simpl in H. inv H.
    exists eq_refl; reflexivity. inv H.
  Qed.

  Lemma cast_action_eq:
    forall {reg_t ext_fn_t: Type}
           (R: reg_t -> type)
           (Sigma: ext_fn_t -> ExternalSignature)
           (p: pos_t) (sig: tsig var_t) (tau1 tau2: type)
           (a: TypedSyntax.action pos_t var_t fn_name_t R Sigma sig tau1) a',
      TypeInference.cast_action R Sigma p tau2 a = Success a'
      -> exists p : tau1 = tau2, a' = eq_rect _ _ a _ p.
  Proof.
    intros. unfold TypeInference.cast_action in H.
    eapply cast_action'_eq; eauto.
  Qed.


  Lemma assert_argtypes'_same_length:
    forall {T} {reg_t ext_fn_t} (R: reg_t -> type)
           (Sigma: ext_fn_t -> ExternalSignature)
           sig p (src: T) nexpected fn_name l1 l2 s0,
      assert_argtypes'
        (sig:=sig)
        (fn_name_t := fn_name_t)
        (pos_t := pos_t)
        (var_t := var_t)
        R Sigma src nexpected fn_name p l1 l2 = Success s0 ->
      List.length l1 = List.length l2.
  Proof.
    induction l1; simpl; intros; eauto.
    - destr_in H; inv H. reflexivity.
    - repeat destr_in H; inv H. simpl.
      eapply IHl1 in Heqr0. rewrite Heqr0; reflexivity.
  Qed.

  Lemma argtypes_app:
    forall {T}  {reg_t ext_fn_t} (R: reg_t -> type)
           (Sigma: ext_fn_t -> ExternalSignature)
           sig p (src: T) nexpected fn_name l1 l2 l3 l4 s0,
      assert_argtypes' (sig:=sig) (fn_name_t := fn_name_t) (pos_t := pos_t)
                       (var_t := var_t) R Sigma src nexpected fn_name p (l1 ++ l2) (l3 ++ l4)
      = Success s0 ->
      List.length l1 = List.length l3 -> List.length l2 = List.length l4 ->
      exists s1 s2,
        assert_argtypes' R Sigma src nexpected fn_name p l1 l3 = Success s1
        /\ assert_argtypes' R Sigma src nexpected fn_name p l2 l4 = Success s2.
  Proof.
    induction l1; simpl; intros; eauto.
    - destruct l3; simpl in *; try lia.
      eexists; eexists; split; eauto.
    - destruct l3; simpl in *; try lia.
      repeat destr_in H; inv H.
      eapply IHl1 in Heqr0; try lia.
      destruct Heqr0 as (s3 & s4 & EQ1 & EQ2).
      rewrite EQ1, EQ2.
      eexists; eexists; split; eauto.
  Qed.

  Lemma argtypes_ok:
    forall {T} {reg_t ext_fn_t} (R: reg_t -> type)
           (Sigma: ext_fn_t -> ExternalSignature)
           args sig p s (src: T) nexpected fn_name argspec argpos s0
           (IHua:
              forall ua' : uaction pos_t var_t fn_name_t reg_t ext_fn_t,
                In ua' args ->
                forall (p : pos_t) (sig : tsig var_t)
                       (a : {
                              tau : type
                                    & TypedSyntax.action pos_t var_t fn_name_t R Sigma sig tau
                       }),
                  type_action R Sigma p sig ua' = Success a ->
                  wt_action pos_t fn_name_t var_t (R:=R) (Sigma:=Sigma) sig ua'
                            (projT1 a)
           )
           (SAMELEN: List.length argpos = List.length s),
      result_list_map (type_action R Sigma p sig) args = Success s ->
      assert_argtypes' R Sigma src nexpected fn_name p (rev argspec)
                       (rev (combine argpos s))
      = Success s0 ->
      Forall2 (wt_action pos_t fn_name_t var_t (R:=R) (Sigma:=Sigma) sig)
              args (map snd argspec).
  Proof.
    induction args; simpl; intros; eauto.
    - inv H. simpl in H0.
      apply assert_argtypes'_same_length in H0. rewrite combine_nil in H0.
      simpl in H0.
      rewrite rev_length in H0.
      apply length_zero_iff_nil in H0. subst. simpl. constructor.
    - assert (
          List.length (rev argspec) = List.length (rev (combine argpos s))
        ).
      apply assert_argtypes'_same_length in H0. auto.
      repeat destr_in H; inv H. simpl in H1.
      simpl in SAMELEN. destruct argpos; simpl in SAMELEN; try lia.
      simpl in H1. rewrite app_length in H1. simpl in H1.
      destruct argspec; simpl in H1; try lia. simpl.
      simpl in H0.
      edestruct @argtypes_app as (s3 & s4 & EQ1 & EQ2). apply H0.
      rewrite app_length in H1. simpl in H1. lia. reflexivity.
      constructor.
      simpl in EQ2. repeat destr_in EQ2; inv EQ2. simpl.
      eapply IHua in Heqr; eauto.
      apply cast_action_eq in Heqr1. destruct Heqr1. rewrite <- x; auto.
      eapply IHargs. intros; eapply IHua; eauto.
      2: apply Heqr0. inv SAMELEN. reflexivity. eauto.
  Qed.


  Lemma result_list_map_length:
    forall {A B F} (f: A -> result B F) l l',
      result_list_map f l = Success l' ->
      List.length l' = List.length l.
  Proof.
    induction l; simpl; intros; eauto.
    inv H; reflexivity.
    repeat destr_in H; inv H. simpl.
    erewrite IHl; eauto.
  Qed.

  Lemma type_action_wt:
    forall {reg_t ext_fn_t} (R: reg_t -> type)
           (Sigma: ext_fn_t -> ExternalSignature)
           ua p sig a,
      type_action R Sigma p sig ua = Success a ->
      wt_action (R:=R) (Sigma:=Sigma) pos_t fn_name_t var_t sig ua (projT1 a).
  Proof.
    intros reg_t ext_fn_t R Sigma ua.
    remember (size_uaction ua).
    revert ua Heqn.
    pattern n.
    eapply Nat.strong_right_induction with (z:=0).
    { red. red. intros. subst. tauto. } 2: lia.
    intros n0 _ Plt ua Heqn. subst.
    assert (Plt':
              forall (ua': Syntax.uaction pos_t var_t fn_name_t reg_t ext_fn_t),
                size_uaction ua' < size_uaction ua ->
                forall (p : pos_t) (sig : tsig var_t)
                       (a : {
                              tau : type & TypedSyntax.action pos_t var_t fn_name_t R Sigma sig tau
                       }),
                  type_action R Sigma p sig ua' = Success a ->
                  wt_action pos_t fn_name_t var_t (R:=R) (Sigma:=Sigma) sig ua' (projT1 a)
           ).
    { intros. eapply Plt. 3: reflexivity. lia. auto. eauto. } clear Plt.
    rename Plt' into IHua. clear n.
    destruct ua; simpl; intros.
    - inv H.
    - inv H. simpl. constructor.
    - destr_in H; inv H.
      unfold opt_result in Heqr.
      destr_in Heqr; inv Heqr. simpl.
      econstructor. econstructor; eauto.
    - inv H. simpl. econstructor.
    - repeat destr_in H; inv H. simpl. econstructor.
      eapply IHua. simpl. lia. eauto.
      unfold opt_result in Heqr. destr_in Heqr; inv Heqr.
      edestruct @cast_action_eq. eauto. simpl in H. rewrite x.
      econstructor; eauto.
    - repeat destr_in H; inv H. simpl. econstructor.
      eapply cast_action_eq in Heqr0. destruct Heqr0. rewrite <- x.
      eapply IHua. simpl. lia. eauto.
      eapply IHua. simpl. lia. eauto.
    - repeat destr_in H; inv H. simpl. econstructor.
      eapply IHua. simpl. lia. eauto.
      eapply IHua. simpl. lia. eauto.
    - repeat destr_in H; inv H. simpl. econstructor.
      eapply cast_action_eq in Heqr0. destruct Heqr0. rewrite <- x.
      eapply IHua. simpl. lia. eauto.
      eapply IHua. simpl. lia. eauto.
      eapply cast_action_eq in Heqr3. destruct Heqr3. rewrite <- x.
      eapply IHua. simpl. lia. eauto.
    - repeat destr_in H; inv H. simpl. econstructor.
    - repeat destr_in H; inv H. simpl. econstructor.
      eapply cast_action_eq in Heqr0. destruct Heqr0. rewrite <- x.
      eapply IHua. simpl. lia. eauto.
    - repeat destr_in H; inv H. simpl.
      eapply IHua in Heqr. 2: simpl; lia. simpl in *.
      eapply cast_action_eq in Heqr1. destruct Heqr1. subst.
      econstructor. 2: eauto.
      rewrite x.
      destruct (PrimTypeInference.tc1 ufn1 (projT1 s)) eqn:?; simpl in Heqr0; inv Heqr0.
      Lemma wt_unop_primsigs:
        forall ufn1 t s0,
          PrimTypeInference.tc1 ufn1 t = Success s0 ->
          wt_unop ufn1 (arg1Sig (PrimSignatures.Sigma1 s0))
                  (retSig (PrimSignatures.Sigma1 s0)).
      Proof.
        intros ufn1 t s0 PTI.
        destruct ufn1; simpl in *;
          unfold opt_bind in PTI;
          repeat destr_in PTI; inv PTI.
        - repeat destr_in Heqr; inv Heqr; simpl; econstructor; eauto.
        - simpl; econstructor; eauto.
        - simpl; econstructor; eauto.
        - simpl; econstructor; eauto.
        - simpl; econstructor; eauto.
        - simpl; econstructor; eauto.
        - simpl; econstructor; eauto.
        - simpl; econstructor; eauto.
        - simpl; econstructor; eauto.
        - simpl; econstructor; eauto.
        - simpl; econstructor; eauto.
        - simpl; econstructor; eauto.
        - simpl; econstructor; eauto.
        - simpl; econstructor; eauto.
        - simpl; econstructor; eauto.
      Qed.
      eapply wt_unop_primsigs; eauto.
    - repeat destr_in H; inv H. simpl.
      eapply IHua in Heqr. 2: simpl; lia. simpl in *.
      eapply IHua in Heqr0. 2: simpl; lia. simpl in *.
      eapply cast_action_eq in Heqr2. destruct Heqr2. subst.
      eapply cast_action_eq in Heqr3. destruct Heqr3. subst.
      econstructor. 2-3: eauto.
      rewrite x, x0.
      destruct (PrimTypeInference.tc2 ufn2 (projT1 s) (projT1 s0)) eqn:?; simpl in Heqr1; inv Heqr1.
      Lemma wt_binop_primsigs:
        forall ufn2 t1 t2 s1,
          PrimTypeInference.tc2 ufn2 t1 t2 = Success s1 ->
          wt_binop ufn2 (arg1Sig (PrimSignatures.Sigma2 s1))
                   (arg2Sig (PrimSignatures.Sigma2 s1))
                  (retSig (PrimSignatures.Sigma2 s1)).
      Proof.
        intros ufn2 t1 t2 s1 PTI.
        destruct ufn2; simpl in *;
          unfold opt_bind in PTI;
          repeat destr_in PTI; inv PTI; simpl; try now (econstructor; eauto).
        repeat destr_in Heqr; inv Heqr.
        repeat destr_in Heqr0; inv Heqr0.
        rewrite Nat.add_comm.
        econstructor; eauto.
      Qed.
      eapply wt_binop_primsigs; eauto.
    - repeat destr_in H; inv H. simpl.
      econstructor.
      eapply cast_action_eq in Heqr0. destruct Heqr0. subst. rewrite <- x;
                                                               eauto.
    - repeat destr_in H; inv H. simpl.
      eapply cast_action_eq in Heqr2. destruct Heqr2. subst.
      eapply IHua in Heqr1. 2: simpl; lia.
      econstructor. 2: rewrite <- x; eauto.

      unfold assert_argtypes in Heqr0.

      eapply argtypes_ok.
      4: apply Heqr0.
      3: eauto.
      {
        intros; eapply IHua; eauto. simpl.
        cut (size_uaction ua' <= list_sum (map size_uaction args)). lia.
        clear - H. revert ua' args H. induction args; simpl; intros; eauto.
        easy.
        destruct H. subst. lia.
        apply IHargs in H. lia.
      }
      rewrite map_length.
      erewrite <- result_list_map_length; eauto.
    - repeat destr_in H; inv H. simpl. constructor. eapply IHua; eauto.
    - inv H.
  Qed.

  Lemma cast_action'_ok:
    forall {reg_t ext_fn_t: Type}
           (R: reg_t -> type)
           (Sigma: ext_fn_t -> ExternalSignature)
           (sig : tsig var_t) (t1 : type) (a : TypedSyntax.action pos_t var_t fn_name_t R Sigma sig t1)
           (pos : pos_t) (t2 : type) (p: t1 = t2),
      cast_action' R Sigma pos t2 a (BasicError (TypeMismatch t1 t2)) =
      Success (rew [TypedSyntax.action pos_t var_t fn_name_t R Sigma sig] p in a).
  Proof.
    unfold cast_action'.
    intros. subst.
    destruct eq_dec; try congruence. simpl.
    unfold eq_rect_r.
    rewrite eq_dec_rew_type_family. auto.
  Qed.

  Lemma cast_action_ok:
    forall {reg_t ext_fn_t: Type}
           (R: reg_t -> type)
           (Sigma: ext_fn_t -> ExternalSignature)
           sig t1 (a: TypedSyntax.action pos_t var_t fn_name_t R Sigma sig t1) pos t2 (p: t1 = t2),
      cast_action R Sigma pos (sig:=sig) t2 a = Success (rew  [TypedSyntax.action pos_t var_t fn_name_t R Sigma sig] p in a).
  Proof.
    unfold cast_action. intros.
    apply cast_action'_ok.
  Qed.

  Lemma type_action_same_sig:
    forall  {reg_t ext_fn_t} (R: reg_t -> type)
            (Sigma: ext_fn_t -> ExternalSignature)
            pos sig1 sig2 ua s (p: sig1 = sig2),
      type_action R Sigma pos sig1 ua = Success s ->
      type_action R Sigma pos sig2 ua = Success (existT _ (projT1 s) (rew [fun sig => TypedSyntax.action pos_t var_t fn_name_t R Sigma sig (projT1 s)] p in (projT2 s))).
  Proof.
    intros. subst. rewrite H. destruct s. f_equal.
  Qed.


      Lemma argtypes_app':
        forall {reg_t ext_fn_t: Type}
               (R: reg_t -> type)
               (Sigma: ext_fn_t -> ExternalSignature)
               {T} sig p (src: T) nexpected fn_name l1 l2 l3 l4 s1 s2,
          assert_argtypes' R Sigma src nexpected fn_name p l1 l3 = Success s1 ->
          assert_argtypes' R Sigma src nexpected fn_name p l2 l4 = Success s2 ->
          assert_argtypes'
            (sig:=sig)
            (fn_name_t := fn_name_t)
            (pos_t := pos_t)
            (var_t := var_t)
            R Sigma src nexpected fn_name p
            (l1 ++ l2)
            (l3 ++ l4) =
          Success (capp s1 s2).
      Proof.
        induction l1; simpl; intros; eauto.
        - destruct l3; simpl in *; try lia. eauto. inv H.
        - repeat destr_in H; inv H.
          simpl. rewrite Heqr. erewrite IHl1. eauto. eauto. auto.
      Qed.


      Lemma argtypes_ok':
        forall {T reg_t ext_fn_t} R Sigma args sig p (src: T) nexpected fn_name argspec argpos
               (IHua:
                  forall  (ua' : uaction pos_t var_t fn_name_t reg_t ext_fn_t),
                    In ua' args ->
                    forall (sig : tsig var_t) t,
                      wt_action pos_t fn_name_t var_t (R:=R) (Sigma:=Sigma) sig ua' t ->
                      forall p,
                      exists a, type_action R Sigma p sig ua' = Success a /\
                                projT1 a = t
               )
               (SAMELEN: List.length argspec = List.length argpos)
        ,
          Forall2 (wt_action pos_t fn_name_t var_t (R:=R) (Sigma:=Sigma) sig) args (map snd argspec) ->
          exists s s0,
            result_list_map (type_action R Sigma p sig) args = Success s /\
            assert_argtypes' R Sigma src nexpected fn_name p
                             (rev argspec)
                             (rev (combine argpos s)) =
            Success s0.
      Proof.
        induction args; simpl; intros; eauto.
        - inv H. destruct argspec; simpl in *; try congruence.
          destruct argpos; simpl in *; try congruence. eexists; eexists; split; eauto.
        - inv H.
          destruct argspec; simpl in *; try congruence.
          destruct argpos; simpl in *; try congruence. inv H2.
          edestruct (IHua a) as (a01 & TA1 & EQt1). auto. eauto.
          rewrite TA1.
          edestruct IHargs as (s & s0 & RLM & AAT). intros; eapply IHua; eauto. 2: eauto. inv SAMELEN. apply H0.
          rewrite RLM.
          exists (a01 :: s). simpl.
          destruct p0. erewrite argtypes_app'. 2: apply AAT.
          2:{
            simpl. erewrite cast_action_ok. eauto.
            Unshelve. rewrite EQt1; reflexivity.
          }
          eexists; split; eauto.
      Qed.

      Lemma argtypes_ok2':
        forall {T reg_t1 ext_fn_t1 reg_t2 ext_fn_t2}
               (* R1 Sigma1 *)
               R2 Sigma2
               (fR: reg_t1 -> reg_t2) (fSigma: ext_fn_t1 -> ext_fn_t2)
               args sig p (src: T) nexpected fn_name argspec argpos
               (IHua:
                  forall ua' : uaction pos_t var_t fn_name_t reg_t1 ext_fn_t1,
                    In ua' args ->
                    forall (sig : tsig var_t) t,
                      wt_action pos_t fn_name_t var_t (R:=fun r => R2 (fR r)) (Sigma:=fun fn => Sigma2 (fSigma fn)) sig ua' t ->
                      forall p p2,
                      exists a, type_action R2 Sigma2 p sig (Desugaring.desugar_action' p2 fR fSigma ua') = Success a /\
                                projT1 a = t
               )
               (SAMELEN: List.length argspec = List.length argpos)
        ,
          Forall2 (wt_action pos_t fn_name_t var_t (R:=fun r => R2 (fR r)) (Sigma:=fun fn => Sigma2 (fSigma fn)) sig) args (map snd argspec) ->
          forall p2,
          exists s s0,
            result_list_map (type_action R2 Sigma2 p sig) (map (Desugaring.desugar_action' p2 fR fSigma) args) = Success s /\
            assert_argtypes' R2 Sigma2 src nexpected fn_name p
                             (rev argspec)
                             (rev (combine argpos s)) =
            Success s0.
      Proof.
        induction args; simpl; intros; eauto.
        - inv H. destruct argspec; simpl in *; try congruence.
          destruct argpos; simpl in *; try congruence. eexists; eexists; split; eauto.
        - inv H.
          destruct argspec; simpl in *; try congruence.
          destruct argpos; simpl in *; try congruence. inv H2.
          edestruct (IHua a) as (a01 & TA1 & EQt1). auto. eauto.
          rewrite TA1.
          edestruct IHargs as (s & s0 & RLM & AAT). intros; eapply IHua; eauto. 2: eauto. inv SAMELEN. apply H0.
          rewrite RLM.
          exists (a01 :: s). simpl.
          destruct p0. erewrite argtypes_app'. 2: apply AAT.
          2:{
            simpl. erewrite cast_action_ok. eauto.
            Unshelve. rewrite EQt1; reflexivity.
          }
          eexists; split; eauto.
      Qed.

      Lemma Forall2_length:
        forall {A B} (P: A -> B -> Prop) l1 l2,
          Forall2 P l1 l2 -> List.length l1 = List.length l2.
      Proof.
        induction 1; simpl; intros; eauto.
      Qed.

      Lemma uprogn_wt_type:
        forall {reg_t ext_fn_t} (R: reg_t -> type) (Sigma: ext_fn_t -> ExternalSignature)aa sig,
          Forall (fun ua =>
                    forall p,
                    exists a : {tau : type & TypedSyntax.action pos_t var_t fn_name_t R Sigma sig tau},
                      type_action R Sigma p sig ua = Success a /\ projT1 a = unit_t
                 ) aa ->
          forall p,
          exists a : {tau : type & TypedSyntax.action pos_t var_t fn_name_t R Sigma sig tau},
            type_action R Sigma p sig (SyntaxMacros.uprogn aa) =
            Success a /\ projT1 a = unit_t.
      Proof.
        induction 1; simpl; intros; eauto.
        destruct l; simpl in *; eauto.
        edestruct H as (a0 & TA0 & EQt0). rewrite TA0.
        erewrite cast_action_ok.
        edestruct IHForall as (a1 & TA1 & EQt1). rewrite TA1.
        eexists; split; eauto. Unshelve. auto.
      Qed.

      Lemma ustruct_subst_wt:
        forall {reg_t ext_fn_t} (R: reg_t -> type)
               (Sigma: ext_fn_t -> ExternalSignature)
               sg p sig fields,
          Forall (fun '(f,v) =>
                    exists idx,
                      PrimTypeInference.find_field sg f = Success idx /\
                      exists a,
                        type_action R Sigma p sig v = Success a /\ projT1 a = snd(List_nth (struct_fields sg) idx)) fields ->
          forall i ai,
            type_action R Sigma p sig i = Success ai ->
            projT1 ai = struct_t sg ->
            exists a,
              type_action
                (pos_t := pos_t)
                (var_t := var_t)
                (fn_name_t := fn_name_t)
                R Sigma p sig
                (fold_left (fun acc '(f, a0) =>
                              UBinop (PrimUntyped.UStruct2 (PrimUntyped.USubstField f)) acc a0
                           ) fields i) = Success a /\ projT1 a = struct_t sg.
      Proof.
        induction 1; simpl; intros; eauto.
        destruct x.
        decompose [ex and] H; clear H. subst.
        eapply IHForall. simpl. rewrite H1, H5.
        unfold lift_fn2_tc_result.
        setoid_rewrite H2.
        rewrite H4. simpl.
        erewrite cast_action_ok; eauto.
        erewrite cast_action_ok; eauto. simpl. auto.
        Unshelve. auto. unfold field_type; auto.
      Qed.

      Lemma uarray_subst_wt:
        forall {reg_t ext_fn_t} (R: reg_t -> type)
           (Sigma: ext_fn_t -> ExternalSignature) p sig sg elements,
          Forall (fun v =>
                    exists a,
                      type_action R Sigma p sig v = Success a /\ projT1 a = array_type sg) elements ->
          forall pi i ai,
            pi + List.length elements = array_len sg ->
            type_action R Sigma p sig i = Success ai ->
            projT1 ai = array_t sg ->
            exists a,
              type_action
                (pos_t := pos_t)
                (var_t := var_t)
                (fn_name_t := fn_name_t)
                R Sigma p sig
                (snd (fold_left (fun '(pos, acc) a0 =>
                                   (S pos,
                                    UBinop (PrimUntyped.UArray2 (PrimUntyped.USubstElement pos)) acc a0)
                                ) elements (pi, i))) = Success a /\ projT1 a = array_t sg.
      Proof.
        induction 1; simpl; intros; eauto.
        decompose [ex and] H; clear H.
        edestruct (@index_of_nat_bounded (array_len sg) pi) as (idx & IDXEQ). lia.
        eapply IHForall. lia. simpl. rewrite H2, H5.
        unfold lift_fn2_tc_result.
        setoid_rewrite H3.
        unfold PrimTypeInference.check_index.
        rewrite IDXEQ. simpl.
        erewrite cast_action_ok; eauto.
        erewrite cast_action_ok; eauto. simpl. auto.
        Unshelve. auto. auto.
      Qed.



  Lemma wt_action_type:
    forall  {reg_t ext_fn_t} (R: reg_t -> type)
            (Sigma: ext_fn_t -> ExternalSignature)
            {reg_t' ext_fn_t': Type}
           ua sig t
           (fR: reg_t' -> reg_t) (fSigma: ext_fn_t' -> ext_fn_t),
      wt_action pos_t fn_name_t var_t (R:=fun r => R (fR r)) (Sigma:=fun fn => Sigma (fSigma fn)) sig ua t ->
      forall p p2 ,
      exists a,
        type_action R Sigma p sig (Desugaring.desugar_action' p2 fR fSigma ua) = Success a /\
        projT1 a = t.
  Proof.
    intros reg_t ext_fn_t R Sigma reg_t' ext_fn_t' ua.
    remember (size_uaction ua).
    revert reg_t' ext_fn_t' ua Heqn.
    pattern n.
    eapply Nat.strong_right_induction with (z:=0).
    { red. red. intros. subst. tauto. } 2: lia.
    intros n0 _ Plt reg_t' ext_fn_t' ua Heqn. subst.
    assert (Plt':
              forall {reg_t' ext_fn_t': Type}
                     (ua': Syntax.uaction pos_t var_t fn_name_t reg_t' ext_fn_t'),
                size_uaction ua' < size_uaction ua ->
                forall sig t fR fSigma,
                  wt_action pos_t fn_name_t var_t (R:=fun r => R (fR r)) (Sigma:=fun fn => Sigma (fSigma fn)) sig ua' t ->
                  forall p p2,
                  exists a,
                    type_action R Sigma p sig (Desugaring.desugar_action' p2 fR fSigma ua') = Success a /\
                    projT1 a = t
           ).
    { intros. eapply Plt. 3: reflexivity. lia. auto. eauto. } clear Plt.
    rename Plt' into IHua. clear n.
    Ltac autofold :=
      repeat match goal with
             | |- context [(Desugaring.desugar_action' ?p2 ?fR ?fSigma ?a)] =>
               fold (@Desugaring.desugar_action pos_t var_t fn_name_t _ _ p2 a)
             | |- context [?f ?rt ?efnt ?p2 ?fR ?fSigma ?a] =>
               fold (@Desugaring.desugar_action' pos_t var_t fn_name_t _ _  rt efnt p2 fR fSigma a)
             end.
    intros sig t fR fSigma WT. inv WT; simpl; intros; autofold;  eauto.
    - inv H. rewrite H0; simpl. eexists; split; eauto.
    - inv H0. rewrite H1; simpl.
      edestruct (IHua _ _ a) as (a0 & TA & EQt). simpl; lia. eauto.
      rewrite TA. erewrite cast_action_ok.
      eexists; split; eauto.
      Unshelve. eauto.
    - edestruct (IHua _ _ a1) as (a01 & TA1 & EQt1). simpl; lia. eauto.
      edestruct (IHua _ _ a2) as (a02 & TA2 & EQt2). simpl; lia. eauto.
      rewrite TA1, TA2. erewrite cast_action_ok.
      Unshelve. 2: eauto.
      eexists; split; eauto.
    - edestruct (IHua _ _ a1) as (a01 & TA1 & EQt1). simpl; lia. eauto.
      edestruct (IHua _ _ a2) as (a02 & TA2 & EQt2). simpl; lia. eauto.
      rewrite TA1.
      erewrite type_action_same_sig. 2: apply TA2.
      Unshelve. 2: rewrite EQt1; eauto. simpl. eexists; split; eauto.
    - edestruct (IHua _ _ cond) as (a01 & TA1 & EQt1). simpl; lia. eauto.
      edestruct (IHua _ _ athen) as (a02 & TA2 & EQt2). simpl; lia. eauto.
      edestruct (IHua _ _ aelse) as (a03 & TA3 & EQt3). simpl; lia. eauto.
      rewrite TA1, TA2, TA3.
      erewrite cast_action_ok. Unshelve. 2: eauto.
      erewrite cast_action_ok. Unshelve. 2: congruence.
      eexists; split; eauto.
    - edestruct (IHua _ _ v) as (a01 & TA1 & EQt1). simpl; lia. eauto.
      rewrite TA1.
      erewrite cast_action_ok. Unshelve. 2: eauto.
      eexists; split; eauto.
    - edestruct (IHua _ _ arg) as (a01 & TA1 & EQt1). simpl; lia. eauto.
      rewrite TA1.
      unfold lift_fn1_tc_result. simpl.
      setoid_rewrite EQt1.
      inv H; simpl;       try erewrite cast_action_ok; try now (eexists; split; eauto).
      + rewrite H1. simpl. erewrite cast_action_ok; try now (eexists; split; eauto).
      + rewrite H1. simpl. erewrite cast_action_ok; try now (eexists; split; eauto).
      + rewrite H1. simpl. erewrite cast_action_ok; try now (eexists; split; eauto).
      + rewrite H1. simpl. erewrite cast_action_ok; try now (eexists; split; eauto).
        Unshelve. all: auto. rewrite <- H3. destruct sg; simpl. f_equal. f_equal. simpl in *. auto.
    - edestruct (IHua _ _ arg1) as (a01 & TA1 & EQt1). simpl; lia. eauto.
      edestruct (IHua _ _ arg2) as (a02 & TA2 & EQt2).  simpl; lia. eauto.
      rewrite TA1, TA2.
      fold (@desugar_action' pos_t var_t fn_name_t reg_t ext_fn_t reg_t' ext_fn_t').
      unfold lift_fn2_tc_result. setoid_rewrite EQt1. setoid_rewrite EQt2.
      inv H; simpl; repeat erewrite cast_action_ok; try now (eexists; split; eauto).
      + eexists; split; eauto.  simpl. f_equal. lia.
      + rewrite H2. simpl.
        repeat erewrite cast_action_ok; try now (eexists; split; eauto).
      + rewrite H2. simpl.
        repeat erewrite cast_action_ok; try now (eexists; split; eauto).
      + rewrite H2. simpl.
        repeat erewrite cast_action_ok; try now (eexists; split; eauto).
      + rewrite H2. simpl.
        repeat erewrite cast_action_ok; try now (eexists; split; eauto).
      Unshelve. all: auto.
    - edestruct (IHua _ _ a) as (a01 & TA1 & EQt1). simpl; lia. eauto.
      rewrite TA1.
      erewrite cast_action_ok.
      eexists; split; eauto.
      Unshelve. auto.
    - edestruct (IHua _ _ (int_body fn)) as (a01 & TA1 & EQt1). simpl; lia. eauto.
      rewrite TA1.
      erewrite cast_action_ok.
      autofold.
      fold (Desugaring.desugar_action'
              (var_t:=var_t)
              (fn_name_t := fn_name_t)
              (reg_t := reg_t)
              (ext_fn_t := ext_fn_t)
              p2 fR fSigma).

      unfold assert_argtypes.
      edestruct (@argtypes_ok2') with (args:=args) as (s & s0 & RLM & AAT).
      { intros; eapply IHua. clear - H1.
        revert ua' H1. induction args; simpl; intros; eauto. easy. destruct H1; subst; eauto.
        lia. apply IHargs in H. simpl in H. lia. eauto.
      }
      2: eauto.
      2: rewrite RLM, AAT.
      rewrite map_length.
      apply Forall2_length in H. rewrite map_length. rewrite H. rewrite map_length. auto.
      eexists; split; eauto.
      Unshelve. auto.
    - edestruct (IHua _ _ e) as (a01 & TA1 & EQt1). simpl; lia. eauto.
      rewrite TA1.
      eexists; split; eauto.
    - cbn. rewrite H. simpl. eexists; split; eauto.
    - change (Desugaring.desugar_action' p2 fR fSigma (USugar (UProgn aa)))
        with (SyntaxMacros.uprogn (map (Desugaring.desugar_action' p2 fR fSigma) aa)).
      cbn.
      apply uprogn_wt_type.
      rewrite Forall_forall; intros.
      rewrite in_map_iff in H0. destruct H0 as (x0 & DES & IN). subst.
      generalize (H _ IN); intro HH.
      eapply IHua in HH. eauto. simpl.
      clear - IN.
      revert IN. induction aa; simpl; intros; eauto. easy.
      destruct IN; subst. lia. apply IHaa in H. lia.
    - change (Desugaring.desugar_action' p2 fR fSigma (USugar (ULet bindings body)))
        with (fold_right
                (fun '(var, a) (acc : uaction pos_t var_t fn_name_t reg_t ext_fn_t) => UBind var (Desugaring.desugar_action' p2 fR fSigma a) acc)
                (Desugaring.desugar_action' p2 fR fSigma body) bindings).
      assert(IHua':
               forall ua' : uaction pos_t var_t fn_name_t reg_t' ext_fn_t',
                 In ua' (map snd bindings) \/ ua' = body ->
                 forall (sig : tsig var_t) (t : type),
                   wt_action pos_t fn_name_t var_t (R:=fun r => R (fR r)) (Sigma:= fun fn => Sigma (fSigma fn)) sig ua' t ->
                   forall p p2 : pos_t,
                   exists a : {tau : type & TypedSyntax.action pos_t var_t fn_name_t R Sigma sig tau},
                     type_action R Sigma p sig (Desugaring.desugar_action' p2 fR fSigma ua') = Success a /\ projT1 a = t
            ).
      {
        intros; eapply IHua. simpl.
        destruct H2; subst; try lia.
        clear - H2. revert H2; induction bindings; simpl; intros; eauto.
        easy.
        destruct a, H2; subst; eauto; simpl; try lia.
        apply IHbindings in H; lia. auto.
      }
      clear IHua.
      revert bindings body bind_taus sig sig' t H H0 H1 IHua' p p2.
      induction bindings.
      + simpl. intros. eapply IHua'. auto. inv H0. simpl in H1; auto.
      + simpl; intros.
        inv H. inv H0. simpl in *.
        edestruct (IHua' a0) as (aa0 & TA0 & TEQ0). auto. eauto.
        rewrite TA0. subst.
        edestruct (IHbindings) as (aa1 & TA1 & TEQ1). eauto. eauto.
        rewrite <- app_assoc in H1. simpl in H1; eauto.
        intros; eapply IHua'; eauto. destruct H; auto.
        rewrite TA1. eexists; split; eauto.
    - edestruct (IHua _ _ cond) as (a01 & TA1 & EQt1). simpl; lia. eauto.
      edestruct (IHua _ _ body) as (a02 & TA2 & EQt2). simpl; lia. eauto.
      rewrite TA1, TA2.
      erewrite cast_action_ok. Unshelve. 2: eauto.
      erewrite cast_action_ok. Unshelve. 2: congruence.
      eexists; split; eauto.
    - assert(IHbranches_case:
               forall ua' : uaction pos_t var_t fn_name_t reg_t' ext_fn_t',
                 In ua' (map fst branches) ->
                 forall p p2 : pos_t,
                 exists a : {tau' : type & TypedSyntax.action pos_t var_t fn_name_t R Sigma sig tau'},
                   type_action R Sigma p sig (Desugaring.desugar_action' p2 fR fSigma ua') = Success a /\ projT1 a = tau
            ).
      {
        intros; eapply IHua; simpl; auto.
        clear - H2. revert H2; induction branches; simpl; intros; eauto.
        intuition easy.
        destruct a; simpl in *.
        destruct H2 as [H2|H2]; subst; eauto; simpl; try lia.
        apply IHbranches in H2. lia.
        rewrite Forall_forall in H1.
        rewrite in_map_iff in H2. decompose [ex and] H2. subst.
        apply H1 in H5. tauto.
      }
      assert(IHbranches_val:
               forall ua' : uaction pos_t var_t fn_name_t reg_t' ext_fn_t',
                 In ua' (map snd branches) ->
                 forall p p2 : pos_t,
                 exists a : {tau' : type & TypedSyntax.action pos_t var_t fn_name_t R Sigma sig tau'},
                   type_action R Sigma p sig (Desugaring.desugar_action' p2 fR fSigma ua') = Success a /\ projT1 a = t
            ).
      {
        intros; eapply IHua; simpl; auto.
        clear - H2. revert H2; induction branches; simpl; intros; eauto.
        intuition easy.
        destruct a; simpl in *.
        destruct H2 as [H2|H2]; subst; eauto; simpl; try lia.
        apply IHbranches in H2. lia.
        rewrite Forall_forall in H1.
        rewrite in_map_iff in H2. decompose [ex and] H2. subst.
        apply H1 in H5. tauto.
      }
      change (Desugaring.desugar_action' p2 fR fSigma (USugar (USwitch var default branches))) with
          (SyntaxMacros.uswitch
             (Desugaring.desugar_action' p2 fR fSigma var)
             (Desugaring.desugar_action' p2 fR fSigma default)
             (map (fun '(cond, body) =>
                     (Desugaring.desugar_action' p2 fR fSigma cond,
                      Desugaring.desugar_action' p2 fR fSigma body)
                  ) branches)
          ).
      edestruct (IHua _ _ var) with (p:=p) (p2:=p2) as (a0 & TA0 & Teq0). simpl; lia. eauto.
      edestruct (IHua _ _ default) with (p:=p) (p2:=p2) as (a1 & TA1 & Teq1). simpl; lia. eauto.
      subst.
      revert IHbranches_case IHbranches_val TA0 TA1. clear.
      revert a0 a1.
      induction branches; simpl; intros; eauto.
      destruct a. simpl in *.
      rewrite TA0.
      edestruct (IHbranches_val _ (or_introl eq_refl)) as (a2 & TA2 & Teq2).
      edestruct (IHbranches_case _ (or_introl eq_refl)) as (a3 & TA3 & Teq3).
      rewrite TA2, TA3.
      erewrite cast_action_ok.
      erewrite cast_action_ok.
      simpl.
      edestruct IHbranches as (a4 & TA4 & Teq4).
      intros; eapply IHbranches_case; eauto.
      intros; eapply IHbranches_val; eauto. eauto. eauto.
      rewrite TA4.
      erewrite cast_action_ok. eexists; split; eauto.
      Unshelve. auto. auto. congruence.
    - change (Desugaring.desugar_action' _ _ _ _)
        with (SyntaxMacros.ustruct_init sg (map (fun '(f,a) => (f, Desugaring.desugar_action' p2 fR fSigma a)) fields)).
      assert(IHfields:
               Forall (fun '(f, ua') =>
                         exists idx,
                           PrimTypeInference.find_field sg f = Success idx /\
                           exists a : {tau' : type & TypedSyntax.action pos_t var_t fn_name_t R Sigma sig tau'},
                             type_action R Sigma p sig (Desugaring.desugar_action' p2 fR fSigma ua') = Success a /\ projT1 a = snd (List_nth (struct_fields sg) idx)
                      ) fields).
      {
        rewrite Forall_forall; intros. destruct x.
        generalize H0; intro IN.
        rewrite Forall_forall in H. apply H in H0.
        destruct H0 as (idx & FF & WT). simpl in *.
        eexists; split; eauto.
        eapply IHua; simpl; auto.
        clear - IN. revert IN; induction fields; simpl; intros; eauto.
        easy.
        destruct a; simpl in *.
        destruct IN as [H2|H2].
        inv H2. lia.
        apply IHfields in H2. lia.
      }
      clear IHua H.
      unfold SyntaxMacros.ustruct_init.
      eapply ustruct_subst_wt.
      rewrite Forall_forall; intros x IN.
      rewrite in_map_iff in IN. decompose [ex and] IN. clear IN. destruct x0. subst. simpl in *.
      rewrite Forall_forall in IHfields.
      apply IHfields in H1. destruct H1 as (idx & FF & IH).
      eexists; split; eauto.
      simpl. erewrite cast_action_ok; eauto. simpl. auto.
      Unshelve. auto.
    - change (Desugaring.desugar_action' _ _ _ _)
        with (
            let sg := {| array_type := tau; array_len := Datatypes.length elements |} in
            let usubst := fun pos0 : nat => UBinop (PrimUntyped.UArray2 (PrimUntyped.USubstElement pos0)) in
            let empty := SyntaxMacros.uinit (array_t sg) in
            snd
              (fold_left
                 (fun '(pos0, acc) (a : uaction pos_t var_t fn_name_t reg_t' ext_fn_t') =>
                    (S pos0, usubst pos0 acc (Desugaring.desugar_action' p2 fR fSigma a))) elements (0, empty))
          ).
      assert(IHelements:
               Forall (fun v =>
                         exists a : {tau' : type & TypedSyntax.action pos_t var_t fn_name_t R Sigma sig tau'},
                           type_action R Sigma p sig (Desugaring.desugar_action' p2 fR fSigma v) = Success a /\ projT1 a = tau
                      ) elements).
      {
        rewrite Forall_forall; intros.
        eapply IHua; eauto.
        rename H0 into IN.
        clear - IN. revert IN; induction elements; simpl; intros; eauto.
        easy.
        destruct IN as [H2|H2].
        inv H2. lia.
        apply IHelements in H2. simpl in H2. lia.
        rewrite Forall_forall in H; eapply H; eauto.
      }
      clear IHua H. simpl.
      replace (fold_left
                 (fun '(pos0, acc) (a0 : uaction pos_t var_t fn_name_t reg_t' ext_fn_t') =>
                    (S pos0,
                     UBinop (PrimUntyped.UArray2 (PrimUntyped.USubstElement pos0)) acc
                            (Desugaring.desugar_action' p2 fR fSigma a0))) elements
                 (0,
                  SyntaxMacros.uinit
                    (array_t {| array_type := tau; array_len := Datatypes.length elements |})))
        with
          (fold_left
             (fun '(pos0, acc) (a0 : uaction pos_t var_t fn_name_t reg_t ext_fn_t) =>
                (S pos0,
                 UBinop (PrimUntyped.UArray2 (PrimUntyped.USubstElement pos0)) acc
                        a0)) (map (Desugaring.desugar_action' p2 fR fSigma) elements)
             (0,
              SyntaxMacros.uinit
                (array_t {| array_type := tau; array_len := Datatypes.length elements |}))).
      2: {
        generalize (0,
                    SyntaxMacros.uinit (pos_t:=pos_t)
                                       (var_t := var_t)
                                       (fn_name_t := fn_name_t)
                                       (reg_t:=reg_t)
                                       (ext_fn_t:=ext_fn_t)
                                       (array_t {| array_type := tau; array_len := Datatypes.length elements |})).
        clear.
        induction elements; simpl; intros; eauto.
        destruct p; simpl.
        rewrite IHelements. reflexivity.
      }
      edestruct @uarray_subst_wt with
          (elements:=map (Desugaring.desugar_action' p2 fR fSigma) elements) as (aa & TA & Teq).
      5: rewrite TA; eexists; split; eauto. all: simpl.
      rewrite Forall_forall; intros x IN; rewrite in_map_iff in IN; decompose [ex and] IN; clear IN.
      rewrite Forall_forall in IHelements; apply IHelements in H1; eauto. subst. auto.
      rewrite map_length; auto.
      erewrite cast_action_ok; eauto. simpl. auto.
      Unshelve. auto.
    - fold (Desugaring.desugar_action'
              (pos_t :=pos_t)
              (var_t := var_t)
              (fn_name_t := fn_name_t)
              p2 fR fSigma).
      fold (Desugaring.desugar_action'
              (pos_t :=pos_t)
              (var_t := var_t)
              (fn_name_t := fn_name_t)
              p2 (fun r=> fR (fR0 r)) (fun fn => fSigma (fSigma0 fn))).
      edestruct @argtypes_ok2' as (s & s0 & RLM & AARGS). 3: apply H.
      {
        simpl; intros; eapply IHua; eauto.
        simpl.
        clear - H1. revert H1.
        induction args; simpl; intros; eauto. easy.
        destruct H1. subst; lia.
        apply IHargs in H; lia.
      }
      2:{
        rewrite RLM.
        unfold assert_argtypes. rewrite AARGS.
        edestruct (IHua _ _ (int_body fn)) as (abody & TAbody & TEQbody). simpl; lia. apply H0.
        rewrite TAbody.
        erewrite cast_action_ok. eexists; split; eauto.
        Unshelve. auto.
      }
      apply Forall2_length in H.
      repeat (rewrite ?map_length, ?H). auto.
  Qed.

  Lemma type_desugared_action_wt:
    forall {reg_t ext_fn_t} (R: reg_t -> type)
           (Sigma: ext_fn_t -> ExternalSignature)
           ua tau sig a ta pos,
      desugar_action pos ua = ta ->
      type_action R Sigma tau sig ta = Success a ->
      wt_action pos_t fn_name_t var_t (R:=R) (Sigma:=Sigma) sig ta (projT1 a).
  Proof.
    intros reg_t ext_fn_t R Sigma ua tau sig a ta pos H.
    eapply type_action_wt.
  Qed.

  Definition wt_renv {reg_t:Type} (R: reg_t -> type) (REnv: Env reg_t) ctx :=
    forall x,
      wt_val (R x) (getenv REnv ctx x).

  Definition wt_log {reg_t:Type} (R: reg_t -> type) (REnv: Env reg_t) (l: UntypedSemantics.Log REnv) :=
    forall idx le,
      In le (getenv REnv l idx) ->
      kind le = Logs.LogWrite ->
      wt_val (R idx) (UntypedLogs.val le).

  Inductive wt_env : tsig var_t -> list (var_t * val) -> Prop :=
  | wt_env_nil: wt_env [] []
  | wt_env_cons:
      forall sig ctx t x v,
        wt_env sig ctx ->
        wt_val t x ->
        wt_env ((v,t)::sig) ((v,x)::ctx).

  (* Variable sigma: ext_fn_t -> val -> val. *)
  (* Hypothesis sigma_wt: forall fn v, wt_val (arg1Sig (Sigma fn)) v -> *)
  (*                                   wt_val (retSig (Sigma fn)) (sigma fn v). *)

  (* Variable REnv: Env reg_t. *)
  (* Variable r: env_t REnv (fun _ => val). *)



  Ltac trim H :=
    match type of H with
    | ?a -> ?b =>
      let x := fresh "H" in
      assert(x: a);[|specialize(H x); clear x]
    end.

  Lemma wt_var_determ:
    forall sig v t1 t2,
      wt_var var_t sig v t1 ->
      wt_var var_t sig v t2 ->
      t1 = t2.
  Proof.
    intros sig v t1 t2 H H0. inv H; inv H0. congruence.
  Qed.

  Ltac iinv A :=
    inv A;
    repeat match goal with
             H: existT _ _ _ = existT _ _ _ |- _ =>
             apply Eqdep.EqdepTheory.inj_pair2 in H; try subst
           end.


  Lemma wt_env_list_assoc:
    forall sig ctx,
      wt_env sig ctx ->
      forall var v t,
        list_assoc ctx var = Some v ->
        wt_var var_t sig var t ->
        wt_val t v.
  Proof.
    intros sig ctx WTE var v t LA WTV.
    inv WTV.
    revert var v LA tm H.
    induction WTE; simpl; intros; eauto. congruence.
    destr_in H0; subst.
    - inv LA.
      unfold eq_rect_r in H0. rewrite eq_dec_rew_type_family in H0. inv H0. simpl. auto.
    - repeat destr_in H0; inv H0. simpl.
      eapply IHWTE in LA. 2: eauto. simpl in LA. auto.
  Qed.

  Lemma wt_env_set:
    forall sig k t0 Gamma v0,
      wt_var var_t sig k t0 ->
      wt_env sig Gamma ->
      wt_val t0 v0 ->
      wt_env sig (list_assoc_set Gamma k v0).
  Proof.
    intros sig k t0 Gamma v0 WTV WTE WTv.
    inv WTV. revert v0 tm WTv H.
    induction WTE; simpl; intros; eauto. easy.
    repeat destr_in H0; inv H0.
    + unfold eq_rect_r in H2. rewrite eq_dec_rew_type_family in H2. inv H2.
      simpl in *. constructor; auto.
    + simpl in *. constructor; eauto. eapply IHWTE; eauto. simpl; auto.
  Qed.

  Lemma list_find_op_spec:
    forall {A B} (f: A -> option B) l v,
      list_find_opt f l = Some v ->
      exists x, In x l /\ f x = Some v.
  Proof.
    induction l; simpl; intros; eauto. easy.
    destr_in H. inv H. exists a; split; eauto.
    edestruct IHl as (xx & IN & SOME); eauto.
  Qed.
  Lemma log_find_wt:
    forall {T reg_t} R (REnv: Env reg_t) l idx f v,
      log_find (T:=T) l idx f = Some v ->
      forall (FF: forall x y, f x = Some y -> kind x = Logs.LogWrite),
        wt_log R REnv l ->
        exists x,
          f x = Some v /\
          wt_val (R idx) (UntypedLogs.val x).
  Proof.
    intros.
    red in H0.
    unfold log_find in H.
    edestruct @list_find_op_spec as (x & F & IN). eauto.
    generalize IN; intro IN'.
    apply FF in IN.
    apply H0 in F; auto.
    eauto.
  Qed.

  Lemma wt_log_app:
    forall {reg_t} (R: reg_t -> type) REnv l1 l2,
      wt_log R REnv l1 ->
      wt_log R REnv l2 ->
      wt_log R REnv (log_app l1 l2).
  Proof.
    unfold wt_log. intros.
    revert H1.
    unfold log_app.
    rewrite getenv_map2. rewrite in_app_iff. intros [?|?]; eauto.
  Qed.

  (* Instance reg_eq : EqDec reg_t. *)
  (* Proof. *)
  (*   eapply EqDec_FiniteType. Unshelve. *)
  (*   apply finite_keys. auto. *)
  (* Qed. *)

  Instance eq_dec_env {A: Type} `{Env A} : EqDec A.
  Proof.
    destruct Env0. apply EqDec_FiniteType.
  Defined.

  Lemma wt_log_cons:
    forall {reg_t} (R: reg_t -> type) REnv l1 le idx,
      wt_log R REnv l1 ->
      (kind le = Logs.LogWrite -> wt_val (R idx) (UntypedLogs.val le)) ->
      wt_log R REnv (log_cons idx le l1).
  Proof.
    unfold wt_log. intros.
    revert H1.
    unfold log_cons.
    destruct (@eq_dec _ (@eq_dec_env _ REnv) idx idx0); subst.
    rewrite get_put_eq. simpl; intros; eauto. destruct H1; subst; simpl in *. eauto. eauto.
    rewrite get_put_neq. eauto. auto.
  Qed.


  Fixpoint typsz (t: type) : nat :=
    match t with
    | bits_t sz => 1
    | enum_t sg => 1
    | struct_t sg => 1 + list_sum (map (fun '(_,t) => typsz t) (struct_fields sg))
    | array_t sg => 1 + typsz (array_type sg)
    end.

  Lemma type_ind' :
    forall (P: type -> Prop)
           (Pb: forall sz, P (bits_t sz))
           (Pe: forall sg, P (enum_t sg))
           (Ps: forall sg (IH: forall v t, In (v, t) (struct_fields sg) -> P t),
               P (struct_t sg)
           )
           (Pa: forall sg (IH: P (array_type sg)),
               P (array_t sg)
           ),
    forall t, P t.
  Proof.
    intros P Pb Pe Ps Pa t.
    eapply (strong_ind_type (fun n => forall t, typsz t = n -> P t)).
    3: reflexivity. 2: reflexivity.
    intros. subst.
    assert (IH: forall t, typsz t < typsz t0 -> P t).
    {
      intros; eapply H; eauto.
    } clear H.
    destruct t0; auto.
    - apply Ps.
      intros. eapply IH.
      clear - H.
      simpl.
      revert H. generalize (struct_fields sig).
      induction l; simpl; intros; eauto. easy.
      destruct a.
      destruct H; subst; simpl in *; eauto. inv H. lia.
      apply IHl in H. lia.
  Qed.

  Lemma uvalue_of_struct_bits_rew :
    forall fields l,
      (fix uvalue_of_struct_bits (fields : list (string * type)) (bs : list bool) {struct fields} :
         option (list val) :=
         match fields with
         | [] => Some []
         | (_, tau) :: fields0 =>
           match take_drop (Datatypes.length bs - type_sz tau) bs with
           | Some (b0, b1) =>
             match uvalue_of_struct_bits fields0 b0 with
             | Some x0 =>
               match uvalue_of_bits (tau:=tau) b1 with
               | Some x1 => Some (x1 :: x0)
               | None => None
               end
             | None => None
             end
           | None => None
           end
         end) fields l = uvalue_of_struct_bits fields l.
  Proof.
    reflexivity.
  Qed.

  Lemma bits_splitn_inv:
    forall n sz l1 l2,
      bits_splitn n sz l1 = Some l2 ->
      Forall (fun x => List.length x = sz) l2 /\ List.length l2 = n.
  Proof.
    induction n; simpl; intros; eauto. inv H; split; constructor.
    unfold opt_bind in H. repeat destr_in H; inv H.
    edestruct IHn; eauto. subst. simpl.
    split; auto.
    constructor; eauto. eapply take_drop_spec in Heqo. tauto.
  Qed.
  Lemma uvalue_of_list_bits_inv:
    forall (tau : type) (l : list (list bool))
           (l0 : list val)
           (F: Forall (fun x => List.length x = type_sz tau) l)
           ( IH : forall (v1 : list bool) (v : val),
               Datatypes.length v1 = type_sz tau ->
               uvalue_of_bits (tau:=tau) v1 = Some v -> wt_val tau v
           ),
      uvalue_of_list_bits (tau:=tau) l = Some l0 ->
      Forall (fun y => wt_val tau y) l0 /\ List.length l0 = List.length l.
  Proof.
    induction l; simpl; intros; eauto.
    - inv H; split; constructor.
    - unfold opt_bind in H. repeat destr_in H; inv H.
      split.
      constructor; eauto.
      eapply IH; eauto. inv F; eauto.
      inv F. eapply IHl; eauto.
      simpl; auto.
      edestruct IHl; eauto. inv F; auto.
  Qed.

  Lemma uvalue_of_list_bits_app:
    forall tau l1 l2 l1' l2',
      uvalue_of_list_bits (tau:=tau) l1 = Some l1' ->
      uvalue_of_list_bits (tau:=tau) l2 = Some l2' ->
      uvalue_of_list_bits (tau:=tau) (l1 ++ l2) = Some (l1' ++ l2').
  Proof.
    induction l1; simpl; intros; eauto. inv H; auto.
    unfold opt_bind in H. repeat destr_in H; inv H.
    simpl. erewrite IHl1; eauto. simpl. auto.
  Qed.


  Lemma uvalue_of_list_bits_rev:
    forall tau l l',
      uvalue_of_list_bits (tau:=tau) l = Some l' ->
      uvalue_of_list_bits (tau:=tau) (rev l) = Some (rev l').
  Proof.
    induction l; simpl; intros; eauto. inv H; auto.
    unfold opt_bind in H. repeat destr_in H; inv H.
    simpl. eapply uvalue_of_list_bits_app. eauto. simpl. rewrite Heqo. reflexivity.
  Qed.


  Lemma uvalue_of_struct_bits_wt:
    forall fields l v
           (IH : forall (v : string) (t : type),
               In (v, t) fields ->
               forall (v1 : list bool) (v0 : val),
                 Datatypes.length v1 = type_sz t -> uvalue_of_bits (tau:=t) v1 = Some v0 -> wt_val t v0
           )
           (LEN: List.length l = struct_fields_sz fields),
      uvalue_of_struct_bits fields l = Some v ->
      Forall2 wt_val (map snd fields) v.
  Proof.
    induction fields; simpl; intros; eauto. inv H. constructor.
    unfold opt_bind in H. repeat destr_in H; inv H.
    simpl.
    constructor; eauto.
    eapply IH; eauto.
    eapply take_drop_spec in Heqo. intuition. rewrite H2.
    rewrite LEN. unfold struct_fields_sz. simpl. lia.
    eapply IHfields; eauto.
    eapply take_drop_spec in Heqo. intuition. rewrite H1.
    rewrite LEN. unfold struct_fields_sz; simpl. lia.
  Qed.

  Lemma uvalue_of_bits_wt:
    forall tau v1 v,
      List.length v1 = type_sz tau ->
      uvalue_of_bits (tau:=tau) v1 = Some v ->
      wt_val tau v.
  Proof.
    intros tau. pattern tau.
    eapply type_ind'; simpl; intros; eauto.
    - inv H0. constructor. auto.
    - unfold opt_bind in H0; repeat destr_in H0; inv H0.
      constructor; auto.
      eapply take_drop_spec in Heqo; eauto. tauto.
    - unfold opt_bind in H0; repeat destr_in H0; inv H0.
      rewrite uvalue_of_struct_bits_rew in Heqo.
      constructor.
      eapply uvalue_of_struct_bits_wt; eauto.
    - unfold opt_bind in H0; repeat destr_in H0; inv H0.
      rewrite UntypedSemantics.uvalue_of_list_bits_rew in Heqo0.
      apply bits_splitn_inv in Heqo. destruct Heqo.
      apply uvalue_of_list_bits_rev in Heqo0.
      rewrite rev_involutive in Heqo0.
      eapply uvalue_of_list_bits_inv in Heqo0; eauto.
      destruct Heqo0.
      constructor.
      rewrite <- (rev_involutive).
      eapply UntypedSemantics.Forall_rev. auto.
      rewrite <- H1, <- H3, rev_length. auto.
  Qed.

  Lemma wt_val_bits:
    forall n l,
      n = List.length l ->
      wt_val (bits_t n) (Bits l).
  Proof.
    intros; subst; constructor; auto.
  Qed.

  Lemma wt_unop_sigma1:
    forall u ta tr v0 v,
      wt_unop u ta tr ->
      wt_val ta v0 ->
      UntypedSemantics.sigma1 u v0 = Some v ->
      wt_val tr v.
  Proof.
    intros u ta tr v0 v WTU WTv SIG.
    inv WTU; simpl in *.
    - inv SIG; constructor; reflexivity.
    - inv SIG; constructor; reflexivity.
    - inv SIG. constructor.
      apply ubits_of_value_len'. auto.
    - unfold opt_bind in SIG. repeat destr_in SIG; inv SIG.
      inv WTv.
      eapply uvalue_of_bits_wt; eauto.
    - inv SIG; constructor; auto.
    - inv WTv. simpl in *. inv SIG.
      constructor. apply map_length.
    - inv WTv. simpl in *. inv SIG.
      apply wt_val_bits; auto.
      rewrite app_length. rewrite repeat_length. lia.
    - inv WTv. simpl in *. inv SIG.
      apply wt_val_bits; auto.
      rewrite app_length. rewrite repeat_length. lia.
    - inv WTv. simpl in *. inv SIG.
      apply wt_val_bits; auto.
      rewrite app_length. rewrite repeat_length. lia.
    - inv WTv. simpl in *. inv SIG.
      apply wt_val_bits; auto.
      erewrite length_concat_same. rewrite repeat_length. eauto.
      rewrite Forall_forall; intros x IN.
      apply repeat_spec in IN. subst. auto.
    - inv WTv. simpl in *.
      repeat destr_in SIG.
      unfold opt_bind in SIG; repeat destr_in SIG; inv SIG.
      generalize (take_drop'_spec2 _ _ _ _ Heqp).
      generalize (take_drop'_spec2 _ _ _ _ Heqp0).
      generalize (take_drop'_spec _ _ _ _ Heqp).
      generalize (take_drop'_spec _ _ _ _ Heqp0). intuition.
      apply wt_val_bits; auto.
      rewrite app_length.
      rewrite repeat_length. lia.
    - inv WTv. simpl in *.
      unfold PrimTypeInference.find_field in H. unfold opt_result in H.
      destr_in H; inv H.
      revert H1 SIG Heqo. unfold field_type.
      revert idx. clear. generalize (struct_fields sg).
      intro l; revert lv.
      induction l. simpl. easy.
      intros. Opaque eq_dec. simpl in *.
      repeat destr_in Heqo; inv Heqo.
      + repeat destr_in SIG; inv SIG. inv H1. simpl; auto.
        simpl in n. congruence.
      + repeat destr_in SIG; inv SIG. simpl in n; congruence.
        eapply IHl; eauto.
        inv H1. simpl; auto.
    - inv WTv. simpl in *.
      unfold PrimTypeInference.find_field in H. unfold opt_result in H.
      destr_in H; inv H.
      revert H1 SIG Heqo. unfold field_sz, field_type.
      intros. unfold opt_bind in SIG.
      repeat destr_in SIG; inv SIG.
      apply wt_val_bits; auto.
      generalize (take_drop'_spec2 _ _ _ _ Heqp1).
      generalize (take_drop'_spec2 _ _ _ _ Heqp2).
      generalize (take_drop'_spec _ _ _ _ Heqp1).
      generalize (take_drop'_spec _ _ _ _ Heqp2). intuition.
      rewrite app_length, repeat_length, H7, H10, H8, H1.
      clear H H4 H0 H7 H2 H8 H3 H9 H5 H10 Heqp1 Heqp2.
      unfold struct_sz. simpl. transitivity n0. 2: lia.
      revert idx Heqo Heqo0. generalize (struct_fields sg). clear.
      induction l; simpl; intros; eauto. easy.
      repeat destr_in Heqo; inv Heqo.
      + repeat destr_in Heqo0; inv Heqo0; simpl in *. reflexivity.
        congruence.
      + repeat destr_in Heqo0; inv Heqo0; simpl in *. congruence. eauto.
    - inv WTv.
      rewrite Forall_forall in H1. apply H1.
      eapply nth_error_In; eauto.
    - inv WTv. simpl in *.
      unfold opt_bind in SIG.
      repeat destr_in SIG; inv SIG.
      eapply wt_val_bits; eauto.
      generalize (take_drop'_spec2 _ _ _ _ Heqp).
      generalize (take_drop'_spec2 _ _ _ _ Heqp0).
      generalize (take_drop'_spec _ _ _ _ Heqp).
      generalize (take_drop'_spec _ _ _ _ Heqp0). intuition.
      rewrite app_length, repeat_length. lia.
  Qed.


  Lemma bitwise_length:
    forall f a b,
      List.length a = List.length b ->
      List.length (bitwise f a b) = List.length a.
  Proof.
    induction a; simpl; intros; eauto.
    - destruct b; simpl in *; try congruence.
    - destruct b; simpl in *; try congruence.
      erewrite IHa; eauto.
  Qed.

  Lemma wt_binop_sigma1:
    forall u ta tb tr v0 v1 v,
      wt_binop u ta tb tr ->
      wt_val ta v0 ->
      wt_val tb v1 ->
      UntypedSemantics.sigma2 u v0 v1 = Some v ->
      wt_val tr v.
  Proof.
    intros u ta tb tr v0 b1 v WTB WTv1 WTv2 SIG.
    inv WTB; simpl in *.
    - destruct neg; inv SIG; constructor; auto.
    - repeat destr_in SIG; inv SIG. apply wt_val_bits; auto.
      inv WTv1. inv WTv2.
      erewrite bitwise_length; eauto.
    - repeat destr_in SIG; inv SIG. apply wt_val_bits; auto.
      inv WTv1. inv WTv2.
      erewrite bitwise_length; eauto.
    - repeat destr_in SIG; inv SIG. apply wt_val_bits; auto.
      inv WTv1. inv WTv2.
      erewrite bitwise_length; eauto.
    - inv WTv1. inv WTv2. inv SIG. apply wt_val_bits; auto.
      Lemma iter_length:
        forall {A} n (f: list A -> list A) (l: list A) len,
          List.length l = len ->
          (forall l, List.length l = len -> List.length (f l) = len) ->
          List.length (Nat.iter n f l) = List.length l.
      Proof.
        induction n; simpl; intros; eauto.
        rewrite H0; eauto. erewrite IHn; eauto.
      Qed.
      erewrite iter_length. auto. eauto. intros.
      rewrite <- H.
      Transparent eq_dec. destruct l. simpl; auto.
      Opaque removelast. simpl. f_equal.
      Lemma removelast_length: forall {A} (l: list A), List.length (removelast l) = List.length l - 1.
      Proof.
        Transparent removelast.
        induction l; simpl; intros; eauto.
        destruct l. reflexivity. Opaque removelast.
        simpl. rewrite IHl. simpl. lia.
      Qed.
      rewrite removelast_length. simpl. lia.
    - inv WTv1. inv WTv2. inv SIG. apply wt_val_bits; auto.
      erewrite iter_length. auto. eauto. intros.
      rewrite <- H.
      destruct l. simpl; auto.
      simpl. rewrite app_length; simpl. lia.
    - inv WTv1. inv WTv2. inv SIG. apply wt_val_bits; auto.
      erewrite iter_length. auto. eauto. intros.
      rewrite <- H.
      destruct l; simpl; auto.
      rewrite app_length; simpl. lia.
    - inv WTv1. inv WTv2. inv SIG. apply wt_val_bits; auto.
      rewrite app_length; simpl. lia.
    - inv WTv1. inv WTv2. inv SIG. apply wt_val_bits; auto.
    - inv WTv1. inv WTv2. inv SIG. apply wt_val_bits; auto.
      destr. destr. unfold fst. destr.
      generalize (take_drop'_spec _ _ _ _ Heqp).
      generalize (take_drop'_spec _ _ _ _ Heqp0).
      generalize (take_drop'_spec _ _ _ _ Heqp1).
      generalize (take_drop'_spec2 _ _ _ _ Heqp).
      generalize (take_drop'_spec2 _ _ _ _ Heqp0).
      generalize (take_drop'_spec2 _ _ _ _ Heqp1). intuition.
      rewrite H6. rewrite ! app_length.
      rewrite H13. lia.
    - inv WTv1. inv WTv2. inv SIG. apply wt_val_bits; auto.
      destr. destr.
      generalize (take_drop'_spec _ _ _ _ Heqp).
      generalize (take_drop'_spec _ _ _ _ Heqp0).
      generalize (take_drop'_spec2 _ _ _ _ Heqp).
      generalize (take_drop'_spec2 _ _ _ _ Heqp0).
      intuition.
      rewrite app_length, repeat_length. lia.
    - inv WTv1. inv WTv2. inv SIG. apply wt_val_bits; auto.
      rewrite vect_to_list_length. auto.
    - inv WTv1. inv WTv2. inv SIG. apply wt_val_bits; auto.
      rewrite vect_to_list_length. auto.
    - inv WTv1. inv WTv2. inv SIG. apply wt_val_bits; auto.
      rewrite vect_to_list_length. auto.
    - inv WTv1. inv WTv2. destruct eq_dec; try congruence. inv SIG. apply wt_val_bits; auto.
    - inv WTv1.
      unfold opt_bind in SIG. repeat destr_in SIG; inv SIG. constructor. auto.
      unfold PrimTypeInference.find_field in H.
      unfold opt_result in H. destr_in H; inv H.
      revert Heqo Heqo0 H1.
      destruct sg. simpl in *.
      revert idx WTv2. unfold field_type. simpl.
      Opaque eq_dec.
      revert lv l.
      induction struct_fields; simpl; intros; eauto.
      inv Heqo0.
      repeat destr_in Heqo; inv Heqo. simpl in *.
      rewrite Heqs0 in Heqo0. inv Heqo0. inv H1; constructor; eauto.
      simpl in *.
      rewrite Heqs0 in Heqo0. inv Heqo0.
      unfold opt_bind in H0. destr_in H0; inv H0.
      destr_in H2; inv H2. inv H1; constructor; eauto.
    - inv WTv1. inv WTv2.
      unfold opt_bind in SIG. repeat destr_in SIG; inv SIG. apply wt_val_bits; auto.
      unfold PrimTypeInference.find_field in H.
      unfold opt_result in H. destr_in H; inv H.
      rewrite <- H1.
      unfold fst. destr.
      generalize (take_drop'_spec _ _ _ _ Heqp).
      generalize (take_drop'_spec _ _ _ _ Heqp2).
      generalize (take_drop'_spec _ _ _ _ Heqp1).
      generalize (take_drop'_spec2 _ _ _ _ Heqp).
      generalize (take_drop'_spec2 _ _ _ _ Heqp2).
      generalize (take_drop'_spec2 _ _ _ _ Heqp1). intuition.
      rewrite H10, ! app_length.
      rewrite H8, H15, H9.
      cut (n0 = List.length bs0). lia.
      rewrite H2. clear - Heqo Heqo0.
      revert idx Heqo Heqo0.
      unfold field_sz, field_type. generalize (struct_fields sg). induction l; simpl; intros; eauto.
      easy.
      repeat destr_in Heqo; inv Heqo; simpl in *;
        rewrite Heqs0 in Heqo0; inv Heqo0. reflexivity.
      destr_in H1; inv H1; eauto.
    - inv WTv1.
      unfold opt_bind in SIG. repeat destr_in SIG; inv SIG.
      generalize (take_drop_spec _ _ _ _ Heqo); intuition. subst. constructor.
      2: rewrite <- H2, ! app_length; simpl; auto.
      Lemma Forall_app:
        forall {A} (P: A -> Prop) l1 l2,
          Forall P (l1 ++ l2) <-> (Forall P l1 /\ Forall P l2).
      Proof.
        induction l1; simpl; intros; eauto.
        split. split; auto. intuition.
        intuition. inv H; constructor; auto. rewrite IHl1 in H3; intuition.
        inv H. rewrite IHl1 in H3; intuition.
        inv H0. constructor. auto. rewrite IHl1; tauto.
      Qed.
      rewrite Forall_app in H1 |- *. destruct H1; split; auto.
      inv H1; constructor; auto.
    - inv WTv1. inv WTv2. inv SIG. apply wt_val_bits. auto.
      destr. destr. unfold fst. destr.
      generalize (take_drop'_spec _ _ _ _ Heqp).
      generalize (take_drop'_spec _ _ _ _ Heqp0).
      generalize (take_drop'_spec _ _ _ _ Heqp1).
      generalize (take_drop'_spec2 _ _ _ _ Heqp).
      generalize (take_drop'_spec2 _ _ _ _ Heqp0).
      generalize (take_drop'_spec2 _ _ _ _ Heqp1). intuition.
      rewrite H9, ! app_length.
      rewrite H11, H16. lia.
  Qed.

  Lemma interp_unop_wt_preserves:
    forall
      {reg_t ext_fn_t} (R: reg_t -> type) (Sigma: ext_fn_t -> ExternalSignature)
      (REnv: Env reg_t)
      (r: env_t REnv (fun _ => val))
      (sigma: ext_fn_t -> val -> val)
      (ctx ctx' : list (var_t * val)) (sig : tsig var_t)
      (action_log sched_log action_log' : UntypedSemantics.Log REnv) 
      (v : val) u a ta tr,
      wt_renv R REnv r ->
      wt_env sig ctx ->
      wt_log R REnv action_log ->
      wt_log R REnv sched_log ->
      wt_unop u ta tr ->
      wt_action pos_t fn_name_t var_t (R:=R) (Sigma:=Sigma) sig a ta ->
      interp_action r sigma ctx action_log sched_log (UUnop u a) action_log' v ctx' ->
      (forall (ctx ctx' : list (var_t * val)) (t : type) (sig : tsig var_t)
              (action_log sched_log action_log' : UntypedSemantics.Log REnv) 
              (v : val),
          wt_renv R REnv r ->
          wt_env sig ctx ->
          wt_log R REnv action_log ->
          wt_log R REnv sched_log ->
          wt_action pos_t fn_name_t var_t (R:=R) (Sigma:=Sigma) sig a t ->
          interp_action r sigma ctx action_log sched_log a action_log' v ctx' ->
          wt_env sig ctx' /\ wt_val t v /\ wt_log R REnv action_log'
      ) ->
      wt_env sig ctx' /\ wt_val tr v /\ wt_log R REnv action_log'.
  Proof.
    intros reg_t0 ext_fn_t0 R0 Sigma0 REnv0 r0 sigma0.
    intros ctx ctx' sig action_log sched_log action_log' v u a ta tr WTR WTE WTLA WTLS WTU WTA INT IH.
    iinv INT.
    eapply IH in H16; eauto.
    destruct H16 as (WTE' & WTv & WTLA'). repeat split; eauto.
    eapply wt_unop_sigma1; eauto.
  Qed.


  Lemma interp_binop_wt_preserves:
    forall
      {reg_t ext_fn_t} (R: reg_t -> type) (Sigma: ext_fn_t -> ExternalSignature)
      (REnv: Env reg_t)
      (r: env_t REnv (fun _ => val))
      (sigma: ext_fn_t -> val -> val)
      (ctx ctx' : list (var_t * val)) (sig : tsig var_t)
      (action_log sched_log action_log' : UntypedSemantics.Log REnv) 
      (v : val) u a b ta tb tr,
      wt_renv R REnv r ->
      wt_env sig ctx ->
      wt_log R REnv action_log ->
      wt_log R REnv sched_log ->
      wt_binop u ta tb tr ->
      wt_action pos_t fn_name_t var_t (R:=R) (Sigma:=Sigma) sig a ta ->
      wt_action pos_t fn_name_t var_t (R:=R) (Sigma:=Sigma) sig b tb ->
      interp_action r sigma ctx action_log sched_log (UBinop u a b) action_log' v ctx' ->
      (forall ua, ua = a \/ ua = b -> forall (ctx ctx' : list (var_t * val)) (t : type) (sig : tsig var_t)
                                             (action_log sched_log action_log' : UntypedSemantics.Log REnv) 
                                             (v : val),
            wt_renv R REnv r ->
            wt_env sig ctx ->
            wt_log R REnv action_log ->
            wt_log R REnv sched_log ->
            wt_action pos_t fn_name_t var_t (R:=R) (Sigma:=Sigma) sig ua t ->
            interp_action r sigma ctx action_log sched_log ua action_log' v ctx' ->
            wt_env sig ctx' /\ wt_val t v /\ wt_log R REnv action_log'
      ) ->
      wt_env sig ctx' /\ wt_val tr v /\ wt_log R REnv action_log'.
  Proof.
    intros reg_t0 ext_fn_t0 R0 Sigma0 REnv0 r0 sigma0.
    intros ctx ctx' sig action_log sched_log action_log' v u a b ta tb tr WTR WTE WTLA WTLS WTU WTA WTB INT IH.
    iinv INT.
    eapply IH in H17; eauto.
    destruct H17 as (WTE' & WTv & WTLA').
    eapply IH in H18; eauto.
    destruct H18 as (WTE'' & WTv' & WTLA'').
    repeat split; eauto.
    eapply wt_binop_sigma1; eauto.
  Qed.

  Lemma interp_list_ctx_wt:
    forall
      {reg_t ext_fn_t} (R: reg_t -> type) (Sigma: ext_fn_t -> ExternalSignature)
      (REnv: Env reg_t)
      (r: env_t REnv (fun _ => val))
      (sigma: ext_fn_t -> val -> val),
    forall (i: list (var_t * val) ->
               UntypedSemantics.Log REnv ->
               UntypedSemantics.Log REnv ->
               uaction pos_t var_t fn_name_t reg_t ext_fn_t ->
               UntypedSemantics.Log REnv -> val -> list (var_t * val) ->
               Prop) args argtypes
           (WTR: wt_renv R REnv r)
           (ARGS: Forall2 (fun '(_, a) t =>
                             forall sig ctx ctx' action_log sched_log action_log' v,
                               wt_env sig ctx ->
                               wt_log R REnv action_log ->
                               wt_log R REnv sched_log ->
                               wt_action pos_t fn_name_t var_t (R:=R) (Sigma:=Sigma) sig a t ->
                               i ctx action_log sched_log a action_log' v ctx' ->
                               wt_env sig ctx' /\ wt_val t v /\ wt_log R REnv action_log'
                          ) args argtypes),
    forall sig ctx action_log sched_log,
      wt_env sig ctx ->
      wt_log R REnv action_log ->
      wt_log R REnv sched_log ->
      forall (WTL: wt_list _ _ _ (wt_action _ _ _ (R:=R) (Sigma:=Sigma)) sig args argtypes),
      forall action_log' ctx',
        interp_list_ctx
          r sigma i ctx action_log sched_log args action_log' ctx' ->
        wt_env (rev (map (fun '(name, _, t) => (name,t)) (combine args argtypes)) ++ sig) ctx' /\
        wt_log R REnv action_log'.
  Proof.
    induction args; simpl; intros; eauto.
    - inv ARGS. inv H2. split; eauto.
    - inv ARGS. inv H2.
      inv WTL.
      eapply H5 in H10; eauto.
      destruct H10 as (WTE' & WTv' & WTLA').
      eapply IHargs in H13; eauto.
      2: constructor; auto. destruct H13. split; auto.
      simpl.
      rewrite <- app_assoc. simpl. auto.
  Qed.


  Lemma interp_list_wt:
    forall
      {reg_t ext_fn_t} (R: reg_t -> type) (Sigma: ext_fn_t -> ExternalSignature)
      (REnv: Env reg_t)
      (r: env_t REnv (fun _ => val))
      (sigma: ext_fn_t -> val -> val),
    forall (i: list (var_t * val) ->
               UntypedSemantics.Log REnv ->
               UntypedSemantics.Log REnv ->
               uaction pos_t var_t fn_name_t reg_t ext_fn_t ->
               UntypedSemantics.Log REnv -> val -> list (var_t * val) -> Prop) args argtypes
           sig
           (WTR: wt_renv R REnv r)
           (ARGS: Forall2 (fun a t =>
                             forall ctx ctx' action_log sched_log action_log' v,
                               wt_env sig ctx ->
                               wt_log R REnv action_log ->
                               wt_log R REnv sched_log ->
                               i ctx action_log sched_log a action_log' v ctx' ->
                               wt_env sig ctx' /\ wt_val t v /\ wt_log R REnv action_log'
                          ) args argtypes),
    forall ctx action_log sched_log,
      wt_env sig ctx ->
      wt_log R REnv action_log ->
      wt_log R REnv sched_log ->
      forall action_log' ctx' lv,
        interp_list
          r sigma i ctx action_log sched_log args action_log' lv ctx' ->
        wt_env sig ctx' /\
        Forall2 (fun v t => wt_val t v) (rev lv) argtypes /\
        wt_log R REnv action_log'.
  Proof.
    induction args; simpl; intros; eauto.
    - inv ARGS. inv H2. simpl; repeat split; eauto.
    - inv ARGS. inv H2.
      eapply H5 in H10; eauto. rewrite rev_app_distr. simpl.
      destruct H10 as (WTE' & WTv' & WTLA').
      eapply IHargs in H14; eauto.
      intuition.
  Qed.

  Lemma Forall2_impl:
    forall {A B} (P1 P2: A -> B -> Prop) l1 l2,
      Forall2 P1 l1 l2 ->
      (forall x y, In x l1 -> In y l2 -> P1 x y -> P2 x y) ->
      Forall2 P2 l1 l2.
  Proof.
    induction 1; simpl; intros; eauto.
    constructor; eauto.
  Qed.

  Lemma wt_env_app:
    forall sig1 ctx1,
      wt_env sig1 ctx1 ->
      forall sig2 ctx2,
        wt_env sig2 ctx2 ->
        wt_env (sig1 ++ sig2) (ctx1 ++ ctx2).
  Proof.
    induction 1; simpl; intros; eauto.
    constructor; auto.
  Qed.

  Lemma wt_env_rev:
    forall sig ctx,
      wt_env sig ctx ->
      wt_env (rev sig) (rev ctx).
  Proof.
    induction 1; simpl; intros; eauto. constructor.
    apply wt_env_app. auto. repeat constructor. auto.
  Qed.

  Lemma forall2_wt_wt_env:
    forall lv lt,
      Forall2 (fun v t => wt_val t v) lv (map snd lt) ->
      wt_env (rev lt) (map (fun '(name, _, v0) => (name, v0)) (combine (rev lt) (rev lv))).
  Proof.
    intros. rewrite <- UntypedSemantics.combine_rev.
    2: erewrite (Forall2_length _ _ _ H), map_length; eauto.
    rewrite map_rev.
    apply wt_env_rev.
    revert lt H.
    induction lv; simpl; intros; eauto.
    - inv H. destruct lt; simpl in *; try congruence. constructor.
    - inv H. destruct lt; simpl in *; try congruence.
      destr. simpl in *. inv H2. constructor; eauto.
  Qed.

  Lemma wt_env_tl sig ctx:
    wt_env sig ctx -> wt_env (tl sig) (tl ctx).
  Proof.
    induction 1; simpl; auto. constructor.
  Qed.

  Lemma wt_env_iter_tl n: forall sig ctx,
      wt_env sig ctx ->
      wt_env (Nat.iter n (@tl (var_t * type)) sig) (Nat.iter n (@tl (var_t * val)) ctx).
  Proof.
    induction n; simpl; intros; eauto.
    apply wt_env_tl. eauto.
  Qed.

  Lemma tl_app:
    forall {A: Type} (l1 l2: list A),
      Nat.iter (List.length l1) (@tl A) (l1 ++ l2) = l2.
  Proof.
    induction l1; simpl; intros; eauto.
    simpl. rewrite <- iter_assoc_spec. simpl. rewrite IHl1. auto.
  Qed.

  Lemma sig_of_bindings_eq:
    forall {A: Type} (bindings: list (var_t * A)) (bind_taus: list type) sig,
      sig_of_bindings var_t bindings bind_taus sig ->
      sig = map (fun '(name, _, t) => (name, t)) (combine bindings bind_taus).
  Proof.
    induction 1; simpl; intros; eauto.
    f_equal. eauto.
  Qed.


  Lemma forall2_map_l:
    forall {A B C: Type} (f: A -> B) (P: B -> C -> Prop) l1 (l2: list C),
      Forall2 (fun x y => P (f x) y) l1 l2 ->
      Forall2 P (map f l1) l2.
  Proof.
    induction 1; simpl; intros; eauto.
  Qed.

  Lemma fold_subst_field_name_some:
    forall sg vals si sf,
      fold_left (fun vs '(name, v) =>
                   let/opt vs0 := vs in
                   subst_field_name (struct_fields sg) name v vs0
                ) vals si = Some sf ->
      exists ssi, si = Some ssi.
  Proof.
    induction vals; simpl; intros; eauto.
    repeat destr_in H. destruct si; simpl in *. eauto.
    apply IHvals in H. destruct H; congruence.
  Qed.

  Lemma subst_field_name_wt:
    forall sg name v,
      (exists idx : index (Datatypes.length (struct_fields sg)),
          PrimTypeInference.find_field sg name = Success idx /\
          wt_val (snd (List_nth (struct_fields sg) idx)) v) ->
      forall si sf,
        Forall2 (wt_val) (map snd (struct_fields sg)) si ->
        subst_field_name (struct_fields sg) name v si = Some sf ->
        Forall2 (wt_val) (map snd (struct_fields sg)) sf.
  Proof.
    unfold PrimTypeInference.find_field.
    intro sg.
    generalize (struct_fields sg).

    assert (
        forall (l : list (string * type)) (name : string) (v : val),
          (exists idx : index (Datatypes.length l),
              List_assoc name l = Some idx /\
              wt_val (snd (List_nth l idx)) v) ->
          forall si sf : list val,
            Forall2 wt_val (map snd l) si ->
            subst_field_name l name v si = Some sf -> Forall2 wt_val (map snd l) sf
      ).
    {
      clear.
      induction l; simpl; intros; eauto.
      destr_in H1; congruence.
      destruct a; simpl in *.
      destruct H as (idx & EQ & WTv).
      repeat destr_in H1; inv H1.
      - inv EQ. simpl in *. inv H0; constructor; auto.
      - destr_in EQ; inv EQ. unfold opt_bind in H2; destr_in H2; inv H2.
        inv H0; constructor; auto.
        eapply IHl; eauto.
    }
    intros; eapply H; eauto.
    decompose [ex and] H0. unfold opt_result in H4. destr_in H4; inv H4.
    eexists; split; eauto.
  Qed.

  Lemma fold_subst_field_name_wt:
    forall sg vals,
      Forall (fun '(name,v) =>
                exists idx : index (Datatypes.length (struct_fields sg)),
                  PrimTypeInference.find_field sg name = Success idx /\
                  wt_val (snd (List_nth (struct_fields sg) idx)) v
             ) vals ->
      forall si sf,
        Forall2 (wt_val) (map snd (struct_fields sg)) si ->
        fold_left (fun vs '(name, v) =>
                     let/opt vs0 := vs in
                     subst_field_name (struct_fields sg) name v vs0
                  ) vals (Some si) = Some sf ->
        Forall2 (wt_val) (map snd (struct_fields sg)) sf.
  Proof.
    induction 1; simpl; intros; eauto.
    inv H0; auto.
    destruct x.
    edestruct fold_subst_field_name_some; eauto. rewrite H3 in H2.
    eapply IHForall. 2: eauto.
    eapply subst_field_name_wt; eauto.
  Qed.

  Lemma forall2_3:
    forall {A B C D: Type}
           (P: (A * B) -> C -> Prop)
           (Q: D -> C -> Prop)
           (R: A * D -> Prop)
           l1 l2 l3,
      Forall2 P l1 l2 ->
      Forall2 Q l3 l2 ->
      (forall x y z,
          P x y ->
          Q z y ->
          R (fst x, z)
      ) ->
      Forall R (combine (map fst l1) l3).
  Proof.
    induction l1; simpl; intros; eauto. inv H. inv H0. constructor; eauto.
  Qed.


  Lemma fold_subst_none:
    forall (vals: list val),
      fold_left
        (fun acc v =>
           let/opt2 pos, vs := acc in
           let/opt pat0 := take_drop pos vs in
           match pat0 with
             (l1, []) => None
           | (l1, _ :: l3) => Some (S pos, l1 ++ v :: l3)
           end
        ) vals None = None.
  Proof.
    induction vals; simpl; intros; eauto.
  Qed.

  Lemma fold_subst_array_wt:
    forall t vals,
      Forall (fun v => wt_val t v) vals ->
      forall ai af,
        Forall (fun v => wt_val t v) (snd ai) ->
        fold_left
          (fun acc v =>
             let/opt2 pos, vs := acc in
             let/opt pat0 := take_drop pos vs in
             match pat0 with
               (l1, []) => None
             | (l1, _ :: l3) => Some (S pos, l1 ++ v :: l3)
             end
          ) vals (Some ai) = Some af ->
        Forall (fun v => wt_val t v) (snd af) /\ List.length (snd af) = List.length (snd ai).
  Proof.
    induction 1; simpl; intros; eauto. inv H0; auto.
    destruct ai. unfold opt_bind in H2. repeat destr_in H2; inv H2.
    - rewrite fold_subst_none in H4; congruence.
    - eapply IHForall in H4.
      destruct H4. simpl in *.
      apply take_drop_spec in Heqo. destruct Heqo as [Heqo _]. subst.
      split; auto.
      rewrite H3; rewrite ! app_length. simpl; auto.
      apply take_drop_spec in Heqo. destruct Heqo as [Heqo _]. subst.
      clear - H H1. simpl in *.
      rewrite Forall_app in *. intuition. inv H2. constructor; auto.
    - rewrite fold_subst_none in H4; congruence.
  Qed.

  Lemma Forall2_Forall:
    forall {A B: Type} (P: A -> B -> Prop) l1 l2,
      Forall2 P l1 l2 ->
      Forall (fun x => exists y, In y l2 /\ P x y) l1.
  Proof.
    induction 1; simpl; intros; eauto.
    constructor; eauto.
    eapply Forall_impl; eauto. simpl. intros. decompose [ex and] H1; eauto.
  Qed.


  Lemma uvalue_of_list_bits_length:
    forall tau l1 l2,
      uvalue_of_list_bits (tau:=tau) l1 = Some l2 ->
      List.length l2 = List.length l1.
  Proof.
    induction l1; simpl; intros; eauto. inv H; auto.
    unfold opt_bind in H; repeat destr_in H; inv H. simpl. f_equal; eauto.
  Qed.


  Lemma wt_action_preserves_wt_env:
    forall {reg_t ext_fn_t} (R: reg_t -> type) (Sigma: ext_fn_t -> ExternalSignature)
           (REnv: Env reg_t)
           (r: env_t REnv (fun _ => val))
           (sigma: ext_fn_t -> val -> val)
           (sigma_wt: forall fn v, wt_val (arg1Sig (Sigma fn)) v ->
                                   wt_val (retSig (Sigma fn)) (sigma fn v))
           a ctx ctx' t sig action_log sched_log action_log' v,
      wt_renv R REnv r ->
      wt_env sig ctx ->
      wt_action pos_t fn_name_t var_t (R:=R) (Sigma:=Sigma) sig a t ->
      wt_log R REnv action_log ->
      wt_log R REnv sched_log ->
      UntypedIndSemantics.interp_action r sigma ctx action_log sched_log a action_log' v ctx' ->
      wt_env sig ctx' /\ wt_val t v /\ wt_log R REnv action_log'.
  Proof.
    clear.
    intros reg_t ext_fn_t R Sigma REnv r sigma sigma_wt ua.
    remember (size_uaction ua).
    revert reg_t ext_fn_t R Sigma REnv r sigma sigma_wt ua Heqn.
    pattern n.
    eapply Nat.strong_right_induction with (z:=0).
    { red. red. intros. subst. tauto. } 2: lia.
    intros n0 _ Plt reg_t ext_fn_t R Sigma REnv r sigma sigma_wt ua Heqn. subst.
    assert (Plt':
              forall
                {reg_t ext_fn_t} (R: reg_t -> type) (Sigma: ext_fn_t -> ExternalSignature)
                (REnv: Env reg_t)
                (r: env_t REnv (fun _ => val))
                (sigma: ext_fn_t -> val -> val)
                (sigma_wt: forall fn v, wt_val (arg1Sig (Sigma fn)) v ->
                                        wt_val (retSig (Sigma fn)) (sigma fn v))
                (ua': Syntax.uaction pos_t var_t fn_name_t reg_t ext_fn_t),
                size_uaction ua' < size_uaction ua ->
                forall (ctx ctx' : list (var_t * val)) (t : type) (sig : tsig var_t)
                       (action_log sched_log action_log' : UntypedSemantics.Log REnv) (v : val),
                  wt_renv R REnv r ->
                  wt_env sig ctx ->
                  wt_log R REnv action_log ->
                  wt_log R REnv sched_log ->
                  wt_action pos_t fn_name_t var_t (R:=R) (Sigma:=Sigma) sig ua' t ->
                  interp_action r sigma ctx action_log sched_log ua' action_log' v ctx' -> wt_env sig ctx' /\ wt_val t v /\ wt_log R REnv action_log').
    { intros. eapply Plt. 4: reflexivity. lia. eauto. auto. eauto. 5: eauto. all: eauto. } clear Plt.
    rename Plt' into IHua. clear n.
    intros ctx ctx' t sig action_log sched_log action_log' v WTR WTE WTA WTLa WTLs INT.
    inv WTA.
    - iinv INT.
    - iinv INT. repeat split; auto.
      eapply wt_env_list_assoc; eauto.
    - iinv INT. repeat split; auto. apply wt_val_of_value.
    - iinv INT.
      eapply IHua in H18. 3: simpl; lia. all: eauto.
      destruct H18 as (? & ? & ?).
      repeat split; eauto.
      + eapply wt_env_set; eauto.
      + constructor; reflexivity.
    - iinv INT.
      eapply (IHua) in H18; eauto. 2: simpl; lia.
      eapply (IHua) in H19; eauto. simpl; lia. tauto. tauto.
    - iinv INT.
      eapply (IHua) in H19; eauto. 2: simpl; lia.
      eapply (IHua) in H20; eauto. 2: simpl; lia.
      + intuition.
        inv H5. simpl; auto.
      + intuition. constructor; auto.
      + tauto.
    - iinv INT.
      eapply (IHua) in H20; eauto. 2: simpl; lia.
      eapply (IHua) in H21; eauto. destruct b; simpl; lia. tauto. tauto.
      destruct b; auto.
    - iinv INT. repeat split; auto.
      destr. eauto.
      + destr; eauto. unfold latest_write0 in Heqo.
        edestruct @log_find_wt. apply Heqo.  intros. destruct x; simpl in H0.
        repeat destr_in H0; inv H0. reflexivity.
        eapply wt_log_app; eauto. destruct H0.
        unfold log_latest_write0_fn in H0. repeat destr_in H0; inv H0. simpl in *; auto.
      + eapply wt_log_cons; eauto. simpl. congruence.
    - iinv INT.
      eapply IHua in H18. 3: simpl; lia. all: eauto.
      destruct H18 as (? & ? & ?).
      repeat split. 2: constructor; reflexivity. auto.
      eapply wt_log_cons; eauto.
    - eapply interp_unop_wt_preserves. 7: eauto. all: eauto.
      intros; eapply IHua. 8: eauto. auto. simpl; lia. all: eauto.
    - 
      Ltac autobinop IHua :=
        repeat match goal with
               | Hint: interp_action ?r ?sigma ?ctx ?al ?sl (UBinop ?u ?a ?b) ?al' ?v ?ctx'
                 |- _ /\ _ /\ _ =>
                 eapply (fun sig =>
                           @interp_binop_wt_preserves
                             _ _ _ _ _ r sigma ctx ctx'
                             sig al sl al' v u a b
                        ); eauto
               | |- wt_binop _ _ _ _ => econstructor; eauto
               | |- forall _, _ \/ _ -> _ => let x := fresh "H" in
                                             intros ? x; eapply IHua; eauto; try (destruct x; subst; simpl; lia)
               end.
      autobinop IHua.
    - iinv INT.
      Ltac iaauto :=
        match goal with
        | |- interp_action _ _ _ _ _ _ _ _ _ => eauto
        | |- interp_list _ _ _ _ _ _ _ _ _ _ => eauto
        | |- _ => idtac
        end.
      Ltac autoIH IHua a :=
        let wte := fresh "WTE" in
        let wtv := fresh "WTV" in
        let wtla := fresh "WTLA" in
        edestruct (fun R Sigma REnv r sigma sigma_wt =>
                     IHua _ _ R Sigma REnv r sigma sigma_wt a
                  ) as (wte & wtv & wtla); iaauto; eauto.
      Ltac eautoIH IHua :=
        let wte := fresh "WTE" in
        let wtv := fresh "WTV" in
        let wtla := fresh "WTLA" in
        edestruct IHua as (wte & wtv & wtla); iaauto; eauto.
      eautoIH IHua.
    - iinv INT.
      edestruct @interp_list_wt as (WTE' & WTLV & WTLA'); iaauto; eauto.
      eapply Forall2_impl. eauto.
      intros; eauto.
      eautoIH IHua.
      simpl.
      clear - H3. revert H3; induction args; simpl; intros; eauto. easy.
      destruct H3; subst; simpl in *; eauto. lia.
      apply IHargs in H. lia.
      eautoIH IHua. simpl; lia.
      eapply forall2_wt_wt_env in WTLV.
      rewrite rev_involutive in WTLV. auto.
    - iinv INT. eautoIH IHua.
    - iinv INT.
      repeat split; eauto. constructor; reflexivity.
    - iinv INT.
      repeat split; eauto. apply wt_val_bits; auto. unfold l; rewrite vect_to_list_length. auto.
    - iinv INT.
      repeat split; eauto. constructor.
      2: rewrite map_length, vect_to_list_length; reflexivity. simpl.
      rewrite Forall_forall. intro. rewrite in_map_iff. intros (x0 & EQ & IN). subst.
      apply wt_val_bits; auto.
    - iinv INT. repeat split; eauto.
      apply wt_val_of_value.
    - iinv INT.
      edestruct @interp_list_wt as (WTE' & WTLV & WTLA'); iaauto; eauto.
      instantiate (1:=map (fun _ => unit_t) aa).
      assert (Forall2 (fun a t => wt_action _ _ _ (R:=R) (Sigma:=Sigma) sig a t) aa (map (fun _ => unit_t) aa)). {
        clear - H. revert H. induction aa; simpl; intros; eauto. constructor; eauto.
      }
      eapply Forall2_impl. eauto.
      intros; eauto.
      eapply IHua. 8: eauto. all: eauto. simpl.
      clear - H2. revert H2; induction aa; simpl; intros; eauto. easy.
      destruct H2; subst; simpl in *; eauto. lia.
      apply IHaa in H. lia.
      repeat split; eauto.
      apply UntypedSemantics.Forall2_rev in WTLV. rewrite rev_involutive in WTLV. inv WTLV.
      simpl; constructor; auto.
      simpl.
      assert (IN: In y (y :: l')) by (simpl; auto).
      rewrite H1 in IN. rewrite <- In_rev in IN.
      rewrite in_map_iff in IN.
      decompose [ex and] IN. subst. auto.
    - iinv INT.

      assert (IHua': forall ua' : uaction pos_t var_t fn_name_t reg_t ext_fn_t,
                 In ua' (map snd bindings) ->
                 forall (ctx ctx' : list (var_t * val)) (t : type) (sig : tsig var_t)
                        (action_log sched_log action_log' : UntypedSemantics.Log REnv)
                        (v : val),
                   wt_renv R REnv r ->
                   wt_env sig ctx ->
                   wt_log R REnv action_log ->
                   wt_log R REnv sched_log ->
                   wt_action pos_t fn_name_t var_t (R:=R) (Sigma:=Sigma) sig ua' t ->
                   interp_action r sigma ctx action_log sched_log ua' action_log' v ctx' ->
                   wt_env sig ctx' /\ wt_val t v /\ wt_log R REnv action_log'
             ).
      {
        intros; eapply IHua. 8: eauto. all: eauto.
        simpl. clear - H4. revert H4.
        induction bindings; simpl; intros; eauto. easy.
        destruct a, H4; simpl in *; subst. lia.
        apply IHbindings in H. lia.
      }

      edestruct @interp_list_ctx_wt as (WTE' & WTLA'). 7: eauto. all: eauto.

      clear - WTR H IHua'.
      revert bindings sig bind_taus H IHua'.
      + induction 1; simpl; intros; eauto.
        constructor; eauto.
      +
        autoIH IHua body. simpl; lia.

        erewrite <- sig_of_bindings_eq. 2: eauto. eauto.

        eapply IHua in H20. all: eauto. 2: simpl; lia.
        2: erewrite <- sig_of_bindings_eq; eauto.
        repeat split; auto.

        destruct H20 as (WTE''' & WTV' & WTLA''').

        eapply wt_env_iter_tl in WTE'''.
        rewrite tl_app in WTE'''.
        rewrite rev_length, map_length, combine_length in WTE'''.
        assert (List.length bindings = List.length bind_taus).
        {
          clear - H.
          revert H. induction 1; simpl; intros; eauto.
        }
        rewrite H4 in WTE'''.
        rewrite Nat.min_id in WTE'''.
        rewrite <- H4 in WTE'''. auto.
    - iinv INT.
      autoIH IHua cond. simpl; lia.
      autoIH IHua body. simpl; lia.
    - iinv INT.
      + autoIH IHua default. simpl; lia.
      + inv H1. destruct H6.
        autoIH IHua var.  simpl; lia.
        autoIH IHua cond. simpl; lia.
        autoIH IHua body. simpl; lia.
      + inv H1. destruct H6.
        autoIH IHua var.  simpl; lia.
        autoIH IHua cond. simpl; lia.
        eautoIH IHua. simpl; lia.
        econstructor. eauto. eauto. eauto.
    - iinv INT.
      assert (exists l,
                 Forall2 (fun '(name, a) t =>
                            exists idx,
                              PrimTypeInference.find_field sg name = Success idx /\
                              t = snd (List_nth (struct_fields sg) idx) /\
                              wt_action (R:=R) (Sigma:=Sigma) pos_t fn_name_t var_t sig a t
                         )
                         fields l
             ).
      {
        clear - H. revert H.
        induction 1; simpl; intros; eauto.
        decompose [ex and] H; clear H.
        decompose [ex and] IHForall; clear IHForall.
        destruct x.
        eexists; econstructor; eauto.
      } destruct H2.
      edestruct @interp_list_wt as (WTE1 & WTLV1 & WTLA1). 7: eauto. all: eauto.

      eapply forall2_map_l.
      eapply Forall2_impl. eauto.
      simpl. destruct x0; simpl. intros. destruct H5 as (idx & FF & EQ & WT). subst.
      eapply IHua. 8: eauto.
      all: eauto. simpl. clear -H3.
      revert H3.
      induction fields; simpl; intros; eauto. easy.
      destruct H3. subst. lia.
      apply IHfields in H. lia.
      repeat split; auto.
      constructor.
      
      eapply fold_subst_field_name_wt in H19; eauto.
      eapply forall2_3; eauto. simpl; intros. destruct x0.
      decompose [ex and] H3; clear H3. subst. eauto.
      eapply uvalue_of_struct_bits_wt; eauto.
      intros; eapply uvalue_of_bits_wt; eauto.
      unfold zeroes; rewrite repeat_length. auto.
    - iinv INT.
      assert (Forall2 (fun elt t =>
                         wt_action (R:=R) (Sigma:=Sigma) pos_t fn_name_t var_t sig elt t /\ t = tau
                      )
                      elements (repeat tau (List.length elements))
             ).
      {
        clear - H. revert H.
        induction 1; simpl; intros; eauto.
      }
      edestruct @interp_list_wt as (WTE1 & WTLV1 & WTLA1); iaauto; eauto.
      eapply Forall2_impl. eauto.
      simpl.
      intros x y INelts INRep (WT & EQ) ctx0 ctx'0 action_log0 sched_log0 action_log'0 v
             WTE' WTLA WTLS IA.
      eapply IHua; iaauto; eauto.
      simpl. clear - INelts.
      revert INelts.
      induction elements; simpl; intros; eauto. easy.
      destruct INelts. subst. lia.
      apply IHelements in H. lia.
      repeat split; auto.


      edestruct fold_subst_array_wt. 3: eauto.
      eapply Forall_impl. 2: eapply Forall2_Forall. 2: eapply WTLV1. simpl.
      intros a (y & IN & WT).
      apply repeat_spec in IN. subst; eauto. simpl.
      eapply uvalue_of_list_bits_inv. 3: eauto.
      rewrite Forall_forall; intros x IN. unfold zeroes in IN; apply repeat_spec in IN. subst.
      rewrite repeat_length. auto.
      intros; eapply uvalue_of_bits_wt; eauto.
      constructor.
      unfold sig0; simpl; auto.
      rewrite H4; simpl.
      erewrite uvalue_of_list_bits_length; eauto.
      unfold zeroes; rewrite repeat_length. auto.
    - iinv INT.
      edestruct @interp_list_wt as (WTE' & WTLV & WTLA'); iaauto; eauto.
      eapply Forall2_impl. eauto.
      intros; eauto.
      eautoIH IHua.
      simpl.
      clear - H3. revert H3; induction args; simpl; intros; eauto. easy.
      destruct H3; subst; simpl in *; eauto. lia.
      apply IHargs in H. lia.
      eautoIH IHua. simpl. auto. simpl; lia.
      + clear - WTR.
        red in WTR; red. intros.
        rewrite getenv_create. eauto.
      + eapply forall2_wt_wt_env in WTLV.
        rewrite rev_involutive in WTLV. auto.
      + clear - WTLa. red in WTLa. red.
        Opaque ContextEnv.
        unfold UntypedSemantics.fLog.
        intros idx le. rewrite getenv_create. eauto.
      + clear - WTLA'. red in WTLA'. red.
        Opaque ContextEnv.
        unfold UntypedSemantics.fLog.
        intros idx le. rewrite getenv_create. eauto.
      + repeat split; auto.
        unfold UntypedSemantics.fLog'.
        red.
        intros idx le. rewrite getenv_create.
        red in WTLA. red in WTLA'.
        destr; eauto.
        intros. eapply WTLA in H3; eauto.
        eapply UntypedSemantics.fRinv_correct_inv in Heqo. subst; eauto.
  Qed.

  Lemma wt_action_to_daction:
    forall {reg_t ext_fn_t} (R: reg_t -> type) (Sigma: ext_fn_t -> ExternalSignature)
           sig ua t,
      wt_action (R:=R) (Sigma:=Sigma) pos_t fn_name_t var_t sig ua t ->
      forall da,
        uaction_to_daction ua = Some da ->
        wt_daction (R:=R) (Sigma:=Sigma) pos_t fn_name_t var_t sig da t.
  Proof.
    intros reg_t ext_fn_t R Sigma sig ua t.
    remember (size_uaction ua).
    revert reg_t ext_fn_t R Sigma sig ua t Heqn.
    pattern n.
    eapply Nat.strong_right_induction with (z:=0).
    { red. red. intros. subst. tauto. } 2: lia.
    intros n0 _ Plt reg_t ext_fn_t R Sigma sig ua t Heqn. subst.
    assert (Plt':
              forall
                {reg_t ext_fn_t} (R: reg_t -> type) (Sigma: ext_fn_t -> ExternalSignature)
                (ua': Syntax.uaction pos_t var_t fn_name_t reg_t ext_fn_t),
                size_uaction ua' < size_uaction ua ->
                forall (t : type) (sig : tsig var_t),
                  wt_action (R:=R) (Sigma:=Sigma) pos_t fn_name_t var_t sig ua' t ->
                  forall da,
                    uaction_to_daction ua' = Some da ->
                    wt_daction (R:=R) (Sigma:=Sigma) pos_t fn_name_t var_t sig da t).
    { intros. eapply Plt. 4: apply H0. 3: reflexivity. lia. eauto. auto. } clear Plt.
    rename Plt' into IHua. clear n.
    intros WTA da UA.
    inv WTA; simpl in UA; unfold opt_bind in UA; repeat destr_in UA; inv UA; try now (econstructor; eauto; try (eapply IHua; eauto; simpl; try lia)).
    - econstructor.
      eapply wt_val_of_value.
    - econstructor; eauto.
      eapply IHua. 3: eauto. simpl; lia. eauto.
      eapply IHua. 3: eauto. simpl; lia. eauto.
      eapply IHua. 3: eauto. simpl; lia. eauto.
    - econstructor; eauto.
      simpl.

      Lemma Forall2_impl':
        forall {A B C: Type} (P: A -> C -> Prop) (f: A -> option B) (Q: B -> C -> Prop)
        l1 l2,
          Forall2 P l1 l2 ->
          forall l3,
          Forall2 (fun a b => f a = Some b) l1 l3 ->
          (forall x b t, In x l1 -> P x t -> f x = Some b -> Q b t) ->
          Forall2 Q l3 l2.
      Proof.
        induction 1; simpl; intros; eauto.
        - inv H. constructor.
        - inv H1.
          econstructor; eauto.
      Qed.

      eapply Forall2_impl'. apply H.
      eapply UntypedSemantics.map_error_forall2. eauto.
      intros. eapply IHua. 3: eauto. 2: eauto. simpl.
      cut (size_uaction x <= list_sum (map size_uaction args)). lia.
      clear - H1. revert x args H1. induction args; simpl; intros; eauto.
      easy.
      destruct H1. subst. lia.
      apply IHargs in H. lia.

      simpl. eapply IHua. 3: eauto. simpl; lia. eauto.
  Qed.

Fixpoint size_daction
         {pos_t var_t fn_name_t reg_t ext_fn_t: Type}
         (da: @daction pos_t var_t fn_name_t reg_t ext_fn_t) {struct da}
  : nat :=
  match da  with
  | DError err => 0
  | DFail tau => 0
  | DVar var => 0
  | DConst _ cst => 0
  | DAssign v ex => 1 + size_daction ex
  | DSeq a1 a2 => 1 + size_daction a1 + size_daction a2
  | DBind v ex body => 1 + size_daction ex + size_daction body
  | DIf cond tbranch fbranch =>
    1 + size_daction cond + size_daction tbranch + size_daction fbranch
  | DRead port idx => 0
  | DWrite port idx value => 1 + size_daction value
  | DUnop ufn1 arg1 => 1 + size_daction arg1
  | DBinop ufn2 arg1 arg2 => 1 + size_daction arg1 + size_daction arg2
  | DExternalCall ufn arg => 1 + size_daction arg
  | DInternalCall ufn args =>
    1 + size_daction (int_body ufn) + list_sum (map size_daction args)
  | DAPos p e => 1 + size_daction e
  end.
  Lemma interp_dlist_wt:
    forall
      {reg_t ext_fn_t} (R: reg_t -> type)
      (REnv: Env reg_t),
    forall (i: list (var_t * val) ->
               UntypedSemantics.Log REnv ->
               UntypedSemantics.Log REnv ->
               @daction pos_t var_t fn_name_t reg_t ext_fn_t ->
               option (UntypedSemantics.Log REnv * val * list (var_t * val)) ) args argtypes
           sig
           (* (WTR: wt_renv R REnv r) *)
           (ARGS: Forall2 (fun a t =>
                             forall ctx ctx' action_log sched_log action_log' v,
                               wt_env sig ctx ->
                               wt_log R REnv action_log ->
                               wt_log R REnv sched_log ->
                               i ctx action_log sched_log a =  Some (action_log', v, ctx') ->
                               wt_env sig ctx' /\ wt_val t v /\ wt_log R REnv action_log'
                          ) args argtypes),
    forall ctx action_log sched_log,
      wt_env sig ctx ->
      wt_log R REnv action_log ->
      wt_log R REnv sched_log ->
      forall l0 at0,
        Forall2 (fun v t => wt_val t v) (rev l0) at0 ->
        forall action_log' ctx' lv,
          fold_left (fun acc a =>
                       match acc with
                       | Some (action_log0, l, Gamma) =>
                           match i Gamma sched_log action_log0 a with
                           | Some (action_log, v, Gamma0) =>
                               Some (action_log, v::l, Gamma0)
                           | None => None
                           end
                       | None => None
                       end
                    ) args (Some (action_log, l0, ctx)) = Some (action_log', lv, ctx') ->
          wt_env sig ctx' /\
            Forall2 (fun v t => wt_val t v) (rev lv) (at0 ++ argtypes) /\
            wt_log R REnv action_log'.
  Proof.
    induction args; simpl; intros; eauto.
    - inv ARGS. inv H3. simpl; repeat split; eauto. rewrite app_nil_r; auto.
    - inv ARGS. repeat destr_in H3.
      edestruct H6 as (WTE & WTV & WTL). 4: now eauto. auto. auto. auto.
      eapply IHargs in H3. 2: eauto. destruct H3; split; eauto.
      revert H4. instantiate (1:=at0++[y]). rewrite <- app_assoc. simpl. auto. auto. auto.
      auto.
      simpl.
      apply Forall2_app. eauto.
      econstructor; eauto.
      rewrite UntypedSemantics.fold_left_none in H3. congruence. auto.
  Qed.

  Lemma wt_daction_preserves_wt_env:
    forall {reg_t ext_fn_t} (R: reg_t -> type) (Sigma: ext_fn_t -> ExternalSignature)
           (REnv: Env reg_t)
           (r: env_t REnv (fun _ => val))
           (sigma: ext_fn_t -> val -> val)
           (sigma_wt: forall fn v, wt_val (arg1Sig (Sigma fn)) v ->
                                   wt_val (retSig (Sigma fn)) (sigma fn v))
           a ctx ctx' t sig action_log sched_log action_log' v,
      wt_renv R REnv r ->
      wt_env sig ctx ->
      wt_daction pos_t fn_name_t var_t (R:=R) (Sigma:=Sigma) sig a t ->
      wt_log R REnv action_log ->
      wt_log R REnv sched_log ->
      UntypedSemantics.interp_daction r sigma ctx action_log sched_log a = Some (action_log', v, ctx') ->
      wt_env sig ctx' /\ wt_val t v /\ wt_log R REnv action_log'.
  Proof.
    intros reg_t ext_fn_t R Sigma REnv r sigma sigma_wt ua.
    remember (size_daction ua).
    revert ua Heqn.
    pattern n.
    eapply Nat.strong_right_induction with (z:=0).
    { red. red. intros. subst. tauto. } 2: lia.
    intros n0 _ Plt ua Heqn. subst.
    assert (Plt':
             forall
               (ua': @daction pos_t var_t fn_name_t reg_t ext_fn_t),
               size_daction ua' < size_daction ua ->
               forall (ctx ctx' : list (var_t * val)) (t : type) (sig : tsig var_t)
                      (action_log sched_log action_log' : UntypedSemantics.Log REnv) (v : val),
                 wt_renv R REnv r ->
                 wt_env sig ctx ->
                 wt_log R REnv action_log ->
                 wt_log R REnv sched_log ->
                 wt_daction pos_t fn_name_t var_t (R:=R) (Sigma:=Sigma) sig ua' t ->
                 UntypedSemantics.interp_daction r sigma ctx action_log sched_log ua' = Some (action_log', v, ctx') -> wt_env sig ctx' /\ wt_val t v /\ wt_log R REnv action_log').
    { intros. eapply Plt. 9: eauto. 3: reflexivity. lia. eauto. auto. eauto. all: eauto. } clear Plt.
    rename Plt' into IHua. clear n.
    intros ctx ctx' t sig action_log sched_log action_log' v WTR WTE WTA WTLa WTLs INT.
    inv WTA; simpl in INT; unfold opt_bind in INT; repeat destr_in INT; inv INT.
    - repeat split; auto.
      eapply wt_env_list_assoc; eauto.
    - repeat split; auto.
    - eapply IHua in Heqo; eauto.
      destruct Heqo as (? & ? & ?).
      repeat split; eauto.
      + eapply wt_env_set; eauto.
      + constructor; reflexivity.
    - eapply IHua in Heqo; eauto.
      destruct Heqo as (?&?&?).
      eapply IHua in H2; eauto. simpl; lia. simpl; lia.
    - eapply IHua in Heqo; eauto.
      destruct Heqo as (?&?&?).
      eapply IHua in Heqo0; eauto.
      destruct Heqo0 as (?&?&?).
      intuition. inv H4. simpl; auto. simpl; lia.
      constructor; auto. simpl; lia.
    - eapply IHua in Heqo; eauto.
      destruct Heqo as (?&?&?).
      eapply IHua in H3; eauto.
      simpl; lia. simpl; lia.
    - eapply IHua in Heqo; eauto.
      destruct Heqo as (?&?&?).
      eapply IHua in H3; eauto.
      simpl; lia. simpl; lia.
    - repeat split; auto.
      eapply wt_log_cons. auto. simpl. inversion 1.
    - repeat split; auto.
      + unfold latest_write0 in Heqo.
        edestruct @log_find_wt. apply Heqo.  intros. destruct x; simpl in H.
        repeat destr_in H; inv H. reflexivity.
        eapply wt_log_app; eauto. destruct H.
        unfold log_latest_write0_fn in H. repeat destr_in H; inv H. simpl in *; auto.
      + eapply wt_log_cons; eauto. simpl. congruence.
    - repeat split; auto.
      eapply wt_log_cons; eauto. simpl. congruence.
    - eapply IHua in Heqo; eauto.
      destruct Heqo as (?&?&?).
      repeat split; auto. repeat constructor.
      eapply wt_log_cons; eauto.
    - eapply IHua in Heqo; eauto.
      destruct Heqo as (?&?&?).
      repeat split; auto.
      eapply wt_unop_sigma1; eauto.
    - eapply IHua in Heqo; eauto.
      destruct Heqo as (?&?&?).
      eapply IHua in Heqo0; eauto.
      destruct Heqo0 as (?&?&?).
      repeat split; auto.
      eapply wt_binop_sigma1; eauto.
      simpl; lia. simpl; lia.
    - eapply IHua in Heqo; eauto. destruct Heqo as (?&?&?).
      repeat split; eauto.
    - edestruct @interp_dlist_wt as (WTE' & WTLV & WTLA'). 6: now eauto.
      + eapply Forall2_impl. eauto.
        intros; eauto.
        eapply IHua. 7: now eauto.
        simpl.
        clear - H1. revert H1; induction args; simpl; intros; eauto. easy.
        destruct H1; subst; simpl in *; eauto. lia.
        apply IHargs in H. lia.
        all: eauto.
      + auto.
      + auto.
      + auto.
      + simpl. constructor.
      + eapply IHua in Heqo0; eauto.
        intuition; eauto.
        simpl; lia.
        eapply forall2_wt_wt_env in WTLV.
        rewrite rev_involutive in WTLV. auto.
    - eapply IHua in H1; eauto.
  Qed.

End WT.
