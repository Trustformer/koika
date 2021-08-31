Require Import BitsToLists.
Require Import TypeInference.

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
  Variable ext_fn_t: Type.
  Variable reg_t: Type.
  Variable R : reg_t -> type.
  Variable Sigma: ext_fn_t -> ExternalSignature.


  Lemma cast_action'_eq:
    forall
      (p: pos_t) (sig: tsig var_t) (tau1 tau2: type)
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
    forall
      (p: pos_t) (sig: tsig var_t) (tau1 tau2: type)
      (a: TypedSyntax.action pos_t var_t fn_name_t R Sigma sig tau1) a',
    TypeInference.cast_action R Sigma p tau2 a = Success a'
    -> exists p : tau1 = tau2, a' = eq_rect _ _ a _ p.
  Proof.
    intros. unfold TypeInference.cast_action in H.
    eapply cast_action'_eq; eauto.
  Qed.

  Lemma type_action_wt:
    forall ua p sig a,
      type_action R Sigma p sig ua = Success a ->
      wt_action pos_t fn_name_t var_t ext_fn_t reg_t R Sigma sig ua (projT1 a).
  Proof.
    intros ua.
    remember (size_uaction ua).
    revert ua Heqn.
    pattern n.
    eapply Nat.strong_right_induction with (z:=0).
    { red. red. intros. subst. tauto. } 2: lia.
    intros n0 _ Plt ua Heqn. subst.
    assert (Plt':
              forall
                (ua': Syntax.uaction pos_t var_t fn_name_t reg_t ext_fn_t),
                size_uaction ua' < size_uaction ua ->
                forall (p : pos_t) (sig : tsig var_t)
                       (a : {tau : type & TypedSyntax.action pos_t var_t fn_name_t R Sigma sig tau}),
                  type_action R Sigma p sig ua' = Success a ->
                  wt_action pos_t fn_name_t var_t ext_fn_t reg_t R Sigma sig ua' (projT1 a)
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
      edestruct cast_action_eq. eauto. simpl in H. rewrite x.
      econstructor; eauto.
    - repeat destr_in H; inv H. simpl. econstructor.
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
      destruct ufn1; simpl in *.
      + repeat destr_in Heqr0; simpl in Heqr0; inv Heqr0.
        destr_in Heqr1; inv Heqr1. simpl in *. econstructor. eauto.
        simpl in *. econstructor. eauto.
      + repeat destr_in Heqr0; simpl in Heqr0; inv Heqr0; simpl in *.
        econstructor. eauto.
        econstructor. rewrite <- x; eauto.
        econstructor. eauto.
      + repeat destr_in Heqr0; simpl in Heqr0; inv Heqr0; simpl in *;
          repeat destr_in Heqr1; inv Heqr1; simpl in *.
        econstructor. eauto.
        econstructor. eauto.
        econstructor. eauto.
        econstructor. eauto.
        econstructor. eauto.
        econstructor. eauto.
      + repeat destr_in Heqr0; simpl in Heqr0; inv Heqr0; simpl in *;
          repeat destr_in Heqr1; inv Heqr1; simpl in *.
        econstructor. eauto. eauto.
        econstructor. rewrite x in Heqr; simpl in Heqr. eauto. eauto.
      + repeat destr_in Heqr0; simpl in Heqr0; inv Heqr0; simpl in *;
          repeat destr_in Heqr1; inv Heqr1; simpl in *.
        econstructor. eauto.
        econstructor. rewrite x in Heqr; simpl in Heqr. eauto.
    - repeat destr_in H; inv H. simpl.
      eapply IHua in Heqr. 2: simpl; lia. simpl in *.
      eapply IHua in Heqr0. 2: simpl; lia. simpl in *.
      eapply cast_action_eq in Heqr2. destruct Heqr2. subst.
      eapply cast_action_eq in Heqr3. destruct Heqr3. subst.
      destruct s, s0; simpl in *. subst.
      destruct ufn2; simpl in *.
      + inv Heqr1. simpl. econstructor; eauto.
        replace (arg1Sig (PrimSignatures.Sigma2 s1)) with (arg2Sig (PrimSignatures.Sigma2 s1)). eauto.
        rewrite <- H0. simpl. eauto.
      + repeat destr_in Heqr1; simpl in *; inv Heqr1; simpl in *; try (econstructor; eauto; fail).
        * replace (s0 + s) with (s + s0). econstructor; eauto. lia.
      + repeat destr_in Heqr1; simpl in *; inv Heqr1; simpl in *; try (econstructor; eauto; fail).
      + repeat destr_in Heqr1; simpl in *; inv Heqr1; simpl in *; try (econstructor; eauto; fail).
    - repeat destr_in H; inv H. simpl.
      econstructor.
      eapply cast_action_eq in Heqr0. destruct Heqr0. subst. rewrite <- x; eauto.
    - repeat destr_in H; inv H. simpl.
      eapply cast_action_eq in Heqr2. destruct Heqr2. subst.
      eapply IHua in Heqr1. 2: simpl; lia.
      econstructor. 2: rewrite <- x; eauto.

      unfold assert_argtypes in Heqr0.

      Lemma assert_argtypes'_same_length:
        forall {T} sig p (src: T) nexpected fn_name l1 l2 s0,
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
        forall {T} sig p (src: T) nexpected fn_name l1 l2 l3 l4 s0,
          assert_argtypes'
            (sig:=sig)
            (fn_name_t := fn_name_t)
            (pos_t := pos_t)
            (var_t := var_t)
            R Sigma src nexpected fn_name p
                           (l1 ++ l2)
                           (l3 ++ l4) =
          Success s0 ->
          List.length l1 = List.length l3 ->
          List.length l2 = List.length l4 ->
          exists s1 s2,
            assert_argtypes' R Sigma src nexpected fn_name p l1 l3 = Success s1 /\
            assert_argtypes' R Sigma src nexpected fn_name p l2 l4 = Success s2.
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
        forall {T} args sig p s (src: T) nexpected fn_name argspec argpos s0
               (IHua:
               forall ua' : uaction pos_t var_t fn_name_t reg_t ext_fn_t,
                 In ua' args ->
                 forall (p : pos_t) (sig : tsig var_t)
                        (a : {tau : type & TypedSyntax.action pos_t var_t fn_name_t R Sigma sig tau}),
                   type_action R Sigma p sig ua' = Success a ->
                   wt_action pos_t fn_name_t var_t ext_fn_t reg_t R Sigma sig ua' (projT1 a)
               )
               (SAMELEN:           List.length argpos = List.length s)
        ,
          result_list_map (type_action R Sigma p sig) args = Success s ->
          assert_argtypes' R Sigma src nexpected fn_name p
                           (rev argspec)
                           (rev (combine argpos s)) =
          Success s0 ->
          Forall2 (wt_action pos_t fn_name_t var_t ext_fn_t reg_t R Sigma sig) args (map snd argspec).
      Proof.
        induction args; simpl; intros; eauto.
        - inv H. simpl in H0.
          apply assert_argtypes'_same_length in H0. rewrite combine_nil in H0. simpl in H0.
          rewrite rev_length in H0.
          apply length_zero_iff_nil in H0. subst. simpl. constructor.
        - assert ( List.length (rev argspec) = List.length (rev (combine argpos s))).
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

      eapply argtypes_ok.
      4: apply Heqr0.
      3: eauto.
      {
        intros; eapply IHua; eauto. simpl.
        cut (size_uaction ua' <= list_sum (map size_uaction args)). lia.
        clear - H. revert ua' args H. induction args; simpl; intros; eauto. easy.
        destruct H. subst. lia.
        apply IHargs in H. lia.
      }
      rewrite map_length.

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
      erewrite <- result_list_map_length; eauto.
    - repeat destr_in H; inv H. simpl. constructor.  eapply IHua; eauto.
    - inv H.
  Qed.

End WT.
