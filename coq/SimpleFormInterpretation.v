Require Import Coq.Strings.Ascii.
Require Import Koika.Environments Koika.SimpleForm Koika.TypeInference
  Koika.UntypedSemantics.
Require Import Koika.BitsToLists.
From RecordUpdate Require Import RecordSet.
Import RecordSetNotations.
Require Import Sact.
Require Import Coq.Sorting.Sorted.
Require Import Coq.Sorting.Mergesort.

Section SimpleFormInterpretation.
  Context {pos_t reg_t ext_fn_t rule_name_t: Type}.
  Context {reg_t_eq_dec: EqDec reg_t}.
  Context {ext_fn_t_eq_dec: EqDec ext_fn_t}.
  Context {REnv: Env reg_t}.
  Context {TR: reg_t -> type}.

  Context (R: reg_t -> type).
  Context (Sigma: ext_fn_t -> ExternalSignature).

  Definition uact := @daction pos_t string string reg_t ext_fn_t.
  Definition schedule := scheduler pos_t rule_name_t.
  Definition ext_funs_defs :=
    forall f: ext_fn_t, BitsToLists.val -> BitsToLists.val.
  Definition UREnv := REnv.(env_t) (fun _ => BitsToLists.val).

  Context (r: UREnv).
  Context (sigma: ext_funs_defs).

  Definition sact := sact (ext_fn_t:=ext_fn_t).

  Fixpoint contains_vars (e: sact) : bool :=
    match e with
    | SConst _ => false
    | SBinop ufn a1 a2 => orb (contains_vars a1) (contains_vars a2)
    | SUnop ufn a1 => contains_vars a1
    | SVar v => true
    | SIf cond tb fb =>
      orb (contains_vars cond) (orb (contains_vars tb) (contains_vars fb))
    | SExternalCall _ a => contains_vars a
    end.

  Fixpoint replace_all_occurrences_in_sact (ua: sact) (from: nat) (to: val)
  : sact :=
    match ua with
    | SBinop ufn a1 a2 =>
      SBinop
        ufn (replace_all_occurrences_in_sact a1 from to)
        (replace_all_occurrences_in_sact a2 from to)
    | SUnop ufn a1 => SUnop ufn (replace_all_occurrences_in_sact a1 from to)
    | SVar v =>
      if eq_dec v from then SConst to
      else SVar v
    | SIf cond tb fb =>
      SIf
        (replace_all_occurrences_in_sact cond from to)
        (replace_all_occurrences_in_sact tb from to)
        (replace_all_occurrences_in_sact fb from to)
    | SConst c => SConst c
    | SExternalCall ufn a => SExternalCall ufn (replace_all_occurrences_in_sact a from to)
    end.

  Definition replace_all_occurrences_in_vars
    (vars: var_value_map) (from: nat) (to: val)
  : var_value_map :=
    map
      (fun '(reg, (t, ua)) => (reg, (t, replace_all_occurrences_in_sact ua from to)))
      vars.

  (* TODO simplify as well: initial simpl pass then whenever change *)
  Definition simple_form := simple_form (reg_t:=reg_t) (ext_fn_t:=ext_fn_t).
  Definition replace_all_occurrences (sf: simple_form) (from: nat) (to: val)
  : simple_form := {|
    final_values := final_values sf;
    vars := replace_all_occurrences_in_vars (vars sf) from to; |}.

  (* TODO use coq record update here as well *)
  (* TODO variable in environment instead of inlining *)

  Definition remove_by_name_var
             (sf: simple_form) (name: nat) : simple_form :=
    {|
      final_values := final_values sf;
      vars := filter (fun '(n, _) => negb (beq_dec n name)) (vars sf);
    |}.


  Fixpoint eval_sact (vars: var_value_map) (a: sact) (fuel: nat) : option val :=
    match fuel with
    | O => None
    | S fuel =>
        match a with
        | SConst v => Some v
        | SVar v =>
            let/opt2 t, vv := list_assoc vars v in
            eval_sact vars vv fuel
        | SIf c t f =>
            let/opt v := eval_sact vars c fuel in
            match v with
            | Bits [b] =>
                if b then eval_sact vars t fuel
                else eval_sact vars f fuel
            | _ => None
            end
        | SUnop ufn a =>
            let/opt v := eval_sact vars a fuel in
            sigma1 ufn v
        | SBinop ufn a1 a2 =>
            let/opt v1 := eval_sact vars a1 fuel in
            let/opt v2 := eval_sact vars a2 fuel in
            sigma2 ufn v1 v2
        | SExternalCall ufn a =>
            let/opt v := eval_sact vars a fuel in
            Some (sigma ufn v)
        end
    end.

  Fixpoint max_var (vars: var_value_map (ext_fn_t:=ext_fn_t)) :=
    match vars with
      [] => O
    | (n,_)::vars => max n (max_var vars)
    end.

  Lemma vvs_range_max_var:
    forall vars,
      vvs_range vars (S (max_var vars)).
  Proof.
    red; intros.
    apply Sact.list_assoc_in in H.
    red.
    revert x y H.
    induction vars; simpl; intros; eauto. easy.
    destruct H. subst. lia.
    eapply IHvars in H. destr. lia.
  Qed.

  Open Scope nat.

  Lemma eval_sact_more_fuel:
    forall n1 vvs a v n2,
      eval_sact vvs a n1 = Some v ->
      n1 <= n2 ->
      eval_sact vvs a n2 = Some v.
  Proof.
    induction n1; simpl; intros; eauto. easy.
    destruct n2; simpl. lia.
    unfold opt_bind in *.
    assert (n1 <= n2) by lia.
    repeat destr_in H; inv H; eauto.
    - erewrite IHn1; eauto.
    - erewrite IHn1; eauto.
      erewrite IHn1; eauto.
    - erewrite IHn1; eauto.
      simpl. erewrite IHn1; eauto.
    - erewrite IHn1; eauto.
    - erewrite IHn1; eauto.
      erewrite IHn1; eauto.
    - erewrite IHn1; eauto.
  Qed.

  Fixpoint vvs_size (vvs:var_value_map) m : nat :=
    match vvs with
      [] => O
    | (n,(t,a))::vvs =>
        if lt_dec n m then
          size_sact (ext_fn_t:=ext_fn_t) a + vvs_size vvs m
        else vvs_size vvs m
    end.

  Lemma vvs_size_le1:
    forall vvs var n,
      var < n ->
      vvs_size vvs var  <= vvs_size vvs n.
  Proof.
    induction vvs; simpl; intros. easy.
    repeat destr; try lia.
    - clear Heqs0. apply IHvvs in H. lia.
    - apply IHvvs in H. lia.
    - apply IHvvs in H. lia.
  Qed.

  Lemma vvs_size_le2:
    forall vvs a var t n,
      var < n ->
      list_assoc vvs var = Some (t, a) ->
      vvs_size vvs var + size_sact a <= vvs_size vvs n.
  Proof.
    induction vvs; simpl; intros. easy.
    repeat destr_in H0. inv H0.
    - destr. lia. destr.
      cut (vvs_size vvs n0 <= vvs_size vvs n).
      2: eapply vvs_size_le1; eauto. lia.
    - destr.
      generalize (IHvvs _ _ _ _ H H0).
      generalize (vvs_size_le1 vvs _ _ H). intros.
      repeat destr; try lia.
  Qed.

  Lemma interp_sact_eval_sact_aux:
    forall (vvs: var_value_map) (VSV: vvs_smaller_variables vvs),
    forall a v,
      interp_sact (sigma:=sigma) vvs a v ->
      forall n, (forall var, var_in_sact a var -> var < n) ->
      exists m, eval_sact vvs a (m + size_sact a) = Some v /\ m <= n + vvs_size vvs n.
  Proof.
    induction 2; simpl; intros; eauto.
    - destruct (IHinterp_sact var) as (m1 & I1 & LE1). intros; eapply VSV. eauto. auto.
      eexists. split. rewrite Nat.add_1_r. simpl. rewrite H; simpl; eauto.
      assert (var < n). eapply H1. constructor.
      generalize (vvs_size_le2 vvs _ _ _ n H2 H). lia.
    - exists 0; split; simpl; eauto.  lia. 
    - edestruct IHinterp_sact1 as (m1 & I1 & LE1).
      intros; eapply H1. apply var_in_if_cond; eauto.
      edestruct IHinterp_sact2 as (m2 & I2 & LE2).
      intros; eapply H1. destruct b. apply var_in_if_true; eauto. apply var_in_if_false; eauto.
      exists ((max m1 m2)). split.
      rewrite Nat.add_succ_r.
      simpl.
      erewrite eval_sact_more_fuel; eauto. 2: lia. simpl.
      destruct b; eapply eval_sact_more_fuel; eauto. lia. lia. lia.
    - edestruct IHinterp_sact as (m1 & I1 & LE1).
      intros; eapply H1. econstructor; eauto.
      exists m1; rewrite Nat.add_succ_r. simpl. rewrite I1.
      split; simpl; eauto.
    - edestruct IHinterp_sact1 as (m1 & I1 & LE1).
      intros; eapply H2. econstructor; eauto.
      edestruct IHinterp_sact2 as (m2 & I2 & LE2).
      intros; eapply H2. eapply var_in_sact_binop_2; eauto.
      exists (max m1 m2); rewrite Nat.add_succ_r. simpl.
      erewrite eval_sact_more_fuel; eauto. 2: lia. simpl.
      erewrite eval_sact_more_fuel; eauto. 2: lia. simpl.
      split; simpl; eauto. lia.
    - edestruct IHinterp_sact as (m1 & I1 & LE1).
      intros; eapply H0. econstructor; eauto.
      exists m1; rewrite Nat.add_succ_r. simpl. rewrite I1.
      split; simpl; eauto.
  Qed.

  Lemma interp_sact_eval_sact:
    forall (vvs: var_value_map) (VSV: vvs_smaller_variables vvs),
    forall a v t,
      wt_sact (Sigma:=Sigma) vvs a t ->
      interp_sact (sigma:=sigma) vvs a v ->
      eval_sact vvs a (S (max_var vvs) + vvs_size vvs (S (max_var vvs)) + size_sact a) = Some v.
  Proof.
    intros.
    generalize (vvs_range_max_var vvs). intro VR.
    generalize (wt_sact_valid_vars vvs _ VR _ _ H). intro VALID.
    generalize (interp_sact_eval_sact_aux _ VSV a v H0 _ VALID).
    intros (m & EVAL & LE).
    eapply eval_sact_more_fuel. eauto. lia.
  Qed.

  Definition do_eval_sact vvs a :=
    eval_sact vvs a (S (max_var vvs) + vvs_size vvs (S (max_var vvs)) + size_sact a).

  Lemma interp_sact_do_eval_sact:
    forall (vvs: var_value_map) (VSV: vvs_smaller_variables vvs),
    forall a v t,
      wt_sact (Sigma:=Sigma) vvs a t ->
      interp_sact (sigma:=sigma) vvs a v ->
      do_eval_sact vvs a = Some v.
  Proof.
    intros.
    eapply interp_sact_eval_sact; eauto.
  Qed.

  Lemma eval_sact_interp_sact:
    forall vvs fuel a v,
      eval_sact vvs a fuel = Some v ->
      interp_sact (sigma:=sigma) vvs a v.
  Proof.
    induction fuel; simpl; intros; eauto. easy.
    unfold opt_bind in H; repeat destr_in H; inv H.
    - econstructor; eauto.
    - econstructor; eauto.
    - econstructor; eauto.
    - econstructor; eauto.
    - econstructor; eauto.
    - econstructor; eauto.
    - econstructor; eauto.
  Qed.
  
  Lemma do_eval_sact_interp_sact:
    forall vvs a v,
      do_eval_sact vvs a = Some v ->
      interp_sact (sigma:=sigma) vvs a v.
  Proof.
    intros; eapply eval_sact_interp_sact; eauto.
  Qed.

  Fixpoint eval_sact_no_vars (a: sact) : option val :=
    match a with
    | SConst v => Some v
    | SVar v => None
    | SIf c t f =>
        let/opt v := eval_sact_no_vars c in
        match v with
        | Bits [b] =>
            if b then eval_sact_no_vars t
            else eval_sact_no_vars f
        | _ => None
        end
    | SUnop ufn a =>
        let/opt v := eval_sact_no_vars a in
        sigma1 ufn v
    | SBinop ufn a1 a2 =>
        let/opt v1 := eval_sact_no_vars a1 in
        let/opt v2 := eval_sact_no_vars a2 in
        sigma2 ufn v1 v2
    | SExternalCall ufn a =>
        let/opt v := eval_sact_no_vars a in
        Some (sigma ufn v)
    end.
  
  Lemma list_assoc_filter:
    forall {K V: Type} {eqdec: EqDec K} (l: list (K*V)) f k,
      (forall v, f (k,v) = true) ->
      list_assoc l k = list_assoc (filter f l) k.
  Proof.
    induction l; simpl; intros; eauto.
    repeat destr.
    - subst. simpl. rewrite eq_dec_refl. reflexivity.
    - subst. simpl. destr. eauto.
    - eauto.
  Qed.
  
  Lemma interp_sact_same_below:
    forall vvs1 vvs2 a res n (VSV: vvs_smaller_variables vvs1),
      (forall v, var_in_sact a v -> v < n) ->
      (forall x, x < n -> list_assoc vvs1 x = list_assoc vvs2 x) ->
      interp_sact (sigma:=sigma) vvs1 a res -> interp_sact (sigma:=sigma) vvs2 a res.
  Proof.
    induction 4; simpl; intros; eauto.
    - assert (var < n). apply H. constructor.
      econstructor; eauto. erewrite <- H0; eauto.
      apply IHinterp_sact. intros; eapply VSV in H1. apply H1 in H4. red in H4. lia.
    - constructor.
    - econstructor. eapply IHinterp_sact1. intros; eapply H; eapply var_in_if_cond; eauto.
      eapply IHinterp_sact2. intros; eapply H.
      destr_in H1. eapply var_in_if_true; eauto. eapply var_in_if_false; eauto.
    - econstructor. eapply IHinterp_sact. intros; eapply H; eapply var_in_sact_unop; eauto. auto.
    - econstructor. eapply IHinterp_sact1. intros; eapply H; eapply var_in_sact_binop_1; eauto.
      eapply IHinterp_sact2. intros; eapply H; eapply var_in_sact_binop_2; eauto. auto.
    - econstructor. eapply IHinterp_sact. intros; eapply H; eapply var_in_sact_external; eauto.
  Qed.

  Lemma map_filter:
    forall {A: Type} (f: A -> A) g,
      (forall x, g x = g (f x)) ->
      forall l,
        map f (filter g l) = filter g (map f l).
  Proof.
    induction l; simpl; intros; eauto.
    rewrite <- H. destruct (g a). simpl. congruence. auto.
  Qed.

  Lemma list_assoc_map:
    forall {K V: Type} {eqdec: EqDec K} (f: K*V -> K*V) (g: V -> V)
           (F: forall k1 v1, f (k1,v1) = (k1, g v1))
           l k,
      list_assoc (map f l) k = option_map g (list_assoc l k).
  Proof.
    induction l; simpl; intros; eauto.
    destruct a. rewrite F. destr. subst. simpl. reflexivity.
  Qed.
  
  Lemma interp_sact_replace:
    forall vvs var v' ,
      interp_sact (sigma:=sigma) vvs (SVar var) v' ->
      forall a res,
        interp_sact (sigma:=sigma) vvs a res ->
        interp_sact (sigma:=sigma) vvs (replace_all_occurrences_in_sact a var v') res.
  Proof.
    induction 2; simpl; intros; eauto.
    - destr.
      + subst. inv H. rewrite H0 in H3. inv H3.
        exploit (interp_sact_determ (ext_fn_t:=ext_fn_t) (sigma:=sigma)). apply H1. apply H4.
        intros ->; econstructor.
      + econstructor; eauto.
    - econstructor.
    - econstructor; eauto.
      destruct b; eauto.
    - econstructor; eauto.
    - econstructor; eauto.
    - econstructor; eauto.
  Qed.

  Lemma interp_sact_replace_inv:
    forall vvs (VSV: vvs_smaller_variables vvs) var v' ,
      interp_sact (sigma:=sigma) vvs (SVar var) v' ->
      forall a n (BELOW: forall v, var_in_sact a v -> v < n) res,
        interp_sact (sigma:=sigma) vvs (replace_all_occurrences_in_sact a var v') res ->
        interp_sact (sigma:=sigma) vvs a res.
  Proof.
    intros vvs VSV var v' INTvar a n.
    change n with (projT1 (existT (fun _ => sact) n a)).
    change a with (projT2 (existT (fun _ => sact) n a)) at 1 3 4.
    generalize (existT (fun _ => sact) n a).
    clear n a. intro s. pattern s.
    eapply well_founded_induction.
    apply wf_order_sact. clear s.
    intros (n1 & a) IH. simpl.
    intros BELOW res INTres.
    destruct a; simpl in *.
    - destr_in INTres.
      + subst. inv INTres. eauto.
      + eauto.
    - inv INTres; econstructor.
    - inv INTres.
      econstructor.
      eapply (IH (existT _ n1 a1)); eauto. constructor 2. simpl; lia.
      simpl; intros. eapply BELOW. eapply var_in_if_cond; eauto.
      eapply (IH (existT _ n1 (if b then a2 else a3))); eauto. constructor 2. destruct b; simpl; lia.
      simpl; intros. eapply BELOW. destruct b.
      eapply var_in_if_true; eauto. eapply var_in_if_false; eauto. simpl.
      destruct b; eauto.
    - inv INTres; econstructor; eauto.
      eapply (IH (existT _ n1 a)); eauto. constructor 2. simpl; lia.
      simpl; intros. eapply BELOW. eapply var_in_sact_unop; eauto.
    - inv INTres; econstructor; eauto.
      eapply (IH (existT _ n1 a1)); eauto. constructor 2. simpl; lia.
      simpl; intros. eapply BELOW. eapply var_in_sact_binop_1; eauto.
      eapply (IH (existT _ n1 a2)); eauto. constructor 2. simpl; lia.
      simpl; intros. eapply BELOW. eapply var_in_sact_binop_2; eauto.
    - inv INTres; econstructor; eauto.
      eapply (IH (existT _ n1 a)); eauto. constructor 2. simpl; lia.
      simpl; intros. eapply BELOW. eapply var_in_sact_external; eauto.
  Qed.

  Lemma interp_sact_replace_iff:
    forall vvs (VSV: vvs_smaller_variables vvs) var v' ,
      interp_sact (sigma:=sigma) vvs (SVar var) v' ->
      forall a t (WT: wt_sact (Sigma:=Sigma) vvs a t) res,
        interp_sact (sigma:=sigma) vvs (replace_all_occurrences_in_sact a var v') res <->
        interp_sact (sigma:=sigma) vvs a res.
  Proof.
    split; intros.
    - eapply interp_sact_replace_inv; eauto.
      eapply wt_sact_valid_vars. 2: eauto.
      apply vvs_range_max_var.
    - eapply interp_sact_replace; eauto.
  Qed.

  Lemma interp_sact_replace_one_variable:
    forall vvs (VSV: vvs_smaller_variables vvs) var v' ,
      interp_sact (sigma:=sigma) vvs (SVar var) v' ->
      forall a n,
        (forall v, var_in_sact a v -> v < n) ->
        forall res,
          interp_sact (sigma:=sigma) vvs a res ->
          interp_sact (sigma:=sigma)
                      (replace_all_occurrences_in_vars
                         (filter (fun '(n, _) => negb (beq_dec n var)) vvs) var v')
                      (replace_all_occurrences_in_sact a var v') res.
  Proof.
    intros vvs VSV var v' INTvar.
    intros a n.
    change n with (projT1 (existT (fun _ => sact) n a)).
    change a with (projT2 (existT (fun _ => sact) n a)) at 1 3 4.
    generalize (existT (fun _ => sact) n a).
    clear n a. intro s. pattern s.
    eapply well_founded_induction.
    apply wf_order_sact. clear s.
    intros (n1 & a) IH. simpl.
    intros BELOW res INTres.
    inv INTres; simpl.
    - destr.
      + subst. inv INTvar. rewrite H2 in H. inv H.
        exploit (interp_sact_determ (sigma:=sigma) (ext_fn_t:=ext_fn_t)).
        apply H3. apply H0. intros; subst. constructor.
      + econstructor. unfold replace_all_occurrences_in_vars.
        rewrite list_assoc_map with (g:=fun '(t,a) => (t, replace_all_occurrences_in_sact a var v')).
        rewrite <- list_assoc_filter.
        2: intros; rewrite negb_true_iff, beq_dec_false_iff; auto.
        2: intros; repeat destr; eauto.
        setoid_rewrite H. simpl. eauto.
        eapply (IH (existT _ var0 a0)).
        constructor. eapply BELOW. constructor.
        simpl. intros; eapply VSV; eauto.
        simpl. auto.
    - constructor.
    - econstructor.
      eapply (IH (existT _ n1 c)). constructor 2. simpl; lia.
      simpl. intros; eapply BELOW. apply var_in_if_cond; eauto. simpl. eauto.
      trim (IH (existT _ n1 (if b then t else f))). constructor 2. destruct b; simpl; lia.
      simpl in IH.
      trim IH. intros; eapply BELOW.
      destruct b. eapply var_in_if_true; eauto. eapply var_in_if_false; eauto.
      specialize (IH _ H0).
      destr; eauto.
    - econstructor.
      eapply (IH (existT _ n1 a0)). constructor 2. simpl; lia.
      simpl. intros; eapply BELOW. apply var_in_sact_unop; eauto. simpl. eauto.
      auto.
    - econstructor.
      eapply (IH (existT _ n1 a1)). constructor 2. simpl; lia.
      simpl. intros; eapply BELOW. apply var_in_sact_binop_1; eauto. simpl. eauto.
      eapply (IH (existT _ n1 a2)). constructor 2. simpl; lia.
      simpl. intros; eapply BELOW. apply var_in_sact_binop_2; eauto. simpl. eauto. auto.
    - econstructor.
      eapply (IH (existT _ n1 a0)). constructor 2. simpl; lia.
      simpl. intros; eapply BELOW. apply var_in_sact_external; eauto. simpl. eauto.
  Qed.

  Lemma interp_sact_replace_one:
    forall vvs (VSV: vvs_smaller_variables vvs) var v' ,
      interp_sact (sigma:=sigma) vvs (SVar var) v' ->
      forall a n,
        (forall v, var_in_sact a v -> v < n) ->
        forall res,
          interp_sact (sigma:=sigma) vvs a res ->
          interp_sact (sigma:=sigma)
                      (replace_all_occurrences_in_vars vvs var v')
                      (replace_all_occurrences_in_sact a var v') res.
  Proof.
    intros vvs VSV var v' INTvar.
    intros a n.
    change n with (projT1 (existT (fun _ => sact) n a)).
    change a with (projT2 (existT (fun _ => sact) n a)) at 1 3 4.
    generalize (existT (fun _ => sact) n a).
    clear n a. intro s. pattern s.
    eapply well_founded_induction.
    apply wf_order_sact. clear s.
    intros (n1 & a) IH. simpl.
    intros BELOW res INTres.
    inv INTres; simpl.
    - destr.
      + subst. inv INTvar. rewrite H2 in H. inv H.
        exploit (interp_sact_determ (sigma:=sigma) (ext_fn_t:=ext_fn_t)).
        apply H3. apply H0. intros; subst. constructor.
      + econstructor. unfold replace_all_occurrences_in_vars.
        rewrite list_assoc_map with (g:=fun '(t,a) => (t, replace_all_occurrences_in_sact a var v')).
        2: intros; repeat destr; eauto.
        setoid_rewrite H. simpl. eauto.
        eapply (IH (existT _ var0 a0)).
        constructor. eapply BELOW. constructor.
        simpl. intros; eapply VSV; eauto.
        simpl. auto.
    - constructor.
    - econstructor.
      eapply (IH (existT _ n1 c)). constructor 2. simpl; lia.
      simpl. intros; eapply BELOW. apply var_in_if_cond; eauto. simpl. eauto.
      trim (IH (existT _ n1 (if b then t else f))). constructor 2. destruct b; simpl; lia.
      simpl in IH.
      trim IH. intros; eapply BELOW.
      destruct b. eapply var_in_if_true; eauto. eapply var_in_if_false; eauto.
      specialize (IH _ H0).
      destr; eauto.
    - econstructor.
      eapply (IH (existT _ n1 a0)). constructor 2. simpl; lia.
      simpl. intros; eapply BELOW. apply var_in_sact_unop; eauto. simpl. eauto.
      auto.
    - econstructor.
      eapply (IH (existT _ n1 a1)). constructor 2. simpl; lia.
      simpl. intros; eapply BELOW. apply var_in_sact_binop_1; eauto. simpl. eauto.
      eapply (IH (existT _ n1 a2)). constructor 2. simpl; lia.
      simpl. intros; eapply BELOW. apply var_in_sact_binop_2; eauto. simpl. eauto. auto.
    - econstructor.
      eapply (IH (existT _ n1 a0)). constructor 2. simpl; lia.
      simpl. intros; eapply BELOW. apply var_in_sact_external; eauto. simpl. eauto.
  Qed.
  
  Lemma interp_eval:
    forall vvs vvs' a b
           (VSV1: vvs_smaller_variables vvs)
           (VSV2: vvs_smaller_variables vvs') ta tb
           (WTa: wt_sact (Sigma:=Sigma) vvs a ta)
           (WTb: wt_sact (Sigma:=Sigma) vvs' b tb)
    ,
      (exists m, forall n, n >= m ->
                           eval_sact vvs a n = eval_sact vvs' b n) ->
      (forall res, interp_sact (sigma:=sigma) vvs a res -> interp_sact (sigma:=sigma) vvs' b res).
  Proof.
    intros.
    destruct H.
    eapply interp_sact_eval_sact in H0; eauto.
    eapply eval_sact_more_fuel with (n2:=max x _) in H0.
    2: apply Nat.le_max_r.
    rewrite H in H0. 2: lia.
    eapply eval_sact_interp_sact; eauto.
  Qed.

  Lemma interp_eval_iff:
    forall vvs vvs' a b
           (VSV1: vvs_smaller_variables vvs)
           (VSV2: vvs_smaller_variables vvs') ta tb
           (WTa: wt_sact (Sigma:=Sigma) vvs a ta)
           (WTb: wt_sact (Sigma:=Sigma) vvs' b tb)
    ,
      (exists m, forall n, n >= m ->
                           eval_sact vvs a n = eval_sact vvs' b n) ->
      (forall res, interp_sact (sigma:=sigma) vvs a res <-> interp_sact (sigma:=sigma) vvs' b res).
  Proof.
    intros vvs vvs' a b VSV1 VSV2 ta tb WTa WTb (m & EQ) res.
    split; intros.
    - eapply interp_eval. 6: eauto. all: eauto.
    - eapply interp_eval. 6: eauto. all: eauto.
      exists m; intros; eauto. rewrite EQ; auto.
  Qed.

  Lemma eval_sact_no_vars_interp:
    forall vvs s v
           (EVAL: eval_sact_no_vars s = Some v),
      interp_sact (sigma:=sigma) vvs s v.
  Proof.
    induction s; simpl; intros; eauto; unfold opt_bind in EVAL; repeat destr_in EVAL; inv EVAL.
    - econstructor; eauto.
    - econstructor; eauto.
    - econstructor; eauto.
    - econstructor; eauto.
    - econstructor; eauto.
    - econstructor; eauto.
  Qed.

  Context {wt_sigma: forall ufn vc,
      wt_val (arg1Sig (Sigma ufn)) vc ->
      wt_val (retSig (Sigma ufn)) (sigma ufn vc)}.

  Lemma var_in_sact_replace:
    forall a n v x,
      var_in_sact (replace_all_occurrences_in_sact a n v) x ->
      var_in_sact a x.
  Proof.
    induction a; simpl; intros; eauto.
    - destr_in H; inv H. constructor.
    - inv H. eapply var_in_if_cond; eauto.
      eapply var_in_if_true; eauto.
      eapply var_in_if_false; eauto.
    - inv H. eapply var_in_sact_unop; eauto.
    - inv H. eapply var_in_sact_binop_1; eauto.
      eapply var_in_sact_binop_2; eauto.
    - inv H. eapply var_in_sact_external; eauto.
  Qed.

  Lemma vvs_smaller_variables_replace:
    forall vvs n v,
      vvs_smaller_variables vvs ->
      vvs_smaller_variables (replace_all_occurrences_in_vars vvs n v).
  Proof.
    unfold vvs_smaller_variables; intros.
    setoid_rewrite list_assoc_map with (g:= fun '(t,a) => (t, replace_all_occurrences_in_sact a n v)) in H0.
    2: intros; repeat destr.
    unfold option_map in H0; repeat destr_in H0; inv H0.
    eapply var_in_sact_replace in H1; eauto.
  Qed.

  Lemma wt_sact_replace:
    forall vvs a t n v t1,
      wt_sact (Sigma:=Sigma) vvs a t ->
      wt_sact (Sigma:=Sigma) vvs (SVar n) t1 ->
      wt_val t1 v ->
      wt_sact (Sigma:=Sigma) vvs (replace_all_occurrences_in_sact a n v) t.
  Proof.
    induction 1; simpl; intros; eauto.
    - destr.
      + subst. inv H0. rewrite H in H3; inv H3. econstructor; eauto.
      + econstructor. eauto.
    - inv H0. econstructor. eauto.
    - econstructor; eauto.
    - econstructor; eauto.
    - econstructor; eauto.
    - econstructor; eauto.
  Qed.

  Lemma wt_sact_replace_vars:
    forall vvs a t n v t1,
      wt_sact (Sigma:=Sigma) vvs a t ->
      wt_sact (Sigma:=Sigma) vvs (SVar n) t1 ->
      wt_val t1 v ->
      wt_sact (Sigma:=Sigma) (replace_all_occurrences_in_vars vvs n v) (replace_all_occurrences_in_sact a n v) t.
  Proof.
    induction 1; simpl; intros; eauto.
    - destr.
      + subst. inv H0. rewrite H in H3; inv H3. econstructor; eauto.
      + econstructor.
        setoid_rewrite list_assoc_map with (g:= fun '(t,a) => (t, replace_all_occurrences_in_sact a n v)). setoid_rewrite H. simpl; eauto. intros; repeat destr.
    - inv H0. econstructor. eauto.
    - econstructor; eauto.
    - econstructor; eauto.
    - econstructor; eauto.
    - econstructor; eauto.
  Qed.

  Lemma wt_sact_replace_vars':
    forall vvs a t n v t1,
      wt_sact (Sigma:=Sigma) vvs a t ->
      wt_sact (Sigma:=Sigma) vvs (SVar n) t1 ->
      wt_val t1 v ->
      wt_sact (Sigma:=Sigma) (replace_all_occurrences_in_vars vvs n v) a t.
  Proof.
    induction 1; simpl; intros; eauto.
    - econstructor.
      setoid_rewrite list_assoc_map with (g:= fun '(t,a) => (t, replace_all_occurrences_in_sact a n v)).
      setoid_rewrite H. simpl; eauto. intros; repeat destr.
    - inv H0. econstructor. eauto.
    - econstructor; eauto.
    - econstructor; eauto.
    - econstructor; eauto.
    - econstructor; eauto.
  Qed.

  Lemma wt_vvs_replace:
    forall vvs n v t1,
      wt_vvs (Sigma:=Sigma) vvs ->
      wt_sact (Sigma:=Sigma) vvs (SVar n) t1 ->
      wt_val t1 v ->
      wt_vvs (Sigma:=Sigma) (replace_all_occurrences_in_vars vvs n v).
  Proof.
    unfold wt_vvs; intros.
    setoid_rewrite list_assoc_map with (g:= fun '(t,a) => (t, replace_all_occurrences_in_sact a n v)) in H2.
    2: intros; repeat destr.
    unfold option_map in H2; repeat destr_in H2; inv H2.
    eapply wt_sact_replace_vars; eauto.
  Qed.

  Lemma eval_sact_no_vars_wt:
    forall vvs s t
           (WT: wt_sact (Sigma:=Sigma) vvs s t)
           v
           (EVAL: eval_sact_no_vars s = Some v),
      wt_val t v.
  Proof.
    induction 1; simpl; intros; unfold opt_bind in EVAL; repeat destr_in EVAL; inv EVAL;
      try now (eauto).
    eapply Wt.wt_unop_sigma1; eauto.
    eapply Wt.wt_binop_sigma1; eauto.
  Qed.

  Definition simplify_var (sf: simple_form) var :=
    match list_assoc (vars sf) var with
      Some (t, a) =>
           match eval_sact_no_vars a with
             Some v => (replace_all_occurrences sf var v, [(var,v)])
           | None => (sf, [])
           end
    | _ => (sf, [])
    end.

  Lemma var_not_in_sact_replace:
    forall s0 v0 v,
      ~ var_in_sact (replace_all_occurrences_in_sact s0 v0 v) v0.
  Proof.
    induction s0; simpl; intros; eauto.
    - destr; inversion 1. congruence.
    - inversion 1.
    - inversion 1; subst; intuition eauto.
    - inversion 1; subst; intuition eauto.
    - inversion 1; subst; intuition eauto.
    - inversion 1; subst; intuition eauto.
  Qed.

  Lemma simplify_var_correct:
    forall sf var sf' l
           (SIMP: simplify_var sf var = (sf', l))
           (VSV: vvs_smaller_variables (vars sf))
           (WT: wt_vvs (Sigma:=Sigma) (vars sf)),
      Forall (fun '(var,v) => interp_sact (sigma:=sigma) (vars sf') (SVar var) v) l
      /\ vvs_smaller_variables (vars sf')
      /\ wt_vvs (Sigma:=Sigma) (vars sf')
      /\ NoDup (map fst l)
      /\ (forall a res t,
             wt_sact (Sigma:=Sigma) (vars sf) a t ->
             interp_sact (sigma:=sigma) (vars sf) a res ->
             interp_sact (sigma:=sigma) (vars sf') a res)
  /\ (forall x t y res,
              list_assoc (vars sf) x = Some (t,y) ->
              interp_sact (sigma:=sigma) (vars sf) y res ->
              (exists y' ,
                  list_assoc (vars sf') x = Some (t,y') /\
                    interp_sact (sigma:=sigma) (vars sf') y' res)
     ) /\
  (forall x t y v, list_assoc (vars sf') x = Some (t,y) ->
                   var_in_sact y v -> ~ In v (map fst l)) /\
        (forall x t y,
            list_assoc (vars sf') x = Some (t, y) ->
            exists y' ,
              list_assoc (vars sf) x = Some (t, y') /\
                forall v, var_in_sact y v -> var_in_sact y' v).
  Proof.
    unfold simplify_var. intros. repeat destr_in SIMP; inv SIMP; eauto.
    assert (VSV': vvs_smaller_variables (vars (replace_all_occurrences sf var v))).
    eapply vvs_smaller_variables_replace; now eauto.
    assert (WTVVS':  wt_vvs (Sigma:=Sigma) (vars (replace_all_occurrences sf var v))).
    {
      eapply wt_vvs_replace; eauto.
      econstructor. eauto.
      eapply eval_sact_no_vars_wt; eauto.
    }
    repeat refine (conj _ _); eauto.
    - repeat constructor.
      simpl.
      erewrite <- interp_sact_replace_iff; eauto.
      eapply interp_sact_replace_one; eauto.
      + econstructor. eauto. eapply eval_sact_no_vars_interp; eauto.
      + intros. eapply wt_sact_valid_vars. 3: eauto. 2: econstructor; eauto.
        apply vvs_range_max_var.
      + econstructor. eauto.
        eapply eval_sact_no_vars_interp; eauto.
      + econstructor.
        setoid_rewrite list_assoc_map with (g:= fun '(t,a) => (t, replace_all_occurrences_in_sact a var v)).
        setoid_rewrite Heqo. simpl; eauto.
        intros; repeat destr.
        eapply interp_sact_replace_one. eauto.
        econstructor. eauto.
        eapply eval_sact_no_vars_interp; eauto.
        eapply wt_sact_valid_vars. 2: eapply (WT var). apply vvs_range_max_var.
        eauto.
        eapply eval_sact_no_vars_interp; eauto.
      + econstructor.
        setoid_rewrite list_assoc_map with (g:= fun '(t,a) => (t, replace_all_occurrences_in_sact a var v)).
        setoid_rewrite Heqo. simpl; eauto.
        intros; repeat destr.
        Unshelve. exact Sigma.
    - simpl. constructor. easy. constructor.
    - simpl. intros.
      erewrite <- interp_sact_replace_iff; eauto.
      eapply interp_sact_replace_one; eauto.
      + econstructor. eauto. eapply eval_sact_no_vars_interp; eauto.
      + intros. eapply wt_sact_valid_vars. 3: eauto. 2: eauto.
        apply vvs_range_max_var.
      + econstructor.
        setoid_rewrite list_assoc_map with (g:= fun '(t,a) => (t, replace_all_occurrences_in_sact a var v)).
        setoid_rewrite Heqo. simpl; eauto.
        intros; repeat destr.
        eapply interp_sact_replace_one. eauto.
        econstructor. eauto.
        eapply eval_sact_no_vars_interp; eauto.
        eapply wt_sact_valid_vars. 2: eapply (WT var). apply vvs_range_max_var.
        eauto.
        eapply eval_sact_no_vars_interp; eauto.
      + eapply wt_sact_replace_vars'. eauto. econstructor; eauto.
        eapply eval_sact_no_vars_wt; eauto.
    - simpl. intros.
      setoid_rewrite list_assoc_map with (g:= fun '(t,a) => (t, replace_all_occurrences_in_sact a var v)).
      setoid_rewrite H. simpl; eauto.
      eexists; split; eauto.
      eapply interp_sact_replace_one; eauto.
      + econstructor. eauto. eapply eval_sact_no_vars_interp; eauto.
      + intros. eapply wt_sact_valid_vars. 3: eauto. 2: eauto.
        apply vvs_range_max_var.
      + intros; repeat destr.
    - simpl.
      setoid_rewrite list_assoc_map with (g:= fun '(t,a) => (t, replace_all_occurrences_in_sact a var v)). 2: intros; destr.
      unfold option_map; intros x t0 y v0 OM; repeat destr_in OM; inv OM.
      intros VIS [EQ|[]]. subst.

      eapply var_not_in_sact_replace; eauto.
    - simpl. intros x t0 y.
      setoid_rewrite list_assoc_map with (g:= fun '(t,a) => (t, replace_all_occurrences_in_sact a var v)). 2: intros; destr.
      unfold option_map; intros OM; repeat destr_in OM; inv OM.
      setoid_rewrite Heqo1. eexists; split; eauto.
      eapply var_in_sact_replace; eauto.
    - repeat refine (conj _ _); eauto. constructor.
    - repeat refine (conj _ _); eauto. constructor.
  Qed.


  Lemma eval_sact_no_vars_succeeds:
    forall a (NoVars: forall v, ~ var_in_sact a v)
           vvs t (WTa: wt_sact (Sigma:=Sigma) vvs a t),
    exists r, eval_sact_no_vars a = Some r.
  Proof.
    induction a; simpl; intros; eauto.
    - elim (NoVars var). constructor.
    - inv WTa.
      edestruct IHa1 as (r1 & EQ1); eauto.
      intros v VIS; eapply NoVars; eauto. apply var_in_if_cond; eauto.
      rewrite EQ1. simpl.
      exploit eval_sact_no_vars_wt. 2: eauto. eauto. intro WTc.
      apply wt_val_bool in WTc. destruct WTc; subst.
      destr. eapply IHa2; eauto.
      intros v VIS; eapply NoVars; eauto. apply var_in_if_true; eauto.
      eapply IHa3; eauto.
      intros v VIS; eapply NoVars; eauto. apply var_in_if_false; eauto.
    - inv WTa.
      edestruct IHa as (r1 & EQ1); eauto.
      intros v VIS; eapply NoVars; eauto. apply var_in_sact_unop; eauto.
      rewrite EQ1. simpl.
      eapply wt_unop_interp; eauto.
      eapply eval_sact_no_vars_wt; eauto.
    - inv WTa.
      edestruct IHa1 as (r1 & EQ1); eauto.
      intros v VIS; eapply NoVars; eauto. apply var_in_sact_binop_1; eauto.
      rewrite EQ1. simpl.
      edestruct IHa2 as (r2 & EQ2); eauto.
      intros v VIS; eapply NoVars; eauto. apply var_in_sact_binop_2; eauto.
      rewrite EQ2. simpl.
      eapply wt_binop_interp; eauto.
      eapply eval_sact_no_vars_wt; eauto.
      eapply eval_sact_no_vars_wt; eauto.
    - inv WTa.
      edestruct IHa as (r1 & EQ1); eauto.
      intros v VIS; eapply NoVars; eauto. apply var_in_sact_external; eauto.
      rewrite EQ1. simpl. eauto.
  Qed.


  Lemma simplify_vars_preserves:
    forall (lvars: list nat) sf l sf' l'
           (FL: fold_left
                  (fun '(sf, l) var =>
                     let '(sf, l1) := simplify_var sf var in
                     (sf,l1++l)) lvars (sf, l) = (sf', l'))
           (WTV: wt_vvs (Sigma:=Sigma) (vars sf))
           (VSV: vvs_smaller_variables (vars sf))
           (NDlvars: NoDup lvars)
           (ND: NoDup (map fst l))
           (DISJ: forall x, In x lvars -> ~ In x (map fst l))
           (NIV: (forall x t y v, list_assoc (vars sf) x = Some (t,y) ->
                                  var_in_sact y v -> ~ In v (map fst l))),
      vvs_smaller_variables (vars sf') /\
        wt_vvs (Sigma:=Sigma) (vars sf') /\ (incl l l') /\ NoDup (map fst l')
      /\ (forall x t y v, list_assoc (vars sf') x = Some (t,y) ->
                          var_in_sact y v -> ~ In v (map fst l')).
  Proof.
    induction lvars; simpl; intros; eauto.
    - inv FL. repeat refine (conj _ _); eauto. easy.
    - repeat destr_in FL.
      edestruct simplify_var_correct as (INT & VSV2 & WT2 & ND2 & INTERP2 & INTERP3 & NAV1 & VIS1); eauto.
      edestruct (IHlvars _ _ _ _ FL) as (VSV3 & WTV3 & INCL & ND3 & NIV2); auto.
      inv NDlvars; eauto.
      {
        rewrite map_app.
        unfold simplify_var in Heqp.
        repeat destr_in Heqp; inv Heqp; simpl; eauto.
        constructor; eauto.
      }
      {
        intros x IN IN2.
        rewrite map_app, in_app_iff in IN2.
        unfold simplify_var in Heqp.
        repeat destr_in Heqp; inv Heqp; simpl in IN2; intuition eauto.
        subst. inv NDlvars; eauto.
      }
      intros.
      specialize (NAV1 _ _ _ _ H H0).
      rewrite map_app. rewrite in_app_iff. intros [IN|IN]; eauto.
      edestruct VIS1 as (y' & GET2 & IMPL). apply H.
      eapply NIV in IN; eauto.
      split; auto. split; auto. split; auto.
      apply incl_app_inv in INCL. apply INCL.
  Qed.

  Lemma simplify_vars_correct:
    forall (lvars: list nat) sf l sf' l'
           (FL: fold_left
                  (fun '(sf, l) var =>
                     let '(sf, l1) := simplify_var sf var in
                     (sf,l1++l)) lvars (sf, l) = (sf', l'))
           (SORTED: Sorted lt lvars)
           (VARS_EXIST: Forall (fun v => exists a t, list_assoc (vars sf) v = Some (t,a)) lvars)
           (WTV: wt_vvs (Sigma:=Sigma) (vars sf))
           (ACC: Forall (fun '(var, v) => interp_sact (sigma:=sigma) (vars sf) (SVar var) v) l)
           (VSV: vvs_smaller_variables (vars sf))
           (NOvarsl: forall x t y v,
               list_assoc (vars sf) x = Some (t,y) ->
               var_in_sact y v -> ~ In v (map fst l) /\ In v lvars)
    ,
      (forall x t y res,
          list_assoc (vars sf) x = Some (t,y) ->
          interp_sact (sigma:=sigma) (vars sf) y res ->
          (exists y' ,
              list_assoc (vars sf') x = Some (t,y') /\
                interp_sact (sigma:=sigma) (vars sf') y' res)
      ) /\
        vvs_smaller_variables (vars sf') /\
        wt_vvs (Sigma:=Sigma) (vars sf') /\
        Forall (fun '(var, v) => interp_sact (sigma:=sigma) (vars sf') (SVar var) v) l' /\
        (forall x t y v, list_assoc (vars sf') x = Some (t,y) ->
                         var_in_sact y v -> ~ In v (map fst l'))
      /\ (incl l l')
  /\ (forall x, In x lvars -> exists v, In (x, v) l').
  Proof.
    induction lvars; simpl; intros; eauto.
    - inv FL. repeat refine (conj _ _); eauto.
      intros x t y v GET VIS; eapply NOvarsl in GET; eauto. destruct GET; easy.
      easy. easy.
    - repeat destr_in FL.
      edestruct simplify_var_correct as (INT & VSV2 & WT2 & ND2 & INTERP2 & INTERP3 & NAV1 & VIS1); eauto.
      edestruct (IHlvars _ _ _ _ FL) as (LGROWS & VSV3 & WT3 & INTERPl & NAV2 & INCL & INl'); auto.
      * inv SORTED; auto.
      * inv VARS_EXIST. rewrite Forall_forall in H2 |- *. intros x IN.
        specialize (H2 _ IN).
        destruct H2 as (aa & t & GET).
        move Heqp at bottom. unfold simplify_var in Heqp.
        repeat destr_in Heqp; inv Heqp; eauto.
        simpl. unfold replace_all_occurrences_in_vars.
        setoid_rewrite list_assoc_map with (g:= fun '(t,a0) => (t, replace_all_occurrences_in_sact a0 a v)). 2: intros; destr.
        setoid_rewrite GET. simpl. do 2 eexists; eauto.
      * eapply Forall_app. split. eauto.
        rewrite Forall_forall in ACC |- *. intros (var & v) IN.
        specialize (ACC _ IN). simpl in ACC.
        inv ACC. 
        eapply INTERP2. econstructor; eauto. econstructor; eauto.
      * intros x t y v GET VIS.
        split.
        -- intro IN. rewrite map_app in IN. rewrite in_app_iff in IN.
           destruct IN; eauto. eapply NAV1; eauto.
           edestruct VIS1 as (y' & GET2 & IMPL). eauto.
           apply IMPL in VIS.
           eapply NOvarsl; eauto.
        -- edestruct (VIS1 _ _ _ GET) as (y'& GET' & VISS).
           destruct (NOvarsl _ _ _ _ GET' (VISS _ VIS)) as (? & [EQ|IN]); eauto.
           exfalso. subst.
           move Heqp at bottom. unfold simplify_var in Heqp. inv VARS_EXIST.
           destruct H2 as (? & ? & GETv). rewrite GETv in Heqp.
           assert (forall x, ~ var_in_sact x0 x).
           {
             intros xx VVIS.
             generalize (VSV v _ _ GETv _ VVIS). intro LT. red in LT.
             destruct (NOvarsl _ _ _ xx GETv VVIS) as (_ & [EQ|IN]).
             lia.
             move SORTED at bottom.
             apply Sorted_StronglySorted in SORTED.
             2:{
               red. intros; lia.
             }
             inv SORTED.
             rewrite Forall_forall in H4; apply H4 in IN; lia.
           }
           edestruct (eval_sact_no_vars_succeeds _ H0) as (rr & ESNV). eapply WTV. eauto.
           rewrite ESNV in Heqp. inv Heqp.
           revert GET. simpl. unfold replace_all_occurrences_in_vars.
           setoid_rewrite list_assoc_map with (g:= fun '(t,a0) => (t, replace_all_occurrences_in_sact a0 v rr)). 2: intros; now destr.
           setoid_rewrite GET'. simpl. intro A; inv A.
           apply var_not_in_sact_replace in VIS. auto.

      * repeat refine (conj _ _); eauto.
        intros x t y res GET INTy.
        edestruct (INTERP3) as (y' & GET2 & INT2); eauto.
        apply incl_app_inv in INCL. apply INCL.
        intros x [EQ|IN]; eauto.
        subst.
        move Heqp at bottom. unfold simplify_var in Heqp.
        inv VARS_EXIST.
        destruct H1 as (? & ? & GETv). rewrite GETv in Heqp.
        assert (forall x, ~ var_in_sact x0 x).
        {
          intros xx VVIS.
          generalize (VSV _ _ _ GETv _ VVIS). intro LT. red in LT.
          destruct (NOvarsl _ _ _ xx GETv VVIS) as (_ & [EQ|IN]).
          lia.
          move SORTED at bottom.
          apply Sorted_StronglySorted in SORTED.
          2:{
            red. intros; lia.
          }
          inv SORTED.
          rewrite Forall_forall in H3; apply H3 in IN; lia.
        }
        edestruct (eval_sact_no_vars_succeeds _ H) as (rr & ESNV). eapply WTV. eauto.
        rewrite ESNV in Heqp. inv Heqp.
        exists rr. eapply INCL. simpl. left. auto.
  Qed.

  Lemma list_assoc_filter2:
    forall {K V: Type} {eqdec: EqDec K} (l: list (K*V)) name k,
      list_assoc (filter (fun '(n,_) => negb (beq_dec n name)) l) k =
        if beq_dec k name then None else list_assoc l k.
  Proof.
    induction l; simpl; intros; eauto.
    repeat destr.
    destruct a.
    destruct (beq_dec k0 name) eqn:?; simpl. apply beq_dec_iff in Heqb. subst.
    rewrite IHl. destr. destr. subst. apply beq_dec_false_iff in Heqb. congruence.
    destr. subst. rewrite Heqb. auto. eauto.
  Qed.

  Lemma wt_sact_remove_one:
    forall vvs v
           (NV: forall x t y, list_assoc vvs x = Some (t,y) -> ~ var_in_sact y v)
           a t
           (WTa: wt_sact (Sigma:=Sigma) vvs a t)
           (NVa: ~ var_in_sact a v),
      wt_sact (Sigma:=Sigma) (filter (fun '(n, _) => negb (beq_dec n v)) vvs) a t.
  Proof.
    induction 2; simpl; intros; eauto.
    - econstructor; eauto.
      rewrite <- list_assoc_filter. eauto.
      intros. rewrite negb_true_iff, beq_dec_false_iff; auto.
      intro; subst. apply NVa. constructor.
    - econstructor; eauto.
    - econstructor; eauto.
      apply IHWTa1. intro VIS; apply NVa; apply var_in_if_cond; auto.
      apply IHWTa2. intro VIS; apply NVa; apply var_in_if_true; auto.
      apply IHWTa3. intro VIS; apply NVa; apply var_in_if_false; auto.
    - econstructor; eauto.
      apply IHWTa. intro VIS; apply NVa; apply var_in_sact_unop; auto.
    - econstructor; eauto.
      apply IHWTa1. intro VIS; apply NVa; apply var_in_sact_binop_1; auto.
      apply IHWTa2. intro VIS; apply NVa; apply var_in_sact_binop_2; auto.
    - econstructor; eauto.
      apply IHWTa. intro VIS; apply NVa; apply var_in_sact_external; auto.
  Qed.

  Lemma eval_sact_bound:
    forall vvs : var_value_map,
      vvs_smaller_variables vvs ->
      forall (a : SimpleForm.sact) t (WTa: wt_sact (Sigma:=Sigma) vvs a t),
        let bnd := (S (max_var vvs) + vvs_size vvs (S (max_var vvs)) + size_sact a) in
        forall m, m >= bnd ->
        eval_sact vvs a m = None ->
        forall n, n >= m -> eval_sact vvs a n = None.
  Proof.
    intros.
    destruct (eval_sact vvs a n) eqn:?; auto.
    eapply eval_sact_interp_sact in Heqo.
    eapply interp_sact_eval_sact in Heqo; eauto.
    eapply eval_sact_more_fuel with (n2:= m) in Heqo. congruence. unfold bnd in H0. lia.
  Qed.

  Lemma remove_var_correct:
    forall vvs (VSV: vvs_smaller_variables vvs) (* (WTvvs: wt_vvs (Sigma:=Sigma) vvs) *) v
           (NV: forall x t y, list_assoc vvs x = Some (t,y) -> ~ var_in_sact y v)
           a
           t (WTa: wt_sact (Sigma:=Sigma) vvs a t)
           (NVa: ~ var_in_sact a v) res,
      interp_sact (sigma:=sigma) vvs a res <->
        interp_sact (sigma:=sigma) (filter (fun '(n,_) => negb (beq_dec n v)) vvs) a res.
  Proof.
    intros. eapply interp_eval_iff. eauto.
    red; intros.
    generalize (list_assoc_filter2 vvs v v0). rewrite H. destr.
    rewrite beq_dec_false_iff in Heqb. intros. symmetry in H1. eauto. eauto.
    eapply wt_sact_remove_one; eauto.

    (* set (F := fun vvs => (S (max_var vvs) + vvs_size vvs (S (max_var vvs)) + size_sact a)). *)
    (* set (vvs2 := (filter (fun '(n,_) => negb (beq_dec n v)) vvs)). *)
    (* exists (max (F vvs) (F vvs2)). *)
    exists O. intros n0 _.
    intros.
    clear VSV WTa.
    revert a NVa. induction n0; simpl; intros; eauto.
    unfold opt_bind.
    destr.
    - rewrite <- list_assoc_filter. repeat destr.  eauto.
      intros; rewrite negb_true_iff, beq_dec_false_iff; auto.
      intro; subst. apply NVa. constructor.
    - rewrite <- IHn0. repeat destr.
      eapply IHn0. intro VIS; apply NVa; eapply var_in_if_true; auto.
      eapply IHn0. intro VIS; apply NVa; eapply var_in_if_false; auto.
      intro VIS; apply NVa; eapply var_in_if_cond; auto.
    - rewrite <- IHn0. repeat destr.
      intro VIS; apply NVa; eapply var_in_sact_unop; auto.
    - rewrite <- ! IHn0. auto.
      intro VIS; apply NVa; eapply var_in_sact_binop_2; auto.
      intro VIS; apply NVa; eapply var_in_sact_binop_1; auto.
    - rewrite <- IHn0. repeat destr.
      intro VIS; apply NVa; eapply var_in_sact_external; auto.
  Qed.

  Lemma remove_var_preserves_vsv:
    forall l sf (VSV: vvs_smaller_variables (vars sf)),
      vvs_smaller_variables (vars (remove_by_name_var sf l)).
  Proof.
    simpl. red; intros.
    generalize (list_assoc_filter2 (vars sf) l v). rewrite H. destr.
    rewrite beq_dec_false_iff in Heqb. intros. symmetry in H1. eauto.
  Qed.

  Lemma remove_vars_preserves_vsv:
    forall l sf (VSV: vvs_smaller_variables (vars sf)),
      vvs_smaller_variables (vars (fold_left remove_by_name_var l sf)).
  Proof.
    induction l; simpl; intros; eauto.
    apply IHl. apply remove_var_preserves_vsv. auto.
  Qed.

  Lemma remove_var_preserves_wt_vvs:
    forall l sf (WT_VVS: wt_vvs (Sigma:=Sigma) (vars sf))
           (NV: forall (x : nat) (t0 : type) (y : SimpleForm.sact),
               list_assoc (vars sf) x = Some (t0, y) -> ~ var_in_sact y l),
      wt_vvs (Sigma:=Sigma) (vars (remove_by_name_var sf l)).
  Proof.
    simpl. red; intros.
    generalize (list_assoc_filter2 (vars sf) l v). rewrite H. destr.
    rewrite beq_dec_false_iff in Heqb. intros. symmetry in H0. eauto.
    eapply wt_sact_remove_one; eauto.
  Qed.

  Lemma remove_vars_preserves_wt_vvs:
    forall l sf (WT_VVS: wt_vvs (Sigma:=Sigma) (vars sf))
           (NV: forall (x : nat) (t0 : type) (y : SimpleForm.sact) v,
               list_assoc (vars sf) x = Some (t0, y) -> var_in_sact y v -> ~ In v l),
      wt_vvs (Sigma:=Sigma) (vars (fold_left remove_by_name_var l sf)).
  Proof.
    induction l; simpl; intros; eauto.
    apply IHl.
    apply remove_var_preserves_wt_vvs; auto.
    intros x t0 y GET VIS; eapply NV; eauto.
    simpl.
    intros x t0 y v GET VIS IN.
    generalize (list_assoc_filter2 (vars sf) a x). rewrite GET. destr.
    rewrite beq_dec_false_iff in Heqb. intros. symmetry in H. eapply NV; eauto.
  Qed.

  Lemma remove_vars_correct:
    forall l sf (VSV: vvs_smaller_variables (vars sf)) 
           (NV: forall v x t y, list_assoc (vars sf) x = Some (t,y) -> var_in_sact y v -> ~ In v l)
           a
           t (WTa: wt_sact (Sigma:=Sigma) (vars sf) a t)
           (NVa: forall v, var_in_sact a v -> ~ In v l) res,
      interp_sact (sigma:=sigma) (vars sf) a res <->
        interp_sact (sigma:=sigma) (vars (fold_left remove_by_name_var l sf)) a res.
  Proof.
    induction l; simpl; intros; eauto. tauto.
    rewrite <- IHl.
    - simpl. eapply remove_var_correct; eauto.
      + intros x t0 y GET VIS; eapply NV; eauto.
      + intro VIS; eapply NVa; eauto.
    - eapply remove_var_preserves_vsv; eauto.
    - simpl. intros.
      generalize (list_assoc_filter2 (vars sf) a x). rewrite H. destr.
      rewrite beq_dec_false_iff in Heqb. intros. symmetry in H1. eauto.
      eapply NV in H1. 2: eauto. intuition.
    - simpl. eapply wt_sact_remove_one; eauto.
      + intros x t0 y GET VIS; eapply NV in VIS; eauto.
      + intro VIS; eapply NVa; eauto.
    - intros v VIS IN; eapply NVa; eauto.
  Qed.

  Definition inlining_pass (sf: simple_form)
    : list (nat * val) :=
    (* Try to determine the value of variables *)
    let ks := NatSort.sort (map fst (vars sf)) in
    let '(sf,l) := fold_left
                     (fun '(sf,l) var =>
                        let '(sf,l1) := simplify_var sf var in
                        (sf, l1++l))
                     ks (sf,[]) in
  l.

  Lemma Sorted_strict:
    forall le1 le2 (STRICT: forall x y, le2 x y <-> (le1 x y /\ x <> y))
           (l: list nat),
      Sorted le1 l ->
      NoDup l ->
      Sorted le2 l.
  Proof.
    induction 2; simpl; intros; eauto.
    inv H1. econstructor. eauto.
    inv H0. econstructor. econstructor. rewrite STRICT. split; auto. intro; subst. apply H4; simpl; auto.
  Qed.

  Lemma sorted_lt:
    forall l,
      NoDup l ->
      Sorted lt (NatSort.sort l).
  Proof.
    intros.
    generalize (NatSort.Sorted_sort l). intros.
    eapply Sorted_strict. 2: apply H0.
    intros. simpl. fold (Nat.leb x y).  unfold is_true. rewrite Nat.leb_le. lia.
    eapply Permutation.Permutation_NoDup. 2: apply H.
    apply NatSort.Permuted_sort.
  Qed.

  Lemma in_list_assoc:
    forall {K V: Type} {eqdec: EqDec K} (l: list (K*V))
           (ND: NoDup (map fst l)) k v,
      In (k,v) l -> list_assoc l k = Some v.
  Proof.
    induction l; simpl; intros; eauto. easy.
    repeat destr; eauto.
    - subst. destruct H. inv H. auto. simpl in ND. inv ND. elim H2.
      change k0 with (fst (k0, v)).
      eapply in_map. eauto.
    - inv ND; destruct H; eauto. inv H. congruence.
  Qed.

  Lemma wt_sact_var_exists:
    forall vvs a t
           (WTa: wt_sact (Sigma:=Sigma) vvs a t)
           (VSV: vvs_smaller_variables vvs)
           (WTV: wt_vvs (Sigma:=Sigma) vvs)
           v (VIS: var_in_sact a v),
      In v (map fst vvs).
  Proof.
    intros vvs a t WTa VSV WTV. revert a t WTa.
    induction 1; simpl; intros; eauto; inv VIS; eauto.
    eapply list_assoc_in_keys; eauto.
  Qed.

  Lemma inlining_pass_correct:
    forall sf l
           (ND: NoDup (map fst (vars sf)))
           (IP: inlining_pass sf = l)
           (VSV: vvs_smaller_variables (vars sf))
           (WT: wt_vvs (Sigma:=Sigma) (vars sf)),
      NoDup (map fst l) /\
        forall v reg (REG: list_assoc (final_values sf) reg = Some v) res
               (INT: interp_sact (sigma:=sigma) (vars sf) (SVar v) res),
          In (v,res) l.
  Proof.
    unfold inlining_pass. intros.
    repeat destr_in IP. inv IP.
    split.
    eapply simplify_vars_preserves; eauto.
    eapply Permutation.Permutation_NoDup. apply NatSort.Permuted_sort. eauto. constructor.
    intros.
    exploit simplify_vars_correct; eauto.
    - apply sorted_lt. auto.
    - eapply Permutation.Permutation_Forall. apply NatSort.Permuted_sort.
      rewrite Forall_forall.  intros x.  rewrite in_map_iff.
      intros ((x0 & (?&?)) & EQ & IN). subst. simpl.
      erewrite in_list_assoc; eauto.
    - simpl. intros x t y v0 GET VIS. split. auto.
      eapply Permutation.Permutation_in. apply NatSort.Permuted_sort.
      exploit WT. apply GET. intro WTy.
      eapply wt_sact_var_exists; eauto.
    - intros (IMPL & VVS' & WT' & INTERPl & NIV & _ & IN).
      edestruct (IN v).
      eapply Permutation.Permutation_in. apply NatSort.Permuted_sort.
      inv INT.
      eapply list_assoc_in_keys; eauto.
      rewrite Forall_forall in INTERPl.
      exploit INTERPl. eauto. simpl. intro.
      inv INT. edestruct IMPL as (y' & GET & INT2). eauto. eauto.
      inv H1. rewrite GET in H5; inv H5.
      exploit @interp_sact_determ. apply H6. apply INT2. intro; subst. auto.
  Qed.

  (* Cycles between variables are possible (a variable v can depend on another
     variable which itself depends on v). However, these can only occur in
     situations in which the cycle can be removed by applying some
     simplifications to the expression. We know this because of the way simple
     forms passed to this function are expected to have been built.

     Note that we don't need our simplifications to be exhaustive: for instance
     we choose to ignore that an and can be short-circuited based on its right
     operand. *)

  Lemma eval_sact_eval_sact_no_vars:
    forall vvs n a res res2,
      eval_sact vvs a n = Some res ->
      eval_sact_no_vars a = Some res2 ->
      res = res2.
  Proof.
    induction n; simpl; intros; eauto. inv H.
    unfold opt_bind in H.
    repeat destr_in H; inv H; simpl in H0; inv H0; eauto.
    - unfold opt_bind in H1. destr_in H1.
      exploit IHn. apply Heqo. eauto. intros <-.
      exploit IHn. apply H2. eauto. auto. inv H1.
    - unfold opt_bind in H1. destr_in H1.
      exploit IHn. apply Heqo. eauto. intros <-.
      exploit IHn. apply H2. eauto. auto. inv H1.
    - unfold opt_bind in H1. destr_in H1.
      exploit IHn. apply Heqo. eauto. intros <-.
      congruence. congruence.
    - unfold opt_bind in H1. destr_in H1.
      exploit IHn. apply Heqo. eauto.
      destr_in H1.
      exploit IHn. apply Heqo0. eauto. intros. congruence. congruence. congruence.
    - unfold opt_bind in H1. destr_in H1.
      exploit IHn. apply Heqo. eauto. intro; subst. congruence. congruence.
  Qed.

  Lemma eval_sact_wt:
    forall vvs (WT: wt_vvs (Sigma:=Sigma) vvs) n a r t (WTa: wt_sact (Sigma:=Sigma) vvs a t)
           (EVAL: eval_sact vvs a n = Some r),
      wt_val t r.
  Proof.
    induction n; simpl; intros; eauto. inv EVAL.
    unfold opt_bind in EVAL; repeat destr_in EVAL; inv EVAL; inv WTa; eauto.
    - rewrite Heqo in H1; inv H1.
      eapply IHn; eauto.
    - eapply Wt.wt_unop_sigma1; eauto.
    - eapply Wt.wt_binop_sigma1; eauto.
  Qed.


  Lemma wt_sact_replace_vars_gen:
    forall vvs f a t,
      wt_sact (Sigma:=Sigma) vvs a t ->
      wt_sact (Sigma:=Sigma) (map (fun '(n,(t,u)) => (n,(t,f u))) vvs) a t.
  Proof.
    induction 1; simpl; intros; eauto.
    - econstructor.
      erewrite list_assoc_map with (g := fun '(t,a) => (t, f a)). 2: intros; repeat destr.
      rewrite H. reflexivity.
    - econstructor; eauto.
    - econstructor; eauto.
    - econstructor; eauto.
    - econstructor; eauto.
    - econstructor; eauto.
  Qed.

  Lemma wt_vvs_replace_gen:
    forall vvs f,
      wt_vvs (Sigma:=Sigma) vvs ->
      (forall t u, wt_sact (Sigma:=Sigma) vvs u t -> wt_sact (Sigma:=Sigma) vvs (f u) t) ->
      wt_vvs (Sigma:=Sigma) (map (fun '(n,(t,u)) => (n,(t,f u)))vvs).
  Proof.
    unfold wt_vvs; intros.
    setoid_rewrite list_assoc_map with (g:= fun '(t,a) => (t, f a)) in H1.
    2: intros; repeat destr.
    unfold option_map in H1; repeat destr_in H1; inv H1.
    eapply wt_sact_replace_vars_gen. eapply H0; eauto.
  Qed.


  Lemma interp_map_vvs:
    forall vvs (VSV: vvs_smaller_variables vvs) (WTvvs: wt_vvs (Sigma:=Sigma) vvs)
           a
           t (WTa: wt_sact (Sigma:=Sigma) vvs a t)
           (* (NVa: ~ var_in_sact a v) *) res f
           (VARS: forall v s, var_in_sact (f s) v -> var_in_sact s v)
           (* (WTf: forall s t, wt_sact (Sigma:=Sigma) vvs s t ->  wt_sact (Sigma:=Sigma) vvs (f s) t) *)
           (* (WTf: forall s t, wt_sact (Sigma:=Sigma) vvs s t ->  wt_sact (Sigma:=Sigma) (map (fun '(n,(t,a)) => (n, (t, f a))) vvs) s t) *)
           (WTf2: forall s t, wt_sact (Sigma:=Sigma) vvs s t ->  wt_sact (Sigma:=Sigma) vvs (f s) t)
           (CORRECT: forall vvs s t n res,
               wt_vvs (Sigma:=Sigma) vvs ->
               wt_sact (Sigma:=Sigma) vvs s t ->
               eval_sact vvs s n = Some res ->
               eval_sact vvs (f s) n = Some res
           )
    ,
      interp_sact (sigma:=sigma) vvs a res ->
      interp_sact (sigma:=sigma) (map (fun '(n,(t,a)) => (n, (t, f a))) vvs) a res.
  Proof.
    intros.
    eapply interp_sact_eval_sact in H; eauto.
    revert H. generalize (S (max_var vvs) + vvs_size vvs (S (max_var vvs)) + size_sact a). intros.
    eapply eval_sact_interp_sact with (fuel:=n).
    revert a res H t WTa.
    
    induction n. simpl; intros; eauto.
    simpl. unfold opt_bind.
    intros a res EVAL.
    destr_in EVAL.
    - repeat destr_in EVAL. 2: inv EVAL.
      rewrite list_assoc_map with (g:=fun '(t,a) => (t, f a)). rewrite Heqo. simpl.
      intros; eapply IHn. eauto. eapply WTvvs in Heqo. eapply WTf2. eauto.
      intros; repeat destr.
    - auto.
    - intros t WTa; inv WTa.
      destr_in EVAL. 2: inv EVAL.
      erewrite IHn; eauto.
      repeat destr_in EVAL; try now inv EVAL. subst.
      eapply IHn; eauto.
      eapply IHn; eauto.
    - intros t WTa; inv WTa.
      destr_in EVAL. 2: inv EVAL.
      erewrite IHn; eauto.
    - intros t WTa; inv WTa.
      destr_in EVAL. 2: inv EVAL.
      destr_in EVAL. 2: inv EVAL.
      erewrite IHn; eauto.
      erewrite IHn; eauto.
    - intros t WTa; inv WTa.
      destr_in EVAL. 2: inv EVAL.
      erewrite IHn; eauto.
  Qed.


  Definition interp_cycle (sf: simple_form) : UREnv :=
    let fenv := inlining_pass sf in
    create REnv (fun k =>
                   match list_assoc (final_values sf) k with
                     | Some n =>
                         match list_assoc fenv n with
                         | Some v => v
                         | None => getenv REnv r k (* Should be unreachable *)
                         end
                   | None => getenv REnv r k
                   end).

  Lemma normal_form_ok:
    forall
      {finreg: FiniteType reg_t}
      (rules: rule_name_t -> daction)
      (s: schedule)
      (GS: good_scheduler s)
      (WTr: Wt.wt_renv R REnv r)
      (TA:
        forall rule,
          exists t,
            wt_daction (R:=R) (Sigma:=Sigma) pos_t string string [] (rules rule) t),
    UntypedSemantics.interp_dcycle rules r sigma s =
      interp_cycle (SimpleForm.schedule_to_simple_form (Sigma:=Sigma) REnv r R rules s).
  Proof.
    intros.
    unfold interp_dcycle.
    generalize (schedule_to_simple_form_ok
                  (wt_sigma:=wt_sigma)
                  REnv r R rules _ GS _ eq_refl TA WTr). simpl.
    intros (WTV & VSV & ND & INFINAL & SPECFINAL).
    unfold interp_cycle. unfold commit_update.
    apply create_funext. intro k.

    generalize (inlining_pass_correct _ _ ND eq_refl VSV WTV).
    intros (ND2 & INLINING).
    destruct (SPECFINAL k) as (n & GET & INTERP).
    exploit INLINING. apply GET. apply INTERP.
    intro IN. apply in_list_assoc in IN.
    rewrite GET.
    rewrite IN.
    auto. auto.
  Qed.

End SimpleFormInterpretation.
