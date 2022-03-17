Require Import Coq.Strings.Ascii.
Require Import Koika.Environments Koika.SimpleForm Koika.TypeInference
        Koika.UntypedSemantics.
Require Import Koika.BitsToLists.
From RecordUpdate Require Import RecordSet.
Import RecordSetNotations.
Require Import Sact.
Require Import Coq.Sorting.Sorted.
Require Import Coq.Sorting.Mergesort.
Require Import Maps.

Module PosOrder <: Orders.TotalLeBool.
  Definition t := positive.
  Definition leb x y := Pos.leb x y.
  Infix "<=?" := leb (at level 70, no associativity).
  Theorem leb_total : forall a1 a2, is_true (a1 <=? a2) \/ is_true (a2 <=? a1).
  Proof.
    intros.
    generalize (Pos.leb_spec a1 a2).
    generalize (Pos.leb_spec a2 a1).
    unfold leb.
    intros A B. inv A; inv B; try lia; auto.
  Qed.
End PosOrder.

Module Import PosSort := Sort PosOrder.


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

  Fixpoint vars_in_sact (s: sact) : list positive :=
    match s with
    | SConst _ => []
    | SVar v => [v]
    | SExternalCall _ a
    | SUnop _ a => vars_in_sact a
    | SBinop _ a1 a2 => vars_in_sact a1 ++ vars_in_sact a2
    | SIf c t f => vars_in_sact c ++ vars_in_sact t ++ vars_in_sact f
    end.

  Fixpoint reachable_vars_aux (vvs: var_value_map) (n: positive) (visited: list positive) fuel :=
    match fuel with
      O => visited
    | S fuel =>
        if in_dec Pos.eq_dec n visited
        then visited
        else
          n::match vvs ! n with
             | None => visited
             | Some (_, s) =>
                 fold_left (fun visited n =>
                              reachable_vars_aux vvs n visited fuel
                           ) (vars_in_sact s) visited
             end
    end.

  Inductive reachable_var (vvs: var_value_map) : sact -> positive -> Prop :=
  | reachable_var_var:
    forall n, reachable_var vvs (SVar n) n
  | reachable_var_in_var:
    forall n x t a,
      vvs ! x = Some (t, a) ->
      reachable_var vvs a n ->
      reachable_var vvs (SVar x) n
  | reachable_var_if_cond:
    forall n c t f,
      reachable_var vvs c n ->
      reachable_var vvs (SIf c t f) n
  | reachable_var_if_true:
    forall n c t f,
      reachable_var vvs t n ->
      reachable_var vvs (SIf c t f) n
  | reachable_var_if_false:
    forall n c t f,
      reachable_var vvs f n ->
      reachable_var vvs (SIf c t f) n
  | reachable_var_binop1:
    forall n c a1 a2,
      reachable_var vvs a1 n ->
      reachable_var vvs (SBinop c a1 a2) n
  | reachable_var_binop2:
    forall n c a1 a2,
      reachable_var vvs a2 n ->
      reachable_var vvs (SBinop c a1 a2) n
  | reachable_var_unop:
    forall n c a1,
      reachable_var vvs a1 n ->
      reachable_var vvs (SUnop c a1) n
  | reachable_var_externalCall:
    forall n c a1,
      reachable_var vvs a1 n ->
      reachable_var vvs (SExternalCall c a1) n.

  Lemma reachable_vars_aux_incr:
    forall vvs fuel n visited,
      incl visited (reachable_vars_aux vvs n visited fuel).
  Proof.
    induction fuel; simpl; intros; eauto.
    apply incl_refl.
    destr. destr.
    - destr. apply incl_tl.
      apply fold_left_induction. apply incl_refl.
      intros. eapply incl_tran. apply H0. apply IHfuel.
    - apply incl_tl, incl_refl.
  Qed.


  Lemma reachable_var_aux_below:
    forall vvs (VSV: vvs_smaller_variables vvs)
           a n (GET: forall v, var_in_sact a v -> (v < n)%positive)
           v (RV: reachable_var vvs a v),
      (v < n)%positive.
  Proof.
    intros vvs VSV a n.
    change n with (projT1 (existT (fun _ => sact) n a)).
    change a with (projT2 (existT (fun _ => sact) n a)) at 1 3.
    generalize (existT (fun _ => sact) n a).
    clear n a. intro s. pattern s.
    eapply well_founded_induction.
    apply wf_order_sact. clear s.
    intros x IH BELOW v RV.
    destruct x; simpl in *.
    inv RV.
    - eapply BELOW. constructor.
    - eapply VSV in H.
      Sact.exploit (IH (existT _ x0 a)). constructor. apply BELOW. constructor.
      simpl. apply H. simpl. eauto. simpl.
      Sact.trim (BELOW x0). constructor.  lia.
    - eapply (IH (existT _ x c)). constructor 2. simpl; lia.
      simpl. intros v0 VIS. eapply BELOW. eapply var_in_if_cond; eauto. simpl; auto.
    - eapply (IH (existT _ x t)). constructor 2. simpl; lia.
      simpl. intros v0 VIS. eapply BELOW. eapply var_in_if_true; eauto. simpl; auto.
    - eapply (IH (existT _ x f)). constructor 2. simpl; lia.
      simpl. intros v0 VIS. eapply BELOW. eapply var_in_if_false; eauto. simpl; auto.
    - eapply (IH (existT _ x a1)). constructor 2. simpl; lia.
      simpl. intros v0 VIS. eapply BELOW. eapply var_in_sact_binop_1; eauto. simpl; auto.
    - eapply (IH (existT _ x a2)). constructor 2. simpl; lia.
      simpl. intros v0 VIS. eapply BELOW. eapply var_in_sact_binop_2; eauto. simpl; auto.
    - eapply (IH (existT _ x a1)). constructor 2. simpl; lia.
      simpl. intros v0 VIS. eapply BELOW. eapply var_in_sact_unop; eauto. simpl; auto.
    - eapply (IH (existT _ x a1)). constructor 2. simpl; lia.
      simpl. intros v0 VIS. eapply BELOW. eapply var_in_sact_external; eauto. simpl; auto.
  Qed.

  Lemma reachable_var_aux_below_get:
    forall vvs (VSV: vvs_smaller_variables vvs)
           a n t (GET: vvs ! n = Some (t,a))
           v (RV: reachable_var vvs a v),
      (v < n)%positive.
  Proof.
    intros; eapply reachable_var_aux_below; eauto.
    eapply VSV. eauto.
  Qed.

  Lemma reachable_inv:
    forall vvs a v,
      reachable_var vvs a v ->
      exists v' , var_in_sact a v' /\ (v = v' \/ exists t' a', vvs ! v' = Some (t', a') /\ reachable_var vvs a' v).
  Proof.
    induction 1; simpl; intros; eauto.
    - exists n. split. constructor. left; auto.
    - destruct IHreachable_var as (v'& VIS & OTHER).
      exists x; split. constructor.
      destruct OTHER as [EQ | (t' & a' & GET & RV)]. subst.
      right; eauto.
      right; exists t, a; split. eauto. eauto.
    - destruct IHreachable_var as (v'& VIS & OTHER).
      exists v'; split. eapply var_in_if_cond. auto.
      destruct OTHER as [EQ | (t' & a' & GET & RV)]; auto. right. eauto.
    - destruct IHreachable_var as (v'& VIS & OTHER).
      exists v'; split. eapply var_in_if_true. auto.
      destruct OTHER as [EQ | (t' & a' & GET & RV)]; auto. right. eauto.
    - destruct IHreachable_var as (v'& VIS & OTHER).
      exists v'; split. eapply var_in_if_false. auto.
      destruct OTHER as [EQ | (t' & a' & GET & RV)]; auto. right. eauto.
    - destruct IHreachable_var as (v'& VIS & OTHER).
      exists v'; split. eapply var_in_sact_binop_1. auto.
      destruct OTHER as [EQ | (t' & a' & GET & RV)]; auto. right. eauto.
    - destruct IHreachable_var as (v'& VIS & OTHER).
      exists v'; split. eapply var_in_sact_binop_2. auto.
      destruct OTHER as [EQ | (t' & a' & GET & RV)]; auto. right. eauto.
    - destruct IHreachable_var as (v'& VIS & OTHER).
      exists v'; split. eapply var_in_sact_unop. auto.
      destruct OTHER as [EQ | (t' & a' & GET & RV)]; auto. right. eauto.
    - destruct IHreachable_var as (v'& VIS & OTHER).
      exists v'; split. eapply var_in_sact_external. auto.
      destruct OTHER as [EQ | (t' & a' & GET & RV)]; auto. right. eauto.
  Qed.

  Lemma var_in_sact_ok:
    forall a v,
      var_in_sact a v -> In v (vars_in_sact a).
  Proof.
    induction 1; simpl; intros; eauto.
    rewrite ! in_app_iff; now eauto.
    rewrite ! in_app_iff; now eauto.
    rewrite ! in_app_iff; now eauto.
    rewrite ! in_app_iff; now eauto.
    rewrite ! in_app_iff; now eauto.
  Qed.

  Lemma var_in_sact_ok_inv:
    forall a v,
      In v (vars_in_sact a) -> var_in_sact a v.
  Proof.
    induction a; simpl; intros; eauto; intuition.
    - subst. constructor.
    - rewrite ! in_app_iff in H. intuition.
      econstructor; eauto.
      eapply var_in_if_true; eauto.
      eapply var_in_if_false; eauto.
    - econstructor; eauto.
    - rewrite ! in_app_iff in H. intuition.
      eapply var_in_sact_binop_1; eauto.
      eapply var_in_sact_binop_2; eauto.
    - econstructor; eauto.
  Qed.

  Lemma rev_sym:
    forall {A: Type} (l1 l2: list A),
      l1 = rev l2 <-> rev l1 = l2.
  Proof.
    split; intro.
    - rewrite H. rewrite rev_involutive. easy.
    - rewrite <- H. rewrite rev_involutive. easy.
  Qed.
  Lemma app_inv_last:
    forall {A: Type} (l1 l2: list A) (x y: A),
      l1 ++ [x] = l2 ++ [y]
      -> x = y.
  Proof.
    intros.
    apply (f_equal (@rev A)) in H.
    rewrite rev_app_distr in H. rewrite rev_app_distr in H at 1.
    simpl in H. inv H.
    easy.
  Qed.

  Lemma fold_left_prop_eventually_no_tail:
    forall {A B: Type} (P: B -> Prop) (f: B -> A -> B) (lb: list A) (s: B) x,
      (forall e, P (f e x))
      -> P (fold_left f (lb ++ [x]) s).
  Proof.
    intros.
    assert (exists l', l' = rev (lb ++ [x])).
    { exists (rev (lb ++ [x])). easy. }
    destruct H0.
    apply rev_sym in H0.
    rewrite <- H0.
    induction x0.
    - destruct lb; easy.
    - rewrite <- fold_left_rev_right. rewrite rev_involutive.
      assert (x = a). { simpl in H0. apply app_inv_last in H0. easy. }
      simpl. inv H1. eapply H.
  Qed.

  Lemma fold_left_prop_eventually:
    forall {A B: Type} (P: B -> Prop) (f: B -> A -> B) (lb la: list A) (s: B) x,
      (forall e, P (f e x))
      -> (forall y e, In y la -> P e -> P (f e y))
      -> P (fold_left f (lb ++ [x] ++ la) s).
  Proof.
    intros A B P f0 lb la s x H0.
    remember (rev la) as la'. apply rev_sym in Heqla'. rewrite <- Heqla'.
    generalize dependent la.
    induction la'; intros; simpl.
    - apply fold_left_prop_eventually_no_tail. easy.
    - rewrite <- fold_left_rev_right.
      repeat (rewrite rev_app_distr; simpl). rewrite rev_involutive.
      apply H.
      + apply in_rev. rewrite rev_involutive. left. easy.
      + assert ((la' ++ [x]) ++ rev lb = rev (lb ++ [x] ++ rev la')).
        { repeat (rewrite rev_app_distr). rewrite rev_involutive. easy. }
        rewrite H1.
        rewrite fold_left_rev_right.
        eapply IHla'.
        * eauto.
        * intros. apply H.
          ** apply in_rev. rewrite rev_involutive.
             apply in_rev in H2. right. easy.
          ** easy.
  Qed.
  Lemma reachable_vars_aux_in:
    forall vvs fuel visited n, (fuel > 0)%nat -> In n (reachable_vars_aux vvs n visited fuel).
  Proof.
    destruct fuel. lia. intros. simpl. destr. destr. destr.
    left; auto. left; auto.
  Qed.

  Lemma fold_left_ev:
    forall {A B: Type} (P: A -> Prop) (I: A -> Prop) (f: A -> B -> A)
           l
           (INV: forall acc y, In y l -> I acc -> I (f acc y))
           (PRESERVES: forall acc y, In y l -> I acc -> P acc -> P (f acc y))
           acc,
      I acc ->
      (P acc \/ exists x, In x l /\ forall acc, I acc -> P (f acc x)) ->
      P (fold_left f l acc).
  Proof.
    induction l; simpl; intros; eauto. destruct H0 as [|(? & [] & ?)]. auto.
    destruct H0 as [Pacc|(x & EQIN & Pf)].
    apply IHl. eauto. eauto. eauto. left; apply PRESERVES; auto.
    apply IHl. eauto. eauto. eauto. destruct EQIN. subst; left; auto.
    right; eauto.
  Qed.

  Lemma reachable_vars_aux_ok:
    forall vvs (VSV: vvs_smaller_variables vvs)
           fuel n visited l,
      reachable_vars_aux vvs n visited fuel = l ->
      (forall n, In n visited ->
                 forall v t a,
                   vvs ! n = Some (t, a) ->
                   reachable_var vvs a v ->
                   In v visited) ->
      ((Pos.to_nat n<fuel)%nat) ->
      forall n1 (IN: In n1 l) v t a,
        vvs ! n1 = Some (t, a) ->
        reachable_var vvs a v ->
        In v l.
  Proof.
    induction fuel; simpl; intros; eauto. lia.
    destr_in H.
    - subst. eapply H0; eauto.
    - subst. destruct IN as [EQ|IN].
      + subst. rewrite H2.
        right.
        cut (exists vv, In vv (vars_in_sact a) /\
                          forall vis,
                            (forall n : positive,
                                In n vis ->
                                forall (v0 : positive) (t0 : type) (a0 : SimpleForm.sact),
                                  vvs ! n = Some (t0, a0) -> reachable_var vvs a0 v0 -> In v0 vis) ->
                            In v (reachable_vars_aux vvs vv vis fuel)
            ).
        intros (vv & IN & REACH).

        eapply fold_left_ev with (I:=fun vis =>
                                       forall n : positive,
                                         In n vis ->
                                         forall (v0 : positive) (t0 : type) (a0 : SimpleForm.sact),
                                           vvs ! n = Some (t0, a0) -> reachable_var vvs a0 v0 -> In v0 vis
                                 ).
        {
          intros.
          eapply IHfuel. eauto. eauto.
          exploit VSV. apply H2. apply var_in_sact_ok_inv. apply H. unfold var_lt. lia. apply H5.
          eauto. eauto.
        }
        {
          intros.
          eapply reachable_vars_aux_incr; eauto.
        }
        eauto.
        right; exists vv; split; eauto.
        destruct (reachable_inv _ _ _ H3) as (v' & VIS & IN).
        apply var_in_sact_ok in VIS.
        eexists; split. apply VIS.
        destruct IN as [EQ|(t' & a' & GET & REACH)].
        subst. intros. eapply reachable_vars_aux_in; eauto. lia.
        intros.
        eapply IHfuel. eauto.
        eauto.
        exploit VSV. apply H2. apply var_in_sact_ok_inv. apply VIS. unfold var_lt. lia.
        2: apply GET. eapply reachable_vars_aux_in. lia. auto.
      + destruct (vvs ! n) eqn:?.
        2: {
          right; eapply H0; eauto.
        }
        destruct p.
        right.
        revert n1 IN v t a H2 H3.
        pattern (fold_left
                   (fun (visited0 : list positive) (n2 : positive) =>
                      reachable_vars_aux vvs n2 visited0 fuel) (vars_in_sact s) visited).
        eapply fold_left_induction. eauto.
        intros.
        eapply IHfuel; eauto.
        exploit VSV. apply Heqo.
        apply var_in_sact_ok_inv. apply H. unfold var_lt. lia.
  Qed.

  Definition useful_vars
             (sf: simple_form (reg_t:=reg_t) (ext_fn_t:=ext_fn_t)) : list positive :=
    let todo := map snd (final_values sf) in
    fold_left (fun visited n => reachable_vars_aux (vars sf) n visited (S (Pos.to_nat n))) todo [].

  Lemma useful_vars_ok:
    forall sf (VSV: vvs_smaller_variables (vars sf)) l,
      useful_vars sf = l ->
      forall n1 (IN: In n1 l) v t a,
        (vars sf) ! n1 = Some (t, a) ->
        reachable_var (vars sf) a v ->
        In v l.
  Proof.
    intros sf VSV l <-.
    unfold useful_vars.
    pattern ((fold_left
       (fun (visited : list positive) (n : positive) =>
        reachable_vars_aux (vars sf) n visited (S (Pos.to_nat n)))
       (map snd (final_values sf)) []) ).
    apply fold_left_induction. easy.
    intros.
    eapply reachable_vars_aux_ok. 2: eauto. eauto. auto. lia. eauto. eauto. eauto.
  Qed.

  Lemma useful_vars_incl:
    forall sf (VSV: vvs_smaller_variables (vars sf)) l,
      useful_vars sf = l ->
      incl (map snd (final_values sf)) l.
  Proof.
    intros sf VSV l <-.
    unfold useful_vars. generalize (map snd (final_values sf)).

    Lemma fold_left_prop:
      forall {A B: Type} (P: A -> Prop) (f: A -> B -> A) (l: list B) x acc,
        In x l ->
        (forall a, P (f a x)) ->
        (forall a x, P a -> P (f a x)) ->
        P (fold_left f l acc).
    Proof.
      intros; eapply fold_left_ev with (I:= fun _ => True). auto. auto. auto. right; eexists; split; eauto.
    Qed.
    red; intros. eapply fold_left_prop. eauto.
    intros; eapply reachable_vars_aux_in; eauto. lia.
    intros; eapply reachable_vars_aux_incr; eauto.
  Qed.

  Theorem useful_vars_good:
    forall sf (VSV: vvs_smaller_variables (vars sf)) n1,
      In n1 (map snd (final_values sf)) ->
      forall v t a,
        (vars sf) ! n1 = Some (t, a) ->
        reachable_var (vars sf) a v ->
        In v (useful_vars sf).
  Proof.
    intros.
    eapply useful_vars_ok; eauto.
    eapply useful_vars_incl; eauto.
  Qed.

  Definition simple_form := simple_form (reg_t:=reg_t) (ext_fn_t:=ext_fn_t).

  Fixpoint eval_sact (vars: var_value_map) (a: sact) (fuel: nat) : option val :=
    match fuel with
    | O => None
    | S fuel =>
        match a with
        | SConst v => Some v
        | SVar v =>
            let/opt2 t, vv := vars ! v in
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

  Lemma eval_remove_var:
    forall vvs fuel a n,
      ~ reachable_var vvs a n ->
      eval_sact vvs a fuel = eval_sact (PTree.remove n vvs) a fuel.
  Proof.
    induction fuel; simpl; intros; eauto.
    destruct a; simpl; intros; eauto.
    - rewrite PTree.gro. unfold opt_bind; repeat destr. apply IHfuel. intro REACH.
      apply H. econstructor; eauto.
      intro; subst. apply H. econstructor.
    - rewrite <- ! IHfuel. eauto.
      intro REACH; apply H. apply reachable_var_if_false; auto.
      intro REACH; apply H. apply reachable_var_if_true; auto.
      intro REACH; apply H. apply reachable_var_if_cond; auto.
    - rewrite <- ! IHfuel. eauto.
      intro REACH; apply H. apply reachable_var_unop; auto.
    - rewrite <- ! IHfuel. eauto.
      intro REACH; apply H. apply reachable_var_binop2; auto.
      intro REACH; apply H. apply reachable_var_binop1; auto.
    - rewrite <- ! IHfuel. eauto.
      intro REACH; apply H. apply reachable_var_externalCall; auto.
  Qed.

  Lemma reachable_remove:
    forall a vvs a0 a1
           (RR : reachable_var (PTree.remove a0 vvs) a a1),
      reachable_var vvs a a1.
  Proof.
    induction 1; simpl; intros; eauto.
    - constructor.
    - rewrite PTree.grspec in H. destr_in H. congruence. econstructor; eauto.
    - eapply reachable_var_if_cond; eauto.
    - eapply reachable_var_if_true; eauto.
    - eapply reachable_var_if_false; eauto.
    - eapply reachable_var_binop1; eauto.
    - eapply reachable_var_binop2; eauto.
    - eapply reachable_var_unop; eauto.
    - eapply reachable_var_externalCall; eauto.
  Qed.

  Lemma eval_remove_vars:
    forall fuel a l vvs,
      Forall (fun n => ~ reachable_var vvs a n) l ->
      eval_sact vvs a fuel = eval_sact (fold_left (fun t n => PTree.remove n t) l vvs) a fuel.
  Proof.
    induction l; simpl; intros; eauto. inv H.
    rewrite <- IHl. eapply eval_remove_var. eauto.
    eapply Forall_impl; eauto. simpl.
    intros a1 NR RR; apply NR; clear NR.
    eapply reachable_remove; eauto.
  Qed.

  Definition remove_vars (sf: simple_form) : simple_form :=
    let useless :=
      List.filter
        (fun p =>
           if in_dec Pos.eq_dec p (useful_vars sf)
           then false else true
        )
        (map fst (PTree.elements (vars sf))) in
    {|
      final_values := final_values sf;
      vars := fold_left (fun t n => PTree.remove n t) useless (vars sf);
    |}.

  Lemma remove_vars_correct:
    forall sf (VSV:   vvs_smaller_variables (vars sf)) n,
      In n (map snd (final_values sf)) ->
      forall fuel,
        eval_sact (vars sf) (SVar n) fuel = eval_sact (vars (remove_vars sf)) (SVar n) fuel.
  Proof.
    intros. simpl.
    apply eval_remove_vars.
    rewrite Forall_forall. intros x IN.
    rewrite filter_In in IN.
    destruct IN as (IN & PRED).
    destr_in PRED; try congruence. clear Heqs PRED.
    intro RV; apply n0.
    inv RV.
    eapply useful_vars_incl; eauto.
    eapply useful_vars_good; eauto.
  Qed.

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

  Fixpoint replace_all_occurrences_in_sact (ua: sact) (from: positive) (to: val)
  : sact :=
    match ua with
    | SBinop ufn a1 a2 =>
      SBinop
        ufn (replace_all_occurrences_in_sact a1 from to)
        (replace_all_occurrences_in_sact a2 from to)
    | SUnop ufn a1 => SUnop ufn (replace_all_occurrences_in_sact a1 from to)
    | SVar v =>
      if Pos.eq_dec v from then SConst to
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
    (vars: var_value_map) (from: positive) (to: val)
  : var_value_map :=
    PTree.map
      (fun reg '(t, ua) =>  (t, replace_all_occurrences_in_sact ua from to))
      vars.

  (* TODO simplify as well: initial simpl pass then whenever change *)

  Definition replace_all_occurrences (sf: simple_form) (from: positive) (to: val)
  : simple_form := {|
    final_values := final_values sf;
    vars := replace_all_occurrences_in_vars (vars sf) from to; |}.

  (* TODO use coq record update here as well *)
  (* TODO variable in environment instead of inlining *)

  Definition max_var (vars: var_value_map (ext_fn_t:=ext_fn_t)) :=
    PTree.fold (fun acc k _ => Pos.max acc k) vars xH.

  Lemma vvs_range_max_var:
    forall vars,
      vvs_range vars (Pos.succ (max_var vars)).
  Proof.
    red; intros.
    unfold max_var.
    rewrite PTree.fold_spec.
    apply PTree.elements_correct in H.
    revert H.
    rewrite <- fold_left_rev_right.
    rewrite in_rev.
    generalize (rev (PTree.elements vars)).
    induction l; simpl; intros; eauto. easy.
    destruct H. subst. simpl. red; lia.
    apply IHl in H. red in H. red. lia.
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

  Definition vvs_size (vvs:var_value_map) m : nat :=
    PTree.fold (fun acc k '(t,a) =>
                  if Pos.ltb k m then
                    size_sact (ext_fn_t := ext_fn_t) a + acc
                  else acc
               ) vvs O.


  Lemma vvs_size1_aux:
    forall var n (LT: (var < n)%positive),
    forall (l : list (positive * (type * SimpleForm.sact))) (n0 n1 : nat),
      n1 <= n0 ->
      fold_left
        (fun (a : nat) (p : positive * (type * SimpleForm.sact)) =>
           let
             '(_, a0) := snd p in
           if (fst p <? var)%positive then size_sact a0 + a else a) l n1 <=
        fold_left
          (fun (a : nat) (p : positive * (type * SimpleForm.sact)) =>
             let
               '(_, a0) := snd p in
             if (fst p <? n)%positive then size_sact (ext_fn_t:=ext_fn_t) a0 + a else a) l n0.
  Proof.
    intros var n LT.

    induction l; simpl; intros; eauto.
    destr. apply IHl.
    destruct a; simpl in *. subst.
    generalize (Pos.ltb_spec p var).
    generalize (Pos.ltb_spec p n).
    intros A B. inv A; inv B; lia.
  Qed.

  Lemma vvs_size_le1:
    forall vvs var n,
      (var < n)%positive ->
      vvs_size vvs var  <= vvs_size vvs n.
  Proof.
    unfold vvs_size. intros.
    rewrite ! PTree.fold_spec.
    assert (O <= O)%nat. lia.
    revert H0. generalize O at 1 3.
    generalize O.
    generalize (PTree.elements vvs).
    eapply vvs_size1_aux; eauto.
  Qed.

  Lemma vvs_size_le2:
    forall vvs a var t n,
      (var < n)%positive ->
      vvs ! var = Some (t, a) ->
      vvs_size vvs var + size_sact a <= vvs_size vvs n.
  Proof.
    unfold vvs_size. intros.
    rewrite ! PTree.fold_spec.
    assert (O <= O)%nat. lia.
    revert H1. generalize O at 1 3.
    generalize O.
    apply PTree.elements_correct in H0. revert H0.
    generalize (PTree.elements vvs).
    induction l; simpl; intros; eauto. easy.
    destr.
    destruct H0.
    subst. simpl in *. inv Heqp.
    admit.
    eapply IHl; eauto.
    generalize (Pos.ltb_spec (fst a0) var).
    generalize (Pos.ltb_spec (fst a0) n).
    intros A B. inv A; inv B; lia.
  Admitted.

  Lemma interp_sact_eval_sact_aux:
    forall (vvs: var_value_map) (VSV: vvs_smaller_variables vvs),
    forall a v,
      interp_sact (sigma:=sigma) vvs a v ->
      forall n, (forall var, var_in_sact a var -> var < n)%positive ->
      exists m, eval_sact vvs a (m + size_sact a) = Some v /\ (m <= Pos.to_nat n + vvs_size vvs n)%nat.
  Proof.
    induction 2; simpl; intros; eauto.
    - destruct (IHinterp_sact var) as (m1 & I1 & LE1). intros; eapply VSV. eauto. auto.
      eexists. split. rewrite Nat.add_1_r. simpl. rewrite H; simpl; eauto.
      assert (var < n)%positive. eapply H1. constructor.
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
      eval_sact vvs a (Pos.to_nat (Pos.succ (max_var vvs)) + vvs_size vvs ((Pos.succ (max_var vvs))) + size_sact a) = Some v.
  Proof.
    intros.
    generalize (vvs_range_max_var vvs). intro VR.
    generalize (wt_sact_valid_vars vvs _ VR _ _ H). intro VALID.
    generalize (interp_sact_eval_sact_aux _ VSV a v H0 _ VALID).
    intros (m & EVAL & LE).
    eapply eval_sact_more_fuel. eauto. lia.
  Qed.

  Definition do_eval_sact vvs a :=
    eval_sact vvs a (Pos.to_nat (Pos.succ (max_var vvs)) + vvs_size vvs ((Pos.succ (max_var vvs))) + size_sact a).

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

  (* Lemma interp_sact_same_below: *)
  (*   forall vvs1 vvs2 a res n (VSV: vvs_smaller_variables vvs1), *)
  (*     (forall v, var_in_sact a v -> v < n) -> *)
  (*     (forall x, x < n -> list_assoc vvs1 x = list_assoc vvs2 x) -> *)
  (*     interp_sact (sigma:=sigma) vvs1 a res -> interp_sact (sigma:=sigma) vvs2 a res. *)
  (* Proof. *)
  (*   induction 4; simpl; intros; eauto. *)
  (*   - assert (var < n). apply H. constructor. *)
  (*     econstructor; eauto. erewrite <- H0; eauto. *)
  (*     apply IHinterp_sact. intros; eapply VSV in H1. apply H1 in H4. red in H4. lia. *)
  (*   - constructor. *)
  (*   - econstructor. eapply IHinterp_sact1. intros; eapply H; eapply var_in_if_cond; eauto. *)
  (*     eapply IHinterp_sact2. intros; eapply H. *)
  (*     destr_in H1. eapply var_in_if_true; eauto. eapply var_in_if_false; eauto. *)
  (*   - econstructor. eapply IHinterp_sact. intros; eapply H; eapply var_in_sact_unop; eauto. auto. *)
  (*   - econstructor. eapply IHinterp_sact1. intros; eapply H; eapply var_in_sact_binop_1; eauto. *)
  (*     eapply IHinterp_sact2. intros; eapply H; eapply var_in_sact_binop_2; eauto. auto. *)
  (*   - econstructor. eapply IHinterp_sact. intros; eapply H; eapply var_in_sact_external; eauto. *)
  (* Qed. *)

  (* Lemma map_filter: *)
  (*   forall {A: Type} (f: A -> A) g, *)
  (*     (forall x, g x = g (f x)) -> *)
  (*     forall l, *)
  (*       map f (filter g l) = filter g (map f l). *)
  (* Proof. *)
  (*   induction l; simpl; intros; eauto. *)
  (*   rewrite <- H. destruct (g a). simpl. congruence. auto. *)
  (* Qed. *)

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
      forall a n (BELOW: forall v, var_in_sact a v -> (v < n)%positive) res,
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
        (forall v, var_in_sact a v -> (v < n)%positive) ->
        forall res,
          interp_sact (sigma:=sigma) vvs a res ->
          interp_sact (sigma:=sigma)
                      (replace_all_occurrences_in_vars
                         (PTree.remove var vvs) var v')
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
        rewrite PTree.gmap. rewrite PTree.gro; auto. rewrite H. simpl; eauto.
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
        (forall v, var_in_sact a v -> (v < n)%positive) ->
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
        rewrite PTree.gmap. setoid_rewrite H. simpl; eauto.
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
    setoid_rewrite PTree.gmap in H0.
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
        setoid_rewrite PTree.gmap. setoid_rewrite H. simpl; eauto.
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
      setoid_rewrite PTree.gmap.
      setoid_rewrite H. simpl; eauto.
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
    setoid_rewrite PTree.gmap in H2.
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
  Lemma wt_sact_var_exists:
    forall a vvs t (WTa: wt_sact (Sigma:=Sigma) vvs a t),
    forall v, var_in_sact a v -> In v (map fst (PTree.elements vvs)).
  Proof.
    induction 1; simpl; intros; eauto.
    - inv H0. apply PTree.elements_correct in H.  apply (in_map fst) in H.  auto.
    - inv H0.
    - inv H; eauto.
    - inv H0; eauto.
    - inv H0; eauto.
    - inv H; eauto.
  Qed.

  (* Fixpoint simplify_var2 n (vvs: var_value_map) : list (nat * val) := *)
  (*   match n, vvs with *)
  (*   | O, _ | _, [] => [] *)
  (*   | S n, (var,(t,a))::vvs => *)
  (*       match eval_sact_no_vars a with *)
  (*       | Some v => *)
  (*           (var,v)::(simplify_var2 n (replace_all_occurrences_in_vars vvs var v)) *)
  (*       | None => [] *)
  (*       end *)
  (*   end. *)

  (* Inductive sorted_vvs : var_value_map -> Prop := *)
  (* | sorted_nil: sorted_vvs [] *)
  (* | sorted_cons: *)
  (*   forall n t a vvs *)
  (*     (NOvars: forall v, var_in_sact (ext_fn_t:=ext_fn_t) a v -> v < n /\ ~ In v (map fst vvs)) *)
  (*     (VarsBelow: forall x t y, list_assoc vvs x = Some (t,y) -> forall v, var_in_sact (ext_fn_t:=ext_fn_t) y v -> v < n) *)
  (*     (Sorted: sorted_vvs vvs), *)
  (*     sorted_vvs ((n,(t,a))::vvs). *)
  (* Lemma simplify_var2_correct: *)
  (*   forall n *)
  (*          vvs (S: sorted_vvs vvs) l *)
  (*          (GE: n >= List.length vvs) *)
  (*          (SIMP: simplify_var2 n vvs = l) *)
  (*          (WTv: wt_vvs (Sigma:=Sigma) vvs) *)
  (*          (* (VSV: vvs_smaller_variables (ext_fn_t:=ext_fn_t) vvs) *) *)
  (*          (ND: NoDup (map fst vvs)) *)
  (*          k *)
  (*          (IN: In k (map fst vvs)) v *)
  (*          (INT: interp_sact (sigma:=sigma) vvs (SVar k) v), *)
  (*     In (k, v) l. *)
  (* Proof. *)
  (*   induction n; simpl; intros; eauto. *)
  (*   assert (vvs = []). destruct vvs; simpl in *; auto. lia. subst. easy. *)
  (*   destruct vvs. simpl in *. lia. simpl in *. inv S. simpl in *. *)
  (*   edestruct (eval_sact_no_vars_succeeds a). *)
  (*   { *)
  (*     intros v0 VIS. *)
  (*     specialize (WTv n0 a t). rewrite list_assoc_cons, eq_dec_refl in WTv. *)
  (*     trim WTv; auto. *)
  (*     eapply wt_sact_var_exists in WTv; eauto. simpl in WTv. *)
  (*     apply NOvars in VIS. destruct VIS. destruct WTv. lia. congruence. *)
  (*   } eapply WTv.  rewrite list_assoc_cons, eq_dec_refl; eauto. rewrite H. *)
  (*   destruct IN as [EQ|IN]. *)
  (*   - subst. inv INT. rewrite list_assoc_cons in H1. rewrite eq_dec_refl in H1. inv H1. *)
  (*     exploit eval_sact_no_vars_interp. eauto. intros INT2. *)
  (*     exploit @interp_sact_determ. apply INT2. apply H2. intros ->. left; auto. *)
  (*   - right. *)
  (*     eapply IHn. 3: eauto. *)

  (*     Lemma sorted_vvs_replace: *)
  (*       forall vvs, *)
  (*         sorted_vvs vvs -> *)
  (*         forall n x, *)
  (*           sorted_vvs (replace_all_occurrences_in_vars vvs n x). *)
  (*     Proof. *)
  (*       induction 1; simpl; intros; eauto. constructor. *)
  (*       constructor; auto. *)
  (*       intros v VIS. apply var_in_sact_replace in VIS. *)
  (*       unfold replace_all_occurrences_in_vars. *)
  (*       rewrite map_map. rewrite in_map_iff. *)
  (*       apply NOvars in VIS. destruct VIS.  split; auto. *)
  (*       intros ((nn & (tt&aa)) & EQ & IN). simpl in EQ. subst. *)
  (*       apply (in_map fst) in IN. simpl in IN. eauto. *)
  (*       intros x0 t0 y. *)
  (*       unfold replace_all_occurrences_in_vars. *)
  (*       rewrite list_assoc_map with (g:= fun '(t,a) => (t, replace_all_occurrences_in_sact a n0 x)). *)
  (*       2: intros; repeat destr. *)
  (*       unfold option_map. destr. destr. intro A; inv A. *)
  (*       intros v VIS. *)
  (*       apply var_in_sact_replace in VIS. eapply VarsBelow; eauto. *)
  (*     Qed. *)
  (*     eapply sorted_vvs_replace. eauto. *)
  (*     setoid_rewrite map_length. fold sact in GE. lia. *)
      
  (*     eapply wt_vvs_replace; eauto. red; intros. *)
  (*     exploit (WTv v0). rewrite list_assoc_cons. *)
  (*     destr. apply list_assoc_in_keys in H0. inv ND. congruence. eauto. *)

  (*     Lemma wt_vvs_cons_inv: *)
  (*       forall n t a vvs s t0, *)
  (*         ~ var_in_sact s n -> *)
  (*         wt_sact (Sigma:=Sigma) ((n,(t,a))::vvs) s t0 -> *)
  (*         wt_sact (Sigma:=Sigma) vvs s t0. *)
  (*     Proof. *)
  (*       induction s; simpl; intros; eauto. *)
  (*       inv H0. rewrite list_assoc_cons in H2. destr_in H2. inv H2. elim H. constructor. *)
  (*       econstructor; eauto. *)
  (*       inv H0; econstructor; eauto. *)
  (*       - inv H0. *)
  (*         econstructor; eauto. *)
  (*         eapply IHs1; eauto. *)
  (*         intro VIS; apply H. apply var_in_if_cond; auto. *)
  (*         eapply IHs2; eauto. *)
  (*         intro VIS; apply H. apply var_in_if_true; auto. *)
  (*         eapply IHs3; eauto. *)
  (*         intro VIS; apply H. apply var_in_if_false; auto. *)
  (*       - inv H0. *)
  (*         econstructor; eauto. *)
  (*         eapply IHs; eauto. *)
  (*         intro VIS; apply H. apply var_in_sact_unop; auto. *)
  (*       - inv H0. *)
  (*         econstructor; eauto. *)
  (*         eapply IHs1; eauto. *)
  (*         intro VIS; apply H. apply var_in_sact_binop_1; auto. *)
  (*         eapply IHs2; eauto. *)
  (*         intro VIS; apply H. apply var_in_sact_binop_2; auto. *)
  (*       - inv H0. *)
  (*         econstructor; eauto. *)
  (*         eapply IHs; eauto. *)
  (*         intro VIS; apply H. apply var_in_sact_external; auto. *)
  (*     Qed. *)
  (*     apply wt_vvs_cons_inv. *)
  (*     intro VIS. *)
  (*     eapply VarsBelow in VIS. lia. eauto. *)
  (*     Lemma sorted_lt: *)
  (*       forall *)
  (*         sorted_vvs vvs -> *)
  (*         list_assoc vvs v = Some (t,s) -> *)
  (*         var_in_sact s n -> *)

  (*     exploit (wt_sact_vars_exist vvs s). eapply WTv. econstructor; eauto. constructor. *)

  (* Qed. *)

  Definition simplify_var (sf: simple_form) var :=
    match (vars sf) ! var with
      Some (t, a) =>
           match eval_sact_no_vars a with
             Some v => (replace_all_occurrences sf var v, [(var,v)])
           | None => (sf, [])
           end
    | _ => (sf, [])
    end.
  Definition simplify_var' (sf: simple_form) var :=
    match (vars sf) ! var with
      Some (t, a) =>
           match eval_sact_no_vars a with
             Some v => ([(var,v)])
           | None => ([])
           end
    | _ => ([])
    end.

  Lemma simplify_var_eq:
    forall sf var, simplify_var' sf var = snd (simplify_var sf var).
  Proof.
    intros; unfold simplify_var, simplify_var'. repeat destr; auto.
  Qed.
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
         (vars sf) ! x = Some (t,y) ->
              interp_sact (sigma:=sigma) (vars sf) y res ->
              (exists y' ,
                  (vars sf') ! x = Some (t,y') /\
                    interp_sact (sigma:=sigma) (vars sf') y' res)
     ) /\
  (forall x t y v, (vars sf') ! x = Some (t,y) ->
                   var_in_sact y v -> ~ In v (map fst l)) /\
        (forall x t y,
            (vars sf') ! x = Some (t, y) ->
            exists y' ,
              (vars sf) ! x = Some (t, y') /\
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
        setoid_rewrite PTree.gmap.
        setoid_rewrite Heqo. simpl; eauto.
        intros; repeat destr.
        eapply interp_sact_replace_one. eauto.
        econstructor. eauto.
        eapply eval_sact_no_vars_interp; eauto.
        eapply wt_sact_valid_vars. 2: eapply (WT var). apply vvs_range_max_var.
        eauto.
        eapply eval_sact_no_vars_interp; eauto.
      + econstructor.
        setoid_rewrite PTree.gmap.
        setoid_rewrite Heqo. simpl; eauto.
        Unshelve. exact Sigma.
    - simpl. constructor. easy. constructor.
    - simpl. intros.
      erewrite <- interp_sact_replace_iff; eauto.
      eapply interp_sact_replace_one; eauto.
      + econstructor. eauto. eapply eval_sact_no_vars_interp; eauto.
      + intros. eapply wt_sact_valid_vars. 3: eauto. 2: eauto.
        apply vvs_range_max_var.
      + econstructor.
        setoid_rewrite PTree.gmap.
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
      setoid_rewrite PTree.gmap.
      setoid_rewrite H. simpl; eauto.
      eexists; split; eauto.
      eapply interp_sact_replace_one; eauto.
      + econstructor. eauto. eapply eval_sact_no_vars_interp; eauto.
      + intros. eapply wt_sact_valid_vars. 3: eauto. 2: eauto.
        apply vvs_range_max_var.
    - simpl.
      setoid_rewrite PTree.gmap.
      unfold option_map; intros x t0 y v0 OM; repeat destr_in OM; inv OM.
      intros VIS [EQ|[]]. subst.

      eapply var_not_in_sact_replace; eauto.
    - simpl. intros x t0 y.
      setoid_rewrite PTree.gmap.
      unfold option_map; intros OM; repeat destr_in OM; inv OM.
      setoid_rewrite Heqo1. eexists; split; eauto.
      eapply var_in_sact_replace; eauto.
    - repeat refine (conj _ _); eauto. constructor.
    - repeat refine (conj _ _); eauto. constructor.
  Qed.


  Lemma simplify_vars_preserves:
    forall (lvars: list positive) sf l sf' l'
           (FL: fold_left
                  (fun '(sf, l) var =>
                     let '(sf, l1) := simplify_var sf var in
                     (sf,l1++l)) lvars (sf, l) = (sf', l'))
           (WTV: wt_vvs (Sigma:=Sigma) (vars sf))
           (VSV: vvs_smaller_variables (vars sf))
           (NDlvars: NoDup lvars)
           (ND: NoDup (map fst l))
           (DISJ: forall x, In x lvars -> ~ In x (map fst l))
           (NIV: (forall x t y v, (vars sf) ! x = Some (t,y) ->
                                  var_in_sact y v -> ~ In v (map fst l))),
      vvs_smaller_variables (vars sf') /\
        wt_vvs (Sigma:=Sigma) (vars sf') /\ (incl l l') /\ NoDup (map fst l')
      /\ (forall x t y v, (vars sf') ! x = Some (t,y) ->
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
    forall (lvars: list positive) sf l sf' l'
           (FL: fold_left
                  (fun '(sf, l) var =>
                     let '(sf, l1) := simplify_var sf var in
                     (sf,l1++l)) lvars (sf, l) = (sf', l'))
           (SORTED: Sorted Pos.lt lvars)
           (VARS_EXIST: Forall (fun v => exists a t, (vars sf) ! v = Some (t,a)) lvars)
           (WTV: wt_vvs (Sigma:=Sigma) (vars sf))
           (ACC: Forall (fun '(var, v) => interp_sact (sigma:=sigma) (vars sf) (SVar var) v) l)
           (VSV: vvs_smaller_variables (vars sf))
           (NOvarsl: forall x t y v,
               (vars sf) ! x = Some (t,y) ->
               var_in_sact y v -> ~ In v (map fst l) /\ In v lvars)
    ,
      (forall x t y res,
          (vars sf) ! x = Some (t,y) ->
          interp_sact (sigma:=sigma) (vars sf) y res ->
          (exists y' ,
              (vars sf') ! x = Some (t,y') /\
                interp_sact (sigma:=sigma) (vars sf') y' res)
      ) /\
        vvs_smaller_variables (vars sf') /\
        wt_vvs (Sigma:=Sigma) (vars sf') /\
        Forall (fun '(var, v) => interp_sact (sigma:=sigma) (vars sf') (SVar var) v) l' /\
        (forall x t y v, (vars sf') ! x = Some (t,y) ->
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
        setoid_rewrite PTree.gmap.
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
           setoid_rewrite PTree.gmap.
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
           (NV: forall x t y, vvs ! x = Some (t,y) -> ~ var_in_sact y v)
           a t
           (WTa: wt_sact (Sigma:=Sigma) vvs a t)
           (NVa: ~ var_in_sact a v),
      wt_sact (Sigma:=Sigma) (PTree.remove v vvs) a t.
  Proof.
    induction 2; simpl; intros; eauto.
    - econstructor; eauto.
      rewrite PTree.gro; eauto. intro; subst; apply NVa; constructor.
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

  (* Lemma eval_sact_bound: *)
  (*   forall vvs : var_value_map, *)
  (*     vvs_smaller_variables vvs -> *)
  (*     forall (a : SimpleForm.sact) t (WTa: wt_sact (Sigma:=Sigma) vvs a t), *)
  (*       let bnd := (S (max_var vvs) + vvs_size vvs (S (max_var vvs)) + size_sact a) in *)
  (*       forall m, m >= bnd -> *)
  (*       eval_sact vvs a m = None -> *)
  (*       forall n, n >= m -> eval_sact vvs a n = None. *)
  (* Proof. *)
  (*   intros. *)
  (*   destruct (eval_sact vvs a n) eqn:?; auto. *)
  (*   eapply eval_sact_interp_sact in Heqo. *)
  (*   eapply interp_sact_eval_sact in Heqo; eauto. *)
  (*   eapply eval_sact_more_fuel with (n2:= m) in Heqo. congruence. unfold bnd in H0. lia. *)
  (* Qed. *)

  (* Lemma remove_var_correct: *)
  (*   forall vvs (VSV: vvs_smaller_variables vvs) (* (WTvvs: wt_vvs (Sigma:=Sigma) vvs) *) v *)
  (*          (NV: forall x t y, vvs ! x = Some (t,y) -> ~ var_in_sact y v) *)
  (*          a *)
  (*          t (WTa: wt_sact (Sigma:=Sigma) vvs a t) *)
  (*          (NVa: ~ var_in_sact a v) res, *)
  (*     interp_sact (sigma:=sigma) vvs a res <-> *)
  (*       interp_sact (sigma:=sigma) (filter (fun '(n,_) => negb (beq_dec n v)) vvs) a res. *)
  (* Proof. *)
  (*   intros. eapply interp_eval_iff. eauto. *)
  (*   red; intros. *)
  (*   generalize (list_assoc_filter2 vvs v v0). rewrite H. destr. *)
  (*   rewrite beq_dec_false_iff in Heqb. intros. symmetry in H1. eauto. eauto. *)
  (*   eapply wt_sact_remove_one; eauto. *)

  (*   (* set (F := fun vvs => (S (max_var vvs) + vvs_size vvs (S (max_var vvs)) + size_sact a)). *) *)
  (*   (* set (vvs2 := (filter (fun '(n,_) => negb (beq_dec n v)) vvs)). *) *)
  (*   (* exists (max (F vvs) (F vvs2)). *) *)
  (*   exists O. intros n0 _. *)
  (*   intros. *)
  (*   clear VSV WTa. *)
  (*   revert a NVa. induction n0; simpl; intros; eauto. *)
  (*   unfold opt_bind. *)
  (*   destr. *)
  (*   - rewrite <- list_assoc_filter. repeat destr.  eauto. *)
  (*     intros; rewrite negb_true_iff, beq_dec_false_iff; auto. *)
  (*     intro; subst. apply NVa. constructor. *)
  (*   - rewrite <- IHn0. repeat destr. *)
  (*     eapply IHn0. intro VIS; apply NVa; eapply var_in_if_true; auto. *)
  (*     eapply IHn0. intro VIS; apply NVa; eapply var_in_if_false; auto. *)
  (*     intro VIS; apply NVa; eapply var_in_if_cond; auto. *)
  (*   - rewrite <- IHn0. repeat destr. *)
  (*     intro VIS; apply NVa; eapply var_in_sact_unop; auto. *)
  (*   - rewrite <- ! IHn0. auto. *)
  (*     intro VIS; apply NVa; eapply var_in_sact_binop_2; auto. *)
  (*     intro VIS; apply NVa; eapply var_in_sact_binop_1; auto. *)
  (*   - rewrite <- IHn0. repeat destr. *)
  (*     intro VIS; apply NVa; eapply var_in_sact_external; auto. *)
  (* Qed. *)

  (* Lemma remove_var_preserves_vsv: *)
  (*   forall l sf (VSV: vvs_smaller_variables (vars sf)), *)
  (*     vvs_smaller_variables (vars (remove_by_name_var sf l)). *)
  (* Proof. *)
  (*   simpl. red; intros. *)
  (*   generalize (list_assoc_filter2 (vars sf) l v). rewrite H. destr. *)
  (*   rewrite beq_dec_false_iff in Heqb. intros. symmetry in H1. eauto. *)
  (* Qed. *)

  (* Lemma remove_vars_preserves_vsv: *)
  (*   forall l sf (VSV: vvs_smaller_variables (vars sf)), *)
  (*     vvs_smaller_variables (vars (fold_left remove_by_name_var l sf)). *)
  (* Proof. *)
  (*   induction l; simpl; intros; eauto. *)
  (*   apply IHl. apply remove_var_preserves_vsv. auto. *)
  (* Qed. *)

  (* Lemma remove_var_preserves_wt_vvs: *)
  (*   forall l sf (WT_VVS: wt_vvs (Sigma:=Sigma) (vars sf)) *)
  (*          (NV: forall (x : nat) (t0 : type) (y : SimpleForm.sact), *)
  (*              list_assoc (vars sf) x = Some (t0, y) -> ~ var_in_sact y l), *)
  (*     wt_vvs (Sigma:=Sigma) (vars (remove_by_name_var sf l)). *)
  (* Proof. *)
  (*   simpl. red; intros. *)
  (*   generalize (list_assoc_filter2 (vars sf) l v). rewrite H. destr. *)
  (*   rewrite beq_dec_false_iff in Heqb. intros. symmetry in H0. eauto. *)
  (*   eapply wt_sact_remove_one; eauto. *)
  (* Qed. *)

  (* Lemma remove_vars_preserves_wt_vvs: *)
  (*   forall l sf (WT_VVS: wt_vvs (Sigma:=Sigma) (vars sf)) *)
  (*          (NV: forall (x : nat) (t0 : type) (y : SimpleForm.sact) v, *)
  (*              list_assoc (vars sf) x = Some (t0, y) -> var_in_sact y v -> ~ In v l), *)
  (*     wt_vvs (Sigma:=Sigma) (vars (fold_left remove_by_name_var l sf)). *)
  (* Proof. *)
  (*   induction l; simpl; intros; eauto. *)
  (*   apply IHl. *)
  (*   apply remove_var_preserves_wt_vvs; auto. *)
  (*   intros x t0 y GET VIS; eapply NV; eauto. *)
  (*   simpl. *)
  (*   intros x t0 y v GET VIS IN. *)
  (*   generalize (list_assoc_filter2 (vars sf) a x). rewrite GET. destr. *)
  (*   rewrite beq_dec_false_iff in Heqb. intros. symmetry in H. eapply NV; eauto. *)
  (* Qed. *)

  (* Lemma remove_vars_correct: *)
  (*   forall l sf (VSV: vvs_smaller_variables (vars sf))  *)
  (*          (NV: forall v x t y, list_assoc (vars sf) x = Some (t,y) -> var_in_sact y v -> ~ In v l) *)
  (*          a *)
  (*          t (WTa: wt_sact (Sigma:=Sigma) (vars sf) a t) *)
  (*          (NVa: forall v, var_in_sact a v -> ~ In v l) res, *)
  (*     interp_sact (sigma:=sigma) (vars sf) a res <-> *)
  (*       interp_sact (sigma:=sigma) (vars (fold_left remove_by_name_var l sf)) a res. *)
  (* Proof. *)
  (*   induction l; simpl; intros; eauto. tauto. *)
  (*   rewrite <- IHl. *)
  (*   - simpl. eapply remove_var_correct; eauto. *)
  (*     + intros x t0 y GET VIS; eapply NV; eauto. *)
  (*     + intro VIS; eapply NVa; eauto. *)
  (*   - eapply remove_var_preserves_vsv; eauto. *)
  (*   - simpl. intros. *)
  (*     generalize (list_assoc_filter2 (vars sf) a x). rewrite H. destr. *)
  (*     rewrite beq_dec_false_iff in Heqb. intros. symmetry in H1. eauto. *)
  (*     eapply NV in H1. 2: eauto. intuition. *)
  (*   - simpl. eapply wt_sact_remove_one; eauto. *)
  (*     + intros x t0 y GET VIS; eapply NV in VIS; eauto. *)
  (*     + intro VIS; eapply NVa; eauto. *)
  (*   - intros v VIS IN; eapply NVa; eauto. *)
  (* Qed. *)


  Definition inlining_pass (sf: simple_form)
    : list (positive * val) :=
    (* Try to determine the value of variables *)
    let ks := PosSort.sort (map fst (PTree.elements (vars sf))) in
    let '(sf,l) := fold_left
                     (fun '(sf,l) var =>
                        let '(sf,l1) := simplify_var sf var in
                        (sf, l1++l))
                     ks (sf,[]) in
  l.

  Lemma Sorted_strict:
    forall le1 le2 (STRICT: forall x y, le2 x y <-> (le1 x y /\ x <> y))
           (l: list positive),
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
      Sorted Pos.lt (PosSort.sort l).
  Proof.
    intros.
    generalize (PosSort.Sorted_sort l). intros.
    eapply Sorted_strict. 2: apply H0.
    intros. simpl. fold (Pos.leb x y).  unfold is_true. rewrite Pos.leb_le. lia.
    eapply Permutation.Permutation_NoDup. 2: apply H.
    apply PosSort.Permuted_sort.
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

  Lemma inlining_pass_correct:
    forall sf l
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
    eapply Permutation.Permutation_NoDup. apply PosSort.Permuted_sort.
    apply PTree.elements_keys_norepet. constructor.
    intros.
    exploit simplify_vars_correct; eauto.
    - apply sorted_lt. apply PTree.elements_keys_norepet.
    - eapply Permutation.Permutation_Forall. apply PosSort.Permuted_sort.
      rewrite Forall_forall.  intros x.  rewrite in_map_iff.
      intros ((x0 & (?&?)) & EQ & IN). subst. simpl.
      erewrite PTree.elements_complete; eauto.
    - simpl. intros x t y v0 GET VIS. split. auto.
      eapply Permutation.Permutation_in. apply PosSort.Permuted_sort.
      exploit WT. apply GET. intro WTy.
      eapply wt_sact_var_exists; eauto.
    - intros (IMPL & VVS' & WT' & INTERPl & NIV & _ & IN).
      edestruct (IN v).
      eapply Permutation.Permutation_in. apply PosSort.Permuted_sort.
      inv INT.
      eapply PTree.elements_correct in H1. apply (in_map fst) in H1; auto.
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

  (* Lemma wt_sact_replace_vars_gen: *)
  (*   forall vvs f a t, *)
  (*     wt_sact (Sigma:=Sigma) vvs a t -> *)
  (*     wt_sact (Sigma:=Sigma) (map (fun '(n,(t,u)) => (n,(t,f u))) vvs) a t. *)
  (* Proof. *)
  (*   induction 1; simpl; intros; eauto. *)
  (*   - econstructor. *)
  (*     erewrite list_assoc_map with (g := fun '(t,a) => (t, f a)). 2: intros; repeat destr. *)
  (*     rewrite H. reflexivity. *)
  (*   - econstructor; eauto. *)
  (*   - econstructor; eauto. *)
  (*   - econstructor; eauto. *)
  (*   - econstructor; eauto. *)
  (*   - econstructor; eauto. *)
  (* Qed. *)

  (* Lemma wt_vvs_replace_gen: *)
  (*   forall vvs f, *)
  (*     wt_vvs (Sigma:=Sigma) vvs -> *)
  (*     (forall t u, wt_sact (Sigma:=Sigma) vvs u t -> wt_sact (Sigma:=Sigma) vvs (f u) t) -> *)
  (*     wt_vvs (Sigma:=Sigma) (map (fun '(n,(t,u)) => (n,(t,f u)))vvs). *)
  (* Proof. *)
  (*   unfold wt_vvs; intros. *)
  (*   setoid_rewrite list_assoc_map with (g:= fun '(t,a) => (t, f a)) in H1. *)
  (*   2: intros; repeat destr. *)
  (*   unfold option_map in H1; repeat destr_in H1; inv H1. *)
  (*   eapply wt_sact_replace_vars_gen. eapply H0; eauto. *)
  (* Qed. *)


  (* Lemma interp_map_vvs: *)
  (*   forall vvs (VSV: vvs_smaller_variables vvs) (WTvvs: wt_vvs (Sigma:=Sigma) vvs) *)
  (*          a *)
  (*          t (WTa: wt_sact (Sigma:=Sigma) vvs a t) *)
  (*          (* (NVa: ~ var_in_sact a v) *) res f *)
  (*          (VARS: forall v s, var_in_sact (f s) v -> var_in_sact s v) *)
  (*          (* (WTf: forall s t, wt_sact (Sigma:=Sigma) vvs s t ->  wt_sact (Sigma:=Sigma) vvs (f s) t) *) *)
  (*          (* (WTf: forall s t, wt_sact (Sigma:=Sigma) vvs s t ->  wt_sact (Sigma:=Sigma) (map (fun '(n,(t,a)) => (n, (t, f a))) vvs) s t) *) *)
  (*          (WTf2: forall s t, wt_sact (Sigma:=Sigma) vvs s t ->  wt_sact (Sigma:=Sigma) vvs (f s) t) *)
  (*          (CORRECT: forall vvs s t n res, *)
  (*              wt_vvs (Sigma:=Sigma) vvs -> *)
  (*              wt_sact (Sigma:=Sigma) vvs s t -> *)
  (*              eval_sact vvs s n = Some res -> *)
  (*              eval_sact vvs (f s) n = Some res *)
  (*          ) *)
  (*   , *)
  (*     interp_sact (sigma:=sigma) vvs a res -> *)
  (*     interp_sact (sigma:=sigma) (map (fun '(n,(t,a)) => (n, (t, f a))) vvs) a res. *)
  (* Proof. *)
  (*   intros. *)
  (*   eapply interp_sact_eval_sact in H; eauto. *)
  (*   revert H. generalize (S (max_var vvs) + vvs_size vvs (S (max_var vvs)) + size_sact a). intros. *)
  (*   eapply eval_sact_interp_sact with (fuel:=n). *)
  (*   revert a res H t WTa. *)
    
  (*   induction n. simpl; intros; eauto. *)
  (*   simpl. unfold opt_bind. *)
  (*   intros a res EVAL. *)
  (*   destr_in EVAL. *)
  (*   - repeat destr_in EVAL. 2: inv EVAL. *)
  (*     rewrite list_assoc_map with (g:=fun '(t,a) => (t, f a)). rewrite Heqo. simpl. *)
  (*     intros; eapply IHn. eauto. eapply WTvvs in Heqo. eapply WTf2. eauto. *)
  (*     intros; repeat destr. *)
  (*   - auto. *)
  (*   - intros t WTa; inv WTa. *)
  (*     destr_in EVAL. 2: inv EVAL. *)
  (*     erewrite IHn; eauto. *)
  (*     repeat destr_in EVAL; try now inv EVAL. subst. *)
  (*     eapply IHn; eauto. *)
  (*     eapply IHn; eauto. *)
  (*   - intros t WTa; inv WTa. *)
  (*     destr_in EVAL. 2: inv EVAL. *)
  (*     erewrite IHn; eauto. *)
  (*   - intros t WTa; inv WTa. *)
  (*     destr_in EVAL. 2: inv EVAL. *)
  (*     destr_in EVAL. 2: inv EVAL. *)
  (*     erewrite IHn; eauto. *)
  (*     erewrite IHn; eauto. *)
  (*   - intros t WTa; inv WTa. *)
  (*     destr_in EVAL. 2: inv EVAL. *)
  (*     erewrite IHn; eauto. *)
  (* Qed. *)


  Definition interp_cycle (sf: simple_form) : UREnv :=
    let sf := remove_vars sf in
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
    intros (WTV & VSV & INFINAL & SPECFINAL).
    unfold interp_cycle. unfold commit_update.
    apply create_funext. intro k.
    simpl.
    destruct (SPECFINAL k) as (n & GET & INTERP). rewrite GET.


    Lemma wt_vvs_remove_vars:
      forall sf,
        wt_vvs (Sigma:=Sigma) (vars sf) ->
        wt_vvs (Sigma:=Sigma) (vars (remove_vars sf)).
    Proof.
      red; intros.
      simpl in *.
    Admitted.

    Lemma vsv_remove_vars:
      forall sf,
        vvs_smaller_variables (vars sf) ->
        vvs_smaller_variables (vars (remove_vars sf)).
    Proof.
      red; intros.
      simpl in *.
      revert H0 v' H1.
      apply fold_left_induction. eauto.
      intros.
      rewrite PTree.grspec in H2; destr_in H2; try congruence. eauto.
    Qed.

    assert (VSV2:=vsv_remove_vars _ VSV).
    assert (WTV2:=wt_vvs_remove_vars _ WTV).

    generalize (inlining_pass_correct _ _ eq_refl VSV2 WTV2).
    intros (ND2 & INLINING).

    inversion INTERP. subst.
    exploit INLINING. apply GET.
    rewrite interp_eval_iff.
    6: (exists O; intros; symmetry; eapply remove_vars_correct; eauto).
    apply INTERP. auto. auto.
    admit. econstructor. eauto.
    eapply list_assoc_in in GET. apply (in_map snd) in GET; eauto.
    intro IN. apply in_list_assoc in IN.
    setoid_rewrite IN.
    auto. auto.
  Admitted.

  Lemma getenv_interp_cycle:
    forall
      {finreg: FiniteType reg_t}
      (rules: rule_name_t -> daction)
      (s: schedule)
      (GS: good_scheduler s)
      (WTr: Wt.wt_renv R REnv r)
      (TA:
        forall rule,
          exists t,
            wt_daction (R:=R) (Sigma:=Sigma) pos_t string string [] (rules rule) t) k,
      let sf := (SimpleForm.schedule_to_simple_form (Sigma:=Sigma) REnv r R rules s) in
      exists n s t,
        list_assoc (final_values sf) k = Some n /\
          (vars sf) ! n = Some (t, s) /\
          do_eval_sact (vars sf) s = Some (getenv REnv (interp_cycle sf) k).
  Proof.
    intros.
    unfold interp_cycle. rewrite getenv_create.
    Opaque vvs_size. Opaque max_var. Opaque size_sact. Opaque eval_sact.
    generalize (schedule_to_simple_form_ok
                  (wt_sigma:=wt_sigma)
                  REnv r R rules _ GS _ eq_refl TA WTr). simpl.
    intros (WTV & VSV  & INFINAL & SPECFINAL).
    destruct (SPECFINAL k) as (n & GET & INTERP).
    unfold sf. rewrite GET.
    inv INTERP. exists n. rewrite H0. exists a, t. split; auto. split; auto.
    eapply interp_sact_eval_sact; eauto.
    generalize (inlining_pass_correct _ _ eq_refl VSV WTV).
    intros (ND2 & INLINING).
    exploit INLINING. apply GET. econstructor; eauto.
    intro IN. apply in_list_assoc in IN.
    (* rewrite IN. *)
    (* auto. auto. *)
  Admitted.


End SimpleFormInterpretation.
