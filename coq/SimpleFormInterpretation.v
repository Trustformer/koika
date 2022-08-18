Require Import Coq.Strings.Ascii.
Require Import Koika.Environments Koika.SimpleForm Koika.TypeInference
  Koika.UntypedSemantics Koika.DesugaredSyntax.
Require Import Koika.BitsToLists.
From RecordUpdate Require Import RecordSet.
Import RecordSetNotations.
Require Import Sact.
Require Import Coq.Sorting.Sorted.
Require Import Coq.Sorting.Mergesort.
Require Import Maps.
Require Import SimpleVal.

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

  Context (R: reg_t -> type).
  Context (Sigma: ext_fn_t -> ExternalSignature).

  Definition uact := @daction pos_t string string reg_t ext_fn_t.
  Definition schedule := scheduler pos_t rule_name_t.
  Definition ext_funs_defs :=
    forall f: ext_fn_t, val -> val.
  Definition UREnv := REnv.(env_t) (fun _ => val).

  Context (r: UREnv).
  Context (sigma: ext_funs_defs).

  Definition sact := sact (ext_fn_t:=ext_fn_t) (reg_t:=reg_t).

  Fixpoint vars_in_sact (s: sact) : list positive :=
    match s with
    | SConst _ => []
    | SReg _ => []
    | SVar v => [v]
    | SExternalCall _ a
    | SUnop _ a => vars_in_sact a
    | SBinop _ a1 a2 => vars_in_sact a1 ++ vars_in_sact a2
    | SIf c t f => vars_in_sact c ++ vars_in_sact t ++ vars_in_sact f
    end.

  Fixpoint reachable_vars_aux
    (vvs: var_value_map) (n: positive) (visited: list positive) fuel
  :=
    match fuel with
    | O => visited
    | S fuel =>
        if in_dec Pos.eq_dec n visited then visited
        else
          n::
            match vvs ! n with
            | None => visited
            | Some (_, s) =>
              fold_left
                (fun visited n => reachable_vars_aux vvs n visited fuel)
                (vars_in_sact s) visited
            end
    end.

  Inductive reachable_var (vvs: var_value_map) : sact -> positive -> Prop :=
  | reachable_var_var: forall n, reachable_var vvs (SVar n) n
  | reachable_var_in_var:
    forall n x t a, vvs ! x = Some (t, a)
    -> reachable_var vvs a n
    -> reachable_var vvs (SVar x) n
  | reachable_var_if_cond:
    forall n c t f, reachable_var vvs c n -> reachable_var vvs (SIf c t f) n
  | reachable_var_if_true:
    forall n c t f, reachable_var vvs t n -> reachable_var vvs (SIf c t f) n
  | reachable_var_if_false:
    forall n c t f, reachable_var vvs f n -> reachable_var vvs (SIf c t f) n
  | reachable_var_binop1:
    forall n c a1 a2,
    reachable_var vvs a1 n -> reachable_var vvs (SBinop c a1 a2) n
  | reachable_var_binop2:
    forall n c a1 a2,
    reachable_var vvs a2 n -> reachable_var vvs (SBinop c a1 a2) n
  | reachable_var_unop:
    forall n c a1, reachable_var vvs a1 n -> reachable_var vvs (SUnop c a1) n
  | reachable_var_externalCall:
    forall n c a1,
    reachable_var vvs a1 n -> reachable_var vvs (SExternalCall c a1) n.

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
    forall vvs (VSV: vvs_smaller_variables vvs) a n
      (GET: forall v, var_in_sact a v -> (v < n)%positive) v
      (RV: reachable_var vvs a v),
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
      simpl. intros v0 VIS. eapply BELOW.
      eapply var_in_if_cond; eauto. simpl; auto.
    - eapply (IH (existT _ x t)). constructor 2. simpl; lia.
      simpl. intros v0 VIS. eapply BELOW.
      eapply var_in_if_true; eauto. simpl; auto.
    - eapply (IH (existT _ x f)). constructor 2. simpl; lia.
      simpl. intros v0 VIS. eapply BELOW.
      eapply var_in_if_false; eauto. simpl; auto.
    - eapply (IH (existT _ x a1)). constructor 2. simpl; lia.
      simpl. intros v0 VIS. eapply BELOW.
      eapply var_in_sact_binop_1; eauto. simpl; auto.
    - eapply (IH (existT _ x a2)). constructor 2. simpl; lia.
      simpl. intros v0 VIS. eapply BELOW.
      eapply var_in_sact_binop_2; eauto. simpl; auto.
    - eapply (IH (existT _ x a1)). constructor 2. simpl; lia.
      simpl. intros v0 VIS. eapply BELOW.
      eapply var_in_sact_unop; eauto. simpl; auto.
    - eapply (IH (existT _ x a1)). constructor 2. simpl; lia.
      simpl. intros v0 VIS. eapply BELOW.
      eapply var_in_sact_external; eauto. simpl; auto.
  Qed.

  Lemma reachable_var_aux_below_get:
    forall vvs (VSV: vvs_smaller_variables vvs) a n t
      (GET: vvs ! n = Some (t,a)) v (RV: reachable_var vvs a v),
    (v < n)%positive.
  Proof.
    intros; eapply reachable_var_aux_below; eauto.
    eapply VSV. eauto.
  Qed.

  Lemma reachable_inv:
    forall vvs a v, reachable_var vvs a v
    -> exists v',
     var_in_sact a v'
     /\ (
       v = v'
       \/ exists t' a', vvs ! v' = Some (t', a') /\ reachable_var vvs a' v
     ).
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

  Lemma var_in_sact_ok: forall a v, var_in_sact a v -> In v (vars_in_sact a).
  Proof.
    induction 1; simpl; intros; eauto.
    rewrite ! in_app_iff; now eauto.
    rewrite ! in_app_iff; now eauto.
    rewrite ! in_app_iff; now eauto.
    rewrite ! in_app_iff; now eauto.
    rewrite ! in_app_iff; now eauto.
  Qed.

  Lemma var_in_sact_ok_inv:
    forall a v, In v (vars_in_sact a) -> var_in_sact a v.
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

  Lemma rev_sym: forall {A: Type} (l1 l2: list A), l1 = rev l2 <-> rev l1 = l2.
  Proof.
    split; intro.
    - rewrite H. rewrite rev_involutive. easy.
    - rewrite <- H. rewrite rev_involutive. easy.
  Qed.

  Lemma app_inv_last:
    forall {A: Type} (l1 l2: list A) (x y: A),
    l1 ++ [x] = l2 ++ [y] -> x = y.
  Proof.
    intros.
    apply (f_equal (@rev A)) in H.
    rewrite rev_app_distr in H. rewrite rev_app_distr in H at 1.
    simpl in H. inv H.
    easy.
  Qed.

  Lemma fold_left_prop_eventually_no_tail:
    forall {A B: Type} (P: B -> Prop) (f: B -> A -> B) (lb: list A) (s: B) x,
    (forall e, P (f e x)) -> P (fold_left f (lb ++ [x]) s).
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
    forall vvs fuel visited n,
    (fuel > 0)%nat -> In n (reachable_vars_aux vvs n visited fuel).
  Proof.
    destruct fuel. lia. intros. simpl. destr. destr. destr.
    left; auto. left; auto.
  Qed.

  Lemma fold_left_ev:
    forall {A B: Type} (P: A -> Prop) (I: A -> Prop) (f: A -> B -> A)
      l (INV: forall acc y, In y l -> I acc -> I (f acc y))
      (PRESERVES: forall acc y, In y l -> I acc -> P acc -> P (f acc y)) acc,
    I acc
    -> (P acc \/ exists x, In x l /\ forall acc, I acc -> P (f acc x))
    -> P (fold_left f l acc).
  Proof.
    induction l; simpl; intros; eauto. destruct H0 as [|(? & [] & ?)]. auto.
    destruct H0 as [Pacc|(x & EQIN & Pf)].
    apply IHl. eauto. eauto. eauto. left; apply PRESERVES; auto.
    apply IHl. eauto. eauto. eauto. destruct EQIN. subst; left; auto.
    right; eauto.
  Qed.

  Lemma reachable_vars_aux_inv:
    forall vvs (VSV: vvs_smaller_variables vvs) fuel n visited l,
    reachable_vars_aux vvs n visited fuel = l
    -> forall v, In v l
    -> In v visited
    \/ v = n
    \/ exists t a, vvs !n = Some (t, a) /\ reachable_var vvs a v.
  Proof.
    induction fuel; simpl; intros; eauto.
    subst. auto.
    subst. destr_in H0. auto.
    destruct H0 as [EQ|IN]. auto.
    destr_in IN; auto. destr_in IN.
    destruct (in_dec Pos.eq_dec v visited); auto.
    right.
    cut (
      exists vv, In vv (vars_in_sact s)
      /\ exists vis, ~In v vis /\ In v (reachable_vars_aux vvs vv vis fuel)).
    intros (vv & IN' & vis & INCL & INv).
    edestruct (IHfuel _ _ _ eq_refl _ INv) as [Invis | [EQ | PROP]].
    congruence. subst.
    Lemma reachable_vars_in_sact:
      forall vvs vv s, In vv (vars_in_sact s) -> reachable_var vvs s vv.
    Proof.
      intros. apply var_in_sact_ok_inv in H.
      revert vv s H.
      induction 1; simpl; intros; eauto.
      constructor.
      eapply reachable_var_if_cond; eauto.
      eapply reachable_var_if_true; eauto.
      eapply reachable_var_if_false; eauto.
      eapply reachable_var_unop; eauto.
      eapply reachable_var_binop1; eauto.
      eapply reachable_var_binop2; eauto.
      eapply reachable_var_externalCall; eauto.
    Qed.
    right; do 2 eexists; split; eauto using reachable_vars_in_sact.
    destruct PROP as (?t & ?a & GET & RV).
    right. do 2 eexists; split; eauto.

    Lemma reachable_vars_in_sact2:
      forall vvs vv s, var_in_sact s vv
      -> forall t a, vvs ! vv = Some (t, a)
      -> forall v2, reachable_var vvs a v2
      -> reachable_var vvs s v2.
    Proof.
      induction 1; simpl; intros; eauto.
      econstructor; eauto.
      eapply reachable_var_if_cond; eauto.
      eapply reachable_var_if_true; eauto.
      eapply reachable_var_if_false; eauto.
      eapply reachable_var_unop; eauto.
      eapply reachable_var_binop1; eauto.
      eapply reachable_var_binop2; eauto.
      eapply reachable_var_externalCall; eauto.
    Qed.
    eapply reachable_vars_in_sact2; eauto.
    apply var_in_sact_ok_inv; auto.
    Lemma fold_left_prop_inv:
      forall {A B: Type} (f: A -> B -> A) (P: A -> Prop)
        (PRES: forall acc x, P acc -> P (f acc x))
        (Pdec: forall acc, {P acc} + {~ P acc}) (l: list B) acc,
      P (fold_left f l acc)
      -> ~ P acc
      -> exists x acc, In x l /\ ~ P acc /\ P (f acc x).
    Proof.
      induction l; simpl; intros; eauto. congruence.
      destruct (Pdec (f acc a)).
      exists a, acc; split; eauto.
      apply IHl in H; auto.
      destruct H as (x & ?acc & IN & NP & PF).
      exists x, acc0; split; eauto.
    Qed.
    edestruct @fold_left_prop_inv as (x & acc & INN & NP & PACC). 3: apply IN.
    simpl; intros. eapply reachable_vars_aux_incr; eauto.
    apply in_dec. apply Pos.eq_dec.
    auto.
    exists x; split; auto. simpl in PACC. eauto.
  Qed.

  Lemma reachable_vars_aux_nd:
    forall vvs (VSV: vvs_smaller_variables vvs) fuel n visited l,
    reachable_vars_aux vvs n visited fuel = l
    -> forall (ND: NoDup visited), NoDup l.
  Proof.
    induction fuel; simpl; intros; eauto. subst; auto.
    destr_in H.
    subst. auto. subst.
    constructor.
    - destr. destr.
      intro IN.
      edestruct @fold_left_prop_inv as (x & acc & INN & NP & PACC). 3: apply IN.
      simpl; intros. eapply reachable_vars_aux_incr; eauto.
      apply in_dec. apply Pos.eq_dec.
      auto. simpl in PACC.
      edestruct reachable_vars_aux_inv as [INv | [EQv | PROP]]. eauto. eauto.
      apply PACC.
      congruence.
      subst.
      exploit VSV. apply Heqo. apply var_in_sact_ok_inv. apply INN.
      unfold var_lt. lia.
      destruct PROP as (? & ? & GET & REACH).
      eapply reachable_var_aux_below in REACH. 3: eapply VSV; eauto.
      exploit VSV. apply Heqo. apply var_in_sact_ok_inv. apply INN.
      unfold var_lt. lia.
      auto.
    - repeat destr.
      eapply fold_left_induction. auto. intros. eapply IHfuel; eauto.
  Qed.

  Lemma reachable_vars_aux_ok:
    forall vvs (VSV: vvs_smaller_variables vvs) fuel n visited l,
    reachable_vars_aux vvs n visited fuel = l
    -> (forall n, In n visited
        -> forall v t a, vvs ! n = Some (t, a)
        -> reachable_var vvs a v
        -> In v visited)
    -> ((Pos.to_nat n<fuel)%nat)
    -> forall n1 (IN: In n1 l) v t a, vvs ! n1 = Some (t, a)
    -> reachable_var vvs a v
    -> In v l.
  Proof.
    induction fuel; simpl; intros; eauto. lia.
    destr_in H. subst. eauto.
    subst.
    destruct IN as [EQ|IN].
      + subst. rewrite H2.
        right.
        cut (
          exists vv, In vv (vars_in_sact a)
          /\ forall vis,
             (forall n : positive, In n vis
              -> forall (v0 : positive) (t0 : type) (a0 : SimpleForm.sact),
              vvs ! n = Some (t0, a0)
              -> reachable_var vvs a0 v0
              -> In v0 vis)
              -> In v (reachable_vars_aux vvs vv vis fuel)).
        intros (vv & IN & REACH).
        eapply fold_left_ev with (
          I := fun vis =>
            forall n : positive, In n vis
            -> forall (v0 : positive) (t0 : type) (a0 : SimpleForm.sact),
            vvs ! n = Some (t0, a0)
            -> reachable_var vvs a0 v0
            -> In v0 vis).
        {
          intros.
          eapply IHfuel. eauto. eauto.
          exploit VSV. apply H2. apply var_in_sact_ok_inv. apply H.
          unfold var_lt. lia. apply H5.
          eauto. eauto.
        }
        { intros. eapply reachable_vars_aux_incr; eauto. }
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
        exploit VSV. apply H2. apply var_in_sact_ok_inv. apply VIS.
        unfold var_lt. lia.
        2: apply GET. eapply reachable_vars_aux_in. lia. auto.
      + destruct (vvs ! n) eqn:?.
        2: { right; eapply H0; eauto. }
        destruct p.
        right.
        revert n1 IN v t a H2 H3.
        pattern (
          fold_left
            (fun (visited0 : list positive) (n2 : positive) =>
              reachable_vars_aux vvs n2 visited0 fuel)
            (vars_in_sact s) visited).
        eapply fold_left_induction. eauto.
        intros. eapply IHfuel; eauto.
        exploit VSV. apply Heqo.
        apply var_in_sact_ok_inv. apply H. unfold var_lt. lia.
  Qed.

  Definition useful_vars (sf: simple_form (reg_t:=reg_t) (ext_fn_t:=ext_fn_t))
  : list positive :=
    let todo := map snd (final_values sf) in
    fold_left
      (fun visited n =>
        reachable_vars_aux (vars sf) n visited (S (Pos.to_nat n)))
      todo [].

  Lemma useful_vars_ok:
    forall sf (VSV: vvs_smaller_variables (vars sf)) l, useful_vars sf = l
    -> forall n1 (IN: In n1 l) v t a, (vars sf) ! n1 = Some (t, a)
    -> reachable_var (vars sf) a v
    -> In v l.
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
    forall sf (VSV: vvs_smaller_variables (vars sf)) l, useful_vars sf = l
    -> incl (map snd (final_values sf)) l.
  Proof.
    intros sf VSV l <-.
    unfold useful_vars. generalize (map snd (final_values sf)).

    Lemma fold_left_prop:
      forall {A B: Type} (P: A -> Prop) (f: A -> B -> A) (l: list B) x acc,
        In x l
        -> (forall a, P (f a x))
        -> (forall a x, P a -> P (f a x))
        -> P (fold_left f l acc).
    Proof.
      intros; eapply fold_left_ev with (I:= fun _ => True). auto. auto. auto. right; eexists; split; eauto.
    Qed.
    red; intros. eapply fold_left_prop. eauto.
    intros; eapply reachable_vars_aux_in; eauto. lia.
    intros; eapply reachable_vars_aux_incr; eauto.
  Qed.

  Theorem useful_vars_good:
    forall sf (VSV: vvs_smaller_variables (vars sf)) n1,
      In n1 (map snd (final_values sf))
      -> forall v t a,
        (vars sf) ! n1 = Some (t, a)
        -> reachable_var (vars sf) a v
        -> In v (useful_vars sf).
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
        | Bits [b] => if b then eval_sact vars t fuel else eval_sact vars f fuel
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
      | SReg idx => Some (getenv REnv r idx)
      end
    end.

  Lemma eval_remove_var:
    forall vvs fuel a n, ~ reachable_var vvs a n
    -> eval_sact vvs a fuel = eval_sact (PTree.remove n vvs) a fuel.
  Proof.
    induction fuel; simpl; intros; eauto.
    destruct a; simpl; intros; eauto.
    - rewrite PTree.gro. unfold opt_bind; repeat destr. apply IHfuel.
      intro REACH.
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
    forall a vvs a0 a1 (RR : reachable_var (PTree.remove a0 vvs) a a1),
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
    forall fuel a l vvs, Forall (fun n => ~ reachable_var vvs a n) l
    ->
      eval_sact vvs a fuel
      = eval_sact (fold_left (fun t n => PTree.remove n t) l vvs) a fuel.
  Proof.
    induction l; simpl; intros; eauto. inv H.
    rewrite <- IHl. eapply eval_remove_var. eauto.
    eapply Forall_impl; eauto. simpl.
    intros a1 NR RR; apply NR; clear NR.
    eapply reachable_remove; eauto.
  Qed.

  Definition remove_vars (sf: simple_form) : simple_form := {|
      final_values := final_values sf;
      vars :=
        fold_left
          (fun t n =>
            match (vars sf) ! n with
            | Some v => PTree.set n v t
            | _ => t
            end)
          (useful_vars sf)
          (PTree.empty _); |}.

  Definition filter_ptree
    (vvs t2: var_value_map (ext_fn_t:=ext_fn_t) (reg_t:=reg_t))
    (l: list positive)
  :=
    (fold_left
      (fun t n =>
        match vvs ! n with
        | Some v => PTree.set n v t
        | _ => t
        end)
      l t2).

  Lemma nodup_reachable_vars_aux:
    forall vvs (VSV:   vvs_smaller_variables vvs) fuel x acc,
      NoDup acc
      -> NoDup (reachable_vars_aux vvs x acc fuel).
  Proof.
    intros.
    eapply reachable_vars_aux_nd; eauto.
  Qed.

  Lemma nodup_useful_vars sf:
    vvs_smaller_variables (vars sf)
    -> NoDup(useful_vars sf).
  Proof.
    intros. unfold useful_vars.
    apply fold_left_induction. constructor.
    intros.
    eapply nodup_reachable_vars_aux; eauto.
  Qed.

Lemma remove_vars_correct:
    forall sf (VSV:   vvs_smaller_variables (vars sf)) n,
      In n (map snd (final_values sf))
      -> forall fuel,
        eval_sact (vars sf) (SVar n) fuel = eval_sact (vars (remove_vars sf)) (SVar n) fuel.
  Proof.
    intros. simpl.
    assert (forall v, reachable_var (vars sf) (SVar n) v -> In v (useful_vars sf)).
    {
      intros v RV. inv RV.
      eapply useful_vars_incl; eauto.
      intros; eapply useful_vars_good; eauto.
    }
    assert (
      forall l v (vvs t2: var_value_map (ext_fn_t:=ext_fn_t) (reg_t:=reg_t)),
      In v l
      -> NoDup l
      -> (forall x, In x l -> t2 ! x = None)
      -> vvs ! v = (filter_ptree vvs t2 l) ! v
    ).
    {
      clear.
      induction l; simpl; intros. easy.
      inv H0. destruct H. subst.
      destr.
      Lemma filter_ptree_in:
        forall l vvs t2 v (NI: ~ In v l),
          (filter_ptree vvs t2 l) ! v = t2 ! v.
      Proof.
        induction l; simpl; intros; eauto.
        rewrite IHl. destr. rewrite PTree.gso. auto. intuition congruence. intuition.
      Qed.
      rewrite filter_ptree_in. rewrite PTree.gss. auto. auto.
      rewrite filter_ptree_in; auto. symmetry; apply H1. auto.
      rewrite <- IHl. auto. auto. auto. intros.
      destr; eauto. rewrite PTree.gso; eauto. congruence.
    }

    specialize (fun v REACH vvs t2 => H1 _ _ vvs t2 (H0 v REACH) (nodup_useful_vars _ VSV)).
    fold (filter_ptree (vars sf) (PTree.empty _) (useful_vars sf)).

    Lemma eval_sact_reachable:
      forall v1 v2 fuel a
             (SAME: forall v, reachable_var v1 a v -> v1 ! v = v2 ! v),
        eval_sact v1 a fuel = eval_sact v2 a fuel.
    Proof.
      induction fuel; simpl; intros; eauto.
      destruct a; simpl in *; eauto.
      - rewrite <- SAME. unfold opt_bind; repeat destr; eauto.
        eapply IHfuel. intros; apply SAME. econstructor; eauto. constructor.
      - rewrite <- ! IHfuel. auto.
        intros v RV; apply SAME. eapply reachable_var_if_false; eauto.
        intros v RV; apply SAME. eapply reachable_var_if_true; eauto.
        intros v RV; apply SAME. eapply reachable_var_if_cond; eauto.
      - rewrite <- ! IHfuel. auto.
        intros v RV; apply SAME. eapply reachable_var_unop; eauto.
      - rewrite <- ! IHfuel. auto.
        intros v RV; apply SAME. eapply reachable_var_binop2; eauto.
        intros v RV; apply SAME. eapply reachable_var_binop1; eauto.
      - rewrite <- ! IHfuel. auto.
        intros v RV; apply SAME. eapply reachable_var_externalCall; eauto.
    Qed.
    apply eval_sact_reachable. intros; apply H1. auto. intros; apply PTree.gempty.
  Qed.

  Lemma eval_no_var:
    forall vvs vvs' fuel a,
      (forall n, ~ reachable_var vvs a n)
      -> eval_sact vvs a fuel = eval_sact vvs' a fuel.
  Proof.
    induction fuel; simpl; intros; eauto.
    destruct a; simpl; intros; eauto.
    - elim (H var). constructor.
    - rewrite <- ! IHfuel. eauto.
      intros n REACH; eapply H. apply reachable_var_if_false; eauto.
      intros n REACH; eapply H. apply reachable_var_if_true; eauto.
      intros n REACH; eapply H. apply reachable_var_if_cond; eauto.
    - rewrite <- ! IHfuel. eauto.
      intros n REACH; eapply H. apply reachable_var_unop; eauto.
    - rewrite <- ! IHfuel. eauto.
      intros n REACH; eapply H. apply reachable_var_binop2; eauto.
      intros n REACH; eapply H. apply reachable_var_binop1; eauto.
    - rewrite <- ! IHfuel. eauto.
      intros n REACH; eapply H. apply reachable_var_externalCall; eauto.
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
    | SReg _ => false
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
    | SReg r => SReg r
    end.

  Fixpoint replace_reg_in_sact (ua: sact) (from: reg_t) (to: val)
  : sact :=
    match ua with
    | SBinop ufn a1 a2 =>
      SBinop
        ufn (replace_reg_in_sact a1 from to)
        (replace_reg_in_sact a2 from to)
    | SUnop ufn a1 => SUnop ufn (replace_reg_in_sact a1 from to)
    | SVar v => SVar v
    | SIf cond tb fb =>
      SIf
        (replace_reg_in_sact cond from to)
        (replace_reg_in_sact tb from to)
        (replace_reg_in_sact fb from to)
    | SConst c => SConst c
    | SExternalCall ufn a => SExternalCall ufn (replace_reg_in_sact a from to)
    | SReg r => if eq_dec r from then SConst to else SReg r
    end.

  Definition replace_all_occurrences_in_vars
    (vars: var_value_map) (from: positive) (to: val)
  : var_value_map :=
    PTree.map
      (fun _ '(t, ua) => (t, replace_all_occurrences_in_sact ua from to))
      vars.

  Definition replace_reg_in_vars
    (vars: var_value_map) (from: reg_t) (to: val)
  : var_value_map :=
    PTree.map
      (fun _ '(t, ua) => (t, replace_reg_in_sact ua from to))
      vars.

  Fixpoint exploit_partial_bitwise_information_in_var
    (ua: sact) (reg: reg_t) (first_known_bit: nat) (known_bits: list bool)
  : sact :=
    match ua with
    | SBinop ufn a1 a2 =>
      let a1' :=
        exploit_partial_bitwise_information_in_var
          a1 reg first_known_bit known_bits
      in
      let a2' :=
        exploit_partial_bitwise_information_in_var
          a2 reg first_known_bit known_bits
      in
      let ua' := SBinop ufn a1' a2' in
      match ufn with
      | PrimUntyped.UBits2 (PrimUntyped.USliceSubst offset width) =>
        match a1' with
        | SReg r =>
          match a2' with
          | SConst c =>
            match c with
            | Bits bs => ua' (* TODO *)
            | _ => ua'
            end
          | _ => ua'
          end
        | _ => ua'
        end
      | PrimUntyped.UBits2 (PrimUntyped.UIndexedSlice width) =>
        match a1', a2' with
        | SReg x, SConst (Bits bs) =>
            if eq_dec x reg then
              match (R x) with
              | bits_t sz =>
                  let offset := Bits.to_nat (vect_of_list bs) in
                  if (
                      (first_known_bit <=? offset)
                      && (offset + width <=? first_known_bit + (List.length known_bits))
                      && (offset + width <=? sz) (* TODO remove? Still simplifiable. *)
                    )
                       (* TODO rely on take_drop'? *)
                  then
                    SConst (Bits (
                      List.firstn
                        width
                        (List.skipn (offset - first_known_bit) known_bits)
                      ))
                  else ua'
              | _ => ua'
              end
            else ua'
        | _, _ => ua'
        end
      | _ => ua'
      end
    | SUnop ufn a1 =>
      let a1' :=
        exploit_partial_bitwise_information_in_var
          a1 reg first_known_bit known_bits
      in
      let ua' := SUnop ufn a1' in
      match ufn, a1' with
      (* TODO what about SVar? *)
      | PrimUntyped.UBits1 (PrimUntyped.USlice offset width), SReg x =>
        if (eq_dec reg x) then
          match (R x) with
          | bits_t sz =>
            if (
              (first_known_bit <=? offset)
              && (offset + width <=? first_known_bit + (List.length known_bits))
              && (offset + width <=? sz) (* TODO remove? Still simplifiable. *)
            )
            then
              SConst (Bits (
                List.firstn
                  width (List.skipn (offset - first_known_bit) known_bits)
              ))
            else ua'
          | _ => ua'
          end
        else ua'
      | _, _ => ua'
      end
    | SIf cond tb fb =>
      SIf
        (exploit_partial_bitwise_information_in_var cond reg first_known_bit
         known_bits)
        (exploit_partial_bitwise_information_in_var tb reg first_known_bit
         known_bits)
        (exploit_partial_bitwise_information_in_var fb reg first_known_bit
         known_bits)
    | SExternalCall ufn a =>
      SExternalCall
        ufn
        (exploit_partial_bitwise_information_in_var a reg first_known_bit
         known_bits)
    | SConst c => SConst c
    | SVar v => SVar v
    | SReg r => SReg r
    end.

  Definition exploit_partial_bitwise_information_in_vars
    (vars: var_value_map) (reg: reg_t) (first_known_bit: nat)
    (known_bits: list bool)
  : var_value_map :=
    PTree.map
      (fun _ '(t, ua) => (
        t,
        exploit_partial_bitwise_information_in_var
          ua reg first_known_bit known_bits
      ))
      vars.

  Definition exploit_partial_bitwise_information
    (sf: simple_form) (reg: reg_t) (first_known_bit: nat)
    (known_bits: list bool)
  : simple_form := {|
    final_values := final_values sf;
    vars :=
      exploit_partial_bitwise_information_in_vars
        (vars sf) reg first_known_bit known_bits
  |}.

  (* TODO simplify as well: initial simpl pass then whenever change *)
  Definition replace_all_occurrences (sf: simple_form) (from: positive) (to: val)
  : simple_form := {|
    final_values := final_values sf;
    vars := replace_all_occurrences_in_vars (vars sf) from to |}.

  Definition replace_reg (sf: simple_form) (from: reg_t) (to: val)
  : simple_form := {|
    final_values := final_values sf;
    vars := replace_reg_in_vars (vars sf) from to; |}.

  (* TODO use coq record update here as well *)
  (* TODO variable in environment instead of inlining *)

  Definition max_var (vars: var_value_map (reg_t:=reg_t) (ext_fn_t:=ext_fn_t))
  :=
    PTree.fold (fun acc k _ => Pos.max acc k) vars xH.

  Lemma vvs_range_max_var:
    forall vars, vvs_range vars (Pos.succ (max_var vars)).
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
      eval_sact vvs a n1 = Some v
      -> n1 <= n2
      -> eval_sact vvs a n2 = Some v.
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

  Definition vvs_size
    (vvs:var_value_map (reg_t:=reg_t) (ext_fn_t:=ext_fn_t)) m
  : nat :=
    PTree.fold (
      fun acc k '(t,a) =>
        if Pos.ltb k m
        then size_sact (ext_fn_t := ext_fn_t) a + acc
        else acc
    ) vvs O.

  Lemma vvs_size1_aux:
    forall var n (LT: (var < n)%positive),
    forall (l : list (positive * (type * SimpleForm.sact))) (n0 n1 : nat),
      n1 <= n0
      -> fold_left
        (fun (a : nat) (p : positive * (type * SimpleForm.sact)) =>
           let
             '(_, a0) := snd p in
           if (fst p <? var)%positive then size_sact a0 + a else a) l n1 <=
        fold_left
          (fun (a : nat) (p : positive * (type * SimpleForm.sact)) =>
             let
               '(_, a0) := snd p in
             if (fst p <? n)%positive then size_sact (reg_t:=reg_t) (ext_fn_t:=ext_fn_t) a0 + a else a) l n0.
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
      (var < n)%positive
      -> vvs_size vvs var  <= vvs_size vvs n.
  Proof.
    unfold vvs_size. intros.
    rewrite ! PTree.fold_spec.
    assert (O <= O)%nat. lia.
    revert H0. generalize O at 1 3.
    generalize O.
    generalize (PTree.elements vvs).
    eapply vvs_size1_aux; eauto.
  Qed.

  Lemma vvs_size_rew:
    forall l m n,
    fold_left
    (fun (a0 : nat) (p : positive * (type * SimpleForm.sact)) =>
     let
     '(_, a1) := snd p in
      if (fst p <? n)%positive then size_sact a1 + a0 else a0)
    l m =
  fold_left
    (fun (a0 : nat) (p : positive * (type * SimpleForm.sact (ext_fn_t:=ext_fn_t)(reg_t:=reg_t))) =>
     let
     '(_, a1) := snd p in
      if (fst p <? n)%positive then size_sact a1 + a0 else a0)
    l 0 + m.
  Proof.
    induction l; simpl; intros; eauto.
    rewrite IHl. destruct a. simpl. destruct p0. simpl.
    rewrite (IHl (if (p <? n)%positive then _ else _)). rewrite <- Nat.add_assoc. f_equal.
    destr; lia.
  Qed.

  Lemma vvs_size_le2:
    forall vvs a var t n,
      (var < n)%positive
      -> vvs ! var = Some (t, a)
      -> vvs_size vvs var + size_sact a <= vvs_size vvs n.
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
    rewrite (vvs_size_rew _ (if (_ <? _)%positive then _ else _)).
    rewrite (vvs_size_rew _ (if (_ <? _)%positive then _ else _)).
    generalize (Pos.ltb_spec var var). intro A; inv A. lia.
    generalize (Pos.ltb_spec var n). intro A; inv A. 2: lia.
    generalize (vvs_size1_aux _ _ H4 l _ _ H1).
    rewrite (Nat.add_comm _ n0); rewrite Nat.add_assoc.
    rewrite <- ! vvs_size_rew. lia.
    eapply IHl; eauto.
    generalize (Pos.ltb_spec (fst a0) var).
    generalize (Pos.ltb_spec (fst a0) n).
    intros A B. inv A; inv B; lia.
  Qed.

  Lemma interp_sact_eval_sact_aux:
    forall (vvs: var_value_map) (VSV: vvs_smaller_variables vvs) a v,
    interp_sact (sigma := sigma) REnv r vvs a v
    -> forall n, (forall var, var_in_sact a var -> var < n)%positive
    -> exists m,
       eval_sact vvs a (m + size_sact a) = Some v
       /\ (m <= Pos.to_nat n + vvs_size vvs n)%nat.
  Proof.
    induction 2; simpl; intros; eauto.
    - destruct (IHinterp_sact var) as (m1 & I1 & LE1).
      intros; eapply VSV. eauto. auto.
      eexists. split. rewrite Nat.add_1_r. simpl. rewrite H; simpl; eauto.
      assert (var < n)%positive. eapply H1. constructor.
      generalize (vvs_size_le2 vvs _ _ _ n H2 H). lia.
    - exists 0; split; simpl; eauto.  lia.
    - edestruct IHinterp_sact1 as (m1 & I1 & LE1).
      intros; eapply H1. apply var_in_if_cond; eauto.
      edestruct IHinterp_sact2 as (m2 & I2 & LE2).
      intros; eapply H1. destruct b.
      apply var_in_if_true; eauto. apply var_in_if_false; eauto.
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
    - exists O; split; simpl; eauto.  lia.
  Qed.

  Lemma interp_sact_eval_sact:
    forall (vvs: var_value_map) (VSV: vvs_smaller_variables vvs),
    forall a v t,
      wt_sact (Sigma:=Sigma) R vvs a t
      -> interp_sact (sigma:=sigma) REnv r vvs a v
      -> eval_sact vvs a (Pos.to_nat (Pos.succ (max_var vvs)) + vvs_size vvs ((Pos.succ (max_var vvs))) + size_sact a) = Some v.
  Proof.
    intros.
    generalize (vvs_range_max_var vvs). intro VR.
    generalize (wt_sact_valid_vars _ vvs _ VR _ _ H). intro VALID.
    generalize (interp_sact_eval_sact_aux _ VSV a v H0 _ VALID).
    intros (m & EVAL & LE).
    eapply eval_sact_more_fuel. eauto. lia.
  Qed.

  Definition do_eval_sact vvs a :=
    eval_sact
      vvs a
      (Pos.to_nat
        (Pos.succ (max_var vvs))
        + vvs_size vvs ((Pos.succ (max_var vvs)))
        + size_sact a).

  Lemma interp_sact_do_eval_sact:
    forall (vvs: var_value_map) (VSV: vvs_smaller_variables vvs) a v t,
    wt_sact (Sigma:=Sigma) R vvs a t
    -> interp_sact (sigma:=sigma) REnv r vvs a v
    -> do_eval_sact vvs a = Some v.
  Proof. intros. eapply interp_sact_eval_sact; eauto. Qed.

  Lemma eval_sact_interp_sact:
    forall vvs fuel a v, eval_sact vvs a fuel = Some v
    -> interp_sact (sigma:=sigma) REnv r vvs a v.
  Proof.
    induction fuel; simpl; intros; eauto. easy.
    unfold opt_bind in H; repeat destr_in H; inv H; econstructor; eauto.
  Qed.

  Lemma do_eval_sact_interp_sact:
    forall vvs a v, do_eval_sact vvs a = Some v
    -> interp_sact (sigma:=sigma) REnv r vvs a v.
  Proof. intros; eapply eval_sact_interp_sact; eauto. Qed.

  Scheme Equality for list.

  Definition val_beq_bits (v1 v2: val) : bool :=
    match v1, v2 with
    | Bits b1, Bits b2 => list_beq bool Bool.eqb b1 b2
    | _, _ => false
    end.

  Lemma val_beq_bits_implies_eq :
    forall v1 v2, val_beq_bits v1 v2 = true -> v1 = v2.
  Proof.
    intros.
    induction v1; induction v2; inv H.
    assert (v = v0).
    {
      generalize dependent v0.
      induction v; intros.
      - inv H1. destruct v0; eauto. discriminate.
      - destruct v0.
        + simpl in H1. discriminate.
        + simpl in H1. eapply andb_true_iff in H1. destruct H1.
          eapply Bool.eqb_prop in H. eapply IHv in H0. subst. reflexivity.
    }
    subst. reflexivity.
  Qed.

  Fixpoint eval_sact_no_vars (a: sact) : option val :=
    match a with
    | SConst v => Some v
    | SReg idx => Some (getenv REnv r idx)
    | SVar v => None
    | SIf c t f =>
      let/opt v := eval_sact_no_vars c in
      match v with
      | Bits [b] => if b then eval_sact_no_vars t else eval_sact_no_vars f
      | _ => None
      end
    | SUnop ufn a =>
      let/opt v := eval_sact_no_vars a in
      sigma1 ufn v
    | SBinop ufn a1 a2 =>
      let/opt v1 := eval_sact_no_vars a1 in
      let/opt v2 := eval_sact_no_vars a2 in
      match ufn with
      | PrimUntyped.UEq false =>
        if (val_beq_bits v1 v2) then Some (Bits [true]) else sigma2 ufn v1 v2
      | PrimUntyped.UEq true =>
        if (val_beq_bits v1 v2) then Some (Bits [false]) else sigma2 ufn v1 v2
      | _ => sigma2 ufn v1 v2
      end
    | SExternalCall ufn a =>
      let/opt v := eval_sact_no_vars a in
      Some (sigma ufn v)
    end.

  Lemma list_assoc_filter:
    forall {K V: Type} {eqdec: EqDec K} (l: list (K*V)) f k,
    (forall v, f (k,v) = true)
    -> list_assoc l k = list_assoc (filter f l) k.
  Proof.
    induction l; simpl; intros; eauto.
    repeat destr.
    - subst. simpl. rewrite eq_dec_refl. reflexivity.
    - subst. simpl. destr. eauto.
    - eauto.
  Qed.

  Lemma list_assoc_map:
    forall
      {K V: Type} {eqdec: EqDec K} (f: K*V -> K*V) (g: V -> V)
      (F: forall k1 v1, f (k1,v1) = (k1, g v1)) l k,
    list_assoc (map f l) k = option_map g (list_assoc l k).
  Proof.
    induction l; simpl; intros; eauto.
    destruct a. rewrite F. destr. subst. simpl. reflexivity.
  Qed.

  Lemma interp_sact_replace:
    forall vvs var v', interp_sact (sigma:=sigma) REnv r vvs (SVar var) v'
    -> forall a res, interp_sact (sigma:=sigma) REnv r vvs a res
    ->
      interp_sact
        (sigma:=sigma) REnv r vvs (replace_all_occurrences_in_sact a var v')
        res.
  Proof.
    induction 2; simpl; intros; eauto.
    - destr.
      + subst. inv H. rewrite H0 in H3. inv H3.
        exploit (interp_sact_determ (ext_fn_t:=ext_fn_t) (reg_t:=reg_t)).
        apply H1. apply H4.
        intros ->; econstructor.
      + econstructor; eauto.
    - econstructor.
    - econstructor; eauto.
      destruct b; eauto.
    - econstructor; eauto.
    - econstructor; eauto.
    - econstructor; eauto.
    - econstructor.
  Qed.

  Lemma eval_sact_replace_reg:
    forall vvs idx v', getenv REnv r idx = v'
    -> forall fuel a,
    eval_sact vvs a fuel = eval_sact vvs (replace_reg_in_sact a idx v') fuel.
  Proof.
    induction fuel; simpl; intros; eauto.
    destruct a; simpl; intros; auto; repeat (rewrite <- ! IHfuel; now eauto).
    destruct eq_dec; subst; auto.
  Qed.

  Lemma eval_sact_replace_reg_vars:
    forall vvs idx v', getenv REnv r idx = v'
    -> forall fuel a,
    eval_sact vvs a fuel = eval_sact (replace_reg_in_vars vvs idx v') a fuel.
  Proof.
    induction fuel; simpl; intros; eauto.
    destruct a; simpl; intros; auto; repeat (rewrite <- ! IHfuel; now eauto).
    setoid_rewrite PTree.gmap. unfold option_map.
    unfold opt_bind. repeat destr. setoid_rewrite Heqo in Heqo0. inv Heqo0.
    rewrite <- IHfuel.  apply eval_sact_replace_reg.  auto.
    setoid_rewrite Heqo in Heqo0. inv Heqo0.
    setoid_rewrite Heqo in Heqo0. inv Heqo0.
  Qed.

  Lemma eval_sact_replace_reg_sact_vars:
    forall vvs idx v', getenv REnv r idx = v'
    -> forall fuel a,
    eval_sact vvs a fuel
    = eval_sact
        (replace_reg_in_vars vvs idx v') (replace_reg_in_sact a idx v') fuel.
  Proof.
    intros; rewrite <- eval_sact_replace_reg_vars, <- eval_sact_replace_reg;
      eauto.
  Qed.

  Lemma interp_sact_replace_inv:
    forall vvs (VSV: vvs_smaller_variables vvs) var v',
    interp_sact (sigma := sigma) REnv r vvs (SVar var) v'
    -> forall a n (BELOW: forall v, var_in_sact a v -> (v < n)%positive) res,
    interp_sact
      (sigma := sigma) REnv r vvs (replace_all_occurrences_in_sact a var v') res
    -> interp_sact (sigma:=sigma) REnv r vvs a res.
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
    - auto.
  Qed.

  Lemma interp_sact_replace_iff:
    forall vvs (VSV: vvs_smaller_variables vvs) var v' ,
      interp_sact (sigma:=sigma) REnv r vvs (SVar var) v'
      -> forall a t (WT: wt_sact (Sigma:=Sigma) R vvs a t) res,
        interp_sact (sigma:=sigma) REnv r vvs (replace_all_occurrences_in_sact a var v') res <->
        interp_sact (sigma:=sigma) REnv r vvs a res.
  Proof.
    split; intros.
    - eapply interp_sact_replace_inv; eauto.
      eapply wt_sact_valid_vars. 2: eauto.
      apply vvs_range_max_var.
    - eapply interp_sact_replace; eauto.
  Qed.

  Lemma interp_sact_replace_one_variable:
    forall vvs (VSV: vvs_smaller_variables vvs) var v' ,
      interp_sact (sigma:=sigma) REnv r vvs (SVar var) v'
      -> forall a n,
        (forall v, var_in_sact a v -> (v < n)%positive)
        -> forall res,
          interp_sact (sigma:=sigma) REnv r vvs a res
          -> interp_sact (sigma:=sigma) REnv r
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
        exploit (interp_sact_determ (reg_t:=reg_t) (ext_fn_t:=ext_fn_t)).
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
    - constructor.
  Qed.

  Lemma interp_sact_replace_one:
    forall vvs (VSV: vvs_smaller_variables vvs) var v',
    interp_sact (sigma:=sigma) REnv r vvs (SVar var) v'
    -> forall a n, (forall v, var_in_sact a v -> (v < n)%positive)
    -> forall res, interp_sact (sigma:=sigma) REnv r vvs a res
    -> interp_sact
         (sigma:=sigma) REnv r (replace_all_occurrences_in_vars vvs var v')
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
        exploit (interp_sact_determ (reg_t:=reg_t) (ext_fn_t:=ext_fn_t)).
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
    - constructor.
  Qed.

  Lemma interp_eval:
    forall vvs vvs' a b
           (VSV1: vvs_smaller_variables vvs)
           (VSV2: vvs_smaller_variables vvs') ta tb
           (WTa: wt_sact (Sigma:=Sigma) R vvs a ta)
           (WTb: wt_sact (Sigma:=Sigma) R vvs' b tb)
    ,
      (exists m, forall n, n >= m
      -> eval_sact vvs a n = eval_sact vvs' b n)
      -> (forall res, interp_sact (sigma:=sigma) REnv r vvs a res -> interp_sact (sigma:=sigma) REnv r vvs' b res).
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
           (WTa: wt_sact (Sigma:=Sigma) R vvs a ta)
           (WTb: wt_sact (Sigma:=Sigma) R vvs' b tb)
    ,
      (exists m, forall n, n >= m
      -> eval_sact vvs a n = eval_sact vvs' b n)
      -> (forall res, interp_sact (sigma:=sigma) REnv r vvs a res <-> interp_sact (sigma:=sigma) REnv r vvs' b res).
  Proof.
    intros vvs vvs' a b VSV1 VSV2 ta tb WTa WTb (m & EQ) res.
    split; intros.
    - eapply interp_eval. 6: eauto. all: eauto.
    - eapply interp_eval. 6: eauto. all: eauto.
      exists m; intros; eauto. rewrite EQ; auto.
  Qed.

  Lemma var_in_replace_reg:
    forall i v s v',
    var_in_sact (replace_reg_in_sact s i v) v' -> var_in_sact s v'.
  Proof.
    induction s; simpl; intros; eauto.
    - inv H.
      + apply IHs1 in H4. apply var_in_if_cond. eauto.
      + apply IHs2 in H4. apply var_in_if_true. eauto.
      + apply IHs3 in H4. apply var_in_if_false. eauto.
    - inv H. econstructor. eauto.
    - inv H.
      + eapply IHs1 in H4. apply var_in_sact_binop_1. eauto.
      + eapply IHs2 in H4. apply var_in_sact_binop_2. eauto.
    - inv H. apply IHs in H3. econstructor. eauto.
    - destruct (eq_dec idx i).
      + inv H.
      + inv H.
  Qed.

  Lemma wt_sact_replace_reg:
    forall vvs a i v t, wt_sact (Sigma:=Sigma) R vvs a t
    -> wt_val (R i) v
    -> wt_sact (Sigma:=Sigma) R vvs (replace_reg_in_sact a i v) t.
  Proof.
    induction a; simpl; intros; eauto; try (inv H; econstructor; eauto).
    inv H. destr; eauto. subst. constructor; auto.
    constructor.
  Qed.

  Lemma wt_sact_replace_reg_in_vars:
    forall vvs a i v t, wt_sact (Sigma:=Sigma) R vvs a t
    -> wt_val (R i) v
    -> wt_sact (Sigma:=Sigma) R (replace_reg_in_vars vvs i v) a t.
  Proof.
    induction a; simpl; intros; eauto.
    inv H. econstructor; eauto. setoid_rewrite PTree.gmap. setoid_rewrite H2.
    simpl; eauto.
    inv H; econstructor; eauto.
    inv H; econstructor; eauto.
    inv H; econstructor; eauto.
    inv H; econstructor; eauto.
    inv H; econstructor; eauto.
    inv H; econstructor; eauto.
  Qed.

  Hypothesis WTRENV: Wt.wt_renv R REnv r.

  Lemma interp_sact_replace_reg' :
    forall sf idx v a t res,
      vvs_smaller_variables (vars sf)
      -> wt_sact (Sigma:=Sigma) R (vars sf) a t
      -> getenv REnv r idx = v
      -> interp_sact (sigma:=sigma) REnv r (vars sf) a res <->
        interp_sact (sigma:=sigma) REnv r (vars (replace_reg sf idx v)) a res.
  Proof.
    intros.
    eapply interp_eval_iff; eauto.
    {
      simpl. red; intros. unfold replace_reg_in_vars in H2.
      rewrite PTree.gmap in H2. unfold option_map in H2; destr_in H2; inv H2.
      destr_in H5. inv H5.
      apply H in Heqo. apply Heqo.
      apply var_in_replace_reg in H3; auto.
    }
    simpl. eapply wt_sact_replace_reg_in_vars; eauto. subst. apply WTRENV.
    exists 0; intros.
    apply eval_sact_replace_reg_vars. auto.
  Qed.

  Lemma eval_sact_no_vars_interp:
    forall vvs s v (EVAL: eval_sact_no_vars s = Some v),
    interp_sact (sigma:=sigma) REnv r vvs s v.
  Proof.
    induction s; simpl; intros; eauto; unfold opt_bind in EVAL;
      repeat destr_in EVAL; inv EVAL; try (econstructor; eauto).
    - eapply val_beq_bits_implies_eq in Heqb0. destruct Heqb0.
      simpl. destruct (val_eq_dec v0 v0); eauto; destruct n; eauto.
    - eapply val_beq_bits_implies_eq in Heqb0. destruct Heqb0.
      simpl. destruct (val_eq_dec v0 v0); eauto; destruct n; eauto.
  Qed.

  Context {wt_sigma:
    forall ufn vc, wt_val (arg1Sig (Sigma ufn)) vc
    -> wt_val (retSig (Sigma ufn)) (sigma ufn vc)}.

  Lemma var_in_sact_replace:
    forall a n v x, var_in_sact (replace_all_occurrences_in_sact a n v) x
    -> var_in_sact a x.
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
      vvs_smaller_variables vvs
      -> vvs_smaller_variables (replace_all_occurrences_in_vars vvs n v).
  Proof.
    unfold vvs_smaller_variables; intros.
    setoid_rewrite PTree.gmap in H0.
    unfold option_map in H0; repeat destr_in H0; inv H0.
    eapply var_in_sact_replace in H1; eauto.
  Qed.

  Lemma wt_sact_replace:
    forall vvs a t n v t1,
      wt_sact (Sigma:=Sigma) R vvs a t
      -> wt_sact (Sigma:=Sigma) R vvs (SVar n) t1
      -> wt_val t1 v
      -> wt_sact (Sigma:=Sigma) R vvs (replace_all_occurrences_in_sact a n v) t.
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
    - constructor.
  Qed.

  Lemma wt_sact_replace_vars:
    forall vvs a t n v t1,
      wt_sact (Sigma:=Sigma) R vvs a t
      -> wt_sact (Sigma:=Sigma) R vvs (SVar n) t1
      -> wt_val t1 v
      -> wt_sact (Sigma:=Sigma) R (replace_all_occurrences_in_vars vvs n v) (replace_all_occurrences_in_sact a n v) t.
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
    - constructor.
  Qed.

  Lemma wt_sact_replace_vars':
    forall vvs a t n v t1,
      wt_sact (Sigma:=Sigma) R vvs a t
      -> wt_sact (Sigma:=Sigma) R vvs (SVar n) t1
      -> wt_val t1 v
      -> wt_sact (Sigma:=Sigma) R (replace_all_occurrences_in_vars vvs n v) a t.
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
    - constructor.
  Qed.

  Lemma wt_vvs_replace:
    forall vvs n v t1, wt_vvs (Sigma:=Sigma) R vvs
    -> wt_sact (Sigma:=Sigma) R vvs (SVar n) t1
    -> wt_val t1 v
    -> wt_vvs (Sigma:=Sigma) R (replace_all_occurrences_in_vars vvs n v).
  Proof.
    unfold wt_vvs; intros.
    setoid_rewrite PTree.gmap in H2.
    unfold option_map in H2; repeat destr_in H2; inv H2.
    eapply wt_sact_replace_vars; eauto.
  Qed.

  Lemma eval_sact_no_vars_wt:
    forall vvs s t (WT: wt_sact (Sigma:=Sigma) R vvs s t)
      v (EVAL: eval_sact_no_vars s = Some v),
    wt_val t v.
  Proof.
    induction 1; simpl; intros; unfold opt_bind in EVAL; try (inversion EVAL).
    - inv H1; eauto.
    - repeat destr_in EVAL; try (inversion EVAL).
      + eapply IHWT2 in EVAL; eauto.
      + eapply IHWT3 in EVAL; eauto.
    - repeat destr_in EVAL; try (inversion EVAL).
      eapply Wt.wt_unop_sigma1; eauto.
    - repeat destr_in EVAL; try (inversion EVAL);
        try (inv H; econstructor; eauto); eapply Wt.wt_binop_sigma1; eauto.
    - repeat destr_in EVAL; inv EVAL; eauto.
    - repeat destr_in EVAL; inv EVAL; eauto.
  Qed.

  Lemma eval_sact_no_vars_succeeds:
    forall a (NoVars: forall v, ~ var_in_sact a v)
           vvs t (WTa: wt_sact (Sigma:=Sigma) R vvs a t),
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
      { intros v VIS; eapply NoVars; eauto. apply var_in_sact_binop_1; eauto. }
      edestruct IHa2 as (r2 & EQ2); eauto.
      { intros v VIS; eapply NoVars; eauto. apply var_in_sact_binop_2; eauto. }
      rewrite EQ1, EQ2. simpl.
      edestruct wt_binop_interp. apply H5.
      eapply eval_sact_no_vars_wt. eauto. eauto.
      eapply eval_sact_no_vars_wt. eauto. eauto.
      exists x.
      destr.
      transitivity (if val_beq_bits r1 r2 then Some (Bits [negb negate]) else sigma2 (PrimUntyped.UEq negate) r1 r2).
      repeat destr; reflexivity.
      destr.
      unfold val_beq_bits in Heqb.
      repeat destr_in Heqb; inv Heqb.
      apply internal_list_dec_bl in H1. subst.
      destruct negate; simpl in H. inv H. simpl. destr. inv H. simpl.
      destr.
      intros; apply Bool.eqb_eq. rewrite H0. constructor.
    - inv WTa.
      edestruct IHa as (r1 & EQ1); eauto.
      intros v VIS; eapply NoVars; eauto. apply var_in_sact_external; eauto.
      rewrite EQ1. simpl. eauto.
  Qed.

  Lemma wt_sact_var_exists:
    forall a vvs t (WTa: wt_sact (Sigma:=Sigma) R vvs a t),
    forall v, var_in_sact a v -> In v (map fst (PTree.elements vvs)).
  Proof.
    induction 1; simpl; intros; eauto.
    - inv H0. apply PTree.elements_correct in H. apply (in_map fst) in H. auto.
    - inv H0.
    - inv H; eauto.
    - inv H0; eauto.
    - inv H0; eauto.
    - inv H; eauto.
    - inv H.
  Qed.

  Fixpoint simplify_sif (ua: sact) : sact :=
    match ua with
    | SIf cond tb fb =>
      match eval_sact_no_vars cond with
      | Some (Bits [true]) => tb
      | Some (Bits [false]) => fb
      | _ => ua
      end
    | SBinop ufn a1 a2 => SBinop ufn (simplify_sif a1) (simplify_sif a2)
    | SUnop ufn a => SUnop ufn (simplify_sif a)
    | SExternalCall ufn a => SExternalCall ufn (simplify_sif a)
    | SVar _ | SReg _ | SConst _ => ua
    end.

  Fixpoint simplify_sact (ua: sact) : sact :=
    match ua with
    | SIf cond tb fb =>
      let cond' := simplify_sact cond in
      match eval_sact_no_vars cond' with
      | Some (Bits [true]) => simplify_sact tb
      | Some (Bits [false]) => simplify_sact fb
      | _ => SIf cond' (simplify_sact tb) (simplify_sact fb)
      end
    | SBinop ufn a1 a2 =>
      let a1' := simplify_sact a1 in
      match ufn with
      | PrimUntyped.UBits2 PrimUntyped.UAnd =>
        match eval_sact_no_vars a1' with
        | Some (Bits [false]) => const_false
        | Some (Bits [true]) => simplify_sact a2
        | _ =>
          let a2' := simplify_sact a2 in
          match eval_sact_no_vars a2' with
          | Some (Bits [false]) => const_false
          | Some (Bits [true]) => a1'
          | _ => SBinop ufn a1' a2'
          end
        end
      | PrimUntyped.UBits2 PrimUntyped.UOr =>
        match eval_sact_no_vars a1' with
        | Some (Bits [true]) => const_true
        | Some (Bits [false]) => simplify_sact a2
        | _ =>
          let a2' := simplify_sact a2 in
          match eval_sact_no_vars a2' with
          | Some (Bits [true]) => const_true
          | Some (Bits [false]) => a1'
          | _ => SBinop ufn a1' a2'
          end
        end
      | fn =>
        let a2' := simplify_sact a2 in
        match eval_sact_no_vars a1', eval_sact_no_vars a2' with
        | Some x, Some y =>
          match sigma2 fn x y with
          | Some r => SConst r
          | None => SBinop ufn a1' a2'
          end
        | _, _ => SBinop ufn a1' a2'
        end
      end
    | SUnop ufn a => (* Perhaps not strictly required *)
      let a := simplify_sact a in
      (* match ufn with *)
      (* | PrimUntyped.UBits1 PrimUntyped.UNot => *)
      (*   match eval_sact_no_vars a with *)
      (*   | Some (Bits [b]) => SConst (Bits [negb b]) *)
      (*   | _ => SUnop ufn a *)
      (*   end *)
      (* | fn => *)
        match eval_sact_no_vars a with
        | Some x =>
          match sigma1 ufn x with
          | Some r => SConst r
          | None => SUnop ufn a
          end
        | None => SUnop ufn a
        end
      (* end *)
    | SExternalCall ufn a => SExternalCall ufn (simplify_sact a)
    | SVar _ | SReg _ | SConst _ => ua
    end.


  Definition simplify_var (sf: simple_form) var :=
    match (vars sf) ! var with
    | Some (t, a) =>
      match eval_sact_no_vars a with
      | Some v => (replace_all_occurrences sf var v, [(var,v)])
      | None => (sf, [])
      end
    | None => (sf, [])
    end.

  Definition simplify_vars (v: var_value_map) :=
    Maps.PTree.map (fun _ '(t, a) => (t, simplify_sact a)) v.

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
    - inversion 1.
  Qed.

  Lemma simplify_var_correct:
    forall sf var sf' l
           (SIMP: simplify_var sf var = (sf', l))
           (VSV: vvs_smaller_variables (vars sf))
           (WT: wt_vvs (Sigma:=Sigma) R (vars sf)),
      Forall (fun '(var,v) => interp_sact (sigma:=sigma) REnv r (vars sf') (SVar var) v) l
      /\ vvs_smaller_variables (vars sf')
      /\ wt_vvs (Sigma:=Sigma) R (vars sf')
      /\ NoDup (map fst l)
      /\ (forall a res t,
             wt_sact (Sigma:=Sigma) R (vars sf) a t
             -> interp_sact (sigma:=sigma) REnv r (vars sf) a res
             -> interp_sact (sigma:=sigma) REnv r (vars sf') a res)
  /\ (forall x t y res,
         (vars sf) ! x = Some (t,y)
         -> interp_sact (sigma:=sigma) REnv r (vars sf) y res
         -> (exists y' ,
                  (vars sf') ! x = Some (t,y') /\
                    interp_sact (sigma:=sigma) REnv r (vars sf') y' res)
     ) /\
  (forall x t y v, (vars sf') ! x = Some (t,y)
  -> var_in_sact y v -> ~ In v (map fst l)) /\
        (forall x t y,
            (vars sf') ! x = Some (t, y)
            -> exists y' ,
              (vars sf) ! x = Some (t, y') /\
                forall v, var_in_sact y v -> var_in_sact y' v).
  Proof.
    unfold simplify_var. intros. repeat destr_in SIMP; inv SIMP; eauto.
    assert (VSV': vvs_smaller_variables (vars (replace_all_occurrences sf var v))).
    eapply vvs_smaller_variables_replace; now eauto.
    assert (WTVVS':  wt_vvs (Sigma:=Sigma) R (vars (replace_all_occurrences sf var v))).
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
        Unshelve. exact R. exact Sigma.
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
           (WTV: wt_vvs (Sigma:=Sigma) R (vars sf))
           (VSV: vvs_smaller_variables (vars sf))
           (NDlvars: NoDup lvars)
           (ND: NoDup (map fst l))
           (DISJ: forall x, In x lvars -> ~ In x (map fst l))
           (NIV: (forall x t y v, (vars sf) ! x = Some (t,y)
           -> var_in_sact y v -> ~ In v (map fst l))),
      vvs_smaller_variables (vars sf') /\
        wt_vvs (Sigma:=Sigma) R (vars sf') /\ (incl l l') /\ NoDup (map fst l')
      /\ (forall x t y v, (vars sf') ! x = Some (t,y)
      -> var_in_sact y v -> ~ In v (map fst l')).
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
           (WTV: wt_vvs (Sigma:=Sigma) R (vars sf))
           (ACC: Forall (fun '(var, v) => interp_sact (sigma:=sigma) REnv r (vars sf) (SVar var) v) l)
           (VSV: vvs_smaller_variables (vars sf))
           (NOvarsl: forall x t y v,
               (vars sf) ! x = Some (t,y)
               -> var_in_sact y v -> ~ In v (map fst l) /\ In v lvars)
    ,
      (forall x t y res,
          (vars sf) ! x = Some (t,y)
          -> interp_sact (sigma:=sigma) REnv r (vars sf) y res
          -> (exists y' ,
              (vars sf') ! x = Some (t,y') /\
                interp_sact (sigma:=sigma) REnv r (vars sf') y' res)
      ) /\
        vvs_smaller_variables (vars sf') /\
        wt_vvs (Sigma:=Sigma) R (vars sf') /\
        Forall (fun '(var, v) => interp_sact (sigma:=sigma) REnv r (vars sf') (SVar var) v) l' /\
        (forall x t y v, (vars sf') ! x = Some (t,y)
        -> var_in_sact y v -> ~ In v (map fst l'))
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
          2:{ red. intros; lia. }
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
           (WTa: wt_sact (Sigma:=Sigma) R vvs a t)
           (NVa: ~ var_in_sact a v),
      wt_sact (Sigma:=Sigma) R (PTree.remove v vvs) a t.
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
    - constructor.
  Qed.

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
      Sorted le1 l
      -> NoDup l
      -> Sorted le2 l.
  Proof.
    induction 2; simpl; intros; eauto.
    inv H1. econstructor. eauto.
    inv H0. econstructor. econstructor. rewrite STRICT. split; auto. intro; subst. apply H4; simpl; auto.
  Qed.

  Lemma sorted_lt: forall l, NoDup l -> Sorted Pos.lt (PosSort.sort l).
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
           (WT: wt_vvs (Sigma:=Sigma) R (vars sf)),
      NoDup (map fst l) /\
        forall v reg (REG: list_assoc (final_values sf) reg = Some v) res
               (INT: interp_sact (sigma:=sigma) REnv r (vars sf) (SVar v) res),
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
  Lemma val_eq_dec_refl: forall v, exists x, val_eq_dec v v = left x.
  Proof. intros. destruct (val_eq_dec v v); eauto. congruence. Qed.

  Lemma eval_sact_eval_sact_no_vars:
    forall vvs n a res res2,
      eval_sact vvs a n = Some res
      -> eval_sact_no_vars a = Some res2
      -> res = res2.
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
    - unfold opt_bind in H1.
      destruct (eval_sact_no_vars s1) eqn:eq1;
      destruct (eval_sact_no_vars s2) eqn:eq2; try congruence.
      apply (IHn _ _ _ Heqo) in eq1.
      apply (IHn _ _ _ Heqo0) in eq2.
      destruct eq1. destruct eq2.
      destruct ufn2; simpl in H2.
      + repeat (destr_in H1); simpl in *; try congruence; destr_in H2;
        try congruence.
        * apply val_beq_bits_implies_eq in Heqb0. congruence.
        * apply val_beq_bits_implies_eq in Heqb0. congruence.
      + repeat destr_in H2; simpl in *; congruence.
      + repeat destr_in H2; simpl in *; congruence.
      + destr_in H2; destr_in H2; simpl in *; congruence.
    - unfold opt_bind in H1. destr_in H1.
      exploit IHn. apply Heqo. eauto. intro; subst. congruence. congruence.
  Qed.

  Lemma wt_simplify_sact:
    forall vss a t,
      wt_sact R (Sigma:=Sigma) vss a t ->
      wt_sact R (Sigma:=Sigma) vss (simplify_sact a) t.
  Proof.
    induction 1; simpl; intros; eauto.
    - econstructor; eauto.
    - econstructor; eauto.
    - destr.
      exploit eval_sact_no_vars_wt. 2: eauto. eauto.
      intro WT. apply wt_val_bool in WT. destruct WT; subst.
      destr.
      econstructor; eauto.
    -
      assert (wt_sact (Sigma:=Sigma) R vss
                match eval_sact_no_vars (simplify_sact a) with
                | Some x => match sigma1 ufn x with
                            | Some r => SConst r
                            | None => SUnop ufn (simplify_sact a)
                            end
                | None => SUnop ufn (simplify_sact a)
                end t'
             ).
      {
        destr.
        exploit eval_sact_no_vars_wt. 2: eauto. eauto.
        intro WT.
        destr.
        econstructor; eauto.
        eapply Wt.wt_unop_sigma1; eauto.
        econstructor; eauto.
        econstructor; eauto.
      }
      destr; auto.
    - assert ( wt_sact (Sigma:=Sigma) R vss
                 match eval_sact_no_vars (simplify_sact a1) with
                 | Some x =>
                     match eval_sact_no_vars (simplify_sact a2) with
                     | Some y => match sigma2 ufn x y with
                                 | Some r0 => SConst r0
                                 | None => SBinop ufn (simplify_sact a1) (simplify_sact a2)
                                 end
                     | None => SBinop ufn (simplify_sact a1) (simplify_sact a2)
                     end
                 | None => SBinop ufn (simplify_sact a1) (simplify_sact a2)
                 end t').
      {
        destr.
        2: econstructor; eauto.
        destr.
        2: econstructor; eauto.
        exploit eval_sact_no_vars_wt. 2: apply Heqo. eauto.
        intro WT1.
        exploit eval_sact_no_vars_wt. 2: apply Heqo0. eauto.
        intro WT2.
        destr.
        2: econstructor; eauto.
        econstructor.
        eapply Wt.wt_binop_sigma1; eauto.
      }
      destr; auto.
      destr; auto.
      + clear H2. inv H1.
        destr. exploit eval_sact_no_vars_wt. apply IHwt_sact1. eauto. intro WT1. inv WT1.
        destruct (eval_sact_no_vars (simplify_sact a2)) eqn:?.
        exploit eval_sact_no_vars_wt. apply IHwt_sact2. eauto. intro WT2. inv WT2.
        destr. destr. econstructor; eauto. econstructor; eauto. simpl in H2; lia.
        destruct bs0. simpl in H2; lia. simpl in H2. destruct l.
        destr; eauto. constructor. constructor. auto.
        destruct bs0. simpl in H2; lia. simpl in H2.
        repeat destr; eauto; econstructor; eauto; constructor; auto.
        repeat destr;
          repeat econstructor; eauto.
        repeat destr;
          repeat econstructor; eauto.
        subst.
        exploit eval_sact_no_vars_wt. apply IHwt_sact2. eauto. intro WT2. inv WT2.
        auto.
      + clear H2. inv H1.
        destr. exploit eval_sact_no_vars_wt. apply IHwt_sact1. eauto. intro WT1. inv WT1.
        destruct (eval_sact_no_vars (simplify_sact a2)) eqn:?.
        exploit eval_sact_no_vars_wt. apply IHwt_sact2. eauto. intro WT2. inv WT2.
        destr. destr. econstructor; eauto. econstructor; eauto. simpl in H2; lia.
        destruct bs0. simpl in H2; lia. simpl in H2. destruct l.
        destr; eauto. constructor. constructor. auto.
        destruct bs0. simpl in H2; lia. simpl in H2.
        repeat destr; eauto; econstructor; eauto; constructor; auto.
        repeat destr;
          repeat econstructor; eauto.
        repeat destr;
          repeat econstructor; eauto.
        subst.
        exploit eval_sact_no_vars_wt. apply IHwt_sact2. eauto. intro WT2. inv WT2.
        auto.
    - econstructor; eauto.
    - econstructor; eauto.
  Qed.

  Lemma simplify_unop_cases:
    forall ufn a a',
    simplify_sact (SUnop ufn a) = a' ->
    forall ta tr vss,
    wt_unop ufn ta tr ->
    wt_sact (Sigma:=Sigma) R vss a ta ->
      (
        exists b x,
          eval_sact_no_vars (simplify_sact a) = Some b
          /\ sigma1 ufn b = Some x
          /\ a' = SConst x
      )
    \/ a' = SUnop ufn (simplify_sact a).
  Proof.
    intros. simpl in H. simpl.
    subst. destr. destr.
    - left. exists v, v0; split; auto.
    - right; auto.
    - right; auto.
  Qed.

  Lemma simplify_bnop_cases:
    forall ufn a1 a2 a' ,
      simplify_sact (SBinop ufn a1 a2) = a'
      -> a' = SBinop ufn (simplify_sact a1) (simplify_sact a2)
      \/ (ufn = PrimUntyped.UBits2 PrimUntyped.UAnd
          /\ ((eval_sact_no_vars (simplify_sact a1) = Some (Bits [true])
               /\ a' = simplify_sact a2)
              \/ (eval_sact_no_vars (simplify_sact a1) = Some (Bits [false])
                  /\ a' = const_false)
              \/ (eval_sact_no_vars (simplify_sact a2) = Some (Bits [true])
                  /\ a' = simplify_sact a1)
              \/ (eval_sact_no_vars (simplify_sact a2) = Some (Bits [false])
                  /\ a' = const_false)))
      \/ (ufn = PrimUntyped.UBits2 PrimUntyped.UOr
          /\ ((eval_sact_no_vars (simplify_sact a1) = Some (Bits [true])
               /\ a' = const_true)
              \/ (eval_sact_no_vars (simplify_sact a1) = Some (Bits [false])
                  /\ a' = simplify_sact a2)
              \/ (eval_sact_no_vars (simplify_sact a2) = Some (Bits [true])
                  /\ a' = const_true)
              \/ (eval_sact_no_vars (simplify_sact a2) = Some (Bits [false])
                  /\ a' = simplify_sact a1)))
  \/ (
      exists v1 v2 v,
      eval_sact_no_vars (simplify_sact a1) = Some v1 /\
      eval_sact_no_vars (simplify_sact a2) = Some v2 /\
        sigma2 ufn v1 v2 = Some v /\
        a' = SConst v
    ).
  Proof.
    intros. simpl in H. subst.
    repeat destr; intuition eauto.
    - repeat right. do 3 eexists; repeat split; eauto.
    - repeat right. do 3 eexists; repeat split; eauto.
    - repeat right. do 3 eexists; repeat split; eauto.
    - repeat right. do 3 eexists; repeat split; eauto.
    - repeat right. do 3 eexists; repeat split; eauto.
    - repeat right. do 3 eexists; repeat split; eauto.
    - repeat right. do 3 eexists; repeat split; eauto.
    - repeat right. do 3 eexists; repeat split; eauto.
    - repeat right. do 3 eexists; repeat split; eauto.
    - repeat right. do 3 eexists; repeat split; eauto.
    - repeat right. do 3 eexists; repeat split; eauto.
    - repeat right. do 3 eexists; repeat split; eauto.
    - repeat right. do 3 eexists; repeat split; eauto.
    - repeat right. do 3 eexists; repeat split; eauto.
    - repeat right. do 3 eexists; repeat split; eauto.
  Qed.

  Lemma eval_sact_wt:
    forall vvs (WT: wt_vvs (Sigma:=Sigma) R vvs) n a r t
      (WTa: wt_sact (Sigma:=Sigma) R vvs a t)
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

  Lemma simplify_sact_correct:
    forall vvs (WTV: wt_vvs R (Sigma:=Sigma) vvs) n a res t,
    wt_sact (Sigma:=Sigma) R vvs a t
    -> eval_sact vvs a n = Some res
    -> eval_sact vvs (simplify_sact a) n = Some res.
  Proof.
    induction n; intros a res t WT EVAL; eauto.
    simpl in EVAL.
    unfold opt_bind in EVAL.
    repeat destr_in EVAL; inv EVAL; auto.
    - simpl. rewrite Heqo; eauto.
    - inv WT.
      simpl.
      destruct (eval_sact_no_vars (simplify_sact s1)) eqn:?.
      eapply eval_sact_eval_sact_no_vars in Heqo0; eauto. subst.
      transitivity (eval_sact vvs (simplify_sact s2) (S n)). reflexivity.
      exploit IHn. 2: apply H0. eauto. intro ES. exploit eval_sact_more_fuel.
      apply ES.
      2: intro ES'; rewrite ES'. lia. eauto.
      erewrite IHn. 2-3: eauto. simpl.
      erewrite IHn; eauto.
    - inv WT.
      simpl.
      destruct (eval_sact_no_vars (simplify_sact s1)) eqn:?.
      eapply eval_sact_eval_sact_no_vars in Heqo0; eauto. subst.
      transitivity (eval_sact vvs (simplify_sact s3) (S n)). reflexivity.
      exploit IHn. 2: apply H0. eauto. intro ES. exploit eval_sact_more_fuel.
      apply ES.
      2: intro ES'; rewrite ES'. lia. eauto.
      erewrite IHn. 2-3: eauto. simpl.
      erewrite IHn; eauto.
    - inv WT.
      edestruct (simplify_unop_cases ufn1 s _ eq_refl) as
        [(b & vv & EQ & ESNV & EQ')|EQ]; eauto.
      + rewrite EQ'. simpl.
        exploit eval_sact_eval_sact_no_vars. 2: eauto. eapply IHn. eauto. eauto.
        intros ->.
        simpl. auto.
      + rewrite EQ. simpl. erewrite IHn; simpl; eauto.
    - inv WT.
      exploit eval_sact_wt. 3: apply Heqo. all: eauto.
      exploit eval_sact_wt. 3: apply Heqo0. all: eauto.
      intros WTv2 WTv1.
      exploit Wt.wt_binop_sigma1. eauto. eauto. eauto. eauto. intro WTres.
      eapply IHn in Heqo; eauto.
      eapply IHn in Heqo0; eauto.
      destruct (simplify_bnop_cases ufn2 s1 s2 _ eq_refl) as
        [EQ|[(ufneq & [(ESNV & EQ)|[(ESNV & EQ)|[(ESNV & EQ)|(ESNV & EQ)]]])
            |[(ufneq & [(ESNV & EQ)|[(ESNV & EQ)|[(ESNV & EQ)|(ESNV & EQ)]]])|
        (v1 & v2 & vv & ESNV1 & ESNV2 & SIGMA & EQ)]]]; rewrite EQ; clear EQ.
      + simpl. rewrite Heqo, Heqo0.  reflexivity.
      + exploit eval_sact_eval_sact_no_vars. apply Heqo. apply ESNV. intros ->.
        inv WTv1. inv H6.
        apply wt_val_bool in WTv2.
        apply wt_val_bool in WTres.
        destruct WTv2, WTres. subst.
        erewrite eval_sact_more_fuel. 2: eauto. simpl. auto. lia.
      + exploit eval_sact_eval_sact_no_vars. apply Heqo. apply ESNV. intros ->.
        inv WTv1. inv H6.
        apply wt_val_bool in WTv2.
        apply wt_val_bool in WTres.
        destruct WTv2, WTres. subst.
        simpl. auto.
      + exploit eval_sact_eval_sact_no_vars. 2: apply ESNV. eauto. intros ->.
        inv WTv2. inv H6.
        apply wt_val_bool in WTv1.
        apply wt_val_bool in WTres.
        destruct WTv1, WTres. subst.
        erewrite eval_sact_more_fuel. 2: eauto. simpl. rewrite andb_true_r; auto. lia.
      + exploit eval_sact_eval_sact_no_vars. 2: apply ESNV. eauto. intros ->.
        inv WTv2. inv H6.
        apply wt_val_bool in WTv1.
        apply wt_val_bool in WTres.
        destruct WTv1, WTres. subst.
        simpl. rewrite andb_false_r; auto.
      + exploit eval_sact_eval_sact_no_vars. 2: apply ESNV. eauto. intros ->.
        inv WTv1. inv H6.
        apply wt_val_bool in WTv2.
        apply wt_val_bool in WTres.
        destruct WTv2, WTres. subst. simpl; auto.
      + exploit eval_sact_eval_sact_no_vars. 2: apply ESNV. eauto. intros ->.
        inv WTv1. inv H6.
        apply wt_val_bool in WTv2.
        apply wt_val_bool in WTres.
        destruct WTv2, WTres. subst.
        erewrite eval_sact_more_fuel. 2: eauto. simpl. auto. lia.
      + exploit eval_sact_eval_sact_no_vars. 2: apply ESNV. eauto. intros ->.
        inv WTv2. inv H6.
        apply wt_val_bool in WTv1.
        apply wt_val_bool in WTres.
        destruct WTv1, WTres. subst. simpl. rewrite orb_true_r; auto.
      + exploit eval_sact_eval_sact_no_vars. 2: apply ESNV. eauto. intros ->.
        inv WTv2. inv H6.
        apply wt_val_bool in WTv1.
        apply wt_val_bool in WTres.
        destruct WTv1, WTres. subst.
        erewrite eval_sact_more_fuel. 2: eauto. simpl. rewrite orb_false_r; auto. lia.
      + exploit eval_sact_eval_sact_no_vars. 2: apply ESNV1. eauto. intros ->.
        exploit eval_sact_eval_sact_no_vars. 2: apply ESNV2. eauto. intros ->.
        rewrite H0 in SIGMA. inv SIGMA. simpl. eauto.
    - simpl. inv WT;  erewrite IHn; simpl; eauto.
  Qed.

  Fixpoint regs_in_sact_aux (s: sact) (regs: list reg_t) :=
    match s with
    | SReg idx => if in_dec eq_dec idx regs then regs else idx::regs
    | SVar _
    | SConst _ => regs
    | SUnop _ a
    | SExternalCall _ a => regs_in_sact_aux a regs
    | SBinop _ a1 a2 => regs_in_sact_aux a1 (regs_in_sact_aux a2 regs)
    | SIf a0 a1 a2 => regs_in_sact_aux a0 (regs_in_sact_aux a1 (regs_in_sact_aux a2 regs))
    end.

  Definition useful_vars_for_var (sf: simple_form) (v: positive)
  : list positive :=
    reachable_vars_aux (vars sf) v [] (S (Pos.to_nat v)).

  Definition useful_regs_for_var sf v :=
    fold_left
      (fun regs v =>
        match (vars sf) ! v with
        | Some (_, s) => regs_in_sact_aux s regs
        | None => regs
        end
      )
      (useful_vars_for_var sf v) [].

  Definition interp_cycle (sf: simple_form) : UREnv :=
    let sf := remove_vars sf in
    let fenv := inlining_pass sf in
    create
      REnv
      (fun k =>
        match list_assoc (final_values sf) k with
        | Some n =>
          match list_assoc fenv n with
          | Some v => v
          | None => getenv REnv r k (* Should be unreachable *)
          end
        | None => getenv REnv r k
        end).

  Definition prune_irrelevant_aux (sf: simple_form) reg v := {|
    final_values := [(reg, v)];
    vars := filter_ptree (vars sf) (PTree.empty _) (useful_vars_for_var sf v)
  |}.

  Definition prune_irrelevant (sf: simple_form) reg :=
    match list_assoc (final_values sf) reg with
    | Some v => Some (prune_irrelevant_aux sf reg v)
    | None => None
    end.

  Definition get_val (sf: simple_form) reg : option val :=
    let sf := remove_vars sf in
    let fenv := inlining_pass sf in
    match list_assoc (final_values sf) reg with
    | Some n => list_assoc fenv n
    | None => None
    end.

  Lemma normal_form_ok:
    forall
      {finreg: FiniteType reg_t} (rules: rule_name_t -> daction) (s: schedule)
      (GS: good_scheduler s) (WTr: Wt.wt_renv R REnv r)
      (TA:
        forall rule, exists t,
        wt_daction (R:=R) (Sigma:=Sigma) pos_t string string [] (rules rule) t),
    UntypedSemantics.interp_dcycle rules r sigma s
    = interp_cycle
      (SimpleForm.schedule_to_simple_form (Sigma:=Sigma) R rules s).
  Proof.
    intros.
    unfold interp_dcycle.
    generalize (schedule_to_simple_form_ok
                  (wt_sigma:=wt_sigma)
                  REnv r R WTRENV rules _ GS _ eq_refl TA WTr). simpl.
    intros (WTV & VSV & INFINAL & WTFinal & SPECFINAL).
    unfold interp_cycle. unfold commit_update.
    apply create_funext. intro k.
    simpl.
    destruct (SPECFINAL k) as (n & GET & INTERP). rewrite GET.

    Lemma filter_ptree_eq:
      forall l v (vvs t2: var_value_map (ext_fn_t:=ext_fn_t) (reg_t:=reg_t)),
        In v l
        -> NoDup l
        -> (forall x, In x l -> t2 ! x = None)
        -> vvs ! v = (filter_ptree vvs t2 l) ! v.
    Proof.
      induction l; simpl; intros. easy.
      inv H0. destruct H. subst.
      destr.
      rewrite filter_ptree_in. rewrite PTree.gss. auto. auto.
      rewrite filter_ptree_in; auto. symmetry; apply H1. auto.
      rewrite <- IHl. auto. auto. auto. intros.
      destr; eauto. rewrite PTree.gso; eauto. congruence.
    Qed.
    Lemma wt_sact_reachable:
      forall v1 v2 a t
             (SAME: forall v, reachable_var v1 a v -> v1 ! v = v2 ! v),
        wt_sact (Sigma:=Sigma) R v1 a t -> wt_sact (Sigma:=Sigma) R v2 a t.
    Proof.
      induction 2; simpl; intros; eauto.
      - econstructor. rewrite <- SAME. eauto. constructor.
      - constructor; auto.
      - econstructor.
        apply IHwt_sact1. intros v RV; apply SAME. eapply reachable_var_if_cond; eauto.
        apply IHwt_sact2. intros v RV; apply SAME. eapply reachable_var_if_true; eauto.
        apply IHwt_sact3. intros v RV; apply SAME. eapply reachable_var_if_false; eauto.
      - econstructor; eauto.
        apply IHwt_sact. intros v RV; apply SAME. eapply reachable_var_unop; eauto.
      - econstructor; eauto.
        apply IHwt_sact1. intros v RV; apply SAME. eapply reachable_var_binop1; eauto.
        apply IHwt_sact2. intros v RV; apply SAME. eapply reachable_var_binop2; eauto.
      - econstructor; eauto.
        apply IHwt_sact. intros v RV; apply SAME. eapply reachable_var_externalCall; eauto.
      - constructor.
    Qed.

    Lemma wt_sact_remove_vars:
      forall sf (VSV: vvs_smaller_variables (vars sf))
             v (IN: In v (useful_vars sf))
             s t
             (GET: (vars sf) ! v = Some (t, s))
             (WT: wt_sact (Sigma:=Sigma) R (vars sf) s t),
        wt_sact (Sigma:=Sigma) R (vars (remove_vars sf)) s t.
    Proof.
      intros.
      assert (forall v0, reachable_var (vars sf) (SVar v) v0 -> In v0 (useful_vars sf)).
      {
        intros v0 RV. inv RV. auto.
        rewrite GET in H0; inv H0.
        intros; eapply useful_vars_ok; eauto.
      }
      specialize (fun v REACH vvs t2 => filter_ptree_eq _ _ vvs t2 (H v REACH) (nodup_useful_vars _ VSV)).
      simpl.
      fold (filter_ptree (vars sf) (PTree.empty _) (useful_vars sf)).
      intros. eapply wt_sact_reachable. 2: eauto.
      intros; apply H0. econstructor; eauto.
      intros; apply PTree.gempty.
    Qed.

    Lemma filter_ptree_inv:
      forall vvs l t2 v x,
        (filter_ptree vvs t2 l ) ! v = Some x
        -> NoDup l
        -> (forall x, In x l -> t2 ! x = None)
        -> t2 ! v = Some x \/ In v l /\ vvs ! v = Some x.
    Proof.
      induction l; simpl; intros; eauto.
      inv H0.
      apply IHl in H; auto.
      - destruct H as [EQ | (IN & GET)].
        + destr_in EQ; auto.
          rewrite PTree.gsspec in EQ.
          destr_in EQ; auto. inv EQ.
          right; split; eauto.
        + right; split; eauto.
      - intros. destr. rewrite PTree.gso; eauto. congruence. apply H1; auto.
    Qed.

    Lemma wt_vvs_remove_vars:
      forall sf (VSV: vvs_smaller_variables (vars sf)),
      wt_vvs (Sigma:=Sigma) R (vars sf)
      -> wt_vvs (Sigma:=Sigma) R (vars (remove_vars sf)).
    Proof.
      red; intros.
      simpl in *.
      fold (filter_ptree (vars sf) (PTree.empty _) (useful_vars sf)) in H0.
      apply filter_ptree_inv in H0. rewrite PTree.gempty in H0.
      destruct H0 as [|(IN & GET)]. inv H0.
      eapply wt_sact_remove_vars; eauto.
      eapply nodup_useful_vars; eauto.
      intros; apply PTree.gempty.
    Qed.

    Lemma vsv_remove_vars:
      forall sf,
      vvs_smaller_variables (vars sf)
      -> vvs_smaller_variables (vars (remove_vars sf)).
    Proof.
      red; intros.
      simpl in *.
      fold (filter_ptree (vars sf) (PTree.empty _) (useful_vars sf)) in H0.
      apply filter_ptree_inv in H0.
      destruct H0.
      rewrite PTree.gempty in H0. congruence.
      destruct H0 as (IN & GET).
      eapply H; eauto.
      eapply nodup_useful_vars; eauto.
      intros; apply PTree.gempty.
    Qed.

    assert (VSV2:=vsv_remove_vars _ VSV).
    assert (WTV2:=wt_vvs_remove_vars _ VSV WTV).

    generalize (inlining_pass_correct _ _ eq_refl VSV2 WTV2).
    intros (ND2 & INLINING).

    inversion INTERP. subst.
    exploit INLINING. apply GET.
    rewrite interp_eval_iff.
    6: (exists O; intros; symmetry; eapply remove_vars_correct; eauto).
    apply INTERP. auto. auto.
    econstructor. simpl.
    fold (filter_ptree (vars (schedule_to_simple_form (Sigma:=Sigma) R rules s))
                       (PTree.empty _)
                       (useful_vars (schedule_to_simple_form (Sigma:=Sigma) R rules s))
         ).
    rewrite <- filter_ptree_eq. eauto.
    eapply useful_vars_incl. 2: eauto. eauto.
    eapply list_assoc_in in GET. apply (in_map snd) in GET; eauto.
    apply nodup_useful_vars; auto.
    intros; apply PTree.gempty. econstructor; eauto.
    eapply list_assoc_in in GET. apply (in_map snd) in GET; eauto.
    intro IN. apply in_list_assoc in IN.
    setoid_rewrite IN.
    auto. auto.
  Qed.

  Lemma getenv_interp_cycle:
    forall
      {finreg: FiniteType reg_t} (rules: rule_name_t -> daction) (s: schedule)
      (GS: good_scheduler s) (WTr: Wt.wt_renv R REnv r)
      (TA:
        forall rule, exists t,
        wt_daction (R:=R) (Sigma:=Sigma) pos_t string string [] (rules rule) t)
      k,
    let sf := (SimpleForm.schedule_to_simple_form (Sigma:=Sigma) R rules s) in
    exists n s t,
    list_assoc (final_values sf) k = Some n
    /\ (vars sf) ! n = Some (t, s)
    /\ do_eval_sact (vars sf) s = Some (getenv REnv (interp_cycle sf) k).
  Proof.
    intros.
    unfold interp_cycle. rewrite getenv_create.
    Opaque vvs_size. Opaque max_var. Opaque size_sact. Opaque eval_sact.
    generalize (schedule_to_simple_form_ok
                  (wt_sigma:=wt_sigma)
                  REnv r R WTRENV rules _ GS _ eq_refl TA WTr). simpl.
    intros (WTV & VSV  & INFINAL & WTFinal & SPECFINAL).
    destruct (SPECFINAL k) as (n & GET & INTERP).
    unfold sf. rewrite GET.
    inv INTERP. exists n. rewrite H0. exists a, t. split; auto. split; auto.
    eapply interp_sact_eval_sact; eauto.
    edestruct inlining_pass_correct as (ND2 & INLINING). reflexivity.
    apply vsv_remove_vars; eauto.
    apply wt_vvs_remove_vars; eauto.
    exploit INLINING. simpl. apply GET.
    eapply interp_eval. apply VSV. eapply vsv_remove_vars; eauto.
    eapply wt_sact_var. eauto.
    econstructor. simpl.
    fold (
      filter_ptree
        (vars (schedule_to_simple_form (Sigma:=Sigma) R rules s))
        (PTree.empty _)
        (useful_vars (schedule_to_simple_form (Sigma:=Sigma) R rules s))).
    rewrite <- filter_ptree_eq. eauto.
    eapply useful_vars_incl. 2: eauto. eauto.
    eapply list_assoc_in in GET. apply (in_map snd) in GET; eauto.
    apply nodup_useful_vars; auto.
    intros; apply PTree.gempty.
    exists O; intros.
    apply remove_vars_correct. auto.
    eapply list_assoc_in in GET. apply (in_map snd) in GET; eauto.
    econstructor; eauto.
    intro IN. apply in_list_assoc in IN.
    setoid_rewrite IN.
    auto. auto.
  Qed.

  Definition simplify_sf sf :=
    {| final_values := final_values sf; vars := simplify_vars (vars sf) |}.

  Definition simplify_sifs_sf sf := {|
    final_values := final_values sf;
    vars := Maps.PTree.map (fun _ '(t, a) => (t, simplify_sif a)) (vars sf) |}.

  Lemma bits_Bits:
    forall vvs a sz (WTA : wt_sact (Sigma := Sigma) R vvs a (bits_t sz))
      x (VA : eval_sact_no_vars a = Some x),
    exists b, x = Bits b /\ List.length b = sz.
  Proof.
    intros.
    apply (eval_sact_no_vars_wt _ _ _ WTA _) in VA.
    inv VA. exists bs. split; eauto.
  Qed.

  Lemma simplify_sact_wt_sact_ok':
    forall vvs a t (WTS: wt_sact (Sigma := Sigma) R vvs a t),
    wt_sact (Sigma := Sigma) R vvs (simplify_sact a) t.
  Proof.
    apply wt_simplify_sact.
  Qed.

  Lemma interp_sact_eval_sact_iff:
    forall vvs a v (VVSSV: vvs_smaller_variables vvs) t
      (WTS: wt_sact (Sigma := Sigma) R vvs a t),
    interp_sact (sigma := sigma) REnv r vvs a v
    <-> exists fuel, eval_sact vvs a fuel = Some v.
  Proof.
    intros. split; intros.
    - exists (
        Pos.to_nat (Pos.succ (max_var vvs))
        + vvs_size vvs (Pos.succ (max_var vvs))
        + size_sact a
      ). eapply interp_sact_eval_sact; eauto.
    - destruct H. eapply eval_sact_interp_sact; eauto.
  Qed.

  Lemma simplify_vars_wt_sact_ok:
    forall vvs s t (WTS: wt_sact (Sigma := Sigma) R (simplify_vars vvs) s t),
    wt_sact (Sigma := Sigma) R vvs s t.
  Proof.
    intros.
    induction WTS; try (econstructor; eauto; fail).
    unfold simplify_vars in H.
    rewrite Maps.PTree.gmap in H. unfold option_map in H.
    destr_in H. destruct p.
    - apply Some_inj in H. apply pair_inj in H. destruct H. subst.
      econstructor. eauto.
    - easy.
  Qed.

  Lemma simplify_vars_wt_sact_ok':
    forall vvs s t (WTS: wt_sact (Sigma := Sigma) R vvs s t),
    wt_sact (Sigma := Sigma) R (simplify_vars vvs) s t.
  Proof.
    intros.
    induction WTS; econstructor; eauto.
    unfold simplify_vars.
    setoid_rewrite Maps.PTree.gmap.
    unfold option_map. setoid_rewrite H. easy.
  Qed.

  Lemma simplify_vars_get_ok:
    forall vvs x t a (GET: Maps.PTree.get x (simplify_vars vvs) = Some (t, a)),
    exists a', Maps.PTree.get x vvs = Some (t, a').
  Proof.
    intros. unfold simplify_vars in GET.
    rewrite Maps.PTree.gmap in GET. unfold option_map in GET.
    repeat (destr_in GET); inv GET; eauto.
  Qed.

  Lemma simplify_vars_get_ok':
    forall vvs x t a (GET: Maps.PTree.get x vvs = Some (t, a)),
    Maps.PTree.get x (simplify_vars vvs) = Some (t, simplify_sact a).
  Proof.
    intros. unfold simplify_vars.
    rewrite Maps.PTree.gmap. unfold option_map.
    setoid_rewrite GET. eauto.
  Qed.

  Lemma simplify_vars_wtvvs_ok':
    forall vvs (WTVVS: wt_vvs (Sigma := Sigma) R vvs),
    wt_vvs (Sigma := Sigma) R (simplify_vars vvs).
  Proof.
    intros. unfold wt_vvs. intros.
    apply simplify_vars_wt_sact_ok'.
    unfold simplify_vars in H.
    rewrite Maps.PTree.gmap in H. unfold option_map in H.
    destr_in H. destruct p.
    - apply Some_inj in H. apply pair_inj in H. destruct H. subst t0.
      inv H0. apply simplify_sact_wt_sact_ok'; eauto.
    - easy.
  Qed.

  Lemma simplify_sact_reachable_vars_ok:
    forall vvs s v (RV: reachable_var vvs (simplify_sact s) v),
    reachable_var vvs s v.
  Proof.
    intros.
    induction s; simpl in *; eauto.
    - repeat (destr_in RV); eauto;
        try (
          inv RV;
          try (eapply reachable_var_if_cond; eauto; fail);
          try (eapply reachable_var_if_true; eauto; fail);
          try (eapply reachable_var_if_false; eauto; fail);
          fail); subst.
      + eapply IHs2 in RV. eapply reachable_var_if_true; eauto.
      + eapply IHs3 in RV. eapply reachable_var_if_false; eauto.
    - repeat (destr_in RV); econstructor; inv RV; eauto.
    - repeat (destr_in RV);
      try (eapply reachable_var_binop1; eauto; fail);
      try (eapply reachable_var_binop2; eauto; fail);
      try (
        inv RV;
        try (eapply reachable_var_binop1; eauto; fail);
        try (eapply reachable_var_binop2; eauto; fail);
        fail
      );
      subst.
    - inv RV. econstructor. eauto.
  Qed.

  (* TODO simplify_sact_reachable_vars_ok' is false *)

  Lemma simplify_sact_interp_sact_ok':
    forall a v vvs (WTVVS: wt_vvs (Sigma := Sigma) R vvs) t
      (WTS: wt_sact (Sigma := Sigma) R vvs a t)
      (VVSSV: vvs_smaller_variables vvs),
    interp_sact (sigma := sigma) REnv r vvs a v
    -> interp_sact (sigma := sigma) REnv r vvs (simplify_sact a) v.
  Proof.
    intros.
    eapply interp_sact_do_eval_sact in H; eauto.
    unfold do_eval_sact in H.
    eapply eval_sact_interp_sact.
    erewrite simplify_sact_correct; eauto.
  Qed.

  Lemma simplify_sact_var_in_sact_ok':
    forall s v (VIS: var_in_sact (simplify_sact s) v),
    var_in_sact s v.
  Proof.
    intros.
    induction s; try (eauto; fail).
    - simpl in VIS. repeat (destr_in VIS); try (
        inv VIS; try (apply var_in_if_cond; eauto; fail);
        try (apply var_in_if_true; eauto; fail);
        try (apply var_in_if_false; eauto; fail);
        fail).
      + apply var_in_if_true; eauto.
      + apply var_in_if_false; eauto.
    - simpl in VIS. repeat (destr_in VIS);
        (econstructor; eapply IHs; inv VIS; easy).
    - simpl in VIS. destr_in VIS;
      try (
        inv VIS;
        try (apply var_in_sact_binop_1; eauto; fail);
        try (apply var_in_sact_binop_2; eauto; fail);
        fail).
      repeat (destr_in VIS);
        try (apply var_in_sact_binop_1; eauto; fail);
        try (apply var_in_sact_binop_2; eauto; fail);
        try (
          inv VIS; try (apply var_in_sact_binop_1; eauto; fail);
          try (apply var_in_sact_binop_2; eauto; fail); fail).
      repeat (destr_in VIS);
        try (apply var_in_sact_binop_1; eauto; fail);
        try (apply var_in_sact_binop_2; eauto; fail);
        try (
          inv VIS; try (apply var_in_sact_binop_1; eauto; fail);
          try (apply var_in_sact_binop_2; eauto; fail); fail).
      repeat (destr_in VIS);
        try (apply var_in_sact_binop_1; eauto; fail);
        try (apply var_in_sact_binop_2; eauto; fail);
        try (
          inv VIS; try (apply var_in_sact_binop_1; eauto; fail);
          try (apply var_in_sact_binop_2; eauto; fail); fail).
      repeat (destr_in VIS);
        try (apply var_in_sact_binop_1; eauto; fail);
        try (apply var_in_sact_binop_2; eauto; fail);
        try (
          inv VIS; try (apply var_in_sact_binop_1; eauto; fail);
          try (apply var_in_sact_binop_2; eauto; fail); fail).
    - inv VIS. econstructor. eauto.
  Qed.

  Lemma simplify_vars_vvssv_ok':
    forall vvs (VVSSV: vvs_smaller_variables vvs),
    vvs_smaller_variables (simplify_vars vvs).
  Proof.
    intros.
    unfold vvs_smaller_variables in *. intros.
    unfold simplify_vars in H.
    rewrite Maps.PTree.gmap in H. unfold option_map in H.
    destr_in H. destruct p.
    - apply Some_inj in H. apply pair_inj in H. destruct H. subst t0.
      eapply VVSSV; eauto. inv H1.
      apply simplify_sact_var_in_sact_ok'. eauto.
    - easy.
  Qed.

  Lemma replace_reg_in_vars_wt_sact_vvs_ok':
    forall vvs v reg s t (WTV: wt_val (R reg) v)
      (WTVVS: wt_vvs (Sigma := Sigma) R vvs)
      (WTS: wt_sact (Sigma := Sigma) R vvs s t),
    wt_sact (Sigma := Sigma) R (replace_reg_in_vars vvs reg v) s t.
  Proof.
    intros.
    induction WTS; econstructor; eauto.
    setoid_rewrite Maps.PTree.gmap. unfold option_map.
    setoid_rewrite H. easy.
  Qed.

  Lemma wt_vvs_replace_reg_in_vars:
    forall vvs v reg (WTV: wt_val (R reg) v)
      (WTVVS: wt_vvs (Sigma := Sigma) R vvs),
    wt_vvs (Sigma := Sigma) R (replace_reg_in_vars vvs reg v).
  Proof.
    intros.
    unfold wt_vvs. intros.
    setoid_rewrite Maps.PTree.gmap in H. unfold option_map in H.
    unfold wt_vvs in WTVVS.
    repeat destr_in H; inv H.
    apply wt_sact_replace_reg; eauto.
    apply WTVVS in Heqo.
    apply replace_reg_in_vars_wt_sact_vvs_ok'; eauto.
  Qed.

  Lemma vsv_replace_reg_in_vars:
    forall vvs v reg
      (VSV: vvs_smaller_variables vvs),
      vvs_smaller_variables (replace_reg_in_vars vvs reg v).
  Proof.
    intros.
    red. intros.
    setoid_rewrite Maps.PTree.gmap in H. unfold option_map in H.
    repeat destr_in H; inv H.
    apply var_in_replace_reg in H0. eauto.
  Qed.

  Lemma replace_reg_in_vars_ok:
    forall (vvs : var_value_map) (VSV: vvs_smaller_variables vvs)
           (idx : reg_t) (v' : val) v a t (WT: wt_sact R (Sigma:=Sigma) vvs a t)
    (WTVVS: wt_vvs R (Sigma:=Sigma) vvs),
    getenv REnv r idx = v'
    -> interp_sact (sigma := sigma) REnv r (replace_reg_in_vars vvs idx v') a v
    -> interp_sact (sigma := sigma) REnv r vvs a v.
  Proof.
    intros vvs VSV idx v' v a t WT WTVVS H.
    eapply interp_eval.
    eapply vsv_replace_reg_in_vars; eauto.
    auto.
    eapply replace_reg_in_vars_wt_sact_vvs_ok'. subst. apply WTRENV. auto.
    eauto. eauto.
    exists O; intros; symmetry; apply eval_sact_replace_reg_vars. auto.
  Qed.

  Lemma simplify_vars_interp_sact_ok':
    forall vvs a v (WTVVS: wt_vvs (Sigma := Sigma) R vvs)
      (VVSSV: vvs_smaller_variables vvs)
      (EV_INIT: interp_sact (sigma := sigma) REnv r vvs a v),
    interp_sact (sigma := sigma) REnv r (simplify_vars vvs) a v.
  Proof.
    intros.
    induction EV_INIT; try (econstructor; eauto; fail).
    econstructor.
    - unfold simplify_vars. setoid_rewrite Maps.PTree.gmap.
      unfold option_map. setoid_rewrite H.
      f_equal.
    - eapply simplify_sact_interp_sact_ok'; eauto.
      + apply simplify_vars_wtvvs_ok'. eauto.
      + apply simplify_vars_wt_sact_ok'. eauto.
      + apply simplify_vars_vvssv_ok'. eauto.
  Qed.


  Lemma simplify_vars_ok:
    forall
      fuel vvs a res
      (EV_INIT: eval_sact vvs a fuel = Some res)
      (WTVVS: wt_vvs (Sigma := Sigma) R vvs)
      t (WTS: wt_sact (Sigma := Sigma) R vvs a t),
    eval_sact (simplify_vars vvs) a fuel = Some res.
  Proof.
    induction fuel; simpl; intros; eauto.
    Transparent eval_sact.
    destruct a; simpl in *.
    - unfold opt_bind in EV_INIT. repeat destr_in EV_INIT; inv EV_INIT.
      setoid_rewrite PTree.gmap. setoid_rewrite Heqo. simpl.
      erewrite IHfuel. eauto. eapply simplify_sact_correct; eauto. auto.
      eapply wt_simplify_sact; eauto.
    - congruence.
    - unfold opt_bind in EV_INIT. destr_in EV_INIT; inv EV_INIT.
      erewrite IHfuel. 2: eauto. simpl.
      destr_in H0; inv H0.
      destr_in H1; inv H1.
      destr_in H0; inv H0.
      rewrite H1.
      inv WTS.
      destr_in H1; (erewrite IHfuel; eauto).
      auto. inv WTS. eauto.
    - unfold opt_bind in EV_INIT. destr_in EV_INIT; inv EV_INIT.
      inv WTS.
      erewrite IHfuel. 2: eauto. simpl. auto. auto. eauto.
    - unfold opt_bind in EV_INIT. destr_in EV_INIT; inv EV_INIT.
      destr_in H0; inv H0.
      inv WTS.
      erewrite IHfuel; eauto.
      erewrite IHfuel; eauto. simpl. auto.
    - unfold opt_bind in EV_INIT. destr_in EV_INIT; inv EV_INIT.
      inv WTS.
      erewrite IHfuel. 2: eauto. simpl. auto. auto. eauto.
    - auto.
  Qed.

  Lemma simplify_sact_interp_sact_ok:
    forall vvs
           (WTVVS: wt_vvs (Sigma := Sigma) R vvs)
           (VVSSV: vvs_smaller_variables vvs)
           a v
           (EV_INIT: interp_sact (sigma := sigma) REnv r vvs (simplify_sact a) v)
           t (WTS: wt_sact (Sigma := Sigma) R vvs a t),
      interp_sact (sigma := sigma) REnv r vvs a v.
  Proof.
    induction a; simpl; intros; eauto; inv WTS.
    - destr_in EV_INIT.
      exploit eval_sact_no_vars_wt. 2: apply Heqo.
      apply wt_simplify_sact. eauto. intro WT. apply wt_val_bool in WT. destruct WT; subst.
      econstructor. eapply eval_sact_no_vars_interp in Heqo.
      eapply IHa1 in Heqo. eauto. eauto. destr; eauto.
      inv EV_INIT.
      econstructor; eauto.
      destr; eauto.
    - destr_in EV_INIT.
      destr_in EV_INIT.
      + inv EV_INIT.
        econstructor; eauto.
        eapply eval_sact_no_vars_interp in Heqo; eauto.
      + inv EV_INIT.
        econstructor; eauto.
      + inv EV_INIT.
        econstructor; eauto.
    - destruct (eval_sact_no_vars (simplify_sact a1)) eqn:?.
      exploit eval_sact_no_vars_interp. apply Heqo. intro IS1. (* eapply IHa1 in IS1. 2: eauto. *)
      destruct (eval_sact_no_vars (simplify_sact a2)) eqn:?.
      exploit eval_sact_no_vars_interp. apply Heqo0. intro IS2. (* eapply IHa2 in IS2. 2: eauto. *)
      + destr_in EV_INIT.
        destr_in EV_INIT; inv EV_INIT.
        econstructor; eauto.
        econstructor; eauto.
        econstructor; eauto.
        assert (interp_sact (sigma:=sigma) REnv r vvs match sigma2 (PrimUntyped.UBits2 fn) v0 v1 with
                                        | Some r => SConst r
                                        | None => SBinop (PrimUntyped.UBits2 fn) (simplify_sact a1) (simplify_sact a2)
                                        end v ->
                sigma2 (PrimUntyped.UBits2 fn) v0 v1 = Some v
               ).
        clear EV_INIT.
        intros EV.
        destr_in EV. inv EV. auto. inv EV.
        generalize (interp_sact_determ _ _ _ _ _ IS1 _ H3).
        generalize (interp_sact_determ _ _ _ _ _ IS2 _ H7). congruence.
        destr_in EV_INIT; auto.
        simpl.
        inv H5.
        exploit @interp_sact_wt. eauto. eauto. eauto. auto. apply vvs_range_max_var. apply H2. eauto.
        exploit @interp_sact_wt. eauto. eauto. eauto. auto. apply vvs_range_max_var. apply H4. eauto.
        intros WT2 WT1. inv WT2; inv WT1. simpl in *.
        destr_in EV_INIT. destruct bs; [|simpl in H1; lia].
        inv EV_INIT.
        generalize (interp_sact_determ _ _ _ _ _ IS1 _ H6).
        generalize (interp_sact_determ _ _ _ _ _ IS2 _ H8).
        intros. subst. simpl in H9. inv H9. reflexivity.
        destruct bs; [simpl in H1; lia|].
        destruct l, bs; try (simpl in H1; lia).
        subst. simpl in *.
        destr_in EV_INIT. simpl.
        generalize (interp_sact_determ _ _ _ _ _ IS2 _ EV_INIT). congruence. inv EV_INIT. reflexivity.
        assert ( interp_sact (sigma:=sigma) REnv r vvs
                   (SBinop (PrimUntyped.UBits2 PrimUntyped.UAnd) (simplify_sact a1) (simplify_sact a2)) v).
        repeat destr_in EV_INIT; eauto. clear EV_INIT. inv H0.
        generalize (interp_sact_determ _ _ _ _ _ IS1 _ H7).
        generalize (interp_sact_determ _ _ _ _ _ IS2 _ H9). intros; subst.
        simpl in H10. inv H10. simpl. auto.
        simpl.
        inv H5.
        exploit @interp_sact_wt. eauto. eauto. eauto. auto. apply vvs_range_max_var. apply H2. eauto.
        exploit @interp_sact_wt. eauto. eauto. eauto. auto. apply vvs_range_max_var. apply H4. eauto.
        intros WT2 WT1. inv WT2; inv WT1. simpl in *.
        destr_in EV_INIT. destruct bs; [|simpl in H1; lia].
        inv EV_INIT.
        generalize (interp_sact_determ _ _ _ _ _ IS1 _ H6).
        generalize (interp_sact_determ _ _ _ _ _ IS2 _ H8).
        intros. subst. simpl in H9. inv H9. reflexivity.
        destruct bs; [simpl in H1; lia|].
        destruct l, bs; try (simpl in H1; lia).
        subst. simpl in *.
        destr_in EV_INIT. simpl. inv EV_INIT. auto. simpl.
        generalize (interp_sact_determ _ _ _ _ _ IS2 _ EV_INIT). congruence.
        assert ( interp_sact (sigma:=sigma) REnv r vvs
                   (SBinop (PrimUntyped.UBits2 PrimUntyped.UOr) (simplify_sact a1) (simplify_sact a2)) v).
        repeat destr_in EV_INIT; eauto. clear EV_INIT. inv H0.
        generalize (interp_sact_determ _ _ _ _ _ IS1 _ H7).
        generalize (interp_sact_determ _ _ _ _ _ IS2 _ H9). intros; subst.
        simpl in H10. inv H10. simpl. auto.
        destr_in EV_INIT; auto.
        econstructor. eauto. eauto.
        inv EV_INIT. auto.
        inv EV_INIT.
        generalize (interp_sact_determ _ _ _ _ _ IS1 _ H3).
        generalize (interp_sact_determ _ _ _ _ _ IS2 _ H7). intros; subst.
        econstructor; eauto.
        destr_in EV_INIT; auto.
        econstructor. eauto. eauto.
        inv EV_INIT. auto.
        inv EV_INIT.
        generalize (interp_sact_determ _ _ _ _ _ IS1 _ H3).
        generalize (interp_sact_determ _ _ _ _ _ IS2 _ H7). intros; subst.
        econstructor; eauto.
      + destr_in EV_INIT. inv EV_INIT.
        * generalize (interp_sact_determ _ _ _ _ _ IS1 _ H3). intro; subst.
          econstructor; eauto.
        * assert (interp_sact (sigma:=sigma) REnv r vvs (SBinop (PrimUntyped.UBits2 fn) (simplify_sact a1) (simplify_sact a2)) v ->
                  interp_sact (sigma:=sigma) REnv r vvs (SBinop (PrimUntyped.UBits2 fn) a1 a2) v
                 ).
          clear EV_INIT.
          intro IS. inv IS.
          generalize (interp_sact_determ _ _ _ _ _ IS1 _ H3). intro; subst.
          econstructor; eauto.
          repeat destr_in EV_INIT; eauto.
          clear H.
          inv H5. econstructor; eauto.
          exploit @interp_sact_wt. eauto. eauto. eauto. auto. apply vvs_range_max_var. apply H4. eauto.
          intro A; inv A.
          exploit @interp_sact_wt. eauto. eauto. eauto. auto. apply vvs_range_max_var. apply H2. eauto.
          intro A; inv A.
          simpl in H1. destruct bs; simpl in H1; try lia. destruct bs; simpl in H1; try lia.
          simpl. auto.
          clear H.
          inv H5. inv EV_INIT.
          exploit @wt_sact_interp. eauto. eauto. eauto. eauto. apply vvs_range_max_var. apply H4. intros (v2 & IS2 & WT2). inv WT2.
          econstructor; eauto.
          exploit @interp_sact_wt. eauto. eauto. eauto. auto. apply vvs_range_max_var. apply H2. eauto.
          intro A; inv A.
          simpl in H1. destruct bs; simpl in H1; try lia. destruct bs; simpl in H1; try lia.
          simpl. auto.
          clear H.
          inv H5. inv EV_INIT.
          exploit @wt_sact_interp. eauto. eauto. eauto. eauto. apply vvs_range_max_var. apply H4. intros (v2 & IS2 & WT2). inv WT2.
          econstructor; eauto.
          exploit @interp_sact_wt. eauto. eauto. eauto. auto. apply vvs_range_max_var. apply H2. eauto.
          intro A; inv A.
          simpl in H1. destruct bs; simpl in H1; try lia. destruct bs; simpl in H1; try lia.
          simpl. auto.

          clear H.
          inv H5. econstructor; eauto.
          exploit @interp_sact_wt. eauto. eauto. eauto. auto. apply vvs_range_max_var. apply H4. eauto.
          intro A; inv A.
          exploit @interp_sact_wt. eauto. eauto. eauto. auto. apply vvs_range_max_var. apply H2. eauto.
          intro A; inv A.
          simpl in H1. destruct bs; simpl in H1; try lia. destruct bs; simpl in H1; try lia.
          simpl. auto.
        * inv EV_INIT. generalize (interp_sact_determ _ _ _ _ _ IS1 _ H3). intro; subst.
          econstructor; eauto.
        * inv EV_INIT. generalize (interp_sact_determ _ _ _ _ _ IS1 _ H3). intro; subst.
          econstructor; eauto.
      + assert (interp_sact (sigma:=sigma) REnv r vvs (SBinop ufn2 (simplify_sact a1) (simplify_sact a2)) v ->
                interp_sact (sigma:=sigma) REnv r vvs (SBinop ufn2 a1 a2) v
               ).
        {
          clear EV_INIT.
          intro IS. inv IS.
          econstructor; eauto.
        }
        destr_in EV_INIT; auto.
        repeat destr_in EV_INIT; auto; clear H.
        econstructor; eauto.
        eapply IHa2.
        eapply eval_sact_no_vars_interp. eauto. eauto.
        exploit eval_sact_no_vars_wt. 2: apply Heqo0. eapply wt_simplify_sact; eauto.
        exploit @interp_sact_wt. eauto. eauto. eauto. eauto. apply vvs_range_max_var. apply H2. eauto.
        intros WT1 WT2. inv H5. inv WT2. inv WT1.
        destruct bs; simpl in H0; try lia.
        destruct bs; simpl in H0; try lia.
        simpl. rewrite andb_true_r. auto.
        exploit @wt_sact_interp. eauto. eauto. eauto. eauto. apply vvs_range_max_var. apply H2. intros (vv1 & IS1 & WT1).
        econstructor; eauto.
        eapply IHa2.
        eapply eval_sact_no_vars_interp. eauto. eauto.
        exploit eval_sact_no_vars_wt. 2: apply Heqo0. eapply wt_simplify_sact; eauto.
        intros WT2. inv H5. inv WT2. inv WT1.
        destruct bs; simpl in H0; try lia.
        destruct bs; simpl in H0; try lia.
        simpl. rewrite andb_false_r. inv EV_INIT. auto.

        exploit @wt_sact_interp. eauto. eauto. eauto. eauto. apply vvs_range_max_var. apply H2. intros (vv1 & IS1 & WT1).
        econstructor; eauto.
        eapply IHa2.
        eapply eval_sact_no_vars_interp. eauto. eauto.
        exploit eval_sact_no_vars_wt. 2: apply Heqo0. eapply wt_simplify_sact; eauto.
        intros WT2. inv H5. inv WT2. inv WT1.
        destruct bs; simpl in H0; try lia.
        destruct bs; simpl in H0; try lia.
        simpl. rewrite orb_true_r. inv EV_INIT. auto.

        econstructor; eauto.
        eapply IHa2.
        eapply eval_sact_no_vars_interp. eauto. eauto.
        exploit eval_sact_no_vars_wt. 2: apply Heqo0. eapply wt_simplify_sact; eauto.
        exploit @interp_sact_wt. eauto. eauto. eauto. eauto. apply vvs_range_max_var. apply H2. eauto.
        intros WT1 WT2. inv H5. inv WT2. inv WT1.
        destruct bs; simpl in H0; try lia.
        destruct bs; simpl in H0; try lia.
        simpl. rewrite orb_false_r. auto.
    - inv EV_INIT. econstructor; eauto.
  Qed.

  Lemma simplify_vars_interp_sact_ok:
    forall vvs
           (WTVVS: wt_vvs (Sigma := Sigma) R vvs)
           (VVSSV: vvs_smaller_variables vvs)
           a v
           (EV_INIT: interp_sact (sigma := sigma) REnv r (simplify_vars vvs) a v)
           t (WTS: wt_sact (Sigma := Sigma) R vvs a t),
      interp_sact (sigma := sigma) REnv r vvs a v.
  Proof.
    induction 3; simpl; intros; inv WTS.
    - setoid_rewrite PTree.gmap in H. setoid_rewrite H1 in H. simpl in H. inv H.
      econstructor; eauto.
      eapply simplify_sact_interp_sact_ok; eauto.
      eapply IHEV_INIT.
      eapply wt_simplify_sact; eauto.
    - econstructor.
    - econstructor. eauto.
      eapply IHEV_INIT2. destr; eauto.
    - econstructor; eauto.
    - econstructor; eauto.
    - econstructor; eauto.
    - econstructor; eauto.
  Qed.

  Lemma simplify_vars_reachable_var_ok:
    forall vvs v (VVSSV: vvs_smaller_variables vvs) a,
    reachable_var (simplify_vars vvs) a v
    -> reachable_var vvs a v.
  Proof.
    induction 2; simpl; intros; eauto.
    - econstructor.
    - setoid_rewrite PTree.gmap in H. unfold option_map in H.
      repeat destr_in H; inv H.
      econstructor; eauto.
      eapply simplify_sact_reachable_vars_ok. auto.
    - eapply reachable_var_if_cond; eauto.
    - eapply reachable_var_if_true; eauto.
    - eapply reachable_var_if_false; eauto.
    - eapply reachable_var_binop1; eauto.
    - eapply reachable_var_binop2; eauto.
    - eapply reachable_var_unop; eauto.
    - constructor; auto.
  Qed.

  Record wf_sf (sf: simple_form) := {
    wf_sf_wt: wt_vvs (Sigma:=Sigma) R (vars sf);
    wf_sf_vvs: vvs_smaller_variables (vars sf);
    wf_sf_final:
    forall reg k,
      list_assoc (final_values sf) reg = Some k ->
      wt_sact (Sigma:=Sigma) R (vars sf) (SVar k) (R reg)
  }.

  Lemma schedule_to_simple_form_wf:
    forall `{finite: FiniteType reg_t} (rules: rule_name_t -> SimpleForm.uact)
           sched (GS: good_scheduler sched)
           (WTrules: forall r0 : rule_name_t, exists tret : type, wt_daction (R:=R) (Sigma:=Sigma) pos_t string string [] (rules r0) tret)
    ,
      wf_sf (schedule_to_simple_form (pos_t := pos_t) R (Sigma:=Sigma) rules sched).
  Proof.
    intros.
    edestruct (@schedule_to_simple_form_ok) as (WT & VSV & FINAL & FINALWt & FINAL2).
    apply wt_sigma. apply WTRENV. apply GS. reflexivity. apply WTrules.
    apply WTRENV.
    constructor; auto.
    - apply WT.
    - apply VSV.
    - intros. edestruct FINALWt as (n & GET & WTreg).
      rewrite GET in H; inv H. eauto.
  Qed.

  Record sf_eq (sf1 sf2: simple_form) := {
    sf_eq_final: final_values sf1 = final_values sf2;
    sf_eq_vars: forall reg v t,
      In (reg,v) (final_values sf1) ->
      wt_sact (Sigma:=Sigma) R (vars sf1) (SVar v) t ->
      forall x,
        interp_sact REnv (sigma:=sigma) r (vars sf1) (SVar v) x <->
          interp_sact REnv (sigma:=sigma) r (vars sf2) (SVar v) x;
    sf_eq_wt:
      forall reg v t,
      In (reg,v) (final_values sf1) ->
      wt_sact (Sigma:=Sigma) R (vars sf1) (SVar v) t <->
      wt_sact (Sigma:=Sigma) R (vars sf2) (SVar v) t
  }.

  Lemma sf_eq_simplify_sf sf: wf_sf sf -> sf_eq sf (simplify_sf sf).
  Proof.
    unfold simplify_sf. intros. inv H. constructor; auto.
    intros. simpl.
    split; intros.
    eapply simplify_vars_interp_sact_ok'; auto.
    inversion H1. subst.
    unfold simplify_vars in H3. rewrite PTree.gmap in H3.
    unfold option_map in H3. repeat destr_in H3; inv H3.
    eapply simplify_vars_interp_sact_ok; auto.
    econstructor. eauto.
    simpl. intros.
    split. eapply simplify_vars_wt_sact_ok'; eauto.
    eapply simplify_vars_wt_sact_ok; eauto.
  Qed.

  Lemma wf_sf_simplify_sf: forall sf, wf_sf sf -> wf_sf (simplify_sf sf).
  Proof.
    destruct 1; constructor.
    eapply simplify_vars_wtvvs_ok'. auto.
    eapply simplify_vars_vvssv_ok'; eauto.
    simpl. intros.
    eapply wf_sf_final0 in H.
    eapply simplify_vars_wt_sact_ok'. auto.
  Qed.

  Lemma sf_eq_refl: forall sf, sf_eq sf sf.
  Proof. constructor; tauto. Qed.

  Lemma sf_eq_trans:
    forall sf1 sf2,
    sf_eq sf1 sf2
    -> forall sf3, sf_eq sf2 sf3
    -> sf_eq sf1 sf3.
  Proof.
    intros sf1 sf2 EQ1 sf3 EQ2.
    inv EQ1; inv EQ2.
    constructor. congruence.
    intros.
    rewrite sf_eq_vars0. 2: eauto. eapply sf_eq_vars1. rewrite <- sf_eq_final0. eauto.
    eapply sf_eq_wt0. eauto. eauto. eauto.
    intros.
    erewrite sf_eq_wt0. 2: eauto.
    rewrite sf_eq_final0 in H. eauto.
  Qed.

  Lemma sf_eq_sym: forall sf1 sf2, sf_eq sf1 sf2 -> sf_eq sf2 sf1.
  Proof.
    destruct 1; constructor; eauto.
    intros; symmetry; eapply sf_eq_vars0. rewrite sf_eq_final0; eauto.
    rewrite <- sf_eq_final0 in H. rewrite <-sf_eq_wt0 in H0. eauto. eauto.
    intros.
    rewrite <- sf_eq_final0 in H. rewrite <-sf_eq_wt0 . tauto. eauto.
  Qed.

  Lemma sf_eq_remove_vars sf: wf_sf sf -> sf_eq sf (remove_vars sf).
  Proof.
    constructor; auto.
    - intros.
      inversion H1. subst.
      eapply interp_eval_iff. apply H.
      apply vsv_remove_vars; auto. apply H. eauto.
      econstructor.
      simpl. fold (filter_ptree (vars sf) (PTree.empty _) (useful_vars sf)).
      rewrite <- filter_ptree_eq. eapply H3.
      eapply useful_vars_incl. apply H. eauto.
      change v with (snd (reg, v)). apply in_map. eauto.
      apply nodup_useful_vars. apply H.
      intros; rewrite PTree.gempty. auto.
      exists O; intros; eapply remove_vars_correct. apply H.
      change v with (snd (reg, v)). apply in_map. eauto.
    - intros. destruct H. split; intros.
      + inversion H. subst.
        econstructor.
        simpl. fold (filter_ptree (vars sf) (PTree.empty _) (useful_vars sf)).
        rewrite <- filter_ptree_eq. eapply H2.
        eapply useful_vars_incl. eauto. auto.
        change v with (snd (reg, v)). apply in_map. eauto.
        apply nodup_useful_vars. auto.
        intros; rewrite PTree.gempty. auto.
      + inv H.
        unfold remove_vars in H2. simpl in H2.
        fold (filter_ptree (vars sf) (PTree.empty _) (useful_vars sf)) in H2.
        apply filter_ptree_inv in H2. rewrite PTree.gempty in H2.
        destruct H2. congruence.
        destruct H. econstructor; eauto.
        apply nodup_useful_vars. auto.
        intros; rewrite PTree.gempty. auto.
  Qed.

  Instance sf_eq_equi: RelationClasses.Equivalence sf_eq.
  Proof.
    constructor.
    red. apply sf_eq_refl.
    red. apply sf_eq_sym.
    red. intros; eapply sf_eq_trans; eauto.
  Qed.

  Lemma sf_eq_apply_l:
    forall F1 (F1OK: forall sf, wf_sf sf -> sf_eq sf (F1 sf)),
    forall sf1 sf2, wf_sf sf1 -> sf_eq sf1 sf2 -> sf_eq (F1 sf1) sf2.
  Proof. intros. rewrite <- F1OK. auto. auto. Qed.

  Lemma sf_eq_apply:
    forall F1 (F1OK: forall sf, wf_sf sf -> sf_eq sf (F1 sf)),
    forall sf1 sf2,
    wf_sf sf1 -> wf_sf sf2 -> sf_eq sf1 sf2 -> sf_eq (F1 sf1) (F1 sf2).
  Proof. intros. rewrite <- ! F1OK; auto. Qed.

  Record sf_eq_restricted l (sf1 sf2: simple_form) :=
    {
      sf_eqr_final:
      forall reg,
        In reg l ->
        list_assoc (final_values sf1) reg =
          list_assoc (final_values sf2) reg;
      sf_eqr_vars: forall reg v t,
        In reg l ->
        list_assoc (final_values sf2) reg = Some v ->
        wt_sact (Sigma:=Sigma) R (vars sf1) (SVar v) t ->
        forall x,
          interp_sact REnv (sigma:=sigma) r (vars sf1) (SVar v) x <->
            interp_sact REnv (sigma:=sigma) r (vars sf2) (SVar v) x;
      sf_eqr_wt:
      forall reg v t,
        In reg l ->
        list_assoc (final_values sf2) reg = Some v ->
        wt_sact (Sigma:=Sigma) R (vars sf1) (SVar v) t <->
          wt_sact (Sigma:=Sigma) R (vars sf2) (SVar v) t
    }.

  Lemma inlining_pass_sf_eqr':
    forall sf1 sf2 l
           (SFEQ: sf_eq_restricted l sf1 sf2)
           (VSV1: vvs_smaller_variables (vars sf1))
           (VSV2: vvs_smaller_variables (vars sf2))
           (WT1: wt_vvs (Sigma:=Sigma) R (vars sf1))
           (WT2: wt_vvs (Sigma:=Sigma) R (vars sf2))
           (WTfinal: forall reg k,
               list_assoc (final_values sf1) reg = Some k ->
               wt_sact (Sigma:=Sigma) R (vars sf1) (SVar k) (R reg)
           )
           reg k
           (IN: In reg l)
           (FINAL: list_assoc (final_values sf1) reg = Some k),
      list_assoc (inlining_pass sf1) k = list_assoc (inlining_pass sf2) k.
  Proof.
    intros.
    exploit inlining_pass_correct. reflexivity. apply VSV1. apply WT1.
    exploit inlining_pass_correct. reflexivity. apply VSV2. apply WT2.
    intros (ND2 & SPEC2) (ND1 & SPEC1).
    specialize (SPEC2 k reg).
    erewrite <- sf_eqr_final in SPEC2. 2: eauto. 2: auto.
    specialize (SPEC2 FINAL).
    exploit @wt_sact_interp. eauto. eauto. apply WT1. apply VSV1. apply vvs_range_max_var.
    apply WTfinal. eauto.
    intros (v & IS & WT).
    erewrite in_list_assoc. 2: auto. 2: eapply SPEC1; eauto.
    erewrite in_list_assoc. 2: auto. 2: eapply SPEC2; eauto.
    reflexivity.
    rewrite <- sf_eqr_vars; eauto.
    erewrite <- sf_eqr_final; eauto.
  Qed.

  Lemma inlining_pass_sf_eqr:
    forall sf1 sf2 l
           (SFEQ: sf_eq_restricted l sf1 sf2)
           (WF1: wf_sf sf1)
           (WF2: wf_sf sf2)
           reg k (IN: In reg l)
           (FINAL: list_assoc (final_values sf1) reg = Some k),
      list_assoc (inlining_pass sf1) k = list_assoc (inlining_pass sf2) k.
  Proof.
    intros.
    destruct WF1, WF2;
    eapply inlining_pass_sf_eqr'; eauto.
  Qed.

  Lemma sf_eq_is_restricted:
    forall sf1 sf2,
      sf_eq sf1 sf2 ->
      sf_eq_restricted (@finite_elements _ (finite_keys REnv)) sf1 sf2.
  Proof.
    intros.
    inv H. constructor.
    - rewrite sf_eq_final0. tauto.
    (* - intros. elim H. eapply nth_error_In. eapply finite_surjective. *)
    - rewrite <- sf_eq_final0. intros; eapply sf_eq_vars0; eauto.
      eapply list_assoc_in; eauto.
    - rewrite <- sf_eq_final0. intros; eapply sf_eq_wt0; eauto.
      eapply list_assoc_in; eauto.
  Qed.

  Lemma inlining_pass_sf_eq:
    forall sf1 sf2
           (SFEQ: sf_eq sf1 sf2)
           (WF1: wf_sf sf1)
           (WF2: wf_sf sf2)
           reg k
           (FINAL: list_assoc (final_values sf1) reg = Some k),
      list_assoc (inlining_pass sf1) k = list_assoc (inlining_pass sf2) k.
  Proof.
    intros.
    eapply inlining_pass_sf_eqr; eauto. apply sf_eq_is_restricted; auto.
    eapply nth_error_In.
    apply finite_surjective.
  Qed.

  Lemma wf_sf_remove_vars sf: wf_sf sf -> wf_sf (remove_vars sf).
  Proof.
    destruct 1.
    constructor.
    eapply wt_vvs_remove_vars; eauto.
    eapply vsv_remove_vars; eauto.
    intros.
    simpl in H.
    generalize (wf_sf_final0 _ _ H). intro WT. inversion WT; subst.
    simpl. econstructor.
    fold (filter_ptree (vars sf) (PTree.empty _) (useful_vars sf)).
    rewrite <- filter_ptree_eq. eauto. 2: apply nodup_useful_vars. 2: auto.
    2: intros; rewrite PTree.gempty; auto.
    eapply useful_vars_incl. eauto. reflexivity.
    apply list_assoc_in in H.
    apply in_map with (f:=snd) in H. simpl in *; auto.
  Qed.

  Lemma sf_eq_interp_cycle_ok:
    forall reg sf1 sf2,
      wf_sf sf1 -> wf_sf sf2 ->
      sf_eq sf1 sf2 ->
    getenv REnv (interp_cycle sf1) reg
    = getenv REnv (interp_cycle sf2) reg.
  Proof.
    intros.
    unfold interp_cycle. simpl.
    rewrite ! getenv_create.
    erewrite sf_eq_final; eauto.
    destr.
    erewrite inlining_pass_sf_eq. reflexivity.
    apply sf_eq_apply; auto.
    apply sf_eq_remove_vars.
    apply wf_sf_remove_vars; auto.
    apply wf_sf_remove_vars; auto. simpl.
    erewrite sf_eq_final; eauto.
  Qed.

  Lemma simplify_sf_interp_cycle_ok:
    forall reg sf,
    wf_sf sf ->
    getenv REnv (interp_cycle sf) reg
    = getenv REnv (interp_cycle (simplify_sf sf)) reg.
  Proof.
    intros.
    eapply sf_eq_interp_cycle_ok.
    - auto.
    - apply wf_sf_simplify_sf; auto.
    - apply sf_eq_simplify_sf. auto.
  Qed.

  Lemma wt_vvs_f:
    forall f vvs,
      (forall a t,
        wt_sact (Sigma:=Sigma) R vvs a t ->
        wt_sact (Sigma:=Sigma) R (PTree.map (fun _ '(t,a) => (t, f a)) vvs) (f a) t) ->
      wt_vvs (Sigma:=Sigma) R vvs ->
      wt_vvs (Sigma:=Sigma) R (PTree.map (fun _ '(t,a) => (t, f a)) vvs).
  Proof.
    red; intros.
    rewrite PTree.gmap in H1.
    unfold option_map in H1; repeat destr_in H1; inv H1. eauto.
  Qed.

  Lemma f_wt_sact_ok':
    forall f vvs s t (WTS: wt_sact (Sigma := Sigma) R vvs s t),
    wt_sact (Sigma := Sigma) R (PTree.map (fun _ '(t,a) => (t, f a)) vvs) s t.
  Proof.
    intros.
    induction WTS; econstructor; eauto.
    setoid_rewrite Maps.PTree.gmap.
    unfold option_map. setoid_rewrite H. easy.
  Qed.

  Lemma f_wtvvs_ok':
    forall f (FSPEC: forall vvs a t (WTS: wt_sact (Sigma := Sigma) R vvs a t),
               wt_sact (Sigma := Sigma) R vvs (f a) t)
           vvs (WTVVS: wt_vvs (Sigma := Sigma) R vvs),
    wt_vvs (Sigma := Sigma) R (PTree.map (fun _ '(t,a) => (t, f a)) vvs).
  Proof.
    intros. unfold wt_vvs. intros.
    apply f_wt_sact_ok'.
    rewrite Maps.PTree.gmap in H. unfold option_map in H.
    repeat destr_in H; inv H. apply FSPEC; eauto.
  Qed.

  Lemma simplify_sif_wt:
    forall vvs a t (WTS: wt_sact (Sigma := Sigma) R vvs a t),
      wt_sact (Sigma := Sigma) R vvs (simplify_sif a) t.
  Proof.
    induction 1; simpl; intros; try now (econstructor; eauto).
    destr; try (econstructor; eauto).
    exploit eval_sact_no_vars_wt. apply WTS1. eauto. intro A. apply wt_val_bool in A. destruct A. subst.
    destr.
  Qed.

  Lemma vsv_f:
    forall f (FSPEC: forall s v', var_in_sact (f s) v' -> var_in_sact s v')
           vvs,
      vvs_smaller_variables (reg_t:=reg_t) (ext_fn_t:=ext_fn_t) vvs ->
      vvs_smaller_variables (reg_t:=reg_t) (ext_fn_t:=ext_fn_t) (PTree.map (fun _ '(t,a) => (t, f a)) vvs).
  Proof.
    red; intros.
    rewrite Maps.PTree.gmap in H0. unfold option_map in H0.
    repeat destr_in H0; inv H0.
    eapply H in Heqo. apply Heqo. eauto.
  Qed.

  Lemma simplify_sif_vis:
    forall a v' (VIS: var_in_sact (simplify_sif a) v'), var_in_sact a v'.
  Proof.
    induction a; simpl; intros; eauto.
    - repeat destr_in VIS; eauto.
      eapply var_in_if_true; eauto.
      eapply var_in_if_false; eauto.
    - inv VIS; econstructor; eauto.
    - inv VIS. econstructor; eauto.
      eapply var_in_sact_binop_2; eauto.
    - inv VIS; econstructor; eauto.
  Qed.

  Lemma wf_f:
    forall sf f
           (FWT: forall vvs a t (WTS: wt_sact (Sigma := Sigma) R vvs a t),
               wt_sact (Sigma := Sigma) R vvs (f a) t)
           (FVIS: forall s v', var_in_sact (f s) v' -> var_in_sact s v'),
      wf_sf sf ->
      wf_sf {| final_values := final_values sf; vars := PTree.map (fun _ '(t,a) => (t, f a)) (vars sf) |}.
  Proof.
    destruct 3; constructor.
    - eapply f_wtvvs_ok'; eauto.
    - eapply vsv_f; eauto.
    - simpl.
      intros. eapply f_wt_sact_ok'. eauto.
  Qed.

  Lemma wf_simplify_sifs:
    forall sf,
      wf_sf sf ->
      wf_sf (simplify_sifs_sf sf).
  Proof.
    intros; eapply wf_f; eauto.
    eapply simplify_sif_wt.
    eapply simplify_sif_vis.
  Qed.

  Lemma f_interp_sact_ok':
    forall f
           (SPEC: forall (a : SimpleForm.sact) (v : val) (vvs : PTree.t (type * SimpleForm.sact)),
               wt_vvs (Sigma:=Sigma) R vvs ->
               forall t : type,
                 wt_sact (Sigma:=Sigma) R vvs a t ->
                 vvs_smaller_variables vvs ->
                 interp_sact (sigma:=sigma) REnv r vvs a v ->
                 interp_sact (sigma:=sigma) REnv r vvs (f a) v
           )
           (FWT: forall vvs (a0 : SimpleForm.sact) (t0 : type),
               wt_sact (Sigma:=Sigma) R vvs a0 t0 ->
               wt_sact (Sigma:=Sigma) R vvs (f a0) t0)
           (VIS: forall (s : SimpleForm.sact) (v' : positive), var_in_sact (f s) v' -> var_in_sact s v')
           vvs
           (WTVVS: wt_vvs (Sigma := Sigma) R vvs)
           (VVSSV: vvs_smaller_variables vvs)
           a v (EV_INIT: interp_sact (sigma := sigma) REnv r vvs a v)
           t (WTa: wt_sact (Sigma:=Sigma) R vvs a t),
    interp_sact (sigma := sigma) REnv r (PTree.map (fun _ '(t,a) => (t, f a)) vvs) a v.
  Proof.
    intros f SPEC FWT VIS vvs WTVVS VVSSV.
    induction 1; try (econstructor; eauto; fail).
    econstructor.
    - setoid_rewrite Maps.PTree.gmap.
      unfold option_map. setoid_rewrite H.
      f_equal.
    - eapply SPEC; eauto.
      eapply f_wtvvs_ok'; eauto.
      eapply f_wt_sact_ok'; eauto.
      eapply vsv_f; eauto.
    - intros t0 WT; inv WT. econstructor; eauto.
      eapply IHEV_INIT2. destr; eauto.
    - intros t0 WT; inv WT. econstructor; eauto.
    - intros t0 WT; inv WT. econstructor; eauto.
    - intros t0 WT; inv WT. econstructor; eauto.
  Qed.


  Lemma f_interp_sact_ok:
    forall vvs f
           (FSPEC: forall vvs : PTree.t (type * SimpleForm.sact),
               wt_vvs (Sigma:=Sigma) R vvs ->
               vvs_smaller_variables vvs ->
               forall (a : sact) (v : val),
                 interp_sact (sigma:=sigma) REnv r vvs (f a) v ->
                 forall t : type, wt_sact (Sigma:=Sigma) R vvs a t -> interp_sact (sigma:=sigma) REnv r vvs a v
           )
           (FWT: forall vvs (a0 : SimpleForm.sact) (t0 : type),
               wt_sact (Sigma:=Sigma) R vvs a0 t0 ->
               wt_sact (Sigma:=Sigma) R vvs (f a0) t0)
           (WTVVS: wt_vvs (Sigma := Sigma) R vvs)
           (VVSSV: vvs_smaller_variables vvs)
           a v
           (EV_INIT: interp_sact (sigma := sigma) REnv r (PTree.map (fun _ '(t,a) => (t, f a)) vvs) a v)
           t (WTS: wt_sact (Sigma := Sigma) R vvs a t),
      interp_sact (sigma := sigma) REnv r vvs a v.
  Proof.
    induction 5; simpl; intros; inv WTS.
    - setoid_rewrite PTree.gmap in H. setoid_rewrite H1 in H. simpl in H. inv H.
      econstructor; eauto.
      eapply FSPEC; eauto.
    - econstructor.
    - econstructor. eauto.
      eapply IHEV_INIT2. destr; eauto.
    - econstructor; eauto.
    - econstructor; eauto.
    - econstructor; eauto.
    - econstructor; eauto.
  Qed.

  (* Lemma sf_eq_f: *)
  (*   forall sf f (WF: wf_sf sf) *)
  (*          (FSPEC: *)
  (*              forall (a : sact) (v : val), *)
  (*                interp_sact (sigma:=sigma) REnv r (vars sf) (f a) v -> *)
  (*                forall t : type, wt_sact (Sigma:=Sigma) R (vars sf) a t -> *)
  (*                                 interp_sact (sigma:=sigma) REnv r (vars sf) a v *)
  (*          ) *)
  (*          (SPEC: forall (a : SimpleForm.sact) (v : val), *)
  (*              forall t : type, *)
  (*                wt_sact (Sigma:=Sigma) R (vars sf) a t -> *)
  (*                interp_sact (sigma:=sigma) REnv r (vars sf) a v -> *)
  (*                interp_sact (sigma:=sigma) REnv r (vars sf) (f a) v *)
  (*          ) *)
  (*          (FWT: forall (a0 : SimpleForm.sact) (t0 : type), *)
  (*              wt_sact (Sigma:=Sigma) R (vars sf) a0 t0 -> *)
  (*              wt_sact (Sigma:=Sigma) R (vars sf) (f a0) t0) *)
  (*          (VIS: forall (s : SimpleForm.sact) (v' : positive), var_in_sact (f s) v' -> var_in_sact s v') *)
  (*   , *)
  (*     sf_eq sf {| final_values := final_values sf; vars := PTree.map (fun (_ : positive) '(t, a) => (t, f a)) (vars sf) |}. *)
  (* Proof. *)
  (*   intros. *)
  (*   constructor. simpl. auto. *)
  (*   - intros. simpl. *)
  (*     split. *)
  (*     + intro A; inv A. inv H0. rewrite H2 in H4. *)
  (*       inv H4. *)
  (*       econstructor. *)
  (*       rewrite PTree.gmap. setoid_rewrite H2. simpl. reflexivity. *)
  (*       eapply f_interp_sact_ok'. eauto. eauto. eauto. apply H. apply H. eapply SPEC; eauto. *)
  (*       apply H. eapply H. eauto. apply H. *)
  (*       eapply FWT. eapply H. eauto. *)
  (*     + intro A; inv A. rewrite PTree.gmap in H3. unfold option_map in H3; repeat destr_in H3; inv H3. *)
  (*       econstructor. eauto. inv H1. setoid_rewrite H3 in Heqo. inv Heqo. *)
  (*       eapply FSPEC in H4. eapply f_interp_sact_ok; eauto. *)
  (*       apply H. apply H. eapply H. eauto. *)
  (*       eapply f_wtvvs_ok'; eauto. apply H. *)
  (*       eapply vsv_f; eauto. apply H. *)
  (*       eapply f_wt_sact_ok'; eauto. eapply H. eauto. *)
  (*   - intros. simpl. *)
  (*     split. eapply f_wt_sact_ok'; eauto. *)
  (*     intro A; inv A. *)
  (*     rewrite PTree.gmap in H2. unfold option_map in H2; repeat destr_in H2; inv H2. *)
  (*     econstructor. eauto. *)
  (* Qed. *)

  Lemma sf_eq_f:
    forall sf f
           (FSPEC: forall vvs : PTree.t (type * SimpleForm.sact),
               wt_vvs (Sigma:=Sigma) R vvs ->
               vvs_smaller_variables vvs ->
               forall (a : sact) (v : val),
                 interp_sact (sigma:=sigma) REnv r vvs (f a) v ->
                 forall t : type, wt_sact (Sigma:=Sigma) R vvs a t -> interp_sact (sigma:=sigma) REnv r vvs a v
           )
           (SPEC: forall (a : SimpleForm.sact) (v : val) (vvs : PTree.t (type * SimpleForm.sact)),
               wt_vvs (Sigma:=Sigma) R vvs ->
               forall t : type,
                 wt_sact (Sigma:=Sigma) R vvs a t ->
                 vvs_smaller_variables vvs ->
                 interp_sact (sigma:=sigma) REnv r vvs a v ->
                 interp_sact (sigma:=sigma) REnv r vvs (f a) v
           )
           (FWT: forall vvs (a0 : SimpleForm.sact) (t0 : type),
               wt_sact (Sigma:=Sigma) R vvs a0 t0 ->
               wt_sact (Sigma:=Sigma) R vvs (f a0) t0)
           (VIS: forall (s : SimpleForm.sact) (v' : positive), var_in_sact (f s) v' -> var_in_sact s v')
    ,
      wf_sf sf ->
      sf_eq sf {| final_values := final_values sf; vars := PTree.map (fun (_ : positive) '(t, a) => (t, f a)) (vars sf) |}.
  Proof.
    intros.
    constructor. simpl. auto.
    - intros. simpl.
      split.
      + intro A; inv A. inv H1. rewrite H3 in H5.
        inv H5.
        econstructor.
        rewrite PTree.gmap. setoid_rewrite H3. simpl. reflexivity.
        eapply f_interp_sact_ok'. eauto. eauto. eauto. apply H. apply H. eapply SPEC; eauto.
        apply H. eapply H. eauto. apply H.
        eapply FWT. eapply H. eauto.
      + intro A; inv A. rewrite PTree.gmap in H3. unfold option_map in H3; repeat destr_in H3; inv H3.
        econstructor. eauto. inv H1. setoid_rewrite H3 in Heqo. inv Heqo.
        eapply FSPEC in H4. eapply f_interp_sact_ok; eauto.
        apply H. apply H. eapply H. eauto.
        eapply f_wtvvs_ok'; eauto. apply H.
        eapply vsv_f; eauto. apply H.
        eapply f_wt_sact_ok'; eauto. eapply H. eauto.
    - intros. simpl.
      split. eapply f_wt_sact_ok'; eauto.
      intro A; inv A.
      rewrite PTree.gmap in H2. unfold option_map in H2; repeat destr_in H2; inv H2.
      econstructor. eauto.
  Qed.

  Lemma simplify_sif_interp_inv:
    forall vvs : PTree.t (type * SimpleForm.sact),
      wt_vvs (Sigma:=Sigma) R vvs ->
      vvs_smaller_variables vvs ->
      forall (a : sact) (v : val),
        interp_sact (sigma:=sigma) REnv r vvs (simplify_sif a) v ->
        forall t : type, wt_sact (Sigma:=Sigma) R vvs a t -> interp_sact (sigma:=sigma) REnv r vvs a v.
  Proof.
    induction a; simpl; intros; eauto.
    - inv H2.
      destr_in H1; auto.
      exploit eval_sact_no_vars_wt. 2: eauto. eauto. intro A; apply wt_val_bool in A. destruct A. subst.
      econstructor; eauto.
      eapply eval_sact_no_vars_interp; eauto.
    - inv H2; inv H1. econstructor; eauto.
    - inv H2; inv H1. econstructor; eauto.
    - inv H2; inv H1. econstructor; eauto.
  Qed.

  Lemma simplify_sif_interp:
    forall vvs : PTree.t (type * SimpleForm.sact),
      wt_vvs (Sigma:=Sigma) R vvs ->
      vvs_smaller_variables vvs ->
      forall (a : sact) (v : val),
        interp_sact (sigma:=sigma) REnv r vvs a v ->
        forall t : type, wt_sact (Sigma:=Sigma) R vvs a t -> interp_sact (sigma:=sigma) REnv r vvs (simplify_sif a) v.
  Proof.
    induction 3; simpl; intros; try now (econstructor; eauto).
    - inv H1. destr.
      exploit eval_sact_no_vars_wt. 2: eauto. eauto. intro A; apply wt_val_bool in A. destruct A. subst.
      eapply simplify_sif_interp_inv; eauto.
      exploit @interp_sact_determ. apply H1_. eapply eval_sact_no_vars_interp; eauto.
      intro A; inv A.
      eapply IHinterp_sact2. destr; eauto. destr; eauto.
      econstructor; eauto.
    - inv H3. econstructor; eauto.
    - inv H2. econstructor; eauto.
    - inv H2. econstructor; eauto.
  Qed.

  Lemma sf_eq_simplify_sifs:
    forall sf,
      wf_sf sf ->
      sf_eq sf (simplify_sifs_sf sf).
  Proof.
    intros.
    eapply sf_eq_f; eauto.
    - eapply simplify_sif_interp_inv; eauto.
    - intros; eapply simplify_sif_interp; eauto.
    - apply simplify_sif_wt; eauto.
    - eapply simplify_sif_vis.
  Qed.

  Lemma simplify_sifs_sf_interp_cycle_ok:
    forall reg sf,
      wf_sf sf ->
    getenv REnv (interp_cycle (simplify_sifs_sf sf)) reg
    = getenv REnv (interp_cycle sf) reg.
  Proof.
    intros.
    eapply sf_eq_interp_cycle_ok.
    apply wf_simplify_sifs; auto. auto.
    apply sf_eq_sym. apply sf_eq_simplify_sifs. auto.
  Qed.

  Lemma replace_reg_interp_inv:
    forall reg (vvs : PTree.t (type * SimpleForm.sact)),
      wt_vvs (Sigma:=Sigma) R vvs ->
      vvs_smaller_variables vvs ->
      forall (a : sact) (v : val),
        interp_sact (sigma:=sigma) REnv r vvs (replace_reg_in_sact a reg (getenv REnv r reg)) v ->
        forall t : type, wt_sact (Sigma:=Sigma) R vvs a t -> interp_sact (sigma:=sigma) REnv r vvs a v.
  Proof.
    induction a; simpl; intros; eauto.
    - inv H2. inv H1.
      econstructor; eauto.
      destr; eauto.
    - inv H2; inv H1. econstructor; eauto.
    - inv H2; inv H1. econstructor; eauto.
    - inv H2; inv H1. econstructor; eauto.
    - inv H2. destr_in H1. subst. inv H1. econstructor. eauto.
  Qed.

  Lemma replace_reg_interp:
    forall reg (vvs : PTree.t (type * SimpleForm.sact)),
    wt_vvs (Sigma:=Sigma) R vvs
    -> vvs_smaller_variables vvs
    -> forall (a : sact) (v : val),
    interp_sact (sigma:=sigma) REnv r vvs a v
    -> forall t : type,
    wt_sact (Sigma:=Sigma) R vvs a t
    -> interp_sact
        (sigma:=sigma) REnv r vvs
        (replace_reg_in_sact a reg (getenv REnv r reg)) v.
  Proof.
    induction 3; simpl; intros; try now (econstructor; eauto).
    - inv H1. econstructor; eauto. destr; eauto.
    - inv H3. econstructor; eauto.
    - inv H2. econstructor; eauto.
    - inv H2. econstructor; eauto.
    - inv H1. destr; subst; econstructor.
  Qed.

  Lemma replace_reg_wt:
    forall reg vvs a t (WTS: wt_sact (Sigma := Sigma) R vvs a t),
      wt_sact (Sigma := Sigma) R vvs (replace_reg_in_sact a reg (getenv REnv r reg)) t.
  Proof.
    induction 1; simpl; intros; try now (econstructor; eauto).
    destr; try (econstructor; eauto).
    subst. eauto.
  Qed.

  Lemma replace_reg_vis:
    forall
      reg a v'
      (VIS: var_in_sact (replace_reg_in_sact a reg (getenv REnv r reg)) v'),
    var_in_sact a v'.
  Proof.
    induction a; simpl; intros; eauto.
    - inv VIS.
      eapply var_in_if_cond; eauto.
      eapply var_in_if_true; eauto.
      eapply var_in_if_false; eauto.
    - inv VIS; econstructor; eauto.
    - inv VIS. econstructor; eauto.
      eapply var_in_sact_binop_2; eauto.
    - inv VIS; econstructor; eauto.
    - destr_in VIS; inv VIS.
  Qed.

  Lemma wf_sf_replace_reg :
    forall reg val sf,
    getenv REnv r reg = val -> wf_sf sf -> wf_sf (replace_reg sf reg val).
  Proof.
    intros.
    rewrite <- H.
    eapply wf_f.
    - apply replace_reg_wt.
    - apply replace_reg_vis.
    - auto.
  Qed.

  Lemma sf_eq_replace_reg:
    forall reg sf,
    wf_sf sf -> sf_eq sf (replace_reg sf reg (getenv REnv r reg)).
  Proof.
    intros.
    eapply sf_eq_f.
    - eapply replace_reg_interp_inv.
    - intros; eapply replace_reg_interp; eauto.
    - apply replace_reg_wt.
    - apply replace_reg_vis.
    - auto.
  Qed.

  Lemma replace_reg_interp_cycle_ok:
    forall {reg} {sf} {val} (REG_VAL: getenv REnv r reg = val),
    wf_sf sf ->
    getenv REnv (interp_cycle sf) reg
    = getenv REnv (interp_cycle (replace_reg sf reg val)) reg.
  Proof.
    intros.
    eapply sf_eq_interp_cycle_ok.
    - auto.
    - eapply wf_sf_replace_reg in H; eauto.
    - rewrite <- REG_VAL. apply sf_eq_replace_reg. auto.
  Qed.

  Lemma wt_sact_filter:
    forall
      l (ND: NoDup l) vvs (VSV: vvs_smaller_variables vvs) v (IN: In v l) s t
      (GET: vvs ! v = Some (t, s)) (WT: wt_sact (Sigma := Sigma) R vvs s t)
      (REACH: forall v0, reachable_var vvs s v0 -> In v0 l),
    wt_sact (Sigma := Sigma) R (filter_ptree vvs (PTree.empty _) l) s t.
  Proof.
    intros.
    assert (forall v0, reachable_var vvs (SVar v) v0 -> In v0 l).
    {
      intros v0 RV. inv RV. auto.
      rewrite GET in H0; inv H0. eauto.
    }
    specialize (fun v REACH vvs t2 => filter_ptree_eq _ _ vvs t2 (H v REACH) ND).
    simpl.
    fold (filter_ptree vvs (PTree.empty _) l).
    intros. eapply wt_sact_reachable. 2: eauto.
    intros; apply H0. econstructor; eauto.
    intros; apply PTree.gempty.
  Qed.

  Lemma wt_vvs_filter:
    forall vvs l (ND: NoDup l) (VSV: vvs_smaller_variables vvs),
    wt_vvs (Sigma := Sigma) R vvs
    -> (
      forall
        v t s (IN : In v l) (GET : vvs ! v = Some (t, s)) v0
        (REACH: reachable_var vvs s v0), In v0 l
    )
    -> wt_vvs (Sigma:=Sigma) R (filter_ptree vvs (PTree.empty _) l).
  Proof.
    red; intros vvs l ND VSV WTVVS CLOSED v s t GET.
    apply filter_ptree_inv in GET; auto. rewrite PTree.gempty in GET.
    destruct GET as [GET|(IN & GET)]. inv GET.
    eapply wt_sact_filter; eauto.
    intros; apply PTree.gempty.
  Qed.

  Lemma vsv_filter:
    forall vvs l (ND: NoDup l),
    vvs_smaller_variables vvs
    -> vvs_smaller_variables (filter_ptree vvs (PTree.empty _) l).
  Proof.
    red; intros.
    simpl in *.
    apply filter_ptree_inv in H0.
    destruct H0.
    rewrite PTree.gempty in H0. congruence.
    destruct H0 as (IN & GET).
    eapply H; eauto. auto.
    intros; apply PTree.gempty.
  Qed.

  Lemma wf_sf_filter_ptree sf1 sf2 l
    (ND: NoDup l)
    (CLOSED:
      forall
        v t s (IN : In v l) (GET : (vars sf1) ! v = Some (t, s)) v0
        (REACH: reachable_var (vars sf1) s v0),
        In v0 l
    )
  :
    wf_sf sf1 ->
    (forall r k,
      list_assoc (final_values sf2) r = Some k
      -> list_assoc (final_values sf1) r = Some k /\ In k l
    )
    -> vars sf2 = filter_ptree (vars sf1) (PTree.empty _) l
    -> wf_sf sf2.
  Proof.
    destruct 1; intros.
    constructor.
    - rewrite H0. eapply wt_vvs_filter; eauto.
    - rewrite H0. apply vsv_filter; auto.
    - intros.
      apply H in H1. destruct H1.
      apply wf_sf_final0 in H1. inv H1.
      econstructor.
      rewrite H0.
      erewrite <- filter_ptree_eq. eauto. auto. auto.
      intros; rewrite PTree.gempty; auto.
  Qed.

  Lemma wf_sf_prune_irrelevant_aux:
    forall sf reg v,
    list_assoc (final_values sf) reg = Some v
    -> wf_sf sf
    -> wf_sf (prune_irrelevant_aux sf reg v).
  Proof.
    intros.
    eapply wf_sf_filter_ptree. 5: reflexivity.
    eapply nodup_reachable_vars_aux. apply H0. constructor.
    intros; eapply reachable_vars_aux_ok. 2: reflexivity. apply H0. simpl; easy.
    lia. eauto. eauto. eauto. auto.
    simpl. intros. destr_in H1; inv H1. rewrite H. split; auto.
  Qed.

  Lemma filter_ptree_correct:
    forall sf1 sf2 l lr (ND: NoDup l)
    (CLOSED:
      forall
        v t s (IN : In v l) (GET : (vars sf1) ! v = Some (t, s)) v0
        (REACH: reachable_var (vars sf1) s v0), In v0 l
    ),
    wf_sf sf1 ->
    (forall reg v,
        In reg lr ->
        list_assoc (final_values sf1) reg = Some v ->
        list_assoc (final_values sf2) reg = Some v) ->
    (forall r k,
        list_assoc (final_values sf2) r = Some k ->
        list_assoc (final_values sf1) r = Some k /\ In k l) ->
    vars sf2 = filter_ptree (vars sf1) (PTree.empty _) l ->
    forall reg n,
      list_assoc (final_values sf2) reg = Some n
      -> forall fuel,
        eval_sact (vars sf1) (SVar n) fuel = eval_sact (vars sf2) (SVar n) fuel.
  Proof.
    intros. simpl.
    assert (forall v, reachable_var (vars sf1) (SVar n) v -> In v l).
    {
      intros v RV. inv RV. eapply H1; eauto.
      eapply CLOSED; eauto. eapply H1; eauto.
    }
    assert (
      forall l v (vvs t2: var_value_map (ext_fn_t:=ext_fn_t) (reg_t:=reg_t)),
      In v l
      -> NoDup l
      -> (forall x, In x l -> t2 ! x = None)
      -> vvs ! v = (filter_ptree vvs t2 l) ! v
    ).
    {
      clear.
      induction l; simpl; intros. easy.
      inv H0. destruct H. subst.
      destr.
      rewrite filter_ptree_in. rewrite PTree.gss. auto. auto.
      rewrite filter_ptree_in; auto. symmetry; apply H1. auto.
      rewrite <- IHl. auto. auto. auto. intros.
      destr; eauto. rewrite PTree.gso; eauto. congruence.
    }

    specialize (fun v REACH vvs t2 => H5 _ _ vvs t2 (H4 v REACH) ND).
    rewrite H2.
    apply eval_sact_reachable. intros; apply H5. auto. intros; apply PTree.gempty.
  Qed.

  Lemma reachable_filter_inv:
    forall vvs l (ND: NoDup l) v a,
    reachable_var
      (filter_ptree vvs (PTree.empty (type * SimpleForm.sact)) l) a v
    -> reachable_var vvs a v.
  Proof.
    induction 2; simpl; intros; eauto.
    - econstructor.
    - apply filter_ptree_inv in H; auto. rewrite PTree.gempty in H.
      destruct H as [H|[A B]]; [congruence|]. econstructor; eauto.
      intros; apply PTree.gempty.
    - eapply reachable_var_if_cond; eauto.
    - eapply reachable_var_if_true; eauto.
    - eapply reachable_var_if_false; eauto.
    - eapply reachable_var_binop1; eauto.
    - eapply reachable_var_binop2; eauto.
    - eapply reachable_var_unop; eauto.
    - eapply reachable_var_externalCall; eauto.
  Qed.

  Lemma filter_ptree_wt:
    forall
      sf1 sf2 l lr (ND: NoDup l)
      (CLOSED:
        forall
          v t s (IN : In v l) (GET : (vars sf1) ! v = Some (t, s)) v0
          (REACH: reachable_var (vars sf1) s v0), In v0 l),
    wf_sf sf1 ->
    (forall reg v,
        In reg lr ->
        list_assoc (final_values sf1) reg = Some v ->
        list_assoc (final_values sf2) reg = Some v) ->
    (forall r k,
        list_assoc (final_values sf2) r = Some k ->
        list_assoc (final_values sf1) r = Some k /\ In k l) ->
    vars sf2 = filter_ptree (vars sf1) (PTree.empty _) l ->
    forall reg n t,
      list_assoc (final_values sf2) reg = Some n
      ->
        wt_sact (Sigma:=Sigma) R (vars sf1) (SVar n) t <-> wt_sact (Sigma:=Sigma) R (vars sf2) (SVar n) t.
  Proof.
    intros. simpl.
    assert (forall v, reachable_var (vars sf1) (SVar n) v -> In v l).
    {
      intros v RV. inv RV. eapply H1; eauto.
      eapply CLOSED; eauto. eapply H1; eauto.
    }
    assert (
      forall l v (vvs t2: var_value_map (ext_fn_t:=ext_fn_t) (reg_t:=reg_t)),
      In v l
      -> NoDup l
      -> (forall x, In x l -> t2 ! x = None)
      -> vvs ! v = (filter_ptree vvs t2 l) ! v
    ).
    {
      clear.
      induction l; simpl; intros. easy.
      inv H0. destruct H. subst.
      destr.
      rewrite filter_ptree_in. rewrite PTree.gss. auto. auto.
      rewrite filter_ptree_in; auto. symmetry; apply H1. auto.
      rewrite <- IHl. auto. auto. auto. intros.
      destr; eauto. rewrite PTree.gso; eauto. congruence.
    }

    split; eapply wt_sact_reachable.
    rewrite H2. intros. eapply filter_ptree_eq; eauto.
    intros; apply PTree.gempty.
    rewrite H2. intros. symmetry; eapply filter_ptree_eq; eauto.
    2: intros; apply PTree.gempty.
    inv H6. eapply H1; eauto.
    eapply CLOSED; eauto. 3: eapply reachable_filter_inv; eauto.
    eapply H1; eauto.
    eapply filter_ptree_inv in H8.
    rewrite PTree.gempty in H8. destruct H8 as [|[A B]]. inv H6. eauto. auto.
    intros; apply PTree.gempty.
  Qed.

  Lemma sf_eqr_filter sf1 sf2 lr l
    (ND: NoDup l)
    (CLOSED: forall v t s
                    (IN : In v l)
                    (GET : (vars sf1) ! v = Some (t, s))
                    v0
                    (REACH: reachable_var (vars sf1) s v0), In v0 l):
    wf_sf sf1 ->
    (forall reg,
        In reg lr ->
        list_assoc (final_values sf1) reg =
        list_assoc (final_values sf2) reg) ->
    (forall r k,
        list_assoc (final_values sf2) r = Some k ->
        list_assoc (final_values sf1) r = Some k /\ In k l) ->
    vars sf2 = filter_ptree (vars sf1) (PTree.empty _) l ->
    sf_eq_restricted lr sf1 sf2.
  Proof.
    intros WF SELECT1 SELECT2 VARS. constructor; auto.
    - intros. inversion H1. subst.
      eapply interp_eval_iff. apply WF.
      rewrite VARS. apply vsv_filter; auto. apply WF. eauto.
      econstructor.
      rewrite VARS.
      rewrite <- filter_ptree_eq. eauto.  eapply SELECT2.  eauto. auto.
      intros; rewrite PTree.gempty. auto.
      exists O; intros; eapply filter_ptree_correct; eauto.
      intros. rewrite <- SELECT1. eauto. eauto.
    - intros; eapply filter_ptree_wt; eauto.
      intros. rewrite <- SELECT1. eauto. eauto.
  Qed.

  Lemma sf_eqf_prune_irrelevant_aux:
    forall sf reg v,
      list_assoc (final_values sf) reg = Some v ->
      wf_sf sf ->
      sf_eq_restricted [reg] sf (prune_irrelevant_aux sf reg v).
  Proof.
    intros. eapply sf_eqr_filter. 6: reflexivity.
    apply nodup_reachable_vars_aux. apply H0. constructor.
    intros; eapply reachable_vars_aux_ok; eauto. apply H0. reflexivity.
    easy. auto.
    simpl. intros ? [|[]]. subst.
    destr.
    (* simpl. intros. destr. subst. intuition congruence. *)
    simpl. intros. repeat destr_in H1; inv H1. split; auto.
  Qed.

  Lemma sf_eqr_apply:
    forall F1 l1 l2
           (F1OK: forall sf, wf_sf sf -> sf_eq_restricted l1 sf (F1 sf))
           (* (F1removes: forall sf reg, ~ In reg l1 -> list_assoc (final_values (F1 sf)) reg = None) *),
      forall sf1 sf2,
        wf_sf sf1 -> wf_sf sf2 ->
        sf_eq_restricted l2 sf1 sf2 ->
        forall l3, incl l3 l1 -> incl l3 l2 ->
        sf_eq_restricted l3 (F1 sf1) (F1 sf2).
  Proof.
    intros.
    destruct (F1OK _ H), (F1OK _ H0), H1.
    constructor.
    - intros; eauto.
      rewrite <- sf_eqr_final0; auto.
      rewrite <- sf_eqr_final1; auto.
    (* - intros. rewrite sf_eqr_notin1. auto. *)
    (*   intro IN; apply H1; eauto. *)
    - intros.
      rewrite <- sf_eqr_vars0; eauto.
      rewrite <- sf_eqr_vars1; eauto. eapply sf_eqr_vars2; eauto.
      erewrite sf_eqr_final1; eauto.
      eapply sf_eqr_wt0; eauto.
      rewrite <- sf_eqr_final0; eauto.
      rewrite sf_eqr_final2; eauto.
      rewrite sf_eqr_final1; eauto. eauto.
      eapply sf_eqr_wt2; eauto.
      rewrite sf_eqr_final1; eauto.
      eapply sf_eqr_wt0; eauto.
      rewrite <- sf_eqr_final0; eauto.
      rewrite sf_eqr_final2; eauto.
      rewrite sf_eqr_final1; eauto.
      eauto.
      rewrite <- sf_eqr_final0; eauto.
      rewrite sf_eqr_final2; eauto.
      rewrite sf_eqr_final1; eauto.
      eapply sf_eqr_wt0; eauto.
      rewrite <- sf_eqr_final0; eauto.
      rewrite sf_eqr_final2; eauto.
      rewrite sf_eqr_final1; eauto.
    - intros.
      rewrite <- sf_eqr_wt0; eauto.
      rewrite <- sf_eqr_wt1; eauto.
      eapply sf_eqr_wt2; eauto.
      rewrite sf_eqr_final1; eauto.
      rewrite <- sf_eqr_final0; eauto.
      rewrite sf_eqr_final2; eauto.
      rewrite sf_eqr_final1; eauto.
  Qed.

  Lemma sf_eqr_apply':
    forall F1 l (F1OK: forall sf, wf_sf sf -> sf_eq_restricted l sf (F1 sf)),
      forall sf1 sf2,
        wf_sf sf1 -> wf_sf sf2 ->
        sf_eq_restricted l sf1 sf2 ->
        sf_eq_restricted l (F1 sf1) (F1 sf2).
  Proof.
    intros.
    eapply sf_eqr_apply; eauto.
    red; auto. red; auto.
  Qed.

  Lemma sf_eqr_incl:
    forall l1 l2 sf1 sf2,
      sf_eq_restricted l1 sf1 sf2 ->
      incl l2 l1 ->
      sf_eq_restricted l2 sf1 sf2.
  Proof.
    intros. inv H.
    constructor; eauto.
  Qed.

  Lemma sf_eqr_interp_cycle_ok:
    forall l sf1 sf2,
      wf_sf sf1 -> wf_sf sf2 ->
      sf_eq_restricted l sf1 sf2 ->
      forall reg, In reg l ->
    getenv REnv (interp_cycle sf1) reg
    = getenv REnv (interp_cycle sf2) reg.
  Proof.
    intros.
    unfold interp_cycle. simpl.
    rewrite ! getenv_create.
    erewrite sf_eqr_final; eauto.
    destr.
    erewrite inlining_pass_sf_eqr. reflexivity. 4: apply H2.
    2: apply wf_sf_remove_vars; eauto.
    2: apply wf_sf_remove_vars; eauto.
    eapply sf_eqr_apply; eauto.
    intros; eapply sf_eq_is_restricted.
    apply sf_eq_remove_vars. auto. red; intros.
    eapply nth_error_In, finite_surjective.
    red; auto. simpl.
    erewrite sf_eqr_final; eauto.
  Qed.

  Lemma prune_irrelevant_interp_cycle_ok:
    forall
      reg sf sf' (WF: wf_sf sf) (PRUNE: prune_irrelevant sf reg = Some sf'),
    getenv REnv (interp_cycle sf) reg = getenv REnv (interp_cycle sf') reg.
  Proof.
    intros.
    unfold prune_irrelevant in PRUNE. destr_in PRUNE; inv PRUNE.
    eapply sf_eqr_interp_cycle_ok.
    - auto.
    - eapply wf_sf_prune_irrelevant_aux; eauto.
    - eapply sf_eqf_prune_irrelevant_aux; eauto.
    - simpl; auto.
  Qed.

  Fixpoint collapse_sact (vvs : PTree.t (type * SimpleForm.sact (ext_fn_t:=ext_fn_t)(reg_t:=reg_t))) (a : sact) :=
    match a with
    | SIf cond tb fb =>
      SIf (collapse_sact vvs cond) (collapse_sact vvs tb) (collapse_sact vvs fb)
    | SBinop ufn a1 a2 => SBinop ufn (collapse_sact vvs a1) (collapse_sact vvs a2)
    | SUnop ufn a => SUnop ufn (collapse_sact vvs a)
    | SVar v =>
      match PTree.get v vvs with
      | Some (t, SVar v') => SVar v'
        (* collapse vvs (Var v') *) (* TODO Termination *)
      | Some (t, SConst c) => SConst c
      | _ => a
      end
    | SExternalCall ufn s => SExternalCall ufn (collapse_sact vvs s)
    | _ => a
    end.

  Definition collapse_sf (sf: simple_form) := {|
    final_values := final_values sf;
    vars :=
      Maps.PTree.map (fun _ '(t, a) => (t, collapse_sact (vars sf) a)) (vars sf) |}.

  Lemma collapse_wt:
    forall sf (WF: wf_sf sf) a t (WTS: wt_sact (Sigma := Sigma) R (vars sf) a t),
      wt_sact (Sigma := Sigma) R (vars sf) (collapse_sact (vars sf) a) t.
  Proof.
    induction 2; simpl; intros; try now (econstructor; eauto).
    rewrite H.
    destr; try now (econstructor; eauto).
    eapply wf_sf_wt; eauto.
    eapply wf_sf_wt; eauto.
  Qed.

  Lemma vsv_f_reachable:
    forall f vvs (FSPEC: forall s v', var_in_sact (f s) v' -> reachable_var vvs s v'),
      vvs_smaller_variables (reg_t:=reg_t) (ext_fn_t:=ext_fn_t) vvs ->
      vvs_smaller_variables (reg_t:=reg_t) (ext_fn_t:=ext_fn_t) (PTree.map (fun _ '(t,a) => (t, f a)) vvs).
  Proof.
    red; intros.
    rewrite Maps.PTree.gmap in H0. unfold option_map in H0.
    repeat destr_in H0; inv H0.
    eapply FSPEC in H1.
    eapply reachable_var_aux_below. 3: eauto. auto.
    intros; eapply H; eauto.
  Qed.

  Lemma f_wtvvs_ok'':
    forall f vvs (FSPEC: forall a t (WTS: wt_sact (Sigma := Sigma) R vvs a t),
               wt_sact (Sigma := Sigma) R vvs (f a) t)
           (WTVVS: wt_vvs (Sigma := Sigma) R vvs),
    wt_vvs (Sigma := Sigma) R (PTree.map (fun _ '(t,a) => (t, f a)) vvs).
  Proof.
    intros. unfold wt_vvs. intros.
    apply f_wt_sact_ok'.
    rewrite Maps.PTree.gmap in H. unfold option_map in H.
    repeat destr_in H; inv H. apply FSPEC; eauto.
  Qed.

  Lemma wf_f_reachable:
    forall sf f
           (FWT: forall a t (WTS: wt_sact (Sigma := Sigma) R (vars sf) a t),
               wt_sact (Sigma := Sigma) R (vars sf) (f a) t)
           (FVIS: forall s v', var_in_sact (f s) v' -> reachable_var (vars sf) s v'),
      wf_sf sf ->
      wf_sf {| final_values := final_values sf; vars := PTree.map (fun _ '(t,a) => (t, f a)) (vars sf) |}.
  Proof.
    destruct 3; constructor.
    - eapply f_wtvvs_ok''; eauto.
    - eapply vsv_f_reachable; eauto.
    - simpl.
      intros. eapply f_wt_sact_ok'. eauto.
  Qed.

  Lemma var_in_sact_reachable:
    forall vvs a v,
      var_in_sact a v ->
      reachable_var vvs a v.
  Proof.
    induction 1; simpl; intros; try now (econstructor; eauto).
  Qed.

  Lemma collapse_vis:
    forall vvs a v' (VIS: var_in_sact (collapse_sact vvs a) v'), reachable_var vvs a v'.
  Proof.
    induction a; simpl; intros; eauto; try now (inv VIS).
    -
      specialize (var_in_sact_reachable vvs (SVar var) v'). intros.
      repeat destr_in VIS; auto; clear H.
      subst.
      inv VIS. econstructor; eauto. econstructor; eauto. inv VIS.
    - inv VIS.
      eapply reachable_var_if_cond; eauto.
      eapply reachable_var_if_true; eauto.
      eapply reachable_var_if_false; eauto.
    - inv VIS; econstructor; eauto.
    - inv VIS. econstructor; eauto.
      eapply reachable_var_binop2; eauto.
    - inv VIS; econstructor; eauto.
  Qed.

  Lemma wf_collapse_sf: forall sf, wf_sf sf -> wf_sf (collapse_sf sf).
  Proof.
    intros; eapply wf_f_reachable.
    intros; eapply collapse_wt; eauto.
    intros; eapply collapse_vis; eauto. auto.
  Qed.

  Lemma collapse_interp_inv:
    forall vvs,
      wt_vvs (Sigma:=Sigma) R vvs ->
      vvs_smaller_variables vvs ->
      forall (a : sact) (v : val),
        interp_sact (sigma:=sigma) REnv r vvs (collapse_sact vvs a) v ->
        forall t : type, wt_sact (Sigma:=Sigma) R vvs a t -> interp_sact (sigma:=sigma) REnv r vvs a v.
  Proof.
    induction a; simpl; intros; eauto.
    - inv H2.
      rewrite H4 in H1.
      destr_in H1; auto. econstructor; eauto. econstructor; eauto.
    - inv H2; inv H1. econstructor; eauto. destr; eauto.
    - inv H2; inv H1. econstructor; eauto.
    - inv H2; inv H1. econstructor; eauto.
    - inv H2; inv H1. econstructor; eauto.
  Qed.

  Lemma pos_strong_ind:
    forall (P: positive -> Prop),
      (forall p, (forall n, Pos.lt n p -> P n) -> P p) ->
      forall n m, Pos.le m n -> P m.
  Proof.
    intros.
    generalize (strong_ind_type (fun n => P (Pos.of_nat (S n)))). intro.
    replace m with (Pos.of_nat (S (pred (Pos.to_nat m)))).
    eapply H1.
    intros. apply H.
    intros.
    assert (n1 = Pos.of_nat (S (pred (Pos.to_nat n1)))).
    erewrite Nat.lt_succ_pred. rewrite Pnat.Pos2Nat.id. auto. instantiate (1:=0); lia. rewrite H4.
    apply H2. lia.
    instantiate (1:=pred (Pos.to_nat n)). lia.
    erewrite Nat.lt_succ_pred. rewrite Pnat.Pos2Nat.id. auto. instantiate (1:=0); lia.
  Qed.

  Lemma collapse_interp2:
    forall vvs,
      wt_vvs (Sigma:=Sigma) R vvs
    -> vvs_smaller_variables vvs
    -> forall n a v,
        (forall v, reachable_var vvs a v -> v < n)%positive ->
        interp_sact (sigma:=sigma) REnv r vvs a v ->
        forall t : type, wt_sact (Sigma:=Sigma) R vvs a t ->
                         interp_sact (sigma:=sigma) REnv r (PTree.map (fun _ '(t,a) => (t, collapse_sact vvs a)) vvs) (collapse_sact vvs a) v.
  Proof.
    intros vvs WTvvs VSV n a.
    change n with (projT1 (existT (fun _ => sact) n a)).
    change a with (projT2 (existT (fun _ => sact) n a)) at 1 3 4 5.
    generalize (existT (fun _ => sact) n a).
    clear n a. intro s. pattern s.
    eapply well_founded_induction.
    apply wf_order_sact. clear s.
    intros x IH v BELOW IS t0 WTs.
    assert (IH2: forall a0,
               size_sact a0 < size_sact (projT2 x) ->
               (forall v0, reachable_var vvs a0 v0 -> (v0 < projT1 x)%positive) ->
               forall v t,
                 interp_sact (sigma:=sigma) REnv r vvs a0 v ->
                 wt_sact (Sigma:=Sigma) R vvs a0 t ->
                 interp_sact (sigma:=sigma) REnv r (PTree.map (fun _ '(t,a) => (t, collapse_sact vvs a)) vvs) (collapse_sact vvs a0) v
           ).
    {
      intros. eapply (IH (existT _ (projT1 x) a0)).
      red. destruct x. apply Relation_Operators.right_lex. simpl in H.  auto.
      simpl. auto. simpl. auto. simpl. eauto.
    }
    destruct x; simpl in *.
    inv IS.
    - simpl in *. rewrite H.
      destr.
      + inv H0. econstructor.
        rewrite PTree.gmap; setoid_rewrite H2. reflexivity.
        eapply (IH (existT _ var a0)).
        red. apply Relation_Operators.left_lex. apply BELOW. constructor.
        simpl.
        generalize (reachable_var_aux_below_get _ VSV _ _ _ H). intros.
        eapply H0. econstructor; eauto. simpl. auto.
        simpl. eauto.
      + inv H0; econstructor; eauto.
      + econstructor.
        rewrite PTree.gmap; setoid_rewrite H. reflexivity.
        simpl.
        inv H0.
        generalize (WTvvs _ _ _ H). intro WT. inv WT.
        econstructor.
        eapply (IH (existT _ var s1)).
        red. apply Relation_Operators.left_lex. apply BELOW. constructor.
        simpl.
        generalize (reachable_var_aux_below_get _ VSV _ _ _ H). intros.
        eapply H0. econstructor; eauto. simpl. eauto.
        simpl. eauto.
        destr.
        eapply (IH (existT _ var s2)).
        red. apply Relation_Operators.left_lex. apply BELOW. constructor.
        simpl.
        generalize (reachable_var_aux_below_get _ VSV _ _ _ H). intros.
        eapply H0. eapply reachable_var_if_true; eauto. simpl. eauto.
        simpl. eauto.
        eapply (IH (existT _ var s3)).
        red. apply Relation_Operators.left_lex. apply BELOW. constructor.
        simpl.
        generalize (reachable_var_aux_below_get _ VSV _ _ _ H). intros.
        eapply H0. eapply reachable_var_if_false; eauto. simpl. eauto.
        simpl. eauto.
      + econstructor.
        rewrite PTree.gmap; setoid_rewrite H. reflexivity.
        simpl.
        inv H0.
        generalize (WTvvs _ _ _ H). intro WT. inv WT.
        econstructor.
        eapply (IH (existT _ var s)).
        red. apply Relation_Operators.left_lex. apply BELOW. constructor.
        simpl.
        generalize (reachable_var_aux_below_get _ VSV _ _ _ H). intros.
        eapply H0. econstructor; eauto. simpl. eauto.
        simpl. eauto. auto.
      + econstructor.
        rewrite PTree.gmap; setoid_rewrite H. reflexivity.
        simpl.
        inv H0.
        generalize (WTvvs _ _ _ H). intro WT. inv WT.
        econstructor.
        eapply (IH (existT _ var s1)).
        red. apply Relation_Operators.left_lex. apply BELOW. constructor.
        simpl.
        generalize (reachable_var_aux_below_get _ VSV _ _ _ H). intros.
        eapply H0. eapply reachable_var_binop1; eauto. simpl. eauto.
        simpl. eauto. auto.
        simpl. eapply (IH (existT _ var s2)).
        red. apply Relation_Operators.left_lex. apply BELOW. constructor.
        simpl.
        generalize (reachable_var_aux_below_get _ VSV _ _ _ H). intros.
        eapply H0. eapply reachable_var_binop2; eauto. simpl. eauto.
        simpl. eauto. auto.
      + econstructor.
        rewrite PTree.gmap; setoid_rewrite H. reflexivity.
        simpl.
        inv H0.
        generalize (WTvvs _ _ _ H). intro WT. inv WT.
        econstructor.
        eapply (IH (existT _ var s)).
        red. apply Relation_Operators.left_lex. apply BELOW. constructor.
        simpl.
        generalize (reachable_var_aux_below_get _ VSV _ _ _ H). intros.
        eapply H0. eapply reachable_var_externalCall; eauto. simpl. eauto.
        simpl. eauto.
      + econstructor.
        rewrite PTree.gmap; setoid_rewrite H. reflexivity.
        simpl.
        inv H0.
        generalize (WTvvs _ _ _ H). intro WT. inv WT.
        econstructor.
    - simpl; constructor.
    - simpl.
      inv WTs.
      econstructor.
      eapply IH2. Transparent size_sact. simpl. lia.
      intros; eapply BELOW. eapply reachable_var_if_cond. eauto. eauto. eauto.
      destr.
      eapply IH2. simpl. lia.
      intros; eapply BELOW. eapply reachable_var_if_true. eauto. eauto. eauto.
      eapply IH2. simpl. lia.
      intros; eapply BELOW. eapply reachable_var_if_false. eauto. eauto. eauto.
    - simpl.
      inv WTs.
      econstructor.
      eapply IH2. simpl. lia.
      intros; eapply BELOW. eapply reachable_var_unop. eauto. eauto. eauto. auto.
    - simpl.
      inv WTs.
      econstructor.
      eapply IH2. simpl. lia.
      intros; eapply BELOW. eapply reachable_var_binop1. eauto. eauto. eauto. auto.
      eapply IH2. simpl. lia.
      intros; eapply BELOW. eapply reachable_var_binop2. eauto. eauto. eauto. auto.
    - simpl.
      inv WTs.
      econstructor.
      eapply IH2. simpl. lia.
      intros; eapply BELOW. eapply reachable_var_externalCall. eauto. eauto. eauto.
    - simpl; constructor.
  Qed.

  Lemma collapse_interp_inv2:
    forall vvs,
      wt_vvs (Sigma:=Sigma) R vvs
    -> vvs_smaller_variables vvs
    -> forall n a v,
        (forall v, reachable_var vvs a v -> v < n)%positive ->
interp_sact (sigma:=sigma) REnv r (PTree.map (fun _ '(t,a) => (t, collapse_sact vvs a)) vvs) (collapse_sact vvs a) v ->
        forall t : type, wt_sact (Sigma:=Sigma) R vvs a t ->
                         interp_sact (sigma:=sigma) REnv r vvs a v.
  Proof.
    intros vvs WTvvs VSV n a.
    change n with (projT1 (existT (fun _ => sact) n a)).
    change a with (projT2 (existT (fun _ => sact) n a)) at 1 3 4 5.
    generalize (existT (fun _ => sact) n a).
    clear n a. intro s. pattern s.
    eapply well_founded_induction.
    apply wf_order_sact. clear s.
    intros x IH v BELOW IS t0 WTs.
    assert (IH2: forall a0,
               size_sact a0 < size_sact (projT2 x) ->
               (forall v0, reachable_var vvs a0 v0 -> (v0 < projT1 x)%positive) ->
               forall v t,
                 interp_sact (sigma:=sigma) REnv r (PTree.map (fun _ '(t,a) => (t, collapse_sact vvs a)) vvs) (collapse_sact vvs a0) v ->
                 wt_sact (Sigma:=Sigma) R vvs a0 t ->
                 interp_sact (sigma:=sigma) REnv r vvs a0 v
           ).
    {
      intros. eapply (IH (existT _ (projT1 x) a0)).
      red. destruct x. apply Relation_Operators.right_lex. simpl in H.  auto.
      simpl. auto. simpl. auto. simpl. eauto.
    }
    destruct x; simpl in *.
    destruct s; simpl in *.
    - inv WTs. rewrite H0 in IS. econstructor. eauto.
      destr_in IS; subst.
      + inv IS.
        rewrite PTree.gmap in H1. unfold option_map in H1. repeat destr_in H1; inv H1.
        econstructor. eauto.
        eapply (IH (existT _ var s)).
        red. apply Relation_Operators.left_lex. apply BELOW. constructor.
        simpl.
        generalize (reachable_var_aux_below_get _ VSV _ _ _ Heqo). auto.
        generalize (reachable_var_aux_below_get _ VSV _ _ _ H0). intros.
        trim (H var0). constructor. specialize (H1 _ H3). lia.
        simpl. auto. simpl; eauto.
      + inv IS. constructor.
      + inv IS.
        generalize (WTvvs _ _ _ H0). intro WT; inv WT.
        rewrite PTree.gmap in H1. setoid_rewrite H0 in H1. simpl in H1. inv H1.
        inv H2.
        econstructor.
        eapply (IH (existT _ var s0_1)).
        red. apply Relation_Operators.left_lex. apply BELOW. constructor.
        simpl.
        intros; eapply (reachable_var_aux_below_get _ VSV _ _ _ H0).
        eapply reachable_var_if_cond; eauto. simpl. eauto. simpl. eauto.
        destr.
        eapply (IH (existT _ var s0_2)).
        red. apply Relation_Operators.left_lex. apply BELOW. constructor.
        simpl.
        intros; eapply (reachable_var_aux_below_get _ VSV _ _ _ H0).
        eapply reachable_var_if_true; eauto. simpl. eauto. simpl. eauto.
        eapply (IH (existT _ var s0_3)).
        red. apply Relation_Operators.left_lex. apply BELOW. constructor.
        simpl.
        intros; eapply (reachable_var_aux_below_get _ VSV _ _ _ H0).
        eapply reachable_var_if_false; eauto. simpl. eauto. simpl. eauto.
      + inv IS.
        generalize (WTvvs _ _ _ H0). intro WT; inv WT.
        rewrite PTree.gmap in H1. setoid_rewrite H0 in H1. simpl in H1. inv H1.
        inv H2.
        econstructor.
        eapply (IH (existT _ var s0)).
        red. apply Relation_Operators.left_lex. apply BELOW. constructor.
        simpl.
        intros; eapply (reachable_var_aux_below_get _ VSV _ _ _ H0).
        eapply reachable_var_unop; eauto. simpl. eauto. simpl. eauto. auto.
      + inv IS.
        generalize (WTvvs _ _ _ H0). intro WT; inv WT.
        rewrite PTree.gmap in H1. setoid_rewrite H0 in H1. simpl in H1. inv H1.
        inv H2.
        econstructor.
        eapply (IH (existT _ var s0_1)).
        red. apply Relation_Operators.left_lex. apply BELOW. constructor.
        simpl.
        intros; eapply (reachable_var_aux_below_get _ VSV _ _ _ H0).
        eapply reachable_var_binop1; eauto. simpl. eauto. simpl. eauto.
        eapply (IH (existT _ var s0_2)).
        red. apply Relation_Operators.left_lex. apply BELOW. constructor.
        simpl.
        intros; eapply (reachable_var_aux_below_get _ VSV _ _ _ H0).
        eapply reachable_var_binop2; eauto. simpl. eauto. simpl. eauto. auto.
      + inv IS.
        generalize (WTvvs _ _ _ H0). intro WT; inv WT.
        rewrite PTree.gmap in H1. setoid_rewrite H0 in H1. simpl in H1. inv H1.
        inv H2.
        econstructor.
        eapply (IH (existT _ var s0)).
        red. apply Relation_Operators.left_lex. apply BELOW. constructor.
        simpl.
        intros; eapply (reachable_var_aux_below_get _ VSV _ _ _ H0).
        eapply reachable_var_externalCall; eauto. simpl. eauto. simpl. eauto.
      + inv IS.
        generalize (WTvvs _ _ _ H0). intro WT; inv WT.
        rewrite PTree.gmap in H1. setoid_rewrite H0 in H1. simpl in H1. inv H1.
        inv H2.
        econstructor.
    - inv IS. constructor.
    - inv IS. inv WTs.
      econstructor.
      eapply IH2. lia. intros; eapply BELOW. eapply reachable_var_if_cond; eauto. eauto. eauto.
      destr.
      eapply IH2. lia. intros; eapply BELOW. eapply reachable_var_if_true; eauto. eauto. eauto.
      eapply IH2. lia. intros; eapply BELOW. eapply reachable_var_if_false; eauto. eauto. eauto.
    - inv IS. inv WTs.
      econstructor.
      eapply IH2. lia. intros; eapply BELOW. eapply reachable_var_unop; eauto. eauto. eauto. auto.
    - inv IS. inv WTs.
      econstructor.
      eapply IH2. lia. intros; eapply BELOW. eapply reachable_var_binop1; eauto. eauto. eauto.
      eapply IH2. lia. intros; eapply BELOW. eapply reachable_var_binop2; eauto. eauto. eauto. auto.
    - inv IS. inv WTs.
      econstructor.
      eapply IH2. lia. intros; eapply BELOW. eapply reachable_var_externalCall; eauto. eauto. eauto.
    - inv IS. constructor.
  Qed.

  Lemma sf_eq_collapse_sf:
    forall sf,
      wf_sf sf ->
      sf_eq sf (collapse_sf sf).
  Proof.
    intros sf WF.
    constructor.
    - simpl. auto.
    - generalize (wf_collapse_sf _ WF). intro A; inv WF; inv A.
      intros. inv H0.
      split; intro A.
      + inv A. rewrite H2 in H1; inv H1.
        econstructor. setoid_rewrite PTree.gmap. setoid_rewrite H2. simpl. reflexivity.
        eapply collapse_interp2. eauto. eauto.
        eapply reachable_var_aux_below; eauto.
        eapply wf_sf_vvs0. eauto. auto. eauto.
      + inv A.
        setoid_rewrite PTree.gmap in H1. setoid_rewrite H2 in H1. simpl in H1. inv H1.
        econstructor. eauto.
        eapply collapse_interp_inv2. eauto. eauto.
        eapply reachable_var_aux_below; eauto.
        eapply wf_sf_vvs0. eauto. auto. eauto.
    - intros. simpl.
      split. eapply f_wt_sact_ok'; eauto.
      intro A; inv A.
      rewrite PTree.gmap in H1. unfold option_map in H1; repeat destr_in H1; inv H1.
      econstructor. eauto.
  Qed.

  Lemma sf_eq_restricted_trans:
    forall l1 l2 l3 sf1 sf2 sf3,
      sf_eq_restricted l1 sf1 sf2 ->
      sf_eq_restricted l2 sf2 sf3 ->
      incl l3 l1 -> incl l3 l2 ->
      sf_eq_restricted l3 sf1 sf3.
  Proof.
    intros.
    destruct H, H0.
    constructor.
    - intros.
      rewrite sf_eqr_final0; auto.
    - intros. rewrite sf_eqr_vars0; eauto.
      rewrite sf_eqr_vars1; eauto. tauto.
      eapply sf_eqr_wt0; eauto.
      rewrite sf_eqr_final1; eauto.
      rewrite sf_eqr_final1; eauto.
    - intros.
      rewrite sf_eqr_wt0; eauto.
      rewrite sf_eqr_final1; eauto.
  Qed.

  Lemma sf_eq_sf_eq_restricted_trans:
    forall l sf1 sf2 sf3,
      sf_eq sf1 sf2 ->
      sf_eq_restricted l sf2 sf3 ->
      sf_eq_restricted l sf1 sf3.
  Proof.
    intros. eapply sf_eq_restricted_trans.
    eapply sf_eq_is_restricted. eauto. eauto.
    red; intros. eapply nth_error_In. apply finite_surjective.
    red; tauto.
  Qed.

  Lemma collapse_prune_interp_cycle_ok:
    forall reg sf sf',
    wf_sf sf
    -> prune_irrelevant (collapse_sf sf) reg = Some sf'
    -> getenv REnv (interp_cycle sf) reg = getenv REnv (interp_cycle sf') reg.
  Proof.
    intros.
    unfold prune_irrelevant in H0. destr_in H0; inv H0.
    eapply sf_eqr_interp_cycle_ok.
    - auto.
    - eapply wf_sf_prune_irrelevant_aux.
      + eauto.
      + eapply wf_collapse_sf. auto.
    - eapply sf_eq_sf_eq_restricted_trans.
      2: apply sf_eqf_prune_irrelevant_aux.
      + apply sf_eq_collapse_sf. auto.
      + auto.
      + apply wf_collapse_sf. auto.
    - simpl; auto.
  Qed.

  Lemma wt_exploit:
    forall sf (WF: wf_sf sf)
           vvs (a : SimpleForm.sact) (t : type) r0 b bs,
      wt_sact (Sigma:=Sigma) R vvs a t -> wt_sact (Sigma:=Sigma) R vvs (exploit_partial_bitwise_information_in_var a r0 b bs) t.
  Proof.
    induction a; simpl; intros; eauto.
    - inv H. econstructor; eauto.
    - inv H.
      assert (wt_sact (Sigma:=Sigma) R vvs (SUnop ufn1 (exploit_partial_bitwise_information_in_var a r0 b bs)) t).
      {
        econstructor; eauto.
      }
      destr; auto.
      destr; auto.
      destr; auto.
      destr; auto.
      destr; auto.
      destr; auto.
      subst. inv H4.
      econstructor; eauto. constructor.
      rewrite firstn_length.
      rewrite skipn_length.
      apply min_l.
      apply andb_true_iff in Heqb0. destruct Heqb0.
      apply andb_true_iff in H0. destruct H0.
      apply leb_complete in H3.
      apply leb_complete in H0.
      lia.
    - inv H.
      assert (wt_sact (Sigma:=Sigma) R vvs (SBinop ufn2 (exploit_partial_bitwise_information_in_var a1 r0 b bs) (exploit_partial_bitwise_information_in_var a2 r0 b bs)) t).
      {
        econstructor; eauto.
      }
      destr; auto.
      repeat destr; auto.
      rewrite ! andb_true_iff in Heqb0.
      rewrite ! Nat.leb_le in Heqb0.
      destruct Heqb0 as ((A & B) & C).
      inv H6.
      econstructor. constructor.
      rewrite firstn_length. rewrite skipn_length.
      lia.
    - inv H. econstructor; eauto.
  Qed.

  Lemma vis_exploit:
    forall r0 b bs,
    forall (s : SimpleForm.sact) (v' : positive), var_in_sact (exploit_partial_bitwise_information_in_var s r0 b bs) v' -> var_in_sact s v'.
  Proof.
    induction s; simpl; intros; eauto.
    - inv H. eapply var_in_if_cond; eauto.
      eapply var_in_if_true; eauto.
      eapply var_in_if_false; eauto.
    - eapply var_in_sact_unop.
      repeat destr_in H; inv H; eauto.
    - assert (var_in_sact
                (SBinop ufn2 (exploit_partial_bitwise_information_in_var s1 r0 b bs) (exploit_partial_bitwise_information_in_var s2 r0 b bs)) v' -> var_in_sact (SBinop ufn2 s1 s2) v').
      {
        intros A; inv A.
        eapply var_in_sact_binop_1; eauto.
        eapply var_in_sact_binop_2; eauto.
      }
      repeat destr_in H; eauto. inv H.
    - inv H; econstructor; eauto.
  Qed.


  Lemma wf_exploit:
    forall sf r b bs,
      wf_sf sf -> wf_sf (exploit_partial_bitwise_information sf r b bs).
  Proof.
    intros.
    apply wf_f; auto.
    intros; eapply wt_exploit; eauto.
    intros; eapply vis_exploit; eauto.
  Qed.

  Lemma take_drop'_firstn_skipn:
    forall {A:Type} n (l: list A),
      take_drop' n l = (List.firstn n l, List.skipn n l).
  Proof.
    induction n; simpl; intros; eauto.
    destruct l. reflexivity.
    erewrite take_drop'_cons. 2: eauto. reflexivity.
  Qed.

  Lemma skipn_add:
    forall {A: Type} n2 n1 (l: list A),
      skipn n1 (skipn n2 l) = skipn (n1 + n2) l.
  Proof.
    induction n2; simpl; intros; eauto.
    rewrite Nat.add_0_r. auto.
    replace (n1 + S n2) with (S (n1 + n2)). simpl.
    destr. rewrite skipn_nil. auto. lia.
  Qed.

  Lemma exploit_interp_inv:
    forall vvs,
      wt_vvs (Sigma:=Sigma) R vvs ->
      vvs_smaller_variables vvs ->
      forall r0 b bs,
        (exists v,
            getenv REnv r r0 = Bits v /\
              List.firstn (List.length bs) (List.skipn b v) = bs
        ) ->
      forall (a : sact) (v : val), interp_sact (sigma:=sigma) REnv r vvs (exploit_partial_bitwise_information_in_var a r0 b bs) v -> forall t : type, wt_sact (Sigma:=Sigma) R vvs a t -> interp_sact (sigma:=sigma) REnv r vvs a v.
  Proof.
    intros vvs WT VVS r0 b bs (vv & REG & BS) a v IS t WTa.
    revert a t WTa v IS.
    induction 1; simpl; intros; eauto.
    - inv IS. econstructor; eauto.
      destr; eauto.
    - assert (interp_sact (sigma:=sigma) REnv r vvs
                (SUnop ufn (exploit_partial_bitwise_information_in_var a r0 b bs)) v ->
              interp_sact (sigma:=sigma) REnv r vvs (SUnop ufn a) v).
      {
        intro A; inv A; econstructor; eauto.
      }
      repeat destr_in IS; auto.
      clear H0.
      inv IS.
      econstructor.
      apply IHWTa. econstructor. rewrite REG. simpl.
      rewrite ! take_drop'_firstn_skipn.
      rewrite ! andb_true_iff in Heqb0.
      rewrite ! Nat.leb_le in Heqb0.
      destruct Heqb0 as ((A & B) & C).
      rewrite firstn_length. rewrite skipn_length.
      f_equal. f_equal.
      generalize (WTRENV idx). rewrite REG. intro D; inv D.
      rewrite Heqt0 in H0. inv H0.
      rewrite Nat.min_l. 2: lia.
      rewrite Nat.sub_diag. simpl. rewrite app_nil_r.
      rewrite <- BS.
      rewrite skipn_firstn.
      rewrite skipn_add. replace (offset - b + b) with offset by lia.
      rewrite firstn_firstn. f_equal. lia.
    - assert ( interp_sact REnv r vvs
                                (sigma:=sigma)
                      (SBinop ufn (exploit_partial_bitwise_information_in_var a1 r0 b bs) (exploit_partial_bitwise_information_in_var a2 r0 b bs)) v ->
                    interp_sact (sigma:=sigma) REnv r vvs (SBinop ufn a1 a2) v
             ).
      intro A; inv A.
      econstructor; eauto.
      repeat destr_in IS; eauto. clear H0.
      rewrite ! andb_true_iff in Heqb0.
      rewrite ! Nat.leb_le in Heqb0.
      destruct Heqb0 as ((A & B) & C).
      inv IS.
      econstructor; eauto.
      apply IHWTa1. econstructor.
      apply IHWTa2. econstructor. simpl. rewrite REG.
      generalize (WTRENV r0). rewrite REG. intro D; inv D.
      rewrite Heqt in H0. inv H0.
      rewrite ! take_drop'_firstn_skipn.
      rewrite Nat.min_l. 2: lia.
      rewrite Nat.sub_diag. simpl. rewrite app_nil_r.
      f_equal. f_equal.
      rewrite <- BS.
      rewrite skipn_firstn.
      rewrite skipn_add. replace (Bits.to_nat (Bits.of_list v1) - b + b) with (Bits.to_nat (Bits.of_list v1)) by lia.
      rewrite firstn_firstn. f_equal. lia.
    - inv IS. econstructor; eauto.
  Qed.


  Lemma exploit_interp:
    forall vvs,
      wt_vvs (Sigma:=Sigma) R vvs ->
      vvs_smaller_variables vvs ->
      forall r0 b bs,
        (exists v,
            getenv REnv r r0 = Bits v /\
              List.firstn (List.length bs) (List.skipn b v) = bs
        ) ->
      forall (a : sact) (v : val), forall t : type, wt_sact (Sigma:=Sigma) R vvs a t -> interp_sact (sigma:=sigma) REnv r vvs a v ->
  interp_sact (sigma:=sigma) REnv r vvs (exploit_partial_bitwise_information_in_var a r0 b bs) v.
  Proof.
    intros vvs WT VVS r0 b bs (vv & REG & BS).
    intros a v t WTa IS.
    revert a t WTa v IS.
    induction 1; simpl; intros; eauto.
    - inv IS. econstructor; eauto.
      destr; eauto.
    -
      assert (interp_sact (sigma:=sigma) REnv r vvs (SUnop ufn a) v ->
             interp_sact (sigma:=sigma) REnv r vvs
                (SUnop ufn (exploit_partial_bitwise_information_in_var a r0 b bs)) v ).
      {
        intro A; inv A; econstructor; eauto.
      }
      repeat destr; auto. subst.
      clear H0.
      inv IS.
      apply IHWTa in H2. inv H2. rewrite REG in H4. simpl in H4. inv H4.
      rewrite ! take_drop'_firstn_skipn.
      rewrite ! andb_true_iff in Heqb0.
      rewrite ! Nat.leb_le in Heqb0.
      destruct Heqb0 as ((A & B) & C).
      generalize (WTRENV idx). rewrite REG. intro D; inv D.
      rewrite Heqt0 in H0. inv H0.
      rewrite firstn_length. rewrite skipn_length.
      rewrite Nat.min_l. 2: lia.
      rewrite Nat.sub_diag. simpl. rewrite app_nil_r.
      rewrite <- BS.
      rewrite skipn_firstn.
      rewrite skipn_add. replace (offset - b + b) with offset by lia.
      rewrite firstn_firstn.
      rewrite Nat.min_l by lia. constructor.
    - assert (
          interp_sact (sigma:=sigma) REnv r vvs (SBinop ufn a1 a2) v ->
          interp_sact REnv r vvs
                                (sigma:=sigma)
                      (SBinop ufn (exploit_partial_bitwise_information_in_var a1 r0 b bs) (exploit_partial_bitwise_information_in_var a2 r0 b bs)) v
             ).
      intro A; inv A.
      econstructor; eauto.
      repeat destr; eauto. clear H0.
      rewrite ! andb_true_iff in Heqb0.
      rewrite ! Nat.leb_le in Heqb0.
      destruct Heqb0 as ((A & B) & C).
      inv IS.
      apply IHWTa1 in H3.
      apply IHWTa2 in H5. inv H3. inv H5.
      rewrite REG in H6. simpl in H6. inv H6.
      generalize (WTRENV r0). rewrite REG. intro D; inv D.
      rewrite Heqt in H0. inv H0.
      rewrite ! take_drop'_firstn_skipn.
      rewrite Nat.min_l. 2: lia.
      rewrite Nat.sub_diag. simpl. rewrite app_nil_r.
      rewrite <- BS.
      rewrite skipn_firstn.
      rewrite skipn_add. replace (Bits.to_nat (Bits.of_list v1) - b + b) with (Bits.to_nat (Bits.of_list v1)) by lia.
      rewrite firstn_firstn. rewrite Nat.min_l by lia. constructor.
    - inv IS. econstructor; eauto.
  Qed.


  Lemma sf_eq_exploit:
    forall sf r0 b bs,
      wf_sf sf ->
      (exists v0, getenv REnv r r0 = Bits v0 /\ firstn (Datatypes.length bs) (skipn b v0) = bs) ->
      sf_eq sf (exploit_partial_bitwise_information sf r0 b bs).
  Proof.
    intros.
    eapply sf_eq_f; auto.
    intros; eapply exploit_interp_inv; eauto.
    intros; eapply exploit_interp; eauto.
    intros; eapply wt_exploit; eauto.
    intros; eapply vis_exploit; eauto.
  Qed.

  Theorem exploit_partial_bitwise_information_in_vars_ok:
    forall
      (sf: simple_form) known_reg first_known_bit known_bits
      (EQ:
        exists v0,
        getenv REnv r known_reg = Bits v0
        /\ firstn (Datatypes.length known_bits) (skipn first_known_bit v0)
          = known_bits)
      (WF: wf_sf sf)
      (new_sf :=
        exploit_partial_bitwise_information
          sf known_reg first_known_bit known_bits)
      reg,
    getenv REnv (interp_cycle sf) reg = getenv REnv (interp_cycle new_sf) reg.
  Proof.
    intros.
    subst new_sf.
    apply sf_eq_interp_cycle_ok. auto.
    eapply wf_exploit; eauto.
    eapply sf_eq_exploit; eauto.
  Qed.

  Lemma reachable_vars_aux_stays_in:
    forall fuel e vs n visited,
    In e visited -> In e (reachable_vars_aux vs n visited fuel).
  Proof.
    induction fuel; eauto; intros.
    simpl. destruct (in_dec Pos.eq_dec n visited); eauto.
    destruct (vs ! n); eapply in_cons; eauto.
    destruct p. eapply fold_left_induction; eauto.
  Qed.

  Lemma inlining_no_vars:
    forall reg_id sf (WF: wf_sf sf) t a y k,
      list_assoc (final_values sf) k = Some reg_id ->
      (vars sf) ! reg_id = Some (t,a)
      -> eval_sact_no_vars a = Some y
      -> list_assoc (inlining_pass sf) reg_id = Some y.
  Proof.
    intros.
    exploit inlining_pass_correct. reflexivity. apply WF. apply WF.
    intros (ND & SPEC).
    eapply in_list_assoc. auto. eapply SPEC. eauto.
    econstructor. rewrite H0. eauto.
    eapply eval_sact_no_vars_interp; eauto.
  Qed.

  (* TODO nodup reg_id in sf *)
  Lemma getenv_interp:
    forall reg reg_id reg_act x sf (WF: wf_sf sf)
      (REG_ID: list_assoc (final_values sf) reg = Some reg_id)
      (REG_ACT: Maps.PTree.get reg_id (vars sf) = Some reg_act)
      (EVAL_DETERMINED: eval_sact_no_vars (snd reg_act) = Some x),
    getenv REnv (interp_cycle sf) reg = x.
  Proof.
    intros.
    unfold interp_cycle.
    rewrite getenv_create.
    simpl.
    rewrite REG_ID. destruct reg_act.
    (* remove_vars removes the variables that are not in useful_vars *)
    assert (In reg_id (useful_vars sf)). {
      eapply useful_vars_incl. apply WF. auto.
      apply list_assoc_in in REG_ID.
      apply in_map with (f:=snd) in REG_ID. eauto.
    }
    (* remove_vars keeps an association to reg_id *)
    erewrite <- inlining_pass_sf_eq.
    2: apply sf_eq_remove_vars; auto. 2: auto.
    2: apply wf_sf_remove_vars; auto. 2: eauto.
    (* inlining_pass does not impact the result of list_assoc in our case *)
    erewrite inlining_no_vars; eauto.
  Qed.
End SimpleFormInterpretation.
