Require Import Koika.SimpleForm.Interpretation.
Require Import Koika.SimpleForm.Operations.
Require Import Koika.BitsToLists.
Require Import Koika.KoikaForm.SimpleVal.
Require Import Koika.KoikaForm.Types.
Require Import Koika.SimpleForm.SimpleForm.
Require Import Koika.Utils.EqDec.
Require Import Koika.Utils.Maps.
Require Import Koika.Utils.Environments.

Section Prune.
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
  Local Definition wf_sf := wf_sf R Sigma.
  Hypothesis WTRENV: Wt.wt_renv R REnv r.
  Context {
    wt_sigma:
    forall ufn vc, wt_val (arg1Sig (Sigma ufn)) vc
    -> wt_val (retSig (Sigma ufn)) (sigma ufn vc)
  }.

  Definition prune_irrelevant_aux (sf: @simple_form reg_t ext_fn_t) reg v := {|
final_values := [(reg, v)];
    vars := filter_ptree (vars sf) (PTree.empty _) (useful_vars_for_var sf v)
  |}.

  Definition prune_irrelevant (sf: simple_form) reg :=
    match list_assoc (final_values sf) reg with
    | Some v => Some (prune_irrelevant_aux sf reg v)
    | None => None
    end.

  Fixpoint pos_union_2 (l1 l2 : list positive) : list positive :=
    match l2 with
    | h::t =>
      if List.existsb (Pos.eqb h) l1 then pos_union_2 l1 t
      else h::(pos_union_2 l1 t)
    | nil => l1
    end.

  Lemma pos_union_2_correct:
    forall l1 l2 a, In a (pos_union_2 l1 l2) <-> In a l1 \/ In a l2.
Proof.
    intros. split; intro.
    - induction l2; auto.
      destruct (Pos.eqb a a0) eqn:?.
      + rewrite Pos.eqb_eq in Heqb. subst. right. constructor. reflexivity.
      + simpl in H. destr_in H.
        * apply IHl2 in H. destruct H; auto.
          right. simpl. auto.
        * simpl in H. destruct H.
          ** subst. apply Pos.eqb_neq in Heqb. contradiction.
          ** apply IHl2 in H. destruct H; auto.
             right. simpl. auto.
    - destruct H.
      + induction l2; auto. simpl. destr. simpl. right. auto.
      + induction l2; auto.
        * inv H.
        * simpl in *. destruct H; subst.
          ** destr.
             *** apply existsb_exists in Heqb. destruct Heqb. destruct H.
                 apply Pos.eqb_eq in H0. subst. clear IHl2.
                 induction l2; auto. simpl. destr. simpl. right. auto.
             *** left. auto.
          ** apply IHl2 in H. destr; try right; auto.
  Qed.

  Lemma NoDup_pos_union_2:
    forall l1 l2, NoDup l1 -> NoDup l2 -> NoDup (pos_union_2 l1 l2).
  Proof.
    intros.
    induction l2; eauto.
    inv H0. apply IHl2 in H4.
    simpl. destr.
    constructor; auto.
    assert (~In a l1). {
      clear - Heqb.
      induction l1; auto.
      intro. simpl in H. destruct H.
      - subst. simpl in Heqb. rewrite Pos.eqb_refl in Heqb. discriminate Heqb.
      - simpl in Heqb. apply orb_false_elim in Heqb. destruct Heqb.
        apply IHl1 in H1. auto.
    }
    induction (pos_union_2 l1 l2) eqn:eq; auto.
    intro. rewrite <- eq in H1.
    eapply pos_union_2_correct in H1. destruct H1; auto.
  Qed.

  Definition pos_union (l : list (list positive)) : list positive :=
    List.fold_right (pos_union_2) [] l.

  Lemma NoDup_pos_union:
    forall (l : list (list positive)),
    Forall (@NoDup positive) l -> NoDup (pos_union l).
  Proof.
    induction l; intro; simpl; auto.
    - constructor.
    - inv H. apply NoDup_pos_union_2; auto.
  Qed.

  Definition prune_irrelevant_l
    (sf: @simple_form reg_t ext_fn_t) (regs: list reg_t)
  :=
    let reg_vars_list :=
      list_options_to_list (List.map (list_assoc (final_values sf)) regs)
    in
    let reachable_vars_list := List.map (useful_vars_for_var sf) reg_vars_list in
    let reachable_vars := pos_union reachable_vars_list in {|
      final_values :=
        List.filter
          (fun x => List.existsb (Pos.eqb (snd x)) reg_vars_list)
          (final_values sf);
      vars := filter_ptree (vars sf) (PTree.empty _) reachable_vars
    |}.

  Lemma Forall_map_2:
    forall {A B} (P: B -> Prop) f (l: list A),
    (forall (x: A), P (f x)) -> Forall P (List.map f l).
  Proof.
    induction l; intros; simpl.
    - constructor.
    - constructor; auto.
  Qed.

    Definition is_well_structured_acc
      {A} (f: list A -> A -> list A) (acc: list A)
    :=
      forall x x', In x acc -> In x' (f [] x) -> In x' acc.

    Lemma reachable_var_aux_below_preserves_is_well_structured_acc :
      forall (sf: simple_form) (wfsf: wf_sf sf) acc,
      is_well_structured_acc
        (fun acc x => reachable_vars_aux (vars sf) x acc (S (Pos.to_nat x)))
        acc
      -> forall n,
         is_well_structured_acc
           (fun acc x => reachable_vars_aux (vars sf) x acc (S (Pos.to_nat x)))
           (reachable_vars_aux (vars sf) n acc (S (Pos.to_nat n))).
    Proof.
      intros.
      eapply (
        pos_strong_ind
        (fun n => is_well_structured_acc
          (fun (acc0 : list positive) (x : positive) =>
           reachable_vars_aux (vars sf) x acc0 (S (Pos.to_nat x)))
          (reachable_vars_aux (vars sf) n acc (S (Pos.to_nat n)))
        )
      ).
      ). induction n.

    (* Not a very good name *)
    Definition is_accumulating {A} (f: list A -> A -> list A) :=
      forall e acc e',
      is_well_structured_acc f acc
      -> In e (acc ++ f [] e') <-> In e (f acc e').

    Lemma reachable_vars_aux_is_accumulating_if_acc_ok:
      forall sf f, wf_sf sf
      -> is_accumulating (fun acc n =>
        reachable_vars_aux (vars sf) n acc (S (Pos.to_nat n))
      ).
    Proof.
      intros sf f wfsf.
      induction f.
      - unfold is_accumulating. intros. simpl in *. now rewrite app_nil_r.
      - unfold is_accumulating. intros. simpl.
        split; intro.
        + apply in_app_or in H0.
          destruct H0.
          * (* e is in acc *)
            destr. destr.
            ** right. destruct p.
               unfold is_accumulating in IHf.
               unfold is_well_structured_acc in H.
               apply fold_left_induction; auto.
               intros. now apply reachable_vars_aux_incr.
            ** right. auto.
          * (* e is in the part added by e' *)
            unfold is_accumulating in IHf.
            destr.
            **

                 useful_vars_for_var

  Lemma wf_sf_implies_useful_vars_for_var_smaller:
    forall sf (wfsf: wf_sf sf) v e x s,
    In e (useful_vars_for_var sf v)
    -> (vars sf) ! v = Some (x, s)
    -> (e <= v)%positive.
  Proof.
    intros sf wfsf v.
    eapply (
      pos_strong_ind (
        fun v => forall (e : positive) (x : type) (s : SimpleForm.sact),
          In e (useful_vars_for_var sf v)
          -> (vars sf) ! v = Some (x, s)
          -> (e <= v)%positive
      )
    ).
    - intros. destruct H0. { subst. reflexivity. }
      rewrite H1 in H0.
      destruct wfsf. unfold vvs_smaller_variables in wf_sf_vvs.
      induction (vars_in_sact s). { inv H0. }
      simpl in H0.

(*       Lemma accumulating_fold_left_preserves_acc: *)
(*         forall A B, forall f, is_accumulating f *)
(*         -> forall (l: list B) (acc: list A) e, In e acc *)
(*         -> In e (fold_left f l acc). *)
(*       Proof. *)
(*         induction l; auto. *)
(*         intros. simpl. eapply IHl. *)
(*         now eapply H. *)
(*       Qed. *)

(*   Lemma useful_vars_for_var_reachable_var_equiv: *)
(*     forall sf v e x s (wfsf: wf_sf sf), *)
(*     (vars sf) ! v = Some (x, s) *)
(*     -> In e (useful_vars_for_var sf v) *)
(*     <-> ( *)
(*       reachable_var (reg_t := reg_t) (ext_fn_t := ext_fn_t) (vars sf) s e *)
(*       \/ e = v *)
(*     ). *)
(*   Proof. *)

(*   Lemma wf_sf_prune_irrelevant_l: *)
(*     forall sf regs, wf_sf sf -> wf_sf (prune_irrelevant_l sf regs). *)
(*   Proof. *)

  Lemma wf_sf_prune_irrelevant_aux:
    forall sf reg v,
    list_assoc (final_values sf) reg = Some v
    -> wf_sf sf
    -> wf_sf (prune_irrelevant_aux sf reg v).
  Proof.
    intros.
    eapply wf_sf_filter_ptree. 5: reflexivity.
    eapply nodup_reachable_vars_aux; eauto. apply H0. constructor.
    intros; eapply reachable_vars_aux_ok. eauto. eauto. 2: reflexivity.
    apply H0. simpl; easy. lia. eauto. eauto. eauto. auto.
    simpl. intros. destr_in H1; inv H1. rewrite H. split; auto.
  Qed.

  Lemma sf_eqf_prune_irrelevant_aux:
    forall sf reg v,
    list_assoc (final_values sf) reg = Some v
    -> wf_sf sf
    -> sf_eq_restricted
         R Sigma r sigma [reg] sf (prune_irrelevant_aux sf reg v).
  Proof.
    intros. eapply sf_eqr_filter. 6: reflexivity.
    apply nodup_reachable_vars_aux; eauto. apply H0. constructor.
    intros; eapply reachable_vars_aux_ok; eauto. apply H0. reflexivity.
    easy. auto.
    simpl. intros ? [|[]]. subst.
    destr.
    simpl. intros. repeat destr_in H1; inv H1. split; auto.
  Qed.

  Lemma prune_irrelevant_interp_cycle_ok:
    forall
      reg sf sf' (WF: wf_sf sf) (PRUNE: prune_irrelevant sf reg = Some sf'),
    getenv REnv (interp_cycle r sigma sf) reg
    = getenv REnv (interp_cycle r sigma sf') reg.
  Proof.
    intros.
    unfold prune_irrelevant in PRUNE. destr_in PRUNE; inv PRUNE.
    eapply sf_eqr_interp_cycle_ok; eauto.
    - eapply wf_sf_prune_irrelevant_aux; eauto.
    - eapply sf_eqf_prune_irrelevant_aux; eauto.
    - simpl; auto.
  Qed.
End Prune.
