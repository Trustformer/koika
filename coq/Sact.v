Require Import Coq.Numbers.DecimalString Coq.Program.Equality Coq.Strings.Ascii.
Require Import Koika.Primitives Koika.Syntax.
From RecordUpdate Require Import RecordSet.
Import RecordSetNotations.
Require Import UntypedSemantics Koika.BitsToLists.
Require Import Wt.
Require Import Wellfounded.

Lemma modusponens: forall (P Q: Prop), P -> (P -> Q) -> Q.
Proof. auto. Qed.

Ltac exploit x :=
  refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
  || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
  || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
  || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
  || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
  || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
  || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
  || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
  || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
  || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
  || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
  || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
  || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
  || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
  || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
  || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
  || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
  || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
  || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
  || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
  || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
  || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
  || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _) _)
  || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _) _)
  || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _) _)
  || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _) _)
  || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _) _)
  || refine (modusponens _ _ (x _ _ _ _ _ _ _ _) _)
  || refine (modusponens _ _ (x _ _ _ _ _ _ _) _)
  || refine (modusponens _ _ (x _ _ _ _ _ _) _)
  || refine (modusponens _ _ (x _ _ _ _ _) _)
  || refine (modusponens _ _ (x _ _ _ _) _)
  || refine (modusponens _ _ (x _ _ _) _)
  || refine (modusponens _ _ (x _ _) _)
  || refine (modusponens _ _ (x _) _).

Ltac trim H :=
  match type of H with
  | ?a -> ?b =>
      let x := fresh "H" in
      assert(x: a);[|specialize(H x); clear x]
  end.

(* List utils *)

Fixpoint filter_map {A B: Type} (f: A -> option B) (l: list A) : list B :=
  match l with
    [] => []
  | x::r =>
      match f x with
      | None => filter_map f r
      | Some b => b::filter_map f r
      end
  end.

Lemma filter_map_In:
  forall {A B: Type} (f: A -> option B) l x,
    In x (filter_map f l) <-> (exists y, Some x = f y /\ In y l).
Proof.
  induction l; simpl; intros; eauto. split. tauto. intros (y & _ & []).
  destr; simpl; rewrite IHl.
  - split. intros [C | (y & EQ & IN)]. subst. eexists; split; eauto.
    eexists; split; eauto.
    intros (y & EQ & [IN|IN]); subst. left; congruence. right; eexists; split; eauto.
  - split; intros (y & EQ & IN); eauto.
    destruct IN as [IN|IN]; eauto. congruence.
Qed.

Lemma Forall_list_options:
  forall {A:Type} (P: A -> Prop) l,
    (forall x y,
        In x l ->
        x = Some y ->
        P y
    ) ->
    Forall P (filter_map id l).
Proof.
  intros.
  rewrite Forall_forall. intros.
  rewrite filter_map_In in H0. destruct H0 as (y & EQ & IN). unfold id in EQ. subst.
  eauto.
Qed.

Lemma list_assoc_set_key_in:
  forall {K V: Type} {eq_dec_k: EqDec K} (l: list (K*V)) k v,
    In k (map fst (list_assoc_set l k v)).
Proof.
  induction l; simpl; intros; eauto.
  repeat destr. subst; simpl; auto. simpl; eauto.
Qed.


Lemma list_assoc_set_key_stays_in:
  forall {K V: Type} {eq_dec_k: EqDec K} (l: list (K*V)) k k' v,
    In k (map fst l) ->
    In k (map fst (list_assoc_set l k' v)).
Proof.
  induction l; simpl; intros; eauto.
  repeat destr. subst; simpl; auto. simpl in *; eauto.
  destruct H; auto.
Qed.

Lemma list_assoc_cons:
  forall {K V: Type} {eq_dec_k: EqDec K} (l: list (K*V)) k k' v,
    list_assoc ((k,v)::l) k' =
      if eq_dec k' k then Some v else list_assoc l k'.
Proof.
  reflexivity.
Qed.

Lemma list_assoc_set_not_before:
  forall {K V: Type} {eqdec: EqDec K} (l: list (K * V)) k v k' v' ,
    ~ In k (map fst l) ->
    In (k', v') (list_assoc_set l k v) <-> In (k', v') l \/ (k, v) = (k', v').
Proof.
  induction l; simpl; intros; eauto. tauto.
  repeat destr; simpl in *; subst.
  contradict H. auto.
  rewrite IHl. tauto. tauto.
Qed.

Lemma list_assoc_app : forall {K V: Type} {eqdec: EqDec K} (l1 l2: list (K * V)) k v,
    list_assoc l1 k = Some v ->
    list_assoc (l1 ++ l2) k = Some v.
Proof.
  induction l1; simpl; intros; eauto. easy. repeat destr_in H; eauto.
Qed.

Lemma list_assoc_app_none : forall {K V: Type} {eqdec: EqDec K} (l1 l2: list (K * V)) k,
    list_assoc l1 k = None ->
    list_assoc (l1 ++ l2) k = list_assoc l2 k.
Proof.
  induction l1; simpl; intros; eauto. repeat destr_in H; eauto. easy.
Qed.


Lemma list_assoc_spec: forall {K V} {eqdec: EqDec K} (l: list (K * V)) k k' v,
    list_assoc (list_assoc_set l k v) k' = if eq_dec k k' then Some v else list_assoc l k'.
Proof.
  intros; destr; subst.
  rewrite list_assoc_gss; auto.
  rewrite list_assoc_gso; auto.
Qed.

Lemma list_assoc_app_spec: forall {K V} {eqdec: EqDec K} (l1 l2: list (K * V)) k,
    list_assoc (l1 ++ l2) k =
      match list_assoc l1 k with
      | Some v => Some v
      | None => list_assoc l2 k
      end.
Proof.
  intros; destr; subst.
  eapply list_assoc_app; eauto.
  eapply list_assoc_app_none; eauto.
Qed.

Lemma list_assoc_unknown_key:
  forall {A B: Type} {eqdec: EqDec A} (l: list (A * B)) k,
    ~ In k (map fst l) ->
    list_assoc l k = None.
Proof.
  induction l; simpl; intros; eauto. repeat destr; intuition.
Qed.

Lemma list_assoc_none_unknown_key:
  forall {A B: Type} {eqdec: EqDec A} (l: list (A * B)) k,
    list_assoc l k = None ->
    ~ In k (map fst l).
Proof.
  induction l; simpl; intros; eauto. repeat destr_in H. easy.
  apply IHl in H. simpl. intuition.
Qed.

Lemma list_assoc_in_keys:
  forall {A B: Type} {eqdec: EqDec A} (l: list (A * B)) k x,
    list_assoc l k = Some x ->
    In k (map fst l).
Proof.
  induction l; simpl; intros; eauto. easy.
  repeat destr_in H; inv H; eauto.
Qed.

Lemma list_assoc_in:
  forall {K V: Type} {eq_dec_k: EqDec K} (l: list (K*V)) k v,
    list_assoc l k = Some v -> In (k,v) l.
Proof.
  induction l; simpl; intros; eauto. easy. repeat destr_in H. inv H. auto. eauto.
Qed.

Lemma in_list_assoc_set_inv:
  forall {K V: Type} {eq_dec: EqDec K} (l: list (K * V)) k' v' k v,
    In (k', v') (list_assoc_set l k v) ->
    (k, v) = (k', v') \/ In (k', v') l.
Proof.
  induction l; simpl; intros; eauto.
  repeat destr_in H; simpl in *; subst.
  destruct H; auto.
  destruct H; auto. apply IHl in H. destruct H; auto.
Qed.

Lemma in_map_list_assoc_set_inv:
  forall {K V: Type} {eqdec: EqDec K} (l : list (K * V)) (k : K)
    (v : V) k' ,
    In k' (map fst (list_assoc_set l k v)) ->
    k = k' \/ In k' (map fst l).
Proof.
  induction l; simpl; intros; eauto. repeat destr_in H. subst. simpl. auto.
  simpl in *. destruct H; auto. apply IHl in H. tauto.
Qed.

Lemma in_keys_list_assoc_ex:
  forall {K V: Type} {eqdec: EqDec K} (l: list (K*V)) k,
    In k (map fst l) ->
    exists v, list_assoc l k = Some v.
Proof.
  induction l; simpl; intros; eauto. easy.
  destruct H. destr. simpl in *. subst. rewrite eq_dec_refl. eauto.
  repeat destr; subst; eauto.
Qed.

Lemma assoc_list_assoc:
  forall {K1 K2: Type} {eqdec: EqDec K1} (l: list (K1 * K2)) k tm,
    assoc k l = Some tm ->
    list_assoc l k = Some (projT1 tm).
Proof.
  induction l; simpl; intros; eauto. inv H.
  repeat destr_in H.
  subst.
  unfold eq_rect_r in H; simpl in H. inv H. simpl. auto.
  inv H. simpl. erewrite IHl; eauto. simpl; auto. inv H.
Qed.

Lemma incl_incl_map:
  forall {A B: Type} (l1 l2: list (A * B))
         (P: forall x y, In (x, y) l1 -> In (x, y) l2),
  forall x, In x (map fst l1) -> In x (map fst l2).
Proof.
  intros.
  rewrite in_map_iff in H.
  destruct H as ((a,b) & EQ & IN). subst.
  apply in_map; auto.
Qed.

Lemma nth_error_lt:
  forall {A: Type} (l: list A) n (LT: n < List.length l),
  exists a, nth_error l n = Some a.
Proof.
  induction l; simpl; intros; eauto. lia.
  destruct n. simpl. eauto.
  simpl. apply IHl. lia.
Qed.

Lemma NoDup_map_In_eq:
  forall {A B: Type} (f: A -> B)
         l
         (ND: NoDup (map f l)) x1 x2
         (IN1: In x1 l)
         (IN2: In x2 l)
         (EQ: f x1 = f x2),
    x1 = x2.
Proof.
  induction l; simpl; intros; eauto. easy. inv ND.
  destruct IN1 as [EQ1|IN1]. subst. destruct IN2 as [EQ2|IN2]; eauto.
  apply (in_map f) in IN2. congruence.
  destruct IN2 as [EQ2|IN2]; eauto.
  subst.
  apply (in_map f) in IN1. congruence.
Qed.

Lemma Forall2_trans:
  forall {P: Type} (R: P -> P -> Prop) (Rtrans: forall x y z, R x y -> R y z -> R x z)
    l1 l2,
    Forall2 R l1 l2 -> forall l3, Forall2 R l2 l3 -> Forall2 R l1 l3.
Proof.
  induction 2; simpl; intros; eauto. inv H1; constructor; eauto.
Qed.


Fixpoint val_of_type (t: type) : val :=
  match t with
  | bits_t n => Bits (repeat false n)
  | enum_t sg => Enum sg (repeat false (enum_bitsize sg))
  | struct_t sg => Struct sg (map (fun x => val_of_type (snd x)) (struct_fields sg))
  | array_t sg => Array sg (repeat (val_of_type (array_type sg)) (array_len sg))
  end.

Lemma wt_val_of_type:
  forall t,
    wt_val t (val_of_type t).
Proof.
  induction t using type_ind'; simpl; intros; eauto.
  - constructor. rewrite repeat_length. auto.
  - constructor. rewrite repeat_length. auto.
  - constructor. revert IH. generalize (struct_fields sg).
    induction l; simpl; intros; eauto.
    constructor; eauto. eapply IH. left. apply surjective_pairing.
  - constructor. rewrite Forall_forall.
    intros x IN. apply repeat_spec in IN. subst. eauto.
    rewrite repeat_length. auto.
Qed.

Lemma wt_unop_interp:
  forall ufn t1 t2 v,
    wt_unop ufn t1 t2 ->
    wt_val t1 v ->
    exists v2, sigma1 ufn v = Some v2.
Proof.
  inversion 1; subst; simpl; intros; eauto.
  - inv H0. edestruct uvalue_of_bits_succeeds. eauto. rewrite H0. simpl; eauto.
  - inv H0. simpl.  eauto.
  - inv H0. simpl. eauto. 
  - inv H0. simpl. eauto.
  - inv H0. simpl. eauto. 
  - inv H0. simpl. eauto.
  - inv H0. simpl. eauto. 
  - inv H1. simpl.
    unfold PrimTypeInference.find_field in H0. unfold opt_result in H0.
    destr_in H0; inv H0. clear - Heqo H3.
    revert lv idx Heqo H3. generalize (struct_fields sg).
    induction l; simpl; intros; eauto. easy. destr. simpl in *. subst.
    inv H3.
    repeat destr_in Heqo; inv Heqo.
    rewrite Heqs0. eauto.
    destr. subst; congruence. 
    eauto.
  - inv H1. simpl.
    unfold PrimTypeInference.find_field in H0. unfold opt_result in H0.
    destr_in H0; inv H0. clear - Heqo H3.
    revert bs idx Heqo H3. generalize (struct_fields sg).
    induction l; simpl; intros; eauto. easy. destr. simpl in *. subst.
    repeat destr_in Heqo; inv Heqo.
    simpl. eauto. eauto.
  - inv H1.
    apply nth_error_lt.
    unfold PrimTypeInference.check_index, opt_result in H0.
    destr_in H0; inv H0.
    destruct (lt_dec idx (Datatypes.length lv)). auto.
    erewrite index_of_nat_ge_none in Heqo. congruence. lia.
  - inv H1. simpl.  eauto.
Qed.

Lemma wt_binop_interp:
  forall ufn t1 t2 t3 v1 v2,
    wt_binop ufn t1 t2 t3 ->
    wt_val t1 v1 ->
    wt_val t2 v2 ->
    exists v3, sigma2 ufn v1 v2 = Some v3.
Proof.
  inversion 1; subst; simpl; intros WT1 WT2; try now (inv WT1; inv WT2; simpl; eauto).
  - destr; eauto.
  - inv WT1.
    unfold PrimTypeInference.find_field in H0. unfold opt_result in H0.
    destr_in H0; inv H0. clear - Heqo H2.
    revert lv idx Heqo H2. generalize (struct_fields sg).
    induction l; simpl; intros; eauto. easy. destr. simpl in *. subst.
    inv H2.
    repeat destr_in Heqo; inv Heqo.
    simpl; eauto.
    edestruct IHl; eauto. unfold opt_bind in H; repeat destr_in H; inv H. simpl; eauto.
  - inv WT1. inv WT2.

    assert (exists w, find_field_offset_right (struct_fields sg) name = Some w).
    {
      unfold PrimTypeInference.find_field in H0. unfold opt_result in H0.
      destr_in H0; inv H0. clear - Heqo.
      revert idx Heqo. generalize (struct_fields sg).
      induction l; simpl; intros; eauto. easy. destr. simpl in *. subst.
      repeat destr_in Heqo; inv Heqo. eauto. eauto.
    }
    destruct H1. rewrite H1. simpl. destr. eauto.
  - inv WT1.
    assert (idx < List.length lv).
    unfold PrimTypeInference.check_index, opt_result in H0.
    destr_in H0; inv H0.
    destruct (lt_dec idx (Datatypes.length lv)). lia.
    erewrite index_of_nat_ge_none in Heqo. congruence. lia.
    edestruct (@take_drop_succeeds) as (la & lb & EQ).
    2: rewrite EQ. lia.
    edestruct (@take_drop_spec) as (EQapp & LA & LB). eauto. simpl.
    destr. simpl in LB. lia. eauto.
Qed.

Lemma wt_val_bool:
  forall x, wt_val (bits_t 1) x -> exists b, x = Bits [b].
Proof.
  inversion 1. subst.
  destruct bs; simpl in *; try lia.
  destruct bs; simpl in *; try lia. eauto.
Qed.


        (* Lemma merge_cond_logs_interp2: *)
        (*   forall idx g vvs cond *)
        (*          (WTvvs: wt_vvs vvs) *)
        (*          (VSV: vvs_smaller_variables vvs) n *)
        (*          (VR: vvs_range vvs n) *)
        (*          (WTcond: wt_sact vvs cond (bits_t 1)) *)
        (*          (IFALSE: interp_sact vvs cond (Bits 1 [false])) *)
        (*          c2 c1 *)
        (*          (WT1: forall (i : reg_t) (a : sact), *)
        (*              In (i, a) c1 -> wt_sact vvs a (bits_t 1)) *)
        (*          (WT2: forall (i : reg_t) (a : sact), *)
        (*              In (i, a) c2 -> wt_sact vvs a (bits_t 1)) g1, *)
        (*     list_assoc (merge_cond_logs c1 c2 cond) idx = Some g -> *)
        (*     list_assoc c2 idx = Some g1 -> *)
        (*     forall v, interp_sact vvs g v <-> interp_sact vvs g1 v. *)
        (* Proof. *)
        (*   induction c2; simpl; intros; eauto. assert (g=g1) by congruence. subst. tauto. *)
        (*   destr_in H. *)
        (*   destr_in H0. *)
        (*   - subst. inv H0. *)
        (*   unfold list_assoc_modify in H. destr_in H. *)
        (*   - exploit IHc2. *)
        (*     3: apply H. *)
        (*     { *)
        (*       intros. *)
        (*       apply in_list_assoc_set_inv in H1. destruct H1; eauto. inv H1. *)
        (*       econstructor; eauto. eapply WT1. apply list_assoc_in; eauto. *)
        (*       econstructor; eauto. constructor. constructor. *)
        (*     } *)
        (*     { *)
        (*       intros; eauto. *)
        (*     } *)
        (*     rewrite list_assoc_spec. rewrite H0. *)
        (*     instantiate (1:=if eq_dec r0 idx then (uor s0 (uand cond s)) else g1). destr; eauto. *)
        (*     intro A. rewrite A. destr. 2: tauto. subst. *)
        (*     rewrite Heqo in H0; inv H0. *)
        (*     split; intros II. *)
        (*     inv II. *)
        (*     exploit interp_sact_wt_bool. 1-3: eauto. eapply WT1. apply list_assoc_in; eauto. eauto. *)
        (*     intros (? & ?); subst. *)
        (*     inv H5. *)
        (*     exploit interp_sact_wt_bool. 1-3: eauto. eapply WT2. left;reflexivity. eauto. *)
        (*     intros (? & ?). subst. *)
        (*     exploit interp_sact_determ. apply IFALSE. apply H4. intros <-. *)
        (*     simpl in H9. inv H9. simpl in H6. inv H6. rewrite orb_false_r. auto. *)
        (*     exploit interp_sact_wt_bool. 1-3: eauto. eapply WT1. apply list_assoc_in; eauto. eauto. *)
        (*     intros (? & ?); subst. *)
        (*     exploit wt_sact_interp_bool. 1-3: eauto. eapply WT2. left;reflexivity. *)
        (*     intros (? & ?). *)
        (*     econstructor. eauto. *)
        (*     econstructor; eauto. simpl. reflexivity. simpl. rewrite orb_false_r. auto. *)
        (*   - exploit IHc2. *)
        (*     3: apply H. *)
        (*     { *)
        (*       intros. *)
        (*       apply in_list_assoc_set_inv in H1. destruct H1; eauto. inv H1. *)
        (*       econstructor; eauto. constructor. *)
        (*     } *)
        (*     { *)
        (*       intros; eauto. *)
        (*     } *)
        (*     rewrite list_assoc_spec. rewrite H0. *)
        (*     instantiate (1:=if eq_dec r0 idx then (uand cond s) else g1). destr; eauto. *)
        (*     intro A. rewrite A. destr. tauto. *)
        (* Qed. *)
        (* Lemma merge_cond_logs_interp_none: *)
        (*   forall c2 c1 cond idx, *)
        (*     list_assoc (merge_cond_logs c1 c2 cond) idx = None -> *)
        (*     list_assoc c1 idx = None /\ list_assoc c2 idx = None. *)
        (* Proof. *)
        (*   induction c2; simpl; intros; eauto. *)
        (*   destr_in H. *)
        (*   exploit IHc2. eauto. intros (A & B). *)
        (*   clear H IHc2. *)
        (*   unfold list_assoc_modify in A. rewrite list_assoc_spec in A. *)
        (*   destr_in A; inv A. destr; subst. congruence. intuition. congruence. *)
        (* Qed. *)
 (*  Lemma match_logs_merge_rirs: *)
 (*    forall r2v1 r2v2 r2v3 sched_rir rir r1 sched_log l2 vvs n vvs3 m2 m, *)
 (*      match_logs_r2v r2v1 vvs sched_rir rir sched_log log_empty -> *)
 (*      match_logs_r2v r2v2 vvs sched_rir r1 sched_log l2 -> *)
 (*      wt_sact vvs (SVar n) (bits_t 1) -> *)
 (*      wf_rir r1 vvs -> *)
 (*      wf_rir rir vvs -> *)
 (*      wf_rir sched_rir vvs -> *)
 (*      reg2var_vvs r2v1 vvs -> *)
 (*      reg2var_vvs r2v2 vvs -> *)
 (*      m > n -> *)
 (*      merge_reg2vars r2v1 r2v2 n vvs m = (r2v3, vvs3, m2) -> *)
 (*      interp_sact vvs3 (SVar n) (Bits 1 [false]) -> *)
 (*      wt_vvs vvs -> *)
 (*      vvs_smaller_variables vvs -> *)
 (*      vvs_range vvs m -> *)
 (*      match_logs_r2v r2v3 vvs3 sched_rir (merge_rirs rir r1 n vvs) sched_log l2. *)
 (*  Proof. *)
 (*    intros r2v1 r2v2 r2v3 sched_rir rir r1 sched_log l2 vvs n vvs3 m2 m MLR1 MLR2 WTn WFr1 WFrir WFsr R2V1 R2V2 GT MR FALSE WTvvs VSV VR. *)
 (*    split. *)
 (*    - intros reg prt n0 MaR GET. *)
 (*      edestruct r2v_vvs as (y1 & y2 & GET1 & GET2 & INTERP). 5: eauto. all: eauto. *)
 (*      apply vvs_grows_refl. *)
 (*      edestruct r2v_vvs_aux as (VG3 & VR3 & LE2 & WT3 & VSV3). apply MR. all: auto.  *)
 (*      eapply wt_sact_vvs_grows in WTn; eauto. *)
 (*      erewrite <- INTERP.  2: eauto. simpl. *)
 (*      exploit mlr_read. apply MLR2. eauto. eauto. *)
 (*      eapply vvs_grows_interp_sact with (v2:=vvs3). *)
 (*      eauto using vvs_grows_trans. *)

 (*    - inv MLR2. *)
 (*      edestruct r2v_vvs_aux as (VG3 & VR3 & LE2 & WT3 & VSV3). apply MR. all: eauto. *)
 (*      eapply wt_sact_vvs_grows in WTn; eauto. *)
 (*      eapply match_log_vvs_grows'. eauto. *)
 (*      eauto using vvs_grows_trans. all: eauto. *)
 (*    - inv MLR2. *)
 (*      edestruct r2v_vvs_aux as (VG3 & VR3 & LE2 & WT3 & VSV3). apply MR. all: eauto. *)
 (*      eapply wt_sact_vvs_grows in WTn; eauto. *)
 (*      split; intros. *)
 (*      + rewrite mlv_read0. 2: eauto. *)
 (*        (* unfold merge_rirs, rir_has_read0; simpl. *) *)
 (*        rewrite <- interp_sact_vvs_grows_iff with (vvs':= vvs3); eauto. *)
 (*        2: eapply wt_rir_has_read0; eauto. *)
 (*        unfold merge_rirs, rir_has_read0; simpl. *)
 (*        2: eapply wf_rir_incr. 2: apply WF. 2: eauto using vvs_grows_trans. *)
 (*        destruct (list_assoc (merge_cond_logs _ _ _) _) eqn:?. *)
 (*        eapply merge_cond_logs_interp in Heqo. rewrite Heqo. *)
 (*        split; intros. *)

 (*        destruct (list_assoc (rir_read0s rir) idx) eqn:?. *)
 (*        exploit wt_sact_interp_bool. 4: eapply WFrir. 4: eapply list_assoc_in; eauto. *)
 (*        1-3: eauto. *)
 (*        intros (? & Is0). *)
 (*        econstructor; eauto. *)
 (*        eapply vvs_grows_interp_sact. 2: eauto. eauto using vvs_grows_trans. *)
 (*        instantiate (1:=Bits 1 [x]). *)
 (*        destr. econstructor; eauto. simpl. *)
        
 (*        destruct (list_assoc (merge_cond_logs _ _ _) _) eqn:?. *)
 (*        destr. *)
 (*        exploit merge_cond_logs_interp. 8: apply Heqo. 8: apply Heqo0. *)

 (* 1-3: eauto. 5: eauto. auto. auto. *)
 (*        intros; eapply wt_sact_vvs_grows. 2: eapply WFrir. eauto using vvs_grows_trans. eauto. *)

 (*        intros; eapply wt_sact_vvs_grows. 2: eapply wf_rir_read0s. 3: apply H. 2: apply WF. *)
 (* eauto using vvs_grows_trans. eauto. *)
 (*        eapply match_log_vvs_grows'. eauto. *)
 (*      eauto using vvs_grows_trans. *)
 (*      red; intros. eapply WF. eapply VG2; eauto. *)
 (*      red; intros. eapply WF. eapply VG2; eauto. auto. *)
 (*      eauto. eauto. *)
 (*      red; intros. eapply VG2 in H. eapply wfs_wt_vvs in H; eauto. *)
 (*      eapply wt_sact_vvs_grows. 2: eauto. eauto using vvs_grows_trans. *)
 (*      red; intros. eapply WF. *)
 (*      eapply vvs_range_incr. apply WF. *)
 (*      intros idx EX. *)
 (*      rewrite log_existsb_log_app in EX. *)
 (*      rewrite orb_false_iff in EX. destruct EX. *)
 (*      intros c GET. *)
 (*      simpl in GET. *)

 (*  Admitted. *)
