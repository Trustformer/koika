(*! Proving | Transformation of a schedule into a proof-friendly form !*)
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
  | bits_t n => Bits n (repeat false n)
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
  forall x, wt_val (bits_t 1) x -> exists b, x = Bits 1 [b].
Proof.
  inversion 1. subst.
  destruct bs; simpl in *; try lia.
  destruct bs; simpl in *; try lia. eauto.
Qed.

(* When reasoning about a Koîka schedule, a lot of tedious implicit mechanisms
   have to be considered explicitly (rules merging, cancellation, ...).
   Furthermore, performance issues related to abstract interpretation make
   reasoning about the behavior of some even moderately complex models (e.g.,
   the RISC-V processor example) impossible.

   This is what this simpler form aims to fix. For instance, it makes finding
   under which conditions the value of a register is updated or proving that the
   value of register x never reaches 5 much easier (even trivial in certain
   cases).

   It goes without saying that the result of the interpretation of a model
   before or after its conversion to the form defined hereafter should be equal
   (in terms of the effects of a cycle on the final state of the registers and
   of the emitted extcalls, although the latter are not really considered in
   Koîka's pure semantics). *)

Open Scope nat.
Section SimpleForm.
  Context {pos_t reg_t ext_fn_t rule_name_t: Type}.
  Context {reg_t_eq_dec: EqDec reg_t}.
  Context {ext_fn_t_eq_dec: EqDec ext_fn_t}.
  Definition uact := @daction pos_t string string reg_t ext_fn_t.

  Inductive sact :=
  | SVar (var: nat)
  | SConst (v:val)
  | SIf (cond: sact) (tbranch: sact) (fbranch: sact)
  | SUnop (ufn1: PrimUntyped.ufn1) (arg1: sact)
  | SBinop (ufn2: PrimUntyped.ufn2) (arg1: sact) (arg2: sact)
  | SExternalCall (ufn: ext_fn_t) (arg: sact).

  Definition const_nil := SConst (Bits 0 []).
  Definition const_true := SConst (Bits 1 [true]).
  Definition const_false := SConst (Bits 1 [false]).

  Definition uor (x y: sact) := SBinop (PrimUntyped.UBits2 PrimUntyped.UOr) x y.
  Definition uand (x y: sact) := SBinop (PrimUntyped.UBits2 PrimUntyped.UAnd) x y.
  Definition unot (x: sact) := SUnop (PrimUntyped.UBits1 PrimUntyped.UNot) x.

  Variable REnv : Env reg_t.
  Variable r : env_t REnv (fun _ => val).
  Variable sigma : ext_fn_t -> val -> val.
  Variable R: reg_t -> type.
  Variable Sigma: ext_fn_t -> ExternalSignature.

  Hypothesis wt_sigma: forall ufn vc,
      wt_val (arg1Sig (Sigma ufn)) vc ->
      wt_val (retSig (Sigma ufn)) (sigma ufn vc).

  Inductive wt_sact (vt: list (nat * (type * sact))) : sact -> type -> Prop :=
  | wt_sact_var var t s:
    list_assoc vt var = Some (t, s) ->
    wt_sact vt (SVar var) t
  | wt_sact_const v t:
    wt_val t v ->
    wt_sact vt (SConst v) t
  | wt_sact_if c bt bf t:
    wt_sact vt c (bits_t 1) ->
    wt_sact vt bt t ->
    wt_sact vt bf t ->
    wt_sact vt (SIf c bt bf) t
  | wt_sact_unop ufn a t t' :
    wt_sact vt a t ->
    wt_unop ufn t t' ->
    wt_sact vt (SUnop ufn a) t'
  | wt_sact_binop ufn a1 a2 t1 t2 t' :
    wt_sact vt a1 t1 ->
    wt_sact vt a2 t2 ->
    wt_binop ufn t1 t2 t' ->
    wt_sact vt (SBinop ufn a1 a2) t'
  | wt_sact_extcall ufn a:
    wt_sact vt a (arg1Sig (Sigma ufn)) ->
    wt_sact vt (SExternalCall ufn a) (retSig (Sigma ufn)).

  Inductive interp_sact (vvs: list (nat * (type * sact))) : sact -> val -> Prop :=
  | interp_sact_var var t a v:
    list_assoc vvs var = Some (t, a) ->
    interp_sact vvs a v ->
    interp_sact vvs (SVar var) v
  | interp_sact_const v: interp_sact vvs (SConst v) v
  | interp_sact_if c t f b v:
    interp_sact vvs c (Bits 1 [b]) ->
    interp_sact vvs (if b then t else f) v ->
    interp_sact vvs (SIf c t f) v
  | interp_sact_unop ufn a v v':
                     interp_sact vvs a v ->
    UntypedSemantics.sigma1 ufn v = Some v' ->
    interp_sact vvs (SUnop ufn a) v'
  | interp_sact_binop ufn a1 a2 v1 v2 v' :
    interp_sact vvs a1 v1 ->
    interp_sact vvs a2 v2 ->
    UntypedSemantics.sigma2 ufn v1 v2 = Some v' ->
    interp_sact vvs (SBinop ufn a1 a2) v'
  | interp_sact_extcall ufn a v :
    interp_sact vvs a v ->
    interp_sact vvs (SExternalCall ufn a) (sigma ufn v).

  Lemma interp_sact_determ:
    forall vvs a v1,
      interp_sact vvs a v1 ->
      forall v2,
        interp_sact vvs a v2 ->
        v1 = v2.
  Proof.
    induction 1; simpl; intros ? IS; inv IS; eauto.
    - rewrite H in H2; inv H2. eauto.
    - apply IHinterp_sact1 in H5. inv H5.
      eauto.
    - apply IHinterp_sact in H3. subst. congruence.
    - apply IHinterp_sact1 in H5. subst.
      apply IHinterp_sact2 in H7. subst. congruence.
    - apply IHinterp_sact in H3. subst. congruence.
  Qed.


  Definition schedule := scheduler pos_t rule_name_t.

  (* Simple form and related structures *)
  Definition cond_log := list (reg_t * sact).
  Record write_info := mkWriteInfo { wcond: sact; wval: sact }.
  Definition write_log := list (reg_t * list (write_info)).
  Definition write_log_raw := list (reg_t * (sact * list (write_info))).
  Definition var_value_map := list (nat * (type * sact)).

  Record rule_information_raw :=
    mkRuleInformationRaw {
        rir_read0s: cond_log;
        rir_read1s: cond_log;
        rir_write0s: write_log_raw;
        rir_write1s: write_log_raw;
        rir_vars: var_value_map;
        rir_failure_cond: sact
      }.
  Instance etaRuleInformationRaw : Settable _ :=
    settable! mkRuleInformationRaw
    <rir_read0s; rir_read1s;
  rir_write0s; rir_write1s; rir_vars;
  rir_failure_cond >.
  Record rule_information_clean :=
    mkRuleInformationClean {
        ric_write0s: write_log;
        ric_write1s: write_log;
        ric_vars: var_value_map;
        ric_failure_cond: sact
      }.
  Instance etaRuleInformationClean : Settable _ :=
    settable! mkRuleInformationClean
    < ric_write0s; ric_write1s; ric_vars; ric_failure_cond >.
  Record schedule_information :=
    mkScheduleInformation {
        sc_write0s: cond_log;
        sc_write1s: cond_log;
        sc_vars: var_value_map
      }.
  Instance etaScheduleInformation : Settable _ :=
    settable! mkScheduleInformation
    < sc_write0s; sc_write1s; sc_vars >.
  Record simple_form :=
    mkSimpleForm {
        final_values: list (reg_t * nat);
        vars: var_value_map
      }.
  Instance etaSimpleForm : Settable _ :=
    settable! mkSimpleForm < final_values; vars >.

  (* * rule_information extraction *)
  (* ** Addition of a new action into an existing rule_information *)
  (* *** Merger of failure conditions *)
  Definition or_conds (conds: list sact) :=
    fold_left uor conds const_false.

  Definition merge_failures (f1 f2: sact) : sact := uor f1 f2.

  (* *** Merger of actions *)
  (* Remove Nones from list, turn rest from (Some x) to x. *)
  Definition list_options_to_list (l: list (option sact)) : list sact :=
    filter_map id l.

  Definition merge_conds (wl: (list write_info)) : sact :=
    or_conds (map wcond wl).

  Definition merge_failures_list (action_cond: sact) (conds: list sact) : sact :=
    uand action_cond (or_conds conds).

  Definition add_read0 (rir: rule_information_raw) (grd: sact) (reg: reg_t)
    (* Returns modified rir *)
    : rule_information_raw :=
    let new_grd :=
      match list_assoc (rir_read0s rir) reg with
      | None => grd
      | Some cond' => uor cond' grd
      end in
    rir <| rir_read0s := list_assoc_set (rir_read0s rir) reg new_grd |>.

  Definition add_read1 (rir: rule_information_raw) (grd: sact) (reg: reg_t)
    (* Returns modified rule_information_raw *)
    : rule_information_raw :=
    let new_grd :=
      match list_assoc (rir_read1s rir) reg with
      | None => grd
      | Some cond' => uor cond' grd
      end in
    rir <| rir_read1s := list_assoc_set (rir_read1s rir) reg new_grd |>.

  Definition add_write0
             (rir: rule_information_raw) (grd: sact) (reg: reg_t) (val: sact)
    (* Returns modified rule_information_raw, failure conditions *)
    : rule_information_raw * sact :=
    let (new_grd, new_wi) :=
      match list_assoc (rir_write0s rir) reg with
      | None => (grd, [{| wcond := grd; wval := val |}])
      | Some c =>
          (uor (fst c) grd,
            (snd c)++[{| wcond := grd; wval := val |}])
      end in
    ((rir <| rir_write0s := list_assoc_set (rir_write0s rir) reg (new_grd, new_wi) |>),
      merge_failures_list
        grd
        (list_options_to_list
           [option_map fst (list_assoc (rir_write0s rir) reg);
            list_assoc (rir_read1s rir) reg;
            option_map fst (list_assoc (rir_write1s rir) reg)
           ]
        )
    ).

  Definition add_write1
             (rir: rule_information_raw) (grd: sact) (reg: reg_t) (val: sact)
    (* Returns modified rule_information_raw, failure conditions *)
    : rule_information_raw * sact :=
    let (new_grd, new_wi) :=
      match list_assoc (rir_write1s rir) reg with
      | None => (grd, [{| wcond := grd; wval := val |}])
      | Some c =>
          (uor (fst c) grd,
            (snd c)++[{| wcond := grd; wval := val |}])
      end in
    ((rir <| rir_write1s := list_assoc_set (rir_write1s rir) reg (new_grd, new_wi) |>),
      merge_failures_list grd (list_options_to_list
                                 [option_map fst (list_assoc (rir_write1s rir) reg)])).

  (* ** Extraction of actions from rule *)
  Definition reduce t (ua: option (sact)) : sact :=
    match ua with
    | None => SConst (val_of_type t)
    | Some x => x
    end.

  Fixpoint merge_branches
           (vm_tb vm_fb: list (string*nat))
           (vvs: list (nat * (type * sact)))
           (nid: nat)
           (cond_name: nat) :=
    match vm_tb, vm_fb with
    | (str, n1)::vm_tb, (_, n2)::vm_fb =>
        let '(acc, vv', nid) := merge_branches vm_tb vm_fb vvs nid cond_name in
        if eq_nat_dec n1 n2
        then ((str, n1)::acc, vv', nid)
        else
          let t :=
            match list_assoc vvs n1 with
            | Some (t, _) => t
            | None => bits_t 0
            end in
          ((str, nid)::acc,
            list_assoc_set vv' nid (t, SIf (SVar cond_name) (SVar n1) (SVar n2)),
            S nid)
    | _, _ => ([], vvs, nid)
    end.

  Definition merge_reg2vars_reg (r1 r2: list ((reg_t*Port)*nat)) reg prt cond_name r vvs nid :=
    match list_assoc r1 (reg,prt), list_assoc r2 (reg,prt) with
    | Some v1, Some v2 =>
        if eq_nat_dec v1 v2 then (list_assoc_set r (reg,prt) v1, vvs, nid)
        else
          let t :=
            match list_assoc vvs v1 with
            | Some (t, _) => t
            | None => bits_t 0
            end in
          (list_assoc_set r (reg,prt) nid,
            list_assoc_set vvs nid (t, SIf (SVar cond_name) (SVar v1) (SVar v2)),
            S nid)
    | _, _ => (r, vvs, nid)
    end.

  Fixpoint merge_reg2vars_aux ks (r1 r2: list ((reg_t*Port)*nat)) r cond_name vvs nid :=
    match ks with
    | [] => (r, vvs, nid)
    | (reg,prt)::ks =>
        let '(r, vvs, nid) := merge_reg2vars_reg r1 r2 reg prt cond_name r vvs nid in
        merge_reg2vars_aux ks r1 r2 r cond_name vvs nid
    end.

  Definition merge_reg2vars (r1 r2: list ((reg_t*Port)*nat)) cond_name vvs nid :=
    let keys := List.map fst r1 in
    merge_reg2vars_aux keys r1 r2 [] cond_name vvs nid.

  Definition gria_list
             (guard: sact)
             (rec: uact -> (list (string * type)) -> list (string * nat) ->
                   list (reg_t * Port * nat) -> list(nat * (type*sact)) ->
                   sact -> rule_information_raw -> nat ->
                   (option sact * list (string * nat) * list (reg_t * Port * nat) * list (nat * (type * sact)) * sact * rule_information_raw * nat * type))
    :=
    fix gria_list
        (args: list uact)
        (tsig: list (string * type))
        (env: list (string * nat))
        (reg2var : list (reg_t * Port * nat))
        (vvs: list (nat * (type * sact)))
        (rir: rule_information_raw)
        (nid: nat)
        names0
        fail0
      : list (nat * type) * list (string * nat) * list (reg_t * Port * nat) * list (nat * (type * sact)) * sact * rule_information_raw * nat
      :=
      match args with
        [] => (names0, env, reg2var, vvs, fail0, rir, nid)
      | a::args =>
          let '(vc, vms, reg2var, vvs, failure, rir, nid, t) :=
            rec a tsig env reg2var vvs guard rir nid in
          let arg_bind_name := nid in
          gria_list args tsig vms reg2var
                    (list_assoc_set vvs arg_bind_name (t, reduce t vc))
                    rir (S nid) ((arg_bind_name, t) :: names0) (merge_failures failure fail0)
      end.

  (* This function extracts the actions for a given rule. *)

  (*
    - ua : the original action to simplify
    - tsig : the name and type of local variables
    - env : mapping from original var name to fresh variable
    - reg2var : mapping from register-port pair to fresh variable
    - vvs : for each fresh variable, its type and simple action (sact)
    - guard : a simple action denoting the path condition we're in
    - rir : information about reads and writes performed within this rule
    - nid : the next available fresh variable name

    Returns:
    - option sact : a simple action which evaluates equivalently to the original daction
    - list (string * nat) : updated env
    - list ((reg_t * Port) * nat) : updated reg2var
    - list (nat * (type * sact)) : updated vvs
    - sact : the condition under which the action fails
    - rule_information_raw : updated rir
    - nat : updated nid
    - type : the type of the original action

   *)

  Fixpoint get_rule_information_aux
           (* No need to pass failures as these impact the whole rule - taking note of
       all of them and factoring the conditions in is enough. Conflicts between
       different actions are also dealt with here. *)
           (ua: uact)
           (tsig: list (string * type))
           (env: list (string * nat))
           (reg2var: list ((reg_t * Port) * nat))
           (vvs: list (nat * (type * sact)))
           (guard: sact)
           (rir: rule_information_raw) (nid: nat)
    (* Returns value, env, var_values, failure condition, rule_information_raw,
       next_ids *)
    : option (sact)
      * list (string * nat)
      * list ((reg_t * Port) * nat)
      * (list (nat * (type * sact)))
      * sact * rule_information_raw * nat * type
    (* TODO remove redundancies with rule_information_raw (failure_cond,
         var_values) *)
    :=
    match ua with
    | DBind var val body =>
        let '(ret_val, vm_val, reg2var, vv_val, failures_val, rir_val, nid, tval) :=
          get_rule_information_aux val tsig env reg2var vvs guard rir nid in
        let name := nid in
        let '(ret_body, vm_body, reg2var, vv_body, failures_body, rir_body, nid, tbody) :=
          get_rule_information_aux
            body ((var, tval)::tsig) ((var, name)::vm_val) reg2var
            (list_assoc_set vv_val name (tval, (reduce tval ret_val)))
            guard rir_val (S nid) in
        (ret_body, skipn 1 vm_body (* var's binding goes out of scope *),
          reg2var,
          vv_body,
          merge_failures failures_val failures_body, rir_body, nid, tbody)
    | DAssign var val =>
        let '(ret_val, vm_val, reg2var, vv_val, failures_val, rir_val, nid, t) :=
          get_rule_information_aux val tsig env reg2var vvs guard rir nid in
        let name := nid in
        (None,
          list_assoc_set vm_val var name,
          reg2var,
          list_assoc_set vv_val name (t, (reduce t ret_val)),
          failures_val, rir_val, S nid, bits_t 0
        )
    | DVar var =>
        match list_assoc env var, list_assoc tsig var with
        | Some x, Some t => (Some (SVar x), env, reg2var, vvs, const_false, rir, nid, t)
        | _, _ => (* Unreachable assuming rule valid *)
            (None, env, reg2var, vvs, const_true, rir, nid, bits_t 0)
        end
    | DSeq a1 a2 =>
        let '(_, vm_a1, reg2var, vv_a1, failures_a1, rir_a1, nid_a1, _) :=
          get_rule_information_aux a1 tsig env reg2var vvs guard rir nid in
        let '(ret_a2, vm_a2, reg2var, vv_a2, failures_a2, rir_a2, nid_a2, t) :=
          get_rule_information_aux a2 tsig vm_a1 reg2var vv_a1 guard rir_a1 nid_a1 in
        (ret_a2, vm_a2, reg2var, vv_a2, merge_failures failures_a1 failures_a2,
          rir_a2, nid_a2, t)
    | DIf cond tb fb =>
        let '(ret_cond, vm_cond, reg2var, vv_cond, failures_cond, rir_cond, nid, t) :=
          get_rule_information_aux cond tsig env reg2var vvs guard rir nid in
        let cond_name := nid in
        let guard_tb_name := (nid + 1) in
        let guard_fb_name := (nid + 2) in
        let guard_tb := uand guard (SVar cond_name) in
        let guard_fb := uand guard (unot (SVar cond_name)) in
        let vv_cond := list_assoc_set vv_cond cond_name (bits_t 1, reduce (bits_t 1) ret_cond) in
        let vv_cond := list_assoc_set vv_cond guard_tb_name (bits_t 1, guard_tb) in
        let vv_cond := list_assoc_set vv_cond guard_fb_name (bits_t 1, guard_fb) in
        let '(ret_tb, vm_tb, reg2var_tb, vv_tb, failures_tb, rir_tb, nid, t1) :=
          get_rule_information_aux tb tsig vm_cond reg2var vv_cond (SVar guard_tb_name) rir_cond
                                   (nid + 3)
        in
        let '(ret_fb, vm_fb, reg2var_fb, vv_fb, failures_fb, rir_fb, nid, t2) :=
          (* We use rir_tb here even though we know that none of the actions added
           by the other branch can impact those from this branch (they are
           mutually exclusive). This way, we don't have to deal with
           rule_information_raw merging. However, this also means that the
           failure condition will contain some redundancy. *)
          get_rule_information_aux fb tsig vm_cond reg2var vv_tb (SVar guard_fb_name) rir_tb nid
        in
        (* Merge var maps: if vm_tb and vm_fb disagree for some variable, generate
         a new variable reflecting the condition and update the variables map.
         *)
        let '(vm_merge, vvs, nid) := merge_branches vm_tb vm_fb vv_fb nid cond_name in
        let '(reg2var, vvs, nid) := merge_reg2vars reg2var_tb reg2var_fb cond_name vvs nid in
        (Some (SIf (reduce (bits_t 1) ret_cond) (reduce t1 ret_tb) (reduce t2 ret_fb)),
          vm_merge,
          reg2var,
          vvs,
          uor failures_cond
              (uor (uand (reduce (bits_t 1) ret_cond) failures_tb)
                   (uand (unot (reduce (bits_t 1) ret_cond)) failures_fb)),
          rir_fb, nid, t1)
    | DUnop ufn a =>
        let '(ret_a, vm_a, reg2var, vv_a, failures_a, rir_a, nid, t) :=
          get_rule_information_aux a tsig env reg2var vvs guard rir nid in
        (Some (SUnop ufn (reduce t ret_a)), vm_a, reg2var,
          vv_a, failures_a, rir_a, nid, ret_type_unop ufn t)
    | DBinop ufn a1 a2 =>
        let '(ret_a1, vm_a1, reg2var, vvs, failures_a1, rir_a1, nid, t1) :=
          get_rule_information_aux a1 tsig env reg2var vvs guard rir nid in
        let '(ret_a2, vm_a2, reg2var, vvs, failures_a2, rir_a2, nid, t2) :=
          get_rule_information_aux a2 tsig vm_a1 reg2var vvs guard rir_a1 nid in
        (Some (SBinop ufn (reduce t1 ret_a1) (reduce t2 ret_a2)), vm_a2, reg2var, vvs,
          merge_failures failures_a1 failures_a2, rir_a2, nid, ret_type_binop ufn t1 t2)
    | DInternalCall ufn args =>
        let '(arg_names, vm_args, reg2var, vv_args, failure_args, rir_args, nid) :=
          gria_list guard get_rule_information_aux
                    args tsig env reg2var vvs rir nid [] const_false in
        let vm_tmp :=
          combine
            (fst (split (rev (int_argspec ufn)))) (* Names from argspec *)
            (map fst arg_names) in
        let '(ret_ic, _, reg2var, vv_ic, failure_ic, rir_ic, nid, t) :=
          get_rule_information_aux (int_body ufn) (rev (int_argspec ufn)) vm_tmp reg2var vv_args guard rir_args nid in
        (* We can forget vm_tmp which contained the temporary map for use in the
         called function. *)
        (ret_ic, vm_args, reg2var, vv_ic, merge_failures failure_ic failure_args,
          rir_ic, nid, t)
    | DAPos _ e => get_rule_information_aux e tsig env reg2var vvs guard rir nid
    | DRead port reg =>
        let modified_rir :=
          match port with
          | P0 => add_read0 rir guard reg
          | P1 => add_read1 rir guard reg
          end in
        match list_assoc reg2var (reg, port) with
        | Some v => (Some (SVar v), env, reg2var, vvs, const_false, modified_rir, nid, R reg)
        | None => (None, env, reg2var, vvs, const_true, modified_rir, nid, R reg)
        end
    | DWrite port reg val =>
        let '(ret_val, vm_val, reg2var, vvs, failures_val, actions_val, nid, t) :=
          get_rule_information_aux val tsig env reg2var vvs guard rir nid in
        let '(rir_wr, failure_wr) :=
          match port with
          | P0 => add_write0 actions_val guard reg (reduce t ret_val)
          | P1 => add_write1 actions_val guard reg (reduce t ret_val)
          end
        in
        let '(reg2var, vvs, nid, t) :=
          match port with
          | P0 =>
              let v_read1 := nid in
              let nid := nid + 1 in
              let vvs := list_assoc_set vvs v_read1 (t, reduce t ret_val) in
              let reg2var := list_assoc_set reg2var (reg, P1) v_read1 in
              (reg2var, vvs, nid, t)
          | P1 => (reg2var, vvs, nid, t)
          end in
        (None, vm_val, reg2var, vvs, merge_failures failures_val failure_wr, rir_wr,
          nid, bits_t 0)
    | DExternalCall ufn arg =>
        let '(ret_arg, vm_arg, reg2var, vv_arg, failures_arg, rir, nid, t) :=
          get_rule_information_aux arg tsig env reg2var vvs guard rir nid in
        let name := nid in
        (Some (SVar name), vm_arg, reg2var,
          list_assoc_set vv_arg name (retSig (Sigma ufn), SExternalCall ufn (reduce t ret_arg)),
          failures_arg, rir,
          S nid, retSig (Sigma ufn))
    | DError _ => (None, env, reg2var, vvs, const_true, rir, nid, bits_t 0)
    | DFail tau => (None, env, reg2var, vvs, const_true, rir, nid, tau)
    | @DConst _ _ _ _ _ tau c =>
        (Some (SConst (BitsToLists.val_of_value c)), env, reg2var, vvs, const_false, rir, nid, tau)
    end.

  Inductive var_in_sact : sact -> nat -> Prop :=
  | var_in_sact_var v: var_in_sact (SVar v) v
  | var_in_if_cond c t f v:
    var_in_sact c v ->
    var_in_sact (SIf c t f) v
  | var_in_if_true c t f v:
    var_in_sact t v ->
    var_in_sact (SIf c t f) v
  | var_in_if_false c t f v:
    var_in_sact f v ->
    var_in_sact (SIf c t f) v
  | var_in_sact_unop ufn a v:
    var_in_sact a v -> var_in_sact (SUnop ufn a) v
  | var_in_sact_binop_1 ufn a1 a2 v:
    var_in_sact a1 v -> var_in_sact (SBinop ufn a1 a2) v
  | var_in_sact_binop_2 ufn a1 a2 v:
    var_in_sact a2 v -> var_in_sact (SBinop ufn a1 a2) v
  | var_in_sact_external ufn a v: var_in_sact a v -> var_in_sact (SExternalCall ufn a) v.

  Definition same_env env1 env2 :=
    Forall2 (fun x y : string * nat => fst x = fst y) env1 env2.

  Lemma same_env_set_in:
    forall env' env
           (SAMEENV: same_env env env')
           v n
           (VARIN: In v (map fst env)) ,
      same_env env (list_assoc_set env' v n).
  Proof.
    Opaque eq_dec.
    induction env'; simpl; intros; eauto.
    - inv SAMEENV. simpl in *; easy.
    - inv SAMEENV. simpl in *. destr. simpl in *. subst.
      destr.
      + subst. simpl. constructor. reflexivity. auto.
      + constructor. reflexivity. eapply IHenv'. eauto. destruct VARIN; congruence.
  Qed.

  Lemma same_env_trans:
    forall l1 l2,
      same_env l1 l2 -> forall l3, same_env l2 l3 -> same_env l1 l3.
  Proof.
    eapply Forall2_trans. congruence.
  Qed.

  Lemma same_env_refl:
    forall (l: list (string * nat)),
      same_env l l.
  Proof.
    unfold same_env; induction l; simpl; intros; eauto.
  Qed.

  Lemma same_env_sym:
    forall (l1 l2: list (string * nat)),
      same_env l1 l2 ->
      same_env l2 l1.
  Proof.
    unfold same_env.
    induction 1; simpl; intros; eauto.
  Qed.

  Lemma merge_vms_preserve_same_env:
    forall (l2 l4: list (string*nat))
           (F: same_env l2 l4)
           (l3: list (nat*(type*sact))) cname n1 env' vvs n2,
      merge_branches l2 l4 l3 n1 cname = (env', vvs, n2) ->
      same_env l2 env'.
  Proof.
    induction 1; simpl; intros; eauto.
    - inv H. constructor.
    - do 4 destr_in H0. apply IHF in Heqp1.
      destr_in H0. inv H0. constructor; auto.
      inv H0. constructor; auto.
  Qed.

  Lemma fst_split_map:
    forall {A B: Type} (l: list (A*B)),
      fst (split l) = map fst l.
  Proof.
    induction l; simpl; intros; eauto. repeat destr. subst. simpl. f_equal.
    simpl in IHl. auto.
  Qed.

  Definition valid_name name nid :=
    name < nid.

  Lemma valid_name_incr:
    forall name n1 n2 (INCR: n1 <= n2),
      valid_name name n1 -> valid_name name n2.
  Proof.
    unfold valid_name. intros; lia.
  Qed.

  Definition vvs_range (vvs: list (nat * (type * sact))) (nid: nat) :=
    forall x y,
      list_assoc vvs x = Some y -> valid_name x nid.

  Lemma vvs_range_list_assoc_set:
    forall vvs n name v,
      vvs_range vvs n ->
      valid_name name n ->
      vvs_range (list_assoc_set vvs name v) n.
  Proof.
    unfold vvs_range; simpl; intros.
    destruct (eq_dec name x). subst.
    rewrite list_assoc_gss in H1. inv H1; eauto.
    rewrite list_assoc_gso in H1; eauto.
  Qed.

  Lemma vvs_range_incr:
    forall vvs n1 n2 (INCR: n1 <= n2),
      vvs_range vvs n1 -> vvs_range vvs n2.
  Proof.
    unfold vvs_range; simpl; intros; eauto using valid_name_incr.
  Qed.

  Lemma vvs_range_none:
    forall l n name,
      vvs_range l n ->
      ~ valid_name name n ->
      list_assoc l name = None.
  Proof.
    unfold vvs_range; intros.
    destruct (list_assoc l name) eqn:?; eauto. eapply H in Heqo; eauto. congruence.
  Qed.

  Definition var_lt (v1 v2: nat) :=
    v1 < v2.

  Lemma var_lt_gen_r:
    forall s n n' ,
      n <= n' ->
      var_lt s n ->
      var_lt s n'.
  Proof.
    unfold var_lt; intros; lia.
  Qed.

  Definition vvs_smaller_variables (vvs: list (nat * (type * sact))) :=
    forall (v : nat) (t: type) (a : sact),
      list_assoc vvs v = Some (t, a) ->
      forall v' : nat, var_in_sact a v' -> var_lt v' v.

  Definition vvs_grows (vvs1 vvs2: list (nat * (type*sact))) :=
    forall x y, list_assoc vvs1 x = Some y -> list_assoc vvs2 x = Some y.

  Lemma vvs_grows_refl: forall v, vvs_grows v v.
  Proof.
    red; auto.
  Qed.

  Lemma vvs_grows_trans:
    forall v1 v2,
      vvs_grows v1 v2 ->
      forall v3,
        vvs_grows v2 v3 ->
        vvs_grows v1 v3.
  Proof.
    unfold vvs_grows; intros; eauto.
  Qed.


  Lemma vvs_grows_interp_sact:
    forall v1 v2 a v,
      vvs_grows v1 v2 ->
      interp_sact v1 a v ->
      interp_sact v2 a v.
  Proof.
    induction 2; simpl; intros; eauto; try now (econstructor; eauto).
  Qed.

  Lemma vvs_grows_set:
    forall vvs n k l,
      vvs_range vvs n ->
      k >= n ->
      vvs_grows vvs (list_assoc_set vvs k l).
  Proof.
    red; intros.
    rewrite list_assoc_gso; eauto.
    eapply H in H1. red in H1. lia.
  Qed.

  Lemma wt_sact_fold_uor:
    forall conds vvs,
      Forall (fun a => wt_sact vvs a (bits_t 1)) conds ->
      forall ci,
        wt_sact vvs ci (bits_t 1) ->
        wt_sact vvs (fold_left uor conds ci) (bits_t 1).
  Proof.
    induction 1; simpl; intros; eauto.
    apply IHForall. econstructor; eauto. constructor.
  Qed.

  Lemma wt_sact_or_conds:
    forall conds vvs,
      Forall (fun a => wt_sact vvs a (bits_t 1)) conds ->
      wt_sact vvs (or_conds conds) (bits_t 1).
  Proof.
    intros; eapply wt_sact_fold_uor; eauto.
    repeat constructor.
  Qed.

  Definition env_vvs (env: list (string * nat)) (vvs: list (nat * (type * sact))) (tsig: tsig string) :=
    Forall2 (fun '(var1, fv) '(var2, t) =>
               var1 = var2 /\ exists s, list_assoc vvs fv = Some (t, s)
            ) env tsig.

  Lemma env_vvs_ex:
    forall env vvs tsig (EV: env_vvs env vvs tsig)
           x v t
           (GET1: list_assoc env x = Some v)
           (GET2: list_assoc tsig x = Some t),
    exists s, list_assoc vvs v = Some (t, s).
  Proof.
    induction 1; simpl; intros; eauto. inv GET1.
    repeat destr_in H. subst.
    destruct H as (EQ & (ss & GET3)). subst.
    destr_in GET1. inv GET1; inv GET2. eauto.
    eauto.
  Qed.

  Lemma env_vvs_some_none:
    forall env vvs tsig,
      env_vvs env vvs tsig ->
      forall v n,
        list_assoc env v = Some n ->
        list_assoc tsig v = None ->
        False.
  Proof.
    induction 1; simpl; intros; eauto. easy.
    repeat destr_in H. destruct H as (? & ? & ?). subst.
    repeat destr_in H1. easy. eauto.
  Qed.

  Lemma env_vvs_set:
    forall env vvs tsig,
      env_vvs env vvs tsig ->
      forall  v n t a,
        list_assoc tsig v = Some t ->
        vvs_range vvs n ->
        env_vvs (list_assoc_set env v n) (list_assoc_set vvs n (t, a)) tsig.
  Proof.
    induction 1; simpl; intros; eauto. easy.
    repeat destr_in H. destruct H as (EQ & ss & GET). subst.
    destr_in H1; inv H1.
    + constructor. split; auto. rewrite list_assoc_gss; eauto.
      eapply Forall2_impl. eauto.
      simpl; intros; eauto.
      repeat destr_in H3. destruct H3 as (? & ? & GET2). subst. split; eauto.
      rewrite list_assoc_gso; eauto.
      intro; subst.
      eapply H2 in GET2. red in GET2. lia.
    + constructor. split; auto. rewrite list_assoc_gso. eauto.
      eapply H2 in GET. red in GET. lia.
      eapply Forall2_impl.
      eapply IHForall2. eauto. auto.
      simpl; intros. repeat destr_in H4. destruct H4 as (? & ? & GET2). eauto.
  Qed.

  Lemma env_vvs_change_vvs:
    forall env vvs tsig,
      env_vvs env vvs tsig ->
      forall n k v,
        vvs_range vvs n ->
        k >= n ->
        env_vvs env (list_assoc_set vvs k v) tsig.
  Proof.
    induction 1; simpl; intros; eauto. constructor.
    repeat destr_in H. destruct H as (? & ? & ?). subst.
    constructor; eauto.
    - split; auto. rewrite list_assoc_gso. eauto.
      apply H1 in H3. red in H3. lia.
    - eapply IHForall2; eauto.
  Qed.
  Lemma env_vvs_vvs_grows:
    forall env vvs tsig,
      env_vvs env vvs tsig ->
      forall vvs' ,
        vvs_grows vvs vvs' ->
        env_vvs env vvs' tsig.
  Proof.
    induction 1; simpl; intros; eauto. constructor.
    repeat destr_in H. destruct H as (? & ? & ?). subst.
    constructor; eauto.
    eapply Forall2_impl; eauto. simpl. intros (?&?) (?&?) IN1 IN2 (? & ? & ?). subst. eauto.
  Qed.

  Lemma vvs_smaller_variables_set:
    forall vvs,
      vvs_smaller_variables vvs ->
      forall n t a,
        (forall v, var_in_sact a v -> v < n) ->
        vvs_smaller_variables (list_assoc_set vvs n (t, a)).
  Proof.
    red; intros.
    rewrite list_assoc_spec in H1. destr_in H1. inv H1. red. eauto.
    eauto.
  Qed.

  Lemma wt_sact_vvs_set:
    forall vvs s t,
      wt_sact vvs s t ->
      forall k v n,
        vvs_range vvs n ->
        k >= n ->
        wt_sact (list_assoc_set vvs k v) s t.
  Proof.
    induction 1; simpl; intros; eauto.
    - econstructor. rewrite list_assoc_gso; eauto. apply H0 in H. red in H; lia.
    - econstructor; eauto.
    - econstructor; eauto.
    - econstructor; eauto.
    - econstructor; eauto.
    - econstructor; eauto.
  Qed.

  Definition wt_vvs (vvs: list (nat * (type * sact))) :=
    forall v s t,
      list_assoc vvs v = Some (t, s) ->
      wt_sact vvs s t.

  Lemma wt_vvs_set:
    forall vvs n,
      wt_vvs vvs ->
      vvs_range vvs n ->
      forall k t v,
        wt_sact vvs v t ->
        k >= n ->
        wt_vvs (list_assoc_set vvs k (t, v)).
  Proof.
    red; intros.
    rewrite list_assoc_spec in H3.
    destr_in H3; eauto.
    inv H3.
    eapply wt_sact_vvs_set; eauto.
    eapply wt_sact_vvs_set; eauto.
  Qed.

  Lemma wt_sact_vvs_grows:
    forall vvs vvs' ,
      vvs_grows vvs vvs' ->
      forall s t,
        wt_sact vvs s t ->

        wt_sact vvs' s t.
  Proof.
    induction 2; simpl; intros; eauto.
    - eapply H in H0. econstructor; eauto.
    - constructor; auto.
    - econstructor; eauto.
    - econstructor; eauto.
    - econstructor; eauto.
    - econstructor; eauto.
  Qed.

  Lemma wt_sact_reduce:
    forall vvs t o,
      (forall x, o = Some x -> wt_sact vvs x t) ->
      wt_sact vvs (reduce t o) t.
  Proof.
    intros.
    destruct o. simpl. eauto.
    simpl. constructor. apply wt_val_of_type.
  Qed.

  Fixpoint size_sact (s: sact) : nat :=
    match s with
      SVar _ => 0
    | SConst _ => 0
    | SIf c t f => 1 + size_sact c + size_sact t + size_sact f
    | SUnop _ a => 1 + size_sact a
    | SBinop _ a b => 1 + size_sact a + size_sact b
    | SExternalCall _ a => 1 + size_sact a
    end.

  Definition order_sact :=
    Relation_Operators.lexprod
      nat (fun _ => sact)
      (fun s1 s2 => s1 < s2)
      (fun s s1 s2 => size_sact s1 < size_sact s2).

  Lemma wf_order_sact:
    well_founded (order_sact).
  Proof.
    apply wf_lexprod.
    - apply lt_wf.
    - intros. apply wf_inverse_image. apply lt_wf.
  Qed.

  Lemma wt_sact_interp':
    forall vvs,
      wt_vvs vvs ->
      vvs_smaller_variables vvs ->
      forall n a t,
      (forall v, var_in_sact a v -> v < n) ->
      wt_sact vvs a t ->
      exists v, interp_sact vvs a v /\ wt_val t v.
  Proof.
    intros vvs WTvvs VSV n a.
    change n with (projT1 (existT (fun _ => sact) n a)).
    change a with (projT2 (existT (fun _ => sact) n a)) at 1 3 4.
    generalize (existT (fun _ => sact) n a).
    clear n a. intro s. pattern s.
    eapply well_founded_induction.
    apply wf_order_sact. clear s.
    intros x IH t BELOW WTs.
    destruct x; simpl in *.
    inv WTs.
    - trim (BELOW var). constructor.
      generalize (VSV _ _ _ H). intros.
      edestruct (IH (existT _ var s0)) as (v & IS & WTv).
      + red. apply Relation_Operators.left_lex. simpl. auto.
      + simpl. eauto.
      + simpl. eapply WTvvs; eauto.
      + eexists; split. econstructor; eauto. auto.
    - eexists. split. econstructor. auto.
    - edestruct (IH) as (vc & ISc & WTvc); simpl; eauto.
      {
        red. apply Relation_Operators.right_lex. instantiate (1:=c). simpl; lia.
      }
      {
        simpl. intros; eapply BELOW. constructor. auto.
      }
      simpl. eauto. simpl in *.
      inv WTvc. destruct bs; simpl in H3; try lia.
      destruct bs; simpl in H3; try lia.
      edestruct (fun n => IH (existT _ n (if b then bt else bf))) as (vb & ISb & WTb); simpl; eauto.
      {
        red. apply Relation_Operators.right_lex. simpl; destruct b; lia.
      }
      {
        simpl. intros; eapply BELOW.
        destruct b. eapply var_in_if_true. eauto. eapply var_in_if_false; eauto.
      }
      destruct b; eauto. simpl in ISb.
      eexists; split. econstructor; eauto. auto.
    - edestruct (IH) as (vc & ISc & WTvc); simpl; eauto.
      {
        red. apply Relation_Operators.right_lex. instantiate (1:=a). simpl; lia.
      }
      {
        simpl. intros; eapply BELOW. constructor. auto.
      }
      simpl. eauto. simpl in *.
      edestruct wt_unop_interp as (v2 & SIG1); eauto.
      eexists; split. econstructor; eauto.
      eapply wt_unop_sigma1; eauto.
    - edestruct (fun n=> IH (existT _ n a1)) as (vc & ISc & WTvc); simpl; eauto.
      {
        red. apply Relation_Operators.right_lex. simpl; lia.
      }
      {
        simpl. intros; eapply BELOW. constructor. auto.
      }
      simpl. eauto. simpl in *.
      edestruct (fun n => IH (existT _ n a2)) as (vc2 & ISc2 & WTvc2); simpl; eauto.
      {
        red. apply Relation_Operators.right_lex. simpl; lia.
      }
      {
        simpl. intros; eapply BELOW. eapply var_in_sact_binop_2; eauto.
      }
      simpl in *.
      edestruct wt_binop_interp as (v2 & SIG2); eauto.
      eexists; split. econstructor; eauto.
      eapply wt_binop_sigma1; eauto.
    - edestruct (IH) as (vc & ISc & WTvc); simpl; eauto.
      {
        red. apply Relation_Operators.right_lex. instantiate (1:=a). simpl; lia.
      }
      {
        simpl. intros; eapply BELOW. constructor. auto.
      }
      simpl. eauto. simpl in *.
      eexists; split. econstructor; eauto.
      eapply wt_sigma; eauto.
  Qed.

  Lemma wt_sact_valid_vars:
    forall vvs n
      (WFS: vvs_range vvs n)
      a t
      (WTGUARD: wt_sact vvs a t),
      forall v, var_in_sact a v -> v < n.
  Proof.
    intros vvs n WFS.
    induction 1; simpl; intros; eauto.
    - inv H0. eapply WFS in H; eauto.
    - inv H0.
    - inv H; eauto.
    - inv H0; eauto.
    - inv H0; eauto.
    - inv H; eauto.
  Qed.

  Lemma wt_sact_interp:
    forall vvs,
      wt_vvs vvs ->
      vvs_smaller_variables vvs ->
      forall n a t,
        vvs_range vvs n ->
        wt_sact vvs a t ->
      exists v, interp_sact vvs a v /\ wt_val t v.
  Proof.
    intros.
    eapply wt_sact_interp'; eauto.
    eapply wt_sact_valid_vars; eauto.
  Qed.

  Lemma wt_val_determ:
    forall v t1 t2,
      wt_val t1 v ->
      wt_val t2 v ->
      t1 = t2.
  Proof.
    induction v using val_ind'; simpl; intros; eauto.
    - inv H. inv H0. auto.
    - inv H. inv H0. auto.
    - inv H0. inv H1. auto.
    - inv H0. inv H1. auto.
  Qed.

  Lemma interp_sact_wt:
    forall vvs,
      wt_vvs vvs ->
      vvs_smaller_variables vvs ->
      forall (n : nat) (a : sact) (t : type),
        vvs_range vvs n ->
        wt_sact vvs a t ->
        forall v,
        interp_sact vvs a v ->
        wt_val t v.
  Proof.
    intros.
    edestruct wt_sact_interp as (x & IV & WTv); eauto.
    exploit interp_sact_determ. apply H3. apply IV. intros ->; auto.
  Qed.

  Lemma interp_sact_list_assoc_set:
    forall vvs,
      wt_vvs vvs ->
      vvs_smaller_variables vvs ->
      forall n a x v,
        (forall v, var_in_sact a v -> v < n) ->
        forall m,
          n <= m ->
          interp_sact (list_assoc_set vvs m x) a v -> interp_sact vvs a v.
  Proof.
    intros vvs WTvvs VSV n a.
    change n with (projT1 (existT (fun _ => sact) n a)).
    change a with (projT2 (existT (fun _ => sact) n a)) at 1 4 5.
    generalize (existT (fun _ => sact) n a).
    clear n a. intro s. pattern s.
    eapply well_founded_induction.
    apply wf_order_sact. clear s.
    intros x IH t vv BELOW m LE INTERP.
    destruct x; simpl in *.
    inv INTERP.
    - trim (BELOW var). constructor. rewrite list_assoc_gso in H by lia.
      econstructor; eauto.
      generalize (VSV _ _ _ H). intros.
      eapply (IH (existT _ var a)). 4: simpl; eauto.
      + red. apply Relation_Operators.left_lex. auto.
      + simpl. eauto.
      + simpl. lia.
    - constructor.
    - exploit IH.
      + red. apply Relation_Operators.right_lex. instantiate (1:=c). simpl; lia.
      + simpl. intros; eapply BELOW. constructor. auto.
      + simpl. eauto.
      + simpl. eauto.
      + exploit (IH (existT _ x (if b then t0 else f))).
        * red. apply Relation_Operators.right_lex. simpl; destruct b; lia.
        * simpl. intros; eapply BELOW.
          destruct b. eapply var_in_if_true. eauto. eapply var_in_if_false; eauto.
        * simpl. eauto.
        * simpl. eauto.
        * simpl. intros.
          econstructor; eauto.
    - exploit IH.
      + red. apply Relation_Operators.right_lex. instantiate (1:=a). simpl; lia.
      + simpl. intros; eapply BELOW. constructor. auto.
      + simpl. eauto.
      + simpl in *. eauto.
      + simpl; auto. intros. econstructor; eauto.
    - exploit IH.
      + red. apply Relation_Operators.right_lex. instantiate (1:=a1). simpl; lia.
      + simpl. intros; eapply BELOW. constructor. auto.
      + simpl. eauto.
      + simpl in *. eauto.
      + exploit IH.
        * red. apply Relation_Operators.right_lex. instantiate (1:=a2). simpl; lia.
        * simpl. intros; eapply BELOW. eapply var_in_sact_binop_2; eauto.
        * simpl. eauto.
        * simpl in *. eauto.
        * simpl; auto. intros. econstructor; eauto.
    - exploit IH.
      + red. apply Relation_Operators.right_lex. instantiate (1:=a). simpl; lia.
      + simpl. intros; eapply BELOW. constructor. auto.
      + simpl. eauto.
      + simpl in *. eauto.
      + simpl; auto. intros. econstructor; eauto.
  Qed.
 
  Lemma interp_sact_list_assoc_set':
    forall vvs,
      wt_vvs vvs ->
      vvs_smaller_variables vvs ->
      forall n a x v,
        vvs_range vvs n ->
        (forall v, var_in_sact a v -> v < n) ->
        interp_sact (list_assoc_set vvs n x) a v <-> interp_sact vvs a v.
  Proof.
    intros; split.
    eapply interp_sact_list_assoc_set; eauto.
    intros; eapply vvs_grows_interp_sact; eauto.
    eapply vvs_grows_set; eauto.
  Qed.

  Definition match_Gamma_env (Gamma: list (string * val)) (env: list (string * nat)) vvs :=
    Forall2 (fun x y =>
               fst x = fst y /\ interp_sact vvs (SVar (snd y)) (snd x)
            ) Gamma env.

  Lemma merge_branches_grows:
    forall vm_tb vm_fb vvs nid cond_name vm' vvs' nid' tsig
           (MB: merge_branches vm_tb vm_fb vvs nid cond_name = (vm', vvs', nid'))
           (ENVVVS1: env_vvs vm_tb vvs tsig)
           (ENVVVS2: env_vvs vm_fb vvs tsig)
           (RNGVVS: vvs_range vvs nid)
           (VVSVALID: vvs_smaller_variables vvs)
           (VALIDCOND: valid_name cond_name nid)
           (WTCOND: wt_sact vvs (SVar cond_name) (bits_t 1))
           (WTVVS: wt_vvs vvs),
      vvs_grows vvs vvs'
      /\ vvs_range vvs' nid'
      /\ env_vvs vm' vvs' tsig
      /\ nid <= nid'
      /\ vvs_smaller_variables vvs'
      /\ wt_vvs vvs'
      /\ Forall2 (fun '(xt,xf) x =>
                    forall b,
                      interp_sact vvs' (SVar cond_name) (Bits 1 [b]) ->
                      (forall v,
                          interp_sact vvs' (SVar (snd (if b then xt else xf))) v
                          <-> interp_sact vvs' (SVar (snd x)) v)
                 ) (combine vm_tb vm_fb) vm'.
  Proof.
    induction vm_tb; simpl; intros; eauto.
    - inv MB. repeat split; eauto using vvs_grows_refl.
    - repeat destr_in MB; inv MB. now auto.
      + inv ENVVVS1. inv ENVVVS2. destruct y.
        destruct H1 as ( ? & ? & GET1).
        destruct H4 as ( ? & ? & GET2). subst.
        edestruct IHvm_tb as (VVSGROWS3 & VVSRANGE3 & ENVVVS3 & NIDGROWS3 & VVSVALID3 & WTVVS3 & EVAL3); eauto.
        repeat split; auto.
        constructor; eauto.
        constructor; eauto.
        intros. destr; tauto.
      + inv ENVVVS1. inv ENVVVS2. destruct y.
        destruct H1 as ( ? & ? & GET1).
        destruct H4 as ( ? & ? & GET2). subst.
        edestruct IHvm_tb as (VVSGROWS3 & VVSRANGE3 & ENVVVS3 & NIDGROWS3 & VVSVALID3 & WTVVS3 & EVAL3); eauto.
        repeat split; auto.
        * eapply vvs_grows_trans; eauto. eapply vvs_grows_set; eauto.
        * eapply vvs_range_list_assoc_set. eapply vvs_range_incr. 2: eauto. lia. red; lia.
        * constructor. split; auto. rewrite list_assoc_gss.  assert (t = t0) by congruence. subst; eauto.
          eapply env_vvs_change_vvs. eauto. eauto. lia.
        * eapply vvs_smaller_variables_set; eauto.
          intros v VIS. inv VIS.
          -- inv H4. red in VALIDCOND; lia.
          -- inv H4. apply RNGVVS in Heqo. red in Heqo. lia.
          -- inv H4. apply RNGVVS in GET2. red in GET2. lia.
        * eapply wt_vvs_set; eauto.
          rewrite GET1 in Heqo; inv Heqo.
          econstructor; eauto.
          eapply wt_sact_vvs_grows; eauto.
          econstructor. eapply VVSGROWS3; eauto.
          econstructor. eapply VVSGROWS3; eauto.
        * constructor; eauto.
          -- intros.
             (* rewrite list_assoc_gso in H1. 2: red in VALIDCOND; lia. *)
             split; intros IS.
             ++ (* inv IS. rewrite list_assoc_gso in H0. simpl. *)
               econstructor. rewrite list_assoc_gss. eauto.
               econstructor. eauto. destruct b; eauto.
             ++ simpl in IS. inv IS. rewrite list_assoc_gss in H1. inv H1.
                inv H2.
                exploit interp_sact_determ. apply H. apply H7. intro A; inv A.
                destruct b0; eauto.
          -- eapply Forall2_impl. eauto. simpl; intros.
             repeat destr_in H1.
             intros.
             rewrite interp_sact_list_assoc_set' in H2; eauto.
             rewrite interp_sact_list_assoc_set'; eauto.
             rewrite interp_sact_list_assoc_set'; eauto.
             inversion 1; subst.
             exploit @Forall2_Forall. apply ENVVVS3.
             rewrite Forall_forall; intro F.
             destruct (F _ H0) as ( yy & IN & EQ).
             repeat destr_in EQ. subst. destruct EQ as (? & ? & GET). subst.
             eapply VVSRANGE3 in GET. red in GET; simpl; lia.
             inversion 1; subst.
             destr.
             exploit @Forall2_Forall. apply H3.
             rewrite Forall_forall; intro F.
             destruct (F _ (in_combine_l _ _ _ _ H)) as ( yy & IN & EQ).
             repeat destr_in EQ. subst. destruct EQ as (? & ? & GET). subst.
             eapply RNGVVS in GET. red in GET; simpl; lia.
             exploit @Forall2_Forall. apply H6.
             rewrite Forall_forall; intro F.
             destruct (F _ (in_combine_r _ _ _ _ H)) as ( yy & IN & EQ).
             repeat destr_in EQ. subst. destruct EQ as (? & ? & GET). subst.
             eapply RNGVVS in GET. red in GET; simpl; lia.
             inversion 1; subst. red in VALIDCOND. lia.
             
      + inv ENVVVS1. destr_in H1. decompose [ex and] H1. congruence.
  Qed.
        
  Definition reg2var_vvs (reg2var: list (reg_t * Port * nat)) (vvs: list (nat * (type * sact))) :=
    forall x, exists y, list_assoc reg2var x = Some y /\ exists z, list_assoc vvs y = Some (R (fst x), z).

  Lemma reg2var_vvs_grows:
    forall r2v vvs1 vvs2,
      reg2var_vvs r2v vvs1 ->
      vvs_grows vvs1 vvs2 ->
      reg2var_vvs r2v vvs2.
  Proof.
    unfold reg2var_vvs; intros.
    edestruct H as (y & GET & z & GET2). eauto.
  Qed.

  Lemma reg2var_vvs_set:
    forall r2v vvs r v,
      reg2var_vvs r2v vvs ->
      (exists z : sact, list_assoc vvs v = Some (R (fst r), z)) ->
      reg2var_vvs (list_assoc_set r2v r v) vvs.
  Proof.
    red; intros.
    rewrite list_assoc_spec.
    destr; eauto. subst. eexists; split; eauto.
  Qed.

  Definition do_read (sched_log action_log: Log REnv) reg prt :=
    match prt with
      P0 => getenv REnv r reg
    | P1 =>
        match latest_write0 (V:=val) (log_app action_log sched_log) reg with
          None => getenv REnv r reg
        | Some v => v
        end
    end.

  Record match_logs_r2v
         (r2v: list (reg_t * Port * nat))
         (vvs: list (nat * (type*sact)))
         (rir: rule_information_raw)
         (sched_log action_log: Log REnv)
    :=
    {
      mlr_read:
      forall reg prt n,
        may_read sched_log prt reg = true ->
        list_assoc r2v (reg, prt) = Some n ->
        interp_sact vvs (SVar n) (do_read sched_log action_log reg prt);
      mlr_read1:
      forall idx,
        log_existsb (log_app action_log sched_log) idx is_read1 = false ->
        forall c,
          list_assoc (rir_read1s rir) idx = Some c ->
          interp_sact vvs c (Bits 1 [false]);
      mlr_write0:
      forall idx,
        log_existsb (log_app action_log sched_log) idx is_write0 = false ->
        forall g wil,
          list_assoc (rir_write0s rir) idx = Some (g, wil) ->
          forall wi,
            In wi wil ->
            interp_sact vvs (wcond wi) (Bits 1 [false]);
      mlr_write1:
      forall idx,
        log_existsb (log_app action_log sched_log) idx is_write1 = false ->
        forall g wil,
          list_assoc (rir_write1s rir) idx = Some (g, wil) ->
          forall wi,
            In wi wil ->
            interp_sact vvs (wcond wi) (Bits 1 [false]);
    }.

  Lemma merge_reg2var_reg_grows:
    forall reg prt r2v_tb r2v_fb r2v vvs nid cond_name r2v' vvs' nid'
           (MB: merge_reg2vars_reg r2v_tb r2v_fb reg prt cond_name r2v vvs nid = (r2v', vvs', nid'))
           (ENVVVS1: reg2var_vvs r2v_tb vvs)
           (ENVVVS2: reg2var_vvs r2v_fb vvs)
           (ENVVVSR: forall x y, list_assoc r2v x = Some y -> exists z, list_assoc vvs y = Some (R (fst x), z))
           (RNGVVS: vvs_range vvs nid)
           (VVSVALID: vvs_smaller_variables vvs)
           (VALIDCOND: valid_name cond_name nid)
           (WTCOND: wt_sact vvs (SVar cond_name) (bits_t 1))
           (WT: wt_vvs vvs)
    ,
      vvs_grows vvs vvs'
      /\ vvs_range vvs' nid'
      /\ (forall x y, list_assoc r2v' x = Some y -> exists z, list_assoc vvs' y = Some (R (fst x), z))
      /\ (incl ((reg,prt)::map fst r2v) (map fst r2v'))
      /\ nid <= nid'
      /\ vvs_smaller_variables vvs'
      /\ wt_vvs vvs'
      /\ forall rir sched_log action_log
                (MLR: match_logs_r2v r2v vvs rir sched_log action_log)
                (R2VOK: 
                  forall b n,
                    interp_sact vvs (SVar cond_name) (Bits 1 [b]) ->
                    may_read sched_log prt reg = true ->
                    list_assoc (if b then r2v_tb else r2v_fb) (reg,prt) = Some n ->
                    interp_sact vvs (SVar n) (do_read sched_log action_log reg prt)),
        match_logs_r2v r2v' vvs' rir sched_log action_log.
  Proof.
    intros.
    unfold merge_reg2vars_reg in MB.
    repeat destr_in MB; inv MB; eauto using vvs_grows_refl.
    - repeat refine (conj _ _); eauto using vvs_grows_refl.
      intros. rewrite list_assoc_spec in H; destr_in H; eauto.
      subst. inv H.
      edestruct ENVVVS1 as (? & GET1 & ? & GET2). setoid_rewrite Heqo in GET1; inv GET1. eauto.
      red; intros. simpl in H; destruct H. subst.
      apply list_assoc_set_key_in.
      eapply list_assoc_set_key_stays_in; eauto.
      + intros.
        exploit wt_sact_interp. 4: apply WTCOND. auto. auto. eauto.
        intros (v & ISV & WTV). edestruct wt_val_bool. eauto. subst.
        specialize (fun n => R2VOK _ n ISV).
        split; eauto.
        * intros reg0 prt0 n MR GET.
          rewrite list_assoc_spec in GET. destr_in GET.
          -- inv GET. clear Heqs0. inv e.
             exploit R2VOK. eauto. destr; eauto. tauto.
          -- eapply MLR; eauto.
        * intros; eapply mlr_read1; eauto.
        * intros; eapply mlr_write0; eauto.
        * intros; eapply mlr_write1; eauto.
    - repeat refine (conj _ _); eauto using vvs_grows_refl.
      + red; intros. rewrite list_assoc_gso; eauto.
        intro; subst. eapply RNGVVS in H.  red in H.  lia.
      + eapply vvs_range_list_assoc_set; eauto.
        eapply vvs_range_incr. 2: eauto. lia.
        red; lia.
      + edestruct (ENVVVS1) as (z & IN & ? & IN2).
        setoid_rewrite Heqo in IN. inv IN.
        intros. rewrite list_assoc_spec in H. destr_in H. inv H.
        rewrite list_assoc_gss.
        rewrite Heqo1 in IN2. inv IN2. eauto.
        rewrite list_assoc_gso. eauto.
        edestruct ENVVVSR; eauto. eapply RNGVVS in H0; red in H0. lia.
      + red; intros. simpl in H; destruct H.
        subst. apply list_assoc_set_key_in.
        eapply list_assoc_set_key_stays_in; eauto.
      + red; intros. rewrite list_assoc_spec in H. destr_in H; inv H; eauto.
        red in VVSVALID.
        inv H0.
        -- inv H4. red in VALIDCOND; red; lia.
        -- inv H4; eauto.
           edestruct ENVVVS1 as (? & IN & ? & IN').
           setoid_rewrite Heqo in IN; inv IN.
           apply RNGVVS in IN'. auto.
        -- inv H4; eauto.
           edestruct ENVVVS2 as (? & IN & ? & IN').
           setoid_rewrite Heqo0 in IN; inv IN.
           apply RNGVVS in IN'. auto.
      + eapply wt_vvs_set; eauto.
        edestruct ENVVVS1 as (? & IN & ? & IN').
        setoid_rewrite Heqo in IN; inv IN.
        edestruct ENVVVS2 as (? & IN & ? & IN'').
        setoid_rewrite Heqo0 in IN; inv IN.
        rewrite Heqo1 in IN'; inv IN'.
        econstructor; eauto.
        econstructor; eauto.
        econstructor; eauto.
      + intros.
        exploit wt_sact_interp. 4: apply WTCOND. auto. auto. eauto.
        intros (v & ISV & WTV). edestruct wt_val_bool. eauto. subst.
        split.
        * intros reg0 prt0 n2 MR GET.
          rewrite list_assoc_spec in GET. destr_in GET.
          -- inv GET. clear Heqs0. inv e.
             exploit R2VOK. eauto. eauto.
             instantiate (1:=if x then n else n0). destr; eauto.
             intro IS.
             econstructor. rewrite list_assoc_gss. eauto.
             eapply vvs_grows_interp_sact.
             eapply vvs_grows_set; eauto.
             econstructor. eauto. destr; auto.
          -- inv MLR. eapply vvs_grows_interp_sact. 2: eauto.
             eapply vvs_grows_set; eauto.
        * intros; inv MLR. eapply vvs_grows_interp_sact. 2: eauto.
          eapply vvs_grows_set; eauto.
        * intros; inv MLR. eapply vvs_grows_interp_sact. 2: eauto.
          eapply vvs_grows_set; eauto.
        * intros; inv MLR. eapply vvs_grows_interp_sact. 2: eauto.
          eapply vvs_grows_set; eauto.
    - edestruct ENVVVS1 as (? & ? & ? & ?); eauto.
      setoid_rewrite Heqo in H. congruence.
    - edestruct (ENVVVS2 (reg,prt)) as (? & ? & ? & ? ). setoid_rewrite Heqo0 in H. congruence.
    - edestruct (ENVVVS1 (reg,prt)) as (? & ? & ? & ? ). setoid_rewrite Heqo in H. congruence.
  Qed.

  Lemma merge_reg2var_aux_grows:
    forall ks r2v_tb r2v_fb r2v vvs nid cond_name r2v' vvs' nid'
           (MB: merge_reg2vars_aux ks r2v_tb r2v_fb r2v cond_name vvs nid = (r2v', vvs', nid'))
           (ENVVVS1: reg2var_vvs r2v_tb vvs)
           (ENVVVS2: reg2var_vvs r2v_fb vvs)
           (ENVVVSR: forall x y, list_assoc r2v x = Some y -> exists z, list_assoc vvs y = Some (R (fst x), z))
           (RNGVVS: vvs_range vvs nid)
           (VVSVALID: vvs_smaller_variables vvs)
           (VALIDCOND: valid_name cond_name nid)
           (WTCOND: wt_sact vvs (SVar cond_name) (bits_t 1))
           (WT: wt_vvs vvs)
    ,
      vvs_grows vvs vvs'
      /\ vvs_range vvs' nid'
      /\ (forall x y, list_assoc r2v' x = Some y -> exists z, list_assoc vvs' y = Some (R (fst x), z))
      /\ (incl (ks ++ map fst r2v) (map fst r2v'))
      /\ nid <= nid'
      /\ vvs_smaller_variables vvs'
      /\ wt_vvs vvs'
      /\ forall sched_log action_log rir
           (MLR: match_logs_r2v r2v vvs rir sched_log action_log)
           (MLR2:
             forall (b : bool),
               interp_sact vvs (SVar cond_name) (Bits 1 [b]) ->
               match_logs_r2v (if b then r2v_tb else r2v_fb) vvs rir sched_log action_log
           ),
        match_logs_r2v r2v' vvs' rir sched_log action_log.
  Proof.
    induction ks; simpl; intros; eauto.
    - inv MB. repeat split; eauto using vvs_grows_refl. apply incl_refl.
      inv MLR; eauto.
      inv MLR; eauto.
      inv MLR; eauto.
      inv MLR; eauto.
    - repeat destr_in MB; inv MB.
      edestruct merge_reg2var_reg_grows as (VG1 & VR1 & EX1 & INCL1 & LT1 & VSV1 & WT1 & MLR1); eauto.
      edestruct IHks as (VG2 & VR2 & EX2 & INCL2 & LT2 & VSV2 & WT2 & MLR2); eauto using reg2var_vvs_grows.
      red in VALIDCOND; red; lia.
      eapply wt_sact_vvs_grows; eauto.
      repeat refine (conj _ _); eauto using vvs_grows_trans. 2: lia.
      red; intros. eapply INCL2. simpl in H. destruct H; auto.
      subst. apply in_app_iff. right. eapply INCL1; simpl; eauto.
      rewrite in_app_iff in H.
      rewrite in_app_iff. destruct H; auto. right.
      eapply INCL1; simpl; eauto.
      + intros.
        eapply MLR2. eapply MLR1; eauto.
        intros. eapply MLR0; eauto.
        intros.
        assert (interp_sact vvs (SVar cond_name) (Bits 1 [b])).
        {
          exploit wt_sact_interp. 4: apply WTCOND. auto. auto. eauto.
          intros (v & ISV & WTV). inv WTV. destruct bs; simpl in H2. lia.
          destruct bs; simpl in H2. 2: lia.
          exploit vvs_grows_interp_sact. 2: apply ISV. eauto. intros ISL0.
          exploit interp_sact_determ. apply ISL0. apply H. intro A; inv A. eauto.
        }
        split.
        * intros. eapply vvs_grows_interp_sact.
          2: eapply MLR0; eauto. auto.
        * intros; eapply vvs_grows_interp_sact. eauto.
          eapply mlr_read1; eauto.
        * intros; eapply vvs_grows_interp_sact. eauto.
          eapply mlr_write0; eauto.
        * intros; eapply vvs_grows_interp_sact. eauto.
          eapply mlr_write1; eauto.
  Qed.

  Lemma merge_reg2var_grows:
    forall r2v_tb r2v_fb vvs nid cond_name r2v' vvs' nid'
           (MB: merge_reg2vars r2v_tb r2v_fb cond_name vvs nid = (r2v', vvs', nid'))
           (ENVVVS1: reg2var_vvs r2v_tb vvs)
           (ENVVVS2: reg2var_vvs r2v_fb vvs)
           (RNGVVS: vvs_range vvs nid)
           (VVSVALID: vvs_smaller_variables vvs)
           (VALIDCOND: valid_name cond_name nid)
           (WTCOND: wt_sact vvs (SVar cond_name) (bits_t 1))
           (WT: wt_vvs vvs)
    ,
      vvs_grows vvs vvs'
      /\ vvs_range vvs' nid'
      /\ reg2var_vvs r2v' vvs'
      /\ nid <= nid'
      /\ vvs_smaller_variables vvs'
      /\ wt_vvs vvs'
      /\ forall sched_log action_log rir
                (MLR2:
                  forall (b : bool),
                    interp_sact vvs (SVar cond_name) (Bits 1 [b]) ->
                    match_logs_r2v (if b then r2v_tb else r2v_fb) vvs rir sched_log action_log
                ),
        match_logs_r2v r2v' vvs' rir sched_log action_log.
  Proof.
    unfold merge_reg2vars. simpl; intros.
    edestruct merge_reg2var_aux_grows as (VG & VR & R2V1 & R2V2 & NG & VSV & WTVVS & EVAL); eauto.
    simpl; easy.
    repeat refine (conj _ _); eauto.
    rewrite app_nil_r in R2V2.
    red; intros.
    edestruct ENVVVS1 as (? & GET1 & ? & GET2).
    apply list_assoc_in_keys in GET1. apply R2V2 in GET1.
    destruct (list_assoc r2v' x) eqn:?.
    2:{
      apply list_assoc_none_unknown_key in Heqo. contradict Heqo. apply GET1.
    }
    eexists; split; eauto.
    intros; eapply EVAL; eauto.
    exploit wt_sact_interp. 4: apply WTCOND. auto. auto.
    eauto.
    intros (v & ISV & WTV). inv WTV. destruct bs; simpl in H0. lia.
    destruct bs; simpl in H0. 2: lia.
    specialize (MLR2 _ ISV). inv MLR2.
    split; eauto. simpl; easy.
  Qed.

  Record wf_write_log_raw (wl: write_log_raw) (vvs: list (nat * (type * sact))) :=
    {
      wf_wlr_glob_cond: forall i a, In (i, a) wl -> wt_sact vvs (fst a) (bits_t 1) ;
      wf_wlr_glob_interp:
      forall i a,
        In (i, a) wl ->
        (interp_sact vvs (fst a) (Bits 1 [true]) <->
           Exists (fun wi => interp_sact vvs (wcond wi) (Bits 1 [true]) ) (snd a) );
      wf_wlr_each_cond: forall i a, In (i, a) wl ->
                                    Forall (fun wi => wt_sact vvs (wcond wi) (bits_t 1)) (snd a);
      wf_wlr_each_act: forall i a, In (i, a) wl ->
                                   Forall (fun wi => wt_sact vvs (wval wi) (R i)) (snd a);
    }.

  Record wf_rir (r: rule_information_raw) (vvs: list (nat * (type * sact))) :=
    {
      wf_rir_read0s: forall i a, In (i, a) (rir_read0s r) -> wt_sact vvs a (bits_t 1);
      wf_rir_read1s: forall i a, In (i, a) (rir_read1s r) -> wt_sact vvs a (bits_t 1);
      wf_rir_write0s: wf_write_log_raw (rir_write0s r) vvs;
      wf_rir_write1s: wf_write_log_raw (rir_write1s r) vvs;
      wf_fail_wt: wt_sact (rir_vars r) (rir_failure_cond r) (bits_t 1);
    }.

  Lemma wf_write_log_raw_incr:
    forall r n1 n2 n,
      wf_write_log_raw r n1 ->
      vvs_grows n1 n2 ->
      wt_vvs n1 ->
      vvs_range n1 n ->
      vvs_smaller_variables n1 ->
      wf_write_log_raw r n2.
  Proof.
    intros. inv H. split; eauto using wt_sact_vvs_grows.
    - intros.
      specialize (wf_wlr_glob_cond0 _ _ H).
      specialize (wf_wlr_glob_interp0 _ _ H).
      split; intros.
      edestruct (wt_sact_interp) as (v & IS & WT). 4: apply wf_wlr_glob_cond0. all: eauto.
      exploit vvs_grows_interp_sact. eauto. eauto. intros IS2.
      exploit interp_sact_determ. apply H4. apply IS2. intros; subst.
      rewrite wf_wlr_glob_interp0 in IS.
      eapply Exists_impl; eauto. simpl. intros; eapply vvs_grows_interp_sact; eauto.
      eapply vvs_grows_interp_sact; eauto.
      rewrite wf_wlr_glob_interp0.
      rewrite Exists_exists in H4.
      rewrite Exists_exists. destruct H4 as (wi & IN & ISS).
      eexists; split; eauto.
      specialize (wf_wlr_each_cond0 _ _ H). rewrite Forall_forall in wf_wlr_each_cond0.
      specialize (wf_wlr_each_cond0 _ IN).
      edestruct (wt_sact_interp) as (v & IS & WT). 1-3: eauto. apply wf_wlr_each_cond0.
      exploit vvs_grows_interp_sact. eauto. eauto. intros IS2.
      exploit interp_sact_determ. apply ISS. apply IS2. intros; subst.
      auto.
    - intros. eapply Forall_impl. 2: eapply wf_wlr_each_cond0; eauto.
      simpl; intros; eapply wt_sact_vvs_grows; eauto.
    - intros. eapply Forall_impl. 2: eapply wf_wlr_each_act0; eauto.
      simpl; intros; eapply wt_sact_vvs_grows; eauto.
  Qed.

  Lemma wf_rir_incr:
    forall r n1 n2 n,
      wf_rir r n1 ->
      vvs_grows n1 n2 ->
      wt_vvs n1 ->
      vvs_range n1 n ->
      vvs_smaller_variables n1 ->
      wf_rir r n2.
  Proof.
    intros. inv H. split; eauto using wt_sact_vvs_grows, wf_write_log_raw_incr.
  Qed.

  Lemma wf_rir_add_write0:
    forall rir vvs guard v idx rir' fail,
      wf_rir rir vvs ->
      wt_sact vvs guard (bits_t 1) ->
      wt_sact vvs v (R idx) ->
      forall
        (WV: wt_vvs vvs)
        (VSV: vvs_smaller_variables vvs) n
        (VR: vvs_range vvs n),
      add_write0 rir guard idx v = (rir', fail) ->
      wf_rir rir' vvs /\ wt_sact vvs fail (bits_t 1).
  Proof.
    intros. inv H. unfold add_write0 in H2.
    repeat destr_in H2. inv H2.
    split.
    repeat (split; simpl; eauto).
    - intros i a IN.
      apply in_list_assoc_set_inv in IN. destruct IN; eauto.
      inv H. simpl. destr_in Heqp; inv Heqp; eauto.
      apply list_assoc_in in Heqo.
      econstructor; eauto.
      destruct p; simpl in *. eapply wf_wlr_glob_cond in Heqo; eauto. constructor.
      eapply wf_wlr_glob_cond in H; eauto.
    - intros GT. apply in_list_assoc_set_inv in H. destruct H; eauto.
      inv H. simpl. destr_in Heqp; inv Heqp; eauto.
      simpl in GT.
      inv GT.
      destruct p.
      exploit wf_wlr_glob_cond. apply wf_rir_write0s0.
      apply list_assoc_in; eauto. simpl; intros.
      exploit interp_sact_wt. 5: apply H4. all: simpl; eauto.
      exploit interp_sact_wt. 5: apply H6. all: simpl; eauto.
      intros.
      edestruct (wt_val_bool). apply H2.
      edestruct (wt_val_bool). apply H3. subst. simpl in H7. inv H7.
      destruct x0. simpl in *.
      eapply Exists_app. left. inv wf_rir_write0s0.
      exploit wf_wlr_glob_interp0. apply list_assoc_in. eauto. simpl. intros.
      rewrite H5 in H4. auto. simpl in H8. subst.
      eapply Exists_app. right. constructor. simpl. eauto.
      inv wf_rir_write0s0. rewrite <- wf_wlr_glob_interp0. auto. eauto.
    - intros GT. apply in_list_assoc_set_inv in H. destruct H; eauto.
      + inv H. simpl in *. destr_in Heqp; inv Heqp; eauto.
        * rewrite Exists_app in GT. destruct GT. inv wf_rir_write0s0.
          erewrite <- wf_wlr_glob_interp0 in H; eauto.
          2: apply list_assoc_in; eauto.
          edestruct wt_sact_interp as (? & ? & ?). 4: apply H0. all: eauto.
          apply wt_val_bool in H3. destruct H3; subst.
          econstructor; eauto.
          inv H. simpl in H3. destruct p.
          exploit wf_wlr_glob_cond. apply wf_rir_write0s0. apply list_assoc_in; eauto. simpl. intro WTs.
          edestruct wt_sact_interp as (? & ? & ?). 4: apply WTs. all: eauto.
          apply wt_val_bool in H2. destruct H2; subst.
          econstructor; eauto. simpl. rewrite orb_true_r; auto.
          inv H3.
        * inv GT. 2: inv H2. simpl in H2. auto.
      + inv wf_rir_write0s0.
        eapply wf_wlr_glob_interp0. eauto. eauto.
    - intros i a IN.
      apply in_list_assoc_set_inv in IN. destruct IN; eauto.
      inv H. simpl. destr_in Heqp; inv Heqp; eauto.
      apply Forall_app; split; eauto.
      apply list_assoc_in in Heqo.
      destruct p; simpl in *. eapply wf_wlr_each_cond in Heqo; eauto.
      eapply wf_wlr_each_cond in H; eauto.
    - intros i a IN.
      apply in_list_assoc_set_inv in IN. destruct IN; eauto.
      inv H. simpl. destr_in Heqp; inv Heqp; eauto.
      apply Forall_app; split; eauto.
      apply list_assoc_in in Heqo.
      destruct p; simpl in *. eapply wf_wlr_each_act in Heqo; eauto.
      eapply wf_wlr_each_act in H; eauto.
    - econstructor. eauto.
      apply wt_sact_or_conds.
      apply Forall_list_options. simpl. intros. subst. unfold option_map in H.
      destruct H as [H|[H|[H|[]]]]; repeat destr_in H; inv H.
      + destruct p. apply list_assoc_in in Heqo.
        eapply wf_wlr_glob_cond in Heqo; eauto.
      + apply list_assoc_in in H3.
        eapply wf_rir_read1s0 in H3. auto.
      + destruct p. apply list_assoc_in in Heqo.
        eapply wf_wlr_glob_cond in Heqo; eauto.
      + constructor.
  Qed.
  Lemma wf_rir_add_write1:
    forall rir vvs guard v idx rir' fail,
      wf_rir rir vvs ->
      wt_sact vvs guard (bits_t 1) ->
      wt_sact vvs v (R idx) ->
      forall
        (WV: wt_vvs vvs)
        (VSV: vvs_smaller_variables vvs) n
        (VR: vvs_range vvs n),
      add_write1 rir guard idx v = (rir', fail) ->
      wf_rir rir' vvs /\ wt_sact vvs fail (bits_t 1).
  Proof.
    intros. inv H. unfold add_write1 in H2.
    repeat destr_in H2. inv H2.
    split.
    repeat (split; simpl; eauto).
    - intros i a IN.
      apply in_list_assoc_set_inv in IN. destruct IN; eauto.
      inv H. simpl. destr_in Heqp; inv Heqp; eauto.
      apply list_assoc_in in Heqo.
      econstructor; eauto.
      destruct p; simpl in *. eapply wf_wlr_glob_cond in Heqo; eauto. constructor.
      eapply wf_wlr_glob_cond in H; eauto.
    - intros GT. apply in_list_assoc_set_inv in H. destruct H; eauto.
      inv H. simpl. destr_in Heqp; inv Heqp; eauto.
      simpl in GT.
      inv GT.
      destruct p.
      exploit wf_wlr_glob_cond. apply wf_rir_write1s0.
      apply list_assoc_in; eauto. simpl; intros.
      exploit interp_sact_wt. 5: apply H4. all: simpl; eauto.
      exploit interp_sact_wt. 5: apply H6. all: simpl; eauto.
      intros.
      edestruct (wt_val_bool). apply H2.
      edestruct (wt_val_bool). apply H3. subst. simpl in H7. inv H7.
      destruct x0. simpl in *.
      eapply Exists_app. left. inv wf_rir_write1s0.
      exploit wf_wlr_glob_interp0. apply list_assoc_in. eauto. simpl. intros.
      rewrite H5 in H4. auto. simpl in H8. subst.
      eapply Exists_app. right. constructor. simpl. eauto.
      inv wf_rir_write1s0. rewrite <- wf_wlr_glob_interp0. auto. eauto.
    - intros GT. apply in_list_assoc_set_inv in H. destruct H; eauto.
      + inv H. simpl in *. destr_in Heqp; inv Heqp; eauto.
        * rewrite Exists_app in GT. destruct GT. inv wf_rir_write1s0.
          erewrite <- wf_wlr_glob_interp0 in H; eauto.
          2: apply list_assoc_in; eauto.
          edestruct wt_sact_interp as (? & ? & ?). 4: apply H0. all: eauto.
          apply wt_val_bool in H3. destruct H3; subst.
          econstructor; eauto.
          inv H. simpl in H3. destruct p.
          exploit wf_wlr_glob_cond. apply wf_rir_write1s0. apply list_assoc_in; eauto. simpl. intro WTs.
          edestruct wt_sact_interp as (? & ? & ?). 4: apply WTs. all: eauto.
          apply wt_val_bool in H2. destruct H2; subst.
          econstructor; eauto. simpl. rewrite orb_true_r; auto.
          inv H3.
        * inv GT. 2: inv H2. simpl in H2. auto.
      + inv wf_rir_write1s0.
        eapply wf_wlr_glob_interp0. eauto. eauto.
    - intros i a IN.
      apply in_list_assoc_set_inv in IN. destruct IN; eauto.
      inv H. simpl. destr_in Heqp; inv Heqp; eauto.
      apply Forall_app; split; eauto.
      apply list_assoc_in in Heqo.
      destruct p; simpl in *. eapply wf_wlr_each_cond in Heqo; eauto.
      eapply wf_wlr_each_cond in H; eauto.
    - intros i a IN.
      apply in_list_assoc_set_inv in IN. destruct IN; eauto.
      inv H. simpl. destr_in Heqp; inv Heqp; eauto.
      apply Forall_app; split; eauto.
      apply list_assoc_in in Heqo.
      destruct p; simpl in *. eapply wf_wlr_each_act in Heqo; eauto.
      eapply wf_wlr_each_act in H; eauto.
    - econstructor. eauto.
      apply wt_sact_or_conds.
      apply Forall_list_options. simpl. intros. subst. unfold option_map in H.
      destruct H as [H|[]]; repeat destr_in H; inv H.
      + destruct p. apply list_assoc_in in Heqo.
        eapply wf_wlr_glob_cond in Heqo; eauto.
      + constructor.
  Qed.

  Lemma wf_rir_add_read0:
    forall rir vvs guard idx,
      wf_rir rir vvs ->
      wt_sact vvs guard (bits_t 1) ->
      wf_rir (add_read0 rir guard idx) vvs.
  Proof.
    intros. inv H. unfold add_read0. split; simpl; eauto.
    intros.
    edestruct @in_list_assoc_set_inv. eapply H.
    - inv H1. destr; eauto.
      econstructor; eauto. 2: constructor.
      eapply wf_rir_read0s0; eauto.
      apply list_assoc_in in Heqo. eauto.
    - eauto.
  Qed.

  Lemma wf_rir_add_read1:
    forall rir vvs guard idx,
      wf_rir rir vvs ->
      wt_sact vvs guard (bits_t 1) ->
      wf_rir (add_read1 rir guard idx) vvs.
  Proof.
    intros. inv H. unfold add_read1. split; simpl; eauto.
    intros.
    apply in_list_assoc_set_inv in H. destruct H.
    - inv H. destr; eauto.
      econstructor; eauto.
      apply list_assoc_in in Heqo. eauto.
      constructor.
    - eauto.
  Qed.

  Definition in_wil idx wi (wl: write_log_raw) :=
    exists gcond wil, list_assoc wl idx = Some (gcond, wil) /\ In wi wil.

  Definition write_log_raw_grows (wl1 wl2: write_log_raw) vvs2 grd :=
    forall idx wi,
      (in_wil idx wi wl1 -> in_wil idx wi wl2) /\
        (~ in_wil idx wi wl1 -> in_wil idx wi wl2 ->
         interp_sact vvs2 grd (Bits 1 [false]) ->
         interp_sact vvs2 (wcond wi) (Bits 1 [false])).


  Definition bool_sact_grows vvs1 c1 vvs2 c2 : Prop :=
    interp_sact vvs1 c1 (Bits 1 [true]) ->
    interp_sact vvs2 c2 (Bits 1 [true]).

  Definition cond_log_grows vvs1 (cl1: cond_log) vvs2 cl2 grd :=
    forall idx,
      let c := match list_assoc cl1 idx with Some c => c | None => const_false end in
      let c' := match list_assoc cl2 idx with Some c => c | None => const_false end in
      bool_sact_grows vvs1 c vvs2 c'
      /\ (interp_sact vvs2 grd (Bits 1 [false]) ->
          forall b, interp_sact vvs1 c (Bits 1 [b]) <-> interp_sact vvs2 c' (Bits 1 [b])
         ).


  Record rir_grows vvs1 r1 vvs2 r2 grd : Prop :=
    {
      rir_grows_read0s: cond_log_grows vvs1 (rir_read0s r1) vvs2 (rir_read0s r2) grd;
      rir_grows_read1s: cond_log_grows vvs1 (rir_read1s r1) vvs2 (rir_read1s r2) grd;
      rir_grows_write0s: write_log_raw_grows (rir_write0s r1) (rir_write0s r2) vvs2 grd;
      rir_grows_write1s: write_log_raw_grows (rir_write1s r1) (rir_write1s r2) vvs2 grd;
      rir_vvs_grows: vvs_grows vvs1 vvs2;
      rir_wt_grd: wt_sact vvs2 grd (bits_t 1);
    }.

  Lemma rir_grows_interp_sact:
    forall r1 v1 r2 v2 a v grd,
      rir_grows v1 r1 v2 r2 grd ->
      interp_sact v1 a v ->
      interp_sact v2 a v.
  Proof.
    inversion 1; eapply vvs_grows_interp_sact; eauto.
  Qed.

  Lemma write_log_raw_grows_refl: forall wl vvs grd, write_log_raw_grows wl wl vvs grd.
  Proof.
    red; intros.
    split; intros. eauto. congruence.
  Qed.

  Lemma bool_sact_grows_refl: forall vvs c, bool_sact_grows vvs c vvs c.
  Proof.
    red; intros; eauto.
  Qed.

  Lemma cond_log_grows_refl: forall vvs cl grd, cond_log_grows vvs cl vvs cl grd.
  Proof.
    red; intros. repeat split; eauto using bool_sact_grows_refl.
  Qed.

  Lemma rir_grows_refl: forall vvs r grd,
      wt_sact vvs grd (bits_t 1) ->
      rir_grows vvs r vvs r grd.
  Proof.
    split; eauto using incl_refl, write_log_raw_grows_refl, cond_log_grows_refl, vvs_grows_refl.
  Qed.

  Instance eq_sact_dec: EqDec sact.
  Proof.
    constructor. decide equality.
    apply eq_nat_dec. apply val_eq_dec.
    decide equality.
    decide equality.
    decide equality.
    decide equality.
    decide equality.
    decide equality.
    decide equality.
    apply eq_dec.
    decide equality; apply eq_dec.
    decide equality; apply eq_dec.
    decide equality; apply eq_dec.
    decide equality; apply eq_dec.
    apply eq_dec.
  Defined.

  Record wf_state tsig env reg2var vvs rir nid :=
    {
      wfs_wt_vvs: wt_vvs vvs;
      wfs_env_vvs: env_vvs env vvs tsig;
      wfs_r2v_vvs: reg2var_vvs reg2var vvs;
      wfs_vvs_range: vvs_range vvs nid;
      wfs_vsv: vvs_smaller_variables vvs;
      wfs_rir: wf_rir rir vvs;
    }.


  Lemma wf_sact_interp:
    forall tsig env r2v vvs rir n a t,
      wt_sact vvs a t ->
      wf_state tsig env r2v vvs rir n ->
      exists v, interp_sact vvs a v /\ wt_val t v.
  Proof.
    intros tsig env r2v vvs rir n a t WTs WFs. inv WFs.
    eapply wt_sact_interp; eauto.
  Qed.

  Lemma in_wil_dec: forall idx wi wil, {in_wil idx wi wil} + {~ in_wil idx wi wil}.
  Proof.
    unfold in_wil. intros.
    destruct (list_assoc wil idx) eqn:?.
    - destruct p.
      destruct (in_dec eq_dec wi l). left; do 2 eexists; split; eauto.
      right. intros (gcond & wil0 & EQ & IN). congruence.
    - right. intros (gcond & wil0 & EQ & IN). congruence.
  Qed.

  Lemma write_log_raw_grows_trans:
    forall wl1 wl2 vvs2 grd env tsig r2v rir n,
      wt_sact vvs2 grd (bits_t 1) ->
      wf_state tsig env r2v vvs2 rir n ->
      write_log_raw_grows wl1 wl2 vvs2 grd ->
      forall wl3 vvs3 grd' tsig' rir' n' r2v' env' ,
        wt_sact vvs3 grd' (bits_t 1) ->
        wf_state tsig' env' r2v' vvs3 rir' n' ->
        vvs_grows vvs2 vvs3 ->
        write_log_raw_grows wl2 wl3 vvs3 grd' ->
        write_log_raw_grows wl1 wl3 vvs3 (uor grd grd').
  Proof.
    red; intros wl1 wl2 vvs2 grd env tsig r2v rir n WTG1 WFS1 WLRG
                wl3 vvs3 grd' tsig' rir' n' r2v' env'
                WTG2 WFS2 VG WLRG2 idx wi.
    edestruct (WLRG idx wi).
    edestruct (WLRG2 idx wi).
    split; intros.
    eauto.
    edestruct (wf_sact_interp) with (a:=grd) as (vv & IS & WTV); eauto.
    edestruct wt_val_bool. apply WTV. subst.
    edestruct (wf_sact_interp) with (a:=grd') as (vv & IS' & WTV'); eauto.
    edestruct wt_val_bool. apply WTV'. subst.
    exploit vvs_grows_interp_sact. eauto. eauto. intro ISg.
    inv H5.
    exploit interp_sact_determ. apply ISg. apply H9.
    exploit interp_sact_determ. apply IS'. apply H11. intros; subst.
    simpl in H12. inv H12. apply orb_false_iff in H6. destruct H6; subst. simpl.
    destruct (in_wil_dec idx wi wl2).
    - exploit H0; eauto. eapply vvs_grows_interp_sact. auto.
    - exploit H2; eauto.
  Qed.

  Lemma bool_sact_grows_trans:
    forall vvs1 c1 vvs2 c2,
      bool_sact_grows vvs1 c1 vvs2 c2 ->
      forall vvs3 c3,
        bool_sact_grows vvs2 c2 vvs3 c3 ->
        bool_sact_grows vvs1 c1 vvs3 c3.
  Proof.
    red; intros.
    eapply H in H1. eapply H0 in H1. eauto.
  Qed.

  Lemma cond_log_grows_trans:
    forall vvs1 cl1 vvs2 cl2 grd tsig env r2v rir n,
      wt_sact vvs2 grd (bits_t 1) ->
      wf_state tsig env r2v vvs2 rir n ->
      cond_log_grows vvs1 cl1 vvs2 cl2 grd ->
      forall cl3 tsig' env' r2v' vvs3 rir' n' grd' ,
        wt_sact vvs3 grd' (bits_t 1) ->
        wf_state tsig' env' r2v' vvs3 rir' n' ->
        vvs_grows vvs2 vvs3 ->
        cond_log_grows vvs2 cl2 vvs3 cl3 grd' ->
        cond_log_grows vvs1 cl1 vvs3 cl3 (uor grd grd').
  Proof.
    red; intros vvs1 cl1 vvs2 cl2 grd tsig env r2v rir n WTG1 WFS1 CLG1
                cl3 tsig' env' r2v' vvs3 rir' n' grd'
                WTG2 WFS2 VG2 CLG2 idx.
    edestruct (CLG1 idx) as (BSG1 & INCR1); eauto.
    edestruct (CLG2 idx) as (BSG2 & INCR2); eauto.
    split.
    eauto using bool_sact_grows_trans.
    intros.
    edestruct (wf_sact_interp) with (a:=grd) as (vv & IS & WTV); eauto.
    edestruct wt_val_bool; eauto. clear WTV; subst.
    edestruct (wf_sact_interp) with (a:=grd') as (vv & IS' & WTV); eauto.
    edestruct wt_val_bool; eauto. clear WTV; subst.
    exploit vvs_grows_interp_sact; eauto. intro ISg.
    inv H.
    exploit interp_sact_determ. apply ISg. apply H3.
    exploit interp_sact_determ. apply IS'. apply H5. intros; subst.
    simpl in H6. inv H6. apply orb_false_iff in H0. destruct H0; subst.
    rewrite INCR1; eauto.
  Qed.

  Lemma rir_grows_trans:
    forall vvs1 r1 vvs2 r2 grd tsig env r2v rir n,
      wf_state tsig env r2v vvs2 rir n ->
      rir_grows vvs1 r1 vvs2 r2 grd ->
      forall vvs3 r3 grd' tsig' env' r2v' rir' n' ,
        wf_state tsig' env' r2v' vvs3 rir' n' ->
        rir_grows vvs2 r2 vvs3 r3 grd' ->
        rir_grows vvs1 r1 vvs3 r3 (uor grd grd').
  Proof.
    intros. inv H0; inv H2.
    split; eauto using incl_tran, write_log_raw_grows_trans, cond_log_grows_trans, vvs_grows_trans.
    econstructor; eauto. eapply wt_sact_vvs_grows; eauto. constructor.
  Qed.

  Lemma rir_grows_add_read0:
    forall vvs rir grd idx tsig env r2v nid
           (WFS: wf_state tsig env r2v vvs rir nid)
           (WTG: wt_sact vvs grd (bits_t 1)),
      rir_grows vvs rir vvs (add_read0 rir grd idx) grd.
  Proof.
    unfold add_read0. intros.
    split; simpl; eauto using incl_refl, write_log_raw_grows_refl, cond_log_grows_refl, vvs_grows_refl.
    red; intros.
    edestruct wf_sact_interp with (a:=grd) as (x & IV & WTv); eauto.
    apply wt_val_bool in WTv. destruct WTv; subst.
    split.
    - destr.
      + subst. rewrite list_assoc_spec. rewrite Heqo.
        destruct eq_dec.
        subst. rewrite Heqo.
        red; intros.
        econstructor; eauto.
        eauto using bool_sact_grows_refl.
      + rewrite list_assoc_spec. rewrite Heqo.
        destruct eq_dec.
        subst. rewrite Heqo.
        red; intros. inv H.
        eauto using bool_sact_grows_refl.
    - intros.
      exploit interp_sact_determ. apply IV. apply H. intro A; inv A.
      rewrite list_assoc_spec.
      destruct eq_dec; subst.
      + destr.
        split; intros. econstructor; eauto. simpl. rewrite orb_false_r; auto.
        inv H0. exploit interp_sact_determ. apply IV. apply H6. intros <-.
        exploit wf_rir_read0s. inv WFS; eauto. apply list_assoc_in. eauto. intro WTs.
        exploit interp_sact_wt. 5: apply H4. 4: eauto.
        1-3: inv WFS; eauto.
        intros WTv. edestruct wt_val_bool. eauto. subst. simpl in H7. inv H7.
        rewrite orb_false_r. auto.
        split; intros. inv H0. auto.
        exploit interp_sact_determ. apply H0. apply IV. intro A; inv A. constructor.
      + destr. tauto. tauto.
  Qed.

  Lemma rir_grows_add_read1:
    forall vvs rir grd idx tsig env r2v nid
           (WFS: wf_state tsig env r2v vvs rir nid)
           (WTG: wt_sact vvs grd (bits_t 1)),
      rir_grows vvs rir vvs (add_read1 rir grd idx) grd.
  Proof.
    unfold add_read1. intros.
    split; simpl; eauto using incl_refl, write_log_raw_grows_refl, cond_log_grows_refl, vvs_grows_refl.
    red; intros.
    edestruct wf_sact_interp with (a:=grd) as (x & IV & WTv); eauto.
    apply wt_val_bool in WTv. destruct WTv; subst.
    split.
    - destr.
      + subst. rewrite list_assoc_spec. rewrite Heqo.
        destruct eq_dec.
        subst. rewrite Heqo.
        red; intros.
        econstructor; eauto.
        eauto using bool_sact_grows_refl.
      + rewrite list_assoc_spec. rewrite Heqo.
        destruct eq_dec.
        subst. rewrite Heqo.
        red; intros. inv H.
        eauto using bool_sact_grows_refl.
    - intros.
      exploit interp_sact_determ. apply IV. apply H. intro A; inv A.
      rewrite list_assoc_spec.
      destruct eq_dec; subst.
      + destr.
        split; intros. econstructor; eauto. simpl. rewrite orb_false_r; auto.
        inv H0. exploit interp_sact_determ. apply IV. apply H6. intros <-.
        exploit wf_rir_read1s. inv WFS; eauto. apply list_assoc_in. eauto. intro WTs.
        exploit interp_sact_wt. 5: apply H4. 4: eauto.
        1-3: inv WFS; eauto.
        intros WTv. edestruct wt_val_bool. eauto. subst. simpl in H7. inv H7.
        rewrite orb_false_r. auto.
        split; intros. inv H0. auto.
        exploit interp_sact_determ. apply H0. apply IV. intro A; inv A. constructor.
      + destr. tauto. tauto.
  Qed.

  Lemma interp_sact_change_vvs:
    forall a
           (vvs1: list (nat * (type * sact)))
           v
           (vvs2: list (nat * (type * sact)))
           n
           (VVSRANGE: vvs_range vvs1 n)
           (VVSGROWS: forall x,
               valid_name x n ->
               forall y, list_assoc vvs1 x = Some y -> list_assoc vvs2 x = Some y)
           (INF: interp_sact vvs1 a v),
      interp_sact vvs2 a v.
  Proof.
    induction 3; simpl; intros; eauto; try now (econstructor; eauto).
  Qed.

  Lemma interp_sact_vvs_grows_inv:
    forall vvs vvs' a v t n,
      wt_vvs vvs ->
      vvs_smaller_variables vvs ->
      vvs_grows vvs vvs' ->
      vvs_range vvs n ->
      wt_sact vvs a t ->
      interp_sact vvs' a v ->
      interp_sact vvs a v.
  Proof.
    intros.
    edestruct wt_sact_interp as (vv & IS & WTv); eauto.
    exploit vvs_grows_interp_sact; eauto. intros.
    exploit interp_sact_determ. apply H4. apply H5. intros ->; eauto.
  Qed.

  Lemma cond_log_grows_change_vvs:
    forall vvs1 vvs2 n cl grd env tsig r2v rir,
      wf_state tsig env r2v vvs1 rir n ->
      vvs_range vvs1 n ->
      (forall x,
          valid_name x n ->
          forall y,
            list_assoc vvs1 x = Some y -> list_assoc vvs2 x = Some y) ->
      (forall i a, In (i, a) cl -> wt_sact vvs1 a (bits_t 1)) ->
      cond_log_grows vvs1 cl vvs2 cl grd.
  Proof.
    red; intros. split.
    - red; simpl; intros. eapply vvs_grows_interp_sact; eauto.
      red; intros; eauto.
    - intros. destr. 2: split; inversion 1; econstructor; eauto.
      split; intros.
      eapply vvs_grows_interp_sact; eauto.
      red; intros; eauto.
      eapply interp_sact_vvs_grows_inv; eauto. inv H; eauto.
      inv H; eauto.
      red; intros; eapply H1; eauto.
      eapply H2; eauto. eapply list_assoc_in; eauto.
  Qed.
  
  Lemma rir_grows_change_vvs:
    forall vvs1 vvs2 rir n grd tsig env r2v,
      wf_state tsig env r2v vvs1 rir n ->
      (forall x,
          valid_name x n ->
          forall y,
            list_assoc vvs1 x = Some y -> list_assoc vvs2 x = Some y) ->
      wt_sact vvs2 grd (bits_t 1) ->
      rir_grows vvs1 rir vvs2 rir grd.
  Proof.
    intros. split; eauto using write_log_raw_grows_refl, incl_refl.
    - eapply cond_log_grows_change_vvs; eauto. inv H; auto.
      inv H. intros; eapply wf_rir_read0s; eauto.
    - eapply cond_log_grows_change_vvs; eauto. inv H; auto.
      inv H. intros; eapply wf_rir_read1s; eauto.
    - red; intros; eapply H0; eauto.
      eapply wfs_vvs_range in H2; eauto.
  Qed.

  Lemma rir_grows_set:
    forall vvs rir name n v tsig env r2v,
      wf_state tsig env r2v vvs rir n ->
      ~ valid_name name n ->
      rir_grows vvs rir (list_assoc_set vvs name v) rir const_false.
  Proof.
    intros; eapply rir_grows_change_vvs; eauto.
    intros; rewrite list_assoc_gso; eauto. congruence.
    eapply wt_sact_vvs_grows; eauto. eapply vvs_grows_set; eauto. inv H; eauto.
    eapply vvs_range_incr. 2: eauto. unfold valid_name in H0. lia.
    repeat constructor.
  Qed.

  Ltac dihyp H :=
    let iv := fresh "INTERPVAL" in
    let ig := fresh "INTERPFAIL" in
    let mge := fresh "MGE" in
    let mlr := fresh "MLR" in
    let wte := fresh "WTE" in
    edestruct H as (iv & ig & mge & mlr & wte); eauto.

  Lemma match_Gamma_env_vvs_grows:
    forall Gamma env vvs,
      match_Gamma_env Gamma env vvs ->
      forall vvs' ,
        vvs_grows vvs vvs' ->
        match_Gamma_env Gamma env vvs'.
  Proof.
    induction 1; simpl; intros; eauto.
    constructor.
    destruct H.
    constructor; eauto. split; eauto using vvs_grows_interp_sact.
    eapply Forall2_impl; eauto. simpl; intros; eauto.
    destruct H5; split; eauto using vvs_grows_interp_sact.
  Qed.
  Lemma match_logs_r2v_vvs_grows:
    forall r2v vvs sl al rir vvs' ,
      match_logs_r2v r2v vvs rir sl al ->
      vvs_grows vvs vvs' ->
      match_logs_r2v r2v vvs' rir sl al.
  Proof.
    intros. inv H. split; intros; eapply vvs_grows_interp_sact; eauto.
  Qed.

  Lemma gria_list_grows2:
    forall
      (I: list (string * nat) -> list (reg_t * Port * nat) -> list (nat * (type * sact)) -> nat -> rule_information_raw -> sact -> Prop)
      (P: list (string * nat) -> list (reg_t * Port * nat) -> list (nat * (type * sact)) -> nat -> rule_information_raw ->
          list (string * nat) -> list (reg_t * Port * nat) -> list (nat * (type * sact)) -> nat -> rule_information_raw -> sact -> Prop)
      (Prefl: forall env r2v vvs nid rir grd,
          wt_sact vvs grd (bits_t 1) ->
          P env r2v vvs nid rir env r2v vvs nid rir grd)
      (Ptrans: forall env1 r2v1 vvs1 nid1 rir1 env2 r2v2 vvs2 nid2 rir2 env3 r2v3 vvs3 nid3 rir3 grd1 grd2 grd3,
          I env1 r2v1 vvs1 nid1 rir1 grd1 ->
          P env1 r2v1 vvs1 nid1 rir1 env2 r2v2 vvs2 nid2 rir2 grd1 ->
          I env2 r2v2 vvs2 nid2 rir2 grd2 ->
          P env2 r2v2 vvs2 nid2 rir2 env3 r2v3 vvs3 nid3 rir3 grd1 ->
          I env3 r2v3 vvs3 nid3 rir3 grd3 ->
          P env1 r2v1 vvs1 nid1 rir1 env3 r2v3 vvs3 nid3 rir3 grd1
      )
      (Psetvvs:
        forall env r2v vvs n rir grd v t,
          I env r2v vvs n rir grd ->
          (* valid_vars_sact v n -> *)
          wt_sact vvs v t ->
          P env r2v vvs n rir env r2v (list_assoc_set vvs n (t, v)) (S n) rir grd
          /\ I env r2v (list_assoc_set vvs n (t, v)) (S n) rir grd
      )
      (Pvvsgrows:
        forall env1 r2v1 vvs1 nid1 rir1 grd1 env2 r2v2 vvs2 nid2 rir2,
          P env1 r2v1 vvs1 nid1 rir1 env2 r2v2 vvs2 nid2 rir2 grd1 ->
          I env1 r2v1 vvs1 nid1 rir1 grd1 ->
          vvs_grows vvs1 vvs2
      )
      (Irange:
        forall env r2v vvs nid rir grd,
          I env r2v vvs nid rir grd ->
          vvs_range vvs nid
      )
      rec args tsig
      (F: Forall (fun u =>
                    forall env r2v guard rir nid v env' r2v' vvs fail_cond rir' nid' vvs0 t t0,
                      wt_daction pos_t string string tsig (R:=R) (Sigma:=Sigma) u t0 ->
                      rec u tsig env r2v vvs0 guard rir nid = (v, env', r2v', vvs, fail_cond, rir', nid', t) ->
                      (* valid_vars_sact guard nid -> *)
                      I env r2v vvs0 nid rir guard ->
                      P env r2v vvs0 nid rir env' r2v' vvs nid' rir' guard /\ I env' r2v' vvs nid' rir' guard
                      (* /\ (forall ov, v = Some ov -> valid_vars_sact ov nid') *)
                      (* /\ valid_vars_sact guard nid' *)
                      (* /\ valid_vars_sact fail_cond nid' *)
                      /\ wt_sact vvs fail_cond (bits_t 1)
                      /\ nid <= nid'
                      /\ wt_sact vvs (reduce t v) t
                      /\ t = t0
                      /\ forall Gamma sched_log action_log action_log' vret Gamma'
                                (WTRENV: wt_renv R REnv r)
                                (WTG: wt_env _ tsig Gamma)
                                (GE: match_Gamma_env Gamma env vvs0)
                                (MLR: match_logs_r2v r2v vvs0 rir sched_log action_log)
                                (INTERP: interp_daction r sigma Gamma sched_log action_log u = Some (action_log', vret, Gamma'))
                                (GUARDOK: interp_sact vvs0 guard (Bits 1 [true])),
                          interp_sact vvs (reduce t v) vret
                          /\ interp_sact vvs fail_cond (Bits 1 [false])
                          /\ match_Gamma_env Gamma' env' vvs
                          /\ match_logs_r2v r2v' vvs rir' sched_log action_log'
                          /\ wt_env _ tsig Gamma'
                 ) args)
      lt
      (WTargs: Forall2 (wt_daction (R:=R) (Sigma:=Sigma) pos_t string string tsig) args lt)
      guard env r2v vvs0 rir nid names0 fail0 names env' r2v' vvs fail1 rir' nid'
      (* (VG: valid_vars_sact guard nid) *)
      (WTg: wt_sact vvs0 guard (bits_t 1))
      (* (VF: valid_vars_sact fail0 nid) *)
      (WTf: wt_sact vvs0 fail0 (bits_t 1))
      (INV: I env r2v vvs0 nid rir guard)
      (GRIA: gria_list guard rec args tsig env r2v vvs0 rir nid names0 fail0 = (names, env', r2v', vvs, fail1, rir', nid'))
      lt0
      (NAMES: Forall2 (fun '(var1, t1) t2 =>
                         t1 = t2 /\
                           exists s, list_assoc vvs0 var1 = Some (t1, s)
                      ) names0 lt0)
    ,
      P env r2v vvs0 nid rir env' r2v' vvs nid' rir' guard
      /\ I env' r2v' vvs nid' rir' guard
      /\ (Forall2 (fun '(var1, t1) t2 =>
                     t1 = t2 /\
                       exists s, list_assoc vvs var1 = Some (t1, s)
                  ) names (rev lt ++ lt0))
      /\ List.length names = List.length names0 + List.length args
      (* /\ valid_vars_sact fail1 nid' *)
      /\ wt_sact vvs fail1 (bits_t 1)
      /\ nid <= nid'
      /\ forall Gamma sched_log action_log action_log' Gamma'
                (WTRENV: wt_renv R REnv r)
                (WTG: wt_env _ tsig Gamma)
                (GE: match_Gamma_env Gamma env vvs0)
                (MLR: match_logs_r2v r2v vvs0 rir sched_log action_log)
                lv0 lv
                (INIT: Forall2 (fun '(n,t) v => interp_sact vvs0 (SVar n) v) names0 lv0)
                (INITFAIL: interp_sact vvs0 fail0 (Bits 1 [false]))
                (INTERP: fold_left
                           (fun acc a0 =>
                              let/opt3 action_log0, l, Gamma0 := acc
                              in (let/opt3 action_log1, v, Gamma1
                                    := interp_daction r sigma Gamma0 sched_log action_log0 a0
                                  in Some (action_log1, v :: l, Gamma1))) args
                           (Some (action_log, lv0, Gamma)) = Some (action_log', lv, Gamma'))
                (GUARDOK: interp_sact vvs0 guard (Bits 1 [true])),
        Forall2 (fun '(n,t) v => interp_sact vvs (SVar n) v) names lv
        /\ interp_sact vvs fail1 (Bits 1 [false])
        /\ match_Gamma_env Gamma' env' vvs
        /\ match_logs_r2v r2v' vvs rir' sched_log action_log'
        /\ wt_env _ tsig Gamma'.
  Proof.
    induction 6; simpl; intros; eauto.
    - inv GRIA. repeat refine (conj _ _); eauto.
      inv WTargs. simpl. eauto.
      intros. inv INTERP. repeat refine (conj _ _); eauto.
    - repeat destr_in GRIA. subst. inv WTargs.
      eapply H in Heqp; eauto.
      destruct Heqp as (P2 & I2 & WTa & NIDGROWS2 & WTf0 & TEQ & INTERPHYP). clear H.
      subst.
      eapply IHF in GRIA;  eauto.
      destruct GRIA as (Pgria & Igria & NAMES1 & LENNAMES & WTf2 & NIDGROWS & INTERPHYP2).

      repeat refine (conj _ _); eauto.
      + eapply Ptrans; eauto.
        eapply Ptrans. eauto. 3: eauto.
        eapply Psetvvs; eauto.
        eapply Psetvvs; eauto. eauto.
      + simpl. rewrite <- app_assoc. apply NAMES1.
      + simpl in LENNAMES; lia.
      + lia.
      + intros.
        destruct (interp_daction r sigma Gamma sched_log action_log x) eqn:?. destruct p as ((? & ?) & ?). simpl in INTERP.
        dihyp INTERPHYP.

        dihyp INTERPHYP2.
        * eapply match_Gamma_env_vvs_grows; eauto. eapply vvs_grows_set; eauto.
        * eapply match_logs_r2v_vvs_grows; eauto. eapply vvs_grows_set; eauto.
        * constructor. econstructor. rewrite list_assoc_gss. eauto.
          eapply vvs_grows_interp_sact; eauto using vvs_grows_set.
          eapply Forall2_impl. eauto. simpl; intros.
          destr. eapply vvs_grows_interp_sact. 2: eauto.
          eapply vvs_grows_trans. 2: eapply vvs_grows_set; eauto.
          eapply Pvvsgrows; eauto.
        * eapply vvs_grows_interp_sact. eapply vvs_grows_set; eauto.
          econstructor; eauto.
          eapply vvs_grows_interp_sact. eapply Pvvsgrows; eauto. eauto. reflexivity.
        * eapply vvs_grows_interp_sact. 2: eauto.
          eapply vvs_grows_trans. 2: eapply vvs_grows_set; eauto.
          eapply Pvvsgrows; eauto.
        * simpl in INTERP.
          rewrite fold_left_none in INTERP. congruence. simpl. auto.
      + eapply wt_sact_vvs_grows. 2: eauto.
        eapply vvs_grows_trans. eauto. eapply vvs_grows_set; eauto.
      + econstructor. eapply wt_sact_vvs_grows. 2: eauto. eapply vvs_grows_set; eauto.
        eapply wt_sact_vvs_grows. 2: eauto.
        eapply vvs_grows_trans. eauto. eapply vvs_grows_set; eauto.
        constructor.
      + eapply Psetvvs; eauto.
      + simpl. constructor. split; auto.
        rewrite list_assoc_gss. eauto.
        eapply Forall2_impl. apply NAMES. simpl.
        intros (n0 & t0) t1 IN1 IN2 (EQ & s0 & GET). subst. split; auto.
        rewrite list_assoc_gso; eauto.
        eapply Pvvsgrows in GET; eauto.
        eapply Irange in GET; eauto. red in GET. lia.
  Qed.


  Lemma wf_state_set:
    forall tsig env reg2var vvs rir n,
      wf_state tsig env reg2var vvs rir n ->
      forall t v vv,
        wt_sact vvs vv t ->
        list_assoc tsig v = Some t ->
        wf_state tsig (list_assoc_set env v n) reg2var (list_assoc_set vvs n (t, vv)) rir (S n).
  Proof.
    intros tsig env reg2var vvs rir n WFS t v vv WTA GETt.
    inv WFS; split; eauto.
    + eapply wt_vvs_set; eauto.
    + eapply env_vvs_set; auto.
    + eapply reg2var_vvs_grows. eauto. eapply vvs_grows_set; eauto.
    + eapply vvs_range_list_assoc_set. eapply vvs_range_incr. 2: eauto. lia.
      red; lia.
    + eapply vvs_smaller_variables_set; eauto.
      eapply wt_sact_valid_vars; eauto.
    + eapply wf_rir_incr; eauto.
      eapply vvs_grows_set; eauto.
  Qed.

  Lemma env_vvs_none_some:
    forall env vvs tsig,
      env_vvs env vvs tsig ->
      forall v n,
        list_assoc env v = None ->
        list_assoc tsig v = Some n ->
        False.
  Proof.
    induction 1; simpl; intros; eauto. easy.
    repeat destr_in H. destruct H as (? & ? & ?). subst.
    repeat destr_in H1. easy. eauto.
  Qed.

  Lemma wf_state_vvs_set:
    forall tsig env reg2var vvs rir n,
      wf_state tsig env reg2var vvs rir n ->
      forall t vv,
        wt_sact vvs vv t ->
        forall k, k >= n ->
                  (forall v0, var_in_sact vv v0 -> v0 < k) ->
                  forall m, m > k ->
                            wf_state tsig env reg2var (list_assoc_set vvs k (t, vv)) rir m
                            /\ vvs_grows vvs (list_assoc_set vvs k (t,vv)).
  Proof.
    intros tsig env reg2var vvs rir n WFS t vv WTA k GEk VARRES m GTk.
    inv WFS; split; [split|]; eauto.
    + eapply wt_vvs_set; eauto.
    + eapply env_vvs_vvs_grows; eauto. eapply vvs_grows_set; eauto.
    + eapply reg2var_vvs_grows. eauto. eapply vvs_grows_set; eauto.
    + eapply vvs_range_list_assoc_set. eapply vvs_range_incr. 2: eauto. lia.
      red; lia.
    + eapply vvs_smaller_variables_set; eauto.
    + eapply wf_rir_incr; eauto. eapply vvs_grows_set; eauto.
    + eapply vvs_grows_set; eauto.
  Qed.

  Lemma wf_state_vvs_grows_incr:
    forall tsig env r2v vvs rir n rir' vvs' n' grd,
      wf_state tsig env r2v vvs rir n ->
      rir_grows vvs rir vvs' rir' grd ->
      wt_vvs vvs' ->
      vvs_range vvs' n' ->
      vvs_smaller_variables vvs' ->
      wf_rir rir' vvs' ->
      n <= n' ->
      wf_state tsig env r2v vvs' rir' n'.
  Proof.
    intros tsig env r2v vvs rir n rir' vvs' n' grd WFS RG WTV VR VSV WFR LE.
    inv WFS; split; eauto.
    eapply env_vvs_vvs_grows; eauto using rir_vvs_grows.
    eapply reg2var_vvs_grows; eauto using rir_vvs_grows.
  Qed.

  Lemma merge_branches_grows' :
    forall vm_tb vm_fb vvs nid cond_name vm' vvs' nid' tsig r2v r2v' rir,
      merge_branches vm_tb vm_fb vvs nid cond_name = (vm', vvs', nid') ->
      wf_state tsig vm_tb r2v vvs rir nid ->
      wf_state tsig vm_fb r2v' vvs rir nid ->
      valid_name cond_name nid ->
      wt_sact vvs (SVar cond_name) (bits_t 1) ->
      vvs_grows vvs vvs' /\
        nid <= nid' /\
        wf_state tsig vm' r2v' vvs' rir nid' /\
        Forall2 (fun '(xt,xf) x =>
                   forall b,
                     interp_sact vvs' (SVar cond_name) (Bits 1 [b]) ->
                     (forall v,
                         interp_sact vvs' (SVar (snd (if b then xt else xf))) v
                         <-> interp_sact vvs' (SVar (snd x)) v)
                ) (combine vm_tb vm_fb) vm'.
  Proof.
    intros. inv H0; inv H1.
    edestruct merge_branches_grows as (VVSGROWS4 & VVSRANGE4 & ENVVVS4 & NIDGROWS4 & VVSVALID4 & WTVVS4 & EVAL); eauto.
    repeat refine (conj _ _); eauto.
    split; eauto.
    eapply reg2var_vvs_grows; eauto.
    eapply wf_rir_incr; eauto.
  Qed.

  Lemma merge_reg2var_grows' :
    forall r2vt r2vf vvs nid cond_name r2v' vvs' nid' rir env tsig env2,
      merge_reg2vars r2vt r2vf cond_name vvs nid = (r2v', vvs', nid') ->
      wf_state tsig env2 r2vt vvs rir nid ->
      wf_state tsig env r2vf vvs rir nid ->
      valid_name cond_name nid ->
      wt_sact vvs (SVar cond_name) (bits_t 1) ->
      vvs_grows vvs vvs' /\ nid <= nid' /\
        wf_state tsig env r2v' vvs' rir nid' /\
        (forall sched_log action_log
                (MLR: forall b : bool,
                    interp_sact vvs (SVar cond_name) (Bits 1 [b]) ->
                    match_logs_r2v (if b then r2vt else r2vf) vvs rir sched_log action_log),
            match_logs_r2v r2v' vvs' rir sched_log action_log).
  Proof.
    intros. inv H0; inv H1.
    edestruct merge_reg2var_grows as (VVSGROWS4 & VVSRANGE4 & R2VVVS4 & NIDGROWS4 & VSV4 & WTVVS4 & EVAL4); eauto.
    split; eauto. split; eauto.
    split; eauto. split; eauto.
    eapply env_vvs_vvs_grows; eauto.
    eapply wf_rir_incr; eauto.
  Qed.

  Lemma wf_state_cons:
    forall tsig env r2v vvs rir n,
      wf_state tsig env r2v vvs rir n ->
      forall v vv t,
        wt_sact vvs vv t ->
        (forall v0, var_in_sact vv v0 -> v0 < n) ->
        wf_state ((v,t)::tsig) ((v,n)::env) r2v (list_assoc_set vvs n (t, vv)) rir (S n).
  Proof.
    intros tsig env r2v vvs rir n WFS v vv t WTs VIS.
    inv WFS; split; eauto.
    + eapply wt_vvs_set; eauto.
    + constructor. split; auto. rewrite list_assoc_gss. eauto.
      eapply env_vvs_vvs_grows. eauto.
      eapply vvs_grows_set; eauto.
    + eapply reg2var_vvs_grows. eauto.
      eapply vvs_grows_set; eauto.
    + apply vvs_range_list_assoc_set. eapply vvs_range_incr. 2: eauto. lia.
      red. eauto.
    + eapply vvs_smaller_variables_set; eauto.
    + eapply wf_rir_incr; eauto. eapply vvs_grows_set; eauto.
  Qed.

  Lemma wf_state_tl:
    forall tsig env r2v vvs rir n,
      wf_state tsig env r2v vvs rir n ->
      wf_state (tl tsig) (tl env) r2v vvs rir n.
  Proof.
    intros tsig env r2v vvs rir n WFS.
    inv WFS; split; eauto.
    inv wfs_env_vvs0; simpl; eauto. constructor.
  Qed.

  Lemma wf_state_change_rir:
    forall tsig env r2v vvs rir nid,
      wf_state tsig env r2v vvs rir nid ->
      forall rir' grd,
        rir_grows vvs rir vvs rir' grd ->
        wf_rir rir' vvs ->
        wf_state tsig env r2v vvs rir' nid.
  Proof.
    intros tsig env r2v vvs rir nid H rir' grd H0 H1.
    inv H; split; eauto.
  Qed.

  Lemma wf_state_change_r2v:
    forall tsig env r2v vvs rir n,
      wf_state tsig env r2v vvs rir n ->
      forall r v,
        (exists z : sact, list_assoc vvs v = Some (R (fst r), z)) ->
        wf_state tsig env (list_assoc_set r2v r v) vvs rir n.
  Proof.
    intros tsig env r2v vvs rir n H r0 v H0.
    inv H; split; eauto.
    eapply reg2var_vvs_set; eauto.
  Qed.

  Lemma match_Gamma_env_ex:
    forall Gamma env vvs,
      match_Gamma_env Gamma env vvs ->
      forall tsig,
        env_vvs env vvs tsig ->
        forall var v,
          list_assoc Gamma var = Some v ->
          exists n t s,
            list_assoc env var = Some n /\
              list_assoc tsig var = Some t /\
              list_assoc vvs n = Some (t, s) /\
              interp_sact vvs s v.
  Proof.
    induction 1; simpl; intros; eauto.
    easy.
    destruct H.
    inv H1.
    repeat destr_in H6. destruct H6 as (? & ? & ?). destruct x; simpl in *. subst.
    repeat destr_in H2; inv H2; eauto.
    exists n, t, x0; repeat split; eauto. inv H3. rewrite H4 in H1; inv H1; auto.
  Qed.


  Lemma match_Gamma_env_set:
    forall Gamma env vvs,
      match_Gamma_env Gamma env vvs ->
      forall v v1 n t0 o,
        vvs_range vvs n ->
        interp_sact vvs (reduce t0 o) v1 ->
        match_Gamma_env (list_assoc_set Gamma v v1) (list_assoc_set env v n)
                        (list_assoc_set vvs n (t0, reduce t0 o)).
  Proof.
    induction 1; simpl; intros; eauto.
    - constructor; simpl. split; auto.
      econstructor. rewrite list_assoc_gss. eauto.
      eapply vvs_grows_interp_sact; eauto. eapply vvs_grows_set; eauto.
      constructor.
    - destruct H. inv H3. destruct x, y. simpl in *; subst.
      destr.
      + subst.
        constructor; simpl; eauto.
        split; auto.
        econstructor. rewrite list_assoc_gss. eauto.
        eapply vvs_grows_interp_sact; eauto. eapply vvs_grows_set; eauto.
        eapply Forall2_impl. eapply H0. simpl; intros. destruct H4; split; auto.
        inv H7.
        eapply vvs_grows_interp_sact; eauto. eapply vvs_grows_set; eauto.
        econstructor; eauto.
      + constructor; simpl; eauto.
        split; auto.
        eapply vvs_grows_interp_sact; eauto. eapply vvs_grows_set; eauto.
        econstructor; eauto. eapply IHForall2; eauto.
  Qed.

  Lemma wt_sact_below:
    forall tsig env reg2var vvs rir n,
      wf_state tsig env reg2var vvs rir n ->
      forall s t,
        wt_sact vvs s t ->
        forall v, var_in_sact s v -> v < n.
  Proof.
    intros; eapply wt_sact_valid_vars; eauto. apply H.
  Qed.

  Lemma mge_merge_branches:
    forall Gamma env1 env2 cond_name env' vvs (b: bool),
      Forall2 (fun x y => fst x = fst y) env1 env2 ->
      Forall2 (fun x y => fst x = fst y) env1 env' ->
      match_Gamma_env Gamma (if b then env1 else env2) vvs ->
      interp_sact vvs (SVar cond_name) (Bits 1 [b]) ->
      Forall2 (fun '(xt,xf) x =>
                 forall b,
                   interp_sact vvs (SVar cond_name) (Bits 1 [b]) ->
                   (forall v,
                       interp_sact vvs (SVar (snd (if b then xt else xf))) v
                       <-> interp_sact vvs (SVar (snd x)) v)
              ) (combine env1 env2) env' ->
      match_Gamma_env Gamma env' vvs.
  Proof.
    induction Gamma; simpl; intros; eauto.
    - inv H1.
      destruct b; inv H; try congruence; inv H3; constructor.
    - inv H1. destruct H7. inv H.
      destruct b; congruence.
      assert (y = if b then x else y0) by (destruct b; congruence).
      assert (l' = if b then l else l'0) by (destruct b; congruence). clear H6.
      subst. simpl in H3. inv H0. inv H3.
      constructor; eauto.
      + split. rewrite H1. destr; congruence.
        eapply H10. eauto. auto.
      + eapply IHGamma. 3: eauto. all: eauto.
  Qed.

  Lemma rir_grows_weaken_guard:
    forall vvs1 rir1 vvs2 rir2 grd1 grd2,
      rir_grows vvs1 rir1 vvs2 rir2 grd1 ->
      (interp_sact vvs2 grd2 (Bits 1 [false]) -> interp_sact vvs2 grd1 (Bits 1 [false])) ->
      wt_sact vvs2 grd2 (bits_t 1) ->
      rir_grows vvs1 rir1 vvs2 rir2 grd2.
  Proof.
    intros. inv H; split; eauto.
    - red; intros.
      edestruct (rir_grows_read0s0 idx). split. eauto.
      intros; eauto.
    - red; intros.
      edestruct (rir_grows_read1s0 idx). split. eauto.
      intros; eauto.
    - red; intros.
      edestruct rir_grows_write0s0; eauto.
    - red; intros.
      edestruct rir_grows_write1s0; eauto.
  Qed.


  Lemma match_logs_r2v_vvs_set:
    forall r2v vvs sl al n x rir,
      match_logs_r2v r2v vvs rir sl al ->
      vvs_range vvs n ->
      match_logs_r2v r2v (list_assoc_set vvs n x) rir sl al.
  Proof.
    intros; eapply match_logs_r2v_vvs_grows. eauto.
    eapply vvs_grows_set; eauto.
  Qed.

  Lemma match_logs_r2v_rir_grows:
    forall r2v vvs sl al rir vvs' rir' grd,
      match_logs_r2v r2v vvs rir sl al ->
      rir_grows vvs rir vvs' rir' grd ->
      interp_sact vvs' grd (Bits 1 [false]) ->
      match_logs_r2v r2v vvs' rir' sl al.
  Proof.
    intros. inv H. inv H0.
    split.
    - intros; eapply vvs_grows_interp_sact; eauto.
    - intros idx EX c IN.
      destruct (list_assoc (rir_read1s rir) idx) eqn:?.
      + exploit mlr_read2. eauto. eauto. intros ISs.
        destruct (rir_grows_read1s0 idx). rewrite Heqo, IN in H0.
        rewrite <- H0. eauto. eauto.
      + destruct (rir_grows_read1s0 idx). rewrite Heqo, IN in H0.
        rewrite <- H0. constructor. eauto.
    - intros idx EX g wil GET wi IN.
      destruct (list_assoc (rir_write0s rir) idx) eqn:?.
      + destruct p.
        destruct (rir_grows_write0s0 idx wi).
        destruct (in_wil_dec idx wi (rir_write0s rir)).
        trim H; auto.
        destruct i as (gcond & wil' & EQ & INw). rewrite Heqo in EQ. inv EQ.
        exploit mlr_write2. eauto. eauto. eauto. eapply vvs_grows_interp_sact; eauto.
        trim H0. auto.
        trim H0. do 2 eexists; split; eauto.
        trim H0. eauto. eauto.
      + destruct (rir_grows_write0s0 idx wi).
        trim H0. intros (gcond & wil' & GET' & IN'). congruence.
        trim H0. do 2 eexists; split; eauto.
        trim H0. eauto. eauto.
    - intros idx EX g wil GET wi IN.
      destruct (list_assoc (rir_write1s rir) idx) eqn:?.
      + destruct p.
        destruct (rir_grows_write1s0 idx wi).
        destruct (in_wil_dec idx wi (rir_write1s rir)).
        trim H; auto.
        destruct i as (gcond & wil' & EQ & INw). rewrite Heqo in EQ. inv EQ.
        exploit mlr_write3. eauto. eauto. eauto. eapply vvs_grows_interp_sact; eauto.
        trim H0. auto.
        trim H0. do 2 eexists; split; eauto.
        trim H0. eauto. eauto.
      + destruct (rir_grows_write1s0 idx wi).
        trim H0. intros (gcond & wil' & GET' & IN'). congruence.
        trim H0. do 2 eexists; split; eauto.
        trim H0. eauto. eauto.
  Qed.

  Lemma log_app_log_cons:
    forall (l1: Log REnv) idx x l2,
      log_app (log_cons idx x l1) l2 = log_cons idx x (log_app l1 l2).
  Proof.
    unfold log_app. unfold log_cons.
    simpl. intros.
    apply equiv_eq.
    red. intros.
    rewrite getenv_map2.
    rewrite getenv_map2.
    destruct (eq_dec idx k). subst.
    rewrite ! get_put_eq. simpl. auto.
    rewrite ! get_put_neq by congruence.
    rewrite getenv_map2. auto.
  Qed.

  Lemma latest_write0_log_cons_read:
    forall idx v (action_log: Log REnv) reg prt,
      latest_write0 (log_cons idx (LE Logs.LogRead prt v) action_log) reg =
        latest_write0 action_log reg.
  Proof.
    unfold latest_write0. unfold log_find, log_cons.
    intros.
    destruct (eq_dec reg idx).
    subst; rewrite get_put_eq. simpl. auto.
    rewrite get_put_neq. simpl. auto. auto.
  Qed.

  Lemma do_read_log_cons_read:
    forall sched_log action_log idx v reg p prt,
      do_read sched_log (log_cons idx (LE Logs.LogRead p v) action_log) reg prt =
        do_read sched_log action_log reg prt.
  Proof.
    unfold do_read. intros. destr; auto.
    rewrite log_app_log_cons.
    rewrite latest_write0_log_cons_read. eauto.
  Qed.


  Lemma interp_sact_fold_or_conds_false:
    forall vvs l,
      Forall (fun a => interp_sact vvs a (Bits 1 [false])) l ->
      forall c0,
        interp_sact vvs c0 (Bits 1 [false]) ->
        interp_sact vvs (fold_left uor l c0) (Bits 1 [false]).
  Proof.
    induction 1; simpl; intros; eauto.
    apply IHForall. econstructor; eauto.
  Qed.

  Lemma interp_sact_or_conds_false:
    forall vvs l,
      Forall (fun a => interp_sact vvs a (Bits 1 [false])) l ->
      interp_sact vvs (or_conds l) (Bits 1 [false]).
  Proof.
    intros; eapply interp_sact_fold_or_conds_false; eauto. constructor.
  Qed.

  Lemma match_logs_r2v_add_read0:
    forall r2v vvs rir (sched_log action_log: Log REnv)
           (MLR : match_logs_r2v r2v vvs rir sched_log action_log)
           idx guard
           (Heqb : may_read sched_log P0 idx = true),
      match_logs_r2v r2v vvs (add_read0 rir guard idx) sched_log
                     (log_cons idx (LE (V:=val) Logs.LogRead P0 (Bits 0 [])) action_log).
  Proof.
    intros.
    inv MLR. unfold add_read0.
    split; intros; eauto.
    - rewrite do_read_log_cons_read; eauto.
    - rewrite log_app_log_cons in H.
      unfold log_existsb, log_cons in H.
      destruct (eq_dec idx idx0). subst.
      rewrite get_put_eq in H. simpl in H.
      simpl in H0. eauto. simpl in H0.
      rewrite get_put_neq in H by auto. eauto.
    - rewrite log_app_log_cons in H.
      unfold log_existsb, log_cons in H. simpl in H0.
      destruct (eq_dec idx idx0). subst.
      rewrite get_put_eq in H. simpl in H. eauto.
      rewrite get_put_neq in H by auto. eauto.
    - rewrite log_app_log_cons in H.
      unfold log_existsb, log_cons in H. simpl in H0.
      destruct (eq_dec idx idx0). subst.
      rewrite get_put_eq in H. simpl in H. eauto.
      rewrite get_put_neq in H by auto. eauto.
  Qed.

  Lemma match_logs_r2v_add_read1:
    forall r2v vvs rir (sched_log action_log: Log REnv)
           (MLR : match_logs_r2v r2v vvs rir sched_log action_log)
           idx guard
           (Heqb : may_read sched_log P1 idx = true),
      match_logs_r2v r2v vvs (add_read1 rir guard idx) sched_log
                     (log_cons idx (LE (V:=val) Logs.LogRead P1 (Bits 0 [])) action_log).
  Proof.
    intros.
    inv MLR. unfold add_read1.
    split; intros; eauto.
    - rewrite do_read_log_cons_read; eauto.
    - rewrite log_app_log_cons in H.
      unfold log_existsb, log_cons in H.
      destruct (eq_dec idx idx0). subst.
      rewrite get_put_eq in H. simpl in H. congruence.
      simpl in H0. eauto. simpl in H0.
      rewrite get_put_neq in H by auto.
      destr_in H0.
      rewrite list_assoc_gso in H0; eauto.
      rewrite list_assoc_gso in H0; eauto.
    - rewrite log_app_log_cons in H.
      unfold log_existsb, log_cons in H. simpl in H0.
      destruct (eq_dec idx idx0). subst.
      rewrite get_put_eq in H. simpl in H. eauto.
      rewrite get_put_neq in H by auto. eauto.
    - rewrite log_app_log_cons in H.
      unfold log_existsb, log_cons in H. simpl in H0.
      destruct (eq_dec idx idx0). subst.
      rewrite get_put_eq in H. simpl in H. eauto.
      rewrite get_put_neq in H by auto. eauto.
  Qed.

  Lemma wf_rir_grows:
    forall rir v1 v2 n,
      wf_rir rir v1 ->
      vvs_grows v1 v2 ->
      wt_vvs v1 ->
      vvs_range v1 n -> vvs_smaller_variables v1 ->
      wf_rir rir v2.
  Proof.
    intros. inv H; split; eauto.
    - intros; eapply wt_sact_vvs_grows; eauto.
    - intros; eapply wt_sact_vvs_grows; eauto.
    - eapply wf_write_log_raw_incr; eauto.
    - eapply wf_write_log_raw_incr; eauto.
  Qed.

  Lemma rir_grows_add_write0:
    forall vvs rir grd idx v rir' grd' tsig env r2v n,
      wt_sact vvs grd (bits_t 1) ->
      wf_state tsig env r2v vvs rir n ->
      add_write0 rir grd idx v = (rir', grd') ->
      forall (WTv: wt_sact vvs v (R idx)),
        let vvs1 := list_assoc_set vvs n (R idx, v) in
        (* let vvs2 := list_assoc_set vvs1 (n + 1) (R idx, v) in *)
        let r2v1 := list_assoc_set r2v (idx, P1) n in
        (* let r2v2 := list_assoc_set r2v1 (idx, P1) (n + 1) in *)
        rir_grows vvs rir vvs1 rir' grd /\
          wf_state tsig env r2v1 vvs1 rir' (n + 1) /\
          wt_sact vvs1 grd' (bits_t 1).
  Proof.
    unfold add_write0. intros. destr_in H1. inv H1.
    split; [|split].
    - split; simpl; eauto using incl_refl, write_log_raw_grows_refl, cond_log_grows_refl, vvs_grows_refl.
      + eapply cond_log_grows_change_vvs. eauto. inv H0; eauto. intros.
        red in H1. repeat rewrite list_assoc_gso by lia. eauto.
        intros; eapply wf_rir_read0s; eauto. inv H0; eauto.
      + eapply cond_log_grows_change_vvs. eauto. inv H0; eauto. intros.
        red in H1. repeat rewrite list_assoc_gso by lia. eauto.
        intros; eapply wf_rir_read1s; eauto. inv H0; eauto.
      + red. intros; split; intros.
        * destruct H1 as (gcond & wil & GET & IN). red.
          rewrite list_assoc_spec.
          destr.
          -- subst. rewrite GET in Heqp. inv Heqp. do 2 eexists; split; eauto. rewrite in_app_iff; auto.
          -- do 2 eexists; split; eauto.
        * destruct H2 as (gcond & wil & GET & IN).
          rewrite list_assoc_spec in GET.
          destr_in GET.
          -- inv GET.
             unfold in_wil in H1.
             destr_in Heqp; inv Heqp.
             destruct p. simpl in *.
             rewrite in_app_iff in IN. destruct IN.
             elim H1; do 2 eexists; split; eauto.
             destruct H2 as [|[]]. subst. simpl. eauto.
             destruct IN as [|[]]. subst. simpl. eauto.
          -- elim H1. do 2 eexists; split; eauto.
      + red; intros.
        exploit wfs_vvs_range; eauto. intro VN; red in VN.
        repeat rewrite list_assoc_gso by lia. eauto.
      + eapply wt_sact_vvs_grows; eauto.
        red; intros.
        exploit wfs_vvs_range; eauto. intro VN; red in VN.
        repeat rewrite list_assoc_gso by lia. eauto.
    - inv H0.
      assert (VG: vvs_grows vvs
                            (list_assoc_set vvs n (R idx, v))).
      {
        eapply vvs_grows_set. eauto. lia.
      }
      split.
      + eapply wt_vvs_set; eauto.
      + eapply env_vvs_change_vvs; eauto.
      + eapply reg2var_vvs_set.
        eapply reg2var_vvs_grows. eauto. eauto.
        simpl. rewrite list_assoc_gss; eauto.
      + eapply vvs_range_list_assoc_set. eapply vvs_range_incr. 2: eauto. lia. red; lia.
      + red; intros.
        repeat rewrite list_assoc_spec in H0.
        red.
        repeat destr_in H0; subst; eauto. inv H0.
        eapply wt_sact_valid_vars; eauto.
        eapply wfs_vsv0 in H0; eauto. eapply H0; eauto.
      + eapply wf_rir_add_write0.
        7:{
          unfold add_write0. rewrite Heqp. simpl. eauto.
        }
        *
          eapply wf_rir_grows; eauto.
        * eapply wt_sact_vvs_grows. 2: eauto. eauto.
        * eapply wt_sact_vvs_grows. 2: eauto. eauto.
        * eapply wt_vvs_set; eauto.
        * red; intros.
          repeat rewrite list_assoc_spec in H0.
          red.
          repeat destr_in H0; subst; eauto. inv H0.
          eapply wt_sact_valid_vars; eauto.
          eapply wfs_vsv0 in H0; eauto. eapply H0; eauto.
        * eapply vvs_range_list_assoc_set. instantiate (1:=n+1).
          eapply vvs_range_incr. 2: eauto. lia. red; lia.
    - assert (VG: vvs_grows vvs (list_assoc_set vvs n (R idx, v))).
      {
        inv H0.
        eapply vvs_grows_set; eauto.
      }
      econstructor.
      eapply wt_sact_vvs_grows; eauto.
      eapply wt_sact_or_conds.
      eapply Forall_list_options. unfold option_map; simpl. intros x y A EQ. subst.
      destruct A as [A|[A|[A|[]]]]; repeat destr_in A; inv A.
      + inv Heqp. destruct p. apply list_assoc_in in Heqo.
        eapply wf_wlr_glob_cond in Heqo; eauto.
        eapply wf_write_log_raw_incr; eauto. eapply wfs_rir; eauto.
        all: inv H0; eauto.
      + apply list_assoc_in in H2.
        eapply wf_rir_read1s in H2.
        eapply wt_sact_vvs_grows; eauto. apply H0.
      + destruct p. apply list_assoc_in in Heqo.
        eapply wf_wlr_glob_cond in Heqo; eauto.
        eapply wf_write_log_raw_incr; eauto. eapply wfs_rir; eauto.
        all: inv H0; eauto.
      + constructor.
  Qed.

  Lemma rir_grows_add_write1:
    forall vvs rir grd idx v rir' grd' tsig env r2v n,
      wt_sact vvs grd (bits_t 1) ->
      wf_state tsig env r2v vvs rir n ->
      add_write1 rir grd idx v = (rir', grd') ->
      forall (WTv: wt_sact vvs v (R idx)),
        (* let vvs1 := list_assoc_set vvs n (R idx, v) in *)
        (* let r2v1 := list_assoc_set r2v (idx, P1) n in *)
        rir_grows vvs rir vvs rir' grd /\
          wf_state tsig env r2v vvs rir' n /\
          wt_sact vvs grd' (bits_t 1).
  Proof.
    unfold add_write1. intros. destr_in H1. inv H1.
    split; [|split].
    - split; simpl; eauto using incl_refl, write_log_raw_grows_refl, cond_log_grows_refl, vvs_grows_refl.
      + red. intros; split; intros.
        * destruct H1 as (gcond & wil & GET & IN). red.
          rewrite list_assoc_spec.
          destr.
          -- subst. rewrite GET in Heqp. inv Heqp. do 2 eexists; split; eauto. rewrite in_app_iff; auto.
          -- do 2 eexists; split; eauto.
        * destruct H2 as (gcond & wil & GET & IN).
          rewrite list_assoc_spec in GET.
          destr_in GET.
          -- inv GET.
             unfold in_wil in H1.
             destr_in Heqp; inv Heqp.
             destruct p. simpl in *.
             rewrite in_app_iff in IN. destruct IN.
             elim H1; do 2 eexists; split; eauto.
             destruct H2 as [|[]]. subst. simpl. eauto.
             destruct IN as [|[]]. subst. simpl. eauto.
          -- elim H1. do 2 eexists; split; eauto.
    - inv H0.
      split; eauto.
      eapply wf_rir_add_write1; eauto.
      unfold add_write1. rewrite Heqp. simpl. eauto.
    - econstructor. eauto.
      eapply wt_sact_or_conds.
      eapply Forall_list_options. unfold option_map; simpl. intros x y A EQ. subst.
      destruct A as [A|[]]; repeat destr_in A; inv A.
      + inv Heqp. destruct p. apply list_assoc_in in Heqo.
        eapply wf_wlr_glob_cond in Heqo; eauto. eapply wfs_rir; eauto.
      + constructor.
  Qed.

  Lemma add_write0_fail:
    forall sched_log action_log idx vvs rir rir' fail_cond grd v tsig env r2v g' ,
      may_write sched_log action_log P0 idx = true ->
      wf_state tsig env r2v vvs rir g' ->
      match_logs_r2v r2v vvs rir sched_log action_log ->
      add_write0 rir grd idx v = (rir', fail_cond) ->
      interp_sact vvs grd (Bits 1 [true]) ->
      interp_sact vvs fail_cond (Bits 1 [false]).
  Proof.
    intros sched_log action_log idx vvs rir rir' fail_cond grd v tsig env r2v g' MW WR MLR AW GRD.
    unfold add_write0 in AW.
    unfold may_write in MW.
    rewrite ! andb_true_iff in MW.
    rewrite ! negb_true_iff in MW.
    destruct MW as ((A & B) & C). destr_in AW. inv AW.
    econstructor. eauto.
    eapply interp_sact_or_conds_false.
    eapply Forall_list_options. unfold option_map; simpl; intros. subst.
    destruct H as [H|[H|[H|[]]]]; repeat destr_in H; inv H; inv Heqp.
    + inv MLR. destruct p. 
      specialize (mlr_write2 _ B _ _ Heqo).
      generalize (list_assoc_in _ _ _ Heqo). intro IN. simpl in *.
      exploit wf_wlr_glob_cond. apply wf_rir_write0s. apply WR. eauto. intro WTs. simpl in *.
      edestruct wf_sact_interp as (? & ISs & WTvs). apply WTs. eauto.
      apply wt_val_bool in WTvs. destruct WTvs. subst.
      destruct x0. 2: now auto.
      exploit wf_rir_write0s. apply WR. inversion 1.
      exploit wf_wlr_glob_interp0. eauto. simpl. intro X; rewrite X in ISs.
      rewrite Exists_exists in ISs.
      destruct ISs as (? & INw & ISw).
      exploit mlr_write2. apply INw. intro ISw2.
      exploit interp_sact_determ. apply ISw. apply ISw2. intro D; inv D.
    + inv MLR. eauto.
    + inv MLR. destruct p.
      specialize (mlr_write3 _ C _ _ Heqo).
      generalize (list_assoc_in _ _ _ Heqo). intro IN. simpl in *.
      exploit wf_wlr_glob_cond. apply wf_rir_write1s. apply WR. eauto. intro WTs. simpl in *.
      edestruct wf_sact_interp as (? & ISs & WTvs). apply WTs. eauto.
      apply wt_val_bool in WTvs. destruct WTvs. subst.
      destruct x0. 2: now auto.
      exploit wf_rir_write1s. apply WR. inversion 1.
      exploit wf_wlr_glob_interp0. eauto. simpl. intro X; rewrite X in ISs.
      rewrite Exists_exists in ISs.
      destruct ISs as (? & INw & ISw).
      exploit mlr_write3. apply INw. intro ISw2.
      exploit interp_sact_determ. apply ISw. apply ISw2. intro D; inv D.
    + reflexivity.
  Qed.
  Lemma add_write1_fail:
    forall sched_log action_log idx vvs rir rir' fail_cond grd v tsig env r2v g' ,
      may_write sched_log action_log P1 idx = true ->
      wf_state tsig env r2v vvs rir g' ->
      match_logs_r2v r2v vvs rir sched_log action_log ->
      add_write1 rir grd idx v = (rir', fail_cond) ->
      interp_sact vvs grd (Bits 1 [true]) ->
      interp_sact vvs fail_cond (Bits 1 [false]).
  Proof.
    intros sched_log action_log idx vvs rir rir' fail_cond grd v tsig env r2v g' MW WR MLR AW GRD.
    unfold add_write1 in AW.
    unfold may_write in MW.
    rewrite ! negb_true_iff in MW.
    destr_in AW. inv AW.
    econstructor. eauto.
    eapply interp_sact_or_conds_false.
    eapply Forall_list_options. unfold option_map; simpl; intros. subst.
    destruct H as [H|[]]; repeat destr_in H; inv H; inv Heqp.
    + inv MLR. destruct p.
      specialize (mlr_write3 _ MW _ _ Heqo).
      generalize (list_assoc_in _ _ _ Heqo). intro IN. simpl in *.
      exploit wf_wlr_glob_cond. apply wf_rir_write1s. apply WR. eauto. intro WTs. simpl in *.
      edestruct wt_sact_interp as (? & ISs & WTvs). 4: apply WTs. 1-3: inv WR; eauto.
      apply wt_val_bool in WTvs. destruct WTvs. subst.
      destruct x0. 2: now auto.
      exploit wf_rir_write1s. apply WR. inversion 1.
      exploit wf_wlr_glob_interp0. eauto. simpl. intro X; rewrite X in ISs.
      rewrite Exists_exists in ISs.
      destruct ISs as (? & INw & ISw).
      exploit mlr_write3. apply INw. intro ISw2.
      exploit interp_sact_determ. apply ISw. apply ISw2. intro D; inv D.
    + reflexivity.
  Qed.


  Lemma latest_write0_log_cons_write_other:
    forall idx v (action_log: Log REnv) reg prt,
      idx <> reg ->
      latest_write0 (log_cons idx (LE Logs.LogWrite prt v) action_log) reg =
        latest_write0 action_log reg.
  Proof.
    unfold latest_write0. unfold log_find, log_cons.
    intros.
    rewrite get_put_neq. simpl. auto. auto.
  Qed.

  Lemma do_read_log_cons_write_other:
    forall sched_log action_log idx v reg p prt,
      reg <> idx ->
      do_read sched_log (log_cons idx (LE Logs.LogWrite p v) action_log) reg prt =
        do_read sched_log action_log reg prt.
  Proof.
    unfold do_read. intros. destr; auto.
    rewrite log_app_log_cons.
    rewrite latest_write0_log_cons_write_other; eauto.
  Qed.

  Lemma match_logs_r2v_add_write0:
    forall r2v vvs r0 sched_log action_log guard idx v rir' s0 n tsig env v' ,
      wf_state tsig env r2v vvs r0 n ->
      match_logs_r2v r2v vvs r0 sched_log action_log ->
      add_write0 r0 guard idx v = (rir', s0) ->
      may_write sched_log action_log P0 idx = true ->
      interp_sact vvs v v' ->
      match_logs_r2v
        (list_assoc_set r2v (idx, P1) n)
        (list_assoc_set vvs n (R idx, v)) 
        rir' sched_log
        (log_cons idx (LE (V:=val) Logs.LogWrite P0 v') action_log).
  Proof.
    intros r2v vvs r0 sched_log action_log guard idx v rir' s0 n tsig env v'
           WFS MLR AW MW IV.
    inv MLR. unfold add_write0 in AW. destr_in AW. inv AW.
    split.
    - intros reg prt n0 MR GET.
      rewrite ! list_assoc_spec in GET.
      repeat destr_in GET; eauto.
      + inv GET. clear Heqs0. inv e. econstructor. rewrite list_assoc_gss. eauto.
        unfold do_read. rewrite log_app_log_cons. unfold latest_write0.
        unfold log_find, log_cons. rewrite get_put_eq. simpl.
        eapply vvs_grows_interp_sact. 2: eauto.
        eapply vvs_grows_set; eauto.
        apply WFS.
      + destruct (eq_dec idx reg). subst. destruct prt; try congruence. simpl.
        exploit mlr_read0. eauto. eauto. simpl.
        eapply vvs_grows_interp_sact; eauto. eapply vvs_grows_set; eauto.
        apply WFS.
        exploit mlr_read0. eauto. eauto. simpl.
        intros.
        eapply vvs_grows_interp_sact in H; eauto. 2: eapply vvs_grows_set; eauto.
        2: apply WFS.


        rewrite do_read_log_cons_write_other. eauto. auto.
    - simpl. intros idx0 EX c GET.
      eapply vvs_grows_interp_sact. eapply vvs_grows_set; eauto. apply WFS.
      eapply mlr_read2; eauto.
      revert EX.
      rewrite log_app_log_cons.
      unfold log_existsb, log_cons.
      destruct (eq_dec idx idx0).
      subst; rewrite get_put_eq. simpl. auto.
      rewrite get_put_neq; simpl; auto.
    - simpl. intros idx0 EX g wil GET wi IN.
      rewrite list_assoc_spec in GET.
      destr_in GET.
      + inv GET.
        revert EX.
        rewrite log_app_log_cons.
        unfold log_existsb, log_cons. rewrite get_put_eq. simpl. congruence.
      + revert EX.
        rewrite log_app_log_cons.
        unfold log_existsb, log_cons. rewrite get_put_neq; auto. intro EX.
        eapply vvs_grows_interp_sact. eapply vvs_grows_set; eauto. apply WFS.
        eapply mlr_write2; eauto.
    - simpl. intros idx0 EX g wil GET wi IN.
      eapply vvs_grows_interp_sact. eapply vvs_grows_set; eauto. apply WFS.
      eapply mlr_write3; eauto.
      revert EX.
      rewrite log_app_log_cons.
      unfold log_existsb, log_cons.
      destruct (eq_dec idx idx0).
      subst; rewrite get_put_eq. simpl. auto.
      rewrite get_put_neq; simpl; auto.
  Qed.
  Lemma match_logs_r2v_add_write1:
    forall r2v vvs r0 sched_log action_log guard idx v rir' s0 n tsig env v' ,
      wf_state tsig env r2v vvs r0 n ->
      match_logs_r2v r2v vvs r0 sched_log action_log ->
      add_write1 r0 guard idx v = (rir', s0) ->
      may_write sched_log action_log P1 idx = true ->
      interp_sact vvs v v' ->
      match_logs_r2v
        r2v
        vvs
        rir' sched_log
        (log_cons idx (LE (V:=val) Logs.LogWrite P1 v') action_log).
  Proof.
    intros r2v vvs r0 sched_log action_log guard idx v rir' s0 n tsig env v'
           WFS MLR AW MW IV.
    inv MLR. unfold add_write1 in AW. destr_in AW. inv AW.
    split.
    - intros reg prt n0 MR GET.
      exploit mlr_read0; eauto.
      unfold do_read. rewrite log_app_log_cons. unfold latest_write0.
      unfold log_find, log_cons.
      destr; eauto.
      destruct (eq_dec idx reg). subst.
      rewrite get_put_eq. simpl. auto.
      rewrite get_put_neq. auto. auto.
    - simpl. intros idx0 EX c GET.
      eapply mlr_read2; eauto.
      revert EX.
      rewrite log_app_log_cons.
      unfold log_existsb, log_cons.
      destruct (eq_dec idx idx0).
      subst; rewrite get_put_eq. simpl. auto.
      rewrite get_put_neq; simpl; auto.
    - simpl. intros idx0 EX g wil GET wi IN.
      revert EX.
      rewrite log_app_log_cons.
      unfold log_existsb, log_cons.
      destruct (eq_dec idx idx0).
      subst. rewrite get_put_eq. simpl. eauto.
      rewrite get_put_neq; auto. eauto.
    - simpl. intros idx0 EX g wil GET wi IN.
      rewrite list_assoc_spec in GET. destr_in GET.
      + inv GET.
        revert EX.
        rewrite log_app_log_cons.
        unfold log_existsb, log_cons. rewrite get_put_eq. simpl. congruence.
      + revert EX.
        rewrite log_app_log_cons.
        unfold log_existsb, log_cons.
        rewrite get_put_neq; eauto.
  Qed.

  Lemma get_rule_information_aux_env_grows:
    forall (ua: uact)
           tsig (env: list (string * nat)) reg2var (guard: sact)
           (rir: rule_information_raw) (nid: nat)
           v env' reg2var' vvs fail_cond rir' nid' t vvs0
           (GRIA: get_rule_information_aux ua tsig env reg2var vvs0 guard rir nid = (v, env', reg2var', vvs, fail_cond, rir', nid', t))
           tret
           (WT: BitsToLists.wt_daction pos_t string string (R:=R) (Sigma:=Sigma) tsig ua tret)
           (WFS: wf_state tsig env reg2var vvs0 rir nid)
           (WTGUARD: wt_sact vvs0 guard (bits_t 1)),
      wf_state tsig env' reg2var' vvs rir' nid'
      /\ rir_grows vvs0 rir vvs rir' guard
      /\ wt_sact vvs (reduce t v) t
      /\ wt_sact vvs fail_cond (bits_t 1)
      /\ nid <= nid'
      /\ same_env env env'
      /\ tret = t
      /\ forall Gamma sched_log action_log action_log' vret Gamma'
                (WTRENV: wt_renv R REnv r)
                (WTG: wt_env _ tsig Gamma)
                (GE: match_Gamma_env Gamma env vvs0)
                (MLR: match_logs_r2v reg2var vvs0 rir sched_log action_log)
                (INTERP: interp_daction r sigma Gamma sched_log action_log ua = Some (action_log', vret, Gamma'))
                (GUARDOK: interp_sact vvs0 guard (Bits 1 [true])),
        interp_sact vvs (reduce t v) vret
        /\ interp_sact vvs fail_cond (Bits 1 [false])
        /\ match_Gamma_env Gamma' env' vvs
        /\ match_logs_r2v reg2var' vvs rir' sched_log action_log'
        /\ wt_env _ tsig Gamma'.
  Proof.
    Opaque skipn.
    intros ua; pattern ua; eapply daction_ind'; simpl; intros; eauto.
    all: repeat destr_in GRIA; inv GRIA; eauto; try now (intuition congruence).
    - inv WT.
    - inv WT.
      intuition try congruence. eapply rir_grows_refl. auto.
      apply wt_sact_reduce. easy. repeat constructor. lia. apply same_env_refl.
    - inv WT.
      repeat refine (conj _ _); eauto.
      + eapply rir_grows_refl. auto.
      + simpl; intros. edestruct env_vvs_ex; eauto. inv WFS; eauto.
        econstructor; eauto.
      + repeat constructor.
      + apply same_env_refl.
      + inv H1.
        eapply assoc_list_assoc in H. congruence.
      + simpl. intros. unfold opt_bind in INTERP.
        repeat destr_in INTERP; inv INTERP.
        edestruct match_Gamma_env_ex as (? & tt & s & GET1 & GET2 & GET3 & GET4); eauto.
        inv WFS; eauto. rewrite GET1 in Heqo; inv Heqo.
        rewrite GET2 in Heqo0; inv Heqo0.
        repeat refine (conj _ _); eauto.
        econstructor; eauto. econstructor; eauto.
    - exfalso; eapply env_vvs_some_none; eauto.
      inv WFS; eauto.
    - inv WT. inv H1.
      apply assoc_list_assoc in H.
      edestruct env_vvs_none_some. inv WFS; eauto. eauto. eauto.
    - intuition try congruence. eapply rir_grows_refl. auto.
      simpl. econstructor. inv WT.
      apply wt_val_of_value.
      repeat constructor. lia.
      apply same_env_refl.
      inv WT. auto.
      inv INTERP.
      simpl; econstructor. constructor.
    - inv WT.
      Ltac dhyp H :=
        let wfs := fresh "WFS" in
        let rg := fresh "RIRGROWS" in
        (* let v := fresh "VARRES" in *)
        let wt := fresh "WTRES" in
        let vvs := fresh "FAILWT" in
        let ng := fresh "NIDGROWS" in
        let se := fresh "SAMEENV" in
        let teq := fresh "TEQ" in
        let interp := fresh "INTERPHYP" in
        (* let ig := fresh "INTERPGUARD" in *)
        (* let mge := fresh "MGE" in *)
        (* let wte := fresh "WTE" in *)
        edestruct H as (wfs & rg & wt & vvs & ng & se & teq & interp); eauto.
      dhyp H.
      subst.
      inversion H5; subst. eapply assoc_list_assoc in H0.
      exploit wf_state_set.  3: eauto. 2: eauto. eauto.
      intros WFS2.
      assert (RG: rir_grows vvs0 rir (list_assoc_set l n (projT1 tm, reduce (projT1 tm) o)) rir' (uor guard const_false)).
      {
        eapply rir_grows_trans. 4: eapply rir_grows_set; eauto. eauto. 2: eauto. auto.
        unfold valid_name; lia.
      }
      repeat (refine (conj _ _)); eauto.
      +
        eapply rir_grows_weaken_guard; eauto.
        intros; econstructor; eauto. constructor. simpl. auto.
        inv RG. inv rir_wt_grd0. inv H9. auto.
      + eapply wt_sact_reduce; eauto. easy.
      + eapply wt_sact_vvs_grows. 2: eauto.
        eapply vvs_grows_set. inv WFS0; eauto. lia.
      + eapply same_env_set_in; eauto.
        destruct (list_assoc env v)eqn:?.
        eapply list_assoc_in_keys; eauto.
        edestruct env_vvs_none_some. inv WFS; eauto. eauto. eauto.
      + simpl; intros.
        unfold opt_bind in INTERP.
        repeat destr_in INTERP; inv INTERP.
        dihyp INTERPHYP.
        repeat (refine (conj _ _)); eauto.
        * econstructor.
        * eapply vvs_grows_interp_sact; eauto.
          eapply vvs_grows_set. inv WFS0; eauto. lia.
        * eapply match_Gamma_env_set; eauto. inv WFS0; eauto.
        * eapply match_logs_r2v_vvs_set; eauto. inv WFS0; eauto.
        * eapply wt_env_set; eauto.
          edestruct (wt_sact_interp) with (a:=reduce (projT1 tm) o) as (vv & IS & WTV); eauto.
          1-3: inv WFS0; eauto.
          exploit interp_sact_determ. apply IS. apply INTERPVAL. intros ->; eauto.
    - inv WT.
      dhyp H. subst.
      dhyp H0.
      eapply wt_sact_vvs_grows. 2: eauto. eauto using rir_vvs_grows.
      subst.
      repeat refine (conj _ _); eauto.
      + eapply rir_grows_weaken_guard.
        eapply rir_grows_trans. 2,4: eauto. all: eauto.
        intros; econstructor; eauto.
        eapply wt_sact_vvs_grows. 2: eauto.
        eauto using vvs_grows_trans, rir_vvs_grows.
      + econstructor; eauto.
        eapply wt_sact_vvs_grows; eauto using rir_vvs_grows.
        constructor.
      + lia.
      + eapply same_env_trans; eauto.
      + intros.
        unfold opt_bind in INTERP. repeat destr_in INTERP; inv INTERP.
        dihyp INTERPHYP.
        dihyp INTERPHYP0.
        eapply vvs_grows_interp_sact. 2: eauto. eauto using vvs_grows_trans, rir_vvs_grows.
        repeat refine (conj _ _); eauto.
        * econstructor.
          eapply vvs_grows_interp_sact. 2: eauto. eapply rir_vvs_grows; eauto. eauto.
          reflexivity.
    - inv WT.
      dhyp H. subst.
      assert (WFS2:   wf_state ((v, t0) :: tsig) ((v, n) :: l1) l0
                               (list_assoc_set l n (t0, reduce t0 o)) r0 (S n)).
      {
        eapply wf_state_cons; eauto. intros.
        eapply wt_sact_below in H1; eauto.
      }
      dhyp H0.
      + eapply wt_sact_vvs_grows; eauto using rir_vvs_grows.
        eapply rir_vvs_grows.
        eapply rir_grows_trans. 2: eauto. eauto.
        2: eapply rir_grows_set; eauto. eauto.
        unfold valid_name; lia.
      + subst. inv SAMEENV0. simpl in H3. subst.
        change (skipn 1 (y::l')) with l'.
        assert (WFS3:   wf_state tsig l' reg2var' vvs rir' nid').
        apply wf_state_tl in WFS1. simpl in WFS1. eauto.
        assert (RG3: rir_grows l r0 (list_assoc_set l n (t0, reduce t0 o)) r0 const_false).
        {
          eapply rir_grows_set. eauto. unfold valid_name; lia.
        }
        repeat (refine (conj _ _)); eauto.
        * eapply rir_grows_weaken_guard.
          eapply rir_grows_trans. 2: eauto. eauto.
          2: eapply rir_grows_trans. 3: eauto. eauto. eauto. eauto. eauto.
          intros; repeat econstructor; eauto. simpl. eauto.
          simpl; eauto.
          eapply wt_sact_vvs_grows. 2: eauto.
          eapply vvs_grows_trans; eauto using rir_vvs_grows, vvs_grows_trans.
        * econstructor.
          -- eapply wt_sact_vvs_grows. 2: eauto.
             eapply vvs_grows_trans; eauto using rir_vvs_grows.
          -- eauto.
          -- econstructor.
        * lia.
        * eapply same_env_trans; eauto.
        * intros.
          unfold opt_bind in INTERP. repeat destr_in INTERP; inv INTERP.
          dihyp INTERPHYP.
          dihyp INTERPHYP0.
          -- eapply wt_env_cons; eauto.
             inv WFS0.
             edestruct (wt_sact_interp) with (a:=reduce t0 o) as (vv & IS & WTV); eauto.
             exploit interp_sact_determ. apply IS. apply INTERPVAL. intros ->; eauto.
          -- constructor. split; auto. simpl. econstructor. rewrite list_assoc_gss. eauto.
             eapply vvs_grows_interp_sact. 2: eauto. eapply vvs_grows_set. eapply wfs_vvs_range; eauto. lia.
             eapply match_Gamma_env_vvs_grows; eauto.
             eapply vvs_grows_set. eapply wfs_vvs_range; eauto. lia.
          -- eapply match_logs_r2v_vvs_grows; eauto.
             eapply vvs_grows_set. eapply wfs_vvs_range; eauto. lia.
          -- eapply vvs_grows_interp_sact. 2: eauto. eauto using vvs_grows_trans, rir_vvs_grows.
          -- repeat (refine (conj _ _)); eauto. 
             econstructor; eauto.
             eapply vvs_grows_interp_sact. 2: eauto.
             eapply vvs_grows_trans; eauto. eapply vvs_grows_set. eapply wfs_vvs_range; eauto.
             2: eauto using rir_vvs_grows. lia. reflexivity.
             inv MGE0. simpl. eauto.
             inv WTE0. simpl. eauto.

    - inv WT.
      dhyp H. subst.
      set (ll1 := (list_assoc_set l n (bits_t 1, reduce (bits_t 1) o))).
      set (ll2 := (list_assoc_set ll1 (n + 1) (bits_t 1, uand guard (SVar n)))).
      set (ll3 := (list_assoc_set ll2 (n + 2) (bits_t 1, uand guard (unot (SVar n))))).

      assert (WFSl1: wf_state tsig l1 l0 ll1 r0 (n + 1) /\ vvs_grows l ll1).
      {
        eapply wf_state_vvs_set; eauto. intros.
        eapply wt_sact_below in H2; eauto. lia.
      }
      destruct WFSl1 as (WFSl1 & VG1).
      assert (WFSl2: wf_state tsig l1 l0 ll2 r0 (n + 2) /\ vvs_grows ll1 ll2).
      {
        eapply wf_state_vvs_set; eauto.
        econstructor. eapply wt_sact_vvs_grows. 2: eauto.
        eapply vvs_grows_trans; eauto using rir_vvs_grows.
        econstructor. unfold ll1. rewrite list_assoc_gss. eauto.
        constructor. simpl.
        intros v VIS. inv VIS.
        eapply wt_sact_below in H7; eauto. eapply wt_sact_vvs_grows. 2: eauto.
        eauto using vvs_grows_trans, rir_vvs_grows.
        inv H7. lia.
        lia.
      }
      destruct WFSl2 as (WFSl2 & VG2).
      assert (WFSl3: wf_state tsig l1 l0 ll3 r0 (n + 3) /\ vvs_grows ll2 ll3).
      {
        eapply wf_state_vvs_set; eauto.
        econstructor. eapply wt_sact_vvs_grows. 2: eauto.
        eapply vvs_grows_trans; eauto using rir_vvs_grows.
        eapply vvs_grows_trans; eauto using rir_vvs_grows.
        econstructor. econstructor. unfold ll2, ll1.
        rewrite list_assoc_gso by lia.
        rewrite list_assoc_gss. eauto.
        constructor. constructor. simpl.
        intros v VIS. inv VIS.
        eapply wt_sact_below in H7; eauto. eapply wt_sact_vvs_grows. 2: eauto.
        eauto using vvs_grows_trans, rir_vvs_grows.
        inv H7. inv H5. lia.
        lia.
      }
      destruct WFSl3 as (WFSl3 & VG3).
      dhyp H0.
      econstructor.
      rewrite list_assoc_gso by lia; rewrite list_assoc_gss; eauto.
      subst.
      dhyp H1.
      inv WFS1; eapply wf_state_vvs_grows_incr; eauto.
      econstructor. eapply rir_vvs_grows. eauto. rewrite list_assoc_gss. eauto.
      subst.
      assert (WTcond: wt_sact l5 (SVar n) (bits_t 1)).
      {
        eapply wt_sact_vvs_grows.
        eapply vvs_grows_trans. 2: eapply rir_vvs_grows; eauto.
        eapply rir_vvs_grows; eauto. econstructor.
        rewrite list_assoc_gso by lia.
        rewrite list_assoc_gso by lia.
        rewrite list_assoc_gss. eauto.
      }
      edestruct merge_branches_grows' as (VVSGROWS4 & NIDGROWS4 & WFS4 & EVAL4); eauto.
      inv WFS2; eapply wf_state_vvs_grows_incr; eauto.
      red; lia.
      assert (RG4: rir_grows l2 r1 l9 rir' (SVar (n+2))).
      {
        eapply rir_grows_weaken_guard.
        - eapply rir_grows_trans. 2: eauto. all: eauto.
          eapply rir_grows_change_vvs with (grd:=const_false); eauto.
          repeat constructor.
        - intros; econstructor; eauto. repeat constructor. reflexivity.
        - eapply wt_sact_vvs_grows.
          eapply vvs_grows_trans. 2: eauto using rir_vvs_grows.
          eapply vvs_grows_trans. 2: eauto using rir_vvs_grows.
          eauto using rir_vvs_grows.
          econstructor. setoid_rewrite list_assoc_gss. eauto.
      }
      edestruct merge_reg2var_grows' as (VVSGROWS5 & NIDGROWS5 & WFS5 & EVAL5); eauto.
      eapply wf_state_vvs_grows_incr; eauto. 1-4: inv WFS4; eauto.
      lia. red; lia.
      eapply wt_sact_vvs_grows; eauto.
      assert (rir_grows l2 r1 vvs rir' (SVar (n+2))).
      {
        eapply rir_grows_weaken_guard.
        - eapply rir_grows_trans. 2: eauto. all: eauto.
          eapply rir_grows_change_vvs with (grd:=const_false); eauto.
          repeat constructor.
        - intros; econstructor; eauto. repeat constructor. reflexivity.
        - eapply wt_sact_vvs_grows.
          eapply vvs_grows_trans. 2: eauto.
          eapply vvs_grows_trans. 2: eauto.
          eapply vvs_grows_trans. 2: eauto using rir_vvs_grows.
          eauto using rir_vvs_grows.
          econstructor. rewrite list_assoc_gss. eauto.
      }
      assert (rir_grows l r0 ll3 r0 const_false).
      {
        eapply rir_grows_change_vvs. eauto.
        intros; eauto using vvs_grows_trans.
        repeat constructor.
      }
      assert (rir_grows l r0 vvs rir' guard).
      {
        eapply rir_grows_weaken_guard.
        eapply rir_grows_trans. 2: eauto. eauto. eauto.
        eapply rir_grows_trans. 4: eauto. all: eauto.
        intros.



        assert (interp_sact ll3 guard (Bits 1 [false])).
        {
          eapply interp_sact_vvs_grows_inv. 6: eauto. all: inv WFSl3; eauto.
          eapply vvs_grows_trans; eauto using rir_vvs_grows.
          eapply wt_sact_vvs_grows. 2: eauto.
          eapply vvs_grows_trans; eauto using rir_vvs_grows.
        }
        assert (exists b, interp_sact ll3 (SVar n) (Bits 1 [b])).
        {
          edestruct wt_sact_interp as (vv & IS & WTv).
          4: apply WTRES. 1-3: inv WFS0; eauto.
          eapply wt_val_bool in WTv. destruct WTv; subst.
          exists x; econstructor.
          unfold ll3; rewrite list_assoc_gso by lia.
          unfold ll2; rewrite list_assoc_gso by lia.
          unfold ll1; rewrite list_assoc_gss. eauto.
          eapply vvs_grows_interp_sact. 2: eauto.
          eauto using rir_vvs_grows.
        } destruct H7.
        assert (interp_sact ll3 (SVar (n + 1)) (Bits 1 [false])).
        {
          econstructor.
          unfold ll3; rewrite list_assoc_gso by lia.
          unfold ll2; rewrite list_assoc_gss. eauto.
          econstructor; eauto.
        }
        assert (interp_sact ll3 (SVar (n + 2)) (Bits 1 [false])).
        {
          econstructor.
          unfold ll3; rewrite list_assoc_gss. eauto.
          econstructor; eauto.
          econstructor; eauto. simpl. eauto. simpl. auto.
        }
        eapply vvs_grows_interp_sact with (v1:=ll3). eapply vvs_grows_trans; eauto using rir_vvs_grows.
        econstructor. repeat econstructor; eauto.
        econstructor. eauto. eauto. simpl. reflexivity. simpl. reflexivity.
        eapply wt_sact_vvs_grows. eapply rir_vvs_grows. apply H2.
        eapply wt_sact_vvs_grows. eapply rir_vvs_grows. eauto.
        eapply wt_sact_vvs_grows. eauto.
        eapply wt_sact_vvs_grows. eauto.
        eapply wt_sact_vvs_grows. eauto.
        eapply wt_sact_vvs_grows. eauto using rir_vvs_grows. eauto.
      }
      assert (rir_grows vvs0 rir vvs rir' guard).
      {
        eapply rir_grows_weaken_guard.
        eapply rir_grows_trans. 2: eauto. 1,2: eauto. eauto.
        intros. econstructor; eauto.
        eapply wt_sact_vvs_grows. eauto using rir_vvs_grows.
        eapply wt_sact_vvs_grows. 2: eauto.
        eapply vvs_grows_trans; eauto using rir_vvs_grows.
        eapply vvs_grows_trans; eauto using rir_vvs_grows.
        eapply vvs_grows_trans; eauto using rir_vvs_grows.
        eapply vvs_grows_trans; eauto using rir_vvs_grows.
        eapply vvs_grows_trans; eauto using rir_vvs_grows.
      }
      repeat (refine (conj _ _)); auto.
      + simpl. econstructor.
        * eapply wt_sact_vvs_grows. 2: eauto. eauto using rir_vvs_grows.
        * eapply wt_sact_vvs_grows. 2: eauto. eauto using rir_vvs_grows.
        * eapply wt_sact_vvs_grows. 2: eauto.
          eapply vvs_grows_trans; eauto.
      + econstructor.
        * eapply wt_sact_vvs_grows. 2: eauto. eauto  using rir_vvs_grows.
        * econstructor.
          econstructor. eapply wt_sact_vvs_grows. 2: eauto. eauto  using rir_vvs_grows.
          eapply wt_sact_vvs_grows. 2: eauto. eauto using rir_vvs_grows.
          constructor.
          econstructor. econstructor.
          eapply wt_sact_vvs_grows. 2: eauto. eauto using rir_vvs_grows. constructor.
          eapply wt_sact_vvs_grows. 2: eauto.
          eapply vvs_grows_trans; eauto. constructor. constructor.
        * constructor.
      + lia.
      + exploit merge_vms_preserve_same_env. 2: eauto.
        eapply same_env_trans. apply same_env_sym; eauto. auto. intro SAMEENV3.
        eapply same_env_trans; eauto.
        eapply same_env_trans. 2: eauto. eauto.

      + intros.
        unfold opt_bind in INTERP.
        destr_in INTERP. 2: inv INTERP.
        repeat (destr_in INTERP; [idtac]).
        destr_in INTERP. 2-4: now inv INTERP.
        destr_in INTERP. now inv INTERP.
        destr_in INTERP. 2: now inv INTERP.
        destr_in INTERP. now inv INTERP.
        destr_in INTERP. 2: try now inv INTERP. subst.
        dihyp INTERPHYP.
        destr_in INTERP.
        * dihyp INTERPHYP0.
          eapply match_Gamma_env_vvs_grows. eauto.
          eauto using vvs_grows_trans.
          eapply match_logs_r2v_vvs_grows; eauto.
          eauto using vvs_grows_trans.
          {
            econstructor. rewrite list_assoc_gso by lia. rewrite list_assoc_gss. eauto.
            econstructor.
            eapply vvs_grows_interp_sact. 2: eauto. eauto using vvs_grows_trans, rir_vvs_grows.
            econstructor. repeat rewrite list_assoc_gso by lia. rewrite list_assoc_gss. eauto.
            eapply vvs_grows_interp_sact. 2: eauto. eauto using vvs_grows_trans, rir_vvs_grows.
            reflexivity.
          }
          repeat refine (conj _ _); eauto.
          -- econstructor.
             eapply vvs_grows_interp_sact. 2: eauto. eauto using rir_vvs_grows.
             simpl.
             eapply vvs_grows_interp_sact. 2: eauto. eauto using rir_vvs_grows.
          -- econstructor.
             eapply vvs_grows_interp_sact. 2: eauto. eauto using rir_vvs_grows.
             instantiate (1:=Bits 1 [false]).
             econstructor. econstructor.
             eapply vvs_grows_interp_sact. 2: eauto. eauto using rir_vvs_grows.
             eapply vvs_grows_interp_sact. 2: eauto. eauto using rir_vvs_grows. simpl. reflexivity.
             instantiate (1:=Bits 1 [false]).
             edestruct wt_sact_interp with (a:=s1) as (x & IV & WTv). 4: eauto.
             1-3: inv WFS2; eauto.
             econstructor. econstructor.
             eapply vvs_grows_interp_sact. 2: eauto. eauto using rir_vvs_grows. reflexivity.
             eapply vvs_grows_interp_sact. 2: eauto. eauto using vvs_grows_trans.
             eapply wt_val_bool in WTv. destruct WTv. subst. simpl. reflexivity.
             reflexivity.
             reflexivity.
          --
            assert (match_Gamma_env Gamma' env' l9).
            {
              eapply mge_merge_branches.
              4: {
                econstructor. eapply VVSGROWS4. eapply rir_vvs_grows; eauto.
                eapply rir_vvs_grows; eauto.
                rewrite list_assoc_gso.
                rewrite list_assoc_gso.
                rewrite list_assoc_gss. eauto. lia. lia.
                eapply vvs_grows_interp_sact. 2: eauto.
                eapply vvs_grows_trans. 2: eauto.
                eapply vvs_grows_trans. apply VG1.
                eapply vvs_grows_trans; eauto.
                eapply vvs_grows_trans; eauto.
                eapply vvs_grows_trans; eauto using rir_vvs_grows.
              }
              3: simpl; eauto. 4: eauto.
              eapply same_env_trans.
              apply same_env_sym. eauto. eauto.
              eapply merge_vms_preserve_same_env. 2: eauto.
              eapply same_env_trans.
              apply same_env_sym. eauto. eauto.
              eapply match_Gamma_env_vvs_grows. apply MGE0. eauto using rir_vvs_grows.
            }
            eapply match_Gamma_env_vvs_grows. apply H7. auto.
          -- apply EVAL5.
             intros.
             assert (b0 = true).
             exploit vvs_grows_interp_sact.
             eapply vvs_grows_trans. 2: apply VVSGROWS4.
             eapply vvs_grows_trans. 2: eauto using rir_vvs_grows.
             eauto using rir_vvs_grows.
             2: intro IS; exploit interp_sact_determ.
             2: apply H7. 2: apply IS.
             econstructor. rewrite list_assoc_gso by lia.
             rewrite list_assoc_gso by lia.
             rewrite list_assoc_gss. eauto.
             eapply vvs_grows_interp_sact. 2: eauto.
             eauto using vvs_grows_trans. intro A; inv A. auto.
             subst.

             eapply match_logs_r2v_rir_grows. eauto. eauto.
             eapply vvs_grows_interp_sact with (v1:=ll3).
             eauto using vvs_grows_trans, rir_vvs_grows.
             unfold ll3,ll2,ll1.
             econstructor.
             rewrite list_assoc_gss. eauto.
             edestruct wt_sact_interp as (vg & ISG & WTGv).
             4: apply WTGUARD. 1-3: inv WFS; eauto.
             apply wt_val_bool in WTGv. destruct WTGv as (? & WTGv). subst.
             econstructor. eapply vvs_grows_interp_sact. 2: eauto.
             eauto using vvs_grows_trans, rir_vvs_grows.
             econstructor.
             eapply interp_sact_vvs_grows_inv. 6: now eauto.
             apply WFSl3.
             apply WFSl3.
             eauto using vvs_grows_trans, rir_vvs_grows.
             apply WFSl3.
             econstructor. rewrite list_assoc_gso by lia.
             rewrite list_assoc_gso by lia.
             rewrite list_assoc_gss. eauto.
             simpl; eauto.
             simpl; eauto. rewrite andb_false_r. auto.

        * dihyp INTERPHYP1.
          -- eapply match_Gamma_env_vvs_grows. eauto.
             eapply vvs_grows_trans. apply VG1.
             eapply vvs_grows_trans; eauto.
             eapply vvs_grows_trans; eauto.
             eauto using vvs_grows_trans, rir_vvs_grows.
          -- eapply match_logs_r2v_rir_grows; eauto.
             eapply rir_grows_trans. 4: eauto. 2: eauto. eauto. eauto.
             eapply vvs_grows_interp_sact. eauto using rir_vvs_grows.
             edestruct wt_sact_interp as (vg & ISG & WTGv).
             4: apply WTGUARD. 1-3: inv WFS; eauto.
             apply wt_val_bool in WTGv. destruct WTGv as (? & WTGv). subst.
             econstructor. constructor. econstructor.
             rewrite list_assoc_gso by lia.
             rewrite list_assoc_gss. eauto.
             econstructor.
             eapply vvs_grows_interp_sact. 2: apply ISG.
             eauto using vvs_grows_trans, rir_vvs_grows.
             econstructor.
             repeat rewrite list_assoc_gso by lia.
             rewrite list_assoc_gss. eauto.
             eapply vvs_grows_interp_sact. 2: apply INTERPVAL.
             eauto using vvs_grows_trans, rir_vvs_grows.
             simpl; eauto. simpl; eauto. rewrite andb_false_r; auto.
          -- eapply vvs_grows_interp_sact.  eauto using rir_vvs_grows.
             econstructor. repeat rewrite list_assoc_gso by lia. rewrite list_assoc_gss. eauto.
             econstructor.
             eapply vvs_grows_interp_sact. 2: eauto. eauto using vvs_grows_trans, rir_vvs_grows.
             econstructor.
             econstructor. repeat rewrite list_assoc_gso by lia. rewrite list_assoc_gss. eauto.
             eapply vvs_grows_interp_sact. 2: eauto. eauto using vvs_grows_trans, rir_vvs_grows.
             reflexivity. reflexivity.
          -- repeat refine (conj _ _); eauto.
             ++ econstructor.
                eapply vvs_grows_interp_sact. 2: eauto. eauto using vvs_grows_trans, rir_vvs_grows.
                simpl.
                eapply vvs_grows_interp_sact. 2: eauto. eauto using vvs_grows_trans, rir_vvs_grows.
             ++ edestruct wt_sact_interp with (a:=s0) as (x & IV & WTv). 4: eauto.
                1-3: inv WFS1; eauto.
                destruct (wt_val_bool _ WTv); subst.
                econstructor.
                eapply vvs_grows_interp_sact. 2: eauto. eauto using rir_vvs_grows.
                (* instantiate (1:=Bits 1 [false]). *)
                econstructor. econstructor.
                eapply vvs_grows_interp_sact. 2: eauto. eauto using rir_vvs_grows.
                eapply vvs_grows_interp_sact. 2: eauto. eauto using rir_vvs_grows. simpl. reflexivity.
                econstructor. econstructor.
                eapply vvs_grows_interp_sact. 2: eauto. eauto using rir_vvs_grows. reflexivity.
                eapply vvs_grows_interp_sact. 2: eauto. eauto using vvs_grows_trans.
                simpl. eauto. simpl; eauto. reflexivity.
             ++ assert (match_Gamma_env Gamma' env' l9).
                {
                  eapply mge_merge_branches.
                  4: {
                    econstructor. eapply VVSGROWS4. eapply rir_vvs_grows; eauto.
                    eapply rir_vvs_grows; eauto.
                    rewrite list_assoc_gso.
                    rewrite list_assoc_gso.
                    rewrite list_assoc_gss. eauto. lia. lia.
                    eapply vvs_grows_interp_sact. 2: eauto.
                    eapply vvs_grows_trans. 2: eauto.
                    eapply vvs_grows_trans. apply VG1.
                    eapply vvs_grows_trans; eauto.
                    eapply vvs_grows_trans; eauto.
                    eapply vvs_grows_trans; eauto using rir_vvs_grows.
                  }
                  3: simpl; eauto. 4: eauto.
                  eapply same_env_trans.
                  apply same_env_sym. eauto. eauto.
                  eapply merge_vms_preserve_same_env. 2: eauto.
                  eapply same_env_trans.
                  apply same_env_sym. eauto. eauto.
                  eapply match_Gamma_env_vvs_grows. apply MGE0. eauto using rir_vvs_grows.
                }
                eapply match_Gamma_env_vvs_grows. apply H7. auto.
             ++ apply EVAL5.
                intros.
                assert (b0 = false).
                exploit vvs_grows_interp_sact.
                eapply vvs_grows_trans. 2: apply VVSGROWS4.
                eapply vvs_grows_trans. 2: eauto using rir_vvs_grows.
                eauto using rir_vvs_grows.
                2: intro IS; exploit interp_sact_determ.
                2: apply H7. 2: apply IS.
                econstructor. rewrite list_assoc_gso by lia.
                rewrite list_assoc_gso by lia.
                rewrite list_assoc_gss. eauto.
                eapply vvs_grows_interp_sact. 2: eauto.
                eauto using vvs_grows_trans. intro A; inv A. auto.
                subst.
                eapply match_logs_r2v_vvs_grows; eauto.
    - repeat (refine (conj _ _)); eauto.
      + exploit wt_sact_interp; eauto. 1-3: inv WFS; eauto.
        intros (v & IS & WTg). destruct (wt_val_bool _ WTg). subst.
        eapply wf_state_change_rir; eauto. eapply rir_grows_add_read0; eauto.
        eapply wf_rir_add_read0; eauto. inv WFS; eauto.
      + exploit wt_sact_interp; eauto. 1-3: inv WFS; eauto.
        intros (v & IS & WTg). destruct (wt_val_bool _ WTg). subst.
        eapply rir_grows_add_read0; eauto.
      + simpl.
        edestruct wfs_r2v_vvs as (? & GET & ? & GET2); eauto.
        setoid_rewrite Heqo in GET. inv GET. eauto.
        econstructor; eauto.
      + constructor. constructor. reflexivity.
      + apply same_env_refl.
      + inv WT. auto.
      + intros.
        destr_in INTERP; inv INTERP.
        inv WT.
        repeat (refine (conj _ _)); eauto.
        * exploit mlr_read. eauto. eauto. eauto. simpl. auto.
        * constructor.
        * eapply match_logs_r2v_add_read0. eauto. eauto.
    - repeat (refine (conj _ _)); eauto.
      + exploit wt_sact_interp; eauto. 1-3: inv WFS; eauto.
        intros (v & IS & WTg). apply wt_val_bool in WTg. inv WTg.
        eapply wf_state_change_rir; eauto. eapply rir_grows_add_read1; eauto.
        eapply wf_rir_add_read1; inv WFS; eauto.
      + exploit wt_sact_interp; eauto. 1-3: inv WFS; eauto.
        intros (v & IS & WTg). apply wt_val_bool in WTg. inv WTg.
        eapply rir_grows_add_read1; eauto.
      + simpl.
        edestruct wfs_r2v_vvs as (? & GET & ? & GET2); eauto.
        setoid_rewrite Heqo in GET. inv GET. eauto.
        econstructor; eauto.
      + repeat constructor.
      + apply same_env_refl.
      + inv WT. auto.
      + intros.
        destr_in INTERP; inv INTERP.
        inv WT.
        repeat (refine (conj _ _)); eauto.
        * exploit mlr_read. eauto. eauto. eauto. simpl. auto.
        * constructor.
        * eapply match_logs_r2v_add_read1; eauto.

    - edestruct wfs_r2v_vvs as (? & GET & ? & GET2); eauto.
      setoid_rewrite Heqo in GET. inv GET.
    - edestruct wfs_r2v_vvs as (? & GET & ? & GET2); eauto.
      setoid_rewrite Heqo in GET. inv GET.
    - inv WT.
      dhyp H. subst.

      assert (rir_grows l r0 vvs rir' guard /\ wf_state tsig env' reg2var' vvs rir' nid' /\ wt_sact vvs s0 (bits_t 1)).
      {
        destr_in Heqp7; inv Heqp7.
        - eapply rir_grows_add_write0; eauto.
          eapply wt_sact_vvs_grows. 2: eauto. eauto using rir_vvs_grows.
        - eapply rir_grows_add_write1; eauto.
          eapply wt_sact_vvs_grows. 2: eauto. eauto using rir_vvs_grows.
      }
      destruct H0 as (RG1 & WFS1 & WTfail).

      assert (n <= nid').
      {
        destr_in Heqp7; inv Heqp7. lia. lia.
      }

      repeat (refine (conj _ _)); eauto.
      + eapply rir_grows_weaken_guard.
        eapply rir_grows_trans. 2: eauto. all: eauto.
        intros.
        econstructor; eauto.
        eapply wt_sact_vvs_grows. 2: eauto.
        eauto using vvs_grows_trans, rir_vvs_grows.
      + simpl. constructor. constructor. reflexivity.
      + econstructor; eauto. 2: constructor.
        eapply wt_sact_vvs_grows. 2: eauto. eauto using rir_vvs_grows.
      + lia.
      + intros.
        unfold opt_bind in INTERP.
        repeat destr_in INTERP; inv INTERP.
        dihyp INTERPHYP.
        repeat (refine (conj _ _)); eauto.
        * repeat constructor.
        * econstructor.
          eapply vvs_grows_interp_sact. 2: eauto. eauto using rir_vvs_grows.
          destr_in Heqp7. inv Heqp7.
          eapply vvs_grows_interp_sact. eauto using rir_vvs_grows.
          eapply add_write0_fail; eauto.
          eapply vvs_grows_interp_sact. 2: eauto. eauto using rir_vvs_grows.
          inv Heqp7.
          eapply add_write1_fail. eauto. 2: eauto. eauto. eauto.
          eapply vvs_grows_interp_sact. 2: eauto. eauto using rir_vvs_grows.
          reflexivity.
        * eapply match_Gamma_env_vvs_grows; eauto. eauto using rir_vvs_grows.
        * destr_in Heqp7; inv Heqp7.
          eapply match_logs_r2v_add_write0; eauto.
          eapply match_logs_r2v_add_write1. 3: eauto. all: eauto.
    - assert (exists t1,
                 wt_daction (R:=R) (Sigma:=Sigma) pos_t string string tsig arg1 t1 /\
                   wt_unop ufn1 t1 tret
             ).
      {
        inv WT; eexists; split; simpl; eauto; try (econstructor; eauto).
      }
      destruct H0 as (t1 & WTa & EQ).
      dhyp H. subst.
      repeat (refine (conj _ _)); eauto.
      + simpl. intros. econstructor. eauto.
        exploit wt_unop_type_unop_ret; eauto. congruence.
      + eapply wt_unop_type_unop_ret; eauto.
      + intros.
        unfold opt_bind in INTERP.
        repeat destr_in INTERP; inv INTERP.
        dihyp INTERPHYP.
        repeat (refine (conj _ _)); eauto.
        * simpl. econstructor. eauto. eauto.

    - assert (exists t1 t2,
                 wt_daction (R:=R) (Sigma:=Sigma) pos_t string string tsig arg1 t1 /\
                   wt_daction (R:=R) (Sigma:=Sigma) pos_t string string tsig arg2 t2 /\
                   wt_binop ufn2 t1 t2 tret
             ).
      {
        inv WT; do 2 eexists; repeat split; simpl; eauto; try (econstructor; eauto).
      }
      destruct H1 as (tt1 & tt2 & WTa & WTb & EQ).
      dhyp H. subst.
      dhyp H0.
      + eapply wt_sact_vvs_grows; eauto. eapply rir_vvs_grows; eauto.
      + repeat (refine (conj _ _)); eauto.
        * eapply rir_grows_weaken_guard. eapply rir_grows_trans. 2,4:eauto. all: eauto.
          intros; econstructor; eauto.
          eapply wt_sact_vvs_grows; eauto.
          eauto using vvs_grows_trans, rir_vvs_grows.
        * simpl. subst.
          econstructor. eapply wt_sact_vvs_grows; eauto using rir_vvs_grows.
          eauto.
          exploit wt_binop_type_binop_ret; eauto. congruence.
        * econstructor.
          eapply wt_sact_vvs_grows. 2: eauto. eauto using rir_vvs_grows. eauto. constructor.
        * lia.
        * eapply same_env_trans; eauto.
        * subst. eapply wt_binop_type_binop_ret; eauto.
        * intros.
          unfold opt_bind in INTERP.
          repeat destr_in INTERP; inv INTERP.
          dihyp INTERPHYP.
          dihyp INTERPHYP0.
          eapply vvs_grows_interp_sact; eauto using rir_vvs_grows.
          repeat (refine (conj _ _)); eauto.
          -- simpl. econstructor. eapply vvs_grows_interp_sact. 2: eauto.
             eauto using vvs_grows_trans, rir_vvs_grows.
             eauto. auto.
          -- simpl. econstructor. eapply vvs_grows_interp_sact. 2: eauto.
             eauto using vvs_grows_trans, rir_vvs_grows.
             eauto. auto.

    - inv WT. dhyp H. subst.
      assert (rir_grows l rir'
                        (list_assoc_set l n (retSig (Sigma ufn), SExternalCall ufn (reduce (arg1Sig (Sigma ufn)) o))) rir' guard).
      {
        eapply rir_grows_change_vvs. eauto.
        intros.
        red in H0.
        rewrite ! list_assoc_gso by lia. auto.
        eapply wt_sact_vvs_grows; eauto.
        eapply vvs_grows_trans. eauto using rir_vvs_grows. eapply vvs_grows_set.
        inv WFS0; eauto. lia.
      }
      edestruct wf_state_vvs_set with (k:= n) (m := S n). apply WFS0.
      apply wt_sact_extcall. apply WTRES. lia.
      intros. inv H1. eapply wt_sact_below in H6; eauto.  lia.
      repeat (refine (conj _ _)); eauto.
      * eapply rir_grows_weaken_guard. eapply rir_grows_trans. 2,4: eauto. all: eauto.
        intros; econstructor; eauto.
        eapply wt_sact_vvs_grows. 2: eauto. eauto using vvs_grows_trans, rir_vvs_grows.
      * simpl. econstructor. rewrite list_assoc_gss. eauto.
      * eapply wt_sact_vvs_grows. 2: eauto. auto.
      * intros.
        unfold opt_bind in INTERP.
        repeat destr_in INTERP; inv INTERP.
        dihyp INTERPHYP.
        repeat (refine (conj _ _)); eauto.
        -- simpl. econstructor. rewrite list_assoc_gss. eauto.
           econstructor.
           eapply vvs_grows_interp_sact. 2: eauto. auto.
        -- simpl. eapply vvs_grows_interp_sact. 2: eauto. auto.
        -- eapply match_Gamma_env_vvs_grows; eauto.
        -- eapply match_logs_r2v_vvs_grows; eauto.
 
    - inv WT.
      eapply gria_list_grows2 with
        (I:= fun env reg2var vvs nid rir guard =>
               wf_state tsig env reg2var vvs rir nid
               /\ wt_sact vvs guard (bits_t 1)
        )
        (P:= fun env reg2var vvs nid rir env' rev2var' vvs' nid' rir' grd =>
               same_env env env'
               /\ rir_grows vvs rir vvs' rir' grd
         ) in Heqp.
      7: {
        eapply Forall_impl.
        2: apply H0. simpl; intros. destruct H5 as (WFS2 & WTG).
        dhyp H1. subst. intuition eauto.
        - eapply wt_sact_vvs_grows; eauto using rir_vvs_grows.
      }
      destruct Heqp as ((SAMEENV1 & RIRGROWS1) & ((WFS1 & WTGUARD1) & (NAMES & LENNAMES & WTS1 & NID1 & INTERP1))); eauto.
      2: {
        intros. split; eauto using same_env_refl, rir_grows_refl.
      }
      2: {
        simpl; intros; eauto.
        decompose [and] H1; clear H1.
        decompose [and] H2; clear H2.
        decompose [and] H3; clear H3.
        decompose [and] H5; clear H5.
        decompose [and] H7; clear H7.
        split.
        eapply same_env_trans; eauto.
        eapply rir_grows_weaken_guard.
        eapply rir_grows_trans. 2,4: eauto. all: eauto.
        intros; econstructor; eauto.
        eapply wt_sact_vvs_grows; eauto.
        eauto using vvs_grows_trans, rir_vvs_grows.
      }
      2: {
        intuition.
        - apply same_env_refl.
        - eapply rir_grows_weaken_guard.
          eapply rir_grows_set; eauto. unfold valid_name; lia.
          constructor.
          eapply wt_sact_vvs_grows; eauto. eapply vvs_grows_set; eauto.
          apply H3.
        - eapply wf_state_vvs_set; eauto.
          eapply wt_sact_below; eauto.
        - eapply wt_sact_vvs_grows; eauto. eapply vvs_grows_set; eauto.
          apply H3.
      }
      2:{
        simpl; intros. intuition; eauto using rir_vvs_grows.
      }
      2: {
        intros. destruct H1. inv H1. eauto.
      }
      2: now eauto.
      2: now eauto.
      2: {
        repeat constructor.
      }
      2: {
        split; auto.
      }
      2: constructor.

      clear H0.
      simpl in LENNAMES.

      assert ( env_vvs (combine (fst (split (rev (int_argspec ufn)))) (map fst l1)) l
                       (rev (int_argspec ufn))).
      {
        rewrite app_nil_r in NAMES.
        revert NAMES.
        rewrite fst_split_map.
        rewrite <- ! map_rev.
        generalize l1.
        generalize (rev (int_argspec ufn)).
        induction l2; simpl; intros; eauto. constructor.
        inv NAMES. simpl.
        repeat destr_in H3. destruct H3 as (? & ? & GET). subst. simpl.
        constructor; eauto.
        destr. simpl. split; eauto.
        eapply IHl2. eauto.
      }

      dhyp H.
      inv WFS1; split; eauto. subst.
      repeat refine(conj _ _); eauto.
      + inv WFS1; inv WFS0; split; eauto.
        eapply env_vvs_vvs_grows; eauto. eapply rir_vvs_grows; eauto.
      + eapply rir_grows_weaken_guard.
        eapply rir_grows_trans. 2,4: now eauto. all: eauto.
        intros; econstructor; eauto.
        eapply wt_sact_vvs_grows; eauto.
        eauto using vvs_grows_trans, rir_vvs_grows.
      + econstructor. eauto.
        eapply wt_sact_vvs_grows. 2: eauto.
        eauto using vvs_grows_trans, rir_vvs_grows.
        constructor.
      + lia.
      + intros.
        unfold opt_bind in INTERP.
        repeat destr_in INTERP; inv INTERP.
        edestruct INTERP1 as (EQv & FAIL & MGE' & MLR' & WTE'); eauto.
        now constructor.
        dihyp INTERPHYP.
        * revert EQv NAMES.
          rewrite app_nil_r. rewrite <- map_rev.
          generalize (rev (int_argspec ufn)).
          generalize l1 l4.
          intros l2 l7 l8 F; revert F l8.

          induction 1; simpl; intros; eauto.
          destruct l8; simpl in *. constructor. inv NAMES.
          destruct l8; simpl in *. inv NAMES. inv NAMES.
          destr.  destr_in H7.  destruct H7 as (? & ? & ?). subst.
          constructor. eauto. simpl in H3.
          inv H1. rewrite H3 in H5; inv H5.
          eapply interp_sact_wt. 5: apply H7. apply WFS1. apply WFS1. apply WFS1.
          eapply wfs_wt_vvs. 2: eauto. eauto.
        * revert EQv NAMES.
          rewrite app_nil_r. rewrite <- map_rev.
          rewrite fst_split_map.
          generalize (rev (int_argspec ufn)).
          generalize l1 l4.
          intros l2 l7 l8 F; revert F l8.
          induction 1; simpl; intros; eauto.
          destruct l8; simpl in *. constructor. inv NAMES.
          destruct l8; simpl in *. inv NAMES. inv NAMES.
          destr.  destr_in H7.  destruct H7 as (? & ? & ?). subst.
          constructor. eauto. apply IHF. eauto.
        * eapply vvs_grows_interp_sact. 2: eauto. eauto using vvs_grows_trans, rir_vvs_grows.
        * repeat refine (conj _ _); eauto.
          -- econstructor. eauto. eapply vvs_grows_interp_sact. 2: eauto.
             eauto using vvs_grows_trans, rir_vvs_grows. reflexivity.
          -- eapply match_Gamma_env_vvs_grows. eauto.
             eauto using vvs_grows_trans, rir_vvs_grows.
    - inv WT.
      dhyp H.
  Qed.

  Definition init_reg r2v vvs sched_log (nid: nat) (idx: reg_t)
    : list (reg_t * Port * nat) * list (nat * (type * sact)) * nat :=
    let r2v := list_assoc_set r2v (idx,P0) nid in
    let r2v := list_assoc_set r2v (idx,P1) (nid+1) in
    let vvs := list_assoc_set vvs nid (R idx, SConst (do_read sched_log log_empty idx P0)) in
    let vvs := list_assoc_set vvs (nid+1) (R idx, SConst (do_read sched_log log_empty idx P1)) in
    (r2v, vvs, nid + 2).

  Definition init_regs r2v vvs sched_log (nid: nat) (l: list reg_t)
    : list (reg_t * Port * nat) * list (nat * (type * sact)) * nat :=
    fold_left (fun '(r2v,vvs,nid) idx => init_reg r2v vvs sched_log nid idx)
              l (r2v,vvs,nid).

  Context {finreg_t: FiniteType reg_t}.

  Definition init_r2v nid sched_log :=
    init_regs [] [] sched_log nid (finite_elements).

  Lemma init_reg_wt_vvs:
    forall r2v vvs sched_log nid idx r2v' vvs' nid' ,
      init_reg r2v vvs sched_log nid idx = (r2v', vvs', nid') ->
      wt_log R REnv sched_log ->
      wt_renv R REnv r ->
      wt_vvs vvs ->
      (forall x y, list_assoc r2v x = Some y -> list_assoc vvs y = Some (R (fst x), SConst (do_read sched_log log_empty (fst x) (snd x)))) ->
      vvs_range vvs nid ->
      vvs_smaller_variables vvs ->
      wt_vvs vvs' 
      /\ (forall x y, list_assoc r2v' x = Some y -> list_assoc vvs' y = Some (R (fst x), SConst (do_read sched_log log_empty (fst x) (snd x))))
      /\ vvs_range vvs' nid'
      /\ vvs_smaller_variables vvs' /\ nid <= nid' /\
        forall i p, In (i,p) (map fst r2v) \/ i = idx ->
                    In (i,p) (map fst r2v').
  Proof.
    intros r2v vvs sched_log nid idx r2v' vvs' nid' IR WTL WTR WT R2V VR VSV.
    unfold init_reg in IR. inv IR.
    repeat refine (conj _ _).
    - eapply wt_vvs_set; eauto.
      eapply wt_vvs_set; eauto.
      constructor. eapply WTR.
      eapply vvs_range_list_assoc_set.
      eapply vvs_range_incr. 2: eauto. lia. red; lia.
      destr.
      econstructor.
      unfold latest_write0 in Heqo.
      exploit @log_find_wt; eauto.
      unfold log_latest_write0_fn. intros x y H; repeat destr_in H. easy. reflexivity. easy.
      red; intros; eapply WTL.
      unfold log_app in H. rewrite getenv_map2 in H.
      rewrite in_app_iff in H. destruct H; eauto.
      unfold log_empty in H.
      rewrite getenv_create in H. easy. auto.
      intros (x & LLW & WTv). unfold log_latest_write0_fn in LLW. repeat destr_in LLW; inv LLW.
      simpl in WTv. auto.
      econstructor. apply WTR.
    - intros.
      rewrite ! list_assoc_spec in H.
      rewrite ! list_assoc_spec.
      destr_in H. inv H. rewrite eq_dec_refl. eauto.
      destr_in H. inv H. rewrite eq_dec_refl. destr. lia. eauto.
      destr; eauto. subst.
      exploit R2V; eauto. intro H0.
      eapply VR in H0. red in H0; lia.
      destr; eauto. subst.
      exploit R2V; eauto. intro H0.
      eapply VR in H0. red in H0; lia.
    - eapply vvs_range_list_assoc_set.
      eapply vvs_range_list_assoc_set.
      eapply vvs_range_incr. 2: eauto. lia.
      red; lia. red; lia.
    - eapply vvs_smaller_variables_set; eauto.
      eapply vvs_smaller_variables_set; eauto.
      inversion 1.
      inversion 1.
    - lia.
    - intros.
      destruct H.
      apply list_assoc_set_key_stays_in.
      apply list_assoc_set_key_stays_in.
      eauto.
      subst. destruct p.
      apply list_assoc_set_key_stays_in.
      apply list_assoc_set_key_in.
      apply list_assoc_set_key_in.
  Qed.

  Lemma init_regs_wt_vvs:
    forall l r2v vvs sched_log nid r2v' vvs' nid' ,
      init_regs r2v vvs sched_log nid l = (r2v', vvs', nid') ->
      wt_log R REnv sched_log ->
      wt_renv R REnv r ->
      wt_vvs vvs ->
      (forall x y, list_assoc r2v x = Some y -> list_assoc vvs y = Some (R (fst x), SConst (do_read sched_log log_empty (fst x) (snd x)))) ->
      vvs_range vvs nid ->
      vvs_smaller_variables vvs ->
      wt_vvs vvs' 
      /\ (forall x y, list_assoc r2v' x = Some y -> list_assoc vvs' y = Some (R (fst x), SConst (do_read sched_log log_empty (fst x) (snd x)))) 
      /\ vvs_range vvs' nid'
      /\ vvs_smaller_variables vvs' /\ nid <= nid' /\
        forall i p, In (i,p) (map fst r2v) \/ In i l ->
                    In (i,p) (map fst r2v').
  Proof.
    unfold init_regs.
    induction l; simpl; intros; eauto.
    - inv H. repeat refine (conj _ _); eauto. intuition.
    - destruct (init_reg r2v vvs sched_log nid a) eqn:?.
      destruct p.
      edestruct init_reg_wt_vvs as (WTvvs' & R2V' & VR' & VSV' & LE & INCL); eauto.
      eapply IHl in H; eauto.
      intuition.
  Qed.

  Lemma wfs_init_r2v:
    forall n0 r2v vvs n sched_log,
      init_r2v n0 sched_log = (r2v,vvs,n) ->
      wt_log R REnv sched_log ->
      wt_renv R REnv r ->
      let rir := {|
                  rir_read0s := [];
                  rir_read1s := [];
                  rir_write0s := [];
                  rir_write1s := [];
                  rir_vars := [];
                  rir_failure_cond := const_false
                |} in
      wf_state [] [] r2v vvs rir
               n /\ n0 <= n /\ match_logs_r2v r2v vvs rir sched_log log_empty.
  Proof.
    intros n0 r2v vvs n sched_log IR WTL WTR. simpl.
    unfold init_r2v in IR.
    edestruct init_regs_wt_vvs as (WTvvs' & R2V' & VR' & VSV' & LE & INCL); eauto.
    red; easy. simpl; easy. red; easy. red; easy.
    split. split; eauto. constructor.
    red; intros.
    simpl in INCL.
    generalize (finite_surjective (fst x)). intro NTH.
    apply nth_error_In in NTH. destruct x. simpl in *.
    edestruct @in_keys_list_assoc_ex. eapply INCL. right; eauto. rewrite H.
    eexists; split. eauto. exploit R2V'; eauto.
    split; simpl; try easy.
    repeat constructor.
    split. lia.
    split; simpl; try congruence.
    intros.
    econstructor. eapply R2V'. eauto. econstructor.
  Qed.

  Definition get_rule_information (ua: uact) (nid: nat) r2v vvs
    : rule_information_raw * list (reg_t * Port * nat) * nat :=
    let '(vret, env, r2v, vvs, failure, rir, nid', t) :=
      get_rule_information_aux
        ua [] [] r2v vvs const_true
        {| rir_read0s := [];
          rir_read1s := [];
          rir_write0s := [];
          rir_write1s := [];
          rir_vars := [];
          rir_failure_cond := const_false |}
        nid
    in (
      (rir <| rir_failure_cond := failure |> <| rir_vars := vvs|>),
      r2v,
      nid').

  Lemma get_rule_information_ok:
    forall (ua: uact)
           (nid: nat)
           rir' nid' sched_log r2v vvs r2v'
           (GRI: get_rule_information ua nid r2v vvs = (rir', r2v', nid'))
           tret
           (WT: BitsToLists.wt_daction pos_t string string (R:=R) (Sigma:=Sigma) [] ua tret)
           (WTL: wt_log R REnv sched_log)
           (WTR: wt_renv R REnv r),
      let rir := {| rir_read0s := [];
                   rir_read1s := [];
                   rir_write0s := [];
                   rir_write1s := [];
                   rir_vars := [];
                   rir_failure_cond := const_false |} in
      forall
        (WFS: wf_state [] [] r2v vvs rir nid)
        (MLR: match_logs_r2v r2v vvs rir sched_log log_empty),
        wf_state [] [] r2v' (rir_vars rir') rir' nid'
        /\ rir_grows vvs rir (rir_vars rir') rir' const_true
        /\ nid <= nid'
        /\ forall action_log' vret Gamma'
                  (INTERP: interp_daction r sigma [] sched_log log_empty ua = Some (action_log', vret, Gamma')),
          interp_sact (rir_vars rir') (rir_failure_cond rir') (Bits 1 [false])
          /\ wt_env _ [] Gamma'
          /\ match_logs_r2v r2v' (rir_vars rir') rir' sched_log action_log'.
  Proof.
    intros.
    unfold get_rule_information in GRI.
    repeat destr_in GRI. inv GRI.
    (* exploit wfs_init_r2v; eauto. intros (WFS & NID & MLR). *)
    dhyp get_rule_information_aux_env_grows; eauto.
    repeat constructor.
    subst.
    repeat refine (conj _ _); eauto.
    - inv SAMEENV. simpl. inv WFS0. split; simpl; eauto.
      inv wfs_rir0; split; simpl; eauto.
    - simpl.
      inv RIRGROWS. split; eauto.
    - intros.
      edestruct INTERPHYP as (RES & FAIL & MGE & MLR' & WE); eauto.
      constructor. constructor.
      repeat constructor. simpl.
      repeat refine (conj _ _); eauto.
      simpl. inv MLR'; split; simpl; eauto.
  Qed.

  (* * Scheduling conflicts detection *)
  (* It is here that we take into account how a rule might cancel any later
     rule. *)
  (* ** Conflicts between two rules *)
  (* rir_failure_cond rir is used in detect_conflicts only so as to keep things
     nicely factored. *)
  Definition detect_conflicts_step
             (acc: sact) (rir: rule_information_raw) (cond: sact) (reg: reg_t)
             (reg_failure_detection:
               rule_information_raw -> sact -> reg_t -> sact)
    : sact :=
    uor acc (reg_failure_detection rir cond reg).

  (* The following functions are meant to be passed as arguments to
     detect_conflicts_step. *)
  Definition detect_conflicts_read0s_reg
             (rir: rule_information_raw) (cond: sact) (reg: reg_t)
    : sact :=
    let prev_wr0 := option_map fst (list_assoc (rir_write0s rir) reg) in
    let prev_wr1 := option_map fst (list_assoc (rir_write1s rir) reg) in
    merge_failures_list cond (list_options_to_list [prev_wr0; prev_wr1]).
  Definition detect_conflicts_write0s_reg
             (rir: rule_information_raw) (cond: sact) (reg: reg_t)
    : sact :=
    let prev_wr0 := option_map fst (list_assoc (rir_write0s rir) reg) in
    let prev_rd1 := list_assoc (rir_read1s rir) reg in
    let prev_wr1 := option_map fst (list_assoc (rir_write1s rir) reg) in
    merge_failures_list
      cond (list_options_to_list [prev_wr0; prev_wr1; prev_rd1]).
  Definition detect_conflicts_read1s_reg
             (rir: rule_information_raw) (cond: sact) (reg: reg_t)
    : sact :=
    let prev_wr1 := option_map fst (list_assoc (rir_write1s rir) reg) in
    merge_failures_list cond (list_options_to_list [prev_wr1]).
  Definition detect_conflicts_write1s_reg
             (rir: rule_information_raw) (cond: sact) (reg: reg_t)
    : sact :=
    let prev_wr1 := option_map fst (list_assoc (rir_write1s rir) reg) in
    merge_failures_list cond (list_options_to_list [prev_wr1]).

  (* These functions take a rule's rule_information_raw as well as a subset of
     the logs of a subsequent rule and return a condition that is true in all
     the situations in which the second rule has to fail for e.g. read0s
     conflicts reasons. *)
  Definition detect_conflicts_read0s (rir: rule_information_raw) (rl: cond_log)
    : sact :=
    fold_left
      (fun acc '(reg, cond) =>
         detect_conflicts_step acc rir cond reg detect_conflicts_read0s_reg)
      rl const_false.
  Definition detect_conflicts_write0s
             (rir: rule_information_raw) (wl: write_log_raw)
    : sact :=
    fold_left
      (fun acc '(reg, (ua,lwi)) =>
         detect_conflicts_step acc rir ua reg detect_conflicts_write0s_reg)
      wl const_false.
  Definition detect_conflicts_read1s (rir: rule_information_raw) (rl: cond_log)
    : sact :=
    fold_left
      (fun acc '(reg, cond) =>
         detect_conflicts_step acc rir cond reg detect_conflicts_read1s_reg)
      rl const_false.
  Definition detect_conflicts_write1s
             (rir: rule_information_raw) (wl: write_log_raw)
    : sact :=
    fold_left
      (fun acc '(reg, (ua, lwi)) =>
         detect_conflicts_step acc rir ua reg detect_conflicts_write1s_reg)
      wl const_false.

  Lemma fold_left_induction:
    forall {A B: Type} (f : A -> B -> A) (P: A -> Prop)
           (l: list B) (acc0: A) ,
      P acc0 ->
      (forall x acc, In x l -> P acc -> P (f acc x)) ->
      P (fold_left f l acc0).
  Proof.
    induction l; simpl; intros; eauto.
    eapply IHl. eapply H0. eauto. eauto. intros; eauto.
  Qed.


  (* The order of the arguments matters! If there is a conflict between a1 and
     a2, a1 takes precedence. This function does not take the fact that rule 1
     might fail and therefore not impact rule 2 into account, as this is done
     from detect_conflicts. *)
  Definition detect_conflicts_actions (a1 a2: rule_information_raw)
    : sact :=
    merge_failures
      (merge_failures
         (merge_failures
            (detect_conflicts_read0s a1 (rir_read0s a2))
            (detect_conflicts_write0s a1 (rir_write0s a2)))
         (detect_conflicts_read1s a1 (rir_read1s a2)))
      (detect_conflicts_write1s a1 (rir_write1s a2)).

  (* Returns a failure condition for ri2's conflicts with ri1. Includes ri1's
     initial failure condition. *)
  Definition detect_conflicts (ri1 ri2: rule_information_raw) : sact :=
    merge_failures
      (rir_failure_cond ri2)
      (* If rule 1 fails, then it can't cause rule 2 to fail. *)
      ((* uand (unot (rir_failure_cond ri1)) *)
        (detect_conflicts_actions ri1 ri2)).

  (* ** Conflicts with any prior rule *)
  Definition detect_conflicts_any_prior
             (r: rule_information_raw) (prior_rules: list rule_information_raw)
    : rule_information_raw :=
    fold_left
      (fun r' p => r' <| rir_failure_cond := detect_conflicts p r' |>)
      prior_rules r.

  Definition clean_rule_information (r: rule_information_raw) :
      rule_information_clean :=
    {|
      ric_write0s := map (fun '(a, (_, b)) => (a, b)) (rir_write0s r);
      ric_write1s := map (fun '(a, (_, b)) => (a, b)) (rir_write1s r);
      ric_vars := rir_vars r;
      ric_failure_cond := rir_failure_cond r
    |}.


  Record rule_information_clean_ok (r: rule_information_clean) (ua: sact) :=
    {
      (* ... *)
    }.

  Definition list_assoc_modify {K V: Type} {eqdec: EqDec K}
             (l: (list (K*V)))
             k vdef (f: V -> V) :=
    let newv :=
      match list_assoc l k with
      | None => vdef
      | Some v => f v
      end in
    list_assoc_set l k newv.

  Fixpoint merge_cond_logs (cl1 cl2: cond_log) (cond2: sact) :=
    match cl2 with
    | [] => cl1
    | (idx, c)::cl2 =>
        let c := uand cond2 c in
        merge_cond_logs (list_assoc_modify cl1 idx c (fun c1 => uor c1 c)) cl2 cond2
    end.


  Fixpoint merge_write_logs (wl1 wl2: write_log_raw) (cond2: sact) :=
    match wl2 with
    | [] => wl1
    | (idx, (gcond, wil))::wl2 =>
        let gcond' := uand cond2 gcond in
        let wil' := map (fun wi => {| wcond := uand cond2 (wcond wi); wval := wval wi |}) wil in
        merge_write_logs
          (list_assoc_modify wl1 idx
                             (gcond', wil')
                             (fun '(g1, wil1) => (uor g1 gcond', wil1 ++ wil')))
          wl2 cond2
    end.

  Definition merge_rirs rir rir' conflict_name vvs :=
    {|
      rir_read0s := merge_cond_logs (rir_read0s rir) (rir_read0s rir') (SVar conflict_name);
      rir_read1s := merge_cond_logs (rir_read1s rir) (rir_read1s rir') (SVar conflict_name);
      rir_write0s := merge_write_logs (rir_write0s rir) (rir_write0s rir') (SVar conflict_name);
      rir_write1s := merge_write_logs (rir_write1s rir) (rir_write1s rir') (SVar conflict_name);
      rir_vars := vvs;
      rir_failure_cond := uor (rir_failure_cond rir) (rir_failure_cond rir')
    |}.

  Fixpoint get_rir_scheduler' (rir: rule_information_raw) r2v
          (rules: rule_name_t -> uact) nid
          (s: scheduler pos_t rule_name_t) {struct s}
    :=
      let interp_cons rl s :=
        let '(rir', r2v', nid) := get_rule_information (rules rl) nid r2v (rir_vars rir) in
        let conflict : sact := detect_conflicts rir rir' in
        let conflict_name := nid in
        let vvs := list_assoc_set (rir_vars rir') nid (bits_t 1, unot conflict) in
        let nid := nid + 1 in
        let '(r2v2, vvs, nid) := merge_reg2vars r2v r2v' conflict_name vvs nid in
        (*   fold_left (fun '(r2v2, vvs, nid) '((rp, n1), (_, n2)) => *)
        (*                ((rp, nid)::r2v2, *)
        (*                list_assoc_set vvs nid (R (fst rp), SIf conflict (SVar n1) (SVar n2)), *)
        (*                nid+1)) *)
        (*             (combine r2v r2v') *)
        (*             ([], rir_vars rir', nid) *)
        (* in *)
        let rir2 := merge_rirs rir rir' conflict_name vvs in
        get_rir_scheduler' rir2 r2v2 rules nid s
      in
      match s with
      | Done => (rir, r2v, nid)
      | Cons r s => interp_cons r s
      | Try r s1 s2 =>   (rir,r2v,nid)       (* Ignored for now *)
      | SPos _ s => get_rir_scheduler' rir r2v rules nid s
      end.


  Lemma wt_sact_detect_conflicts:
    forall (nid : nat) (rir : rule_information_raw)
           (r2v : list (reg_t * Port * nat)) (n : nat) (r1 : rule_information_raw)
           (l : list (reg_t * Port * nat)),
      wf_state [] [] r2v (rir_vars rir) rir nid ->
      wf_state [] [] l (rir_vars r1) r1 n ->
      wt_sact (rir_vars r1) (rir_failure_cond r1) (bits_t 1) ->
      vvs_grows (rir_vars rir) (rir_vars r1) ->
      wt_sact (rir_vars r1) (detect_conflicts rir r1) (bits_t 1).
  Proof.
    intros nid rir r2v n r1 l H H0 WTf H1.
    unfold detect_conflicts.
    econstructor. 3: constructor.
    eauto.
    econstructor. 3: constructor.
    econstructor. 3: constructor.
    econstructor. 3: constructor.
    - unfold detect_conflicts_read0s.
      eapply fold_left_induction. repeat constructor.
      intros (idx & s) acc IN WTS.
      econstructor. eauto.
      unfold detect_conflicts_read0s_reg.
      econstructor.
      eapply wf_rir_read0s; eauto. apply H0.
      eapply wt_sact_or_conds.
      eapply Forall_list_options. simpl.
      unfold option_map. intros x y [EQ|[EQ|[]]] A; subst; destr_in A; inv A.
      destruct p. apply list_assoc_in in Heqo.
      eapply wf_rir_write0s; eauto. eapply wf_rir_grows. apply H. auto.
      1-3: apply H.
      destruct p. apply list_assoc_in in Heqo.
      eapply wf_rir_write1s; eauto. eapply wf_rir_grows. apply H. auto.
      1-3: apply H.
      constructor. constructor.
    - unfold detect_conflicts_write0s.
      eapply fold_left_induction. repeat constructor.
      intros (idx & (g & wil)) acc IN WTS.
      econstructor. eauto.
      unfold detect_conflicts_write0s_reg.
      econstructor.
      eapply wf_wlr_glob_cond in IN; eauto. apply H0.
      eapply wt_sact_or_conds.
      eapply Forall_list_options. simpl.
      unfold option_map. intros x y [EQ|[EQ|[EQ|[]]]] A; subst; try destr_in A; inv A.
      destruct p. apply list_assoc_in in Heqo.
      eapply wf_rir_write0s; eauto. eapply wf_rir_grows. apply H. auto.
      1-3: apply H.
      destruct p. apply list_assoc_in in Heqo.
      eapply wf_rir_write1s; eauto. eapply wf_rir_grows. apply H. auto.
      1-3: apply H.
      apply list_assoc_in in H3.
      eapply wf_rir_read1s; eauto. eapply wf_rir_grows. apply H. auto.
      1-3: apply H.
      constructor. constructor.
    - unfold detect_conflicts_read1s.
      eapply fold_left_induction. repeat constructor.
      intros (idx & s) acc IN WTS.
      econstructor. eauto.
      unfold detect_conflicts_read1s_reg.
      econstructor.
      eapply wf_rir_read1s; eauto. apply H0.
      eapply wt_sact_or_conds.
      eapply Forall_list_options. simpl.
      unfold option_map. intros x y [EQ|[]] A; subst; try destr_in A; inv A.
      destruct p. apply list_assoc_in in Heqo.
      eapply wf_rir_write1s; eauto. eapply wf_rir_grows. apply H. auto.
      1-3: apply H.
      constructor. constructor.
    - unfold detect_conflicts_write1s.
      eapply fold_left_induction. repeat constructor.
      intros (idx & (g & wil)) acc IN WTS.
      econstructor. eauto.
      unfold detect_conflicts_write1s_reg.
      econstructor.
      eapply wf_wlr_glob_cond in IN; eauto. apply H0.
      eapply wt_sact_or_conds.
      eapply Forall_list_options. simpl.
      unfold option_map. intros x y [EQ|[]] A; subst; try destr_in A; inv A.
      destruct p. apply list_assoc_in in Heqo.
      eapply wf_rir_write1s; eauto. eapply wf_rir_grows. apply H. auto.
      1-3: apply H.
      constructor. constructor.
  Qed.

  Inductive good_scheduler: scheduler pos_t rule_name_t -> Prop :=
  | good_scheduler_done: good_scheduler Done
  | good_scheduler_cons r s: good_scheduler s -> good_scheduler (Cons r s)
  | good_scheduler_pos p s: good_scheduler s -> good_scheduler (SPos p s).

  Definition wwlr wl vvs :=
    forall i c wil,
      In (i, (c, wil)) wl ->
      wt_sact vvs c (bits_t 1)
      /\ (interp_sact vvs c (Bits 1 [true]) <-> Exists (fun wi => interp_sact vvs (wcond wi) (Bits 1 [true])) wil)
      /\ Forall (fun wi => wt_sact vvs (wcond wi) (bits_t 1)) wil
      /\ Forall (fun wi => wt_sact vvs (wval wi) (R i)) wil.

  Lemma wwlr_eq:
    forall wl vvs, wf_write_log_raw wl vvs <-> wwlr wl vvs.
  Proof.
    unfold wwlr; split.
    - intro A; inv A. intros. repeat refine (conj _ _).
      eapply wf_wlr_glob_cond0 in H; eauto.
      eapply wf_wlr_glob_interp0 in H; eauto. tauto.
      eapply wf_wlr_glob_interp0 in H; eauto. tauto.
      eapply wf_wlr_each_cond0 in H; eauto.
      eapply wf_wlr_each_act0 in H; eauto.
    - intros. split; intros i (c & wil) IN; simpl; eauto.
      eapply H in IN. intuition.
      eapply H in IN. intuition.
      eapply H in IN. intuition.
      eapply H in IN. intuition.
  Qed.


  Lemma wt_merge_write_logs:
    forall vvs
           (WV: wt_vvs vvs)
           (VSV: vvs_smaller_variables vvs)
           n
           (VR: vvs_range vvs n)
           cond wl2
           (F2: wf_write_log_raw wl2 vvs)
           wl1
           (F1: wf_write_log_raw wl1 vvs)
           (WTcond: wt_sact vvs cond (bits_t 1)),
      wf_write_log_raw (merge_write_logs wl1 wl2 cond) vvs.
  Proof.
    intros. rewrite wwlr_eq. rewrite wwlr_eq in F1, F2.
    revert wl2 F2 wl1 F1.
    induction wl2; simpl; intros; eauto.
    repeat destr.
    eapply IHwl2.
    - red in F2; red. intros i c wil IN.
      eapply F2. right. eauto.
    - red.
      intros i c wil IN.
      unfold list_assoc_modify in IN.
      destr_in IN.
      + eapply in_list_assoc_set_inv in IN. destruct IN as [IN|IN].
        * destr_in IN. inv IN.
          apply list_assoc_in in Heqo.
          specialize (F1 _ _ _ Heqo).
          specialize (F2 _ _ _ (or_introl eq_refl)).
          destruct F1 as (Wcond1 & Icond1 & Wecond1 & Weact1).
          destruct F2 as (Wcond2 & Icond2 & Wecond2 & Weact2).
          split; [|split;[|split]].
          -- econstructor. eauto. econstructor. eauto. eauto.
             constructor. constructor.
          -- split.
             ++ intro I. inv I. inv H4.
                exploit interp_sact_wt. 5: apply H2. all: eauto.
                exploit interp_sact_wt. 5: apply H3. all: eauto.
                exploit interp_sact_wt. 5: apply H7. all: eauto.
                intros A B C.
                apply wt_val_bool in A.
                apply wt_val_bool in B.
                apply wt_val_bool in C.
                destruct A, B, C. subst.
                simpl in H5, H8. inv H8. inv H5.
                apply orb_true_iff in H0. rewrite andb_true_iff in H0.
                destruct H0. subst. rewrite Icond1 in H2.
                apply Exists_app. left.
                simpl. eauto.
                destruct H; subst.
                rewrite Icond2 in H7.
                apply Exists_app. right.


                Lemma Exists_map:
                  forall {A B: Type} (P: A -> Prop) (f: B -> A) l,
                    Exists (fun x => P (f x)) l <->
                      Exists P (map f l).
                Proof.
                  induction l; simpl; intros; eauto.
                  split; inversion 1.
                  rewrite ! Exists_cons. tauto.
                Qed.
                apply Exists_map. simpl. rewrite orb_true_r.
                eapply Exists_impl. 2: eauto. simpl. intros.
                econstructor. eauto. eauto. reflexivity.
             ++ rewrite Exists_app. rewrite <- Exists_map. simpl.
                intros [EX|EX].
                rewrite <- Icond1 in EX.
                edestruct wt_sact_interp with (a:=cond) as (vcond & Icond & WTcond0); eauto.
                apply wt_val_bool in WTcond0; destruct WTcond0; subst.
                edestruct wt_sact_interp with (a:=s) as (vs & Is & WTs0); eauto.
                apply wt_val_bool in WTs0; destruct WTs0; subst.
                econstructor; eauto.
                econstructor; eauto. reflexivity. reflexivity.
                rewrite Exists_exists in EX. destruct EX as (x & IN & I).
                inv I.
                exploit interp_sact_wt. 5: apply H2. all: eauto.
                exploit interp_sact_wt. 5: apply H4. all: eauto.
                rewrite Forall_forall in Wecond2; eauto.
                intros A B.
                apply wt_val_bool in A; destruct A; subst.
                apply wt_val_bool in B; destruct B; subst.
                simpl in H5. inv H5.
                apply andb_true_iff in H0. destruct H0; subst. simpl.
                trim (proj2 Icond2).
                rewrite Exists_exists; eexists; split; eauto. intro.
                edestruct wt_sact_interp with (a:=s0) as (vs0 & Is0 & WTs00); eauto.
                apply wt_val_bool in WTs00; destruct WTs00; subst.
                (* edestruct wt_sact_interp with (a:=s) as (vs & Is & WTs0); eauto. *)
                (* apply wt_val_bool in WTs0; destruct WTs0; subst. *)
                econstructor; eauto.
                econstructor; eauto. reflexivity. simpl. rewrite orb_true_r; auto.
          -- apply Forall_app. split; auto.
             Lemma Forall_map:
               forall {A B: Type} (P: A -> Prop) (f: B -> A) l,
                 Forall (fun x => P (f x)) l <->
                   Forall P (map f l).
             Proof.
               induction l; simpl; intros; eauto.
               split; constructor.
               split; inversion 1; econstructor; eauto.
               subst. tauto. tauto.
             Qed.
             apply Forall_map. simpl.
             eapply Forall_impl. 2: apply Wecond2. simpl. intros.
             econstructor; eauto. constructor.
          -- apply Forall_app. split; auto.
             apply Forall_map. simpl. eauto.
        * eapply F1. auto.
      + apply in_list_assoc_set_inv in IN. destruct IN; eauto.
        inv H.
        specialize (F2 _ _ _ (or_introl eq_refl)).
        destruct F2 as (Wcond2 & Icond2 & Wecond2 & Weact2).
        split; [|split;[|split]].
        * econstructor. eauto. eauto. constructor.
        * split.
          -- intro I. inv I.
             exploit interp_sact_wt. 5: apply H2. all: eauto.
             exploit interp_sact_wt. 5: apply H4. all: eauto.
             intros A B.
             apply wt_val_bool in A.
             apply wt_val_bool in B.
             destruct A, B. subst.
             simpl in H5. inv H5.
             rewrite andb_true_iff in H0.
             destruct H0. subst. rewrite Icond2 in H4.
             apply Exists_map. simpl.
             eapply Exists_impl. 2: eauto.  simpl.
             intros; econstructor; eauto.
          -- rewrite <- Exists_map. simpl.
             intro EX. rewrite Exists_exists in EX. destruct EX as (x & IN & I).
             inv I.
             exploit interp_sact_wt. 5: apply H2. all: eauto.
             exploit interp_sact_wt. 5: apply H4. all: eauto.
             rewrite Forall_forall in Wecond2; eauto.
             intros A B.
             apply wt_val_bool in A; destruct A; subst.
             apply wt_val_bool in B; destruct B; subst.
             simpl in H5. inv H5.
             apply andb_true_iff in H0. destruct H0; subst. simpl.
             trim (proj2 Icond2).
             rewrite Exists_exists; eexists; split; eauto. intro.
             econstructor; eauto.
        * apply Forall_map. simpl.
          eapply Forall_impl. 2: apply Wecond2. simpl. intros.
          econstructor; eauto. constructor.
        * apply Forall_map. simpl. eauto.
  Qed.


  Lemma wf_state_vvs_grows:
    forall tsig env r2v vvs1 vvs2 rir n n2 r2v2 rir2,
      wf_state tsig env r2v vvs1 rir n ->
      vvs_grows vvs1 vvs2 ->
      wf_state tsig env r2v2 vvs2 rir2 n2 ->
      wf_state tsig env r2v vvs2 rir2 n2.
  Proof.
    intros. inv H; inv H1.
    split; eauto.
    eapply reg2var_vvs_grows; eauto.
  Qed.

  Lemma Forall_list_assoc_modify:
    forall {K V: Type} {eqdec: EqDec K} (P: K * V -> Prop)
           l (P0: Forall P l) k def f
           (Pk: P (k, def))
           (Pi: forall v, P (k,v) -> P (k, f v)),
      Forall P (list_assoc_modify l k def f).
  Proof.
    induction 1; simpl; intros; eauto.
    - unfold list_assoc_modify. simpl. constructor; auto.
    - unfold list_assoc_modify. simpl. destr. destr.
      subst; constructor; eauto.
      constructor; eauto.
  Qed.

  Lemma wt_merge_cond_logs:
    forall vvs cond rl2
           (F2: Forall (fun '(idx,c) => wt_sact vvs c (bits_t 1)) rl2)
           rl1
           (F1: Forall (fun '(idx,c) => wt_sact vvs c (bits_t 1)) rl1)
           i a,
      wt_sact vvs cond (bits_t 1) ->
      In (i, a) (merge_cond_logs rl1 rl2 cond) ->
      wt_sact vvs a (bits_t 1).
  Proof.
    induction 1; simpl; intros; eauto.
    rewrite Forall_forall in F1; apply F1 in H0; eauto.
    destr_in H1.
    eapply IHF2 in H1. auto.
    eapply Forall_list_assoc_modify. eauto.
    econstructor; eauto.
    constructor.
    intros; econstructor; eauto. econstructor; eauto. constructor. constructor.
    eauto.
  Qed.

  Lemma wf_state_merge_rirs:
    forall (nid : nat) (rir : rule_information_raw)
           (r2v : list (reg_t * Port * nat)) (n : nat) (r1 : rule_information_raw)
           (l : list (reg_t * Port * nat)) (n0 : nat)
           (l0 : list (reg_t * Port * nat)) (l1 : list (nat * (type * sact))),
      wf_state [] [] r2v (rir_vars rir) rir nid ->
      wf_state [] [] l (rir_vars r1) r1 n ->
      vvs_grows (rir_vars rir) (rir_vars r1) ->
      wt_sact (rir_vars r1) (rir_failure_cond r1) (bits_t 1) ->
      merge_reg2vars r2v l n
                     (list_assoc_set (rir_vars r1) n
                                     (bits_t 1, unot (detect_conflicts rir r1))) 
                     (n + 1) = (l0, l1, n0) ->
      wf_state [] [] l0 l1 (merge_rirs rir r1 n l1) n0.
  Proof.
    intros nid rir r2v n r1 l n0 l0 l1.
    intros.
    exploit merge_reg2var_grows'. eauto.
    2: replace (n+1) with (S n) by lia; eapply wf_state_vvs_set; eauto.
    eapply wf_state_vvs_grows. eauto.
    eapply vvs_grows_trans. eauto. eapply vvs_grows_set. apply H0. lia.
    eapply wf_state_vvs_grows_incr. apply H0.
    eapply rir_grows_set. apply H0. unfold valid_name; lia.
    eapply wt_vvs_set. apply H0. apply H0.
    econstructor.
    eapply wt_sact_detect_conflicts; eauto.
    constructor. lia.
    eapply vvs_range_list_assoc_set.
    eapply vvs_range_incr. 2: eapply H0. lia. red; lia.
    eapply vvs_smaller_variables_set. apply H0.
    {
      intros.
      eapply wt_sact_valid_vars in H4. eauto. apply H0. econstructor. 2: constructor.
      eapply wt_sact_detect_conflicts; eauto.
    }
    eapply wf_rir_grows; eauto. apply H0.
    eapply vvs_grows_set; eauto.
    apply H0. apply H0. apply H0. apply H0. lia.
    econstructor. 2: constructor.
    eapply wt_sact_detect_conflicts; eauto.
    {
      intros.
      eapply wt_sact_valid_vars in H4. eauto. apply H0. econstructor. 2: constructor.
      eapply wt_sact_detect_conflicts; eauto.
    }
    red; lia.
    econstructor. rewrite list_assoc_gss. eauto.
    intros (VG2 & NID2 & WFS2 & INTERP2).
    inv WFS2; split; eauto.
    inv H. inv wfs_rir1; inv wfs_rir0; split; simpl.

    intros; eapply wt_merge_cond_logs. 4: eauto.
    rewrite Forall_forall; intros (?&?) IN; now eauto.
    rewrite Forall_forall; intros (?&?) IN.
    eapply wt_sact_vvs_grows. 2: now eauto. eapply vvs_grows_trans; eauto.
    eapply vvs_grows_trans; eauto. eapply vvs_grows_set; eauto.
    eapply vvs_range_incr. 2: apply H0. lia.
    econstructor.
    eapply VG2. rewrite list_assoc_gss. eauto.
    intros; eapply wt_merge_cond_logs. 4: eauto.
    rewrite Forall_forall; intros (?&?) IN; now eauto.
    rewrite Forall_forall; intros (?&?) IN.
    eapply wt_sact_vvs_grows. 2: now eauto. eapply vvs_grows_trans; eauto.
    eapply vvs_grows_trans; eauto. eapply vvs_grows_set; eauto.
    eapply vvs_range_incr. 2: apply H0. lia.
    econstructor.
    eapply VG2. rewrite list_assoc_gss. eauto.

    eapply wt_merge_write_logs; eauto.
    eapply wf_write_log_raw_incr. eauto.
    eapply vvs_grows_trans. eauto.
    eapply vvs_grows_trans. 2: eauto.
    eapply vvs_grows_set; eauto. apply H0.
    auto. eauto.  auto.

    eapply wt_sact_vvs_grows. eauto.
    econstructor. rewrite list_assoc_gss. eauto.
    eapply wt_merge_write_logs; eauto.
    eapply wf_write_log_raw_incr. eauto.
    eapply vvs_grows_trans. eauto.
    eapply vvs_grows_trans. 2: eauto.
    eapply vvs_grows_set; eauto. apply H0.
    auto. eauto.  auto.

    eapply wt_sact_vvs_grows. eauto.
    econstructor. rewrite list_assoc_gss. eauto.
    econstructor.
    eapply wt_sact_vvs_grows. 2: eauto. eapply vvs_grows_trans. eauto.
    eapply vvs_grows_trans. 2: eauto. eapply vvs_grows_set; eauto.
    eapply H0.
    eapply wt_sact_vvs_grows. 2: eauto.
    eapply vvs_grows_trans. 2: eauto. eapply vvs_grows_set; eauto.
    eapply H0.
    constructor.
  Qed.

  Lemma log_app_empty:
    forall (l: Log REnv),
      log_app (REnv:=REnv) log_empty l = l.
  Proof.
    unfold log_app, log_empty; intros.
    rewrite <- (create_getenv_id _ (map2 _ _ _ _)).
    rewrite <- (create_getenv_id _ l) at 2.
    apply create_funext.
    intros.
    rewrite getenv_map2.
    rewrite getenv_create. reflexivity.
  Qed.

  Lemma r2v_vvs_aux:
    forall ks n m r2v0 r2v3 vvs3 m2
           r2v1 r2v2 vvs2
           (MRA: merge_reg2vars_aux ks r2v1 r2v2 r2v0 n vvs2 m = (r2v3, vvs3, m2))
           (VR: vvs_range vvs2 m)
           (WT: wt_vvs vvs2)
           (VVS: vvs_smaller_variables vvs2)
           (R2V1: reg2var_vvs r2v1 vvs2)
           (R2V2: reg2var_vvs r2v2 vvs2)
           (WTn: wt_sact vvs2 (SVar n) (bits_t 1)),
      vvs_grows vvs2 vvs3 /\ vvs_range vvs3 m2 /\ m <= m2 /\ wt_vvs vvs3 /\ vvs_smaller_variables vvs3.
  Proof.
    induction ks; simpl; intros; eauto.
    - inv MRA. split; eauto using vvs_grows_refl.
    - repeat destr_in MRA. 
      assert (VGG: vvs_grows vvs2 l0).
        unfold merge_reg2vars_reg in Heqp0.
        repeat destr_in Heqp0; inv Heqp0; eauto using vvs_grows_refl.
        eapply vvs_grows_set. eauto. lia.
        eapply vvs_grows_set. eauto. lia.
      eapply IHks in MRA.
      destruct MRA as (?&?&?&?&?); repeat refine (conj _ _); auto.
      + eapply vvs_grows_trans; eauto.
      + unfold merge_reg2vars_reg in Heqp0.
        repeat destr_in Heqp0; inv Heqp0; lia.
      + unfold merge_reg2vars_reg in Heqp0.
        repeat destr_in Heqp0; inv Heqp0; eauto.
        eapply vvs_range_list_assoc_set. eapply vvs_range_incr. 2: eauto. lia. red; lia.
        eapply vvs_range_list_assoc_set. eapply vvs_range_incr. 2: eauto. lia. red; lia.
      + unfold merge_reg2vars_reg in Heqp0.
        edestruct (R2V1 (r0,p)) as (? & GET1 & ? & GET2).
        edestruct (R2V2 (r0,p)) as (? & GET3 & ? & GET4).
        setoid_rewrite GET1 in Heqp0.
        setoid_rewrite GET3 in Heqp0.
        rewrite GET2 in Heqp0.
        repeat destr_in Heqp0; inv Heqp0; eauto.
        eapply wt_vvs_set; eauto. econstructor; eauto.
        econstructor; eauto.
        econstructor; eauto.
      + unfold merge_reg2vars_reg in Heqp0.
        edestruct (R2V1 (r0,p)) as (? & GET1 & ? & GET2).
        edestruct (R2V2 (r0,p)) as (? & GET3 & ? & GET4).
        setoid_rewrite GET1 in Heqp0.
        setoid_rewrite GET3 in Heqp0.
        rewrite GET2 in Heqp0.
        repeat destr_in Heqp0; inv Heqp0; eauto.
        eapply vvs_smaller_variables_set; eauto.
        simpl; intros.
        inv H. inv H4. inv WTn. eapply VR in H0. red in H0. lia.
        inv H4. eapply VR in GET2. red in GET2. lia.
        inv H4. eapply VR in GET4. red in GET4. lia.
      + eapply reg2var_vvs_grows; eauto using vvs_grows_trans.
      + eapply reg2var_vvs_grows; eauto using vvs_grows_trans.
      + eapply wt_sact_vvs_grows; eauto.
  Qed.

  Lemma r2v_vvs_aux_merge:
    forall ks n m (GT: m > n) r2v0 r2v3 vvs3 m2
           r2v1 r2v2 vvs
           (MRA: merge_reg2vars_aux ks r2v1 r2v2 r2v0 n vvs m = (r2v3, vvs3, m2))
           (R2V1: reg2var_vvs r2v1 vvs)
           (R2V2: reg2var_vvs r2v2 vvs)
           (VR: vvs_range vvs m)
           (WTV: wt_vvs vvs)
           (VVS: vvs_smaller_variables vvs)
           (WTcond: wt_sact vvs (SVar n) (bits_t 1))
           (IH: forall x y,
               list_assoc r2v0 x = Some y ->
               exists y1 y2,
                 list_assoc r2v1 x = Some y1
                 /\ list_assoc r2v2 x = Some y2
                 /\ forall b v,
                   interp_sact vvs3 (SVar n) (Bits 1 [b]) ->
                   interp_sact vvs3 (SVar (if b then y1 else y2)) v <->
                     interp_sact vvs3 (SVar y) v),
    forall x y,
      list_assoc r2v3 x = Some y ->
      exists y1 y2,
        list_assoc r2v1 x = Some y1
        /\ list_assoc r2v2 x = Some y2
        /\ forall b v,
          interp_sact vvs3 (SVar n) (Bits 1 [b]) ->
          interp_sact vvs3 (SVar (if b then y1 else y2)) v <->
            interp_sact vvs3 (SVar y) v.
  Proof.
    induction ks; simpl; intros; eauto.
    - inv MRA. eauto.
    - repeat destr_in MRA.
      unfold merge_reg2vars_reg in Heqp0.
      edestruct (R2V1 (r0,p)) as (? & GET1 & ? & GET2).
      edestruct (R2V2 (r0,p)) as (? & GET3 & ? & GET4).
      setoid_rewrite GET1 in Heqp0.
      setoid_rewrite GET3 in Heqp0.
      rewrite GET2 in Heqp0.
      destr_in Heqp0; inv Heqp0.
      + eapply IHks in MRA; eauto.
        intros x0 y0 GET.
        rewrite list_assoc_spec in GET. destr_in GET.
        * inv GET. do 2 eexists; split.  eauto. split. eauto.
          intros. destr; tauto.
        * eauto.
      + assert (VG2: vvs_grows vvs (list_assoc_set vvs m (R r0, SIf (SVar n) (SVar x0) (SVar x2)))).
        {
          eapply vvs_grows_set. eauto. lia.
        }
        assert (VR2: vvs_range (list_assoc_set vvs m (R r0, SIf (SVar n) (SVar x0) (SVar x2))) (S m)).
        {
          eapply vvs_range_list_assoc_set.
          eapply vvs_range_incr. 2: eauto. lia. red; lia.
        }
        assert (WT2:   wt_vvs (list_assoc_set vvs m (R r0, SIf (SVar n) (SVar x0) (SVar x2)))).
        {
          eapply wt_vvs_set. eauto. eauto. econstructor. eauto.
          econstructor. eauto. econstructor; eauto. lia.
        }
        assert (VSV:  vvs_smaller_variables (list_assoc_set vvs m (R r0, SIf (SVar n) (SVar x0) (SVar x2)))).
        {
          eapply vvs_smaller_variables_set; eauto.
          simpl; intros.
          inv H0. inv H5. inv WTcond. eapply VR in H1. red in H1. lia.
          inv H5. eapply VR in GET2. red in GET2. lia.
          inv H5. eapply VR in GET4. red in GET4. lia.
        }
        assert (WTn2:  wt_sact (list_assoc_set vvs m (R r0, SIf (SVar n) (SVar x0) (SVar x2)))
                               (SVar n) (bits_t 1)).
        {
          eapply wt_sact_vvs_grows. 2: eauto. eauto.
        }
        eapply IHks in MRA; eauto.
        * eapply reg2var_vvs_grows. eauto. eauto.
        * eapply reg2var_vvs_grows. eauto. eauto.
        * intros x4 y0 GET.
          rewrite list_assoc_spec in GET. destr_in GET.
          -- inv GET. do 2 eexists; split.  eauto. split. eauto.
             intros.

             Lemma interp_sact_vvs_grows_iff:
               forall (vvs vvs' : list (nat * (type * sact))) (a : sact)
                      (v : val) (t : type) (n : nat),
                 wt_vvs vvs ->
                 vvs_smaller_variables vvs ->
                 vvs_grows vvs vvs' ->
                 vvs_range vvs n ->
                 wt_sact vvs a t -> interp_sact vvs' a v <-> interp_sact vvs a v.
             Proof.
               intros; split.
               eapply interp_sact_vvs_grows_inv; eauto.
               eapply vvs_grows_interp_sact; eauto.
             Qed.
             edestruct r2v_vvs_aux as (VG3 & VR3 & LE2 & WTVVS2 & VSV2). eauto.
             all: eauto.
             eapply reg2var_vvs_grows; eauto using vvs_grows_trans.
             eapply reg2var_vvs_grows; eauto using vvs_grows_trans.

             rewrite (interp_sact_vvs_grows_iff) with (a:=SVar y0).
             4: apply VG3. all: eauto.
             ++ split; intros.
                ** inv H1.
                   econstructor. rewrite list_assoc_gss. eauto.
                   rewrite <- interp_sact_vvs_grows_iff. econstructor. apply H0.
                   destruct b; econstructor; eauto.
                   all: eauto.
                   eapply wt_sact_vvs_grows. eauto.
                   econstructor; eauto.
                   econstructor; eauto.
                   econstructor; eauto.
                ** inv H1. rewrite list_assoc_gss in H3. inv H3. inv H4.
                   eapply vvs_grows_interp_sact. eauto.
                   exploit interp_sact_determ. apply H0. eapply vvs_grows_interp_sact. eauto. apply H6. intros A; inv A.
                   destruct b0; inv H7; econstructor; eauto.
             ++ econstructor. rewrite list_assoc_gss. eauto.
          -- eauto.
  Qed.

  Lemma log_existsb_log_app:
    forall (l1 l2: Log REnv) idx fn,
      log_existsb (log_app l1 l2) idx fn = log_existsb l1 idx fn || log_existsb l2 idx fn.
  Proof.
    unfold log_existsb, log_app.
    intros.
    rewrite getenv_map2.
    rewrite existsb_app. auto.
  Qed.

  Lemma match_logs_merge_logs:
    forall r2v vvs rir sched_log l2,
      match_logs_r2v r2v vvs rir sched_log l2 ->
      match_logs_r2v r2v vvs rir (log_app l2 sched_log) log_empty.
  Proof.
    intros r2v vvs rir sched_log l2 H.
    inv H; split; auto.
    - intros.
      unfold may_read in H.
      destr_in H.
      + rewrite andb_true_iff in H.
        rewrite ! negb_true_iff in H. destruct H.
        rewrite log_existsb_log_app in H, H1.
        rewrite orb_false_iff in H, H1. destruct H, H1.
        exploit mlr_read0. 2: eauto. unfold may_read. rewrite H2, H3. reflexivity.
        simpl. eauto.
      + rewrite ! negb_true_iff in H.
        rewrite log_existsb_log_app in H.
        rewrite orb_false_iff in H. destruct H.
        exploit mlr_read0. 2: eauto. unfold may_read. rewrite H1. reflexivity.
        simpl. rewrite log_app_empty. eauto.
    - intros idx. rewrite log_app_empty. eauto.
    - intros idx. rewrite log_app_empty. eauto.
    - intros idx. rewrite log_app_empty. eauto.
  Qed.
  
 
  Lemma r2v_vvs:
    forall r2v1 r2v2 vvs1 vvs2,
      reg2var_vvs r2v1 vvs1 ->
      reg2var_vvs r2v2 vvs2 ->
      vvs_grows vvs1 vvs2 ->
      forall n m (GT: m > n) r2v3 vvs3 m2,
        merge_reg2vars r2v1 r2v2 n vvs2 m = (r2v3, vvs3, m2) ->
        vvs_range vvs2 m ->
        wt_vvs vvs2 ->
        vvs_smaller_variables vvs2 ->
        wt_sact vvs2 (SVar n) (bits_t 1) ->
        forall x y,
          list_assoc r2v3 x = Some y ->
          exists y1 y2,
            list_assoc r2v1 x = Some y1
            /\ list_assoc r2v2 x = Some y2
            /\ forall b v,
              interp_sact vvs3 (SVar n) (Bits 1 [b]) ->
              interp_sact vvs3 (SVar (if b then y1 else y2)) v <->
                interp_sact vvs3 (SVar y) v.
  Proof.
    unfold merge_reg2vars.
    intros.
    eapply r2v_vvs_aux_merge. 2: eauto. all: auto.
    eapply reg2var_vvs_grows. eauto. eauto. simpl; easy.
  Qed.

  Definition list_assoc_def {K V: Type} {eqdec: EqDec K}
             (l: (list (K*V)))
             k vdef :=
    match list_assoc l k with
    | None => vdef
    | Some v => v
    end.

      (* Lemma list_assoc_merge_cond_logs: *)
      (*   forall cond idx vvs cl2 cl1 c n, *)
      (*     wt_vvs vvs -> *)
      (*     vvs_smaller_variables vvs -> *)
      (*     vvs_range vvs n -> *)
      (*     (forall i a, In (i,a) cl1 -> wt_sact vvs a (bits_t 1)) -> *)
      (*     (forall i a, In (i,a) cl2 -> wt_sact vvs a (bits_t 1)) -> *)
      (*     wt_sact vvs cond (bits_t 1) -> *)
      (*   list_assoc (merge_cond_logs cl1 cl2 cond) idx = Some c -> *)
      (*   forall v, *)
      (*     interp_sact vvs c v <-> *)
      (*       interp_sact vvs (uor (list_assoc_def cl1 idx const_true) (uand cond (list_assoc_def cl2 idx const_true))) v. *)
      (* Proof. *)
      (*   induction cl2; simpl; intros; eauto. *)
      (*   - unfold list_assoc_def. simpl. *)
      (*     split; intros. *)
      (*     + destr. *)
      (*       inv H5. *)
      (*       exploit interp_sact_wt. 5: apply  H6. all: eauto. *)
      (*       eapply H2. eapply list_assoc_in; eauto. *)
      (*       intros WTv. *)
      (*       apply wt_val_bool in WTv; destruct WTv. subst. *)
            
      (*       edestruct wt_sact_interp as (vv & Iv & WTv). 4: eapply H4. *)
      (*       all: eauto. *)
      (*       apply wt_val_bool in WTv; destruct WTv. subst. *)
      (*       econstructor. eauto. econstructor; eauto. econstructor. reflexivity. simpl. *)
      (*       destruct x0; simpl. rewrite  *)
      (*       inv H5. *)
      (* Qed. *)

  Lemma match_logs_merge_rirs:
    forall r2v1 r2v2 r2v3 rir r1 sched_log l2 vvs2 n m vvs3 m2,
      match_logs_r2v r2v1 (rir_vars rir) rir sched_log log_empty ->
      match_logs_r2v r2v2 (rir_vars r1) r1 sched_log l2 ->
      vvs_grows (rir_vars rir) (rir_vars r1) ->
      vvs_grows (rir_vars r1) vvs2 ->
      wt_sact vvs2 (SVar n) (bits_t 1) ->
      m > n ->
      wf_state [] [] r2v2 vvs2 r1 m ->
      reg2var_vvs r2v1 (rir_vars rir) ->
      reg2var_vvs r2v2 (rir_vars r1) ->
      merge_reg2vars r2v1 r2v2 n vvs2 m = (r2v3, vvs3, m2) ->
      match_logs_r2v r2v3 vvs3 (merge_rirs rir r1 n vvs2) sched_log l2.
  Proof.
    intros r2v1 r2v2 r2v3 rir r1 sched_log l2 vvs2 n m vvs3 m2 MLR1 MLR2 VG1 VG2 WTn GT WF R2V1 R2V2 MR.
    split.
    - intros reg prt n0 MaR GET.
      edestruct r2v_vvs as (y1 & y2 & GET1 & GET2 & INTERP). 5: eauto. eauto.
      eapply reg2var_vvs_grows. eauto. auto.
      eapply vvs_grows_trans; eauto. auto. apply WF. apply WF. apply WF. auto. eauto.

      edestruct r2v_vvs_aux as (VG3 & VR2 & LE2 & WT3 & VSV3). apply MR. apply WF. apply WF.
      apply WF.
      eapply reg2var_vvs_grows. eauto. eauto using vvs_grows_trans.
      eapply reg2var_vvs_grows. eauto. eauto using vvs_grows_trans.
      auto.
      eapply wt_sact_vvs_grows in WTn; eauto.
      edestruct wt_sact_interp as (? & ISv & WTv). 4: apply WTn. all: eauto.
      apply wt_val_bool in WTv. destruct WTv; subst.
      erewrite <- INTERP.  2: eauto.
      exploit mlr_read. apply MLR1. eauto. eauto.
      exploit mlr_read. apply MLR2. eauto. eauto.
      intros INT2 INT1.
      eapply vvs_grows_interp_sact with (v2:=vvs3) in INT2. destr; eauto.
      2: eauto using vvs_grows_trans.
      
      admit.
    - intros idx EX.
      rewrite log_existsb_log_app in EX.
      rewrite orb_false_iff in EX. destruct EX.
      intros c GET.
      simpl in GET.

  Admitted.

  Lemma get_rir_scheduler_ok:
    forall (rules: rule_name_t -> uact)
           s
           (GS: good_scheduler s)
           (nid: nat)
           rir r2v rir' r2v' nid'
           (GRI: get_rir_scheduler' rir r2v rules nid s = (rir', r2v', nid'))
           (WT: forall r,
             exists tret,
               BitsToLists.wt_daction pos_t string string (R:=R) (Sigma:=Sigma) [] (rules r) tret)
           sched_log
           (WTL: wt_log R REnv sched_log)
           (WTR: wt_renv R REnv r)
           (WFS: wf_state [] [] r2v (rir_vars rir) rir nid)
           (MLR: match_logs_r2v r2v (rir_vars rir) rir sched_log log_empty),
      wf_state [] [] r2v' (rir_vars rir') rir' nid'
      /\ nid <= nid'
      /\ forall sched_log'
                (INTERP: interp_dscheduler' rules r sigma sched_log s = sched_log'),
        match_logs_r2v r2v' (rir_vars rir') rir' sched_log' log_empty.
  Proof.
    induction 1; simpl; intros; eauto.
    - inv GRI. repeat refine (conj _ _); eauto.
      intros; subst; eauto.
    - edestruct (WT r0) as (tret & WTr). repeat destr_in GRI.
      exploit get_rule_information_ok; eauto.
      + inv WFS.
        split; eauto.
        inv wfs_rir0.
        split; simpl; eauto. easy. easy.
        split; simpl; try easy.
        split; simpl; try easy.
        repeat constructor.
      + inv MLR; split; simpl; try easy.
      + intros (WFS1 & RG1 & NID & INTERP).
        destr.
        * unfold interp_drule in Heqo. repeat destr_in Heqo; inv Heqo.
          edestruct INTERP as (IF1 & _ & MLR1). eauto.
          clear INTERP.
          edestruct IHGS as (WFS2 & NID2 & INTERP2). eauto. eauto.
          instantiate (1:=log_app l2 sched_log). eapply wt_log_app.
          {
            generalize (wt_daction_preserves_wt_env pos_t string string R Sigma REnv r sigma wt_sigma (rules r0) [] l3 tret [] sched_log log_empty l2 v). intro WDPWE.
            trim WDPWE. auto.
            trim WDPWE. constructor.
            trim WDPWE. auto.
            trim WDPWE. auto.
            trim WDPWE. red. intros idx le. unfold log_empty. rewrite getenv_create. easy.
            trim WDPWE. auto. intuition.
          }
          eauto.
          eauto.
          simpl.
          eapply wf_state_merge_rirs. 5: eauto. eauto. eauto. apply RG1. apply WFS1.
          simpl.

          {

            assert (interp_sact (rir_vars r1) (detect_conflicts rir r1) (Bits 1 [false])).
            {
              econstructor. eauto.
              econstructor. econstructor.
              econstructor.
              unfold detect_conflicts_read0s.
              instantiate (1:= Bits 1 [false]).
              eapply fold_left_induction. repeat constructor.
              intros (idx & c) acc.
              econstructor. eauto. econstructor.
            }

            admit.
            (* split. *)
            (* - intros reg prt n1 MR GET. *)
            (*   inv MLR1. *)
            (*   exploit mlr_read0. 2: eauto. *)
            (* exploit merge_reg2var_grows'. eauto. *)

            (* -  *)
          }
          repeat refine (conj _ _). eauto.
          {
            Lemma merge_reg2var_nid:
              forall r2v1 r2v2 n vvs m r2v3 vvs2 m2,
                merge_reg2vars r2v1 r2v2 n vvs m = (r2v3, vvs2, m2) ->
                m <= m2.
            Proof.
              unfold merge_reg2vars.
              intros r2v1.
              generalize (@nil (reg_t * Port * nat)).
              generalize (map fst r2v1).
              intro l; revert l r2v1.
              induction l; simpl; intros; eauto.
              inv H. lia.
              repeat destr_in H.
              apply IHl in H.
              unfold merge_reg2vars_reg in Heqp0.
              repeat destr_in Heqp0; inv Heqp0; lia.
            Qed.
            eapply merge_reg2var_nid in Heqp1. lia.
          }
          intros. eauto.
        * unfold interp_drule in Heqo. repeat destr_in Heqo; inv Heqo.
          edestruct IHGS as (WFS2 & NID2 & INTERP2). eauto. eauto.
          eauto. eauto.
          eapply wf_state_merge_rirs. 5: eauto. eauto. eauto. apply RG1. apply WFS1.
          admit.
          repeat refine (conj _ _). eauto.
          eapply merge_reg2var_nid in Heqp1. lia.
          intros. eauto.
  Admitted.

  Lemma clean_rule_information_ok:
    forall ua r,
      rule_information_raw_ok r ua ->
      rule_information_clean_ok (clean_rule_information r) ua.
  Proof.
  Admitted.


  (* ** All scheduling conflicts *)
  (* This function detects all the scheduling conflicts. It returns a list of
     rule_information where the failure conditions have been edited
     appropriately. *)
  Definition detect_all_conflicts (rl: list rule_information_raw)
  : list rule_information_clean :=
    let raw := fold_left
      (fun acc c => acc ++ [detect_conflicts_any_prior c acc])
      rl []
    in
    (* TODO: PROVE STUFF HERE *)
    map clean_rule_information raw.

  (* * Schedule merger *)
  (* Starting from a schedule with all the right failures conditions under the
     form of a list of rule_information structures, we want to get to a
     schedule_information structure (which is a collection of actions with no
     failure condition, as a schedule can't fail). *)
  (* ** Integrate failure conditions into actions *)
  (* We start by extracting the action logs of all the rules in the schedule. In
     fact, the failure condition was just a building block: we can remove it
     without losing information as long as we integrate it into the conditions
     of all the actions of the rule it guarded. *)
  Definition prepend_condition_writes (cond: sact) (wl: write_log)
  : write_log :=
    map
      (fun '(reg, wl') =>
        (reg, map (fun wi => {| wcond := uand cond (wcond wi); wval := wval wi |}) wl'))
      wl.
  Definition prepend_condition_extcalls (cond: sact) (el: extcall_log)
  : extcall_log :=
    map
      (fun '(ufn, ei) =>
        (ufn, {|
          econd := uand cond (econd ei);
          ebind := ebind ei; earg := earg ei |}))
      el.

  Definition prepend_failure_actions
    (ric: rule_information_clean) (fail_var_name: string)
  : rule_information_clean :=
    let cond := (DVar fail_var_name) in
    ric
      <|ric_write0s := prepend_condition_writes cond (ric_write0s ric)|>
      <|ric_write1s := prepend_condition_writes cond (ric_write1s ric)|>.

  Definition to_negated_cond (cond: option sact) : sact :=
    match cond with
    | Some x => unot x
    | None => const_true
    end.

  Definition integrate_failures (ri: list rule_information_clean) nid
  : list rule_information_clean * nat :=
    fold_left
        (fun '(acc, id') r =>
          let fail_var_name := id' in
          let not_failure_cond := unot (ric_failure_cond r) in (
            ((prepend_failure_actions r fail_var_name)
              (* TODO perhaps return not_failure_cond separately and regroup all
                 such variables at the end of the list so as to preserve order
                *)
              <|ric_vars := (ric_vars r)++[(fail_var_name, not_failure_cond)]|>
              <|ric_failure_cond := const_false|>
            )::acc, S id'))
        ri
        ([], nid).

  (* ** Merge duplicated actions across rules *)
  (* *** Merge one rule *)
  (* Used for both write0 and write1 *)
  Definition merge_next_write (reg: reg_t) (wl: write_log) (w: list write_info)
  : write_log :=
    let prev := list_assoc wl reg in
    match prev with
    | None => list_assoc_set wl reg w
    | Some wil => list_assoc_set wl reg (wil ++ w)
    end.

  Definition merge_writes_single_rule (wl_acc wl_curr: write_log)
  : write_log :=
    fold_left (fun acc '(reg, x) => merge_next_write reg acc x) wl_curr wl_acc.

  (* We do not use the schedule record since we still want to use write logs at
     this point *)
  Definition merge_single_rule (racc r: rule_information_clean)
  : rule_information_clean :=
    let write0s' :=
      merge_writes_single_rule (ric_write0s racc) (ric_write0s r)
    in
    let write1s' :=
      merge_writes_single_rule (ric_write1s racc) (ric_write1s r)
    in
    let extcalls' := app (ric_extcalls racc) (ric_extcalls r) in
    {| ric_write0s := write0s'; ric_write1s := write1s';
       ric_extcalls := extcalls';
       ric_vars := List.concat [ric_vars r; ric_vars racc];
       ric_failure_cond := const_false |}.

  (* *** Merge full schedule *)
  Fixpoint write_log_to_sact (r: reg_t) (wl: list write_info) (p: Port): sact :=
    match wl with
    | [] => DRead p r
    | h::t => DIf (wcond h) (wval h) (write_log_to_sact r t p)
    end.

  Definition merge_schedule (rules_info: list rule_information_clean) nid
  (* next_ids isn't used past this point and therefore isn't returned *)
  : schedule_information * nat :=
    let (rules_info', nid) := integrate_failures rules_info nid in
    let res := fold_left
      merge_single_rule (tl rules_info')
      {| ric_write0s := []; ric_write1s := []; ric_extcalls := [];
         ric_vars := []; ric_failure_cond := const_false |}
    in ({|
      sc_write0s :=
        map (fun '(r, l) => (r, write_log_to_sact r l P0)) (ric_write0s res);
      sc_write1s :=
        map (fun '(r, l) => (r, write_log_to_sact r l P1)) (ric_write1s res);
      sc_extcalls := ric_extcalls res; sc_vars := ric_vars res |}, nid).

  (* * Final simplifications *)
  Definition is_member {A: Type} {eq_dec_A: EqDec A} (l: list A) (i: A) :=
    existsb (beq_dec i) l.

  Fixpoint app_uniq (l1 l2: list reg_t) : list reg_t :=
    match l1 with
    | [] => l2
    | h::t => if (is_member l2 h) then app_uniq t l2 else app_uniq t (h::l2)
    end.

  Fixpoint find_all_ua_regs (ua: sact) : list reg_t :=
    match ua with
    | DRead _ r => [r]
    | DIf cond tb fb =>
      app_uniq
        (find_all_ua_regs cond)
        (app_uniq (find_all_ua_regs tb) (find_all_ua_regs fb))
    | DBinop ufn a1 a2 => app_uniq (find_all_ua_regs a1) (find_all_ua_regs a2)
    | DUnop ufn a => find_all_ua_regs a
    | _ => []
    end.

  Definition find_all_wr_regs (cl: cond_log) : list reg_t :=
    fold_left
      (fun acc '(r, ua) => app_uniq [r] (app_uniq (find_all_ua_regs ua) acc))
      cl [].

  Definition find_all_extc_regs (el: extcall_log) : list reg_t :=
    fold_left
      (fun acc '(_, ei) =>
        app_uniq
          (find_all_ua_regs (econd ei))
          (app_uniq (find_all_ua_regs (earg ei)) acc))
      el [].

  Definition find_all_bind_regs (vvm: var_value_map) : list reg_t :=
    fold_left (fun acc '(_, ua) => app_uniq (find_all_ua_regs ua) acc) vvm [].

  Definition find_all_used_regs (s: schedule_information) : list reg_t :=
    app_uniq
      (app_uniq
        (find_all_wr_regs (sc_write0s s))
        (find_all_wr_regs (sc_write1s s)))
      (app_uniq
        (find_all_extc_regs (sc_extcalls s))
        (find_all_bind_regs (sc_vars s))).

  (* ** Remove read1s *)
  (* *** Replacement of variables by expression *)
  Fixpoint replace_rd1_with_var_in_sact (from: reg_t) (to ua: sact) :=
    match ua with
    | DRead p r =>
      match p with
      | P1 => if beq_dec from r then to else ua
      | _ => ua
      end
    | DIf cond tb fb =>
      DIf
        (replace_rd1_with_var_in_sact from to cond)
        (replace_rd1_with_var_in_sact from to tb)
        (replace_rd1_with_var_in_sact from to fb)
    | DBinop ufn a1 a2 =>
      DBinop
        ufn
        (replace_rd1_with_var_in_sact from to a1)
        (replace_rd1_with_var_in_sact from to a2)
    | DUnop ufn a => DUnop ufn (replace_rd1_with_var_in_sact from to a)
    | _ => ua
    end.

  Definition replace_rd1_with_var_w (w: cond_log) (from: reg_t) (to: sact)
  : cond_log :=
    map (fun '(reg, ua) => (reg, replace_rd1_with_var_in_sact from to ua)) w.

  Definition replace_rd1_with_var_extc (e: extcall_log) (from: reg_t) (to: sact)
  : extcall_log :=
    map
      (fun '(reg, ei) =>
        (reg,
          {| econd := replace_rd1_with_var_in_sact from to (econd ei);
             earg := replace_rd1_with_var_in_sact from to (earg ei);
             ebind := ebind ei |}))
      e.

  Definition replace_rd1_with_var_expr
    (v: var_value_map) (from: reg_t) (to: sact)
  : var_value_map :=
    map (fun '(reg, val) => (reg, replace_rd1_with_var_in_sact from to val)) v.

  (* Variables bound to the return values of read1s need to be replaced with the
     appropriate value. TODO store res as expr instead and change name only *)
  Definition replace_rd1_with_var
    (s: schedule_information) (from: reg_t) (to: sact)
  : schedule_information := {|
      sc_write0s := replace_rd1_with_var_w (sc_write0s s) from to;
      sc_write1s := replace_rd1_with_var_w (sc_write1s s) from to;
      sc_extcalls := replace_rd1_with_var_extc (sc_extcalls s) from to;
      sc_vars := replace_rd1_with_var_expr (sc_vars s) from to |}.

  (* *** Removal *)
  Definition get_intermediate_value (s: schedule_information) (r: reg_t)
  : sact :=
    match list_assoc (sc_write0s s) r with
    | None => DRead P0 r
    | Some v => v (* See write_log_to_sact *)
    end.

  Definition generate_intermediate_values_table
    (s: schedule_information) (regs: list reg_t) nid
  : ((list (reg_t * string)) * (list (nat * (type * sact)))) * nat :=
    let (r, nid) :=
      fold_left
        (fun '(table, vars, id) r =>
          let name := generate_binding_name (S id) in
          ((r, name)::table, (name, get_intermediate_value s r)::vars, S id))
        regs ([], [], nid)
    in (r, nid).

  Definition remove_read1s
    (s: schedule_information) (active_regs: list reg_t)
    (ivt: list (reg_t * string))
  : schedule_information :=
    fold_left
      (fun s' r =>
        match list_assoc ivt r with
        | None => s' (* Unreachable *)
        | Some v => replace_rd1_with_var s' r (DVar v)
        end)
      active_regs s.

  (* ** Remove write0s *)
  Definition get_final_value
    (s: schedule_information) (ivt: list (reg_t * string)) (r: reg_t)
  : sact :=
    match list_assoc (sc_write1s s) r with
    | None => (* Not every active reg is in write1s *)
      match list_assoc ivt r with
      | None => DRead P0 r (* Unreachable *)
      | Some v => DVar v
      end
    | Some v => v
    end.

  Definition generate_final_values_table
    (s: schedule_information) (regs: list reg_t) (ivt: list (reg_t * string)) nid
  : ((list (reg_t * string)) * (list (nat * (type * sact)))) * nat :=
      fold_left
        (fun '(fvt, fvvm, id) r =>
          let name := generate_binding_name (S id) in
          ((r, name)::fvt, (name, get_final_value s ivt r)::fvvm, S id)
        )
        regs ([], [], nid).

  Definition remove_interm (s: schedule_information) nid : simple_form * nat :=
    let active_regs := find_all_used_regs s in
    let '(ivt, ivvm, nid) := generate_intermediate_values_table s active_regs nid in
    let s' := remove_read1s s active_regs ivt in
    let '(fvt, fvvm, nid) := generate_final_values_table s' active_regs ivt nid in
    ({|
      final_values := fvt; vars := fvvm++ivvm++(sc_vars s');
      external_calls := sc_extcalls s' |}, nid).

  (* * Conversion *)
  (* Schedule can contain try or spos, but they are not used in the case we care
     about. *)
  Fixpoint schedule_to_list_of_rules (s: schedule) (rules: rule_name_t -> sact)
  : list sact :=
    match s with
    | Done => []
    | Cons r s' => (rules r)::(schedule_to_list_of_rules s' rules)
    | _ => []
    end.

  (* Precondition: only Cons and Done in schedule. *)
  (* Precondition: rules desugared. TODO desugar from here instead? *)
  Definition schedule_to_simple_form (s: schedule) (rules: rule_name_t -> sact)
  : simple_form * nat :=
    (* Get list of sact from scheduler *)
    let rules_l := schedule_to_list_of_rules s rules in
    (* Get rule_information from each rule *)
    let '(rule_info_l, nid) :=
      fold_left
        (fun '(rir_acc, nid) r =>
          let '(ri, nid) := get_rule_information r nid in
          (rir_acc++[ri], nid))
        rules_l ([], 0)
    in
    (* Detect inter-rules conflicts *)
    let rule_info_with_conflicts_l := detect_all_conflicts rule_info_l in
    (* To schedule info, merge cancel conditions with actions conditions *)
    let (schedule_info, nid) := merge_schedule rule_info_with_conflicts_l nid in
    (* To simple form *)
    remove_interm schedule_info nid.
End SimpleForm.
Close Scope nat.
