(*! Proving | Transformation of a schedule into a proof-friendly form !*)
Require Import Coq.Numbers.DecimalString Coq.Program.Equality Coq.Strings.Ascii.
Require Import Koika.Primitives Koika.Syntax.
From RecordUpdate Require Import RecordSet.
Import RecordSetNotations.
Require Import UntypedSemantics Koika.BitsToLists.
Require Import Wt.
Require Import Wellfounded.

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
  Definition var_value_map := list (nat * sact).

  Record rule_information_raw := mkRuleInformationRaw {
    rir_read0s: cond_log;
    rir_read1s: cond_log;
    rir_write0s: write_log_raw;
    rir_write1s: write_log_raw;
    rir_vars: var_value_map;
    rir_failure_cond: sact }.
  Instance etaRuleInformationRaw : Settable _ :=
    settable! mkRuleInformationRaw <
      rir_read0s; rir_read1s; rir_write0s; rir_write1s; rir_vars;
      rir_failure_cond >.
  Record rule_information_clean := mkRuleInformationClean {
    ric_write0s: write_log;
    ric_write1s: write_log;
    ric_vars: var_value_map;
    ric_failure_cond: sact }.
  Instance etaRuleInformationClean : Settable _ :=
    settable! mkRuleInformationClean
      < ric_write0s; ric_write1s; ric_vars; ric_failure_cond >.
  Record schedule_information := mkScheduleInformation {
    sc_write0s: cond_log;
    sc_write1s: cond_log;
    sc_vars: var_value_map }.
  Instance etaScheduleInformation : Settable _ :=
    settable! mkScheduleInformation
      < sc_write0s; sc_write1s; sc_vars >.
  Record simple_form := mkSimpleForm {
    final_values: list (reg_t * string);
    vars: var_value_map }.
  Instance etaSimpleForm : Settable _ :=
    settable! mkSimpleForm < final_values; vars >.

  (* * Bindings names *)

  (* * rule_information extraction *)
  (* ** Addition of a new action into an existing rule_information *)
  (* *** Merger of failure conditions *)
  Definition or_conds (conds: list sact) :=
    fold_left uor conds const_false.

  Definition merge_failures (f1 f2: sact) : sact := uor f1 f2.

  Definition build_uif (cond ua1 ua2: option sact) : option sact :=
    (* We know that the original if being valid implies that cond != None and
       ua1 = Some x iff. ua2 = Some y *)
    match cond, ua1, ua2 with
    | Some c, Some x, Some y => Some (SIf c x y)
    | _, _, _ => None
    end.


  (* *** Merger of actions *)
  (* Remove Nones from list, turn rest from (Some x) to x. *)
  Definition list_options_to_list (l: list (option sact)) : list sact :=
    filter_map id l.

  Definition merge_conds (wl: (* option *) (list write_info)) : (* option  *)sact :=
    (* match wl with *)
    (* | None => None *)
    (* | Some l =>  *)or_conds (map wcond wl)
    (* end *).

  Definition merge_failures_list (action_cond: sact) (conds: list sact)
    : (* option *) sact :=
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
     (rir <| rir_write0s :=
        list_assoc_set (rir_write0s rir) reg (new_grd, new_wi) |>,
    merge_failures_list
      grd
      (list_options_to_list ([
        option_map fst (list_assoc (rir_write0s rir) reg);
        list_assoc (rir_read1s rir) reg;
        option_map fst (list_assoc (rir_write1s rir) reg)]))).

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
     (rir <| rir_write1s :=
        list_assoc_set (rir_write1s rir) reg (new_grd, new_wi) |>,
    merge_failures_list grd (list_options_to_list [
      option_map fst (list_assoc (rir_write1s rir) reg)])).



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
          (list_assoc_set r (reg,prt) nid, list_assoc_set vvs nid (t, SIf (SVar cond_name) (SVar v1) (SVar v2)), S nid)
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

  Definition gria_list'
             (guard: sact)
             (rec: uact -> (list (string * type)) -> list (string * nat) -> list (reg_t * Port * nat) -> list(nat * (type*sact)) ->
                   sact -> rule_information_raw -> nat ->
                   (option sact * list (string * nat) * list (reg_t * Port * nat) * list (nat * (type * sact)) * sact * rule_information_raw * nat * type))
    :=
    fix gria_list'
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
          gria_list' args tsig vms reg2var
                     (list_assoc_set vvs arg_bind_name (t, reduce t vc))
                   rir (S nid) ((arg_bind_name, t) :: names0) (merge_failures failure fail0)
      end.

  (* This function extracts the actions for a given rule. It also returns the
     updated next_ids structure. *)


 
  Fixpoint get_rule_information_aux
           (* No need to pass failures as these impact the whole rule - taking note of
       all of them and factoring the conditions in is enough. Conflicts between
       different actions are also dealt with here. *)
           (* TODO improve guards management *)
           (* TODO guard could be option string instead *)
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
          get_rule_information_aux val tsig env reg2var vvs guard rir nid
        in
        let name := nid in
        let '(ret_body, vm_body, reg2var, vv_body, failures_body, rir_body, nid, tbody) :=
          get_rule_information_aux
            body
            ((var, tval)::tsig)
            ((var, name)::vm_val)
            reg2var
            (list_assoc_set vv_val name (tval, (reduce tval ret_val)))
            guard
            rir_val
            (S nid)
        in (
          ret_body, skipn 1 vm_body (* var's binding goes out of scope *),
          reg2var,
          vv_body,
          merge_failures failures_val failures_body, rir_body, nid, tbody)
    | DAssign var val =>
        let '(ret_val, vm_val, reg2var, vv_val, failures_val, rir_val, nid, t) :=
          get_rule_information_aux val tsig env reg2var vvs guard rir nid
        in
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
          get_rule_information_aux a1 tsig env reg2var vvs guard rir nid
        in
        let '(ret_a2, vm_a2, reg2var, vv_a2, failures_a2, rir_a2, nid_a2, t) :=
          get_rule_information_aux a2 tsig vm_a1 reg2var vv_a1 guard rir_a1 nid_a1
        in
        (ret_a2, vm_a2, reg2var, vv_a2, merge_failures failures_a1 failures_a2,
          rir_a2, nid_a2, t)
    | DIf cond tb fb =>
        let '(ret_cond, vm_cond, reg2var, vv_cond, failures_cond, rir_cond, nid, t) :=
          get_rule_information_aux cond tsig env reg2var vvs guard rir nid
        in
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
        (build_uif ret_cond ret_tb ret_fb,
          vm_merge,
          reg2var,
          vvs,
          (* Merging the failure conditions: looks complex because of the option
          types but really not that tricky. *)
          (* match ret_cond with *)
          (* | None => const_true (* Unreachable assuming a well-formed rule *) *)
          (* | Some x => *)
              uor failures_cond
                  (uor
                     (uand (reduce (bits_t 1) ret_cond) failures_tb)
                     (uand (unot (reduce (bits_t 1) ret_cond)) failures_fb)
                  )
          (* end *),
          rir_fb, nid, t1)
    | DUnop ufn a =>
        let '(ret_a, vm_a, reg2var, vv_a, failures_a, rir_a, nid, t) :=
          get_rule_information_aux a tsig env reg2var vvs guard rir nid
        in

        (Some (SUnop ufn (reduce t ret_a)), vm_a, reg2var, vv_a, failures_a, rir_a, nid, ret_type_unop ufn t)
    | DBinop ufn a1 a2 =>
        let '(ret_a1, vm_a1, reg2var, vvs, failures_a1, rir_a1, nid, t1) :=
          get_rule_information_aux a1 tsig env reg2var vvs guard rir nid
        in
        let '(ret_a2, vm_a2, reg2var, vvs, failures_a2, rir_a2, nid, t2) :=
          get_rule_information_aux a2 tsig vm_a1 reg2var vvs guard rir_a1 nid
        in
        (Some (SBinop ufn (reduce t1 ret_a1) (reduce t2 ret_a2)), vm_a2, reg2var, vvs,
          merge_failures failures_a1 failures_a2, rir_a2, nid, ret_type_binop ufn t1 t2)
    | DInternalCall ufn args =>
        let '(arg_names, vm_args, reg2var, vv_args, failure_args, rir_args, nid) :=
          gria_list' guard get_rule_information_aux args tsig env reg2var vvs rir nid [] const_false in
        let vm_tmp :=
          combine
            (fst (split (rev (int_argspec ufn)))) (* Names from argspec *)
            (* We know that a value is assigned to each argument in well formed
             rules *)
            (map fst arg_names)
        in
        let '(ret_ic, _, reg2var, vv_ic, failure_ic, rir_ic, nid, t) :=
          get_rule_information_aux (int_body ufn) (rev (int_argspec ufn)) vm_tmp reg2var vv_args guard rir_args nid
        in
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
          end
        in
        match list_assoc reg2var (reg, port) with
        | Some v => (Some (SVar v), env, reg2var, vvs, const_false, modified_rir, nid, R reg)
        | None => (None, env, reg2var, vvs, const_true, modified_rir, nid, R reg)
        end
    | DWrite port reg val =>
        let '(ret_val, vm_val, reg2var, vvs, failures_val, actions_val, nid, t) :=
          get_rule_information_aux val tsig env reg2var vvs guard rir nid
        in
        let '(rir_wr, failure_wr) :=
          match port with
          | P0 => add_write0 actions_val guard reg (reduce t ret_val)
          | P1 => add_write1 actions_val guard reg (reduce t ret_val)
          end
        in
        let '(reg2var, vvs, nid, t) :=
          match port with
          | P0 =>
              let v_read0 := nid in
              let v_read1 := nid + 1 in
              let nid := nid + 2 in
              let vvs := list_assoc_set vvs v_read0 (t, reduce t ret_val) in
              let vvs := list_assoc_set vvs v_read1 (t, reduce t ret_val) in
              let reg2var := list_assoc_set reg2var (reg, P0) v_read0 in
              let reg2var := list_assoc_set reg2var (reg, P1) v_read1 in
              (reg2var, vvs, nid, t)
          | P1 =>
              let v_read1 := nid in
              let nid := nid + 1 in
              let vvs := list_assoc_set vvs v_read1 (t, reduce t ret_val) in
              let reg2var := list_assoc_set reg2var (reg, P1) v_read1 in
              (reg2var, vvs, nid, t)
          end in
        (None, vm_val, reg2var, vvs, merge_failures failures_val failure_wr, rir_wr,
          nid, bits_t 0)
    | DExternalCall ufn arg =>
        let '(ret_arg, vm_arg, reg2var, vv_arg, failures_arg, rir, nid, t) :=
          get_rule_information_aux arg tsig env reg2var vvs guard rir nid
        in
        let name := nid in
        (* let new_rir := add_extcall rir guard ufn (reduce ret_arg) name in *)
        (Some (SVar name), vm_arg, reg2var,
          list_assoc_set vv_arg name (retSig (Sigma ufn), SExternalCall ufn (reduce t ret_arg)),
          failures_arg, rir,
          S nid, retSig (Sigma ufn))
    | DError _ => (None, env, reg2var, vvs, const_true, rir, nid, bits_t 0)
    | DFail tau => (None, env, reg2var, vvs, const_true, rir, nid, tau)
    | @DConst _ _ _ _ _ tau c => (Some (SConst (BitsToLists.val_of_value c)), env, reg2var, vvs, const_false, rir, nid, tau)
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

  Inductive wf_sact_known_vars: list string -> uact -> Prop :=
  | wf_sact_known_vars_error l e: wf_sact_known_vars l (DError e)
  | wf_sact_known_vars_fail l e: wf_sact_known_vars l (DFail e)
  | wf_sact_known_vars_var l v: In v l -> wf_sact_known_vars l (DVar v)
  | wf_sact_known_vars_const l tau (c: type_denote tau): wf_sact_known_vars l (DConst c)
  | wf_sact_known_vars_assign l v a:
    wf_sact_known_vars l a ->
    In v l ->
    wf_sact_known_vars l (DAssign v a)
  | wf_sact_known_vars_seq l a1 a2:
    wf_sact_known_vars l a1 ->
    wf_sact_known_vars l a2 ->
    wf_sact_known_vars l (DSeq a1 a2)
  | wf_sact_known_vars_bind l v a body :
    wf_sact_known_vars l a ->
    wf_sact_known_vars (v::l) body ->
    wf_sact_known_vars l (DBind v a body)
  | wf_sact_known_vars_if l c t f :
    wf_sact_known_vars l c ->
    wf_sact_known_vars l t ->
    wf_sact_known_vars l f ->
    wf_sact_known_vars l (DIf c t f)
  | wf_sact_known_vars_read l p i:
    wf_sact_known_vars l (DRead p i)
  | wf_sact_known_vars_write l p i a:
    wf_sact_known_vars l a ->
    wf_sact_known_vars l (DWrite p i a)
  | wf_sact_known_vars_unop l ufn a:
    wf_sact_known_vars l a ->
    wf_sact_known_vars l (DUnop ufn a)
  | wf_sact_known_vars_binop l ufn a1 a2:
    wf_sact_known_vars l a1 ->
    wf_sact_known_vars l a2 ->
    wf_sact_known_vars l (DBinop ufn a1 a2)
  | wf_sact_known_vars_ext l ufn a:
    wf_sact_known_vars l a ->
    wf_sact_known_vars l (DExternalCall ufn a)
  | wf_sact_known_vars_int l ufn a:
    Forall (wf_sact_known_vars l) a ->
    List.length (map fst (int_argspec ufn)) = List.length a ->
    wf_sact_known_vars (map fst (int_argspec ufn)) (int_body ufn) ->
    wf_sact_known_vars l (DInternalCall ufn a)
  | wf_sact_known_vars_pos l p a:
    wf_sact_known_vars l a ->
    wf_sact_known_vars l (DAPos p a).

  Lemma same_env_set_in:
    forall env' env
           (SAMEENV: Forall2 (fun x y : string * nat => fst x = fst y) env env')
           v n
           (VARIN: In v (map fst env)) ,
      Forall2 (fun x y : string * nat => fst x = fst y) env (list_assoc_set env' v n).
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
    forall {P: Type} (R: P -> P -> Prop) (Rtrans: forall x y z, R x y -> R y z -> R x z)
           l1 l2,
      Forall2 R l1 l2 -> forall l3, Forall2 R l2 l3 -> Forall2 R l1 l3.
  Proof.
    induction 2; simpl; intros; eauto. inv H1; constructor; eauto.
  Qed.

  Lemma same_env_refl:
    forall (l: list (string * nat)),
      Forall2 (fun x y => fst x = fst y) l l.
  Proof.
    induction l; simpl; intros; eauto.
  Qed.

  Lemma same_env_sym:
    forall (l1 l2: list (string * nat)),
      Forall2 (fun x y => fst x = fst y) l1 l2 ->
      Forall2 (fun x y => fst x = fst y) l2 l1.
  Proof.
    induction 1; simpl; intros; eauto.
  Qed.

  Lemma same_env_same_fst:
    forall (l1 l2: list (string * nat)),
      Forall2 (fun x y => fst x = fst y) l1 l2 ->
      map fst l1 = map fst l2.
  Proof.
    induction 1; simpl; intros; eauto. congruence.
  Qed.

  Lemma merge_vms_preserve_same_env:
    forall (l2 l4: list (string*nat))
           (F: Forall2 (fun x y => fst x = fst y) l2 l4)
           (l3: list (nat*(type*sact))) cname n1 env' vvs n2,
      merge_branches l2 l4 l3 n1 cname = (env', vvs, n2) ->
      Forall2 (fun x y => fst x = fst y) l2 env'.
  Proof.
    induction 1; simpl; intros; eauto.
    - inv H. constructor.
    - do 4 destr_in H0. apply IHF in Heqp1.
      destr_in H0. inv H0. constructor; auto.
      inv H0. constructor; auto.
  Qed.

  Lemma gria_list_same_env:
    forall
      args env
      (F: Forall (wf_sact_known_vars (map fst env)) args)
      (IH: Forall
             (fun u : uact =>
                forall (env : list (string * nat)) tsig reg2var (guard : sact)
                       (rir : rule_information_raw) (nid : nat) 
                       (v : option sact) (env' : list (string * nat)) reg2var'
                       (vvs : list (nat * (type*sact))) (fail_cond : sact)
                       (rir' : rule_information_raw) (nid' : nat)
                       (vvs0 : list (nat * (type*sact))) t,
                  wf_sact_known_vars (map fst env) u ->
                  get_rule_information_aux u tsig env reg2var vvs0 guard rir nid =
                    (v, env', reg2var', vvs, fail_cond, rir', nid', t) ->
                  Forall2 (fun x y : string * nat => fst x = fst y) env env') args
      )
      tsig names0 vvs0 fail0 rir nid l0 env' l u r n guard reg2var reg2var' ,
      gria_list' guard get_rule_information_aux args tsig env reg2var vvs0 rir nid names0 fail0 =
        (l0, env', reg2var', l, u, r, n) ->
      Forall2 (fun x y => fst x = fst y) env env' /\ List.length l0 = List.length names0 + List.length args.
  Proof.
    induction args; simpl; intros; eauto.
    - inv H. split. apply same_env_refl. lia.
    - repeat destr_in H. subst. inv IH. inv F.
      eapply H2 in Heqp; eauto. clear H2.
      eapply IHargs in H; eauto.
      destruct H.
      split.
      eapply same_env_trans; eauto. congruence.
      simpl in H0. lia.
      erewrite <- same_env_same_fst; eauto.
  Qed.

  Lemma map_fst_combine:
    forall {A B: Type} (l1: list A) (l2: list B),
      List.length l1 = List.length l2 ->
      map fst (combine l1 l2) = l1.
  Proof.
    induction l1; simpl; intros; eauto. destr. simpl in *; lia. simpl in *.
    f_equal. eauto.
  Qed.

  Lemma fst_split_map:
    forall {A B: Type} (l: list (A*B)),
      fst (split l) = map fst l.
  Proof.
    induction l; simpl; intros; eauto. repeat destr. subst. simpl. f_equal.
    simpl in IHl. auto.
  Qed.

  Lemma wf_sact_known_vars_incl:
    forall s l
           (WF1: wf_sact_known_vars l s)
           l' (INCL: incl l l') ,
      wf_sact_known_vars l' s.
  Proof.
    intros s. unfold uact in s. pattern s.
    induction s using daction_ind'; simpl; intros;  inv WF1; try now (econstructor; eauto).
    - econstructor; eauto. eapply IHs2; eauto.
      red; simpl; intuition.
    - econstructor; eauto.
      revert INCL H2 H.
      clear. revert args l l'.
      induction args; simpl; intros; eauto.
      inv H. inv H2. constructor; eauto.
  Qed.

  (* Lemma get_rule_information_aux_same_vm: *)
  (*   forall (ua: uact) *)
  (*          (env: list (string * nat)) tsig reg2var (guard: sact) *)
  (*          (rir: rule_information_raw) (nid: nat) *)
  (*          v env' reg2var' vvs fail_cond rir' nid' vvs0 t *)
  (*          (WUKV: wf_sact_known_vars (map fst env) ua) *)
  (*          (GRIA: get_rule_information_aux ua tsig env reg2var vvs0 guard rir nid = (v, env', reg2var', vvs, fail_cond, rir', nid', t)) *)
  (*   , *)
  (*     Forall2 (fun x y => fst x = fst y) env env'. *)
  (* Proof. *)
  (*   Opaque skipn. *)
  (*   intros ua; pattern ua; eapply daction_ind'; simpl; intros; eauto. *)
  (*   all: try now (repeat destr_in GRIA; inv GRIA; inv WUKV; eauto using same_env_refl). *)
  (*   - repeat destr_in GRIA; inv GRIA; inv WUKV; eauto. *)
  (*     apply H in Heqp; auto. *)
  (*     eapply same_env_set_in; eauto. *)
  (*   - repeat destr_in GRIA; inv GRIA; inv WUKV; eauto. *)
  (*     apply H in Heqp; auto. *)
  (*     apply H0 in Heqp6; auto. *)
  (*     eapply same_env_trans; eauto. congruence. *)
  (*     erewrite <- same_env_same_fst; eauto. *)
  (*   - repeat destr_in GRIA. inv GRIA. *)
  (*     apply H in Heqp; auto. *)
  (*     apply H0 in Heqp6; auto. *)
  (*     inv Heqp6. change (skipn 1 (y :: l')) with l'. *)
  (*     eapply same_env_trans; eauto. congruence. *)
  (*     inv WUKV. simpl; auto. eapply wf_sact_known_vars_incl. eauto. red; simpl; intuition. *)
  (*     erewrite <- same_env_same_fst; eauto. *)
  (*     inv WUKV. auto. *)
  (*   - repeat (destr_in GRIA; [idtac]). inv GRIA; inv WUKV; eauto. *)
  (*     apply H in Heqp; auto. *)
  (*     apply H0 in Heqp6; auto. *)
  (*     apply H1 in Heqp13; auto. *)
  (*     eapply merge_vms_preserve_same_env in Heqp20. *)
  (*     eapply same_env_trans; eauto. congruence. *)
  (*     eapply same_env_trans. congruence. apply Heqp6. auto. *)
  (*     eapply same_env_trans. congruence. apply same_env_sym. eauto. auto. *)
  (*     erewrite <- same_env_same_fst; eauto. *)
  (*     erewrite <- same_env_same_fst; eauto. *)
  (*   - repeat destr_in GRIA. inv GRIA. inv WUKV. *)
  (*     apply H in Heqp; auto. *)
  (*     apply H0 in Heqp6; auto. *)
  (*     eapply same_env_trans; eauto. congruence. *)
  (*     erewrite <- same_env_same_fst; eauto. *)
  (*   - repeat destr_in GRIA. inv GRIA. inv WUKV. *)
  (*     eapply gria_list_same_env in Heqp; eauto. *)
  (*     destruct Heqp; eauto. *)
  (* Qed. *)


  Definition valid_name name nid :=
    name < nid.
  Definition vvs_range (vvs: list (nat * (type * sact))) (nid: nat) :=
    forall x y,
      list_assoc vvs x = Some y -> valid_name x nid.


  Lemma vvs_range_in_fst:
    forall vvs n,
    vvs_range vvs n ->
    forall k v,
      list_assoc vvs k = Some v ->
      k < n.
  Proof.
    unfold vvs_range. intros.
    apply H in H0. eauto.
  Qed.

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

  Lemma valid_name_incr:
    forall name n1 n2 (INCR: n1 <= n2),
      valid_name name n1 -> valid_name name n2.
  Proof.
    unfold valid_name. intros; lia.
  Qed.

  Lemma vvs_range_incr:
    forall vvs n1 n2 (INCR: n1 <= n2),
      vvs_range vvs n1 -> vvs_range vvs n2.
  Proof.
    unfold vvs_range; simpl; intros; eauto using valid_name_incr.
  Qed.

  Ltac trim H :=
    match type of H with
    | ?a -> ?b =>
      let x := fresh "H" in
      assert(x: a);[|specialize(H x); clear x]
    end.

  Lemma in_map_list_assoc_set_inv:
    forall {K V: Type} {eqdec: EqDec K} (l : list (K * V)) (k : K)
           (v : V) k' ,
      In k' (map fst (list_assoc_set l k v)) ->
      k = k' \/ In k' (map fst l).
  Proof.
    induction l; simpl; intros; eauto. repeat destr_in H. subst. simpl. auto.
    simpl in *. destruct H; auto. apply IHl in H. tauto.
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


  Lemma vvs_range_none:
    forall l n name,
      vvs_range l n ->
      ~ valid_name name n ->
      list_assoc l name = None.
  Proof.
    unfold vvs_range; intros.
    destruct (list_assoc l name) eqn:?; eauto. eapply H in Heqo; eauto. congruence.
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

  Lemma env_vvs_set:
    forall env vvs tsig,
      env_vvs env vvs tsig ->
      forall  v n t a,
        list_assoc tsig v = Some t ->
        vvs_range vvs n ->
        (* (forall x n0, In (x,n0) env -> n0 < n) -> *)
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


  Lemma merge_branches_grows:
    forall vm_tb vm_fb vvs nid cond_name vm' vvs' nid' tsig
           (MB: merge_branches vm_tb vm_fb vvs nid cond_name = (vm', vvs', nid'))
           (ENVVVS1: env_vvs vm_tb vvs tsig)
           (ENVVVS2: env_vvs vm_fb vvs tsig)
           (RNGVVS: vvs_range vvs nid)
           (VVSVALID: vvs_smaller_variables vvs)
           (VALIDCOND: valid_name cond_name nid)
           (WTCOND: wt_sact vvs (SVar cond_name) (bits_t 1))
           (WTVVS: wt_vvs vvs)
    ,
      vvs_grows vvs vvs'
      /\ vvs_range vvs' nid'
      /\ env_vvs vm' vvs' tsig
      /\ nid <= nid'
      /\ vvs_smaller_variables vvs'
      /\ wt_vvs vvs'.
  Proof.
    induction vm_tb; simpl; intros; eauto.
    - inv MB. split; eauto using vvs_grows_refl.
    - repeat destr_in MB; inv MB. now auto.
      + inv ENVVVS1. inv ENVVVS2. destruct y.
        destruct H1 as ( ? & ? & GET1).
        destruct H4 as ( ? & ? & GET2). subst.
        edestruct IHvm_tb as (VVSGROWS3 & VVSRANGE3 & ENVVVS3 & NIDGROWS3 & VVSVALID3 & WTVVS3); eauto.
        repeat split; auto.
        constructor; eauto.
      + inv ENVVVS1. inv ENVVVS2. destruct y.
        destruct H1 as ( ? & ? & GET1).
        destruct H4 as ( ? & ? & GET2). subst.
        edestruct IHvm_tb as (VVSGROWS3 & VVSRANGE3 & ENVVVS3 & NIDGROWS3 & VVSVALID3 & WTVVS3); eauto.
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
      /\ wt_vvs vvs'.
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
    - repeat refine (conj _ _); eauto using vvs_grows_refl.
      + red; intros. rewrite list_assoc_gso; eauto.
        intro; subst. eapply RNGVVS in H.  red in H.  lia.
      + eapply vvs_range_list_assoc_set; eauto.
        eapply vvs_range_incr. 2: eauto. lia.
        red; lia.
      +
        edestruct (ENVVVS1) as (z & IN & ? & IN2).
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
    - edestruct ENVVVS1 as (? & ? & ? & ?); eauto.
      setoid_rewrite Heqo in H. congruence.
    - repeat split; eauto using vvs_grows_refl.
      edestruct (ENVVVS2 (reg,prt)) as (? & ? & ? & ? ). setoid_rewrite Heqo0 in H. congruence.
    - repeat split; eauto using vvs_grows_refl.
      edestruct (ENVVVS1 (reg,prt)) as (? & ? & ? & ? ). setoid_rewrite Heqo in H. congruence.
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
      /\ wt_vvs vvs'.
  Proof.
    induction ks; simpl; intros; eauto.
    - inv MB. repeat split; eauto using vvs_grows_refl. apply incl_refl.
    - repeat destr_in MB; inv MB.
      edestruct merge_reg2var_reg_grows as (VG1 & VR1 & EX1 & INCL1 & LT1 & VSV1 & WT1); eauto.
      edestruct IHks as (VG2 & VR2 & EX2 & INCL2 & LT2 & VSV2 & WT2); eauto using reg2var_vvs_grows.
      red in VALIDCOND; red; lia.
      eapply wt_sact_vvs_grows; eauto.
      repeat refine (conj _ _); eauto using vvs_grows_trans. 2: lia.
      red; intros. eapply INCL2. simpl in H. destruct H; auto.
      subst. apply in_app_iff. right. eapply INCL1; simpl; eauto.
      rewrite in_app_iff in H.
      rewrite in_app_iff. destruct H; auto. right.
      eapply INCL1; simpl; eauto.
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
      /\ wt_vvs vvs'.
  Proof.
    unfold merge_reg2vars. simpl; intros.
    edestruct merge_reg2var_aux_grows as (VG & VR & R2V1 & R2V2 & NG & VSV & WTVVS); eauto.
    simpl; easy. repeat split; eauto.
    rewrite app_nil_r in R2V2.
    red; intros.
    edestruct ENVVVS1 as (? & GET1 & ? & GET2).
    apply list_assoc_in_keys in GET1. apply R2V2 in GET1.
    destruct (list_assoc r2v' x) eqn:?.
    2:{
      apply list_assoc_none_unknown_key in Heqo. contradict Heqo. apply GET1.
    }
    eexists; split; eauto.
  Qed.

  Definition valid_vars_sact v n :=
    forall var, var_in_sact v var -> var_lt var n.

  Lemma valid_vars_merge_failures:
    forall u u0 n,
      valid_vars_sact u n ->
      valid_vars_sact u0 n ->
      valid_vars_sact (merge_failures u u0) n.
  Proof.
    red; intros. inv H1; eauto.
  Qed.

  Lemma valid_vars_and:
    forall u u0 n,
      valid_vars_sact u n ->
      valid_vars_sact u0 n ->
      valid_vars_sact (uand u u0) n.
  Proof.
    red; intros. inv H1; eauto.
  Qed.

  Lemma valid_vars_not:
    forall u n,
      valid_vars_sact u n ->
      valid_vars_sact (unot u) n.
  Proof.
    red; intros. inv H0; eauto.
  Qed.

  Lemma valid_vars_fold_uor:
    forall conds n,
      Forall (fun a => valid_vars_sact a n) conds ->
      forall ci,
        valid_vars_sact ci n ->
        valid_vars_sact (fold_left uor conds ci) n.
  Proof.
    induction 1; simpl; intros; eauto.
    apply IHForall. apply valid_vars_merge_failures; auto.
  Qed.

  Lemma valid_vars_or_conds:
    forall conds n,
      Forall (fun a => valid_vars_sact a n) conds ->
      valid_vars_sact (or_conds conds) n.
  Proof.
    intros; eapply valid_vars_fold_uor; eauto.
    red; intros. inv H0.
  Qed.

  Lemma valid_var_sact_incr:
    forall v n1 n2,
      valid_vars_sact v n1 ->
      n1 <= n2 ->
      valid_vars_sact v n2.
  Proof.
    red; intros.
    eapply H in H1. eapply var_lt_gen_r; eauto.
  Qed.




  Record wf_write_log_raw (wl: write_log_raw) (n: nat) :=
    {
      wf_wlr_glob_cond: forall i a, In (i, a) wl -> valid_vars_sact (fst a) n ;
      wf_wlr_each_cond: forall i a, In (i, a) wl ->
                                    Forall (fun wi => valid_vars_sact (wcond wi) n) (snd a);
      wf_wlr_each_act: forall i a, In (i, a) wl ->
                                   Forall (fun wi => valid_vars_sact (wval wi) n) (snd a);
    }.

  Record wf_rir (r: rule_information_raw) (n: nat) :=
    {
      wf_rir_read0s: forall i a, In (i, a) (rir_read0s r) -> valid_vars_sact a n;
      wf_rir_read1s: forall i a, In (i, a) (rir_read1s r) -> valid_vars_sact a n;
      wf_rir_write0s: wf_write_log_raw (rir_write0s r) n;
      wf_rir_write1s: wf_write_log_raw (rir_write1s r) n;
    }.

  Lemma wf_write_log_raw_incr:
    forall r n1 n2,
      wf_write_log_raw r n1 ->
      n1 <= n2 ->
      wf_write_log_raw r n2.
  Proof.
    intros. inv H. split; eauto using valid_var_sact_incr.
    intros. apply wf_wlr_each_cond0 in H. eapply Forall_impl; eauto. simpl; eauto using valid_var_sact_incr.
    intros. apply wf_wlr_each_act0 in H. eapply Forall_impl; eauto. simpl; eauto using valid_var_sact_incr.
  Qed.

  Lemma wf_rir_incr:
    forall r n1 n2,
      wf_rir r n1 ->
      n1 <= n2 ->
      wf_rir r n2.
  Proof.
    intros. inv H. split; eauto using valid_var_sact_incr, wf_write_log_raw_incr.
  Qed.

  Lemma vss_or_extcall_var_lt:
    forall l n
           (VVSRANGE : vvs_range l n)
           v' z
           (H0 : list_assoc l v' = Some z),
      var_lt v' n.
  Proof.
    intros. eapply VVSRANGE in H0. red in H0; red; lia.
  Qed.


  Lemma wf_rir_add_write0:
    forall rir n guard v idx rir' fail,
      wf_rir rir n ->
      valid_vars_sact guard n ->
      valid_vars_sact v n ->
      add_write0 rir guard idx v = (rir', fail) ->
      wf_rir rir' n /\ valid_vars_sact fail n.
  Proof.
    intros. inv H. unfold add_write0 in H2.
    repeat destr_in H2. inv H2.
    split. repeat (split; simpl; eauto).
    - intros i a IN.
      apply in_list_assoc_set_inv in IN. destruct IN; eauto.
      inv H. simpl. destr_in Heqp; inv Heqp; eauto.
      apply list_assoc_in in Heqo.
      destruct p; simpl in *. apply valid_vars_merge_failures; eauto.
      inv wf_rir_write0s0. eapply wf_wlr_glob_cond0 in Heqo; eauto.
      eapply wf_wlr_glob_cond in H; eauto.
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
    - apply valid_vars_and. auto.
      apply valid_vars_or_conds.
      apply Forall_list_options. simpl. intros. subst. unfold option_map in H.
      destruct H as [H|[H|[H|[]]]]; repeat destr_in H; inv H.
      + destruct p. apply list_assoc_in in Heqo.
        eapply wf_wlr_glob_cond in Heqo; eauto.
      + apply list_assoc_in in H3.
        eapply wf_rir_read1s0 in H3. auto.
      + destruct p. apply list_assoc_in in Heqo.
        eapply wf_wlr_glob_cond in Heqo; eauto.
  Qed.

  Lemma wf_rir_add_write1:
    forall rir n guard v idx rir' fail,
      wf_rir rir n ->
      valid_vars_sact guard n ->
      valid_vars_sact v n ->
      add_write1 rir guard idx v = (rir', fail) ->
      wf_rir rir' n /\ valid_vars_sact fail n.
  Proof.
    intros. inv H. unfold add_write1 in H2.
    repeat destr_in H2. inv H2.
    split. repeat (split; simpl; eauto).
    - intros i a IN.
      apply in_list_assoc_set_inv in IN. destruct IN; eauto.
      inv H. simpl. destr_in Heqp; inv Heqp; eauto.
      apply list_assoc_in in Heqo.
      destruct p; simpl in *. apply valid_vars_merge_failures; eauto.
      inv wf_rir_write1s0. eapply wf_wlr_glob_cond0 in Heqo; eauto.
      eapply wf_wlr_glob_cond in H; eauto.
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
    - apply valid_vars_and. auto.
      apply valid_vars_or_conds.
      apply Forall_list_options. simpl. intros. subst. unfold option_map in H.
      destruct H as [H|[]]; repeat destr_in H; inv H.
      destruct p. apply list_assoc_in in Heqo.
      eapply wf_wlr_glob_cond in Heqo; eauto.
  Qed.

  Lemma wf_rir_add_read0:
    forall rir n guard idx,
      wf_rir rir n ->
      valid_vars_sact guard n ->
      wf_rir (add_read0 rir guard idx) n.
  Proof.
    intros. inv H. unfold add_read0. split; simpl; eauto.
    intros.
    apply in_list_assoc_set_inv in H. destruct H.
    - inv H. destr; eauto.
      apply valid_vars_merge_failures; auto.
      apply list_assoc_in in Heqo. eauto.
    - eauto.
  Qed.
  Lemma wf_rir_add_read1:
    forall rir n guard idx,
      wf_rir rir n ->
      valid_vars_sact guard n ->
      wf_rir (add_read1 rir guard idx) n.
  Proof.
    intros. inv H. unfold add_read1. split; simpl; eauto.
    intros.
    apply in_list_assoc_set_inv in H. destruct H.
    - inv H. destr; eauto.
      apply valid_vars_merge_failures; auto.
      apply list_assoc_in in Heqo. eauto.
    - eauto.
  Qed.

(* Goal forall P r, let res := get_rule_information_aux *)
(*                               (DSeq (DWrite P1 r const_false) (DWrite P0 r const_false)) *)
(*                               [] [] const_true *)
(*                    {| rir_read0s := []; rir_read1s := []; rir_write0s := []; *)
(*            rir_write1s := []; rir_extcalls := []; rir_vars := []; *)
(*                                                   rir_failure_cond := const_false |} 0 in *)
(*                P res. *)
(*   simpl. intros. *)
(*   unfold set. simpl. *)
(*   unfold list_options_to_list. simpl. unfold merge_failures_list. unfold or_conds, id. simpl. *)
(*   rewrite eq_dec_refl. simpl. *)

  Definition write_log_raw_grows (wl1 wl2: write_log_raw) :=
    forall idx gcond wil,
      list_assoc wl1 idx = Some (gcond, wil) ->
      exists gcond' wil' ,
        list_assoc wl2 idx = Some (gcond', wil') /\ incl wil wil'.


  Definition bool_sact_grows vvs1 c1 vvs2 c2 : Prop :=
      interp_sact vvs1 c1 (Bits 1 [true]) ->
      interp_sact vvs2 c2 (Bits 1 [true]).

  Definition cond_log_grows vvs1 (cl1: cond_log) vvs2 cl2 :=
    forall idx c,
      list_assoc cl1 idx = Some c ->
      exists c' ,
        list_assoc cl2 idx = Some c' /\ bool_sact_grows vvs1 c vvs2 c'.


  Record rir_grows vvs1 r1 vvs2 r2 : Prop :=
    {
      rir_grows_read0s: cond_log_grows vvs1 (rir_read0s r1) vvs2 (rir_read0s r2);
      rir_grows_read1s: cond_log_grows vvs1 (rir_read1s r1) vvs2 (rir_read1s r2);
      rir_grows_write0s: write_log_raw_grows (rir_write0s r1) (rir_write0s r2);
      rir_grows_write1s: write_log_raw_grows (rir_write1s r1) (rir_write1s r2);
      rir_vvs_grows: vvs_grows vvs1 vvs2;
    }.


  Lemma rir_grows_interp_sact:
        forall r1 v1 r2 v2 a v,
          rir_grows v1 r1 v2 r2 ->
          interp_sact v1 a v ->
          interp_sact v2 a v.
  Proof.
    inversion 1; eapply vvs_grows_interp_sact; eauto.
  Qed.


  Lemma write_log_raw_grows_refl: forall wl, write_log_raw_grows wl wl.
  Proof.
    red; intros; eauto using incl_refl.
  Qed.

  Lemma bool_sact_grows_refl: forall vvs c, bool_sact_grows vvs c vvs c.
  Proof.
    red; intros; eauto.
  Qed.

  Lemma cond_log_grows_refl: forall vvs cl, cond_log_grows vvs cl vvs cl.
  Proof.
    red; intros; eauto using bool_sact_grows_refl.
  Qed.

  Lemma rir_grows_refl: forall vvs r, rir_grows vvs r vvs r.
  Proof.
    split; eauto using incl_refl, write_log_raw_grows_refl, cond_log_grows_refl, vvs_grows_refl.
  Qed.


  Lemma write_log_raw_grows_trans:
    forall wl1 wl2,
      write_log_raw_grows wl1 wl2 ->
      forall wl3,
        write_log_raw_grows wl2 wl3 ->
        write_log_raw_grows wl1 wl3.
  Proof.
    red; intros.
    edestruct (H idx) as (g1 & wil1 & LA1 & INCL1); eauto.
    edestruct (H0 idx) as (g2 & wil2 & LA2 & INCL2); eauto.
    eauto using incl_tran.
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
    forall vvs1 cl1 vvs2 cl2,
      cond_log_grows vvs1 cl1 vvs2 cl2 ->
      forall vvs3 cl3,
        cond_log_grows vvs2 cl2 vvs3 cl3 ->
        cond_log_grows vvs1 cl1 vvs3 cl3.
  Proof.
    red; intros.
    edestruct (H idx) as (c1 & LA1 & INCL1); eauto.
    edestruct (H0 idx) as (c2 & LA2 & INCL2); eauto.
    eauto using bool_sact_grows_trans.
  Qed.

  Lemma rir_grows_trans:
    forall vvs1 r1 vvs2 r2,
      rir_grows vvs1 r1 vvs2 r2 ->
      forall vvs3 r3,
        rir_grows vvs2 r2 vvs3 r3 ->
        rir_grows vvs1 r1 vvs3 r3.
  Proof.
    intros. inv H; inv H0.
    split; eauto using incl_tran, write_log_raw_grows_trans, cond_log_grows_trans, vvs_grows_trans.
  Qed.

  Lemma rir_grows_add_read0:
    forall vvs rir grd idx b,
      interp_sact vvs grd (Bits 1 [b]) ->
      rir_grows vvs rir vvs (add_read0 rir grd idx).
  Proof.
    unfold add_read0. intros.
    split; simpl; eauto using incl_refl, write_log_raw_grows_refl, cond_log_grows_refl, vvs_grows_refl.
    red; intros.
    destruct (eq_dec idx idx0); subst.
    + rewrite H0.
      rewrite list_assoc_gss. eexists; split; eauto.
      red; intros.
      econstructor; eauto.
    + rewrite list_assoc_gso; eauto. eexists; split; eauto.
      red; intros. auto.
  Qed.

  Lemma rir_grows_add_read1:
    forall vvs rir grd idx b,
      interp_sact vvs grd (Bits 1 [b]) ->
      rir_grows vvs rir vvs (add_read1 rir grd idx).
  Proof.
    unfold add_read1. intros.
    split; simpl; eauto using incl_refl, write_log_raw_grows_refl, cond_log_grows_refl, vvs_grows_refl.
    - red; intros.
      destruct (eq_dec idx idx0); subst.
      + rewrite H0.
        rewrite list_assoc_gss. eexists; split; eauto.
        red; intros.
        econstructor; eauto.
      + rewrite list_assoc_gso; eauto. eexists; split; eauto.
        red; intros. auto.
  Qed.

  Lemma valid_name_gen:
    forall n nid,
      valid_name n nid <-> n < nid.
  Proof.
    intros n nid. unfold valid_name. tauto.
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


  Lemma rir_grows_change_vvs:
    forall vvs1 vvs2 rir n,
      vvs_range vvs1 n ->
      (forall x,
          valid_name x n ->
          forall y,
            list_assoc vvs1 x = Some y -> list_assoc vvs2 x = Some y) ->
      rir_grows vvs1 rir vvs2 rir.
  Proof.
    intros. split; eauto using write_log_raw_grows_refl, incl_refl.
    - red; intros. eexists; split; eauto.
      red; intros. eapply interp_sact_change_vvs; eauto.
    - red; intros. eexists; split; eauto.
      red; intros. eapply interp_sact_change_vvs; eauto.
    - red; intros; eapply H0; eauto.
  Qed.

  Lemma rir_grows_set:
    forall vvs rir name n v,
      vvs_range vvs n ->
      ~ valid_name name n ->
      rir_grows vvs rir (list_assoc_set vvs name v) rir.
  Proof.
    intros; eapply rir_grows_change_vvs; eauto.
    intros; rewrite list_assoc_gso; eauto. congruence.
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
      (fun s1 s2 => 
           s1 < s2
      )
      (fun s s1 s2 => size_sact s1 < size_sact s2).

  Lemma wf_order_sact:
    well_founded (order_sact).
  Proof.
    apply wf_lexprod.
    - apply lt_wf.
    - intros. apply wf_inverse_image. apply lt_wf.
  Qed.


  Lemma wt_sact_interp:
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


  Lemma rir_grows_add_write0:
    forall vvs rir grd idx v rir' grd' ,
      wt_sact vvs grd (bits_t 1) ->
      add_write0 rir grd idx v = (rir', grd') ->
      rir_grows vvs rir vvs rir'.
  Proof.
    unfold add_write0. intros.
    destr_in H0. inv H0.
    split; simpl; eauto using incl_refl, write_log_raw_grows_refl, cond_log_grows_refl, vvs_grows_refl.
    - red; intros.
      rewrite list_assoc_spec. destr. subst.
      + do 2 eexists; split; eauto.
        rewrite H0 in Heqp. inv Heqp. apply incl_appl, incl_refl.
      + rewrite H0. do 2 eexists; split; eauto.
        apply incl_refl.
  Qed.
  Lemma rir_grows_add_write1:
    forall vvs rir grd idx v rir' grd' ,
      wt_sact vvs grd (bits_t 1) ->
      add_write1 rir grd idx v = (rir', grd') ->
      rir_grows vvs rir vvs rir'.
  Proof.
    unfold add_write1. intros.
    destr_in H0. inv H0.
    split; simpl; eauto using incl_refl, write_log_raw_grows_refl, cond_log_grows_refl, vvs_grows_refl.
    - red; intros.
      rewrite list_assoc_spec. destr. subst.
      + do 2 eexists; split; eauto.
        rewrite H0 in Heqp. inv Heqp. apply incl_appl, incl_refl.
      + rewrite H0. do 2 eexists; split; eauto.
        apply incl_refl.
  Qed.
 
  Lemma gria_list_grows:
    forall
      (I: list (string * nat) -> list (reg_t * Port * nat) -> list (nat * (type * sact)) -> nat -> rule_information_raw -> sact -> Prop)
      (P: list (string * nat) -> list (reg_t * Port * nat) -> list (nat * (type * sact)) -> nat -> rule_information_raw ->
          list (string * nat) -> list (reg_t * Port * nat) -> list (nat * (type * sact)) -> nat -> rule_information_raw -> Prop)
      (Prefl: forall env r2v vvs nid rir, P env r2v vvs nid rir env r2v vvs nid rir)
      (Ptrans: forall env1 r2v1 vvs1 nid1 rir1 env2 r2v2 vvs2 nid2 rir2 env3 r2v3 vvs3 nid3 rir3 grd1 grd2,
          I env1 r2v1 vvs1 nid1 rir1 grd1 ->
          P env1 r2v1 vvs1 nid1 rir1 env2 r2v2 vvs2 nid2 rir2 ->
          I env2 r2v2 vvs2 nid2 rir2 grd2 ->
          P env2 r2v2 vvs2 nid2 rir2 env3 r2v3 vvs3 nid3 rir3 ->
          P env1 r2v1 vvs1 nid1 rir1 env3 r2v3 vvs3 nid3 rir3
      )
      (* (Pwukv: *)
      (*   forall env1 r2v1 vvs1 nid1 rir1 env2 r2v2 vvs2 nid2 rir2, *)
      (*     P env1 r2v1 vvs1 nid1 rir1 env2 r2v2 vvs2 nid2 rir2 -> *)
      (*     forall u, *)
      (*       wf_sact_known_vars (map fst env1) u -> *)
      (*       wf_sact_known_vars (map fst env2) u *)
      (* ) *)
      (Psetvvs:
        forall env r2v vvs n rir grd v t,
          I env r2v vvs n rir grd ->
          valid_vars_sact v n ->
          wt_sact vvs v t ->
          P env r2v vvs n rir env r2v (list_assoc_set vvs n (t, v)) (S n) rir
          /\ I env r2v (list_assoc_set vvs n (t, v)) (S n) rir grd
      )
      (Pvvsgrows:
        forall env1 r2v1 vvs1 nid1 rir1 grd1 env2 r2v2 vvs2 nid2 rir2,
          P env1 r2v1 vvs1 nid1 rir1 env2 r2v2 vvs2 nid2 rir2 ->
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
                      valid_vars_sact guard nid ->
                      I env r2v vvs0 nid rir guard ->
                      P env r2v vvs0 nid rir env' r2v' vvs nid' rir' /\ I env' r2v' vvs nid' rir' guard
                      /\ (forall ov, v = Some ov -> valid_vars_sact ov nid')
                      /\ valid_vars_sact guard nid'
                      /\ valid_vars_sact fail_cond nid'
                      /\ nid <= nid'
                      /\ wt_sact vvs (reduce t v) t
                      /\ t = t0
                 ) args)
      lt
      (WTargs: Forall2 (wt_daction (R:=R) (Sigma:=Sigma) pos_t string string tsig) args lt)
      guard env r2v vvs0 rir nid names0 fail0 names env' r2v' vvs fail1 rir' nid'
      (VG: valid_vars_sact guard nid)
      (VF: valid_vars_sact fail0 nid)
      (INV: I env r2v vvs0 nid rir guard)
      (GRIA: gria_list' guard rec args tsig env r2v vvs0 rir nid names0 fail0 = (names, env', r2v', vvs, fail1, rir', nid'))
      lt0
      (NAMES: Forall2 (fun '(var1, t1) t2 =>
                         t1 = t2 /\
                           exists s, list_assoc vvs0 var1 = Some (t1, s)
                      ) names0 lt0)
    ,
      P env r2v vvs0 nid rir env' r2v' vvs nid' rir'
      /\ I env' r2v' vvs nid' rir' guard
      /\ (Forall2 (fun '(var1, t1) t2 =>
                     t1 = t2 /\
                           exists s, list_assoc vvs var1 = Some (t1, s)
                      ) names (rev lt ++ lt0))
      /\ List.length names = List.length names0 + List.length args
      /\ valid_vars_sact fail1 nid'
      /\ nid <= nid'.
  Proof.
    induction 6; simpl; intros; eauto.
    - inv GRIA. repeat split; eauto. inv WTargs. simpl. eauto.
    - repeat destr_in GRIA. subst. inv WTargs.
      eapply H in Heqp; eauto. destruct Heqp as (P2 & I2 & RV2 & VG2 & VF2 & NIDGROWS2 & WTa & TEQ). clear H.
      subst.
      eapply IHF in GRIA;  eauto.
      destruct GRIA as (Pgria & Igria & NAMES1 & LENNAMES & VF3 & NIDGROWS).

      repeat split; eauto.
      + eapply Ptrans; eauto.
        eapply Ptrans. eauto. 3: eauto.
        all: eapply Psetvvs; eauto.
        destruct o; simpl; eauto. red; inversion 1.
        destruct o; simpl; eauto. red; inversion 1.
      + simpl. rewrite <- app_assoc. apply NAMES1.
      + simpl in LENNAMES; lia.
      + lia.
      + eapply valid_var_sact_incr; eauto.
      + eapply valid_vars_merge_failures; eauto using valid_var_sact_incr.
      + eapply Psetvvs; eauto.
        intros. destruct o. simpl. eauto. red; simpl; intros. inv H.
      + simpl. constructor. split; auto.
        rewrite list_assoc_gss. eauto.
        eapply Forall2_impl. apply NAMES. simpl.
        intros (n0 & t0) t1 IN1 IN2 (EQ & s0 & GET). subst. split; auto.
        rewrite list_assoc_gso; eauto.
        eapply Pvvsgrows in GET; eauto.
        eapply Irange in GET; eauto. red in GET. lia.
  Qed.

  Record wf_state tsig env reg2var vvs rir nid :=
    {
      wfs_wt_vvs: wt_vvs vvs;
      wfs_env_vvs: env_vvs env vvs tsig;
      wfs_r2v_vvs: reg2var_vvs reg2var vvs;
      wfs_vvs_range: vvs_range vvs nid;
      wfs_vsv: vvs_smaller_variables vvs;
      wfs_rir: wf_rir rir nid;
    }.

  Lemma wf_state_set:
    forall tsig env reg2var vvs rir n,
      wf_state tsig env reg2var vvs rir n ->
      forall t v vv,
        wt_sact vvs vv t ->
        list_assoc tsig v = Some t ->
        (forall v0, var_in_sact vv v0 -> v0 < n) ->
        wf_state tsig (list_assoc_set env v n) reg2var (list_assoc_set vvs n (t, vv)) rir (S n).
  Proof.
    intros tsig env reg2var vvs rir n WFS t v vv WTA GETt VARRES.
    inv WFS; split; eauto.
    + eapply wt_vvs_set; eauto.
    + eapply env_vvs_set; auto.
    + eapply reg2var_vvs_grows. eauto. eapply vvs_grows_set; eauto.
    + eapply vvs_range_list_assoc_set. eapply vvs_range_incr. 2: eauto. lia.
      red; lia.
    + eapply vvs_smaller_variables_set; eauto.
    + eapply wf_rir_incr; eauto.
  Qed.

  Lemma wt_daction_wf_sact:
    forall ua tsig tret,
      wt_daction (R:=R) (Sigma:=Sigma) pos_t string string tsig ua tret ->
      wf_sact_known_vars (map fst tsig) ua.
  Proof.
    induction ua using daction_ind'; simpl; intros tsig tret WT; try now (inv WT; econstructor; eauto).
    - inv WT. econstructor. inv H1. apply assoc_list_assoc in H.
      eapply list_assoc_in_keys; eauto.
    - inv WT. inv H4. apply assoc_list_assoc in H.
      eapply list_assoc_in_keys in H; eauto.
      econstructor; eauto.
    - inv WT. econstructor; eauto. eapply IHua2 in H5; eauto.
    - inv WT. econstructor; eauto.
      revert H H3. clear H5 IHua. generalize (map snd (int_argspec ufn)).
      induction args; simpl; intros; eauto.
      inv H. inv H3. constructor; eauto.
      eapply Forall2_length in H3.
      setoid_rewrite H3. rewrite ! map_length. auto.
      apply IHua in H5.
      eapply wf_sact_known_vars_incl. eauto.
      red; intros.
      rewrite in_map_iff in H0. rewrite in_map_iff.
      destruct H0 as ((? & ?) & ? & IN). subst. simpl.
      eexists; split; eauto. 2: apply in_rev; eauto. reflexivity.
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
    + eapply wf_rir_incr; eauto. lia.
    + eapply vvs_grows_set; eauto.
  Qed.

  Lemma wf_state_vvs_grows_incr:
    forall tsig env r2v vvs rir n rir' vvs' n' ,
      wf_state tsig env r2v vvs rir n ->
      rir_grows vvs rir vvs' rir' ->
      wt_vvs vvs' ->
      vvs_range vvs' n' ->
      vvs_smaller_variables vvs' ->
      wf_rir rir' n' ->
      n <= n' ->
      wf_state tsig env r2v vvs' rir' n'.
  Proof.
    intros tsig env r2v vvs rir n rir' vvs' n' WFS RG WTV VR VSV WFR LE.
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
        wf_state tsig vm' r2v' vvs' rir nid'.
  Proof.
    intros. inv H0; inv H1.
    edestruct merge_branches_grows as (VVSGROWS4 & VVSRANGE4 & ENVVVS4 & NIDGROWS4 & VVSVALID4 & WTVVS4); eauto.
    split; eauto. split; eauto.
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
        wf_state tsig env r2v' vvs' rir nid'.
  Proof.
    intros. inv H0; inv H1.
    edestruct merge_reg2var_grows as (VVSGROWS4 & VVSRANGE4 & R2VVVS4 & NIDGROWS4 & VSV4 & WTVVS4); eauto.
    split; eauto. split; eauto.
    split; eauto.
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
    + eapply wf_rir_incr; eauto.
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
      forall rir' ,
        rir_grows vvs rir vvs rir' ->
        wf_rir rir' nid ->
        wf_state tsig env r2v vvs rir' nid.
  Proof.
    intros tsig env r2v vvs rir nid H rir' H0 H1.
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

  Lemma get_rule_information_aux_env_grows:
    forall (ua: uact)
           tsig (env: list (string * nat)) reg2var (guard: sact)
           (rir: rule_information_raw) (nid: nat)
           v env' reg2var' vvs fail_cond rir' nid' t vvs0
           (GRIA: get_rule_information_aux ua tsig env reg2var vvs0 guard rir nid = (v, env', reg2var', vvs, fail_cond, rir', nid', t))
           tret
           (WT: BitsToLists.wt_daction pos_t string string (R:=R) (Sigma:=Sigma) tsig ua tret)
           (WFS: wf_state tsig env reg2var vvs0 rir nid)
           (GUARDVALID: valid_vars_sact guard nid)
           (WTGUARD: wt_sact vvs0 guard (bits_t 1)),
      wf_state tsig env' reg2var' vvs rir' nid'
      /\ rir_grows vvs0 rir vvs rir'
      /\ (forall x, var_in_sact (reduce t v) x -> exists z, list_assoc vvs x = Some z)
      /\ wt_sact vvs (reduce t v) t
      /\ valid_vars_sact fail_cond nid'
      /\ nid <= nid'
      /\ Forall2 (fun x y => fst x = fst y) env env'
      /\ tret = t
  .
  Proof.
    Opaque skipn.
    intros ua; pattern ua; eapply daction_ind'; simpl; intros; eauto.
    all: repeat destr_in GRIA; inv GRIA; eauto; try now (intuition congruence).
    - inv WT.
    - intuition try congruence. eapply rir_grows_refl. inv H.
      apply wt_sact_reduce. easy. red; inversion 1. lia. apply same_env_refl. inv WT. auto.
    - intuition try congruence.
      + eapply rir_grows_refl. 
      + inv H. edestruct env_vvs_ex; eauto. inv WFS; eauto.
      + simpl. edestruct env_vvs_ex; eauto. inv WFS; eauto.
        econstructor; eauto.
      + red; inversion 1.
      + lia.
      + apply same_env_refl.
      + inv WT. inv H1.
        eapply assoc_list_assoc in H. congruence.
    - exfalso; eapply env_vvs_some_none; eauto.
      inv WFS; eauto.
    - inv WT. inv H1.
      apply assoc_list_assoc in H.
      edestruct env_vvs_none_some. inv WFS; eauto. eauto. eauto.
    - intuition try congruence. eapply rir_grows_refl. inv H.
      simpl. econstructor. inv WT.
      apply wt_val_of_value.
      red; intros. inv H. lia.
      apply same_env_refl.
      inv WT. auto.
    - inv WT.
      Ltac dhyp H :=
        let wfs := fresh "WFS" in
        let rg := fresh "RIRGROWS" in
        let v := fresh "VARRES" in
        let wt := fresh "WTRES" in
        let vvs := fresh "FAILVALID" in
        let ng := fresh "NIDGROWS" in
        let se := fresh "SAMEENV" in
        let teq := fresh "TEQ" in
        edestruct H as (wfs & rg & v & wt & vvs & ng & se & teq); eauto.
      dhyp H.
      subst.
      assert (RG: rir_grows vvs0 rir (list_assoc_set l n (t0, reduce t0 o)) rir').
      {
        eapply rir_grows_trans. eauto. eapply rir_grows_set; eauto.
        inv WFS0; eauto.
        unfold valid_name; lia.
      }
      repeat (refine (conj _ _)); eauto.
      + eapply wf_state_set; eauto. inv H5. eapply assoc_list_assoc in H0. eauto.
        intros.
        edestruct VARRES as (z & GET); eauto. eapply wfs_vvs_range in GET; eauto.
      + simpl; inversion 1.
      + eapply wt_sact_reduce; eauto. easy.
      + eapply valid_var_sact_incr; eauto.
      + eapply same_env_set_in; eauto. inv H5. apply assoc_list_assoc in H0.
        destruct (list_assoc env v) eqn:?.
        eapply list_assoc_in_keys; eauto.
        edestruct env_vvs_none_some. inv WFS; eauto. eauto. eauto.
    - inv WT.
      dhyp H. subst.
      dhyp H0.
      eapply valid_var_sact_incr; eauto.
      eapply wt_sact_vvs_grows; eauto.
      eapply rir_vvs_grows; eauto.
      subst.
      repeat refine (conj _ _); eauto.
      eapply rir_grows_trans; eauto.
      eapply valid_vars_merge_failures; eauto.
      eapply valid_var_sact_incr; eauto. lia.
      eapply same_env_trans; eauto. congruence.
    - inv WT.
      dhyp H. subst.
      dhyp H0.


      + eapply wf_state_cons; eauto. intros. edestruct VARRES as (z & GET); eauto.
        eapply wfs_vvs_range in GET; eauto. 
      + eapply valid_var_sact_incr; eauto.
      + eapply wt_sact_vvs_grows; eauto.
        eapply rir_vvs_grows.
        eapply rir_grows_trans; eauto.
        eapply rir_grows_set; eauto.
        inv WFS0; eauto.
        unfold valid_name; lia.
      + subst. inv SAMEENV0. simpl in H3. subst.
        change (skipn 1 (y::l')) with l'.


        repeat (refine (conj _ _)); eauto.
        * apply wf_state_tl in WFS1. simpl in WFS1. eauto.
        * eapply rir_grows_trans; eauto.
          eapply rir_grows_trans; eauto.
          eapply rir_grows_set; eauto.
          inv WFS0; eauto.
          unfold valid_name; lia.
        * eapply valid_vars_merge_failures; eauto. eapply valid_var_sact_incr; eauto. lia.
        * lia.
        * eapply same_env_trans; eauto. congruence.
    - inv WT.
      dhyp H. subst.
      set (ll1 := (list_assoc_set l n (bits_t 1, reduce (bits_t 1) o))).
      set (ll2 := (list_assoc_set ll1 (n + 1) (bits_t 1, uand guard (SVar n)))).
      set (ll3 := (list_assoc_set ll2 (n + 2) (bits_t 1, uand guard (unot (SVar n))))).

      assert (WFSl1: wf_state tsig l1 l0 ll1 r0 (n + 1) /\ vvs_grows l ll1).
      {
        eapply wf_state_vvs_set; eauto. intros.
        edestruct VARRES as (z & GET). eauto. eapply wfs_vvs_range in GET; eauto. lia.
      }
      destruct WFSl1 as (WFSl1 & VG1).
      assert (WFSl2: wf_state tsig l1 l0 ll2 r0 (n + 2) /\ vvs_grows ll1 ll2).
      {
        eapply wf_state_vvs_set; eauto.
        econstructor. eapply wt_sact_vvs_grows. 2: eauto.
        eapply vvs_grows_trans; eauto using rir_vvs_grows.
        econstructor. unfold ll1. rewrite list_assoc_gss. eauto.
        constructor. simpl.
        intros v VIS. inv VIS. eapply GUARDVALID in H7. red in H7. lia.
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
        intros v VIS. inv VIS. eapply GUARDVALID in H7. red in H7. lia.
        inv H7. inv H5. lia.
        lia.
      }
      destruct WFSl3 as (WFSl3 & VG3).
      dhyp H0.
      red; intros. inv H2. red; lia.
      econstructor. rewrite list_assoc_gso by lia; rewrite list_assoc_gss; eauto.
      subst.
      dhyp H1.
      inv WFS1; eapply wf_state_vvs_grows_incr; eauto.
      inversion 1; subst; simpl. red; lia.
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
      edestruct merge_branches_grows' as (VVSGROWS4 & NIDGROWS4 & WFS4); eauto.
      inv WFS2; eapply wf_state_vvs_grows_incr; eauto.
      red; lia.
      edestruct merge_reg2var_grows' as (VVSGROWS5 & NIDGROWS5 & WFS5); eauto.
      inv WFS4; eapply wf_state_vvs_grows_incr; eauto.
      eapply rir_grows_trans. eauto.
      inv WFS2.
      eapply rir_grows_change_vvs; eauto.
      lia. red; lia.
      eapply wt_sact_vvs_grows; eauto.
      repeat (refine (conj _ _)); auto.
      eapply rir_grows_trans; eauto.
      eapply rir_grows_trans.
      2: eapply rir_grows_trans; eauto.
      eapply rir_grows_trans; eauto.
      eapply rir_grows_change_vvs; eauto. inv WFS0; eauto.
      eapply rir_grows_change_vvs; eauto. inv WFS2; eauto.
      {
        intros x VIS.
        destruct o. 2: now inv VIS.
        destruct o0. 2: now inv VIS.
        destruct o1. 2: now inv VIS.
        simpl in *. inv VIS.
        + edestruct VARRES as (z & IN); eauto.
          exists z.
          eapply VVSGROWS5.
          eapply VVSGROWS4.
          eapply rir_vvs_grows. eauto.
          eapply rir_vvs_grows. eauto.
          exploit wfs_vvs_range. 2: apply IN. eauto. unfold valid_name; intro.
          rewrite ! list_assoc_gso by lia; auto.
        + edestruct VARRES0; eauto. eexists.
          eapply VVSGROWS5.
          eapply VVSGROWS4.
          eapply rir_vvs_grows. eauto. eauto.
        + edestruct VARRES1; eauto.
      }
      {
        apply wt_sact_reduce.
        intros x EQ. unfold build_uif in EQ. repeat destr_in EQ; inv EQ.
        simpl in *.
        econstructor; eauto.
        eapply wt_sact_vvs_grows. 2: eauto.
        eapply vvs_grows_trans; eauto.
        eapply vvs_grows_trans; eauto.
        eapply vvs_grows_trans; eauto.
        eapply vvs_grows_trans; eauto.
        eapply vvs_grows_trans; eauto.
        eapply vvs_grows_trans; eauto using rir_vvs_grows.
        eapply wt_sact_vvs_grows. 2: eauto.
        eapply vvs_grows_trans; eauto.
        eapply vvs_grows_trans; eauto using rir_vvs_grows.
        eapply wt_sact_vvs_grows. 2: eauto.
        eapply vvs_grows_trans; eauto.
      }
      {
        apply valid_vars_merge_failures.
        eapply valid_var_sact_incr. eauto. lia.
        apply valid_vars_merge_failures.
        apply valid_vars_and.
        * simpl in VARRES. red; intros.
          edestruct VARRES; eauto.
          eapply vss_or_extcall_var_lt in H3; eauto.
          eapply vvs_range_incr.  2: inv WFS0; eauto. lia.
        * eapply valid_var_sact_incr. eauto. lia.
        * apply valid_vars_and.
          apply valid_vars_not.
          red; intros.
          edestruct VARRES; eauto.
          eapply vss_or_extcall_var_lt in H3; eauto.
          eapply vvs_range_incr.  2: inv WFS0; eauto. lia.
          eapply valid_var_sact_incr. eauto. lia.
      }
      lia.
      exploit merge_vms_preserve_same_env. 2: eauto.
      eapply same_env_trans. congruence. apply same_env_sym; eauto. auto. intro SAMEENV3.
      eapply same_env_trans; eauto. congruence.
      eapply same_env_trans. congruence. 2: eauto. eauto.
    - repeat (refine (conj _ _)); eauto.

      + exploit wt_sact_interp; eauto. inv WFS; eauto. inv WFS; eauto. intros (v & IS & WTg). inv WTg.
        destruct bs; simpl in H0; try lia.
        destruct bs; simpl in H0; try lia.
        eapply wf_state_change_rir; eauto. eapply rir_grows_add_read0; eauto.
        eapply wf_rir_add_read0; inv WFS; eauto.
      + exploit wt_sact_interp; eauto. inv WFS; eauto. inv WFS; eauto. intros (v & IS & WTg). inv WTg.
        destruct bs; simpl in H0; try lia.
        destruct bs; simpl in H0; try lia.
        eapply rir_grows_add_read0; eauto.
      + simpl. inversion 1; subst. 
        edestruct wfs_r2v_vvs as (? & GET & ? & GET2); eauto.
        setoid_rewrite Heqo in GET. inv GET. eauto.
      + simpl.
        edestruct wfs_r2v_vvs as (? & GET & ? & GET2); eauto.
        setoid_rewrite Heqo in GET. inv GET. eauto.
        econstructor; eauto.
      + red; intros. inv H.
      + apply same_env_refl.
      + inv WT. auto.
    - repeat (refine (conj _ _)); eauto.
      + exploit wt_sact_interp; eauto. inv WFS; eauto. inv WFS; eauto. intros (v & IS & WTg). inv WTg.
        destruct bs; simpl in H0; try lia.
        destruct bs; simpl in H0; try lia.
        eapply wf_state_change_rir; eauto. eapply rir_grows_add_read1; eauto.
        eapply wf_rir_add_read1; inv WFS; eauto.
      + exploit wt_sact_interp; eauto. inv WFS; eauto. inv WFS; eauto. intros (v & IS & WTg). inv WTg.
        destruct bs; simpl in H0; try lia.
        destruct bs; simpl in H0; try lia.
        eapply rir_grows_add_read1; eauto.
      + simpl. inversion 1; subst. 
        edestruct wfs_r2v_vvs as (? & GET & ? & GET2); eauto.
        setoid_rewrite Heqo in GET. inv GET. eauto.
      + simpl.
        edestruct wfs_r2v_vvs as (? & GET & ? & GET2); eauto.
        setoid_rewrite Heqo in GET. inv GET. eauto.
        econstructor; eauto.
      + red; intros. inv H.
      + apply same_env_refl.
      + inv WT. auto.
    - edestruct wfs_r2v_vvs as (? & GET & ? & GET2); eauto.
      setoid_rewrite Heqo in GET. inv GET.
    - edestruct wfs_r2v_vvs as (? & GET & ? & GET2); eauto.
      setoid_rewrite Heqo in GET. inv GET.
    - inv WT.
      dhyp H. subst.
      assert (rir_grows l r0 vvs rir').
      {
        destr_in Heqp7; inv Heqp7.
        eapply rir_grows_trans.
        eapply rir_grows_add_write0; eauto.
        eapply wt_sact_vvs_grows. 2: eauto.
        eapply rir_vvs_grows. eauto.
        eapply rir_grows_change_vvs. eauto.
        inv WFS0; eauto. intros.
        red in H0.
        rewrite ! list_assoc_gso by lia. auto.
        eapply rir_grows_trans.
        eapply rir_grows_add_write1; eauto.
        eapply wt_sact_vvs_grows. 2: eauto.
        eapply rir_vvs_grows. eauto.
        eapply rir_grows_change_vvs. eauto.
        inv WFS0; eauto. intros.
        red in H0.
        rewrite ! list_assoc_gso by lia. auto.
      }
      assert (n <= nid').
      {
        destr_in Heqp7; inv Heqp7. lia. lia.
      }
      assert (wf_rir rir' nid' /\ valid_vars_sact s nid' /\ valid_vars_sact s0 nid').
      {
        destr_in Heqp7; inv Heqp7.
        - edestruct wf_rir_add_write0. 4: eauto. inv WFS0; eauto.
          eapply valid_var_sact_incr; eauto.
          red; intros. edestruct VARRES as (z & IN); eauto.
          eapply wfs_vvs_range in IN; eauto.
          split.
          eapply wf_rir_incr; eauto.
          split; eapply valid_var_sact_incr; eauto.
        - edestruct wf_rir_add_write1. 4: eauto. inv WFS0; eauto.
          eapply valid_var_sact_incr; eauto.
          red; intros. edestruct VARRES as (z & IN); eauto.
          eapply wfs_vvs_range in IN; eauto.
          split.
          eapply wf_rir_incr; eauto.
          split; eapply valid_var_sact_incr; eauto.
      }
      assert (wt_vvs vvs).
      {
        inv WFS0.
        destr_in Heqp7; inv Heqp7.
        eapply wt_vvs_set; eauto.
        eapply wt_vvs_set; eauto.
        eapply vvs_range_list_assoc_set; eauto. eapply vvs_range_incr. 2: eauto. lia. red; lia.
        eapply wt_sact_vvs_grows. eapply vvs_grows_set; eauto. auto.
        eapply wt_vvs_set; eauto.
      }
      assert (vvs_smaller_variables vvs).
      {
        inv WFS0.
        destr_in Heqp7; inv Heqp7.
        eapply vvs_smaller_variables_set; eauto.
        eapply vvs_smaller_variables_set; eauto.
        intros; edestruct VARRES as (z & IN); eauto.
        eapply wfs_vvs_range0 in IN; eauto.
        intros; edestruct VARRES as (z & IN); eauto.
        eapply wfs_vvs_range0 in IN; eauto. red in IN; lia.
        eapply vvs_smaller_variables_set; eauto.
        intros; edestruct VARRES as (z & IN); eauto.
        eapply wfs_vvs_range0 in IN; eauto.
      }
      assert (vvs_range vvs nid').
      {
        inv WFS0.
        destr_in Heqp7; inv Heqp7.
        eapply vvs_range_list_assoc_set.
        eapply vvs_range_list_assoc_set.
        eapply vvs_range_incr; eauto. red; lia. red; lia.
        eapply vvs_range_list_assoc_set.
        eapply vvs_range_incr; eauto. red; lia.
      }
      destruct H2 as (? & ? & ?).

      (* +  *)
      (*   assert (rir_grows l r0 *)
      (*                     (list_assoc_set (list_assoc_set l n (R idx, reduce (R idx) o))  *)
      (*                                     (n + 1) (R idx, reduce (R idx) o)) rir'). *)
      (*   { *)
      (*     eapply rir_grows_trans. *)
      (*     eapply rir_grows_add_write0; eauto. *)
      (*     eapply wt_sact_vvs_grows. 2: eauto. *)
      (*     eapply rir_vvs_grows. eauto. *)
      (*     eapply rir_grows_change_vvs. eauto. *)
      (*     intros. *)
      (*     red in H0. *)
      (*     rewrite ! list_assoc_gso by lia. auto. *)
      (*   } *)
      (*   edestruct wf_rir_add_write0 as (WF2 & FV2). *)
      (*   4: eauto. eapply wf_rir_incr; eauto. *)
      (*   eapply valid_var_sact_incr; eauto. *)
      (*   destruct o; simpl. *)
      (*   red; intros. edestruct VARRES. eauto. eauto. apply VVSRANGE in H3. red in H3; red; lia. *)
      (*   red; intros. inv H1. *)

        repeat (refine (conj _ _)); eauto.
      + 
        destr_in Heqp7; inv Heqp7.
        * eapply wf_state_change_r2v.
          eapply wf_state_change_r2v.
          eapply wf_state_vvs_grows_incr; eauto.
          rewrite list_assoc_gso by lia; rewrite list_assoc_gss; eauto.
          rewrite list_assoc_gss; eauto.
        * eapply wf_state_change_r2v.
          eapply wf_state_vvs_grows_incr; eauto.
          rewrite list_assoc_gss; eauto.
      + eapply rir_grows_trans; eauto.
      + inversion 1.
      + simpl. constructor. constructor. reflexivity.
      + apply valid_vars_merge_failures; auto.
      + lia.

    - assert (exists t1,
                 wt_daction (R:=R) (Sigma:=Sigma) pos_t string string tsig arg1 t1 /\
                   wt_unop ufn1 t1 tret
                   (* tret = ret_type_unop ufn1 t1 *)
             ).
      {
        inv WT; eexists; split; simpl; eauto; try (econstructor; eauto).
      }
      destruct H0 as (t1 & WTa & EQ).
      dhyp H. subst.
      repeat (refine (conj _ _)); eauto.
      + simpl. intros. inv H0. eauto.
      + simpl. intros. econstructor. eauto.
        exploit wt_unop_type_unop_ret; eauto. congruence.
      + eapply wt_unop_type_unop_ret; eauto.
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
      + eapply valid_var_sact_incr; eauto.
      + eapply wt_sact_vvs_grows; eauto. eapply rir_vvs_grows; eauto.
      + repeat (refine (conj _ _)); eauto.
        * eapply rir_grows_trans; eauto.
        * simpl. intros. inv H1.
          -- edestruct VARRES as (? & IN); eauto. eapply rir_vvs_grows in IN; eauto.
          -- eauto.
        * simpl. subst.
          econstructor. eapply wt_sact_vvs_grows; eauto using rir_vvs_grows.
          eauto.
          exploit wt_binop_type_binop_ret; eauto. congruence.
        * eapply valid_vars_merge_failures. eapply valid_var_sact_incr; eauto. auto.
        * lia.
        * eapply same_env_trans; eauto. congruence.
        * subst. eapply wt_binop_type_binop_ret; eauto.
    - inv WT. dhyp H. subst.
      assert (rir_grows l rir'
                        (list_assoc_set l n (retSig (Sigma ufn), SExternalCall ufn (reduce (arg1Sig (Sigma ufn)) o))) rir').
      {
        eapply rir_grows_change_vvs. inv WFS0; eauto.
        intros.
        red in H0.
        rewrite ! list_assoc_gso by lia. auto.
      }
      edestruct wf_state_vvs_set with (k:= n) (m := S n). apply WFS0.
      apply wt_sact_extcall. apply WTRES. lia.
      intros. inv H1. edestruct VARRES as (? & IN); eauto.
      exploit wfs_vvs_range; eauto. lia.
      repeat (refine (conj _ _)); eauto.
      * eapply rir_grows_trans; eauto.
      * simpl. intros x A; inv A. rewrite list_assoc_gss. eauto.
      * simpl. econstructor. rewrite list_assoc_gss. eauto. 
      * eapply valid_var_sact_incr. eauto. lia.
    - inv WT.
      eapply gria_list_grows with
        (I:= fun env reg2var vvs nid rir guard =>
               wf_state tsig env reg2var vvs rir nid
               /\ valid_vars_sact guard nid
               /\ wt_sact vvs guard (bits_t 1)
        )
        (P:= fun env reg2var vvs nid rir env' rev2var' vvs' nid' rir' =>
               Forall2 (fun x y => fst x = fst y) env env'
               /\ rir_grows vvs rir vvs' rir'
         ) in Heqp.
      7: {
        eapply Forall_impl.
        2: apply H0. simpl; intros. destruct H7 as (WFS2 & GV & WTG).
        dhyp H1. subst. intuition eauto.
        - eapply valid_var_sact_incr; eauto.
        - eapply wt_sact_vvs_grows; eauto using rir_vvs_grows.
        - subst. simpl in *. red; intros. edestruct VARRES as (z & IN); eauto.
          eapply wfs_vvs_range in IN; eauto.
        - eapply valid_var_sact_incr; eauto.
      }
      destruct Heqp as ((SAMEENV1 & RIRGROWS1) & ((WFS1 & GUARDVALID1 & WTGUARD1) & (NAMES & LENNAMES & VF1 & NID1))); eauto.
      2: {
        intros. split; eauto using same_env_refl, rir_grows_refl.
      }
      2: {
        simpl; intros; eauto.
        decompose [and] H1; clear H1.
        decompose [and] H2; clear H2.
        decompose [and] H3; clear H3.
        decompose [and] H5; clear H5.
        split.
        eapply same_env_trans; eauto. congruence.
        eapply rir_grows_trans; eauto.
      }
      2: {

        intuition.
        - apply same_env_refl.
        - eapply rir_grows_set; eauto. inv H5; eauto. unfold valid_name; lia. 
        - eapply wf_state_vvs_set; eauto.
        - eapply valid_var_sact_incr; eauto.
        - eapply wt_sact_vvs_grows; eauto. eapply vvs_grows_set; eauto.
          inv H5; eauto.
      }
      2:{
        simpl; intros. intuition; eauto using rir_vvs_grows.
      }
      2: {
        intros. destruct H1. inv H1. eauto.
      }
      2: now eauto.
      2: now (eapply valid_var_sact_incr; eauto).
      2: red; now inversion 1.
      2: now split; auto.
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
      + eapply rir_grows_trans; eauto.
      + eapply valid_vars_merge_failures; eauto using valid_var_sact_incr.
      + lia.
    - inv WT.
      dhyp H.
  Qed.

  Definition match_Gamma_env (Gamma: list (string * val)) (env: list (string * nat)) vvs :=
    Forall2 (fun x y =>
               fst x = fst y /\ interp_sact vvs (SVar (snd y)) (snd x)
            ) Gamma env.

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


  Lemma env_vvs_same_fst:
    forall env vvs tsig,
      env_vvs env vvs tsig ->
      map fst tsig = map fst env.
  Proof.
    induction 1; simpl; intros; eauto.
    repeat destr_in H. destruct H. subst. simpl; eauto. congruence.
  Qed.

  Lemma wt_sact_vvs_range_valid_vars:
    forall vvs nid,
      vvs_range vvs nid ->
      forall grd t,
      wt_sact vvs grd t ->
      valid_vars_sact grd nid.
  Proof.
    red.
    induction 2; simpl; intros; eauto.
    - inv H1. eapply H in H0. red in H0; red; lia.
    - inv H1.
    - inv H0; eauto.
    - inv H2; eauto.
    - inv H1; eauto.
    - inv H1; eauto.
  Qed.

  Lemma get_rule_information_aux_env_grows':
    forall (ua: uact)
           tsig (env: list (string * nat)) reg2var (guard: sact)
           (rir: rule_information_raw) (nid: nat)
           v env' reg2var' vvs fail_cond rir' nid' t vvs0
           (GRIA: get_rule_information_aux ua tsig env reg2var vvs0 guard rir nid = (v, env', reg2var', vvs, fail_cond, rir', nid', t))
           tret
           (WT: BitsToLists.wt_daction pos_t string string (R:=R) (Sigma:=Sigma) tsig ua tret)
           (WTVVS: wt_vvs vvs0)
           (ENVVVS: env_vvs env vvs0 tsig)
           (R2VVVS: reg2var_vvs reg2var vvs0)
           (RNGVVS: vvs_range vvs0 nid)
           (VVSVALID: vvs_smaller_variables vvs0)
           (RIRRNG: wf_rir rir nid)
           (WTGUARD: wt_sact vvs0 guard (bits_t 1)),
      vvs_range vvs nid'
      /\ (env_vvs env' vvs tsig)
      /\ reg2var_vvs reg2var' vvs
      /\ rir_grows vvs0 rir vvs rir'
      /\ (forall x, var_in_sact (reduce t v) x -> exists z, list_assoc vvs x = Some z)
      /\ wt_sact vvs (reduce t v) t
      /\ wf_rir rir' nid'
      /\ wt_vvs vvs
      /\ vvs_smaller_variables vvs
      /\ valid_vars_sact fail_cond nid'
      /\ nid <= nid'
      /\ tret = t.
  Proof.
    intros.
    dhyp get_rule_information_aux_env_grows.
    - eapply wt_daction_wf_sact in WT.
      eapply wf_sact_known_vars_incl; eauto.
      erewrite env_vvs_same_fst; eauto using incl_refl.
    - eapply wt_sact_vvs_range_valid_vars; eauto.
    - repeat refine (conj _ _); auto.
      + destruct v; simpl; intros; eauto. inv H.
      + apply wt_sact_reduce. eauto.
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

  Lemma get_rule_information_aux_interp:
    forall (ua: uact)
           tsig (env: list (string * nat)) reg2var (guard: sact)
           (rir: rule_information_raw) (nid: nat)
           v env' reg2var' vvs fail_cond rir' nid' t vvs0
           (GRIA: get_rule_information_aux ua tsig env reg2var vvs0 guard rir nid = (v, env', reg2var', vvs, fail_cond, rir', nid', t))
           tret
           (WT: BitsToLists.wt_daction pos_t string string (R:=R) (Sigma:=Sigma) tsig ua tret)
           (WTVVS: wt_vvs vvs0)
           (ENVVVS: env_vvs env vvs0 tsig)
           (R2VVVS: reg2var_vvs reg2var vvs0)
           (RNGVVS: vvs_range vvs0 nid)
           (VVSVALID: vvs_smaller_variables vvs0)
           (RIRRNG: wf_rir rir nid)
           (WTGUARD: wt_sact vvs0 guard (bits_t 1))
           Gamma sched_log action_log action_log' vret Gamma'
           (WTRENV: wt_renv R REnv r)
           (WTG: wt_env _ tsig Gamma)
           (GE: match_Gamma_env Gamma env vvs0)
           (INTERP: interp_daction r sigma Gamma sched_log action_log ua = Some (action_log', vret, Gamma')),
      interp_sact vvs (reduce t v) vret
      /\ interp_sact vvs fail_cond (Bits 1 [false])
      /\ match_Gamma_env Gamma' env' vvs
      /\ wt_env _ tsig Gamma'.
  Proof.
    intros ua; pattern ua; induction ua using daction_ind'; simpl; intros; eauto.
    - inv INTERP.
    - inv INTERP.
    - unfold opt_bind in INTERP.
      repeat destr_in INTERP; inv INTERP.
      edestruct match_Gamma_env_ex as (n & tt & s & GET1 & GET2 & GET3 & GET4); eauto.
      rewrite GET1, GET2 in GRIA. inv GRIA. simpl.
      repeat split. econstructor; eauto. constructor. auto. auto.
    - inv INTERP. inv GRIA. simpl.
      repeat split. econstructor; eauto. constructor. auto. auto.
    - unfold opt_bind in INTERP.
      repeat destr_in INTERP; inv INTERP.
      repeat destr_in GRIA. inv GRIA.
      inv WT.
      edestruct IHua as (ISV & ISF & MGE & WTE); eauto.
      dhyp get_rule_information_aux_env_grows'. subst.
      simpl.
      repeat refine (conj _ _).
      + econstructor.
      + eapply vvs_grows_interp_sact. 2: eauto. eapply vvs_grows_set; eauto.
      +
        eapply match_Gamma_env_set; eauto.
      + eapply wt_env_set; eauto.
        edestruct (wt_sact_interp) with (a:=reduce t0 o) as (vv & IS & WTV); eauto.
        intros.
        edestruct VARRES. eauto. apply VVSRANGE in H0. apply H0.
        exploit interp_sact_determ. apply IS. apply ISV. intros ->; eauto.
    - unfold opt_bind in INTERP.
      repeat destr_in INTERP; inv INTERP.
      repeat destr_in GRIA. inv GRIA.
      inv WT.
      edestruct IHua as (ISV & ISF & MGE & WTE); eauto.
      dhyp (get_rule_information_aux_env_grows' a1). subst.
      edestruct IHua0 as (ISV0 & ISF0 & MGE0 & WTE0); eauto.
      eapply wt_sact_vvs_grows; eauto using rir_vvs_grows.
      dhyp (get_rule_information_aux_env_grows' a2).
      eapply wt_sact_vvs_grows; eauto using rir_vvs_grows.
      subst.
      repeat refine (conj _ _); eauto.
      econstructor.
      eapply vvs_grows_interp_sact. 2: eauto. eapply rir_vvs_grows; eauto. eauto.
      reflexivity.
    - unfold opt_bind in INTERP.
      repeat destr_in INTERP; inv INTERP.
      repeat destr_in GRIA. inv GRIA.
      inv WT.
      edestruct IHua as (ISV & ISF & MGE & WTE); eauto.
      dhyp (get_rule_information_aux_env_grows' ex). subst.
      edestruct IHua0 as (ISV0 & ISF0 & MGE0 & WTE0); eauto.
      + eapply wt_vvs_set; eauto.
      + constructor. split; auto. rewrite list_assoc_gss. eauto.
        eapply env_vvs_vvs_grows. eauto.
        eapply vvs_grows_set; eauto.
      + eapply reg2var_vvs_grows. eauto.
        eapply vvs_grows_set; eauto.
      + apply vvs_range_list_assoc_set. eapply vvs_range_incr. 2: eauto. lia.
        red. eauto.
      + eapply vvs_smaller_variables_set; eauto.
        intros.
        edestruct VARRES as (z & GET); eauto. apply VVSRANGE in GET. eauto.
      + eapply wf_rir_incr; eauto.
      + eapply wt_sact_vvs_grows; eauto.
        eapply rir_vvs_grows.
        eapply rir_grows_trans; eauto.
        eapply rir_grows_set; eauto.
        unfold valid_name; lia.
      + eapply wt_env_cons; eauto.
        edestruct (wt_sact_interp) with (a:=reduce t0 o) as (vv & IS & WTV); eauto.
        intros.
        edestruct VARRES. eauto. apply VVSRANGE in H0. apply H0.
        exploit interp_sact_determ. apply IS. apply ISV. intros ->; eauto.
      +


        constructor. split; auto. simpl. econstructor. rewrite list_assoc_gss. eauto.
        eapply vvs_grows_interp_sact. 2: eauto. eapply vvs_grows_set; eauto.
        eapply match_Gamma_env_vvs_grows; eauto.
        eapply vvs_grows_set; eauto.
      +
        dhyp (get_rule_information_aux_env_grows' body). subst.
        repeat refine (conj _ _); eauto.
        econstructor.
        eapply vvs_grows_interp_sact. 2: eauto. eapply rir_vvs_grows; eauto. eauto.
      reflexivity.

      eapply vvs_grows_set; eauto.
      +
        eapply match_Gamma_env_set; eauto.
      + eapply wt_env_set; eauto.
        edestruct (wt_sact_interp) with (a:=reduce t0 o) as (vv & IS & WTV); eauto.
        intros.
        edestruct VARRES. eauto. apply VVSRANGE in H0. apply H0.
        exploit interp_sact_determ. apply IS. apply ISV. intros ->; eauto.
    - 



    all: repeat destr_in GRIA; inv GRIA; inv WUKV; eauto; try now (intuition congruence).
  



  (*
    r : reg_t

    rir_write0s r : (gcond, [(wcond, wval)])

    var_in_sact wval v ->
    reg_in_sact wval r' ->
    

   *)

  Definition write_log_interpretable
      (REnv: Env reg_t)
      (r: env_t REnv (fun _ => val))
      (sigma: ext_fn_t -> val -> val)
      vvs rir (wl: write_log_raw) :=
    forall idx gcond wil,
      list_assoc wl idx = Some (gcond, wil) ->
      (exists v, interp_fact vvs rir gcond v) /\
        Forall
          (fun wi =>
             exists v, interp_fact vvs rir (wcond wi) v /\
                         (v = Bits 1 [true] ->
                          exists va, interp_fact vvs rir (wval wi) va)
          )
          wil.



      Lemma write_log_interpretable_change_vvs:
        forall (REnv: Env reg_t) (r: env_t REnv (fun _ => val))
               (sigma: ext_fn_t -> val -> val)
               (vvs1: list (nat * (type * sact)))
               (rir: rule_information_raw)
               (vvs2: list (nat * (type * sact)))
               n
               (VVSRANGE: vvs_range vvs1 n)
               (VVSGROWS: forall x,
                   valid_name x n ->
                   forall y, In (x, y) vvs1 -> In (x, y) vvs2)
               wl
               (WLI: write_log_interpretable vvs1 rir wl),
          write_log_interpretable vvs2 rir wl.
      Proof.
        intros.
        red; intros. red in WLI.
        destruct (WLI _ _ _ H) as ((vcond & GCOND) & F).
        split.
        eexists; eauto using interp_fact_change_vvs.
        eapply Forall_impl; eauto. simpl.
        intros a (v & INF & ACT).
        eexists; split; eauto using interp_fact_change_vvs.
        intro X; destruct (ACT X) as (va & INFA).
        eexists; eauto using interp_fact_change_vvs.
      Qed.

  Lemma get_rule_information_aux_act:
    forall
      (* (R: reg_t -> type) *)
      (* (Sigma: ext_fn_t -> ExternalSignature) *)
      (ua: sact) (env: list (string * nat)) (guard: sact)
      (rir: rule_information_raw) (nid: nat)
      v env' vvs fail_cond rir' nid' vvs0
      (GRIA: get_rule_information_aux ua env vvs0 guard rir nid = (v, env', vvs, fail_cond, rir', nid'))
      (* sig t *)
      (* (TA: forall p, exists tcr, *)
      (*     TypeInference.tc_action R Sigma p sig t ua = Success tcr) *)

        (WUKV: wf_sact_known_vars (map fst env) ua)
      (ENVVVS: forall x y, In (x,y) env -> In y (map fst vvs0))
      (RNGVVS: vvs_range vvs0 nid)
      (VVSVALID: forall v a, In (v, a) vvs0 -> forall v' , var_in_sact a v' -> var_lt v' v)
      (RIRRNG: wf_rir rir nid)
      (GUARDVALID: valid_vars_sact guard nid)

      (REnv: Env reg_t)
      (r: env_t REnv (fun _ => val))
      (sigma: ext_fn_t -> val -> val)
      Gamma sched_log action_log action_log' v' Gamma'
      (IA: UntypedSemantics.interp_daction
             r sigma Gamma
             sched_log action_log ua = Some (action_log', v', Gamma'))
      (W1I: write_log_interpretable vvs0 rir (rir_write0s rir))
      (W2I: write_log_interpretable vvs0 rir (rir_write1s rir)),
      interp_fact vvs rir' fail_cond (Bits 1 [false])
      /\ write_log_interpretable vvs rir' (rir_write0s rir')
      /\ write_log_interpretable vvs rir' (rir_write1s rir').
  Proof.
    intros ua. pattern ua.
    eapply daction_ind'; simpl; intros; eauto.
    - inv IA.
    - inv IA.
    - unfold opt_bind in IA; repeat destr_in IA; inv IA.
      inv WUKV.
      destr_in GRIA; inv GRIA. split; eauto.
      constructor.
      apply list_assoc_none_unknown_key in Heqo0. congruence.
    - inv IA. inv GRIA. split; eauto. constructor.
    - unfold opt_bind in IA; repeat destr_in IA; inv IA.
      repeat destr_in GRIA; inv GRIA. inv WUKV.
      edestruct H as (IDA1 & W1I1 & W2I1); eauto.
      edestruct get_rule_information_aux_env_grows
        as (VVSGROWS2 & VVSRANGE2 & ENVVVS2 & EXTGROWS2 & VAR2 & RIR2 & VVSVALID2 & FV2 & NID2); eauto.
      repeat (refine (conj _ _)).
      + eapply interp_fact_change_vvs. 3: eauto. all: eauto.
        intros. rewrite list_assoc_set_not_before. auto. intro IN.
        eapply vvs_range_in_fst in IN; eauto. lia.
      + eapply write_log_interpretable_change_vvs. 3: eauto. all: eauto.
        intros. rewrite list_assoc_set_not_before. auto. intro IN.
        eapply vvs_range_in_fst in IN; eauto. lia.
      + eapply write_log_interpretable_change_vvs. 3: eauto. all: eauto.
        intros. rewrite list_assoc_set_not_before. auto. intro IN.
        eapply vvs_range_in_fst in IN; eauto. lia.
    - unfold opt_bind in IA; repeat destr_in IA; inv IA.
      repeat destr_in GRIA; inv GRIA. inv WUKV.
      edestruct H as (IDA1 & W1I1 & W2I1); eauto.
      generalize (get_rule_information_aux_same_vm _ _ _ _ _ _ _ _ _ _ _ _ H5 Heqp). intro SVM1.
      edestruct get_rule_information_aux_env_grows with (ua:=a1)
        as (VVSGROWS2 & VVSRANGE2 & ENVVVS2 & EXTGROWS2 & VAR2 & RIR2 & VVSVALID2 & FV2 & NID2); eauto.

      erewrite same_env_same_fst in H6; eauto.

      edestruct H0 as (IDA2 & W1I2 & W2I2); eauto using valid_var_sact_incr.
      generalize (get_rule_information_aux_same_vm _ _ _ _ _ _ _ _ _ _ _ _ H6 Heqp4). intro SVM2.
      edestruct get_rule_information_aux_env_grows with (ua:=a2)
        as (VVSGROWS3 & VVSRANGE3 & ENVVVS3 & EXTGROWS3 & VAR3 & RIR3 & VVSVALID3 & FV3 & NID3); eauto using valid_var_sact_incr.
      split; eauto.
      erewrite <- same_env_same_fst ; eauto.
      
      repeat (refine (conj _ _)).
      + eapply interp_fact_change_vvs. 3: eauto. all: eauto.
        intros. rewrite list_assoc_set_not_before. auto. intro IN.
        eapply vvs_range_in_fst in IN; eauto. lia.
      + eapply write_log_interpretable_change_vvs. 3: eauto. all: eauto.
        intros. rewrite list_assoc_set_not_before. auto. intro IN.
        eapply vvs_range_in_fst in IN; eauto. lia.
      + eapply write_log_interpretable_change_vvs. 3: eauto. all: eauto.
        intros. rewrite list_assoc_set_not_before. auto. intro IN.
        eapply vvs_range_in_fst in IN; eauto. lia.
    - 

        

        eapply interp_fact_change_vvs. 3: eauto. all: eauto.
        intros. rewrite list_assoc_set_not_before. auto. intro IN.
        eapply vvs_range_in_fst in IN; eauto. lia.


      
      split; eauto.
      constructor.
      apply list_assoc_none_unknown_key in Heqo0. congruence.
    - inv IA. inv GRIA. split; eauto. constructor.
    - repeat destr_in GRIA. inv GRIA. inv WUKV.
      eapply H in Heqp; eauto. rewrite Heqp. reflexivity.
      eapply get_rule_information_aux_env_grows in Heqp; eauto.
      destruct Heqp as (VVSGROWS1 & VVSRANGE1 & ENVVVS1 & EXTGROWS1 & VAR1 & RIR1 & VVSVALID1 & FAILVALID1 & NID1).

  Qed.

  Lemma get_rule_information_aux_failure_condition_correct:
    forall
      (ua: sact) (env: list (string * nat)) (guard: sact)
      (rir: rule_information_raw) (nid: nat)
      v env' vvs fail_cond rir' nid'
      vvs0

      (WUKV: wf_sact_known_vars (map fst env) ua)
      (ENVVVS: forall x y, In (x,y) env -> In y (map fst vvs0))
      (RNGVVS: vvs_range vvs0 nid)
      (VVSVALID: forall v a, In (v, a) vvs0 -> forall v' , var_in_sact a v' -> var_lt v' v)
      (RIRRNG: wf_rir rir nid)
      (GUARDVALID: valid_vars_sact guard nid)

      (GRIA: get_rule_information_aux ua env vvs0 guard rir nid = (v, env', vvs, fail_cond, rir', nid'))
      (REnv: Env reg_t)
      (r: env_t REnv (fun _ => val))
      (sigma: ext_fn_t -> val -> val)
      Gamma sched_log action_log
      (FAILCOND_TRUE: interp_fact vvs rir' fail_cond (Bits 1 [true])),
      UntypedSemantics.interp_daction
        r sigma Gamma
        sched_log action_log ua = None.
  Proof.
    intros ua. pattern ua.
    eapply daction_ind'; simpl; intros; eauto.
    - destr_in GRIA; inv GRIA. dependent destruction FAILCOND_TRUE.
      inv WUKV.
      apply list_assoc_none_unknown_key in Heqo. congruence.
    - inv GRIA. dependent destruction FAILCOND_TRUE.
    - repeat destr_in GRIA. inv GRIA. inv WUKV.
      eapply H in Heqp; eauto. rewrite Heqp. reflexivity.
      eapply get_rule_information_aux_env_grows in Heqp; eauto.
      destruct Heqp as (VVSGROWS1 & VVSRANGE1 & ENVVVS1 & EXTGROWS1 & VAR1 & RIR1 & VVSVALID1 & FAILVALID1 & NID1).


      Lemma interp_fact_change_vvs:
        forall (REnv: Env reg_t) (r: env_t REnv (fun _ => val))
         (sigma: ext_fn_t -> val -> val)
         (vvs1 vvs2: list (nat * (type * sact)))
         (rir: rule_information_raw) a v
         (VVSGROWS: forall x,
             var_in_sact a x ->
             forall y, In (x, y) vvs1 -> In (x, y) vvs2)
        ,
          interp_fact vvs1 rir a v ->
          interp_fact vvs2 rir a v.
      Proof.

      Qed.

      apply list_assoc_in in Heqo.
  Qed.



      

  Record rule_information_raw_ok (r: rule_information_raw) (ua: sact) :=
    {
      rir_read0s_ok:
      forall reg ua', In (reg, ua') (rir_read0s r) ->
                     False;
     
      (* ... *)
    }.


  Lemma get_rule_information_raw_aux:
    forall
      (ua: sact) (env: list (string * nat)) (guard: sact)
      (rir: rule_information_raw) (nid: nat)
      v env' vvs0 vvs fail_cond rir' nid',
      get_rule_information_aux ua env vvs0 guard rir nid = (Some v, env', vvs, fail_cond, rir', nid') ->
      rule_information_raw_ok rir ua ->
      rule_information_raw_ok rir' ua.

  Definition get_rule_information (ua: sact) (nid: nat)
  : rule_information_raw * nat :=
    let '(_, _, vvm, failure, rule_information_raw, nid') :=
      get_rule_information_aux
        ua [] [] const_true
        {| rir_read0s := []; rir_read1s := []; rir_write0s := [];
           rir_write1s := []; rir_extcalls := []; rir_vars := [];
           rir_failure_cond := const_false |}
        nid
    in (
      rule_information_raw <| rir_failure_cond := failure |>
        <| rir_vars := vvm|>,
      nid').

  Lemma get_rule_information_ok:
    forall ua ni r ni',
      get_rule_information ua ni = (r, ni') ->
      rule_information_raw_ok r ua.
  Proof.
  Admitted.

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
      (uand (unot (rir_failure_cond ri1))
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
      ric_extcalls := rir_extcalls r;
      ric_vars := rir_vars r;
      ric_failure_cond := rir_failure_cond r
    |}.


  Record rule_information_clean_ok (r: rule_information_clean) (ua: sact) :=
    {
      (* ... *)
    }.

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
         (* FIXME: uand cond ? *)
        (reg, map (fun wi => {| wcond := wcond wi; wval := wval wi |}) wl'))
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
      <|ric_write1s := prepend_condition_writes cond (ric_write1s ric)|>
      <|ric_extcalls := prepend_condition_extcalls cond (ric_extcalls ric)|>.

  Definition to_negated_cond (cond: option sact) : sact :=
    match cond with
    | Some x => unot x
    | None => const_true
    end.

  Definition integrate_failures (ri: list rule_information_clean) nid
  : list rule_information_clean * nat :=
    fold_left
        (fun '(acc, id') r =>
          let fail_var_name := generate_binding_name id' in
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
