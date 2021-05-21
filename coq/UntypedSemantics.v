(*! Language | Semantics of typed Kôika programs !*)
Require Export Koika.Common Koika.Environments Koika.ULogs Koika.Syntax
        Koika.Syntax.


Ltac destr_in H :=
  match type of H with
  | context[match ?a with _ => _ end] => destruct a eqn:?
  end.

Ltac destr :=
  match goal with
    |- context[match ?a with _ => _ end] => destruct a eqn:?; try congruence
  end.

Ltac inv H :=
  inversion H; try subst; clear H.

Section Interp.
  Context {pos_t var_t fn_name_t reg_t ext_fn_t: Type}.
  Context {reg_t_eq_dec: EqDec reg_t}.
  Context {var_t_eq_dec: EqDec var_t}.

  Inductive val :=
  | Bits (sz:nat) (v: list bool)
  | Enum (sig: enum_sig) (v: list bool)
  | Struct (sig: struct_sig) (v: list val)
  | Array (sig: array_sig) (v: list val).

  Context {Sigma: ext_fn_t -> ExternalSignature}.
  Context {REnv: Env reg_t}.

  Notation Log := (@_ULog val reg_t REnv).

  (* Notation rule := (rule pos_t var_t fn_name_t R Sigma). *)
  Notation uaction := (uaction pos_t var_t fn_name_t reg_t ext_fn_t).
  (* Notation scheduler := (scheduler pos_t rule_name_t). *)

  Definition tcontext (sig: tsig var_t) :=
    context (fun k_tau => val) sig.

  Definition acontext (sig argspec: tsig var_t) :=
    context (fun k_tau => uaction) argspec.

  Section Action.

    Fixpoint ucassoc {sig: tsig var_t} (Gamma: tcontext sig) (k: var_t)
      : option val
      :=
        match Gamma with
        | CtxEmpty => None
        | CtxCons k' v Gamma => if eq_dec k (fst k') then Some v else ucassoc Gamma k
        end.

    Lemma cassoc_ucassoc:
      forall (sig: tsig var_t) (ND: NoDup (map fst sig)) (Gamma: tcontext sig) k,
      forall (m: member k sig), ucassoc Gamma (fst k) = Some (cassoc m Gamma).
    Proof.
      induction Gamma. simpl. intros.
      exfalso. inversion m.
      intros. simpl. destruct eq_dec.
      destruct k, k0; simpl in *. subst.
      inversion m; subst.
      generalize (
          fun nd => member_NoDup (v0, t) (EqDec_pair _ _) nd m (MemberHd _ _)
        ).
      intros. rewrite H. simpl. auto. apply NoDup_map_inv with (f:= fst).
      simpl; auto.
      apply member_In in X. inversion ND. subst. exfalso; apply H1.
      apply in_map_iff. eexists; split. 2: apply X. reflexivity.
      inversion m. subst. congruence. subst.
      generalize (fun nd => member_NoDup k0 (EqDec_pair _ _)
                                         nd m (MemberTl _ _ _ X)).
      intros. rewrite H. simpl. eapply IHGamma. simpl in ND; inversion ND; auto.
      apply NoDup_map_inv with (f:= fst). simpl; auto.
    Qed.

    Fixpoint val_of_value {tau: type} (x: type_denote tau) {struct tau} : val :=
      let val_of_struct_value :=
          (fix val_of_struct_value
               {fields}
               (x: struct_denote fields)
           : list val :=
             match fields return struct_denote fields -> list val with
             | [] => fun _ => []
             | (nm, tau) :: fields =>
               fun '(x, xs) =>
                 val_of_value x :: (val_of_struct_value xs)
             end x) in
      match tau return type_denote tau -> val with
      | bits_t sz => fun bs => Bits sz  (vect_to_list bs)
      | enum_t sig => fun bs => Enum sig (vect_to_list bs)
      | struct_t sig => fun str => Struct sig (val_of_struct_value str)
      | array_t sig => fun v => Array sig (map val_of_value (vect_to_list v))
      end x.

    Fixpoint ubits_of_value (v: val) : list bool :=
      match v with
      | Bits _ bs => bs
      | Enum _ bs => bs
      | Struct _ lv => List.concat (rev (map ubits_of_value lv))
      | Array _ lv => List.concat (rev (map ubits_of_value lv))
      end.

    Lemma ubits_of_value_len:
      forall {tau} (v: type_denote tau) bs,
        ubits_of_value (val_of_value v) = bs ->
        List.length bs = type_sz tau.
    Proof.
      fix IHt 1. destruct tau; simpl; intros; subst.
      apply vect_to_list_length.
      apply vect_to_list_length.
      - revert sig v. destruct sig. simpl.
        induction struct_fields; simpl; intros.
        + subst. reflexivity.
        + destruct a. destruct v. simpl.
          rewrite List.concat_app. simpl.
          rewrite app_length. simpl.
          rewrite IHstruct_fields.
          unfold struct_fields_sz. simpl. f_equal.
          rewrite app_nil_r.
          eapply IHt; eauto.
      - revert sig v. destruct sig. simpl. intros.
        induction array_len; simpl. auto.
        destruct v. simpl.
        rewrite concat_app. rewrite app_length. simpl.
        unfold vect_to_list in IHarray_len. rewrite IHarray_len.
        clear IHarray_len. f_equal. rewrite app_nil_r. eapply IHt. eauto.
    Qed.

    Lemma ubits_of_value_ok:
      forall {tau} (v: type_denote tau) bs,
        ubits_of_value (val_of_value v) = bs ->
        vect_to_list (bits_of_value v) = bs.
    Proof.
      fix IHt 1. destruct tau; simpl; intros; subst; auto.
      - revert sig v. destruct sig. simpl.
        induction struct_fields; simpl; intros.
        + subst. reflexivity.
        + destruct a. destruct v. simpl.
          rewrite List.concat_app. simpl.
          rewrite <- IHstruct_fields. rewrite app_nil_r.
          simpl in *.
          rewrite <- (IHt _ t0 _ eq_refl).
          rewrite <- vect_to_list_app.
          reflexivity.
      - revert sig v. destruct sig. simpl. intros.
        induction array_len; simpl. auto.
        destruct v. simpl.
        rewrite vect_to_list_app. rewrite IHarray_len. clear IHarray_len.
        rewrite concat_app. f_equal. simpl.
        rewrite app_nil_r. eapply IHt. eauto.
    Qed.

    Fixpoint replace {sig: tsig var_t} k (v: val) (Gamma: tcontext sig)
      : tcontext sig
      :=
        match Gamma with
        | CtxEmpty => CtxEmpty
        | CtxCons k0 v0 Gamma =>
          if eq_dec k (fst k0)
          then CtxCons k0 v Gamma
          else CtxCons k0 v0 (replace k v Gamma)
        end.

    Definition bits_split (n: nat) {sz} (v: bits sz)
      : option (bits n * bits (sz - n)).
    Proof.
      destruct (lt_dec n sz). 2: exact None.
      replace sz with (n + (sz - n)) in v. 2: lia.
      destruct (Bits.split v) eqn:?.
      exact (Some (v0, v1)).
    Defined.

    Fixpoint take_drop {A: Type} (n: nat) (l: list A) : option (list A * list A) :=
      match n with
        O => Some ([], l)
      | S n =>
        match l with
          [] => None
        | a::l =>
          let/opt2 l1, l2 := take_drop n l in
          Some (a::l1, l2)
        end
      end.

    Definition take_drop' {A: Type} n (l: list A) :=
      match take_drop n l with
        None => (l,[])
      | Some (l1, l2) => (l1, l2)
      end.

    Fixpoint bits_splitn (nb sz_elt: nat) (bs: list bool)
      : option (list (list bool))
      :=
        match nb with
          O => Some []
        | S nb =>
          let/opt2 hd, rest := take_drop sz_elt bs in
          let/opt tl := bits_splitn nb sz_elt rest in
          Some (hd :: tl)
        end.

    Lemma take_drop_succeeds:
      forall {A:Type} (n: nat) (l: list A) (LT: n <= Datatypes.length l),
      exists la lb,
        take_drop n l = Some (la, lb).
    Proof.
      induction n; simpl; intros; eauto.
      destruct l; simpl in LT. lia.
      destruct (IHn l) as (la & lb & EQ). lia.
      rewrite EQ. simpl.
      eauto.
    Qed.

    Lemma take_drop_spec:
      forall {A:Type} (n: nat) (l la lb: list A),
        take_drop n l = Some (la, lb) ->
        l = la ++ lb /\ List.length la = n /\ List.length lb = List.length l - n.
    Proof.
      induction n; simpl; intros; eauto.
      inversion H; clear H; subst. repeat split; try reflexivity. lia.
      destruct l. congruence.
      destruct (take_drop n l) eqn:EQ; simpl in H; try congruence.
      destruct p. inversion H; clear H; subst.
      apply IHn in EQ. destruct EQ as (EQ1 & EQ2 & EQ3). subst. simpl.
      repeat split; lia.
    Qed.

    Lemma take_drop'_cons:
      forall {A} (l l1 l2: list A) a n,
        take_drop' n l = (l1, l2) ->
        take_drop' (S n) (a::l) = (a::l1, l2).
    Proof.
      unfold take_drop'. simpl. intros. destruct (take_drop n l) eqn:?.
      - destruct p. inversion H; subst. simpl. auto.
      - simpl. inversion H; subst. auto.
    Qed.

    Lemma take_drop'_spec:
      forall {A:Type} (n: nat) (l la lb: list A),
        take_drop' n l = (la, lb) ->
        l = la ++ lb /\ List.length la <= n /\ List.length lb = List.length l - List.length la.
    Proof.
      induction n; simpl; intros; eauto.
      inversion H; clear H; subst. repeat split; try reflexivity. simpl; lia.
      destruct l; simpl in *. unfold take_drop' in H. simpl in *. inversion H; clear H.
      simpl. repeat split; lia.
      destruct (take_drop' n l) as (l1 & l2) eqn:?.
      erewrite take_drop'_cons in H; eauto. inversion H; subst. simpl.
      apply IHn in Heqp. destruct Heqp as (EQ1 & EQ2 & EQ3). subst.
      repeat split; auto. lia.
    Qed.


    Lemma app_eq_inv:
      forall {A:Type} (a b c d: list A),
        a ++ b = c ++ d ->
        List.length a = List.length c ->
        a = c /\ b = d.
    Proof.
      induction a; simpl; intros; eauto.
      - destruct c; simpl in H0; try congruence.
        simpl in *. auto.
      - destruct c; simpl in H0; try congruence.
        simpl in *. inversion H; clear H; subst.
        apply IHa in H3. destruct H3; subst; auto. lia.
    Qed.

    Inductive wt_val: type -> val -> Prop :=
    | wt_bits: forall n bs,
        List.length bs = n ->
        wt_val (bits_t n) (Bits n bs)
    | wt_enum: forall sig bs,
        List.length bs = enum_bitsize sig ->
        wt_val (enum_t sig) (Enum sig bs)
    | wt_struct: forall sig lv,
        Forall2 (fun nt v => wt_val nt v) (map snd (struct_fields sig)) lv ->
        wt_val (struct_t sig) (Struct sig lv)
    | wt_array: forall sig lv,
        Forall (fun v => wt_val (array_type sig) v) lv ->
        List.length lv = array_len sig ->
        wt_val (array_t sig) (Array sig lv).

    Fixpoint size_type (t: type) :=
      match t with
      | bits_t n => 1
      | enum_t sig => 1
      | struct_t sig =>
        1 + list_sum (List.map (fun '(_, t) => size_type t) (struct_fields sig))
      | array_t sig =>
        1 + size_type (array_type sig)
      end.

    Lemma wt_val_ind':
      forall (P : type -> val -> Prop)
             (Hbits: forall (n : nat) (bs : list bool), Datatypes.length bs = n -> P (bits_t n) (Bits n bs))
             (Henum: forall (sig : enum_sig) (bs : list bool),
                 Datatypes.length bs = enum_bitsize sig -> P (enum_t sig) (Enum sig bs))
             (Hstruct: forall (sig : struct_sig) (lv : list val),
                 Forall2 (fun (nt : type) (v : val) => wt_val nt v) (map snd (struct_fields sig)) lv ->
                 Forall2 (fun (nt : type) (v : val) => wt_val nt v -> P nt v) (map snd (struct_fields sig)) lv ->
                 P (struct_t sig) (Struct sig lv))
             (Harray: forall (sig : array_sig) (lv : list val),
                 Forall (fun v : val => wt_val (array_type sig) v) lv ->
                 Forall (fun v : val => wt_val (array_type sig) v -> P (array_type sig) v) lv ->
                 Datatypes.length lv = array_len sig -> P (array_t sig) (Array sig lv)),
      forall (t : type) (v : val), wt_val t v -> P t v.
    Proof.
      intros P Hbits Henum Hstruct Harray t v.
      remember (size_type t).
      revert t v Heqn.
      pattern n.
      eapply Nat.strong_right_induction with (z:=0).
      {
        red. red. intros. subst. tauto.
      } 2: lia.
      intros n0 _ Plt t t0 a Heqn.
      assert (Plt':
                forall t v,
                  size_type t < n0 -> wt_val t v -> P t v
             ).
      {
        intros. eapply Plt. 3: reflexivity. lia. auto. auto.
      } clear Plt.
      rename Plt' into Plt.
      subst.
      inversion Heqn; subst; eauto.
      - eapply Hstruct. eauto.
        revert H.
        simpl in Plt.
        assert (Forall (fun '(n,t) => forall v, wt_val t v -> P t v) (struct_fields sig)).
        {
          revert Plt; clear. destruct sig. simpl.
          induction struct_fields; simpl; intros. constructor.
          constructor; eauto. destruct a; simpl; intros.
          eapply Plt. lia. auto.
          apply IHstruct_fields.
          intros; eapply Plt; eauto. lia.
        }
        clear Heqn. revert H lv. clear Plt.
        destruct sig. simpl. clear.
        induction 1; simpl; intros; eauto. inv H. constructor.
        inv H1.
        constructor; auto. destruct x; simpl in *; eauto.
      - eapply Harray; eauto.
        rewrite Forall_forall. intros x IN WT.
        eapply Plt; eauto.
    Qed.

    Fixpoint size_val (v: val) :=
      match v with
      | Bits _ _ => 1
      | Enum _ _ => 1
      | Struct sig lv => 1 + list_sum (map size_val lv)
      | Array sig lv => 1 + list_sum (map size_val lv)
      end.



    Lemma take_drop_succeeds_eq:
      forall {A:Type} (n: nat) (l: list A) (LT: n = Datatypes.length l),
        take_drop n l = Some (l, []).
    Proof.
      induction n; simpl; intros; eauto.
      destruct l; simpl in LT. reflexivity. lia.
      destruct l; simpl in LT; try lia.
      rewrite IHn; simpl; auto.
    Qed.

    Lemma take_drop_head:
      forall {A} n (l1 l2: list A),
        n = List.length l1 ->
        take_drop n (l1 ++ l2) = Some (l1, l2).
    Proof.
      intros. subst. revert l2.
      induction l1; simpl; intros; subst; eauto.
      rewrite IHl1. simpl. reflexivity.
    Qed.

    Lemma length_concat_same:
      forall {A} (l: list (list A)) sz,
        Forall (fun x => List.length x = sz) l ->
        Datatypes.length (List.concat l) = List.length l * sz.
    Proof.
      induction 1; simpl; intros; eauto.
      rewrite app_length; rewrite IHForall. lia.
    Qed.


    Lemma ubits_of_value_len':
      forall tau v,
        wt_val tau v ->
        List.length (ubits_of_value v) = type_sz tau.
    Proof.
      intros tau v WT.
      pattern tau, v.
      eapply wt_val_ind'; simpl; intros; eauto.
      - revert sig lv H0 H. destruct sig. simpl.
        induction struct_fields; simpl; intros.
        + inv H0. reflexivity.
        + inv H0. inv H. simpl.
          rewrite concat_app, app_length. simpl.
          rewrite app_nil_r. rewrite H3; auto.
          erewrite IHstruct_fields. reflexivity. eauto. auto.
      - rewrite Bits.rmul_correct. erewrite length_concat_same.
        rewrite rev_length. rewrite map_length. rewrite H1. reflexivity.
        rewrite Forall_forall in *.
        intros x IN. subst.
        apply In_rev in IN.
        rewrite in_map_iff in IN. destruct IN as (x0 & EQ & IN); subst.
        eapply H0. auto. eauto.
    Qed.

    Lemma bits_splitn_concat:
      forall sz l n,
        Forall (fun l => List.length l = sz) l ->
        List.length l = n ->
        bits_splitn n sz (List.concat l) = Some l.
    Proof.
      intros. subst.
      induction H; simpl; intros; auto.
      rewrite take_drop_head; auto. simpl.
      rewrite IHForall. simpl. reflexivity.
    Qed.


    Fixpoint uvalue_of_bits {tau: type} (bs: list bool) {struct tau}: option val :=
      let uvalue_of_struct_bits :=
          (fix uvalue_of_struct_bits
               {fields: list (string * type)}
               (bs: list bool)
           : option (list val) :=
             match fields with
             | [] => Some []
             | (nm, tau) :: fields =>
               let/opt2 b0, b1 := take_drop (List.length bs - type_sz tau) bs in
               let/opt tl := uvalue_of_struct_bits (fields:=fields) b0 in
               let/opt hd := uvalue_of_bits (tau:=tau) b1 in
               Some ( hd :: tl)
             end) in
      let uvalue_of_list_bits tau :=
          fix uvalue_of_list_bits (l : list (list bool))
          : option (list val)
            :=
              match l with
              | [] => Some []
              | hd::tl =>
                let/opt hd := uvalue_of_bits (tau:=tau) hd in
                let/opt tl := uvalue_of_list_bits tl in
                Some (hd::tl)
              end in
      match tau with
      | bits_t _ => Some (Bits (Datatypes.length bs) bs)
      | enum_t sig =>
        let/opt2 b0, b1 := take_drop (enum_bitsize sig) bs in
        (* TODO check b1 is empty ? *)
        Some (Enum sig b0)
      | struct_t sig =>
        let/opt lv := uvalue_of_struct_bits (fields:=struct_fields sig) bs in
        Some (Struct sig lv)
      | array_t sig =>
        let/opt lbs := bits_splitn (array_len sig)
                                   (type_sz (array_type sig)) bs in
        let/opt lv := uvalue_of_list_bits (array_type sig) (rev lbs) in
        Some (Array sig lv)
      end
    .


    Lemma uvalue_of_bits_val:
      forall tau v,
        wt_val tau v ->
        uvalue_of_bits (tau:=tau) (ubits_of_value v) =
        Some v.
    Proof.
      intros tau v WT.
      pattern tau, v.
      eapply wt_val_ind'; simpl; intros; eauto.
      - congruence.
      - rewrite take_drop_succeeds_eq; simpl; auto.
      - revert sig lv H H0. destruct sig. simpl.
        induction struct_fields; simpl; intros.
        + inv H. reflexivity.
        + inv H. inv H0. destruct a. simpl in *.
          rewrite concat_app, app_length. simpl. 
          rewrite app_nil_r.
          erewrite ubits_of_value_len'. 2: eauto.
          rewrite take_drop_head. 2: lia. simpl.
          generalize (IHstruct_fields l' H5 H7). intro A.
          match type of A with
            context[ let/opt _ := ?a in _ ] => destruct a eqn:?
          end; simpl in *; try congruence.
          rewrite H4. simpl. inv A; auto. auto.
      -
        assert (Forall (fun v => wt_val (array_type sig) v /\ uvalue_of_bits (tau:= array_type sig) (ubits_of_value v) = Some v) lv).
        {
          rewrite Forall_forall in *; simpl; intros.
          split; eauto.
        }
        clear H H0.

        rewrite bits_splitn_concat.
        simpl.
        rewrite rev_involutive.
        cut ((fix uvalue_of_list_bits (l : list (list bool)) : option (list val) :=
                match l with
                | [] => Some []
                | hd :: tl =>
                  let/opt hd0 := uvalue_of_bits (tau:=array_type sig) hd
                  in (let/opt tl0 := uvalue_of_list_bits tl in Some (hd0 :: tl0))
                end) ((map ubits_of_value lv)) = Some lv).
        intro A; rewrite A. simpl. reflexivity.
        revert H1 H2. generalize lv (array_len sig). clear.
        intros l n EQ. subst. revert l.
        induction l; simpl; intros; eauto.
        inv H2. destruct H1. rewrite H0. simpl.
        rewrite IHl. simpl. auto. auto.
        rewrite Forall_forall in *. intros x IN.
        apply In_rev in IN.
        rewrite in_map_iff in IN. destruct IN as (xx & EQ & IN). subst.
        erewrite ubits_of_value_len'. eauto.
        apply H2. auto. rewrite rev_length, map_length; auto.
    Qed.

    Lemma wt_val_of_value:
      forall (tau: type) (v: tau),
        wt_val tau (val_of_value v).
    Proof.
      fix IHt 1. destruct tau; simpl; intros.
      - constructor. rewrite vect_to_list_length. auto.
      - constructor. rewrite vect_to_list_length. auto.
      - eapply wt_struct.
        revert v. generalize (struct_fields sig).
        induction l; simpl; intros; eauto.
        destruct a. destruct v. simpl. constructor. apply IHt.
        eauto.
      - eapply wt_array.
        rewrite Forall_forall. intros x IN.
        rewrite in_map_iff in IN.
        destruct IN as (xx & EQ & IN). subst.
        apply IHt.
        rewrite map_length.
        rewrite vect_to_list_length. auto.
    Qed.


    Lemma uvalue_of_bits_val':
      forall tau v,
        uvalue_of_bits (tau:=tau) (ubits_of_value (val_of_value (tau:=tau) v)) =
        Some (val_of_value (tau:=tau) v).
    Proof.
      intros.
      apply uvalue_of_bits_val.
      apply wt_val_of_value.
    Qed.

    Locate CircuitPrimSpecs.sigma1.

    Compute vect_of_list [true; true; false].

    Import PrimUntyped.
    Definition usigma1' (fn: PrimUntyped.ubits1) (bs: list bool) : option (list bool) :=
      match fn with
      | UNot => Some (List.map negb bs)
      | USExt w =>
        let msb := List.last bs false in
        Some (bs ++ List.repeat msb (w - List.length bs))
      | UZExtL w =>
        Some (bs ++ List.repeat false (w - List.length bs))
      | UZExtR w =>
        Some (List.repeat false (w - List.length bs) ++ bs)
      | URepeat times =>
        Some (List.concat (List.repeat bs times))
      | USlice ofs w =>
        let '(_, bs) := take_drop' ofs bs in
        let '(bs, _) := take_drop' w bs in
        Some (bs ++ List.repeat false (w - List.length bs))
      end.

    Definition usigma1 fn v : option val :=
      match v with
        Bits _ bs =>
        let/opt res := usigma1' fn bs in
        Some (Bits (List.length res) res)
      | _ => None
      end.

    Fixpoint get_field_struct (s: list (string * type)) (lv: list val) f : option val :=
      match s, lv with
      | (n, _)::s, a::lv =>
        if eq_dec n f
        then Some a
        else get_field_struct s lv f
      | _, _ => None
      end.


    Fixpoint find_field_offset_right (s: list (string * type)) f : option (nat * nat) :=
      match s with
      | (n, t)::s =>
        if eq_dec f n
        then
          Some (struct_fields_sz s, type_sz t)
        else
          find_field_offset_right s f
      | [] => None
      end.

    Definition get_field (s: val) f : option val :=
      match s with
        Struct sig lv =>
        get_field_struct (struct_fields sig) lv f
      | _ => None
      end.

    Definition sigma1 (fn: PrimUntyped.ufn1) : val -> option val :=
      match fn with
      | PrimUntyped.UDisplay fn =>
        match fn with
        | PrimUntyped.UDisplayUtf8 => fun _ => Some (Bits 0 [])
        | PrimUntyped.UDisplayValue _ => fun _ => Some (Bits 0 [])
        end
      | PrimUntyped.UConv fn =>
        match fn with
        | PrimUntyped.UPack => fun v =>
                                 let bs := ubits_of_value v in
                                 Some (Bits (List.length bs) bs)
        | PrimUntyped.UUnpack tau =>
          fun bs =>
            match bs with
            | Bits _ bs => let/opt v := uvalue_of_bits (tau:=tau) bs in Some v
            | _ => None
            end
        | PrimUntyped.UIgnore => fun _ => Some (Bits 0 [])
        end
      | PrimUntyped.UBits1 fn => usigma1 fn
      | PrimUntyped.UStruct1 (PrimUntyped.UGetField f) =>
        fun v => get_field v f
      | PrimUntyped.UStruct1 (UGetFieldBits sig f) =>
        fun v =>
          let/opt2 ofs, sz := find_field_offset_right (struct_fields sig) f in
          usigma1 (USlice ofs sz) v
      | PrimUntyped.UArray1 (PrimUntyped.UGetElement idx) =>
        fun v =>
          match v with
          | Array sig l =>
            List.nth_error l idx
          | _ => None
          end
      | PrimUntyped.UArray1 (PrimUntyped.UGetElementBits sig idx) =>
        fun v =>
          usigma1 (USlice (element_sz sig * (array_len sig - S idx)) (element_sz sig)) v
      end.


    Lemma uvalue_of_bits_val_of_value:
      forall (tau: type) (v: vect bool (type_sz tau)),
        uvalue_of_bits (tau:=tau) (vect_to_list v) = Some (val_of_value (value_of_bits v)).
    Proof.
      intros; rewrite <- uvalue_of_bits_val'. f_equal.
      erewrite <- ubits_of_value_ok. 2: eauto.
      rewrite bits_of_value_of_bits. auto.
    Qed.

    Lemma repeat_bits_const:
      forall x n,
        repeat x n = vect_to_list (Bits.const n x).
    Proof.
      induction n; simpl; auto.
      rewrite IHn. reflexivity.
    Qed.

    Lemma last_nth:
      forall {A} d (l: list A),
        last l d = nth (List.length l - 1) l d.
    Proof.
      induction l; simpl; intros; eauto.
      destr. simpl. auto.
      rewrite IHl. simpl. rewrite Nat.sub_0_r. reflexivity.
    Qed.

    Lemma bits_nth_list:
      forall s (v: vect bool s) idx,
        Bits.nth v idx = nth (index_to_nat idx) (vect_to_list v) false.
    Proof.
      induction s; intros. simpl in idx; easy.
      unfold Bits.nth. destr. simpl. auto. fold @vect_nth.
      rewrite IHs. destruct v.  simpl. reflexivity.
    Qed.

    Lemma msb_spec:
      forall s (v: bits s),
        Bits.msb v = last (vect_to_list v) false.
    Proof.
      unfold Bits.msb. intros.
      destr. destruct v. reflexivity.
      rewrite vect_last_nth.
      rewrite last_nth. rewrite vect_to_list_length.
      simpl Nat.sub.
      rewrite Nat.sub_0_r.
      rewrite bits_nth_list. f_equal.
      apply index_to_nat_of_nat.
      apply index_of_nat_largest.
    Qed.


    Lemma vect_extend_end_firstn:
      forall x s' (v: bits (Nat.min x s')) d,
        vect_to_list (vect_extend_end_firstn v d) =
        vect_to_list (vect_extend_end v x d).
    Proof.
      unfold vect_extend_end_firstn.
      intros. rewrite vect_to_list_eq_rect. auto.
    Qed.

    Lemma vect_to_list_cons:
      forall {A: Type} e s (v: vect A s),
        vect_to_list (e::v)%vect = e:: vect_to_list v.
    Proof.
      reflexivity.
    Qed.

    Lemma vect_firstn_to_list:
      forall s (v: bits s) n,
        vect_to_list (vect_firstn n v) = fst (take_drop' n (vect_to_list v)).
    Proof.
      induction s; simpl; intros. simpl in *. destruct v. destr; reflexivity.
      destr. reflexivity.
      erewrite <- vect_to_list_eq_rect.
      Unshelve.
      3: replace (Nat.min (S n0) (S s)) with (S (Nat.min n0 s)); reflexivity.
      simpl.
      rewrite vect_to_list_cons.
      rewrite IHs.
      destruct v. simpl.
      cbn. unfold take_drop'. simpl. unfold vect_to_list.
      destr. destruct p. simpl. reflexivity.
      simpl. reflexivity.
    Qed.

    Lemma vect_skipn_to_list:
      forall s (v: bits s) n,
        vect_to_list (vect_skipn n v) = snd (take_drop' n (vect_to_list v)).
    Proof.
      induction s; simpl; intros. simpl in *. destruct v. destr; reflexivity.
      destr. reflexivity.
      rewrite IHs.
      unfold take_drop'.
      destruct v. simpl.
      cbn. unfold vect_to_list.
      destr. destruct p. simpl. reflexivity.
      simpl. reflexivity.
    Qed.

    Lemma take_drop'_spec2:
      forall {A:Type} (n: nat) (l la lb: list A),
        take_drop' n l = (la, lb) ->
        l = la ++ lb /\
        List.length la = Nat.min n (List.length l).
    Proof.
      induction n; simpl; intros; eauto.
      inversion H; clear H; subst. repeat split; try reflexivity.
      destruct l; simpl in *. unfold take_drop' in H. simpl in *. inversion H; clear H.
      simpl. repeat split; lia.
      destruct (take_drop' n l) as (l1 & l2) eqn:?.
      erewrite take_drop'_cons in H; eauto. inv H. simpl.
      apply IHn in Heqp. destruct Heqp as (EQ1 & EQ2). subst.
      repeat split; auto.
    Qed.

    Lemma struct_fields_sz_skipn:
      forall n f,
        struct_fields_sz (skipn n f) <= struct_fields_sz f.
    Proof.
      induction n; simpl; intros; eauto. destr. auto.
      etransitivity. apply IHn. unfold struct_fields_sz. simpl. lia.
    Qed.
    Lemma field_offset_right_le:
      forall sig s,
        field_offset_right sig s <= struct_sz sig.
    Proof.
      unfold field_offset_right, struct_sz.
      simpl type_sz.
      intros; apply struct_fields_sz_skipn.
    Qed.

    Lemma find_field_offset_right_spec:
      forall f sig (i: index (List.length (struct_fields sig))),
        PrimTypeInference.find_field sig f = Success i ->
        find_field_offset_right (struct_fields sig) f = Some (field_offset_right sig i, field_sz sig i).
    Proof.
      intros f sig i FF.
      unfold PrimTypeInference.find_field in FF. unfold opt_result in FF.
      destr_in FF; inv FF.
      revert i Heqo. simpl. destruct sig. simpl. clear.
      induction struct_fields; intros; eauto. easy.
      simpl. destruct a. simpl in *.
      destr_in Heqo.
      * inv Heqo. f_equal.
      * destr_in Heqo; inv Heqo.
        erewrite IHstruct_fields; eauto.
        f_equal.
    Qed.

    
    Lemma usigma1_correct:
      forall ufn fn,
        PrimTypeInference.tc1 ufn (arg1Sig (PrimSignatures.Sigma1 fn)) = Success fn ->
        forall (arg: arg1Sig (PrimSignatures.Sigma1 fn)) ret,
          PrimSpecs.sigma1 fn arg = ret ->
          sigma1 ufn (val_of_value arg) = Some (val_of_value ret).
    Proof.
      destruct ufn; simpl; intros.
      - destruct fn.
        + destr_in H; try congruence. inv H. simpl in *. inv Heqr. subst. reflexivity.
        + subst. inv H.
          revert arg. rewrite <- H1. simpl. 
          intro arg. reflexivity.
      - destruct fn.
        + inv H. revert arg. rewrite <- H2. simpl.
          intros. f_equal.
          erewrite ubits_of_value_len; eauto. f_equal.
          erewrite ubits_of_value_ok; eauto.
        + inv H.
          generalize (wt_val_of_value _ arg). simpl. inversion 1; subst.
          rewrite uvalue_of_bits_val_of_value. simpl. auto.
        + inv H. revert arg. rewrite <- H2. simpl.
          intros. f_equal.
      - subst. destr_in H. inv H. simpl in *. inv Heqr.
        revert arg. rewrite <- H0. simpl. destruct fn; simpl in *; intros.
        + rewrite map_length. rewrite vect_to_list_length. f_equal.
          f_equal. rewrite <- vect_to_list_map. f_equal.
        + f_equal. f_equal.
          * rewrite app_length.
            rewrite repeat_length. rewrite vect_to_list_length. lia.
          * unfold Bits.extend_end. simpl.
            rewrite vect_to_list_eq_rect.
            rewrite vect_to_list_app. f_equal.
            rewrite vect_to_list_length.
            rewrite repeat_bits_const. f_equal. f_equal.
            rewrite msb_spec; auto.
        + f_equal. f_equal.
          * rewrite app_length.
            rewrite repeat_length. rewrite vect_to_list_length. lia.
          * unfold Bits.extend_end. simpl.
            unfold eq_rect.
            refine (match vect_extend_end_cast s width with
                    | eq_refl => _
                    end).
            rewrite vect_to_list_app. f_equal.
            rewrite vect_to_list_length.
            rewrite repeat_bits_const. f_equal.
        + f_equal. f_equal.
          * rewrite app_length.
            rewrite repeat_length. rewrite vect_to_list_length. lia.
          * unfold Bits.extend_beginning. simpl.
            unfold eq_rect.
            refine (match vect_extend_beginning_cast s width with
                    | eq_refl => _
                    end).
            rewrite vect_to_list_app. f_equal.
            rewrite vect_to_list_length.
            rewrite repeat_bits_const. f_equal.
        + f_equal. f_equal.
          * erewrite length_concat_same.
            rewrite repeat_length. reflexivity.
            rewrite Forall_forall; intros x IN.
            apply repeat_spec in IN. subst. rewrite vect_to_list_length. lia.
          * induction times; simpl; auto.
            rewrite vect_to_list_app. f_equal. eauto.
        + destruct (take_drop' offset (vect_to_list arg)) as (l1 & l2) eqn:Heq1.
          destruct (take_drop' width l2) as (l3 & l4) eqn:Heq2. simpl.
          f_equal. f_equal.
          apply take_drop'_spec in Heq2.
          apply take_drop'_spec in Heq1.
          intuition subst.
          rewrite app_length.
          rewrite repeat_length. lia.
          unfold Bits.slice.

          rewrite vect_extend_end_firstn.
          unfold Bits.extend_end.
          rewrite vect_to_list_eq_rect.
          rewrite vect_to_list_app.
          rewrite vect_firstn_to_list.
          rewrite vect_skipn_to_list.
          rewrite Heq1. simpl. rewrite Heq2. simpl.
          rewrite <- repeat_bits_const.
          f_equal. f_equal. f_equal.

          apply take_drop'_spec2 in Heq2. destruct Heq2 as (Heq21 & Heq22). rewrite Heq22.
          apply take_drop'_spec2 in Heq1. destruct Heq1 as (Heq11 & Heq12).
          cut (List.length l2 = s - List.length l1). intro A; rewrite A. rewrite Heq12.
          rewrite vect_to_list_length. lia.
          erewrite <- (vect_to_list_length (sz:=s)). rewrite Heq11.
          rewrite app_length. lia.
        + inv H.
      - destr_in H.
        + repeat destr_in H; inv H.
          simpl in Heqr. clear Heqr. simpl in arg.
          simpl PrimSpecs.sigma1.
          simpl.
          unfold PrimTypeInference.find_field in Heqr0. unfold opt_result in Heqr0.
          destr_in Heqr0; inv Heqr0.
          revert s0 Heqo arg. destruct s. simpl. clear.
          induction struct_fields; intros; eauto. easy.
          destruct a. destruct arg.
          Opaque eq_dec.
          simpl. simpl in Heqo.
          destr_in Heqo. inv Heqo. simpl in *. rewrite Heqs2. auto.
          destr.  subst. congruence.
          destr_in Heqo; inv Heqo.
          erewrite IHstruct_fields; eauto. reflexivity.
        + destr_in H; inv H.
          simpl PrimSpecs.sigma1.
          simpl.
          erewrite find_field_offset_right_spec; eauto. simpl. destr. destr. simpl. f_equal.
          unfold take_drop' in Heqp.
          edestruct (@take_drop_succeeds) as (la & lb & EQ).
          2: rewrite EQ in Heqp.
          rewrite vect_to_list_length.

          apply field_offset_right_le.
          f_equal.
          rewrite app_length. rewrite repeat_length.
          cut (List.length l1 <= field_sz sig s). lia.
          apply take_drop'_spec in Heqp0. intuition.

          unfold Bits.slice. rewrite vect_extend_end_firstn.
          unfold Bits.extend_end.
          rewrite vect_to_list_eq_rect.
          rewrite vect_to_list_app.
          rewrite vect_firstn_to_list.
          rewrite vect_skipn_to_list.
          rewrite <- repeat_bits_const.
          unfold take_drop' at 2. rewrite EQ. simpl.
          inv Heqp. rewrite Heqp0. simpl. f_equal. f_equal.
          eapply take_drop'_spec2 in Heqp0. destruct Heqp0.
          rewrite H0.
          clear H0.
          eapply take_drop_spec in EQ. intuition.
          rewrite H3. rewrite vect_to_list_length. reflexivity.
      - destr_in H.
        + repeat destr_in H; inv H. simpl in *.
          rewrite <- vect_nth_map. rewrite <- vect_to_list_map.
          rewrite <- vect_to_list_nth. f_equal.
          unfold PrimTypeInference.check_index in Heqr0.
          unfold opt_result in Heqr0. destr_in Heqr0; inv Heqr0.
          symmetry; apply index_to_nat_of_nat. auto.
        + destr_in H; inv H. simpl in *. destr. destr. simpl.
          unfold PrimTypeInference.check_index in Heqr.
          unfold opt_result in Heqr. destr_in Heqr; inv Heqr.
          apply index_to_nat_of_nat in Heqo. subst.
          unfold take_drop' in *.
          edestruct @take_drop_succeeds as (la & lb & EQ). 2: rewrite EQ in Heqp.
          rewrite vect_to_list_length. unfold array_sz. simpl. rewrite Bits.rmul_correct.
          rewrite Nat.mul_comm. unfold element_sz. apply Nat.mul_le_mono_r.
          cut (index_to_nat s < array_len sig). lia. eapply lt_le_trans.
          apply index_to_nat_bounded. lia.
          inv Heqp.
          generalize EQ; intro EQs.
          apply take_drop_spec in EQ. intuition.
          edestruct @take_drop_succeeds as (la & lb & EQ'). 2: rewrite EQ' in Heqp0.
          rewrite H2, vect_to_list_length. unfold array_sz. simpl. rewrite Bits.rmul_correct.
          unfold element_sz.
          (* rewrite Nat.mul_comm. unfold element_sz. apply Nat.mul_le_mono_r. *)
          cut (index_to_nat s < array_len sig). nia.
          apply index_to_nat_bounded.
          f_equal. f_equal.
          rewrite app_length, repeat_length. 
          inv Heqp0.
          apply take_drop_spec in EQ'. intuition.
          inv Heqp0.
          unfold Bits.slice. rewrite vect_extend_end_firstn.
          unfold Bits.extend_end.
          rewrite vect_to_list_eq_rect.
          rewrite vect_to_list_app.
          rewrite vect_firstn_to_list.
          rewrite vect_skipn_to_list.
          rewrite <- repeat_bits_const.
          unfold take_drop' at 2.
          unfold element_offset_right. rewrite Bits.rmul_correct.
          rewrite Nat.mul_comm. rewrite EQs. simpl.
          unfold take_drop'; rewrite EQ'; simpl. f_equal. f_equal.
          eapply take_drop_spec in EQ'. intuition. rewrite H4.
          rewrite Nat.min_l. auto.
          unfold element_sz. unfold array_sz. simpl.
          rewrite Bits.rmul_correct. rewrite Nat.mul_comm.
          rewrite <- Nat.mul_sub_distr_l.
          cut (1 <= array_len sig - (array_len sig - S (index_to_nat s))). nia.
          generalize (index_to_nat_bounded s). lia.
    Qed.

    Definition enum_sig_eq_dec (s1 s2: enum_sig) : {s1 = s2} + {s1 <> s2}.
    Proof.
      destruct s1, s2; simpl.
      destruct (eq_dec enum_name enum_name0). 2: right; intro A; inv A; congruence.
      destruct (eq_dec enum_size enum_size0). 2: right; intro A; inv A; congruence.
      destruct (eq_dec enum_bitsize enum_bitsize0). 2: right; intro A; inv A; congruence.
      subst.
      destruct (eq_dec enum_members enum_members0).
      destruct (eq_dec enum_bitpatterns enum_bitpatterns0).
      left; subst; reflexivity. right; intro A; inv A.
      apply Eqdep_dec.inj_pair2_eq_dec in H1. 2: apply eq_dec.
      apply Eqdep_dec.inj_pair2_eq_dec in H1. 2: apply eq_dec.
      congruence.
      right; intro A; inv A.
      apply Eqdep_dec.inj_pair2_eq_dec in H0. 2: apply eq_dec. congruence.
    Defined.


    Definition struct_sig_eq_dec (s1 s2: struct_sig) : {s1 = s2} + {s1 <> s2}.
    Proof.
      destruct s1, s2; simpl.
      destruct (eq_dec struct_name struct_name0). 2: right; intro A; inv A; congruence.
      destruct (eq_dec struct_fields struct_fields0). 2: right; intro A; inv A; congruence.
      left; subst; reflexivity.
    Defined.

    Lemma strong_ind_type:
      forall (P: nat -> Type)
             (IH: forall n, (forall m, m < n -> P m) -> P n),
      forall n, forall m, m <= n -> P m.
    Proof.
      induction n. intros. apply IH. lia.
      intros.
      destruct (le_dec m n); eauto.
      assert (m = S n) by lia. clear H n0. subst.
      apply IH. intros. apply IHn; auto. lia.
    Qed.

    Lemma val_ind':
      forall (P : val -> Type)
             (Hbits: forall (n : nat) (bs : list bool), P (Bits n bs))
             (Henum: forall (sig : enum_sig) (bs : list bool),
                 P (Enum sig bs))
             (Hstruct: forall (sig : struct_sig) (lv : list val),
                 (forall x, In x lv -> P x) ->
                 P (Struct sig lv))
             (Harray: forall (sig : array_sig) (lv : list val),
                 (forall x, In x lv -> P x) ->
                 P (Array sig lv)),
      forall (v : val), P v.
    Proof.
      intros P Hbits Henum Hstruct Harray v.
      remember (size_val v).
      revert v Heqn.
      pattern n.
      eapply strong_ind_type. 2: reflexivity.
      intros n0 Plt v Heqn.
      assert (Plt':
                forall v,
                  size_val v < n0 -> P v
             ).
      {
        intros. eapply Plt. 2: reflexivity. lia.
      } clear Plt.
      rename Plt' into Plt.
      subst.
      destruct v; eauto.
      - eapply Hstruct.
        intros.
        eapply Plt. simpl.
        clear Plt. revert x v H.
        induction v; simpl; intros; eauto. easy.
        destruct H; subst; eauto. lia.
        eapply lt_le_trans. apply IHv; auto. lia.
      - eapply Harray.
        intros.
        eapply Plt. simpl.
        clear Plt. revert x v H.
        induction v; simpl; intros; eauto. easy.
        destruct H; subst; eauto. lia.
        eapply lt_le_trans. apply IHv; auto. lia.
    Qed.

    Definition list_eq_dec' {A: Type} (l1 l2: list A) (Aeq: forall x y, In x l1 -> {x = y} + {x <> y}): {l1 = l2} + {l1 <> l2}.
    Proof.
      revert l1 Aeq l2; induction l1; simpl; intros.
      - destruct l2. left; reflexivity. right; intro B; inv B.
      - destruct l2. right; congruence.
        destruct (Aeq a a0). simpl; auto. subst.
        2: right; intro B; inv B; congruence.
        edestruct (fun pf => IHl1 pf l2). intros; eauto.
        subst. left; reflexivity.
        right; intro B; inv B; congruence.
    Defined.

    Definition val_eq_dec (v1 v2: val) : {v1 = v2} + {v1 <> v2}.
    Proof.
      revert v2.
      pattern v1. revert v1.
      eapply val_ind'; simpl; intros.
      - destruct v2; try (right; intro A; inv A; congruence).
        destruct (eq_dec n sz); try (right; intro A; inv A; congruence).
        destruct (eq_dec bs v); try (right; intro A; inv A; congruence).
        subst; left; reflexivity.
      - destruct v2; try (right; intro A; inv A; congruence).
        destruct (enum_sig_eq_dec sig sig0); try (right; intro A; inv A; congruence).
        destruct (eq_dec bs v); try (right; intro A; inv A; congruence).
        subst; left; reflexivity.
      - destruct v2; try (right; intro A; inv A; congruence).
        destruct (struct_sig_eq_dec sig sig0); try (right; intro A; inv A; congruence).
        destruct (list_eq_dec' lv v); try (right; intro A; inv A; congruence). eauto.
        left; subst. reflexivity.
      - destruct v2; try (right; intro A; inv A; congruence).
        destruct (eq_dec sig sig0); subst. 2: (right; intro A; inv A; congruence).
        destruct (list_eq_dec' lv v); try (right; intro A; inv A; congruence). eauto.
        left; subst. reflexivity.
    Defined.

    Fixpoint bitwise (f: bool -> bool -> bool) (l1 l2: list bool) {struct l1}: list bool :=
      match l1, l2 with
      | [], [] => []
      | [], l2 => map (fun x => f false x) l2
      | l1, [] => map (fun x => f x false) l1
      | a1::l1, a2::l2 => f a1 a2 :: bitwise f l1 l2
      end.

    Lemma and_correct:
      forall sz (arg1: arg1Sig (PrimSignatures.Sigma2 (PrimTyped.Bits2 (PrimTyped.And sz))))
             (arg2: arg2Sig (PrimSignatures.Sigma2 (PrimTyped.Bits2 (PrimTyped.And sz)))) ret,
        PrimSpecs.sigma2 (PrimTyped.Bits2 (PrimTyped.And sz)) arg1 arg2 = ret ->
        match val_of_value arg1, val_of_value arg2 with
        | Bits _ arg1, Bits _ arg2 =>
          exists sz, Bits sz (bitwise andb arg1 arg2) = (val_of_value ret)
        | _, _ => False
        end.
    Proof.
      simpl. intros. eexists. f_equal. subst.
      revert arg1 arg2.
      induction sz; simpl. reflexivity.
      destruct arg1, arg2. simpl.
      unfold Bits.and in *. simpl.
      rewrite vect_to_list_cons. f_equal. rewrite <- IHsz.
      reflexivity.
    Qed.


    Lemma len_to_list: forall sz (v: bits sz), sz = Datatypes.length (vect_to_list v).
    Proof.
      intros; rewrite vect_to_list_length. reflexivity.
    Defined.

    Lemma vect_to_list_of_list:
      forall (v: list bool),
        vect_to_list (vect_of_list v) = v.
    Proof.
      induction v; simpl; intros. reflexivity.
      rewrite vect_to_list_cons. congruence.
    Qed.

    Lemma vect_of_list_to_list:
      forall sz (v: bits sz),
        vect_of_list (vect_to_list v) = rew [vect bool] (len_to_list sz v) in v.
    Proof.
      intros. apply vect_to_list_inj.
      rewrite vect_to_list_of_list.
      rewrite vect_to_list_eq_rect. reflexivity.
    Qed.


    Lemma vect_to_list_vect_unsnoc:
      forall sz (v: bits (S sz)) b v',
        vect_unsnoc v = (b, v') ->
        vect_to_list v' = removelast (vect_to_list v).
    Proof.
      induction sz; simpl; intros.
      - inv H. destruct v. simpl. reflexivity.
      - destr_in H. inv H.
        rewrite vect_to_list_cons. f_equal.
        erewrite IHsz. 2: eauto. simpl. reflexivity.
    Qed.


    Lemma lsl1:
      forall sz (v: bits sz),
        sz <> 0 ->
        vect_to_list (Bits.lsl1 v) = false :: removelast (vect_to_list v).
    Proof.
      unfold Bits.lsl1. destruct sz. congruence. intros.
      rewrite vect_to_list_cons. f_equal.
      erewrite vect_to_list_vect_unsnoc. 2: apply surjective_pairing.
      reflexivity.
    Qed.

    Lemma lsl1':
      forall sz (v: bits sz),
        vect_to_list (Bits.lsl1 v) = if eq_dec sz O then [] else false :: removelast (vect_to_list v).
    Proof.
      intros. destr.
      subst. destruct v; reflexivity.
      apply lsl1; auto.
    Qed.


    Definition ubits2_sigma (ub: ubits2) (v1 v2: list bool) : list bool :=
      match ub with
      | UAnd => bitwise andb v1 v2
      | UOr => bitwise orb v1 v2
      | UXor => bitwise xorb v1 v2
      | ULsl =>
        let amount := Bits.to_nat (vect_of_list v2) in
        Nat.iter amount (fun v =>
                           if eq_dec (List.length v1) O then [] else false :: removelast v) v1
      | ULsr =>
        let amount := Bits.to_nat (vect_of_list v2) in
        Nat.iter amount (fun v =>
                           if eq_dec (List.length v1) O then [] else tl v ++ [false]) v1
      | UAsr =>
        let amount := Bits.to_nat (vect_of_list v2) in
        Nat.iter amount (fun v =>
                           if eq_dec (List.length v1) O then [] else tl v ++ [last v false]) v1
      | UConcat =>
        v2 ++ v1
      | USel =>
        [List.nth (Bits.to_nat (vect_of_list v2)) v1 false]
      | USliceSubst ofs w =>
        let '(h, _) := take_drop' ofs v1 in
        let '(_, t) := take_drop' (ofs + w) v1 in
        fst (take_drop' (List.length v1) (h ++ v2 ++ t))
      | UIndexedSlice w =>
        let ofs := Bits.to_nat (vect_of_list v2) in
        let '(_, bs) := take_drop' ofs v1 in
        let '(bs, _) := take_drop' w bs in
        (bs ++ List.repeat false (w - Nat.min w (List.length v1 - ofs)))
      | UPlus =>
        vect_to_list (Bits.of_N (List.length v1) (Bits.to_N (vect_of_list v1) + Bits.to_N (vect_of_list v2)))
      | UMinus =>
        vect_to_list (Bits.of_N (List.length v1)
                                (Bits.to_N (Bits.of_N (List.length v1) (Bits.to_N (vect_of_list v1) + Bits.to_N (Bits.neg (vect_of_list v2)))) + Bits.to_N (sz:=List.length v1) Bits.one))

      | UMul =>
        vect_to_list (Bits.of_N (List.length v1 + List.length v2) (Bits.to_N (vect_of_list v1) * Bits.to_N (vect_of_list v2)))
      | UCompare signed c =>
        let sz1 := List.length v1 in
        let sz2 := List.length v2 in
        match eq_dec sz2 sz1 with
        | left pf =>
          let v1 := vect_of_list v1 in
          let v2 := rew [Bits.bits] pf in vect_of_list v2 in
              [((if signed
                 then
                   match c with
                   | cLt =>  Bits.signed_lt
                   | cGt =>  Bits.signed_gt
                   | cLe =>  Bits.signed_le
                   | cGe =>  Bits.signed_ge
                   end
                 else
                   match c with
                   | cLt =>  Bits.unsigned_lt
                   | cGt =>  Bits.unsigned_gt
                   | cLe =>  Bits.unsigned_le
                   | cGe =>  Bits.unsigned_ge
                   end) v1 v2)]
        | _ => []
        end

      end.

    Import PrimTyped.

    Lemma and_correct':
      forall sz (arg1: bits_t sz)
             (arg2: bits_t sz),
        bitwise andb (vect_to_list arg1) (vect_to_list arg2) = vect_to_list (Bits.and arg1 arg2).
    Proof.
      induction sz; simpl. reflexivity.
      destruct arg1, arg2. simpl.
      unfold Bits.and in *. simpl.
      rewrite vect_to_list_cons. f_equal. rewrite <- IHsz.
      reflexivity.
    Qed.


    Lemma or_correct':
      forall sz (arg1: bits_t sz)
             (arg2: bits_t sz),
        bitwise orb (vect_to_list arg1) (vect_to_list arg2) = vect_to_list (Bits.or arg1 arg2).
    Proof.
      induction sz; simpl. reflexivity.
      destruct arg1, arg2. simpl.
      unfold Bits.or in *. simpl.
      rewrite vect_to_list_cons. f_equal. rewrite <- IHsz.
      reflexivity.
    Qed.


    Lemma xor_correct':
      forall sz (arg1: bits_t sz)
             (arg2: bits_t sz),
        bitwise xorb (vect_to_list arg1) (vect_to_list arg2) = vect_to_list (Bits.xor arg1 arg2).
    Proof.
      induction sz; simpl. reflexivity.
      destruct arg1, arg2. simpl.
      unfold Bits.xor in *. simpl.
      rewrite vect_to_list_cons. f_equal. rewrite <- IHsz.
      reflexivity.
    Qed.

    Lemma iter_assoc_spec:
      forall {A:Type} (f: A -> A) n x,
        Nat.iter n f (f x) = f (Nat.iter n f x).
    Proof.
      induction n; simpl; intros; eauto.
      rewrite IHn. auto.
    Qed.
    
    Lemma vect_dotimes_spec:
      forall {A:Type} (f: A -> A) n x,
        vect_dotimes f n x = Nat.iter n f x.
    Proof.
      induction n; simpl; intros. auto.
      rewrite IHn, iter_assoc_spec. auto.
    Qed.

    Lemma vect_to_list_snoc:
      forall sz (v: bits sz) x,
        vect_to_list (vect_snoc x v) = vect_to_list v ++ [x].
    Proof.
      induction sz; simpl; intros; eauto.
      rewrite vect_to_list_cons. f_equal.
      rewrite IHsz. reflexivity.
    Qed.
    
    Lemma lsr1:
      forall sz (v: bits sz),
        sz <> 0 ->
        vect_to_list (Bits.lsr1 v) = tl (vect_to_list v) ++ [false].
    Proof.
      unfold Bits.lsr1. intros. destr.
      rewrite vect_to_list_snoc.
      rewrite <- (vect_cons_hd_tl v) at 2.
      rewrite vect_to_list_cons. simpl. reflexivity.
    Qed.

    Lemma asr1:
      forall sz (v: bits sz),
        sz <> 0 ->
        vect_to_list (Bits.asr1 v) = tl (vect_to_list v) ++ [last (vect_to_list v) false].
    Proof.
      unfold Bits.asr1. intros. destr.
      rewrite vect_to_list_snoc. f_equal.
      rewrite msb_spec. auto.
    Qed.
    
    Lemma iter_list_vect:
      forall sz (v: bits sz) (f: list bool -> list bool) (g: bits sz -> bits sz),
        (forall x, f (vect_to_list x) = vect_to_list (g x)) ->
        forall n,
          Nat.iter n f (vect_to_list v) = vect_to_list (vect_dotimes g n v).
    Proof.
      intros. rewrite vect_dotimes_spec. induction n; simpl; intros; eauto.
      rewrite IHn. apply H.
    Qed.

    Lemma sel:
      forall sz (bs: bits sz) idx,
        vect_to_list (BitFuns.sel bs idx) =
        [List.nth (Bits.to_nat idx) (vect_to_list bs) false].
    Proof.
      unfold BitFuns.sel. intros.
      destr.
      rewrite bits_nth_list. unfold Bits.to_index in Heqo.
      erewrite index_to_nat_of_nat. 2: eauto. reflexivity.
      unfold Bits.to_index in Heqo.
      rewrite nth_overflow. reflexivity.
      rewrite vect_to_list_length.
      apply index_of_nat_none_ge in Heqo. lia.
    Qed.
    Lemma slice_subst:
      forall sz (bs: bits sz) ofs w v,
        vect_to_list (Bits.slice_subst ofs w bs v) =
        let '(h, _) := take_drop' ofs (vect_to_list bs) in
        let '(_, t) := take_drop' (ofs + w) (vect_to_list bs) in
        fst (take_drop' sz (h ++ (vect_to_list v) ++ t)).
    Proof.
      unfold Bits.slice_subst. intros.
      destr. destr.
      rewrite vect_to_list_eq_rect.
      rewrite vect_firstn_to_list. f_equal.
      rewrite ! vect_to_list_app.
      rewrite vect_firstn_to_list. f_equal.
      rewrite Heqp. simpl. f_equal.
      rewrite vect_skipn_to_list. rewrite Heqp0. reflexivity.
    Qed.

    Lemma slice:
      forall sz (bs: bits sz) ofs w,
        vect_to_list (Bits.slice ofs w bs) =
        let '(_, bs) := take_drop' ofs (vect_to_list bs) in
        let '(bs, _) := take_drop' w bs in
        (bs ++ List.repeat false (w - Nat.min w (sz - ofs))).
    Proof.
      intros. unfold Bits.slice. rewrite vect_extend_end_firstn.
      unfold Bits.extend_end.
      rewrite vect_to_list_eq_rect.
      rewrite vect_to_list_app.
      rewrite vect_firstn_to_list.
      rewrite vect_skipn_to_list.
      rewrite <- repeat_bits_const.
      destr. simpl. destr. simpl.
      f_equal.
    Qed.
    Lemma vect_to_list_eq:
      forall sz1 sz2 (v1: bits sz1) (v2: bits sz2) (pf: sz1 = sz2),
        rew [fun x => bits x] pf in v1 = v2 ->
                                    vect_to_list v1 = vect_to_list v2.
    Proof.
      intros. subst. rewrite vect_to_list_eq_rect. auto.
    Qed.

    Lemma bits_map_rew:
      forall sz1 sz2 (v: bits sz1) f (pf: sz1 = sz2),
        Bits.map f (rew [Bits.bits] pf in v) = rew [Bits.bits] pf in (Bits.map f v).
    Proof.
      intros. subst. simpl. auto.
    Qed.

    Lemma cmp:
      forall sz (v1 v2: bits sz) c,
        vect_to_list (BitFuns.bitfun_of_predicate c v1 v2) =
        [c v1 v2].
    Proof.
      unfold BitFuns.bitfun_of_predicate. simpl; intros. reflexivity.
    Qed.
    Lemma lift_comparison_rew:
      forall {A} sz1 sz1' (pf: sz1 = sz1') (pf2: sz1 = sz1') (v1: bits sz1) (v2: bits sz1) (cast: forall sz, bits sz -> A) compare cmp,
        Bits.lift_comparison (cast sz1') compare cmp (rew [Bits.bits] pf in v1) (rew [Bits.bits] pf2 in v2) =
        Bits.lift_comparison (cast sz1) compare cmp v1 v2.
    Proof.
      intros. subst. simpl.
      rewrite (Eqdep_dec.UIP_refl_nat _ pf2). simpl. reflexivity.
    Qed.

    Lemma ubits2_correct:
      forall
        ub b sz1 sz2
        (UB:
           match ub with
           | USel => Sel sz1
           | USliceSubst offset width => SliceSubst sz1 offset width
           | UIndexedSlice width => IndexedSlice sz1 width
           | UAnd => And sz1
           | UOr => Or sz1
           | UXor => Xor sz1
           | ULsl => Lsl sz1 sz2
           | ULsr => Lsr sz1 sz2
           | UAsr => Asr sz1 sz2
           | UConcat => Concat sz1 sz2
           | UPlus => Plus sz1
           | UMinus => Minus sz1
           | UMul => Mul sz1 sz2
           | UCompare signed c => Compare signed c sz1
           end = b)
        (arg1: arg1Sig (PrimSignatures.Sigma2 (PrimTyped.Bits2 b)))
        (arg2: arg2Sig (PrimSignatures.Sigma2 (PrimTyped.Bits2 b))) ret,
        CircuitPrimSpecs.sigma2 b arg1 arg2 = ret ->
        match val_of_value arg1, val_of_value arg2 with
        | Bits _ arg1, Bits _ arg2 =>
          (ubits2_sigma ub arg1 arg2) = (vect_to_list ret)
        | _, _ => False
        end.
    Proof.
      simpl. intros. subst.
      destruct ub; simpl in *.
      apply and_correct'.
      apply or_correct'.
      apply xor_correct'.
      - unfold BitFuns.lsl. unfold Bits.lsl.
        rewrite vect_of_list_to_list. unfold Bits.to_nat; rewrite Bits.to_N_rew.
        apply iter_list_vect.
        intros. rewrite vect_to_list_length. destr. subst. reflexivity.
        rewrite lsl1; auto.
      - unfold BitFuns.lsr, Bits.lsr.
        rewrite vect_of_list_to_list. unfold Bits.to_nat; rewrite Bits.to_N_rew.
        apply iter_list_vect.
        intros. rewrite vect_to_list_length. destr. subst. reflexivity.
        rewrite lsr1; auto.
      - unfold BitFuns.asr, Bits.asr.
        rewrite vect_of_list_to_list. unfold Bits.to_nat; rewrite Bits.to_N_rew.
        apply iter_list_vect.
        intros. rewrite vect_to_list_length. destr. subst. reflexivity.
        rewrite asr1; auto.
      - rewrite vect_to_list_app; auto.
      - rewrite sel.
        rewrite vect_of_list_to_list. unfold Bits.to_nat; rewrite Bits.to_N_rew. auto.
      - rewrite vect_to_list_length.
        rewrite slice_subst. reflexivity.
      - rewrite slice.
        rewrite vect_of_list_to_list. unfold Bits.to_nat; rewrite Bits.to_N_rew.
        destr. destr. f_equal. f_equal. rewrite vect_to_list_length. reflexivity.
      - unfold Bits.plus.
        rewrite ! vect_of_list_to_list.
        rewrite ! Bits.to_N_rew.
        eapply vect_to_list_eq.
        erewrite (f_equal_dep _ (fun x => Bits.of_N x (Bits.to_N arg1 + Bits.to_N arg2))).
        Unshelve. 2: apply vect_to_list_length.
        auto.
      - unfold Bits.minus.
        rewrite ! vect_of_list_to_list.
        rewrite ! Bits.to_N_rew.
        eapply vect_to_list_eq.
        erewrite (f_equal_dep _ (fun x => Bits.of_N x _)).
        Unshelve. 2: apply vect_to_list_length.
        unfold Bits.plus. f_equal.
        f_equal.
        replace (Bits.neg (rew [Bits.bits] len_to_list sz1 arg2 in arg2))
          with (rew [Bits.bits] len_to_list sz1 arg2 in (Bits.neg arg2)).
        rewrite Bits.to_N_rew.
        erewrite <- (f_equal_dep _ (fun x => (Bits.of_N x _))).
        Unshelve. 5: apply len_to_list.
        rewrite Bits.to_N_rew. auto.
        unfold Bits.neg.
        rewrite bits_map_rew. reflexivity.
        erewrite <- Bits.to_N_rew.
        Unshelve. 3: apply vect_to_list_length.
        f_equal.
        apply f_equal_dep.
      - unfold Bits.mul.
        rewrite ! vect_of_list_to_list.
        rewrite ! Bits.to_N_rew.
        eapply vect_to_list_eq.
        erewrite (f_equal_dep _ (fun x => Bits.of_N x (Bits.to_N arg1 * Bits.to_N arg2))).
        Unshelve. 2: rewrite ! vect_to_list_length; auto.
        auto.
      - destr.
        + rewrite ! vect_of_list_to_list.
          rewrite rew_compose.
          transitivity ( vect_to_list
                           (BitFuns.bitfun_of_predicate (if signed
                                                         then
                                                           match c with
                                                           | cLt =>  Bits.signed_lt
                                                           | cGt =>  Bits.signed_gt
                                                           | cLe =>  Bits.signed_le
                                                           | cGe =>  Bits.signed_ge
                                                           end
                                                         else
                                                           match c with
                                                           | cLt =>  Bits.unsigned_lt
                                                           | cGt =>  Bits.unsigned_gt
                                                           | cLe =>  Bits.unsigned_le
                                                           | cGe =>  Bits.unsigned_ge
                                                           end) arg1 arg2)
                       ). 2: repeat destr; reflexivity.
          rewrite cmp. f_equal.
          repeat destr; apply lift_comparison_rew.
        + clear -n. exfalso.
          rewrite ! vect_to_list_length in n. congruence.
    Qed.


    (*   Definition sigma2 (fn: PrimTyped.fbits2) : CSig_denote (CircuitSignatures.CSigma2 fn) := *)
    (*     match fn with *)
    (*     | Sel _ => sel *)
    (*     | SliceSubst _ offset width => Bits.slice_subst offset width *)
    (*     | IndexedSlice _ width => fun bs offset => Bits.slice (Bits.to_nat offset) width bs *)
    (*     | And _ => Bits.and *)
    (*     | Or _ => Bits.or *)
    (*     | Xor _ => Bits.xor *)
    (*     | Lsl _ _ => lsl *)
    (*     | Lsr _ _ => lsr *)
    (*     | Asr _ _ => asr *)
    (*     | Concat _ _ => Bits.app *)
    (*     | Plus _ => Bits.plus *)
    (*     | Minus _ => Bits.minus *)
    (*     | Mul _ _ => Bits.mul *)
    (*     | EqBits _ false => _eq *)
    (*     | EqBits _ true => _neq *)
    (*     | Compare true cLt _ => bitfun_of_predicate Bits.signed_lt *)
    (*     | Compare true cGt _ => bitfun_of_predicate Bits.signed_gt *)
    (*     | Compare true cLe _ => bitfun_of_predicate Bits.signed_le *)
    (*     | Compare true cGe _ => bitfun_of_predicate Bits.signed_ge *)
    (*     | Compare false cLt _ => bitfun_of_predicate Bits.unsigned_lt *)
    (*     | Compare false cGt _ => bitfun_of_predicate Bits.unsigned_gt *)
    (*     | Compare false cLe _ => bitfun_of_predicate Bits.unsigned_le *)
    (*     | Compare false cGe _ => bitfun_of_predicate Bits.unsigned_ge *)
    (*     end. *)

    Fixpoint subst_field (n: nat) (v: val) (s: list val) : option (list val) :=
      match n, s with
      | _, [] => None
      | O, a::r => Some (v::r)
      | S n, a::r => let/opt s := subst_field n v r in Some (a::s)
      end.

    Fixpoint val_of_struct_value'
             (fields : list (string * type))
             (x : struct_denote fields)
             {struct fields} : list val :=
      match fields as fields0 return (struct_denote fields0 -> list val) with
      | [] => fun _ : unit => []
      | p :: fields0 =>
        let (_, tau) as p0 return (snd p0 * struct_denote fields0 -> list val) := p in
        fun '(x0, xs) => val_of_value x0 :: val_of_struct_value' fields0 xs
      end x.

    Lemma val_of_struct_value_rew:
      forall fields x,
        (fix
           val_of_struct_value (fields : list (string * type)) (x : struct_denote fields) {struct
                                                                                             fields} : list val :=
           match fields as fields0 return (struct_denote fields0 -> list val) with
           | [] => fun _ : unit => []
           | p :: fields0 =>
             let (_, tau) as p0 return (snd p0 * struct_denote fields0 -> list val) := p in
             fun '(x0, xs) => val_of_value x0 :: val_of_struct_value fields0 xs
           end x) fields x =
        val_of_struct_value' fields x.
    Proof.
      induction fields; simpl; intros; eauto.
    Qed.

    Lemma subst_field_ok':
      forall flds idx v s,
        subst_field (index_to_nat idx) (val_of_value v)
                    (val_of_struct_value' flds s) =
        Some (val_of_struct_value' flds
                                   (BitFuns.subst_field flds s idx v)).
    Proof.
      induction flds; simpl; intros; eauto. easy.
      repeat destr. simpl in *. auto.
      simpl in *. rewrite IHflds. simpl. auto.
    Qed.

    Lemma subst_field_ok:
      forall sig idx (s: struct_t sig) v,
        exists s',
          val_of_value s = Struct sig s' /\
          exists s'',
          subst_field (index_to_nat idx) (val_of_value v) s' = Some s'' /\
          Struct sig s'' =
          val_of_value (tau:=struct_t sig) (BitFuns.subst_field (struct_fields sig) s idx v)
    .
    Proof.
      intros.
      simpl in s.
      revert s idx v. simpl. intros.
      rewrite ! val_of_struct_value_rew.
      eexists; split; eauto.
      rewrite subst_field_ok'.
      eexists; split; eauto.
    Qed.

    Fixpoint subst_field_name (flds: list (string * type)) (n: string)
             (v: val) (s: list val) : option (list val) :=
      match flds, s with
      | _, [] => None
      | [], _ => None
      | (name, _)::flds, a::r =>
        if eq_dec n name then Some (v::r)
        else let/opt s := subst_field_name flds n v r in Some (a::s)
      end.


    Lemma subst_field_name_ok':
      forall flds x idx fname v s,
            PrimTypeInference.find_field {| struct_name := x; struct_fields := flds|} fname = Success idx ->
        subst_field_name flds fname (val_of_value v)
                    (val_of_struct_value' flds s) =
        Some (val_of_struct_value' flds
                                   (BitFuns.subst_field flds s idx v)).
    Proof.
      induction flds; simpl; intros; eauto. easy.
      destr_in v.
      - destruct a. destruct s. simpl in *.
        unfold PrimTypeInference.find_field in H. simpl in H.
        destr_in H.
        + subst. simpl in H. inv H. auto.
        + destr_in H; inv H.
      - destruct a, s.
        unfold PrimTypeInference.find_field in H. simpl in H.
        destr_in H.
        + subst. simpl in H. inv H.
        + destr_in H; inv H. simpl in *. erewrite IHflds with (x:=x). simpl. auto.
          unfold PrimTypeInference.find_field. simpl. rewrite Heqo. simpl. auto.
    Qed.

    Lemma subst_field_name_ok:
      forall sig fname idx (s: struct_t sig) v,
        PrimTypeInference.find_field sig fname = Success idx ->
        exists s',
          val_of_value s = Struct sig s' /\
          exists s'',
          subst_field_name (struct_fields sig) fname (val_of_value v) s' = Some s'' /\
          Struct sig s'' =
          val_of_value (tau:=struct_t sig) (BitFuns.subst_field (struct_fields sig) s idx v)
    .
    Proof.
      intros.
      simpl in s.
      revert s idx v H. simpl. intros.
      rewrite ! val_of_struct_value_rew.
      eexists; split; eauto.
      erewrite subst_field_name_ok'.
      eexists; split; eauto.
      instantiate(1:= struct_name sig).
      destruct sig. eauto.
    Qed.

    Lemma vect_replace_to_list:
      forall {A: Type} sz (v: vect A sz) l1 (a: A) l2 x idx,
        vect_to_list v = l1 ++ a :: l2 ->
        List.length l1 = index_to_nat idx ->
        vect_to_list (vect_replace v idx x) = l1 ++ x :: l2.
    Proof.
      induction sz; simpl; intros; eauto. easy.
      destr.
      - destruct l1; simpl in *; try lia. subst.
        rewrite vect_to_list_cons. f_equal.
        destruct v; simpl in *.
        unfold vect_to_list in H. simpl in H. inv H. reflexivity.
      - rewrite vect_to_list_cons. subst. simpl.
        destruct v; simpl in *.
        unfold vect_to_list in H. simpl in H. fold (@vect_to_list A) in H.
        destruct l1. simpl in *. lia. simpl in H. inv H.
        simpl. f_equal. simpl in H0. inv H0.
        eapply IHsz; eauto.
    Qed.

    Lemma take_drop_map:
      forall {A B: Type} (f: A -> B) n l l1 l2,
        take_drop n (map f l) = Some (l1, l2) ->
        exists l1' l2',
          take_drop n l = Some (l1', l2') /\
          l1 = List.map f l1' /\
          l2 = List.map f l2'.
    Proof.
      induction n; simpl; intros; eauto.
      - inv H. exists [], l; repeat split; eauto.
      - destr_in H. inv H.
        destruct (take_drop n l0) eqn:?; try congruence. 2: inv H.
        destruct p; simpl in *. inv H.
        destr. simpl in *. congruence. simpl in *. inv Heql0.
        edestruct IHn as (l1' & l2' & EQ1 & EQ2 & EQ3). eauto.
        rewrite EQ1. simpl. (do 2 eexists); repeat split; eauto.
        subst; reflexivity.
    Qed.

    Definition sigma2 (fn: ufn2) (v1 v2: val) : option val :=
      match fn with
      | UEq false  => Some (Bits 1 [if val_eq_dec v1 v2 then true else false])
      | UEq true  =>  Some (Bits 1 [if val_eq_dec v1 v2 then false else true])
      | UBits2 fn =>
        match v1, v2 with
          Bits _ v1, Bits _ v2 => let res := ubits2_sigma fn v1 v2 in
                                  Some (Bits (List.length res) res)
        | _, _ => None
        end
      | UStruct2 (USubstField fname) =>
        match v1 with
          Struct sig v1 =>
          let/opt res := subst_field_name (struct_fields sig) fname v2 v1 in
          Some (Struct sig res)
        | _ => None
        end
      | UStruct2 (USubstFieldBits sig fname) =>
        match v1, v2 with
          Bits sz v1, Bits _ v2 =>
          let/opt2 ofs, w := find_field_offset_right (struct_fields sig) fname in
          let res := ubits2_sigma (USliceSubst ofs w) v1 v2 in
          Some (Bits sz res)
        | _, _ => None
        end
      | UArray2 (USubstElement n) =>
        match v1 with
          | Array s v1 =>
            let/opt2 l1, l2 := take_drop n v1 in
            match l2 with
              [] => None
            | a::l2 => Some (Array s (l1 ++ v2 :: l2))
            end
          | _ => None
        end
      | UArray2 (USubstElementBits sig n) =>
        match v1, v2 with
          Bits sz v1, Bits _ v2 =>
          let res := ubits2_sigma (USliceSubst ((array_len sig - S n) * element_sz sig) (element_sz sig)) v1 v2 in
          Some (Bits sz res)
        | _, _ => None
        end
      end.


    Lemma sigma2_correct:
          forall ufn fn ty1 ty2,
            PrimTypeInference.tc2
              ufn
              ty1 ty2 = Success fn ->
            forall (arg1: arg1Sig (PrimSignatures.Sigma2 fn))
                   (arg2: arg2Sig (PrimSignatures.Sigma2 fn)),
              sigma2 ufn (val_of_value arg1) (val_of_value arg2) = Some (val_of_value (PrimSpecs.sigma2 fn arg1 arg2)).
    Proof.
      destruct ufn; simpl; intros.
      - inv H. simpl in *. destr; f_equal; f_equal.
        unfold BitFuns._neq. unfold beq_dec. destruct (eq_dec).
        subst. destr. reflexivity.
        destr. 2: reflexivity.
        exfalso. apply n. apply bits_of_value_inj. apply vect_to_list_inj.
        erewrite ! (ubits_of_value_ok _ _ eq_refl). rewrite e. reflexivity.
        unfold BitFuns._eq. unfold beq_dec. destruct (eq_dec).
        subst. destr. reflexivity.
        destr. 2: reflexivity.
        exfalso. apply n. apply bits_of_value_inj. apply vect_to_list_inj.
        erewrite ! (ubits_of_value_ok _ _ eq_refl). rewrite e. reflexivity.
      - destr_in H. 2: congruence.
        destr_in Heqr; try congruence.
        destr_in H; try congruence.
        destr_in Heqr0; try congruence.
        inv Heqr0. inv Heqr. inv H.
        generalize (ubits2_correct fn _ s s0 eq_refl arg1 arg2 _ eq_refl).
        destr; try easy.
        destr; try easy. intro A; rewrite A. simpl.
        rewrite vect_to_list_length. simpl. auto.
      - destr_in H.
        + destr_in H; try congruence.
          destr_in Heqr; try congruence.
          destr_in H; try congruence.
          inv Heqr. inv H. simpl in arg1, arg2.
          edestruct subst_field_name_ok as (s' & VOV & s'' & SFN & EQ). eauto.
          rewrite VOV. rewrite SFN. simpl.
          rewrite ! val_of_struct_value_rew.
          f_equal. rewrite EQ. simpl.
          rewrite val_of_struct_value_rew.
          reflexivity.
        + subst. destr_in H; try congruence. inv H. simpl in *.
          rewrite slice_subst.
          erewrite find_field_offset_right_spec; eauto. simpl.
          rewrite vect_to_list_length. reflexivity.
      - destr.
        + destr_in H; try congruence.
          destr_in H; inv H. destr_in Heqr; inv Heqr. simpl in *.
          assert (pos < array_len s).
          {
            destruct (lt_dec pos (array_len s)). auto.
            unfold PrimTypeInference.check_index in Heqr0. unfold opt_result in Heqr0.
            destr_in Heqr0; inv Heqr0.
            rewrite index_of_nat_ge_none in Heqo. congruence. lia.
          }
          edestruct @take_drop_succeeds as (l1 & l2 & EQ).
          2: rewrite EQ.
          rewrite map_length. rewrite vect_to_list_length. lia. simpl.

          edestruct (@take_drop_map) as (l1' & l2' & EQ4 & EQ5 & EQ6). eauto.

          edestruct (@take_drop_spec) as (EQ1 & EQ2 & EQ3). apply EQ4.
          rewrite vect_to_list_length in EQ3.
          destr. erewrite <- map_length in EQ3. rewrite <- EQ6 in EQ3. simpl in EQ3. lia.

          destruct l2'; simpl in *; try congruence. inv EQ6.
          erewrite vect_replace_to_list; eauto.
          rewrite map_app. reflexivity.
          unfold PrimTypeInference.check_index in Heqr0. unfold opt_result in Heqr0.
          destr_in Heqr0; inv Heqr0.
          symmetry; eapply index_to_nat_of_nat; eauto.

        + destr_in H; try congruence. inv H. simpl in *.
          rewrite slice_subst.
          unfold PrimTypeInference.check_index in Heqr. unfold opt_result in Heqr.
          destr_in Heqr; inv Heqr.
          unfold element_offset_right.
          erewrite index_to_nat_of_nat; eauto.
          rewrite Bits.rmul_correct.
          rewrite vect_to_list_length. reflexivity.
    Qed.

    Context (r: REnv.(env_t) (fun _ => val)).
    Context (sigma: forall f: ext_fn_t, val -> val).

    Section Args.
      Context (interp_action:
                 forall (Gamma: list (var_t * val))
                        (sched_log: Log) (action_log: Log)
                        (a: uaction),
                   option (Log * val * (list (var_t * val)))).

      Fixpoint interp_args'
               (Gamma: list (var_t * val))
               (sched_log: Log)
               (action_log: Log)
               (argspec: tsig var_t)
               (args: list uaction)
        : option (Log * list (var_t * val) * list (var_t * val)) :=
        match argspec, args with
        | [], [] => Some (action_log, [], Gamma)
        | argspec:: argspecs, arg :: args =>
          let/opt3 action_log, ctx, Gamma := interp_args' Gamma sched_log action_log argspecs args in
          let/opt3 action_log, v, Gamma := interp_action Gamma sched_log action_log arg in
          Some (action_log, (fst argspec,v)::ctx, Gamma)
        | _, _ => None
        end.
    End Args.

    Fixpoint list_assoc {K V: Type} {eq: EqDec K} (l: list (K * V)) (k: K): option V :=
      match l with
        [] => None
      | (k1,v1)::l =>
        if eq_dec k k1 then Some v1 else list_assoc  l k
      end.

    Fixpoint list_assoc_set {K V: Type} {eq: EqDec K} (l: list (K * V)) (k: K) (v: V): list (K * V) :=
      match l with
        [] => [(k,v)]
      | (k1,v1)::l =>
        if eq_dec k k1 then (k1,v)::l else (k1,v1) :: list_assoc_set l k v
      end.

    Fixpoint interp_action
             (Gamma: list (var_t * val))
             (sched_log: Log)
             (action_log: Log)
             (a: uaction)
             {struct a}
      : option (Log * val * list (var_t * val)) :=
      match a with
      | UError e => None
      | UFail _ => None
      | USugar _ => None
      | UVar var =>
        let/opt v := list_assoc Gamma var in
        Some (action_log, v, Gamma)
      | @UConst _ _ _ _ _ tau cst =>
        Some (action_log, val_of_value cst, Gamma)
      | UAssign k a =>
        let/opt3 action_log, v, Gamma := interp_action Gamma sched_log action_log a in
        Some (action_log, Bits 0 [], list_assoc_set Gamma k v)
      | USeq a1 a2 =>
        let/opt3 action_log, v, Gamma := interp_action Gamma sched_log action_log a1 in
        interp_action Gamma sched_log action_log a2
      | UBind k a1 a2 =>
        let/opt3 action_log, v, Gamma :=
           interp_action Gamma sched_log action_log a1 in
        let/opt3 action_log, v, Gamma :=
           interp_action ((k, v):: Gamma) sched_log action_log a2
        in Some (action_log, v, tl Gamma)
      | UIf cond athen aelse =>
        let/opt3 action_log, v, Gamma := interp_action Gamma sched_log action_log cond in
        match v with
        | Bits 1 [b] =>
          if b then
            interp_action Gamma sched_log action_log athen
          else
            interp_action Gamma sched_log action_log aelse
        | _ => None
        end
      | URead prt idx =>
        if may_read sched_log prt idx then
          Some (log_cons idx (LE LogRead prt (Bits 0 [])) action_log,
                match prt with
                | P0 => REnv.(getenv) r idx
                | P1 => match latest_write0 (V:=val) (log_app action_log sched_log) idx with
                        | Some v => v
                        | None => REnv.(getenv) r idx
                        end
                end,
                Gamma)
        else None
      | UWrite prt idx v =>
        let/opt3 action_log, val, Gamma := interp_action Gamma sched_log action_log v in
        if may_write sched_log action_log prt idx then
          Some (log_cons idx (LE LogWrite prt val) action_log, Bits 0 [], Gamma)
        else None
      | UUnop fn arg =>
        let/opt3 action_log, arg1, Gamma := interp_action Gamma sched_log action_log arg in
        let/opt v := sigma1 fn arg1 in
        Some (action_log, v, Gamma)
      | UBinop fn arg1 arg2 =>
        let/opt3 action_log, arg1, Gamma := interp_action Gamma sched_log action_log arg1 in
        let/opt3 action_log, arg2, Gamma := interp_action Gamma sched_log action_log arg2 in
        let/opt v := sigma2 fn arg1 arg2 in
        Some (action_log, v, Gamma)
      | UExternalCall fn arg1 =>
        let/opt3 action_log, arg1, Gamma := interp_action Gamma sched_log action_log arg1 in
        Some (action_log, sigma fn arg1, Gamma)
      | UInternalCall f args =>
        let body := int_body f in
        let/opt3 action_log, results, Gamma :=
           fold_right (fun a acc =>
                        let/opt3 action_log, l, Gamma := acc in
                        let/opt3 action_log, v, Gamma :=
                           interp_action Gamma sched_log action_log a in
                        Some (action_log, v::l, Gamma))
                     (Some (action_log, [], Gamma)) args in
        let/opt3 action_log, v, _ :=
           interp_action
             (map (fun '(name, _, v) => (name, v))
                  (combine (int_argspec f) results)) sched_log action_log body in
        Some (action_log, v, Gamma)
      | UAPos p a =>
        interp_action Gamma sched_log action_log a
      end.
    End Action.
End Interp.

Section Eq.
      Require TypedSemantics.

      Require TypeInference.

  Context {pos_t var_t fn_name_t reg_t ext_fn_t: Type}.
  Context {reg_t_eq_dec: EqDec reg_t}.
  Context {var_t_eq_dec: EqDec var_t}.

      
      Context {TR: reg_t -> type}.
  Context {Sigma: ext_fn_t -> ExternalSignature}.
  Context {REnv: Env reg_t}.
      Context (r: env_t REnv (fun x : reg_t => val)).
      Context (sigma: forall f: ext_fn_t, val -> val).
      Context (tr: env_t REnv (fun x : reg_t => TR x)).
      Context (tsigma: forall f, Sig_denote (Sigma f)).

      Hypothesis tsigma_correct:
        forall f v,
          sigma f (val_of_value v) = val_of_value (tsigma f v).

      Definition env_t_R
                 {K: Type}
                 {V1 V2: K -> Type}
                 (R: forall k, V1 k -> V2 k -> Prop)
                 (e: Env K)
                 (e1: env_t e (fun x => V1 x))
                 (e2: env_t e (fun x => V2 x)) : Prop :=
        forall k,
          R k (getenv e e1 k) (getenv e e2 k).

      Definition logentrykind_eq (uk: LogEntryKind) (k: Logs.LogEntryKind) :=
        match uk, k with
        | LogRead, Logs.LogRead => True
        | LogWrite, Logs.LogWrite => True
        | _, _ => False
        end.
      
      (* Definition logentry_eq {V:type} (url: LogEntry val) (rl: Logs.LogEntry V) : Prop. *)
      (*   destruct url, rl. *)
      (*   destruct kind0. exact True. *)
      (*   exact (val0 = val_of_value val1). *)
      (*   Set Printing All. *)
      (*   Show Proof. *)

      Definition logentry_eq {V:type} (ule: LogEntry val) (le: Logs.LogEntry V) : Prop :=
        logentrykind_eq (kind ule) (Logs.kind le) /\
        port ule = Logs.port le /\
        match Logs.kind le as l return
              (match l return Type with
               | Logs.LogRead => unit
               | Logs.LogWrite => type_denote V
               end -> Prop) with
          | Logs.LogRead => fun _ => ULogs.val ule = Bits 0 []
          | Logs.LogWrite => fun v => ULogs.val ule = val_of_value v
        end (Logs.val le).

      Definition rlog_eq {V:type} (url: RLog val) (rl: Logs.RLog V) :=
        Forall2 (fun ule le => logentry_eq ule le) url rl.

      Notation Log := (@_ULog val reg_t REnv).

      (* Notation rule := (rule pos_t var_t fn_name_t R Sigma). *)
      Notation uaction := (uaction pos_t var_t fn_name_t reg_t ext_fn_t).
      (* Notation scheduler := (scheduler pos_t rule_name_t). *)


      Definition log_eq REnv (ul: env_t REnv (fun _ => RLog val)) (l: Logs.Log TR REnv) : Prop :=
        env_t_R (V1:= fun k => Logs.RLog (TR k))
                        (V2:= fun k => RLog val)
                        (fun k v1 v2 => rlog_eq v2 v1) REnv l ul.

      Inductive gamma_eq :
        forall (sig: tsig var_t), list (var_t * val) -> TypedSemantics.tcontext sig -> Prop :=
      | gamma_eq_nil:
          gamma_eq [] [] (CtxEmpty)
      | gamma_eq_cons:
          forall sig k t v ug g,
            gamma_eq sig ug g ->
            gamma_eq ((k,t)::sig) ((k,val_of_value v)::ug) (@CtxCons _ _ _ (k,t) v g)
      .


      (* Definition gamma_eq {sig} (UGamma: list (var_t * val)) *)
      (*            (Gamma: TypedSemantics.tcontext sig) : Prop := *)
      (*   forall k t (m: member _ sig), *)
      (*     assoc k sig = Some (existT _ t m) -> *)
      (*     Some (val_of_value (cassoc m Gamma)) =  (list_assoc UGamma k). *)


      Lemma gamma_eq' {sig} (UGamma: list (var_t * val))
                 (Gamma: TypedSemantics.tcontext sig) :
        gamma_eq sig UGamma Gamma ->
        forall k t (m: member _ sig),
          assoc k sig = Some (existT _ t m) ->
          Some (val_of_value (cassoc m Gamma)) =  (list_assoc UGamma k).
      Proof.
        induction 1; simpl; intros; eauto. congruence. simpl in *.
        repeat destr_in H0; simpl in *; subst.
        unfold eq_rect_r in H0; simpl in H0.
        inv H0.
        apply Eqdep_dec.inj_pair2_eq_dec in H3. subst. 2: apply eq_dec.
        simpl. auto.
        inv H0.
        apply Eqdep_dec.inj_pair2_eq_dec in H3. subst. 2: apply eq_dec.
        simpl. eauto.
        inv H0.
      Qed.

      
      Lemma cast_action'_eq:
        forall (p: pos_t) (sig: tsig var_t) (tau1 tau2: type)
               (a: TypedSyntax.action pos_t var_t fn_name_t TR Sigma sig tau1)
               (e: error_message var_t fn_name_t) a',
          TypeInference.cast_action' TR Sigma p tau2 a e = Success a' ->
          exists p : tau1 = tau2,
            a' = eq_rect _ _ a _ p.
      Proof.
        unfold TypeInference.cast_action'. intros.
        destr_in H. subst.
        unfold eq_rect_r in H. simpl in H. inv H.
        exists eq_refl; reflexivity. inv H.
      Qed.

      Lemma cast_action_eq:
        forall (p: pos_t) (sig: tsig var_t) (tau1 tau2: type)
               (a: TypedSyntax.action pos_t var_t fn_name_t TR Sigma sig tau1)
               a',
          TypeInference.cast_action TR Sigma p tau2 a = Success a' ->
          exists p : tau1 = tau2,
            a' = eq_rect _ _ a _ p.
      Proof.
        intros. unfold TypeInference.cast_action in H.
        eapply cast_action'_eq; eauto.
      Qed.



      Lemma list_assoc_gss:
        forall {K V: Type} (eq: EqDec K) (l: list (K * V)) k v,
          list_assoc (list_assoc_set l k v) k = Some v.
      Proof.
        induction l; simpl; intros; eauto.
        destr.
        repeat destr; eauto.
        simpl. rewrite Heqs. auto.
        simpl. rewrite Heqs. eauto.
      Qed.

      Lemma list_assoc_gso:
        forall {K V: Type} (eq: EqDec K) (l: list (K * V)) k k' v (d: k <> k'),
          list_assoc (list_assoc_set l k v) k' = list_assoc l k'.
      Proof.
        induction l; simpl; intros; eauto.
        destr.
        repeat destr; simpl; eauto.
        - rewrite Heqs0. auto.
        - rewrite Heqs0. auto.
        - rewrite Heqs0. eauto.
      Qed.

      Lemma gamma_eq_replace:
        forall sig g1 g2
               (Geq: gamma_eq sig g1 g2)
               k t v
               (m: member (k, t) sig)
               (ASSOC: assoc k sig = Some (existT (fun k2 : type => member (k, k2) sig) t m)),

          gamma_eq sig (list_assoc_set g1 k (val_of_value v))
                   (creplace m v g2).
      Proof.
        induction 1; simpl; intros; eauto. congruence.
        repeat destr_in ASSOC; simpl in *; try congruence.
        - subst. unfold eq_rect_r in ASSOC; simpl in ASSOC.
          inv ASSOC.
          apply Eqdep_dec.inj_pair2_eq_dec in H1. subst. 2: apply eq_dec.
          simpl.
          constructor. auto.
        - inv ASSOC.
          apply Eqdep_dec.inj_pair2_eq_dec in H1. subst. 2: apply eq_dec.
          simpl.
          constructor. eauto.
      Qed.

      (*       Lemma gamma_eq_replace: *)
      (*   forall sig (* (ND: NoDup (map fst sig)) *) g1 g2 k t v *)
      (*          (m: member (k, t) sig) *)
      (*          (ASSOC: assoc k sig = Some (existT (fun k2 : type => member (k, k2) sig) t m)), *)
      (*     gamma_eq g1 g2 -> *)
      (*     gamma_eq (list_assoc_set g1 k (val_of_value v)) *)
      (*              (creplace m v g2). *)
      (* Proof. *)
      (*   unfold gamma_eq. simpl. intros. *)
      (*   destruct (eq_dec k k0). *)
      (*   - subst. *)
      (*     rewrite H0 in ASSOC; inv ASSOC. *)
      (*     apply Eqdep_dec.inj_pair2_eq_dec in H3. subst. 2: apply eq_dec. *)
      (*     rewrite cassoc_creplace_eq. *)
      (*     rewrite list_assoc_gss. auto. *)
      (*   - rewrite cassoc_creplace_neq_k; auto. *)
      (*     rewrite list_assoc_gso. eauto. auto. intro A; inv A. congruence. *)
      (* Qed. *)



      Lemma log_eq_existsb:
        forall usched_log sched_log,
          log_eq REnv usched_log sched_log ->
          forall idx f uf,
            (forall ule idx le,
                logentrykind_eq ule le ->
                uf ule idx = f le idx
            ) ->
            Logs.log_existsb sched_log idx f =
            log_existsb usched_log idx uf.
      Proof.
        unfold Logs.log_existsb, log_existsb. intros.
        unfold log_eq in H. red in H.
        red in H.
        generalize (H idx).
        generalize (@getenv _ REnv (fun x => Logs.RLog (TR x)) sched_log idx).
        generalize (getenv REnv usched_log idx).
        clear - H0.
        induction 1; simpl; intros. auto.
        red in H. intuition.
        destruct x, y; simpl in *. subst.
        erewrite H0; eauto. f_equal. eauto.
      Qed.

      Lemma may_read_eq:
        forall usched_log sched_log,
          log_eq REnv usched_log sched_log ->
          forall port idx,
            Logs.may_read sched_log port idx =
            may_read usched_log port idx.
      Proof.
        unfold Logs.may_read, may_read.
        intros.
        rewrite ! log_eq_existsb with (f:=Logs.is_write0) (uf:=is_write0) (usched_log:=usched_log); auto.
        rewrite ! log_eq_existsb with (f:=Logs.is_write1) (uf:=is_write1) (usched_log:=usched_log); auto.
        destruct ule, le; simpl; auto; try easy.
        destruct ule, le; simpl; auto; try easy.
      Qed.


      Lemma log_eq_app:
        forall ul1 ul2 l1 l2,
          log_eq REnv ul1 l1 ->
          log_eq REnv ul2 l2 ->
          log_eq REnv (log_app ul1 ul2) (Logs.log_app l1 l2).
      Proof.
        unfold log_app, Logs.log_app.
        unfold log_eq. unfold env_t_R.
        simpl. intros.
        rewrite ! getenv_map2.
        apply Forall2_app; eauto.
        apply H. apply H0.
      Qed.

      Lemma may_write_eq:
        forall usched_log sched_log,
          log_eq REnv usched_log sched_log ->
          forall urule_log rule_log,
            log_eq REnv urule_log rule_log ->
            forall port idx,
              Logs.may_write sched_log rule_log port idx =
              may_write usched_log urule_log port idx.
      Proof.
        unfold Logs.may_write, may_write.
        intros.
        generalize (log_eq_app _ _ _ _ H0 H).
        intros.
        rewrite ! log_eq_existsb with (f:=Logs.is_write0) (uf:=is_write0) (usched_log:=log_app urule_log usched_log); auto.
        rewrite ! log_eq_existsb with (f:=Logs.is_write1) (uf:=is_write1) (usched_log:=log_app urule_log usched_log); auto.
        rewrite ! log_eq_existsb with (f:=Logs.is_read1) (uf:=is_read1) (usched_log:=log_app urule_log usched_log); auto.
        destruct ule, le; simpl; auto; try easy.
        destruct ule, le; simpl; auto; try easy.
        destruct ule, le; simpl; auto; try easy.
      Qed.



      Lemma log_find_eq:
        forall ulog log,
          log_eq REnv ulog log ->
          forall idx,
          forall f uf,
            (forall ule (le: Logs.LogEntry (TR idx)),
                logentry_eq ule le ->
                uf ule = option_map (val_of_value) (f le)
            ) ->

            option_map (val_of_value (tau:=TR idx)) (Logs.log_find log idx f) =
            (log_find ulog idx uf).
      Proof.
        unfold Logs.log_find, log_find.
        intros.
        red in H. red in H. red in H.
        generalize (H idx).
        generalize (@getenv _ REnv (fun x => Logs.RLog (TR x)) log idx).
        generalize (getenv REnv ulog idx).
        clear - H0.
        induction 1; simpl; intros. auto.
        erewrite H0; eauto. destr; simpl; eauto.
      Qed.

      Lemma latest_write0_eq:
        forall ulog log,
          log_eq REnv ulog log ->
          forall idx,
            option_map (val_of_value (tau:=TR idx)) (Logs.latest_write0 log idx) =
            (latest_write0 ulog idx).
      Proof.
        unfold Logs.latest_write0, latest_write0.
        intros.
        eapply log_find_eq. auto.
        intros. red in H0. intuition.
        destruct ule, le; simpl in *. subst.
        destr_in val1.
        - subst. red in H1. destr; try easy.
        - subst. red in H1. destr; try easy.
          destr; auto.
      Qed.

      Lemma log_eq_cons:
        forall idx ulog (log: Logs._Log) ule le,
          log_eq REnv ulog log ->
          logentry_eq ule le ->
          log_eq REnv (log_cons idx ule ulog) (Logs.log_cons idx le log).
      Proof.
        unfold log_eq. unfold env_t_R.
        unfold rlog_eq.
        intros. unfold log_cons, Logs.log_cons.
        destruct (eq_dec idx k).
        - subst.
          rewrite ! get_put_eq.
          constructor; eauto.
        - rewrite ! get_put_neq; eauto.
      Qed.

      

      Hypothesis r_eq:
        forall i,
          getenv REnv r i = val_of_value (getenv REnv tr i).

      Lemma interp_action_correct:
        forall ua p sig tau a
               (TA: TypeInference.type_action TR Sigma p sig ua = Success (existT _ tau a))
               (Gamma: TypedSemantics.tcontext sig)
               (UGamma: list (var_t * val))
               (GammaEq: gamma_eq sig UGamma Gamma)
               sched_log action_log action_log'
               usched_log uaction_log
               (SL: log_eq REnv usched_log sched_log)
               (AL: log_eq REnv uaction_log action_log)
               v Gamma'
        ,
          TypedSemantics.interp_action
            tr tsigma
            Gamma sched_log action_log a = Some (action_log', v, Gamma') ->
          exists uaction_log' UGamma',
            interp_action
              (pos_t:=pos_t)
              (fn_name_t := fn_name_t)
              r sigma UGamma usched_log uaction_log ua = Some (uaction_log', val_of_value v, UGamma')
            /\ log_eq REnv uaction_log' action_log'
            /\ gamma_eq sig UGamma' Gamma'
      .
      Proof.
        fix IHua 1.
        destruct ua; simpl; intros.
        - inv TA.
        - inv TA.
          apply Eqdep_dec.inj_pair2_eq_dec in H2. subst.
          simpl in H. inv H.
          apply eq_dec.
        - destr_in TA; inv TA.
          apply Eqdep_dec.inj_pair2_eq_dec in H2. 2: apply eq_dec. subst.
          simpl in H. inv H.
          unfold opt_result in Heqr0; destr_in Heqr0; inv Heqr0. destruct s.
          simpl.
          setoid_rewrite <- gamma_eq'. simpl.
          exists uaction_log, UGamma; split; eauto. eauto. eauto.
        - inv TA.
          apply Eqdep_dec.inj_pair2_eq_dec in H2. 2: apply eq_dec. subst.
          simpl in H. inv H.
          exists uaction_log, UGamma; split; eauto.
        - destr_in TA; [|inv TA].
          destr_in TA; [|inv TA].
          destr_in TA; [|inv TA]. inv TA.
          apply Eqdep_dec.inj_pair2_eq_dec in H2. 2: apply eq_dec. subst. simpl in H.
          unfold opt_bind in H.
          destr_in H; [|inv H].
          destr_in H. destr_in H. inv H.
          unfold opt_result in Heqr0; destr_in Heqr0; inv Heqr0. destruct s. simpl in *.
          destruct s0. simpl in *.
          apply cast_action_eq in Heqr2.
          destruct Heqr2 as (pf & EQ). subst.
          simpl in Heqo.
          edestruct (IHua ua _ _ _ _ Heqr1) as (ual' & g' & IA' & ALeq & Geq). auto.
          4: apply Heqo. eauto. eauto. eauto.
          rewrite IA'. simpl.
          eexists; eexists; repeat split; eauto.
          apply gamma_eq_replace; eauto.
        - destr_in TA; [|inv TA].
          destr_in TA; [|inv TA].
          destr_in TA; [|inv TA]. inv TA.
          apply Eqdep_dec.inj_pair2_eq_dec in H2. 2: apply eq_dec. subst. simpl in H.
          unfold opt_bind in H.
          destr_in H; [|inv H].
          destr_in H. destr_in H.
          destruct s. simpl in *.
          apply cast_action_eq in Heqr1.
          destruct Heqr1 as (pf & EQ). subst.
          simpl in Heqo.
          edestruct (IHua ua1 _ _ _ _ Heqr0) as (ual' & g' & IA' & ALeq & Geq). auto.
          4: apply Heqo. eauto. eauto. eauto.
          rewrite IA'. simpl.
          destruct s1. simpl in *.
          edestruct (IHua ua2 _ _ _ _ Heqr2) as (ual2' & g2' & IA2' & ALeq2 & Geq2). auto.
          4: apply H. eauto. eauto. eauto.
          rewrite IA2'.
          eexists; eexists; repeat split; eauto.
        - destr_in TA; [|inv TA].
          destr_in TA; [|inv TA].
          inv TA.
          apply Eqdep_dec.inj_pair2_eq_dec in H2. 2: apply eq_dec. subst. simpl in H.
          unfold opt_bind in H.
          destr_in H; [|inv H].
          destr_in H. destr_in H. destr_in H; [|inv H].
          destruct p2. destruct p2. inv H.
          destruct s, s0. simpl in *.
          edestruct (IHua ua1 _ _ _ _ Heqr0) as (ual' & g' & IA' & ALeq & Geq). auto.
          4: apply Heqo. eauto. eauto. eauto.
          rewrite IA'. simpl.
          edestruct (IHua ua2 _ _ _ _ Heqr1 (CtxCons (v,x) t0 t) ((v,val_of_value t0)::g')) as (ual2' & g2' & IA2' & ALeq2 & Geq2).
          4: apply Heqo0. 2-3: eauto.
          constructor; auto.
          rewrite IA2'. simpl.
          eexists; eexists; repeat split; eauto. inv Geq2.
          apply Eqdep_dec.inj_pair2_eq_dec in H4. 2: apply eq_dec. subst. simpl. auto.
        - destr_in TA; [|inv TA].
          destr_in TA; [|inv TA].
          destr_in TA; [|inv TA].
          destr_in TA; [|inv TA].
          destr_in TA; [|inv TA].
          inv TA.
          apply Eqdep_dec.inj_pair2_eq_dec in H2. 2: apply eq_dec. subst. simpl in H.
          unfold opt_bind in H.
          destr_in H; [|inv H].
          destruct p0. destruct p0.
          destruct s. simpl in *.
          apply cast_action_eq in Heqr1.
          destruct Heqr1 as (pf & EQ). subst.
          simpl in Heqo.
          edestruct (IHua ua1 _ _ _ _ Heqr0) as (ual' & g' & IA' & ALeq & Geq).
          4: apply Heqo. eauto. eauto. eauto.
          rewrite IA'. simpl.
          destruct s1, s2. simpl in *.
          apply cast_action_eq in Heqr4.
          destruct Heqr4 as (pf & EQ). subst.
          simpl in H.
          destr.
          + edestruct (IHua ua2 _ _ _ _ Heqr2) as (ual2' & g2' & IA2' & ALeq2 & Geq2).
            4: apply H. eauto. eauto. eauto.
            rewrite IA2'. simpl.
            eexists; eexists; repeat split; eauto.
          + edestruct (IHua ua3 _ _ _ _ Heqr3) as (ual2' & g2' & IA2' & ALeq2 & Geq2).
            4: apply H. eauto. eauto. eauto.
            rewrite IA2'. simpl.
            eexists; eexists; repeat split; eauto.
        - inv TA.
          apply Eqdep_dec.inj_pair2_eq_dec in H2. 2: apply eq_dec. subst. simpl in H.
          erewrite may_read_eq in H; eauto.
          destr_in H; [|inv H]. inv H.
          eexists; eexists; repeat split; eauto.
          f_equal. f_equal. f_equal.
          rewrite ! r_eq.
          destr.

          erewrite <- latest_write0_eq; eauto.
          2: apply log_eq_app; eauto.
          destruct (Logs.latest_write0) eqn:?; simpl; auto.

          apply log_eq_cons; auto.
          red. simpl. auto.
        - destr_in TA; [|inv TA].
          destr_in TA; [|inv TA].
          inv TA.
          apply Eqdep_dec.inj_pair2_eq_dec in H2. 2: apply eq_dec. subst. simpl in H.
          unfold opt_bind in H.
          destr_in H; [|inv H].
          destruct p0. destruct p0.

          destruct s. simpl in *.
          apply cast_action_eq in Heqr1.
          destruct Heqr1 as (pf & EQ). subst.
          simpl in Heqo.
          edestruct (IHua ua _ _ _ _ Heqr0) as (ual' & g' & IA' & ALeq & Geq).
          4: apply Heqo. eauto. eauto. eauto.
          rewrite IA'. simpl.
          erewrite may_write_eq in H; eauto.
          destr_in H; [|inv H]. inv H.
          eexists; eexists; repeat split; eauto.
          apply log_eq_cons; auto.
          red. simpl. auto.
        - destr_in TA; [|inv TA].
          destr_in TA; [|inv TA].
          destr_in TA; [|inv TA].
          inv TA.
          apply Eqdep_dec.inj_pair2_eq_dec in H2. 2: apply eq_dec. subst. simpl in H.
          unfold opt_bind in H.
          destr_in H; [|inv H].
          destruct p0. destruct p0. inv H.
          destruct s. simpl in *.
          apply cast_action_eq in Heqr2.
          destruct Heqr2 as (pf & EQ). subst.
          simpl in Heqo.
          edestruct (IHua ua _ _ _ _ Heqr0) as (ual' & g' & IA' & ALeq & Geq).
          4: apply Heqo. eauto. eauto. eauto.
          rewrite IA'. simpl.
          unfold TypeInference.lift_fn1_tc_result in Heqr1.
          unfold result_map_failure in Heqr1. destr_in Heqr1; inv Heqr1.
          erewrite usigma1_correct; eauto. simpl.
          eexists; eexists; repeat split; eauto.
        - destr_in TA; [|inv TA].
          destr_in TA; [|inv TA].
          destr_in TA; [|inv TA].
          destr_in TA; [|inv TA].
          destr_in TA; [|inv TA].
          inv TA.
          apply Eqdep_dec.inj_pair2_eq_dec in H2. 2: apply eq_dec. subst. simpl in H.
          unfold opt_bind in H.
          destr_in H; [|inv H].
          destruct p0. destruct p0.
          destr_in H; [|inv H].
          destruct p0. destruct p0.
          inv H.
          destruct s, s0. simpl in *.
          apply cast_action_eq in Heqr3.
          destruct Heqr3 as (pf & EQ). subst.
          simpl in Heqo.
          apply cast_action_eq in Heqr4.
          destruct Heqr4 as (pf & EQ). subst.
          simpl in Heqo0.
          edestruct (IHua ua1 _ _ _ _ Heqr0) as (ual' & g' & IA' & ALeq & Geq).
          4: apply Heqo. eauto. eauto. eauto.
          rewrite IA'. simpl.
          edestruct (IHua ua2 _ _ _ _ Heqr1) as (ual2' & g2' & IA2' & ALeq2 & Geq2).
          4: apply Heqo0. eauto. eauto. eauto.
          rewrite IA2'. simpl.
          unfold TypeInference.lift_fn2_tc_result in Heqr2.
          unfold result_map_failure in Heqr2. destr_in Heqr2; inv Heqr2.
          erewrite sigma2_correct; eauto. simpl.
          eexists; eexists; repeat split; eauto.
        - destr_in TA; [|inv TA].
          destr_in TA; [|inv TA].
          inv TA.
          apply Eqdep_dec.inj_pair2_eq_dec in H2. 2: apply eq_dec. subst. simpl in H.
          unfold opt_bind in H.
          destr_in H; [|inv H].
          destruct p0. destruct p0. inv H.
          destruct s. simpl in *.
          apply cast_action_eq in Heqr1.
          destruct Heqr1 as (pf & EQ). subst.
          simpl in Heqo.
          edestruct (IHua ua _ _ _ _ Heqr0) as (ual' & g' & IA' & ALeq & Geq).
          4: apply Heqo. eauto. eauto. eauto.
          rewrite IA'. simpl.
          eexists; eexists; repeat split; eauto.
          rewrite tsigma_correct. eauto.
        - destr_in TA; [|inv TA].
          destr_in TA; [|inv TA].
          destr_in TA; [|inv TA].
          destr_in TA; [|inv TA].
          inv TA.
          apply Eqdep_dec.inj_pair2_eq_dec in H2. 2: apply eq_dec. subst. simpl in H.
          unfold opt_bind in H.
          destr_in H; [|inv H].
          destruct p0. destruct p0. 
          destr_in H; [|inv H].
          destruct p0. destruct p0.
          inv H.
          destruct s1. simpl in *.
          apply cast_action_eq in Heqr3.
          destruct Heqr3 as (pf & EQ). subst.
          simpl in Heqo0.

          unfold TypeInference.assert_argtypes in Heqr1.


    Fixpoint assert_argtypes' {sig}
             (args_desc: tsig var_t)
             (args: list (pos_t * {tau : type & TypedSyntax.action pos_t var_t fn_name_t TR Sigma sig tau}))
      : result (context (K := (var_t * type)) (fun k_tau => TypedSyntax.action pos_t var_t fn_name_t TR Sigma sig (snd k_tau)) args_desc) unit :=
      match args_desc, args with
      | [], [] => Success CtxEmpty
      | [], _ => Failure tt
      | _, [] => Failure tt
      | (name1, tau1) :: fn_sig, (pos1, arg1) :: args =>
        match TypeInference.cast_action TR Sigma pos1 tau1 (projT2 arg1) with
          Success arg1 =>
          let/res ctx := assert_argtypes' fn_sig args in
          Success (CtxCons (name1, tau1) arg1 ctx)
        | _ => Failure tt
        end
      end.
    Lemma assert_argtypes'_eq : forall {T:Type} (sig: tsig var_t) args_desc args s ufn fname n p,
      TypeInference.assert_argtypes' (T:=T) TR Sigma ufn n fname p args_desc args = Success s <->
      assert_argtypes' (sig:=sig) args_desc args = Success s.
    Proof.
      induction args_desc; simpl; intros; eauto.
      - destr; split; intuition congruence.
      - destruct a. split. intros.
        + destr_in H; [inv H|]. destr_in H.
          destr_in H; [|inv H].
          destr_in H; [|inv H]. inv H.
          erewrite (proj1 (IHargs_desc _ _ _ _ _ _)). eauto. eauto.
        + intros. destr_in H; [inv H|]. destr_in H.
          destr_in H; [|inv H].
          destr_in H; [|inv H]. inv H.
          erewrite (proj2 (IHargs_desc _ _ _ _ _ _)). eauto. eauto.
    Qed.

    rewrite assert_argtypes'_eq in Heqr1.

    Lemma result_list_map_length {A B F: Type} (f: A -> result B F):
      forall la lb,
        result_list_map f la = Success lb ->
        List.length lb = List.length la.
    Proof.
      induction la; simpl; intros; eauto. inv H; reflexivity.
      destr_in H; [|inv H].
      destr_in H; [|inv H]. inv H.
      simpl.
      erewrite IHla; eauto.
    Qed.

    Lemma result_list_map_app1 {A B F: Type} (f: A -> result B F):
      forall la1 la2 lb1 lb2,
        result_list_map f la1 = Success lb1 ->
        result_list_map f la2 = Success lb2 ->
        result_list_map f (la1 ++ la2) = Success (lb1 ++ lb2).
    Proof.
      induction la1; simpl; intros; eauto. inv H. simpl; auto.
      destr_in H; [|inv H].
      destr_in H; [|inv H]. inv H.
      erewrite IHla1; eauto. simpl; auto.
    Qed.

    Lemma result_list_map_app2 {A B F: Type} (f: A -> result B F):
      forall la1 la2 lb,
        result_list_map f (la1 ++ la2) = Success lb ->
        exists lb1 lb2,
          result_list_map f la1 = Success lb1 /\
          result_list_map f la2 = Success lb2 /\
          lb = lb1 ++ lb2.
    Proof.
      induction la1; simpl; intros; eauto.
      destr_in H; [|inv H].
      destr_in H; [|inv H]. inv H.
      edestruct IHla1 as (lb1 & lb2 & EQ1 & EQ2 & EQl). eauto. subst.
      rewrite EQ1, EQ2.
      eexists; eexists; repeat split; eauto.
    Qed.

    Lemma result_list_map_rev {A B F: Type} (f: A -> result B F):
      forall la lb,
        result_list_map f la = Success lb ->
        result_list_map f (rev la) = Success (rev lb).
    Proof.
      induction la; simpl; intros; eauto. inv H; reflexivity.
      destr_in H; [|inv H].
      destr_in H; [|inv H]. inv H.
      simpl.
      erewrite result_list_map_app1; eauto. simpl. rewrite Heqr0. auto.
    Qed.
    
    assert (List.length args = List.length (rev s)).
    {
      apply result_list_map_length in Heqr0. rewrite <- Heqr0.
      rewrite rev_length; auto.
    }

    Lemma combine_nil_inv:
      forall {A B: Type} (la: list A) (lb: list B),
        List.length la = List.length lb ->
        combine la lb = [] ->
        la = [] /\ lb = [].
    Proof.
      induction la; simpl; intros.
      - destruct lb; simpl in *; auto. lia.
      - destruct lb. simpl in H. lia. inv H0.
    Qed.

    Lemma rev_nil_inv:
      forall {A:Type} (l: list A),
        rev l = [] -> l = [].
    Proof.
      destruct l; simpl in *. auto.
      intros.
      apply (f_equal (@List.length _)) in H.
      rewrite app_length in H; simpl in H; lia.
    Qed.

    Lemma combine_app:
      forall {A B : Type} (la1 la2 : list A) (lb1 lb2: list B),
        List.length la1 = List.length lb1 ->
        List.length la2 = List.length lb2 ->
        combine (la1 ++ la2) (lb1 ++ lb2) = combine la1 lb1 ++ combine la2 lb2.
    Proof.
      induction la1; simpl; intros; eauto.
      - destruct lb1; simpl in *; try lia. auto.
      - destruct lb1; simpl in *; try lia.
        rewrite IHla1 by lia. auto.
    Qed.

    
    Lemma combine_rev:
      forall {A B : Type} (la : list A) (lb: list B),
        List.length la = List.length lb ->
        rev (combine la lb) = combine (rev la) (rev lb).
    Proof.
      induction la; simpl; intros; eauto.
      destr. simpl in *; lia. simpl in *.
      rewrite IHla by lia.
      rewrite combine_app. simpl. auto.
      rewrite ! rev_length; lia.
      simpl; lia.
    Qed.
    
          assert (
              forall (p : pos_t) (sig : tsig var_t) s,
                result_list_map (TypeInference.type_action TR Sigma p sig) args = Success s ->
                forall (Gamma : TypedSemantics.tcontext sig) (UGamma : list (var_t * val)),
                  gamma_eq sig UGamma Gamma ->
         forall (sched_log action_log action_log' : Logs.Log TR REnv)
           (usched_log uaction_log : env_t REnv (fun _ : reg_t => RLog val)),
         log_eq REnv usched_log sched_log ->
         log_eq REnv uaction_log action_log ->
         forall (s0 : context
         (fun k_tau : var_t * type =>
          TypedSyntax.action pos_t var_t fn_name_t TR Sigma sig (snd k_tau)) 
         (rev (int_argspec ufn))),
           assert_argtypes' (rev (int_argspec ufn))
                            (rev (combine (map (TypeInference.actpos p) args) s)) = Success s0 ->
           List.length args = List.length (rev s) ->
         forall v (Gamma' : TypedSemantics.tcontext sig),
           TypedSemantics.interp_args'
             (@TypedSemantics.interp_action pos_t var_t fn_name_t reg_t ext_fn_t TR Sigma REnv tr tsigma)
             Gamma sched_log action_log s0 = 
         Some (action_log', v, Gamma') ->
         exists (uaction_log' : Log) res (UGamma' : list (var_t * val)),
           fold_right
          (fun a0 (acc : option (Log * list val * list (var_t * val))) =>
           let/opt3 action_log0, l0, Gamma0 := acc
           in (let/opt3 action_log1, v0, Gamma1
               := interp_action r sigma Gamma0 usched_log action_log0 a0
               in Some (action_log1, v0 :: l0, Gamma1))) (Some (uaction_log, [], UGamma)) args =
           Some (uaction_log', res, UGamma') /\
           gamma_eq _ (combine (map fst (rev (int_argspec ufn))) (rev res)) v /\
           log_eq REnv uaction_log' action_log' /\ gamma_eq sig UGamma' Gamma').
          {
            clear - IHua.
            rewrite <- (rev_involutive args).
            generalize (rev args) as args'.
            intros args' p sig s RLM.
            apply result_list_map_rev in RLM.
            rewrite combine_rev.
            rewrite map_rev. rewrite rev_involutive.
            revert RLM. rewrite rev_involutive.
            generalize (rev s) as s'. clear s.
            revert args' p sig.
            generalize (rev (int_argspec ufn)). clear args.
            induction l; simpl; intros.
            admit. admit. admit.
            (* - destr_in H3; [|now inv H3]. inv H3. *)
            (*   apply rev_nil_inv in Heql. *)
            (*   apply combine_nil_inv in Heql; eauto. destruct Heql. subst. *)
            (*   rewrite map_rev in H3. *)
            (*   apply rev_nil_inv in H3. *)
            (*   destruct args'; simpl in *; try congruence. inv H5. *)
            (*   eexists; eexists; eexists; repeat split; eauto. *)
            (*   constructor. *)
            (*   rewrite <- H4. rewrite map_length. auto. *)
            (* - destr_in H3. *)
            (*   destr_in H3; [inv H3|]. *)
            (*   destr_in H3. *)
            (*   destr_in H3; [|inv H3]. *)
            (*   destr_in H3; [|inv H3]. inv H3. *)
            (*   destruct args'. *)
            (*   + simpl in H. inv H. simpl in Heql0. congruence. *)
            (*   + simpl in H. *)
            (*     destr_in H; [|inv H]. *)
            (*   destr_in H; [|inv H]. inv H. simpl in *. *)
            (*   unfold opt_bind in H4. *)
            (*   destr_in H4; [|inv H4]. destruct p0. destruct p0. *)
            (*   destr_in H4; [|inv H4]. destruct p0. destruct p0. *)
            (*   inv H4. simpl in *. *)
            (*   rewrite fold_left_app. *)
            (*   edestruct IHl as (ual' & res & ug' & EQ & Geq' & ALeq & Geq2'). *)
            (*   apply Heqr3. 4: eauto. *)
          }
          admit.
        - destr_in TA; [|inv TA].
          inv TA.
          apply Eqdep_dec.inj_pair2_eq_dec in H2. 2: apply eq_dec. subst. simpl in H.
          destruct s. simpl in *.
          edestruct (IHua ua _ _ _ _ Heqr0) as (ual' & g' & IA' & ALeq & Geq).
          4: apply H. eauto. eauto. eauto.
          rewrite IA'.
          eexists; eexists; repeat split; eauto.
        - inv TA.
      Qed.

      

    End Eq.
    
    Definition interp_rule (sched_log: Log) (rl: rule) : option Log :=
      match interp_action CtxEmpty sched_log log_empty rl with
      | Some (l, _, _) => Some l
      | None => None
      end.
  End Action.

  Section Scheduler.
    Context (r: REnv.(env_t) R).
    Context (sigma: forall f, Sig_denote (Sigma f)).
    Context (rules: rule_name_t -> rule).

    Fixpoint interp_scheduler'
             (sched_log: Log)
             (s: scheduler)
             {struct s} :=
      let interp_try rl s1 s2 :=
          match interp_rule r sigma sched_log (rules rl) with
          | Some l => interp_scheduler' (log_app l sched_log) s1
          | None => interp_scheduler' sched_log s2
          end in
      match s with
      | Done => sched_log
      | Cons r s => interp_try r s s
      | Try r s1 s2 => interp_try r s1 s2
      | SPos _ s => interp_scheduler' sched_log s
      end.

    Definition interp_scheduler (s: scheduler) :=
      interp_scheduler' log_empty s.
  End Scheduler.

  Definition interp_cycle (sigma: forall f, Sig_denote (Sigma f)) (rules: rule_name_t -> rule)
             (s: scheduler) (r: REnv.(env_t) R) :=
    commit_update r (interp_scheduler r sigma rules s).
End Interp.

Notation interp_args r sigma Gamma sched_log action_log args :=
  (interp_args' (@interp_action _ _ _ _ _ _ _ _ r sigma) Gamma sched_log action_log args).
