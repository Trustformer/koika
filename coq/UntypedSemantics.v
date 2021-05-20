(*! Language | Semantics of typed Kôika programs !*)
Require Export Koika.Common Koika.Environments Koika.UntypedLogs Koika.Syntax.

(* This semantics aims at making the demonstration of properties easier in
   Kôika. It achieves this by avoiding the use of dependent typing, among other
   things. *)

(* Custom tactics *)
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

  (* We define a "val" inductive mirroring the "type" inductive found in
     Types.v. It allows us to limit the use of dependent typing, simplifying
     proofs further down the line. *)
  Inductive val :=
  | Bits (sz: nat) (v: list bool)
  | Enum (sig: enum_sig) (v: list bool)
  | Struct (sig: struct_sig) (v: list val)
  | Array (sig: array_sig) (v: list val).

  Context {Sigma: ext_fn_t -> ExternalSignature}.
  Context {REnv: Env reg_t}.

  Notation Log := (@_ULog val reg_t REnv).

  (* TODO Notation rule := (rule pos_t var_t fn_name_t R Sigma). *)
  Notation uaction := (uaction pos_t var_t fn_name_t reg_t ext_fn_t).
  (* TODO Notation scheduler := (scheduler pos_t rule_name_t). *)

  Definition tcontext (sig: tsig var_t) := context (fun k_tau => val) sig.

  Definition acontext (sig argspec: tsig var_t) :=
    context (fun k_tau => uaction) argspec.

  Section Action.
    Context (r: REnv.(env_t) (fun _ => val)).
    Context (sigma: forall f, Sig_denote (Sigma f)).

    Section Args.
      Context (
        interp_uaction:
          forall {sig: tsig var_t} {tau} (Gamma: tcontext sig) (sched_log: Log)
          (action_log: Log) (a: uaction),
          option (Log * type_denote tau * (tcontext sig))
      ).

      (* TODO *)
      (* Fixpoint interp_args' *)
      (*   {sig: tsig var_t} (Gamma: tcontext sig) (sched_log: Log) *)
      (*   (action_log: Log) {argspec: tsig var_t} (args: acontext sig argspec) *)
      (*   : option (Log * tcontext argspec * (tcontext sig)) *)
      (* := *)
      (*   match args with *)
      (*   | CtxEmpty => Some (action_log, CtxEmpty, Gamma) *)
      (*   | @CtxCons _ _ argspec k_tau arg args => *)
      (*     let/opt3 action_log, ctx, Gamma := *)
      (*       interp_args' Gamma sched_log action_log args in *)
      (*     let/opt3 action_log, v, Gamma := *)
      (*       interp_uaction _ _ Gamma sched_log action_log arg in *)
      (*     Some (action_log, CtxCons k_tau v ctx, Gamma) *)
      (*   end. *)
    End Args.

    (* Get the value of var k from the context (value of let bindings) *)
    Fixpoint ucassoc {sig: tsig var_t} (Gamma: tcontext sig) (k: var_t)
      : option val
    :=
      match Gamma with
      | CtxEmpty => None
      | CtxCons k' v Gamma =>
        if eq_dec k (fst k') then Some v else ucassoc Gamma k
      end.

    (* Cassoc tracks membership using dependent typing. If there is proof that
       a context has x as a member, then ucassoc should return
       Some (cassoc x) *)
    Lemma cassoc_ucassoc:
      forall (sig: tsig var_t) (ND: NoDup (map fst sig)) (Gamma: tcontext sig) k
      (m: member k sig), ucassoc Gamma (fst k) = Some (cassoc m Gamma).
    Proof.
      induction Gamma.
      - simpl. intros. inversion m.
      - intros. simpl. destruct eq_dec.
        + destruct k, k0; simpl in *. subst. inversion m; subst.
          * generalize (fun nd =>
              member_NoDup (v0, t) (EqDec_pair _ _) nd m (MemberHd _ _)
            ). intros. rewrite H.
            { simpl. auto. }
            { apply NoDup_map_inv with (f:= fst). simpl; auto. }
          * apply member_In in X. inversion ND. subst. exfalso; apply H1.
            apply in_map_iff. eexists; split.
            2: apply X. reflexivity.
        + inversion m.
          * subst. congruence.
          * subst.
            generalize (
              fun nd => member_NoDup k0 (EqDec_pair _ _) nd m (MemberTl _ _ _ X)
            ). intros. rewrite H.
            { simpl. eapply IHGamma. simpl in ND; inversion ND; auto. }
            { apply NoDup_map_inv with (f:= fst). simpl; auto. }
    Qed.

    (* The values of elements of type "type" are tracked dependently (see
       "type_denote" in Types.v): x represents the contents of a given variable
      of type tau. Of course, we can generate a val using this information. *)
    Fixpoint val_of_value {tau: type} (x: type_denote tau) {struct tau} : val :=
      let val_of_struct_value := (
        fix val_of_struct_value {fields} (x: struct_denote fields) : list val :=
          match fields return struct_denote fields -> list val with
          | [] => fun _ => []
          | (nm, tau) :: fields => fun '(x, xs) =>
            val_of_value x :: (val_of_struct_value xs)
          end x
      ) in
      match tau return type_denote tau -> val with
      | bits_t sz => fun bs => Bits sz (vect_to_list bs)
      | enum_t sig => fun bs => Enum sig (vect_to_list bs)
      | struct_t sig => fun str => Struct sig (val_of_struct_value str)
      | array_t sig => fun v => Array sig (map val_of_value (vect_to_list v))
      end x.

    (* Get raw contents. *)
    Fixpoint ubits_of_value (v: val) : list bool :=
      match v with
      | Bits _ bs => bs
      | Enum _ bs => bs
      | Struct _ lv => List.concat (rev (map ubits_of_value lv))
      | Array _ lv => List.concat (rev (map ubits_of_value lv))
      end.

    (* Proof of the conservation of size. *)
    Lemma ubits_of_value_len:
      forall {tau} (v: type_denote tau) bs,
      ubits_of_value (val_of_value v) = bs -> List.length bs = type_sz tau.
    Proof.
      fix IHt 1. destruct tau; simpl; intros; subst.
      - apply vect_to_list_length.
      - apply vect_to_list_length.
      - revert sig v. destruct sig. simpl.
        induction struct_fields; simpl; intros.
        + subst. reflexivity.
        + destruct a. destruct v. simpl. rewrite List.concat_app. simpl.
          rewrite app_length. simpl. rewrite IHstruct_fields.
          unfold struct_fields_sz. simpl. f_equal. rewrite app_nil_r.
          eapply IHt; eauto.
      - revert sig v. destruct sig. simpl. intros. induction array_len; simpl.
        + auto.
        + destruct v. simpl. rewrite concat_app. rewrite app_length. simpl.
          unfold vect_to_list in IHarray_len. rewrite IHarray_len.
          clear IHarray_len. f_equal. rewrite app_nil_r. eapply IHt. eauto.
    Qed.

    (* Proof of the conservation of contents (TODO does this not imply
       ubits_of_value_len?) *)
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
          rewrite <- (IHt _ t0 _ eq_refl). rewrite <- vect_to_list_app.
          reflexivity.
      - revert sig v. destruct sig. simpl. intros.
        induction array_len; simpl.
        + auto.
        + destruct v. simpl.
          rewrite vect_to_list_app. rewrite IHarray_len. clear IHarray_len.
          rewrite concat_app. f_equal. simpl.
          rewrite app_nil_r. eapply IHt. eauto.
    Qed.

    (* Update a let binding (if present) *)
    Fixpoint replace {sig: tsig var_t} k (v: val) (Gamma: tcontext sig)
      : tcontext sig
    :=
      match Gamma with
      | CtxEmpty => CtxEmpty
      | CtxCons k0 v0 Gamma =>
        if eq_dec k (fst k0) then CtxCons k0 v Gamma
        else CtxCons k0 v0 (replace k v Gamma)
      end.

    (* TODO Remove if unused *)
    Definition bits_split (n: nat) {sz} (v: bits sz)
      : option (bits n * bits (sz - n)).
    Proof.
      destruct (lt_dec n sz). 2: exact None.
      replace sz with (n + (sz - n)) in v. 2: lia.
      destruct (Bits.split v) eqn:?.
      exact (Some (v0, v1)).
    Defined.

    (* Split list, opt return *)
    Fixpoint take_drop {A: Type} (n: nat) (l: list A)
      : option (list A * list A)
    :=
      match n with
      | O => Some ([], l)
      | S n =>
        match l with
        | [] => None
        | a::l => let/opt2 l1, l2 := take_drop n l in Some (a::l1, l2)
        end
      end.

    (* Split bits into nb sz_elt long lists *)
    Fixpoint bits_splitn (nb sz_elt: nat) (bs: list bool)
      : option (list (list bool))
    :=
      match nb with
      | O => Some []
      | S nb =>
        let/opt2 hd, rest := take_drop sz_elt bs in
        let/opt tl := bits_splitn nb sz_elt rest in
        Some (hd :: tl)
      end.

    (* Proof that take_drop returns something when n <= length *)
    Lemma take_drop_succeeds:
      forall {A:Type} (n: nat) (l: list A) (LT: n <= Datatypes.length l),
      exists la lb, take_drop n l = Some (la, lb).
    Proof.
      induction n; simpl; intros; eauto.
      destruct l; simpl in LT. lia.
      destruct (IHn l) as (la & lb & EQ). lia.
      rewrite EQ. simpl. eauto.
    Qed.

    (* take_drop specification *)
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

    (* Proof that take_drop n l = Some (l, []) when n is the size of l *)
    Lemma take_drop_succeeds_eq:
      forall {A:Type} (n: nat) (l: list A) (LT: n = Datatypes.length l),
      take_drop n l = Some (l, []).
    Proof.
      induction n; simpl; intros; eauto.
      destruct l; simpl in LT. reflexivity. lia.
      destruct l; simpl in LT; try lia.
      rewrite IHn; simpl; auto.
    Qed.

    (* Proof about the behavior of take_drop on concatenated lists *)
    Lemma take_drop_head:
      forall {A} n (l1 l2: list A),
      n = List.length l1 -> take_drop n (l1 ++ l2) = Some (l1, l2).
    Proof.
      intros. subst. revert l2.
      induction l1; simpl; intros; subst; eauto.
      rewrite IHl1. simpl. reflexivity.
    Qed.

    (* Split list, un-opt return *)
    Definition take_drop' {A: Type} n (l: list A) :=
      match take_drop n l with
      | None => (l, [])
      | Some (l1, l2) => (l1, l2)
      end.

    (* Proof that take_drop' interacts as expected with concatenation *)
    Lemma take_drop'_cons:
      forall {A} (l l1 l2: list A) a n,
      take_drop' n l = (l1, l2) -> take_drop' (S n) (a::l) = (a::l1, l2).
    Proof.
      unfold take_drop'. simpl. intros. destruct (take_drop n l) eqn:?.
      - destruct p. inversion H; subst. simpl. auto.
      - simpl. inversion H; subst. auto.
    Qed.

    (* take_drop' specification *)
    Lemma take_drop'_spec:
      forall {A:Type} (n: nat) (l la lb: list A),
      take_drop' n l = (la, lb) ->
      l = la ++ lb /\ List.length la <= n /\
        List.length lb = List.length l - List.length la.
    Proof.
      induction n; simpl; intros; eauto.
      inversion H; clear H; subst. repeat split; try reflexivity. simpl; lia.
      destruct l; simpl in *. unfold take_drop' in H. simpl in *.
      inversion H; clear H.
      simpl. repeat split; lia.
      destruct (take_drop' n l) as (l1 & l2) eqn:?.
      erewrite take_drop'_cons in H; eauto. inversion H; subst. simpl.
      apply IHn in Heqp. destruct Heqp as (EQ1 & EQ2 & EQ3). subst.
      repeat split; auto. lia.
    Qed.

    (* Vanilla list property TODO remove if unused *)
    Lemma app_eq_inv:
      forall {A:Type} (a b c d: list A),
      a ++ b = c ++ d -> List.length a = List.length c -> a = c /\ b = d.
    Proof.
      induction a; simpl; intros; eauto.
      - destruct c; simpl in H0; try congruence.
        simpl in *. auto.
      - destruct c; simpl in H0; try congruence.
        simpl in *. inversion H; clear H; subst.
        apply IHa in H3. destruct H3; subst; auto. lia.
    Qed.

    (* Correspondence between vals and types TODO Well-typed values? *)
    Inductive wt_val: type -> val -> Prop :=
    | wt_bits: forall n bs, List.length bs = n -> wt_val (bits_t n) (Bits n bs)
    | wt_enum: forall sig bs,
        List.length bs = enum_bitsize sig -> wt_val (enum_t sig) (Enum sig bs)
    | wt_struct: forall sig lv,
        Forall2 (fun nt v => wt_val nt v) (map snd (struct_fields sig)) lv ->
        wt_val (struct_t sig) (Struct sig lv)
    | wt_array: forall sig lv,
        Forall (fun v => wt_val (array_type sig) v) lv ->
        List.length lv = array_len sig -> wt_val (array_t sig) (Array sig lv).

    (* Complexity of a type (not a size in bits!) *)
    Fixpoint size_type (t: type) :=
      match t with
      | bits_t n => 1
      | enum_t sig => 1
      | struct_t sig =>
        1 + list_sum (List.map (fun '(_, t) => size_type t) (struct_fields sig))
      | array_t sig => 1 + size_type (array_type sig)
      end.

    (* Equivalent definition for val *)
    Fixpoint size_val (v: val) :=
      match v with
      | Bits _ _ => 1
      | Enum _ _ => 1
      | Struct sig lv => 1 + list_sum (map size_val lv)
      | Array sig lv => 1 + list_sum (map size_val lv)
      end.

    (* Induction principle for wt_vals *)
    Lemma wt_val_ind':
      forall (P : type -> val -> Prop)
       (Hbits: forall (n : nat) (bs : list bool),
         Datatypes.length bs = n -> P (bits_t n) (Bits n bs)
       )
       (Henum: forall (sig : enum_sig) (bs : list bool),
         Datatypes.length bs = enum_bitsize sig ->
         P (enum_t sig) (Enum sig bs)
       )
       (Hstruct: forall (sig : struct_sig) (lv : list val),
         Forall2 (fun (nt : type) (v : val) => wt_val nt v)
         (map snd (struct_fields sig)) lv ->
         Forall2 (fun (nt : type) (v : val) => wt_val nt v -> P nt v)
         (map snd (struct_fields sig)) lv ->
         P (struct_t sig) (Struct sig lv)
       )
       (Harray: forall (sig : array_sig) (lv : list val),
         Forall (fun v : val => wt_val (array_type sig) v) lv ->
         Forall (fun v : val => wt_val (array_type sig) v ->
         P (array_type sig) v) lv ->
         Datatypes.length lv = array_len sig -> P (array_t sig) (Array sig lv)
       ), forall (t : type) (v : val), wt_val t v -> P t v.
    Proof.
      intros P Hbits Henum Hstruct Harray t v.
      remember (size_type t).
      revert t v Heqn.
      pattern n.
      eapply Nat.strong_right_induction with (z:=0).
      { red. red. intros. subst. tauto. } 2: lia.
      intros n0 _ Plt t t0 a Heqn.
      assert (Plt': forall t v, size_type t < n0 -> wt_val t v -> P t v).
      { intros. eapply Plt. 3: reflexivity. lia. auto. auto. }
      clear Plt.
      rename Plt' into Plt.
      subst.
      inversion Heqn; subst; eauto.
      - eapply Hstruct. eauto.
        revert H.
        simpl in Plt.
        assert (
          Forall (fun '(n,t) => forall v, wt_val t v -> P t v)
          (struct_fields sig)
        ).
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

    (* Vanilla list property *)
    Lemma length_concat_same:
      forall {A} (l: list (list A)) sz,
      Forall (fun x => List.length x = sz) l ->
      Datatypes.length (List.concat l) = List.length l * sz.
    Proof.
      induction 1; simpl; intros; eauto.
      rewrite app_length; rewrite IHForall. lia.
    Qed.

    (* Proof of the correspondence between type_sz and the size of the item in
       bits *)
    Lemma ubits_of_value_len':
      forall tau v,
      wt_val tau v -> List.length (ubits_of_value v) = type_sz tau.
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

    (* Proof about the interaction between splitn and concat*)
    Lemma bits_splitn_concat:
      forall sz l n,
      Forall (fun l => List.length l = sz) l -> List.length l = n ->
      bits_splitn n sz (List.concat l) = Some l.
    Proof.
      intros. subst.
      induction H; simpl; intros; auto.
      rewrite take_drop_head; auto. simpl.
      rewrite IHForall. simpl. reflexivity.
    Qed.

    (* Convert from raw bits to val of a given type *)
    (* TODO Behavior when list too short? *)
    (* TODO Always returns something, why option? *)
    Fixpoint uvalue_of_bits {tau: type} (bs: list bool) {struct tau}
      : option val
    :=
      let uvalue_of_struct_bits := (
        fix uvalue_of_struct_bits {fields: list (string * type)} (bs: list bool)
          : option (list val)
        :=
          match fields with
          | [] => Some []
          | (nm, tau) :: fields =>
            let/opt2 b0, b1 := take_drop (List.length bs - type_sz tau) bs in
            let/opt tl := uvalue_of_struct_bits (fields:=fields) b0 in
            let/opt hd := uvalue_of_bits (tau:=tau) b1 in
            Some ( hd :: tl)
          end
      ) in
      let uvalue_of_list_bits tau := (
        fix uvalue_of_list_bits (l : list (list bool)) : option (list val) :=
          match l with
          | [] => Some []
          | hd::tl =>
            let/opt hd := uvalue_of_bits (tau:=tau) hd in
            let/opt tl := uvalue_of_list_bits tl in
            Some (hd::tl)
          end
      ) in
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
        let/opt lbs :=
          bits_splitn (array_len sig) (type_sz (array_type sig)) bs in
        let/opt lv := uvalue_of_list_bits (array_type sig) (rev lbs) in
        Some (Array sig lv)
      end
    .

    (* Proof about the  *)
    Lemma uvalue_of_bits_val:
      forall tau v,
      wt_val tau v -> uvalue_of_bits (tau:=tau) (ubits_of_value v) = Some v.
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
      - assert (
          Forall (
            fun v =>
              wt_val (array_type sig) v /\
              uvalue_of_bits (tau:= array_type sig) (ubits_of_value v) = Some v
          ) lv).
        { rewrite Forall_forall in *; simpl; intros. split; eauto. }
        clear H H0.
        rewrite bits_splitn_concat.
        simpl.
        rewrite rev_involutive.
        cut ((
          fix uvalue_of_list_bits (l : list (list bool)) : option (list val) :=
          match l with
          | [] => Some []
          | hd :: tl =>
            let/opt hd0 := uvalue_of_bits (tau:=array_type sig) hd in
            (let/opt tl0 := uvalue_of_list_bits tl in Some (hd0 :: tl0))
          end
          ) ((map ubits_of_value lv)) = Some lv
        ).
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

    (*
    Lemma struct_eq:
      forall fields x,
      rev ((
        fix val_of_struct_value
          (fields : list (string * type)) (x : struct_denote fields)
          {struct fields}
        : list val :=
          match fields as fields0
          return (struct_denote fields0 -> list val) with
          | [] => fun _ : unit => []
          | p :: fields0 =>
            let (_, tau) as p0
              return (snd p0 * struct_denote fields0 -> list val) := p in
            fun '(x0, xs) => val_of_value x0 :: val_of_struct_value fields0 xs
          end x
      ) fields x) = (
        fix val_of_struct_value
          (fields : list (string * type)) (x : struct_denote fields)
          {struct fields}
        : list val :=
        match fields as fields0 return (struct_denote fields0 -> list val) with
        | [] => fun _ : unit => []
        | p :: fields0 =>
          let (_, tau) as p0
            return (snd p0 * struct_denote fields0 -> list val) := p in
          fun '(x0, xs) => [val_of_value x0] ++ val_of_struct_value fields0 xs
        end x
      ) fields x.
    Proof.
      induction fields. reflexivity. intros. destruct a. destruct x.
      rewrite rev_app_distr. simpl. f_equal. eauto.
    Qed.
   *)

    Lemma wt_val_of_value:
      forall (tau: type) (v: tau), wt_val tau (val_of_value v).
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
        rewrite map_length. rewrite vect_to_list_length. auto.
    Qed.

    Lemma uvalue_of_bits_val':
      forall tau v,
      uvalue_of_bits (tau:=tau) (ubits_of_value (val_of_value (tau:=tau) v)) =
      Some (val_of_value (tau:=tau) v).
    Proof. intros. apply uvalue_of_bits_val. apply wt_val_of_value. Qed.

    Import PrimUntyped.
    Definition usigma1' (fn: PrimUntyped.ubits1) (bs: list bool)
      : option (list bool)
    :=
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
      | Bits _ bs =>
        let/opt res := usigma1' fn bs in Some (Bits (List.length res) res)
      | _ => None
      end.

    Fixpoint get_field_struct (s: list (string * type)) (lv: list val) f
      : option val
    :=
      match s, lv with
      | (n, _)::s, a::lv =>
        if eq_dec n f then Some a else get_field_struct s lv f
      | _, _ => None
      end.

    (* TODO Why commented out initially (works unchanged)? *)
    Fixpoint find_field (s: list (string * type)) f : option (nat * nat) :=
      match s with
      | (n, t)::s =>
        if eq_dec f n
        then Some (0, type_sz t)
        else
          let/opt2 ofs, sz := find_field s f in
          Some (ofs + type_sz t, sz)
      | _ => None
      end.

    Fixpoint find_field_offset_right (s: list (string * type)) f
      : option (nat * nat)
    :=
      match s with
      | (n, t)::s =>
        if eq_dec f n then Some (struct_fields_sz s, type_sz t)
        else find_field_offset_right s f
      | [] => None
      end.

    Definition get_field (s: val) f : option val :=
      match s with
      | Struct sig lv => get_field_struct (struct_fields sig) lv f
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
        | PrimUntyped.UUnpack tau => fun bs =>
            match bs with
            | Bits _ bs => let/opt v := uvalue_of_bits (tau:=tau) bs in Some v
            | _ => None
            end
        | PrimUntyped.UIgnore => fun _ => Some (Bits 0 [])
        end
      | PrimUntyped.UBits1 fn => usigma1 fn
      | PrimUntyped.UStruct1 (PrimUntyped.UGetField f) => fun v => get_field v f
      | PrimUntyped.UStruct1 (UGetFieldBits sig f) => fun v =>
          let/opt2 ofs, sz := find_field_offset_right (struct_fields sig) f in
          usigma1 (USlice ofs sz) v
      | PrimUntyped.UArray1 (PrimUntyped.UGetElement idx) => fun v =>
          match v with
          | Array sig l => List.nth_error l idx
          | _ => None
          end
      | PrimUntyped.UArray1 (PrimUntyped.UGetElementBits sig idx) =>
        fun v => usigma1 (
          USlice (element_sz sig * (array_len sig - S idx)) (element_sz sig)
        ) v
      end.

  Lemma uvalue_of_bits_val_of_value:
    forall (tau: type) (v: vect bool (type_sz tau)),
    uvalue_of_bits (tau := tau) (vect_to_list v)
    = Some (val_of_value (value_of_bits v)).
  Proof.
    intros; rewrite <- uvalue_of_bits_val'. f_equal.
    erewrite <- ubits_of_value_ok. 2: eauto.
    rewrite bits_of_value_of_bits. auto.
  Qed.

  Lemma repeat_bits_const:
    forall x n, repeat x n = vect_to_list (Bits.const n x).
  Proof.
    induction n; simpl; auto.
    rewrite IHn. reflexivity.
  Qed.

  Lemma last_nth:
    forall {A} d (l: list A), last l d = nth (List.length l - 1) l d.
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
    rewrite IHs. destruct v. simpl. reflexivity.
  Qed.

  Lemma msb_spec:
    forall s (v: bits s), Bits.msb v = last (vect_to_list v) false.
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
    forall e s (v: bits s), vect_to_list (v~e) = e:: vect_to_list v.
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
    forall {A:Type} (n: nat) (l la lb: list A), take_drop' n l = (la, lb) ->
    l = la ++ lb /\ List.length la = Nat.min n (List.length l).
  Proof.
    induction n; simpl; intros; eauto.
    inversion H; clear H; subst. repeat split; try reflexivity.
    destruct l; simpl in *. unfold take_drop' in H. simpl in *.
    inversion H; clear H.
    simpl. repeat split; lia.
    destruct (take_drop' n l) as (l1 & l2) eqn:?.
    erewrite take_drop'_cons in H; eauto. inv H. simpl.
    apply IHn in Heqp. destruct Heqp as (EQ1 & EQ2). subst.
    repeat split; auto.
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
      + destr_in H; try congruence. inv H. simpl in *. inv Heqr0.
        subst. reflexivity.
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
    - subst. destr_in H. inv H. simpl in *. inv Heqr0.
      revert arg. rewrite <- H0. simpl. destruct fn; simpl in *; intros.
      + rewrite map_length. rewrite vect_to_list_length. f_equal.
        f_equal. rewrite <- vect_to_list_map. f_equal.
      + f_equal. f_equal.
        * rewrite app_length.
          rewrite repeat_length. rewrite vect_to_list_length. lia.
        * unfold Bits.extend_end. simpl.
          rewrite vect_to_list_eq_rect. rewrite vect_to_list_app. f_equal.
          rewrite vect_to_list_length.
          rewrite repeat_bits_const. f_equal. f_equal. rewrite msb_spec; auto.
      + f_equal. f_equal.
        * rewrite app_length.
          rewrite repeat_length. rewrite vect_to_list_length. lia.
        * unfold Bits.extend_end. simpl.
          unfold eq_rect.
          refine (match vect_extend_end_cast s width with eq_refl => _ end)
          rewrite vect_to_list_app. f_equal. rewrite vect_to_list_length.
          rewrite repeat_bits_const. f_equal.
      + f_equal. f_equal.
        * rewrite app_length.
          rewrite repeat_length. rewrite vect_to_list_length. lia.
        * unfold Bits.extend_beginning. simpl.
          unfold eq_rect.
          refine (match vect_extend_beginning_cast s width with eq_refl => _ end).
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
        apply take_drop'_spec in Heq2. apply take_drop'_spec in Heq1.
        intuition subst. rewrite app_length. rewrite repeat_length. lia.
        unfold Bits.slice.

        rewrite vect_extend_end_firstn.
        unfold Bits.extend_end.
        rewrite vect_to_list_eq_rect. rewrite vect_to_list_app.
        rewrite vect_firstn_to_list. rewrite vect_skipn_to_list.
        rewrite Heq1. simpl. rewrite Heq2. simpl. rewrite <- repeat_bits_const.
        f_equal. f_equal. f_equal.

        apply take_drop'_spec2 in Heq2.
        destruct Heq2 as (Heq21 & Heq22). rewrite Heq22.
        apply take_drop'_spec2 in Heq1. destruct Heq1 as (Heq11 & Heq12).
        cut (List.length l2 = s - List.length l1).
        intro A; rewrite A. rewrite Heq12.
        rewrite vect_to_list_length. lia.
        erewrite <- (vect_to_list_length (sz:=s)). rewrite Heq11.
        rewrite app_length. lia.
      + inv H.
    - destr_in H.
      + repeat destr_in H; inv H.
        simpl in Heqr0. clear Heqr0. simpl in arg.
        simpl PrimSpecs.sigma1.
        simpl.
        unfold PrimTypeInference.find_field in Heqr1. unfold opt_result in Heqr1.
        destr_in Heqr1; inv Heqr1.
        revert s0 Heqo arg. destruct s. simpl. clear.
        induction struct_fields; intros; eauto. easy.
        destruct a. destruct arg.
        Opaque eq_dec.
        simpl. simpl in Heqo.
        destr_in Heqo. inv Heqo. simpl in *. rewrite Heqs2. auto.
        destr. subst. congruence.
        destr_in Heqo; inv Heqo.
        erewrite IHstruct_fields; eauto. reflexivity.
      + destr_in H; inv H.
        simpl PrimSpecs.sigma1.
        simpl.
        assert (
          forall sig (i: index (List.length (struct_fields sig))),
          PrimTypeInference.find_field sig f = Success i ->
          find_field_offset_right (struct_fields sig) f =
            Some (field_offset_right sig i, field_sz sig i)
        ).
        {
          clear. intros sig i FF.
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
        }
        erewrite H; eauto. simpl. destr. destr. simpl. f_equal.
        unfold take_drop' in Heqp.
        edestruct (@take_drop_succeeds) as (la & lb & EQ).
        2: rewrite EQ in Heqp.
        rewrite vect_to_list_length.
  Abort.

  Lemma struct_fields_sz_skipn:
    forall n f, struct_fields_sz (skipn n f) <= struct_fields_sz f.
  Proof.
    induction n; simpl; intros; eauto. destr. auto.
    etransitivity. apply IHn. unfold struct_fields_sz. simpl. lia.
  Qed.

  Lemma field_offset_right_le:
    forall sig s, field_offset_right sig s <= struct_sz sig.
  Proof.
    unfold field_offset_right, struct_sz. simpl type_sz.
    intros; apply struct_fields_sz_skipn.
  Qed.

  (* TODO What is all of this? *)
  (*
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
    rewrite H1.
    clear H0 H1.
    eapply take_drop_spec in EQ. intuition.
    rewrite H3. rewrite vect_to_list_length. reflexivity.
- destr_in H.
  + repeat destr_in H; inv H. simpl in *.
    rewrite <- vect_nth_map. rewrite <- vect_to_list_map.
    rewrite <- vect_to_list_nth. f_equal.
    unfold PrimTypeInference.check_index in Heqr1.
    unfold opt_result in Heqr1. destr_in Heqr1; inv Heqr1.
    symmetry; apply index_to_nat_of_nat. auto.
  + destr_in H; inv H. simpl in *. destr. destr. simpl.
    unfold PrimTypeInference.check_index in Heqr0.
    unfold opt_result in Heqr0. destr_in Heqr0; inv Heqr0.
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
  *)
  Qed.

  Definition enum_sig_eq_dec (s1 s2: enum_sig) : {s1 = s2} + {s1 <> s2}.
  Proof.
    destruct s1, s2; simpl.
    destruct (eq_dec enum_name enum_name0).
    2: right; intro A; inv A; congruence.
    destruct (eq_dec enum_size enum_size0).
    2: right; intro A; inv A; congruence.
    destruct (eq_dec enum_bitsize enum_bitsize0).
    2: right; intro A; inv A; congruence.
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
    destruct (eq_dec struct_name struct_name0).
    2: right; intro A; inv A; congruence.
    destruct (eq_dec struct_fields struct_fields0).
    2: right; intro A; inv A; congruence.
    left; subst; reflexivity.
  Defined.

  Lemma val_ind':
    forall (P : val -> Type)
     (Hbits: forall (n : nat) (bs : list bool), P (Bits n bs))
     (Henum: forall (sig : enum_sig) (bs : list bool), P (Enum sig bs))
     (Hstruct: forall (sig : struct_sig) (lv : list val),
       (forall x, In x lv -> P x) -> P (Struct sig lv)
     )
     (Harray: forall (sig : array_sig) (lv : list val),
       (forall x, In x lv -> P x) -> P (Array sig lv)
     ),
    forall (v : val), P v.
  Proof.
    intros P Hbits Henum Hstruct Harray v.
    remember (size_val v).
    revert v Heqn.
    pattern n.
  Abort.

  Lemma strong_ind_type:
    forall (P: nat -> Type) (IH: forall n, (forall m, m < n -> P m) -> P n),
    forall n, forall m, m <= n -> P m.
  Proof.
    induction n. intros. apply IH. lia.
    intros. destruct (le_dec m n); eauto.
    assert (m = S n) by lia. clear H n0. subst.
    apply IH. intros. apply IHn; auto. lia.
  Qed.

  (* TODO What is this?
    eapply strong_ind_type. 2: reflexivity.
    intros n0 Plt v Heqn.
    assert (Plt':
              forall v,
                size_val v < n0 -> P v
           ).
    { intros. eapply Plt. 2: reflexivity. lia. } clear Plt.
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
  *)

    Definition list_eq_dec'
    {A: Type} (l1 l2: list A) (Aeq: forall x y, In x l1 -> {x = y} + {x <> y})
    : {l1 = l2} + {l1 <> l2}.
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
      destruct (enum_sig_eq_dec sig sig0);
        try (right; intro A; inv A; congruence).
      destruct (eq_dec bs v); try (right; intro A; inv A; congruence).
      subst; left; reflexivity.
    - destruct v2; try (right; intro A; inv A; congruence).
      destruct (struct_sig_eq_dec sig sig0);
        try (right; intro A; inv A; congruence).
      destruct (list_eq_dec' lv v); try (right; intro A; inv A; congruence).
      eauto. left; subst. reflexivity.
    - destruct v2; try (right; intro A; inv A; congruence).
      destruct (eq_dec sig sig0); subst. 2: (right; intro A; inv A; congruence).
      destruct (list_eq_dec' lv v); try (right; intro A; inv A; congruence).
      eauto.  left; subst. reflexivity.
    Defined.

    (* Definition ubits2_sigma (ub: ubits2) (v1 v2: list bool) : list bool := *)
    (*   match ubits2 with *)
    (*   | UAnd =>  *)

    Definition sigma2 (fn: ufn2) (v1 v2: val) : option val :=
    match fn with
    | UEq false  => if val_eq_dec v1 v2 then Bits 1 [true] else Bits 1 [false]
    | UEq true  => if val_eq_dec v1 v2 then Bits 1 [false] else Bits 1 [true]
    | UBits2 fn =>
    | Struct2 SubstField sig idx => fun s v =>
    subst_field sig.(struct_fields) s idx v
    | Array2 SubstElement sig idx => fun a e => vect_replace a idx e
    end.

    Fixpoint interp_action {sig: tsig var_t} (Gamma: tcontext sig)
    (sched_log: Log) (action_log: Log) (a: uaction) {struct a}
    : option (Log * val * (tcontext sig)) :=
    match a with
    | UError e => None
    | USugar _ => None
    | UVar var =>
      let/opt v := ucassoc Gamma var in
      Some (action_log, v, Gamma)
    | @UConst _ _ _ _ _ tau cst =>
        Some (action_log, val_of_type_cst _ cst, Gamma)
    | UAssign k a =>
      let/opt3 action_log, v, Gamma :=
        interp_action Gamma sched_log action_log a in
      Some (action_log, Bits _ Ob, replace k v Gamma)
    | USeq a1 a2 =>
      let/opt3 action_log, v, Gamma :=
        interp_action Gamma sched_log action_log a1 in
      interp_action Gamma sched_log action_log a2
    | UBind k a1 a2 =>
      let/opt3 action_log, v, Gamma
        := interp_action Gamma sched_log action_log a1 in
      let/opt3 action_log, v, Gamma := interp_action
        (CtxCons (k, bits_t 0) v Gamma) sched_log action_log a2
      in Some (action_log, v, ctl Gamma)
    | UIf cond athen aelse =>
      let/opt3 action_log, v, Gamma :=
        interp_action Gamma sched_log action_log cond in
      match v with
      | Bits 1 b =>
        if Bits.single b then interp_action Gamma sched_log action_log athen
        else interp_action Gamma sched_log action_log aelse
      | _ => None
      end
    | URead prt idx =>
      if may_read sched_log prt idx then
        Some (log_cons idx (LE LogRead prt (Bits 0 (vect_nil))) action_log,
          match prt with
          | P0 => REnv.(getenv) r idx
          | P1 =>
            match latest_write0 (V:=val) (log_app action_log sched_log) idx with
            | Some v => v
            | None => REnv.(getenv) r idx
            end
        end, Gamma)
      else None
    | UWrite prt idx v =>
      let/opt3 action_log, val, Gamma :=
        interp_action Gamma sched_log action_log v in
      if may_write sched_log action_log prt idx then
        Some (
          log_cons idx (LE LogWrite prt val) action_log, Bits _ Bits.nil, Gamma
        )
      else None
    | UUnop fn arg =>
      let/opt3 action_log, arg1, Gamma :=
        interp_action Gamma sched_log action_log arg in
      Some (action_log, (PrimSpecs.sigma1 fn) arg1, Gamma)
    | _ => None
    end.

    | Unop fn arg1 => fun Gamma =>
      let/opt3 action_log, arg1, Gamma :=
        interp_action Gamma sched_log action_log arg1 in
      Some (action_log, (PrimSpecs.sigma1 fn) arg1, Gamma)
    | Binop fn arg1 arg2 => fun Gamma =>
      let/opt3 action_log, arg1, Gamma :=
        interp_action Gamma sched_log action_log arg1 in
      let/opt3 action_log, arg2, Gamma :=
        interp_action Gamma sched_log action_log arg2 in
      Some (action_log, (PrimSpecs.sigma2 fn) arg1 arg2, Gamma)
    | ExternalCall fn arg1 => fun Gamma =>
      let/opt3 action_log, arg1, Gamma :=
        interp_action Gamma sched_log action_log arg1 in
      Some (action_log, sigma fn arg1, Gamma)
    | InternalCall name args body => fun Gamma =>
      let/opt3 action_log, results, Gamma :=
        interp_args' (@interp_action) Gamma sched_log action_log args in
      let/opt3 action_log, v, _ :=
        interp_action results sched_log action_log body in
      Some (action_log, v, Gamma)
    | APos _ a => fun Gamma =>
      interp_action Gamma sched_log action_log a
    end Gamma.

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

    Fixpoint interp_scheduler' (sched_log: Log) (s: scheduler) {struct s} :=
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

    Definition interp_cycle
    (sigma: forall f, Sig_denote (Sigma f)) (rules: rule_name_t -> rule)
    (s: scheduler) (r: REnv.(env_t) R)
    :=
    commit_update r (interp_scheduler r sigma rules s).
    End Interp.

    Notation interp_args r sigma Gamma sched_log action_log args := (
    interp_args' (@interp_action _ _ _ _ _ _ _ _ r sigma)
    Gamma sched_log action_log args
    ).
