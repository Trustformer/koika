(*! Language | Semantics of typed Kôika programs !*)
Require Export Koika.Common Koika.Environments Koika.ULogs Koika.Syntax
  Koika.Syntax.

Section Interp.
  Context {pos_t var_t fn_name_t reg_t ext_fn_t: Type}.
  Context {reg_t_eq_dec: EqDec reg_t}.
  Context {var_t_eq_dec: EqDec var_t}.

  Inductive val :=
  | Bits (n: nat) (v: bits n)
  | Enum (sig: enum_sig) (v: bits (enum_bitsize sig))
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
    Context (r: REnv.(env_t) (fun _ => val)).
    Context (sigma: forall f, Sig_denote (Sigma f)).

    (* Section Args. *)
    (*   Context (interp_action: *)
    (*              forall {sig: tsig var_t} {tau} *)
    (*                (Gamma: tcontext sig) *)
    (*                (sched_log: Log) (action_log: Log) *)
    (*                (a: action sig tau), *)
    (*                option (Log * type_denote tau * (tcontext sig))). *)

    (*   Fixpoint interp_args' *)
    (*            {sig: tsig var_t} *)
    (*            (Gamma: tcontext sig) *)
    (*            (sched_log: Log) *)
    (*            (action_log: Log) *)
    (*            {argspec: tsig var_t} *)
    (*            (args: acontext sig argspec) *)
    (*     : option (Log * tcontext argspec * (tcontext sig)) := *)
    (*     match args with *)
    (*     | CtxEmpty => Some (action_log, CtxEmpty, Gamma) *)
    (*     | @CtxCons _ _ argspec k_tau arg args => *)
    (*       let/opt3 action_log, ctx, Gamma := interp_args' Gamma sched_log action_log args in *)
    (*       let/opt3 action_log, v, Gamma := interp_action _ _ Gamma sched_log action_log arg in *)
    (*       Some (action_log, CtxCons k_tau v ctx, Gamma) *)
    (*     end. *)
    (* End Args. *)

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
             | (nm, tau) :: fields => fun '(x, xs) =>
                 (val_of_value x) :: (val_of_struct_value xs)
             end x) in
      match tau return type_denote tau -> val with
      | bits_t _ => fun bs => Bits _ bs
      | enum_t _ => fun bs => Enum _ bs
      | struct_t sig => fun str => Struct sig (val_of_struct_value str)
      | array_t sig => fun v => Array sig (map val_of_value (vect_to_list v))
      end x.

    Definition val_bits_app (v1 v2: val) : val :=
      match v1, v2 with
      | Bits _ b1, Bits _ b2 => Bits _ (Bits.app b1 b2)
      | _, _ => Bits _ Ob
      end.

    Definition val_concat (l: list val) : val :=
      fold_left (val_bits_app) l (Bits _ Ob).

    Fixpoint ubits_of_value (v: val) : val :=
      match v with
      | Bits _ bs => Bits _ bs
      | Enum _ bs => Bits _ bs
      | Struct _ lv => val_concat (map ubits_of_value lv)
      | Array _ lv => val_concat (map ubits_of_value lv)
      end.

    Lemma ubits_of_value_ok:
      forall {tau} (v: type_denote tau) bs,
        ubits_of_value (val_of_value v) = Bits _ bs ->
        bits_of_value v = bs.
    Proof.
      induction tau; simpl; intros.
      - inversion H.
        apply Eqdep_dec.inj_pair2_eq_dec in H1. 2: apply eq_dec. auto.
      - inversion H.
        apply Eqdep_dec.inj_pair2_eq_dec in H1. 2: apply eq_dec. auto.
      (*
      - induction struct_fields.
        + cbn in H. injection H.
      *) Admitted.

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

    Definition val_split (n: nat) (v: val) : option (val * val) :=
      match v with
      | Bits sz bs =>
        let/opt2 b0, b1 := bits_split n bs in
        Some (Bits _ b0, Bits _ b1)
      | _ => None
      end.

    Fixpoint bits_splitn {sz} (nb sz_elt: nat) (bs: bits sz)
      : option (list (bits sz_elt))
    :=
      match nb with
        O => Some []
      | S nb =>
        let/opt2 hd, rest := bits_split sz_elt bs in
        let/opt tl := bits_splitn nb sz_elt rest in
        Some (hd :: tl)
      end.

    Definition bits_of_bits (n1: nat) {n} (bs: bits n) : option (bits n1).
      destruct (eq_dec n n1). subst.
      exact (Some bs).
      exact None.
    Defined.

    Definition enum_of_bits (sig: enum_sig) {n} (bs: bits n)
      : option (bits (enum_bitsize sig))
    :=
      bits_of_bits (enum_bitsize sig) bs.

    Fixpoint value_of_bits {tau: type} (bs: val) {struct tau}: option val :=
      let value_of_struct_bits :=
        (fix value_of_struct_bits
             {fields: list (string * type)}
             (bs: val)
         : option (list val) :=
           match fields with
           | [] => Some []
           | (nm, tau) :: fields =>
             let/opt2 b0, b1 := val_split (type_sz tau) bs in
             let/opt hd := value_of_bits (tau:=tau) b0 in
             let/opt tl := value_of_struct_bits (fields:=fields) b1 in
             Some (hd :: tl)
           end) in
      let value_of_list_bits tau :=
        fix value_of_list_bits {sz} (l : list (bits sz))
          : option (list val)
        :=
          match l with
          | [] => Some []
          | hd::tl =>
            let/opt hd := value_of_bits (tau:=tau) (Bits _ hd) in
            let/opt tl := value_of_list_bits tl in
            Some (hd::tl)
          end in
      match bs with
        Bits _ bs' =>
        match tau with
        | bits_t _ => Some bs
        | enum_t sig => option_map (fun bs => Bits _ bs) (enum_of_bits sig bs')
        | struct_t sig => option_map (fun lv => Struct sig lv)
            (value_of_struct_bits (fields:=struct_fields sig) bs)
        | array_t sig =>
          let/opt lbs := bits_splitn (array_len sig)
            (type_sz (array_type sig)) bs' in
          let/opt lv := value_of_list_bits (array_type sig) lbs in
          Some (Array sig lv)
        end
      | _ => None
      end.


      Locate CircuitPrimSpecs.sigma1.
  Definition sigma1 (fn: PrimUntyped.ufn1) : val -> option val :=
    match fn with
    | PrimUntyped.UDisplay fn =>
      match fn with
      | PrimUntyped.UDisplayUtf8 => fun _ => Some (Bits _ Ob)
      | PrimUntyped.UDisplayValue _ => fun _ => Some (Bits _ Ob)
      end
    | PrimUntyped.UConv fn =>
      match fn with
      | PrimUntyped.UPack => fun v => Some (ubits_of_value v)
      | PrimUntyped.UUnpack tau => fun bs => value_of_bits (tau:=tau) bs
      | PrimUntyped.UIgnore => fun _ => Some (Bits _ Ob)
      end
    | PrimUntyped.UBits1 fn => CircuitPrimSpecs.sigma1 fn
    | PrimUntyped.UStruct1 (PrimUntyped.UGetField f) =>
      BitFuns.get_field

    | PrimUntyped.UArray1 (PrimUntyped.UGetElement idx) => fun a => vect_nth a idx
    end.

  (* Definition sigma2 (fn: fn2) : Sig_denote (PrimSignatures.Sigma2 fn) := *)
  (*   match fn with *)
  (*   | Eq tau false  => _eq *)
  (*   | Eq tau true  => _neq *)
  (*   | Bits2 fn => CircuitPrimSpecs.sigma2 fn *)
  (*   | Struct2 SubstField sig idx => fun s v => subst_field sig.(struct_fields) s idx v *)
  (*   | Array2 SubstElement sig idx => fun a e => vect_replace a idx e *)
  (*   end. *)


    Fixpoint interp_action
             {sig: tsig var_t}
             (Gamma: tcontext sig)
             (sched_log: Log)
             (action_log: Log)
             (a: uaction)
             {struct a}
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
        let/opt3 action_log, v, Gamma := interp_action Gamma sched_log action_log a in
        Some (action_log, Bits _ Ob, replace k v Gamma)
      | USeq a1 a2 =>
        let/opt3 action_log, v, Gamma := interp_action Gamma sched_log action_log a1 in
        interp_action Gamma sched_log action_log a2
      | UBind k a1 a2 =>
        let/opt3 action_log, v, Gamma
          := interp_action Gamma sched_log action_log a1 in
        let/opt3 action_log, v, Gamma := interp_action
          (CtxCons (k, bits_t 0) v Gamma) sched_log action_log a2
        in Some (action_log, v, ctl Gamma)
      | UIf cond athen aelse =>
        let/opt3 action_log, v, Gamma := interp_action Gamma sched_log action_log cond in
        match v with
        | Bits 1 b =>
          if Bits.single b then
            interp_action Gamma sched_log action_log athen
          else
            interp_action Gamma sched_log action_log aelse
        | _ => None
        end
      | URead prt idx =>
        if may_read sched_log prt idx then
          Some (log_cons idx (LE LogRead prt (Bits 0 (vect_nil))) action_log,
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
          Some (log_cons idx (LE LogWrite prt val) action_log, Bits _ Bits.nil, Gamma)
        else None
      | UUnop fn arg =>
        let/opt3 action_log, arg1, Gamma := interp_action Gamma sched_log action_log arg in
        Some (action_log, (PrimSpecs.sigma1 fn) arg1, Gamma)
      | _ => None
      end.

      | Unop fn arg1 => fun Gamma =>
        let/opt3 action_log, arg1, Gamma := interp_action Gamma sched_log action_log arg1 in
        Some (action_log, (PrimSpecs.sigma1 fn) arg1, Gamma)
      | Binop fn arg1 arg2 => fun Gamma =>
        let/opt3 action_log, arg1, Gamma := interp_action Gamma sched_log action_log arg1 in
        let/opt3 action_log, arg2, Gamma := interp_action Gamma sched_log action_log arg2 in
        Some (action_log, (PrimSpecs.sigma2 fn) arg1 arg2, Gamma)
      | ExternalCall fn arg1 => fun Gamma =>
        let/opt3 action_log, arg1, Gamma := interp_action Gamma sched_log action_log arg1 in
        Some (action_log, sigma fn arg1, Gamma)
      | InternalCall name args body => fun Gamma =>
        let/opt3 action_log, results, Gamma := interp_args' (@interp_action) Gamma sched_log action_log args in
        let/opt3 action_log, v, _ := interp_action results sched_log action_log body in
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
