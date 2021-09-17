(*! Language | Semantics of typed Kôika programs !*)
Require Export Koika.Common Koika.Environments Koika.Logs Koika.Syntax Koika.TypedSyntax.
Require Import Koika.TypedSemantics.

Require Import Coq.Program.Equality.


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

Lemma existT_inj:
  forall {A:Type}
         (Aeq: forall x y : A, {x = y} + {x <> y})
         (P: A -> Type) t v1 v2,
    existT P t v1 = existT P t v2 -> v1 = v2.
Proof.
  intros.
  eapply Eqdep_dec.inj_pair2_eq_dec; eauto.
Qed.



Section Interp.
  Context {pos_t var_t fn_name_t rule_name_t reg_t ext_fn_t: Type}.
  Context {reg_t_eq_dec: EqDec reg_t}.
  Context {var_t_eq_dec: EqDec var_t}.

  Context {R: reg_t -> type}.
  Context {Sigma: ext_fn_t -> ExternalSignature}.

  Fixpoint size_action
           {t : tsig var_t} {t0 : type}
           (a : TypedSyntax.action pos_t var_t fn_name_t R Sigma t t0) :=
    match a with
    | @Fail _ _ _ _ _ _ _ sig tau => 0
    | @Var _ _ _ _ _ _ _ sig k tau m => 0
    | @Const _ _ _ _ _ _ _ sig tau cst => 0
    | @Assign _ _ _ _ _ _ _ sig k tau m a1 => 1 + size_action a1
    | @Seq _ _ _ _ _ _ _ sig tau a1 a2 => 1 + size_action a1 + size_action a2
    | @Bind _ _ _ _ _ _ _ sig tau tau' var a1 a2 => 1 + size_action a1 + size_action a2
    | @If _ _ _ _ _ _ _ sig tau a1 a2 a3 => 1 + size_action a1 + size_action a2 + size_action a3
    | @Read _ _ _ _ _ _ _ sig port idx => 0
    | @Write _ _ _ _ _ _ _ sig port idx a1 => 1 + size_action a1
    | @Unop _ _ _ _ _ _ _ sig fn a1 => 1 + size_action a1
    | @Binop _ _ _ _ _ _ _ sig fn a1 a2 => 1 + size_action a1 + size_action a2
    | @ExternalCall _ _ _ _ _ _ _ sig fn a1 => 1 + size_action a1
    | @InternalCall _ _ _ _ _ _ _ sig tau fn argspec args a1 =>
      1 + size_action a1 + cfoldl (fun k v acc => acc + size_action v) args 0
    | @APos _ _ _ _ _ _ _ sig tau pos a1 => 1 + size_action a1
    end.

  Context {REnv: Env reg_t}.

  Notation Log := (Log R REnv).


  Notation rule := (rule pos_t var_t fn_name_t R Sigma).
  Notation action := (action pos_t var_t fn_name_t R Sigma).
  Notation scheduler := (scheduler pos_t rule_name_t).

  Lemma cfoldl_size_increases:
    forall (l: tsig var_t) sig (lv: context (fun k_tau => action sig (snd k_tau)) l)
           x0,
      x0 <= cfoldl (fun k (v: action sig (snd k)) acc => acc + size_action v) lv x0.
  Proof.
    induction lv; simpl; intros. lia.
    eapply le_trans. 2: eauto. lia.
  Qed.

  Lemma cfoldl_size_contains:
    forall (l: tsig var_t) sig (lv: context (fun k_tau => action sig (snd k_tau)) l)
           k (m: member k l) x0,
      size_action (cassoc m lv) <= cfoldl (fun k (v: action sig (snd k)) acc => acc + size_action v) lv x0.
  Proof.
    induction lv; simpl; intros. inv m.
    dependent destruction m.
    simpl.
    eapply le_trans. 2: apply cfoldl_size_increases. lia. simpl.
    eapply le_trans. apply IHlv. reflexivity.
  Qed.

  Lemma action_ind_args: forall
      (P : forall (t : tsig var_t) (t0 : type),
          TypedSyntax.action pos_t var_t fn_name_t R Sigma t t0 -> Prop)
      (Pfail: forall (sig : tsig var_t) (tau : type), P sig tau (Fail tau))
      (Pvar: forall (sig : list (var_t * type)) (k : var_t) (tau : type) (m : member (k, tau) sig),
          P sig tau (Var m))
      (Pcst: forall (sig : tsig var_t) (tau : type) (cst : tau), P sig tau (Const cst))
      (Passign: forall (sig : list (var_t * type)) (k : var_t) (tau : type) (m : member (k, tau) sig)
                       (ex : TypedSyntax.action pos_t var_t fn_name_t R Sigma sig tau),
          P sig tau ex -> P sig unit_t (Assign m ex))
      (Pseq: forall (sig : tsig var_t) (tau : type)
                    (r1 : TypedSyntax.action pos_t var_t fn_name_t R Sigma sig unit_t),
          P sig unit_t r1 ->
          forall r2 : TypedSyntax.action pos_t var_t fn_name_t R Sigma sig tau,
            P sig tau r2 -> P sig tau (Seq r1 r2))
      (Pbind: forall (sig : tsig var_t) (tau tau' : type) (var : var_t)
                     (ex : TypedSyntax.action pos_t var_t fn_name_t R Sigma sig tau),
          P sig tau ex ->
          forall body : TypedSyntax.action pos_t var_t fn_name_t R Sigma ((var, tau) :: sig) tau',
            P ((var, tau) :: sig) tau' body -> P sig tau' (Bind var ex body))
      (Pif: forall (sig : tsig var_t) (tau : type)
                   (cond : TypedSyntax.action pos_t var_t fn_name_t R Sigma sig (bits_t 1)),
          P sig (bits_t 1) cond ->
          forall tbranch : TypedSyntax.action pos_t var_t fn_name_t R Sigma sig tau,
            P sig tau tbranch ->
            forall fbranch : TypedSyntax.action pos_t var_t fn_name_t R Sigma sig tau,
              P sig tau fbranch -> P sig tau (If cond tbranch fbranch))
      (Pread: forall (sig : tsig var_t) (port : Port) (idx : reg_t), P sig (R idx) (Read port idx))
      (Pwrite: forall (sig : tsig var_t) (port : Port) (idx : reg_t)
                      (value : TypedSyntax.action pos_t var_t fn_name_t R Sigma sig (R idx)),
          P sig (R idx) value -> P sig unit_t (Write port idx value))
      (Punop: forall (sig : tsig var_t) (fn : PrimTyped.fn1)
                     (arg1 : TypedSyntax.action pos_t var_t fn_name_t R Sigma sig
                                                (arg1Sig (PrimSignatures.Sigma1 fn))),
          P sig (arg1Sig (PrimSignatures.Sigma1 fn)) arg1 ->
          P sig (retSig (PrimSignatures.Sigma1 fn)) (Unop fn arg1))
      (Pbinop: forall (sig : tsig var_t) (fn : PrimTyped.fn2)
                      (arg1 : TypedSyntax.action pos_t var_t fn_name_t R Sigma sig
                                                 (arg1Sig (PrimSignatures.Sigma2 fn))),
          P sig (arg1Sig (PrimSignatures.Sigma2 fn)) arg1 ->
          forall
            arg2 : TypedSyntax.action pos_t var_t fn_name_t R Sigma sig
                                      (arg2Sig (PrimSignatures.Sigma2 fn)),
            P sig (arg2Sig (PrimSignatures.Sigma2 fn)) arg2 ->
            P sig (retSig (PrimSignatures.Sigma2 fn)) (Binop fn arg1 arg2))
      (Pextcall: forall (sig : tsig var_t) (fn : ext_fn_t)
                        (arg : TypedSyntax.action pos_t var_t fn_name_t R Sigma sig (arg1Sig (Sigma fn))),
          P sig (arg1Sig (Sigma fn)) arg -> P sig (retSig (Sigma fn)) (ExternalCall fn arg))
      (Pintcall: forall (sig : tsig var_t) (tau : type) (fn : fn_name_t) (argspec : tsig var_t)
                        (args : context
                                  (fun k_tau : var_t * type =>
                                     TypedSyntax.action pos_t var_t fn_name_t R Sigma sig (snd k_tau))
                                  (rev argspec))
                        (body : TypedSyntax.action pos_t var_t fn_name_t R Sigma (rev argspec) tau)
                        (Pargs: forall k (m: member k (rev argspec)),
                            P sig (snd k) (cassoc m args)
                        ),
          P (rev argspec) tau body -> P sig tau (InternalCall fn args body))
      (Papos: forall (sig : tsig var_t) (tau : type) (pos : pos_t)
                     (a : TypedSyntax.action pos_t var_t fn_name_t R Sigma sig tau),
          P sig tau a -> P sig tau (APos pos a))
      (t : tsig var_t) (t0 : type) (a : TypedSyntax.action pos_t var_t fn_name_t R Sigma t t0),
      P t t0 a.
  Proof.
    intros.
    remember (size_action a).
    revert n t t0 a Heqn.
    intro n. pattern n.
    eapply Nat.strong_right_induction with (z:=0).
    {
      red. red. intros. subst. tauto.
    } 2: lia.
    intros n0 _ Plt t t0 a Heqn.
    assert (Plt':
              forall t t0 a,
                size_action a < n0 -> P t t0 a
           ).
    {
      intros. eapply Plt. 3: reflexivity. lia. auto.
    } clear Plt.
    rename Plt' into Plt.
    destruct a; simpl in Heqn; eauto.
    - eapply Passign. eapply Plt; lia.
    - eapply Pseq; eapply Plt; lia.
    - eapply Pbind; eapply Plt; lia.
    - eapply Pif; eapply Plt; lia.
    - eapply Pwrite; eapply Plt; lia.
    - eapply Punop; eapply Plt; lia.
    - eapply Pbinop; eapply Plt; lia.
    - eapply Pextcall; eapply Plt; lia.
    - eapply Pintcall.
      intros; eapply Plt. inv Heqn.
      specialize (cfoldl_size_contains (rev argspec) sig args _ m 0). lia.
      eapply Plt; lia.
    - eapply Papos; eapply Plt; lia.
  Qed.


  Lemma existT_tcontext:
    forall sig Gamma Gamma0,
      existT (fun x : tsig var_t => tcontext x) sig Gamma0 =
      existT (fun x : tsig var_t => tcontext x) sig Gamma ->
      Gamma0 = Gamma.
  Proof.
    intros.
    apply existT_inj in H. auto.
    decide equality. decide equality; apply eq_dec.
  Qed.

  Lemma existT_action:
    forall sig tau a1 a2,
      existT (fun x : tsig var_t => {x0 : type & action x x0}) sig
             (existT (fun x : type => action sig x) tau a1) =
      existT (fun x : tsig var_t => {x0 : type & action x x0}) sig
             (existT (fun x : type => action sig x) tau a2) ->
      a1 = a2.
  Proof.
    intros.
    apply existT_inj in H.
    apply existT_inj in H.
    auto. apply eq_dec.
    decide equality. decide equality; apply eq_dec.
  Qed.

  Lemma existT_action':
    forall tau v1 v2,
      existT (fun x : type => x) tau v1 = existT (fun x : type => x) tau v2 ->
      v1 = v2.
  Proof.
    intros.
    apply existT_inj in H. auto.
    apply eq_dec.
  Qed.

  Ltac existT_tac :=
    repeat match goal with
           | H: existT _ _ _ = existT _ _ _ |- _ =>
             apply existT_tcontext in H
           | H: existT _ _ _ = existT _ _ _ |- _ =>
             apply existT_action in H
           | H: existT _ _ _ = existT _ _ _ |- _ =>
             apply existT_action' in H
           end.

  Section Action.
    Context (r: REnv.(env_t) R).
    Context (sigma: forall f, Sig_denote (Sigma f)).

    Section Args'.
      Context (ind_interp_action:
                 forall
                   (sched_log: Log)
                   {sig: tsig var_t} {tau}
                   (Gamma: tcontext sig)
                   (action_log: Log)
                   (a: action sig tau)
                   (final_log: Log)
                   (final_val: type_denote tau)
                   (final_gamma: tcontext sig), Prop).

      Inductive ind_interp_args'
                {sig: tsig var_t}
                (sched_log: Log):
        forall {argspec}, tcontext sig -> Log -> acontext sig argspec ->
                          Log -> tcontext argspec -> tcontext sig -> Prop :=
      | ind_interp_args'_nil:
          forall Gamma action_log,
            ind_interp_args' sched_log Gamma action_log CtxEmpty action_log CtxEmpty Gamma
      | ind_interp_args'_cons:
          forall Gamma action_log argspec k_tau arg args v Gamma' Gamma'' ctx action_log' action_log'',
            ind_interp_args' sched_log Gamma action_log args action_log' ctx Gamma' ->
            ind_interp_action sched_log _ _ Gamma' action_log' arg action_log'' v Gamma'' ->
            ind_interp_args' sched_log Gamma action_log (@CtxCons _ _ argspec k_tau arg args)
                             action_log'' (CtxCons k_tau v ctx) Gamma''
      .
    End Args'.



    Section ArgsEq.
      Context (interp_action:
                 forall {sig: tsig var_t} {tau}
                        (Gamma: tcontext sig)
                        (sched_log: Log) (action_log: Log)
                        (a: action sig tau),
                   option (Log * type_denote tau * (tcontext sig))).
      Context (ind_interp_action:
                 forall
                   (sched_log: Log)
                   {sig: tsig var_t} {tau}
                   (Gamma: tcontext sig)
                   (action_log: Log)
                   (a: action sig tau)
                   (final_log: Log)
                   (final_val: type_denote tau)
                   (final_gamma: tcontext sig), Prop).

      Lemma interp_args'_impl:
        forall
          {sig: tsig var_t}
          (sched_log: Log)
          (Gamma: tcontext sig)
          (action_log: Log)
          argspec (args: acontext sig argspec)
          (final_log: Log)
          (final_gamma: tcontext sig) ctx
          (interp_action_impl:
             forall (sched_log: Log)
                    (Gamma: tcontext sig)
                    (action_log: Log)
                    (final_log: Log)
                    k
                    final_val
                    final_gamma
                    (m: member k argspec),
               interp_action _ _ Gamma sched_log action_log (cassoc m args) = Some (final_log, final_val, final_gamma) ->
               ind_interp_action sched_log _ _ Gamma action_log (cassoc m args) final_log final_val final_gamma
          )
        ,
          interp_args' interp_action Gamma sched_log action_log args = Some (final_log, ctx, final_gamma) ->
          ind_interp_args' ind_interp_action sched_log Gamma action_log args final_log ctx final_gamma.
      Proof.
        intros.
        revert sched_log argspec args Gamma action_log final_log final_gamma ctx H interp_action_impl.
        induction args; simpl; intros; eauto.
        - inv H. constructor.
        - unfold opt_bind in H. repeat destr_in H; inv H.
          apply (interp_action_impl _ _ _ final_log k _ _ (MemberHd _ _)) in Heqo0.
          apply IHargs in Heqo.
          econstructor; eauto.
          intros.
          eapply (interp_action_impl _ _ _ _ _ _ _ (MemberTl _ _ _ _)); eauto.
      Qed.

      Lemma ind_interp_args'_impl:
        forall
          {sig: tsig var_t}
          (sched_log: Log)
          (Gamma: tcontext sig)
          (action_log: Log)
          argspec (args: acontext sig argspec)
          (final_log: Log)
          (final_gamma: tcontext sig) ctx
          (ind_interp_action_impl':
             forall (sched_log: Log)
                    (Gamma: tcontext sig)
                    (action_log: Log)
                    (final_log: Log)
                    k
                    final_val
                    final_gamma
                    (m: member k argspec),
               ind_interp_action sched_log _ _ Gamma action_log (cassoc m args) final_log final_val final_gamma ->
               interp_action _ _ Gamma sched_log action_log (cassoc m args) = Some (final_log, final_val, final_gamma)
          )
        ,
          ind_interp_args' ind_interp_action sched_log Gamma action_log args final_log ctx final_gamma ->
          interp_args' interp_action Gamma sched_log action_log args = Some (final_log, ctx, final_gamma).
      Proof.
        intros.
        revert sched_log argspec args Gamma action_log final_log final_gamma ctx H ind_interp_action_impl'.
        induction args; simpl; intros; eauto.
        - inv H.
          apply existT_inj in H0. inv H0. auto.
          decide equality. decide equality; apply eq_dec.
        - unfold opt_bind. inv H.
          apply existT_inj in H2; eauto.
          apply existT_inj in H6; eauto.
          apply existT_inj in H8; eauto. subst.
          apply (ind_interp_action_impl' _ _ _ _ _ _ _ (MemberHd _ _)) in H10.
          apply IHargs in H9. rewrite H9. simpl in H10. rewrite H10. auto.
          intros.
          eapply (ind_interp_action_impl' _ _ _ _ _ _ _ (MemberTl _ _ _ _)); eauto.
          decide equality. decide equality. apply eq_dec. apply eq_dec.
          decide equality. decide equality. apply eq_dec. apply eq_dec.
          decide equality. apply eq_dec. apply eq_dec.
      Qed.

    End ArgsEq.

    Inductive ind_interp_action
              (sched_log: Log):
      forall {sig: tsig var_t},
      forall {tau},
        tcontext sig ->
        Log ->
        action sig tau ->
        Log ->
        tau ->
        tcontext sig -> Prop :=
    | ind_interp_action_var:
        forall sig tau Gamma action_log k (m: member (k, tau) sig),
          ind_interp_action sched_log Gamma action_log (Var m) action_log (cassoc m Gamma) Gamma
    | ind_interp_action_cst:
        forall sig tau Gamma action_log cst,
          ind_interp_action (sig:=sig) sched_log Gamma action_log (Const (tau:=tau) cst) action_log cst Gamma
    | ind_interp_action_seq:
        forall sig tau2 Gamma action_log a1 a2 action_log' action_log'' Gamma' Gamma'' v1 v2,
          ind_interp_action (sig:=sig) (tau:=unit_t) sched_log Gamma action_log a1 action_log' v1 Gamma' ->
          ind_interp_action (sig:=sig) (tau:=tau2) sched_log Gamma' action_log' a2 action_log'' v2 Gamma'' ->
          ind_interp_action (sig:=sig) (tau:=tau2) sched_log Gamma action_log (Seq a1 a2) action_log'' v2 Gamma''
    | ind_interp_action_assign:
        forall sig Gamma action_log k tau m a action_log' Gamma' v,
          ind_interp_action (sig:=sig) (tau:=tau) sched_log Gamma action_log a action_log' v Gamma' ->
          ind_interp_action (sig:=sig) sched_log Gamma action_log (@Assign _ _ _ _ _ _ _ _ k tau m a) action_log' Ob (creplace m v Gamma')
    | ind_interp_action_bind:
        forall sig tau1 tau2 var Gamma action_log a1 a2 action_log' action_log'' v1 v2 Gamma' Gamma'',
          ind_interp_action (sig:=sig) (tau:=tau1) sched_log Gamma action_log a1 action_log' v1 Gamma' ->
          ind_interp_action (sig:=(var,tau1)::sig) (tau:=tau2) sched_log (CtxCons (var, tau1) v1 Gamma') action_log' a2 action_log'' v2 Gamma'' ->
          ind_interp_action (sig:=sig)(tau:=tau2) sched_log Gamma action_log (@Bind _ _ _ _ _ _ _ sig tau1 tau2 var a1 a2) action_log'' v2 (ctl Gamma'')
    | ind_interp_action_if_true:
        forall sig tau2 Gamma action_log cond action_log' action_log'' v1 v2 Gamma' Gamma'' tbranch fbranch,
          ind_interp_action (sig:=sig) (tau:=bits_t 1) sched_log Gamma action_log cond action_log' v1 Gamma' ->
          Bits.single v1 = true ->
          ind_interp_action (sig:=sig) (tau:=tau2) sched_log Gamma' action_log' tbranch action_log'' v2 Gamma'' ->
          ind_interp_action (sig:=sig)(tau:=tau2) sched_log Gamma action_log (If cond tbranch fbranch) action_log'' v2 Gamma''
    | ind_interp_action_if_false:
        forall sig tau2 Gamma action_log cond action_log' action_log'' v1 v2 Gamma' Gamma'' tbranch fbranch,
          ind_interp_action (sig:=sig) (tau:=bits_t 1) sched_log Gamma action_log cond action_log' v1 Gamma' ->
          Bits.single v1 = false ->
          ind_interp_action (sig:=sig) (tau:=tau2) sched_log Gamma' action_log' fbranch action_log'' v2 Gamma'' ->
          ind_interp_action (sig:=sig)(tau:=tau2) sched_log Gamma action_log (If cond tbranch fbranch) action_log'' v2 Gamma''
    | ind_interp_action_read_p0:
        forall sig Gamma action_log prt idx,
          may_read sched_log prt idx = true ->
          prt = P0 ->
          ind_interp_action (sig:=sig) sched_log Gamma action_log
                            (Read prt idx)
                            (log_cons idx (LE LogRead prt tt) action_log) (REnv.(getenv) r idx) Gamma
    | ind_interp_action_read_p1_with_read:
        forall sig Gamma action_log prt idx v,
          may_read sched_log prt idx = true ->
          prt = P1 ->
          latest_write0 (log_app action_log sched_log) idx = Some v ->
          ind_interp_action (sig:=sig) sched_log Gamma action_log
                            (Read prt idx)
                            (log_cons idx (LE LogRead prt tt) action_log) v Gamma
    | ind_interp_action_read_p1_without_read:
        forall sig Gamma action_log prt idx,
          may_read sched_log prt idx = true ->
          prt = P1 ->
          latest_write0 (log_app action_log sched_log) idx = None ->
          ind_interp_action (sig:=sig) sched_log Gamma action_log
                            (Read prt idx)
                            (log_cons idx (LE LogRead prt tt) action_log) (REnv.(getenv) r idx) Gamma
    | ind_interp_action_write:
        forall idx sig Gamma action_log a action_log' Gamma' v prt,
          ind_interp_action (sig:=sig) sched_log Gamma action_log a action_log' v Gamma' ->
          may_write sched_log action_log' prt idx = true ->
          ind_interp_action (sig:=sig) sched_log Gamma action_log
                            (Write prt idx a)
                            (log_cons idx (LE LogWrite prt v) action_log') Bits.nil Gamma'

    | ind_interp_action_unop:
        forall sig Gamma action_log fn a action_log' Gamma' v,
          ind_interp_action (sig:=sig) sched_log Gamma action_log a action_log' v Gamma' ->
          ind_interp_action (sig:=sig) sched_log Gamma action_log
                            (Unop fn a)
                            action_log' (PrimSpecs.sigma1 fn v) Gamma'
    | ind_interp_action_binop:
        forall sig Gamma action_log fn a1 a2 action_log' Gamma' action_log'' Gamma'' v1 v2,
          ind_interp_action (sig:=sig) sched_log Gamma action_log a1 action_log' v1 Gamma' ->
          ind_interp_action (sig:=sig) sched_log Gamma' action_log' a2 action_log'' v2 Gamma'' ->
          ind_interp_action (sig:=sig) sched_log Gamma action_log
                            (Binop fn a1 a2)
                            action_log'' (PrimSpecs.sigma2 fn v1 v2) Gamma''

    | ind_interp_action_extcall:
        forall sig Gamma action_log fn a action_log' Gamma' v,
          ind_interp_action (sig:=sig) sched_log Gamma action_log a action_log' v Gamma' ->
          ind_interp_action (sig:=sig) sched_log Gamma action_log
                            (ExternalCall fn a)
                            action_log' (sigma fn v) Gamma'


    | ind_interp_action_intcall:
        forall sig0 tau0 argspec Gamma action_log action_log' name args v a Gamma' action_log'' Gamma'' ctx,
          ind_interp_args' (argspec:=rev argspec) (@ind_interp_action) sched_log Gamma action_log args
                           action_log' ctx Gamma' ->
          ind_interp_action sched_log ctx action_log' a action_log'' v Gamma'' ->
          ind_interp_action  sched_log Gamma action_log
                             (@InternalCall _ _ _ _ _ _ _ sig0 tau0 name argspec args a)
                             action_log'' v Gamma'

    | ind_interp_action_apos:
        forall sig tau Gamma action_log p a action_log' Gamma' v,
          ind_interp_action (sig:=sig) (tau:=tau) sched_log Gamma action_log a action_log' v Gamma' ->
          ind_interp_action (sig:=sig) (tau:=tau) sched_log Gamma action_log
                            (APos p a)
                            action_log' v Gamma'
    .

    Lemma interp_action_impl:
      forall sched_log sig tau a Gamma action_log action_log' Gamma' v
             (IA: interp_action r sigma Gamma sched_log action_log a = Some (action_log', v, Gamma')),
        @ind_interp_action sched_log sig tau Gamma action_log a action_log' v Gamma'.
    Proof.
      intros sched_log sig tau a. revert sched_log.
      pattern sig, tau, a.
      eapply action_ind_args; simpl; intros; unfold opt_bind in IA; repeat destr_in IA; inv IA.
      - econstructor; eauto.
      - econstructor; eauto.
      - econstructor. eauto.
      - econstructor; eauto.
      - econstructor; eauto.
      - eapply ind_interp_action_if_true; eauto.
      - eapply ind_interp_action_if_false; eauto.
      - eapply ind_interp_action_read_p0; eauto.
      - eapply ind_interp_action_read_p1_with_read; eauto.
      - eapply ind_interp_action_read_p1_without_read; eauto.
      - econstructor; eauto.
      - econstructor; eauto.
      - econstructor; eauto.
      - econstructor; eauto.
      - econstructor; eauto.
        eapply interp_args'_impl in Heqo. eauto.
        intros; eapply Pargs; eauto.
      - econstructor; eauto.
    Qed.

    Lemma ind_inter_action_ind_args:
      forall
        (P : forall (sched_log: Log)(sig : tsig var_t) (tau : type),
            tcontext sig -> Log -> action sig tau -> Log -> tau -> tcontext sig -> Prop)
        (Pvar : forall (sched_log : Log) (sig : list (var_t * type)) (tau : type) (Gamma : tcontext sig)
                       (action_log : Log) (k : var_t) (m : member (k, tau) sig),
            P sched_log sig tau Gamma action_log (Var m) action_log (cassoc m Gamma) Gamma)
        (Pcst : forall (sched_log : Log) (sig : tsig var_t) (tau : type) (Gamma : tcontext sig) (action_log : Log) (cst : tau),
            P sched_log sig tau Gamma action_log (Const cst) action_log cst Gamma)
        (Pseq : forall (sched_log : Log) (sig : tsig var_t) (tau2 : type) (Gamma : tcontext sig) (action_log : Log)
                       (a1 : action sig unit_t) (a2 : action sig tau2) (action_log' action_log'' : Log)
                       (Gamma' Gamma'' : tcontext sig) (v1 : unit_t) (v2 : tau2),
            ind_interp_action sched_log Gamma action_log a1 action_log' v1 Gamma' ->
            P sched_log sig unit_t Gamma action_log a1 action_log' v1 Gamma' ->
            ind_interp_action sched_log Gamma' action_log' a2 action_log'' v2 Gamma'' ->
            P sched_log sig tau2 Gamma' action_log' a2 action_log'' v2 Gamma'' ->
            P sched_log sig tau2 Gamma action_log (Seq a1 a2) action_log'' v2 Gamma'')
        (Passign : forall (sched_log : Log) (sig : tsig var_t) (Gamma : tcontext sig) (action_log : Log)
                          (k : var_t) (tau : type) (m : member (k, tau) sig) (a : action sig tau)
                          (action_log' : Log) (Gamma' : tcontext sig) (v : tau),
            ind_interp_action sched_log Gamma action_log a action_log' v Gamma' ->
            P sched_log sig tau Gamma action_log a action_log' v Gamma' ->
            P sched_log sig unit_t Gamma action_log (Assign m a) action_log' Ob (creplace m v Gamma'))
        (Pbind : forall (sched_log : Log) (sig : tsig var_t) (tau1 tau2 : type) (var : var_t) (Gamma : tcontext sig)
                        (action_log : Log) (a1 : action sig tau1) (a2 : action ((var, tau1) :: sig) tau2)
                        (action_log' action_log'' : Log) (v1 : tau1) (v2 : tau2) (Gamma' : tcontext sig)
                        (Gamma'' : tcontext ((var, tau1) :: sig)),
            ind_interp_action sched_log Gamma action_log a1 action_log' v1 Gamma' ->
            P sched_log sig tau1 Gamma action_log a1 action_log' v1 Gamma' ->
            ind_interp_action sched_log (CtxCons (var, tau1) v1 Gamma') action_log' a2 action_log'' v2
                              Gamma'' ->
            P sched_log ((var, tau1) :: sig) tau2 (CtxCons (var, tau1) v1 Gamma') action_log' a2 action_log'' v2
              Gamma'' -> P sched_log sig tau2 Gamma action_log (Bind var a1 a2) action_log'' v2 (ctl Gamma''))
        (Piftrue: forall (sched_log : Log) (sig : tsig var_t) (tau2 : type) (Gamma : tcontext sig) (action_log : Log)
                         (cond : action sig (bits_t 1)) (action_log' action_log'' : Log)
                         (v1 : bits_t 1) (v2 : tau2) (Gamma' Gamma'' : tcontext sig)
                         (tbranch fbranch : action sig tau2),
            ind_interp_action sched_log Gamma action_log cond action_log' v1 Gamma' ->
            P sched_log sig (bits_t 1) Gamma action_log cond action_log' v1 Gamma' ->
            Bits.single v1 = true ->
            ind_interp_action sched_log Gamma' action_log' tbranch action_log'' v2 Gamma'' ->
            P sched_log sig tau2 Gamma' action_log' tbranch action_log'' v2 Gamma'' ->
            P sched_log sig tau2 Gamma action_log (If cond tbranch fbranch) action_log'' v2 Gamma'')
        (Piffalse : forall (sched_log : Log) (sig : tsig var_t) (tau2 : type) (Gamma : tcontext sig) (action_log : Log)
                           (cond : action sig (bits_t 1)) (action_log' action_log'' : Log)
                           (v1 : bits_t 1) (v2 : tau2) (Gamma' Gamma'' : tcontext sig)
                           (tbranch fbranch : action sig tau2),
            ind_interp_action sched_log Gamma action_log cond action_log' v1 Gamma' ->
            P sched_log sig (bits_t 1) Gamma action_log cond action_log' v1 Gamma' ->
            Bits.single v1 = false ->
            ind_interp_action sched_log Gamma' action_log' fbranch action_log'' v2 Gamma'' ->
            P sched_log sig tau2 Gamma' action_log' fbranch action_log'' v2 Gamma'' ->
            P sched_log sig tau2 Gamma action_log (If cond tbranch fbranch) action_log'' v2 Gamma'')
        (Pread0 : forall (sched_log : Log) (sig : tsig var_t) (Gamma : tcontext sig) (action_log : Log) (prt : Port) (idx : reg_t),
            may_read sched_log prt idx = true ->
            prt = P0 ->
            P sched_log sig (R idx) Gamma action_log (Read prt idx)
              (log_cons idx {| kind := LogRead; port := prt; val := tt |} action_log)
              (getenv REnv r idx) Gamma)
        (Pread1_latest : forall (sched_log : Log) (sig : tsig var_t) (Gamma : tcontext sig) (action_log : _Log)
                                (prt : Port) (idx : reg_t) (v : R idx),
            may_read sched_log prt idx = true ->
            prt = P1 ->
            latest_write0 (log_app action_log sched_log) idx = Some v ->
            P sched_log sig (R idx) Gamma action_log (Read prt idx)
              (log_cons idx {| kind := LogRead; port := prt; val := tt |} action_log) v Gamma)
        (Pread1_unchanged : forall (sched_log : Log) (sig : tsig var_t) (Gamma : tcontext sig) (action_log : _Log)
                                   (prt : Port) (idx : reg_t),
            may_read sched_log prt idx = true ->
            prt = P1 ->
            latest_write0 (log_app action_log sched_log) idx = None ->
            P sched_log sig (R idx) Gamma action_log (Read prt idx)
              (log_cons idx {| kind := LogRead; port := prt; val := tt |} action_log)
              (getenv REnv r idx) Gamma)
        (Pwrite : forall (sched_log : Log) (idx : reg_t) (sig : tsig var_t) (Gamma : tcontext sig) (action_log : Log)
                         (a : action sig (R idx)) (action_log' : Log) (Gamma' : tcontext sig)
                         (v : R idx) (prt : Port),
            ind_interp_action sched_log Gamma action_log a action_log' v Gamma' ->
            P sched_log sig (R idx) Gamma action_log a action_log' v Gamma' ->
            may_write sched_log action_log' prt idx = true ->
            P sched_log sig unit_t Gamma action_log (Write prt idx a)
              (log_cons idx {| kind := LogWrite; port := prt; val := v |} action_log') Ob Gamma')
        (Punop : forall (sched_log : Log) (sig : tsig var_t) (Gamma : tcontext sig) (action_log : Log)
                        (fn : PrimTyped.fn1) (a : action sig (arg1Sig (PrimSignatures.Sigma1 fn)))
                        (action_log' : Log) (Gamma' : tcontext sig) (v : arg1Sig (PrimSignatures.Sigma1 fn)),
            ind_interp_action sched_log Gamma action_log a action_log' v Gamma' ->
            P sched_log sig (arg1Sig (PrimSignatures.Sigma1 fn)) Gamma action_log a action_log' v Gamma' ->
            P sched_log sig (retSig (PrimSignatures.Sigma1 fn)) Gamma action_log (Unop fn a) action_log'
              (PrimSpecs.sigma1 fn v) Gamma')
        (Pbinop : forall (sched_log : Log) (sig : tsig var_t) (Gamma : tcontext sig) (action_log : Log)
                         (fn : PrimTyped.fn2) (a1 : action sig (arg1Sig (PrimSignatures.Sigma2 fn)))
                         (a2 : action sig (arg2Sig (PrimSignatures.Sigma2 fn))) (action_log' : Log)
                         (Gamma' : tcontext sig) (action_log'' : Log) (Gamma'' : tcontext sig)
                         (v1 : arg1Sig (PrimSignatures.Sigma2 fn)) (v2 : arg2Sig (PrimSignatures.Sigma2 fn)),
            ind_interp_action sched_log Gamma action_log a1 action_log' v1 Gamma' ->
            P sched_log sig (arg1Sig (PrimSignatures.Sigma2 fn)) Gamma action_log a1 action_log' v1 Gamma' ->
            ind_interp_action sched_log Gamma' action_log' a2 action_log'' v2 Gamma'' ->
            P sched_log sig (arg2Sig (PrimSignatures.Sigma2 fn)) Gamma' action_log' a2 action_log'' v2 Gamma'' ->
            P sched_log sig (retSig (PrimSignatures.Sigma2 fn)) Gamma action_log (Binop fn a1 a2) action_log''
              (PrimSpecs.sigma2 fn v1 v2) Gamma'')
        (Pextcall : forall (sched_log : Log) (sig : tsig var_t) (Gamma : tcontext sig) (action_log : Log)
                           (fn : ext_fn_t) (a : action sig (arg1Sig (Sigma fn))) (action_log' : Log)
                           (Gamma' : tcontext sig) (v : arg1Sig (Sigma fn)),
            ind_interp_action sched_log Gamma action_log a action_log' v Gamma' ->
            P sched_log sig (arg1Sig (Sigma fn)) Gamma action_log a action_log' v Gamma' ->
            P sched_log sig (retSig (Sigma fn)) Gamma action_log (ExternalCall fn a) action_log'
              (sigma fn v) Gamma')
        (Pintcall : forall (sched_log : Log) (sig0 : tsig var_t) (tau0 : type) (argspec : list (var_t * type))
                           (Gamma : tcontext sig0) (action_log action_log' : Log) (name : fn_name_t)
                           (args : acontext sig0 (rev argspec)) (v : tau0) (a : action (rev argspec) tau0)
                           (Gamma' : tcontext sig0) (action_log'' : Log) (Gamma'' ctx : tcontext (rev argspec)),
            ind_interp_args' ind_interp_action sched_log Gamma action_log args action_log' ctx Gamma' ->
            forall (Pargs: forall (sched_log : Log) k (m: member k (rev argspec))
                                  Gamma action_log action_log' Gamma' v,
                       ind_interp_action sched_log Gamma action_log (cassoc m args) action_log' v Gamma' ->
                       P sched_log sig0 (snd k) Gamma action_log (cassoc m args) action_log' v Gamma'
                   ),
              ind_interp_action sched_log ctx action_log' a action_log'' v Gamma'' ->
              P sched_log (rev argspec) tau0 ctx action_log' a action_log'' v Gamma'' ->
              P sched_log sig0 tau0 Gamma action_log (InternalCall name args a) action_log'' v Gamma')
        (Papos : forall (sched_log : Log) (sig : tsig var_t) (tau : type) (Gamma : tcontext sig) (action_log : Log)
                        (p : pos_t) (a : action sig tau) (action_log' : Log) (Gamma' : tcontext sig)
                        (v : tau),
            ind_interp_action sched_log Gamma action_log a action_log' v Gamma' ->
            P sched_log sig tau Gamma action_log a action_log' v Gamma' ->
            P sched_log sig tau Gamma action_log (APos p a) action_log' v Gamma'),
      forall (sched_log : Log) sig tau Gamma action_log (a: action sig tau) action_log' v Gamma',
        ind_interp_action sched_log Gamma action_log a action_log' v Gamma' ->
        P sched_log sig tau Gamma action_log a action_log' v Gamma'.
    Proof.
      intros.
      remember (size_action a).
      revert n sched_log sig tau Gamma action_log a action_log' v Gamma' H Heqn.
      intro n. pattern n.
      eapply Nat.strong_right_induction with (z:=0).
      {
        red. red. intros. subst. tauto.
      } 2: lia.
      intros n0 _ Plt sched_log sig tau Gamma action_log a action_log' v Gamma' H Heqn.
      assert (Plt':
                forall sched_log sig tau Gamma action_log a action_log' v Gamma',
                  size_action a < n0 ->
                  ind_interp_action sched_log Gamma action_log a action_log' v Gamma' ->
                  P sched_log sig tau Gamma action_log a action_log' v Gamma'
             ).
      {
        intros. eapply Plt. 4: reflexivity. lia. auto. auto.
      } clear Plt.
      rename Plt' into Plt.
      inv H; existT_tac; subst; eauto.
      - eapply Pseq; eauto; eapply Plt; simpl; eauto; lia.
      - destruct v. eapply Passign; eauto; eapply Plt; simpl; eauto; lia.
      - eapply Pbind; eauto; eapply Plt; simpl; eauto; lia.
      - eapply Piftrue; eauto; eapply Plt; simpl; eauto; lia.
      - eapply Piffalse; eauto; eapply Plt; simpl; eauto; lia.
      - destruct v; eapply Pwrite; eauto; eapply Plt; simpl; eauto; lia.
      - eapply Pbinop; eauto; eapply Plt; simpl; eauto; lia.
      - eapply Pintcall; eauto.
        intros; eapply Plt; eauto. simpl.
        specialize (cfoldl_size_contains (rev argspec) sig args _ m 0). lia.
        eapply Plt; simpl; eauto. lia.
    Qed.

    Lemma ind_interp_action_impl:
      forall sched_log sig tau a Gamma action_log action_log' Gamma' v
             (IA: @ind_interp_action sched_log sig tau Gamma action_log a action_log' v Gamma'),
        interp_action r sigma Gamma sched_log action_log a = Some (action_log', v, Gamma').
    Proof.
      intros.
      pattern sched_log, sig, tau, Gamma, action_log, a, action_log', v, Gamma'.
      revert sched_log sig tau Gamma action_log a action_log' v Gamma' IA .
      eapply ind_inter_action_ind_args; simpl; intros; eauto.
      - rewrite H0. simpl. eauto.
      - rewrite H0; simpl; eauto.
      - rewrite H0; simpl; eauto.
        rewrite H2; simpl; eauto.
      - rewrite H0; simpl; eauto.
        rewrite H1,H3; simpl; eauto.
      - rewrite H0; simpl; eauto.
        rewrite H1,H3; simpl; eauto.
      - rewrite H; subst. auto.
      - rewrite H; subst. rewrite H1; auto.
      - rewrite H; subst. rewrite H1; auto.
      - rewrite H0; simpl; rewrite H1; eauto.
      - rewrite H0; simpl; eauto.
      - rewrite H0; simpl.
        rewrite H2; simpl; eauto.
      - rewrite H0; simpl; eauto.
      - erewrite ind_interp_args'_impl; simpl; eauto.
        rewrite H1; simpl; eauto.
    Qed.

    Inductive ind_interp_rule (sched_log: Log) (rl: rule) : Log -> Prop :=
    | ind_interp_rule_intro:
        forall l v g,
          ind_interp_action sched_log CtxEmpty log_empty rl l v g ->
          ind_interp_rule sched_log rl l.

    Lemma interp_rule_eq:
      forall sched_log rl l,
        interp_rule r sigma sched_log rl = Some l <->
        ind_interp_rule sched_log rl l.
    Proof.
      unfold interp_rule; intros. split.
      - repeat destr. apply interp_action_impl in Heqo. inversion 1; subst; econstructor; eauto.
      - intro A; inv A. apply ind_interp_action_impl in H. rewrite H. auto.
    Qed.

  End Action.

End Interp.

Notation ind_interp_args r sigma Gamma sched_log action_log args :=
  (ind_interp_args' (@ind_interp_action _ _ _ _ _ _ _ _ r sigma) Gamma sched_log action_log args).
