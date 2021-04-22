Require Export rv.Stack rv.RVCore rv.rv32 rv.rv32i.
Require Import Koika.TypedSemantics Koika.Frontend Koika.Logs Koika.Std
Koika.ProgramTactics.

Require Import Koika.IndTypedSemantics.

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

Module StackProofs.
  (*
    # Kôika
    Types:
    - type (
      Inductive type : Type :=
      | bits_t : nat -> type
      | enum_t : enum_sig -> type
      | struct_t : struct_sig -> type
      | array_t : array_sig -> type.
    );
    - _Sig (
      Record _Sig {argKind: Type} {nArgs: nat} := {
        argSigs : vect argKind nArgs;
        retSig : argKind
      }.
    );
    - tsig : forall var_t, list (var_t * type);
    - action (
      Inductive action : tsig var_t -> type -> Type :=
      | Fail {sig} tau : action sig tau
      | Var {sig} {k : var_t} {tau : type} (m : member (k, tau) sig)
        : action sig tau.
      ...
      .
    )
    - scheduler (
      Inductive scheduler :=
      | Done
      | Cons (r: rule_name_t) (s: scheduler)
      | Try (r: rule_name_t) (s1 s2: scheduler)
      | SPos (p: pos_t) (s: scheduler).
    ).
    Rôle de Try et SPos ?

    # Modèle
    Types :
    - reg_t : registres (Set);
    - ext_fn_t : fonctions externes (Set);
    - rule_name_t : règles (Set).
    - schedule : (scheduler)
    Fonctions :
    - R : typage des reg_t (reg_t -> type);
    - r : valeur initiale des reg_t ((reg : reg_t) -> R reg);
    - Sigma : décl. des ext_fn_t (ext_fn_t -> _Sig type 1);
    - sigma : déf. des ext_fn_t ((fn : ext_fn_t) -> Sig_denote (Sigma fn));
    - rules : déf. des règles (rule_name_t -> action R Sigma).

    # Fonctions
    interp_action :
    état des registres en début de cycle
    -> déclaration des ext_fn_t [Sigma]
    -> valeur des bindings lets de la règle à ce stade
    -> log des règles précédentes dans le schedule
    -> log de la règle à ce stade
    -> action à interpréter
    -> option (log de la règle, val de retour, nvlle val des bindings let)

    interp_scheduler :
    état des registres en début de cycle
    -> déclaration des ext_fn_t [Sigma]
    -> définition des règles [rules]
    -> schedule à interpréter
    -> log du schedule

    interp_rule :
    état des registres en début de cycle
    -> déclaration des ext_fn_t [Sigma]
    -> log des règles précédentes dans le schedule
    -> règle à interpréter
    -> option (log de la règle)

    interp_cycle :
    déclaration des ext_fn_t [Sigma]
    -> définition des règles [rules]
    -> schedule
    -> état des registres en début de cycle
    -> état des registres suite à ce cycle (càd en début du cycle suivant)

    commit_update :
    état des registres en début de cycle
    -> log à la fin du cycle
    -> état des registres en fin de cycle
  *)

  Definition rv_cycle
    (r: ContextEnv.(env_t) RV32I.R)
    (sigma : forall f, Sig_denote (RV32I.Sigma f))
  :=
  TypedSemantics.interp_cycle sigma RV32I.rv_rules rv_schedule r.

  (*
  Détecter dans quelles situations un write visant le registre halt a lieu.
  Problème : impossible de détecter si l'appel à halt
  *)

  Lemma extract_success_rewrite:
    forall {S F: Type} (res1 res2: result S F) pr1 pr2,
    res1 = res2 -> extract_success res1 pr1 = extract_success res2 pr2.
  Proof.
    intros. subst.
    refine (
      match pr1, pr2 with
      | eq_refl _, eq_refl _ => _
      end
    ).
    destruct res2; congruence.
  Qed.

  Lemma success_inj:
    forall {S F: Type} (x y: S), Success x = @Success S F y -> x = y.
  Proof.
    intros S F x y H. inv H; auto.
  Qed.

  Lemma cast_action'_eq:
    forall (pos_t fn_name_t var_t reg_t ext_fn_t : Type) (R : reg_t -> type)
           (Sigma : ext_fn_t -> ExternalSignature)
           (p: pos_t) (sig: tsig var_t) (tau1 tau2: type)
           (a: action pos_t var_t fn_name_t R Sigma sig tau1)
           (e: error_message var_t fn_name_t) a',
      cast_action' R Sigma p tau2 a e = Success a' ->
      exists p : tau1 = tau2,
        a' = eq_rect _ _ a _ p.
  Proof.
    unfold cast_action'. intros.
    destr_in H. subst.
    unfold eq_rect_r in H. simpl in H. inv H.
    exists eq_refl; reflexivity. inv H.
  Qed.

  Lemma cast_action_eq:
    forall (pos_t fn_name_t var_t reg_t ext_fn_t : Type) (R : reg_t -> type)
           (Sigma : ext_fn_t -> ExternalSignature)
           (p: pos_t) (sig: tsig var_t) (tau1 tau2: type)
           (a: action pos_t var_t fn_name_t R Sigma sig tau1)
           a',
      cast_action R Sigma p tau2 a = Success a' ->
      exists p : tau1 = tau2,
        a' = eq_rect _ _ a _ p.
  Proof.
    intros. unfold cast_action in H.
    eapply cast_action'_eq; eauto.
  Qed.
 
  Lemma execute_overwrites_halt:
    forall (r: ContextEnv.(env_t) RV32I.R) sigma l,
      ind_interp_rule r sigma log_empty RV32I.tc_execute l ->
      log_existsb l RV32I.halt (fun k p =>
                                  match k with
                                    LogRead => false
                                  | LogWrite => true
                                  end
                               ) = true(*  -> *)
      (* let dbk := ContextEnv.(getenv) r (RV32I.d2e RV32I.fromDecode.data0) = dbk in *)
      (* let dInst :=  *)

        (* RV32I.isControlInst *)
  .
  Proof.
    intros.
    inv H.
    unfold RV32I.tc_execute in H0.
    unfold desugar_action in H0.
    intros.
    refine (
      match
        desugar_action' dummy_pos (fun r : RV32I.reg_t => r)
        (fun fn => fn) (RV32I.execute)
      with
         x => _
      end
    ).
    fold x in H0.
    refine ((
      match
        TypeInference.tc_action RV32I.R RV32I.Sigma dummy_pos [] unit_t x
      as r
      return (
        TypeInference.tc_action RV32I.R RV32I.Sigma dummy_pos [] unit_t x = r
        -> is_success r = true -> _
      ) with
      | Success s => fun H1 H2 => _
      | Failure f => fun H1 H2 => _
      end
    ) eq_refl eq_refl).
    2: (simpl in H2; congruence).
    erewrite extract_success_rewrite in H0. 2: apply H1.
    simpl (extract_success _ _) in H0.

    unfold TypeInference.tc_action in H1.
    destr_in H1. 2: congruence.
    clear H2.
    apply cast_action_eq in H1.
    destruct H1 as (p & EQ). subst s.
    revert Heqr0. simpl in x.
    unfold eq_rect in H0.
    destruct p.
    unfold desugar_action' in x. cbn in x.
    unfold x. clear x.
    intro Heqr0.
    vm_compute in Heqr0.
    apply success_inj in Heqr0.
    subst s0. simpl projT1 in v.
    simpl projT2 in H0.
    match type of H0 with
      context [Seq ?a1 ?a2] => set(XX:=a2); fold XX in H0
    end.
    inv H0.

    unfold eq_rect in Heqo.
    destruct p.
    assert (p = eq_refl).
    rewrite <- Heqr0 in Heqo.
    revert H1; rewrite <- Heqr0; clear Heqr0.
    simpl projT2.
    intro Hcast; vm_compute in Hcast; inv Hcast.


    Heqr0.
    vm_compute in H1. inv H1. simpl in H2.
    cbn beta delta iota zeta in H.
    revert H.
    unfold opt_bind.
    destruct may_read.
    - rewrite H0.
      rewrite (proj2 (beq_dec_iff _ _ _)). intro A; inv A. reflexivity.
      reflexivity.
    - congruence.

    unfold x in H1. vm_compute in H1.





    interp_action_t.
  Qed.

  Theorem stack_0_implies_no_setting_halt :
    (r: ContextEnv.(env_t) RV32I.R)
    (sigma : forall f, Sig_denote (RV32I.Sigma f)),
     r.(getenv) halt = 0 -> (rv_cycle r sigma).(getenv) halt = 1 ->

  Theorem forall_calls :
    forall (r : ContextEnv.(env_t) RV32I.R)
    (sigma : forall f, Sig_denote (RV32I.Sigma f)),
    rv_cycle r sigma.
  Proof.
    vm_compute.
  .

  Import StackF.
  Definition default := ContextEnv.(create) r.

  Definition is_stack_empty (reg : ContextEnv.(env_t) R) :=
    ContextEnv.(getenv) reg size = Bits.zero.

  Definition is_stack_full (reg : ContextEnv.(env_t) R) :=
    ContextEnv.(getenv) reg size = (Bits.of_nat index_sz capacity).

  Definition Sigma := RV32I.Sigma.

  Ltac unfolds :=
    unfold desugar_action, desugar_action', TypeInference.tc_action,
    TypeInference.tc_action, type_action, projT2, projT2, lift_fn1_tc_result,
    lift_fn2_tc_result, lift_fn1_tc_result, lift_fn2_tc_result, projT1, projT2,
    cast_action, cast_action' in *.

  Theorem self_implies_left : forall (n : nat), n = n ->
    Nat.eq_dec n n = left eq_refl.
  Proof.
    intros. induction n.
    - trivial.
    - simpl. assert (n = n) by trivial.
      apply IHn in H0. rewrite H0. trivial.
  Qed.

  Theorem type_eq_dec_left :
    forall (x y : type) (Heq: x = y),
      eq_dec x y = left (eq_rect x (fun y => eq x y) eq_refl _ Heq).
  Proof.
    intros. subst.
    destruct (eq_dec y y). simpl.
    f_equal. apply Eqdep_dec.UIP_dec. apply eq_dec.
    congruence.
  Qed.

  (*
    env = contains the value of available registers at the start of the rule for
          read0 and after write0 for read1,
    Gamma = values of the variables created by let bindings before pop,
    Gamma_new = values of the variables created by let bindings after pop,
    sched_log = reads and writes performed by rules executed earlier in the same
                clock cycle,
    action_log = empty, used to accumulate the reads and writes of the rule,
    action_log_new = contains the reads and writes of the rule *)
  Theorem pop_returns_one_when_stack_empty :
    forall env Gamma sched_log action_log action_log_new v Gamma_new,
    interp_action env Sigma Gamma sched_log action_log
      (tc_function R Sigma pop) = Some (action_log_new, v, Gamma_new)
      -> is_stack_empty env -> v = Ob~1.
  Proof.
    intros env Gamma sched_log action_log action_log_new v Gamma_new.
    unfold desugar_action.
    intros.
    refine (
      match
        desugar_action' dummy_pos (fun r : reg_t => r)
        (fun fn : empty_ext_fn_t => fn) (int_body pop)
      with
         x => _
      end
    ).
    fold x in H.
    refine ((
      match
        TypeInference.tc_action R empty_Sigma dummy_pos (int_argspec pop)
        (int_retSig pop) x
      as r
      return (
        TypeInference.tc_action R empty_Sigma dummy_pos (int_argspec pop)
          (int_retSig pop) x = r
        -> is_success r = true -> _
      ) with
      | Success s => fun H1 H2 => _
      | Failure f => fun H1 H2 => _
      end
    ) eq_refl eq_refl).
    2: (simpl in H2; congruence).
    erewrite extract_success_rewrite in H. 2: apply H1. simpl in H.
    Unshelve. 2: reflexivity.
    revert H1.

    unfold TypeInference.tc_action.
    destr. intros.
    revert Heqr0. simpl in x.
    unfold desugar_action' in x. cbn in x.
    unfold x. clear x.

    intro Heqr0.
    vm_compute in Heqr0. inv Heqr0.
    vm_compute in H1. inv H1. simpl in H2.
    cbn beta delta iota zeta in H.
    revert H.
    unfold opt_bind.
    destruct may_read.
    - rewrite H0.
      rewrite (proj2 (beq_dec_iff _ _ _)). intro A; inv A. reflexivity.
      reflexivity.
    - congruence.
  Qed.

  Theorem push_returns_one_when_stack_full :
    forall env Gamma sched_log action_log action_log_new v Gamma_new,
    interp_action env empty_sigma Gamma sched_log action_log
      (tc_function R empty_Sigma push)
      = Some (action_log_new, v, Gamma_new)
    -> is_stack_full env -> v = Ob~1.
  Proof.
    intros env Gamma sched_log action_log action_log_new v Gamma_new.
    unfold desugar_action.
    intros.
    refine (
      match
        desugar_action' dummy_pos (fun r : reg_t => r)
        (fun fn : empty_ext_fn_t => fn) (int_body push)
      with
        x => _
      end
    ).
    fold x in H.
    refine ((
      match
        TypeInference.tc_action R empty_Sigma dummy_pos (int_argspec push)
        (int_retSig push) x
      as r
      return (
        TypeInference.tc_action R empty_Sigma dummy_pos (int_argspec push)
        (int_retSig push) x = r -> is_success r = true -> _
      ) with
      | Success s => fun H1 H2 => _
      | Failure f => fun H1 H2 => _
      end
    ) eq_refl eq_refl).
    2: (simpl in H2; congruence).
    erewrite extract_success_rewrite in H. 2: apply H1. simpl in H.
    Unshelve. 2: reflexivity.

    vm_compute in H1. inv H1. clear H2.
    cbn beta delta iota zeta in H.
    revert H.
    unfold opt_bind.
    intro H1.
    destruct may_read in H1; cbn in H1.
    - rewrite H0 in H1.
      rewrite (proj2 (beq_dec_iff _ _ _)) in H1. inv H1. reflexivity.
      reflexivity.
    - discriminate H1.
  Qed.

  Definition stack_top (reg : ContextEnv.(env_t) R) :=
    let index := (ContextEnv.(getenv) reg size) in
    stack (Vect.index_of_nat (Bits. index)).

  (* Definition pop_candidate_address (reg : ContextEnv.(env_t) R) :=. *)

  (* Definition stack_misuse. *)

  Theorem pop_returns_one_on_address_mismatch :
    forall env Gamma sched_log action_log action_log_new v Gamma_new,
    interp_action env empty_sigma Gamma sched_log action_log
      (tc_function R empty_Sigma pop) = Some (action_log_new, v, Gamma_new)
    -> stack_top env <> pop_candidate_address -> v = Ob~1.
  Proof.
    intros env Gamma sched_log action_log action_log_new v Gamma_new.
    cbn beta delta iota.
    simpl in Gamma.
    unfold TypedSemantics.tcontext in Gamma.
    simpl in Gamma.
    simpl in Gamma.
    unfold desugar_action.
    unfold desugar_action'.
    cbn beta delta iota.
    unfold TypeInference.tc_action.
    simpl desugar_action'.
    unfold desugar_action'.
    Search desugar_action.
    Locate "{{ _ }}".
    cbn beta delta iota.
    unfold log2.
    cbn beta delta iota.
    unfold cast_action.
    unfold cast_action'.
    cbn beta delta iota.
    unfold eq_rec_r.
    unfold eq_rec.
    cbn beta delta iota.
    unfold eq_rect_r.
    unfold eq_rect.
    unfold eq_sym.
    cbn beta delta iota.
    unfold eq_ind_r.
    unfold eq_ind.
    unfold eq_sym.
    cbn beta delta iota.
    unfold Nat.eq_dec.
    cbn beta delta iota.
    simpl type_action.

  Theorem stack_returns_zero_when_not_misused : .

  Theorem pop_failure_sets_halt : .
  Theorem push_failure_sets_halt : .
  Theorem stack_misuse_sets_halt: .

  Theorem all_rules_but_end_execution_fail_when_halt_set :.
  Theorem end_execution_calls_ext_finish_when_halt_set :.

  Theorem end_execution_does_not_update_the_processor_state :.

  Theorem valid_stack_use_does_not_impact_the_execution :.
End Stack.
