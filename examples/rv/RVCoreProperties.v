Require Export rv.Stack rv.RVCore rv.rv32 rv.rv32i.
Require Import Koika.Frontend Koika.Logs Koika.Std Koika.ProgramTactics.

Module StackProofs.
  Import StackF.
  Definition default := ContextEnv.(create) r.

  Definition is_stack_empty (reg : ContextEnv.(env_t) R) :=
    ContextEnv.(getenv) reg size = Bits.zero.

  Definition is_stack_full (reg : ContextEnv.(env_t) R) :=
    ContextEnv.(getenv) reg size = (Bits.of_nat index_sz capacity).

  (* Definition cycle (r: ContextEnv.(env_t) R) := *)
  (*   CompactSemantics.interp_cycle RV32I.Sigma RV32I.rv_rules rv_schedule r. *)

  Ltac unfolds :=
    unfold desugar_action, desugar_action', TypeInference.tc_action,
    TypeInference.tc_action, type_action, projT2, projT2, lift_fn1_tc_result,
    lift_fn2_tc_result, lift_fn1_tc_result, lift_fn2_tc_result, projT1, projT2,
    cast_action, cast_action' in *.

  (* Theorem pop_returns_one_when_stack_empty : *)
  (*   forall env Gamma sched_log action_log action_log_new v Gamma_new, *)
  (*   interp_action env empty_sigma Gamma sched_log action_log *)
  (*     (tc_function R empty_Sigma pop) *)
  (*     = Some (action_log_new, v, Gamma_new) *)
  (*   -> is_stack_empty env -> v = Ob~1. *)
  (* Proof. *)
  (*   intros env Gamma sched_log action_log action_log_new v Gamma_new. *)
  (*   intros. *)
  (*   eauto with SimplifyKoika. *)
  (*   Print HintDb SimplifyKoika. *)
  (*   eauto SimplifyKoika. *)
  (*   (1* eauto SimplifyKoika. *1) *)
  (*   cbv. *)
  (*   Hint Unfold desugar_action. *)
(*     apply desugar_action. *)

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

(* Lemma type_eq_dec_rewrite : *)
(*   forall (T : Type) (x : type) (y : type) (A : _ -> T) (B : _ -> T) *)
(*          (Heq: x = y), *)
(*     match eq_dec x y with *)
(*     | left p => A p *)
(*     | right p => B p *)
(*     end = A Heq . *)
(* Proof. *)
(*   intros. *)
(*   destruct (type_eq_dec_left _ _ Heq) as (p & EQ). *)
(*   rewrite EQ. *)
(*   f_equal. apply Eqdep_dec.UIP_dec. apply eq_dec. *)
(* Qed. *)

  (*
    env = contains the value of available registers at the start of the rule for
          read0 and after write0 for read1,
    Gamma = values of the variables created by let bindings before pop,
    Gamma_new = values of the variables created by let bindings after pop,
    sched_log = reads and writes performed by rules executed earlier in the same
                clock cycle,
    action_log = empty, used to accumulate the reads and writes of the rule,
    action_log_new = contains the reads and writes of the rule
   *)

Ltac destr_in H :=
  match type of H with
  | context[match ?a with _ => _ end] => destruct a eqn:?
  end.

Ltac destr :=
  match goal with
  |- context[match ?a with _ => _ end] => destruct a eqn:?; try congruence
  end.

Lemma extract_success_rewrite:
  forall {S F: Type} (res1 res2: result S F) pr1 pr2,
    res1 = res2 ->
    extract_success res1 pr1 = extract_success res2 pr2.
Proof.
  intros. subst.
  (* Eqdep_dec.UIP_dec *)
Admitted.


Ltac inv H :=
  inversion H; try subst; clear H.


Theorem pop_returns_one_when_stack_empty :
    forall env Gamma sched_log action_log action_log_new v Gamma_new,
    interp_action env empty_sigma Gamma sched_log action_log
      (tc_function R empty_Sigma pop)
      = Some (action_log_new, v, Gamma_new)
    -> is_stack_empty env -> v = Ob~1.
  Proof.
    intros env Gamma sched_log action_log action_log_new v Gamma_new.
    unfold desugar_action.
    intros.
    refine match desugar_action' dummy_pos (fun r : reg_t => r) (fun fn : empty_ext_fn_t => fn) (int_body pop) with
             x => _
           end.
    fold x in H.
    refine (match TypeInference.tc_action R empty_Sigma dummy_pos (int_argspec pop) (int_retSig pop) x as r return (TypeInference.tc_action R empty_Sigma dummy_pos (int_argspec pop) (int_retSig pop) x = r -> is_success r = true -> _) with
             Success s => fun H1 H2 => _
           | Failure f => fun H1 H2 => _
            end eq_refl eq_refl).
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
    refine match desugar_action' dummy_pos (fun r : reg_t => r) (fun fn : empty_ext_fn_t => fn) (int_body push) with
             x => _
           end.
    fold x in H.
    refine (match TypeInference.tc_action R empty_Sigma dummy_pos (int_argspec push) (int_retSig push) x as r return (TypeInference.tc_action R empty_Sigma dummy_pos (int_argspec push) (int_retSig push) x = r -> is_success r = true -> _) with
             Success s => fun H1 H2 => _
           | Failure f => fun H1 H2 => _
            end eq_refl eq_refl).
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

  Theorem forall_calls :
    forall s log, interp_scheduler r sigma rules s = log ->

  .

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
