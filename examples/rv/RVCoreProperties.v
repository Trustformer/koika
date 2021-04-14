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
  forall (x y : type),
  x = y -> exists p, eq_dec x y = left p.
Proof.
  induction 1. exists eq_refl. destruct x.
  - simpl. rewrite (self_implies_left sz); trivial.
  - simpl.
  - 
Qed.

Lemma temp :
  forall (T : Type) (x : type) (y : type) (A : T) (B : T), x = y ->
    match eq_dec x y with
    | left _ => A
    | right _ => B
    end = A.


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
  Theorem pop_returns_one_when_stack_empty :
    forall env Gamma sched_log action_log action_log_new v Gamma_new,
    interp_action env empty_sigma Gamma sched_log action_log
      (tc_function R empty_Sigma pop)
      = Some (action_log_new, v, Gamma_new)
    -> is_stack_empty env -> v = Ob~1.
  Proof.
    intros env Gamma sched_log action_log action_log_new v Gamma_new.
    unfold desugar_action.
    unfold desugar_action'.
    simpl TypeInference.tc_action.
    unfold TypeInference.tc_action.
    unfold type_action.
    simpl projT2.
    simpl projT2.
    simpl lift_fn1_tc_result.
    simpl lift_fn2_tc_result.
    unfold lift_fn1_tc_result.
    unfold lift_fn2_tc_result.
    cbn beta delta iota.
    unfold projT1.
    unfold projT2.
    cbn beta delta iota.
    unfold cast_action.
    unfold cast_action'.
    (* pose proof (eq_dec_refl (bits_t 3)). *)
    (* rewrite H. *)
    unfold eq_rec_r.
    unfold eq_rec.
    unfold Nat.eq_dec.
    unfold eq_rec_r.
    unfold eq_rec.
    unfold eq_rect.
    simpl eq_sym.
    cbn iota.
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
    cbn.
    intros H1 H2.
    rewrite H2 in H1.
    destruct may_read in H1; cbn in H1.
    - injection H1 as H3 H4 H5. symmetry. exact H4.
    - discriminate H1.
  Qed.

  Theorem push_returns_one_when_stack_full :
    forall env Gamma sched_log action_log action_log_new v Gamma_new,
    interp_action env empty_sigma Gamma sched_log action_log
      (tc_function R empty_Sigma push)
      = Some (action_log_new, v, Gamma_new)
    -> is_stack_full env -> v = Ob~1.
  Proof.
    intros env Gamma sched_log action_log action_log_new v Gamma_new.
    cbn beta delta iota.
    unfold desugar_action'.
    cbn beta delta iota.
    unfold TypeInference.tc_action.
    cbn beta delta iota.
    simpl cast_action.
    unfold cast_action.
    unfold cast_action'.
    cbn beta delta iota.
    unfold eq_rec_r.
    simpl eq_rec.
    unfold eq_rec.
    simpl type_action.
    cbn beta delta iota.
    unfold eq_rect_r.
    simpl eq_rect.
    cbn beta delta iota.
    unfold eq_rect.
    cbn beta delta iota.
    unfold eq_sym.
    cbn beta delta iota.
    intros H1 H2.
    rewrite H2 in H1.
    destruct may_read in H1; cbn in H1.
    - injection H1 as H3 H4 H5. symmetry. exact H4.
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
