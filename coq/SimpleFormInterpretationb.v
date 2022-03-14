Require Import Coq.Strings.Ascii.
Require Import Koika.Environments Koika.SimpleForm Koika.TypeInference
  Koika.UntypedSemantics.
Require Import Koika.BitsToLists.
From RecordUpdate Require Import RecordSet.
Import RecordSetNotations.
Require Import Sact.
Require Import Coq.Sorting.Sorted.
Require Import Coq.Sorting.Mergesort.
Require Import SimpleFormb.
Require Import SimpleFormInterpretation.

Section SimpleFormInterpretationb.
  Context {pos_t reg_t ext_fn_t rule_name_t: Type}.
  Variable reg_eqb: reg_t -> reg_t -> bool.
  Hypothesis reg_eqb_correct: forall r1 r2, reflect (r1 = r2) (reg_eqb r1 r2).
  Variable ext_fn_eqb: ext_fn_t -> ext_fn_t -> bool.
  Hypothesis ext_fn_eqb_correct: forall r1 r2, reflect (r1 = r2) (ext_fn_eqb r1 r2).

  Context {REnv: Env reg_t}.
  
  Context (R: reg_t -> type).
  Context (Sigma: ext_fn_t -> ExternalSignature).

  Definition uact := @daction pos_t string string reg_t ext_fn_t.
  Definition schedule := scheduler pos_t rule_name_t.
  Definition ext_funs_defs :=
    forall f: ext_fn_t, BitsToLists.val -> BitsToLists.val.
  Definition UREnv := REnv.(env_t) (fun _ => BitsToLists.val).

  Context (r: UREnv).
  Context (sigma: ext_funs_defs).

  Definition sact := sact (ext_fn_t:=ext_fn_t).

  Fixpoint replace_all_occurrences_in_sactb (ua: sact) (from: nat) (to: val)
  : sact :=
    match ua with
    | SBinop ufn a1 a2 =>
      SBinop
        ufn (replace_all_occurrences_in_sactb a1 from to)
        (replace_all_occurrences_in_sactb a2 from to)
    | SUnop ufn a1 => SUnop ufn (replace_all_occurrences_in_sactb a1 from to)
    | SVar v =>
      if Nat.eqb v from then SConst to
      else SVar v
    | SIf cond tb fb =>
      SIf
        (replace_all_occurrences_in_sactb cond from to)
        (replace_all_occurrences_in_sactb tb from to)
        (replace_all_occurrences_in_sactb fb from to)
    | SConst c => SConst c
    | SExternalCall ufn a => SExternalCall ufn (replace_all_occurrences_in_sactb a from to)
    end.

  Definition replace_all_occurrences_in_varsb
    (vars: var_value_map) (from: nat) (to: val)
  : var_value_map :=
    map
      (fun '(reg, (t, ua)) => (reg, (t, replace_all_occurrences_in_sactb ua from to)))
      vars.

  Definition replace_all_occurrencesb (sf: simple_form (reg_t:=reg_t)) (from: nat) (to: val)
  : simple_form := {|
    final_values := final_values sf;
    vars := replace_all_occurrences_in_varsb (vars sf) from to; |}.

  Definition simplify_varb (sf: simple_form) var :=
    match list_assocb Nat.eqb (vars sf) var with
      Some (t, a) =>
           match eval_sact_no_vars sigma a with
             Some v => (replace_all_occurrencesb sf var v, [(var,v)])
           | None => (sf, [])
           end
    | _ => (sf, [])
    end.

  Definition inlining_passb (sf: simple_form)
    : list (nat * val) :=
    (* Try to determine the value of variables *)
    let ks := NatSort.sort (map fst (vars sf)) in
    let '(sf,l) := fold_left
                     (fun '(sf,l) var =>
                        let '(sf,l1) := simplify_varb sf var in
                        (sf, l1++l))
                     ks (sf,[]) in
  l.

  Definition interp_cycleb (sf: simple_form) : UREnv :=
    let fenv := inlining_passb sf in
    create REnv (fun k =>
                   match list_assocb reg_eqb (final_values sf) k with
                     | Some n =>
                         match list_assocb Nat.eqb fenv n with
                         | Some v => v
                         | None => getenv REnv r k (* Should be unreachable *)
                         end
                   | None => getenv REnv r k
                   end).

  Section Eq.
    Context {eqreg: EqDec reg_t}.
    Context {eqextfn: EqDec ext_fn_t}.

    Lemma replace_all_occurrences_in_sactb_ok:
      forall a n v,
        replace_all_occurrences_in_sact a n v = replace_all_occurrences_in_sactb a n v.
    Proof.
      induction a; simpl; intros; eauto; try congruence.
      generalize (Nat.eqb_spec var n). intro A; inv A; destr; try congruence.
    Qed.

    Lemma replace_all_occurrences_in_varsb_ok:
      forall vvs n v,
        replace_all_occurrences_in_vars vvs n v = replace_all_occurrences_in_varsb vvs n v.
    Proof.
      unfold replace_all_occurrences_in_varsb, replace_all_occurrences_in_vars. intros.
      apply map_ext. intros. do 2 destr.
      rewrite <- replace_all_occurrences_in_sactb_ok. auto.
    Qed.

    Lemma replace_all_occurrencesb_ok:
      forall sf n v,
        replace_all_occurrences sf n v = replace_all_occurrencesb sf n v.
    Proof.
      unfold replace_all_occurrencesb, replace_all_occurrences. intros.
      rewrite <- replace_all_occurrences_in_varsb_ok. auto.
    Qed.

    Ltac rews :=
      repeat rewrite <- ? list_assocb_eq,
        <- ? list_assoc_setb_eq; eauto using Nat.eqb_spec, reflect_reg_port_unit_eqb, eqb_spec.

    Lemma simplify_varb_ok:
      forall sf var,
        simplify_var sigma sf var = simplify_varb sf var.
    Proof.
      unfold simplify_varb, simplify_var. intros. rews.
      do 3 destr. rewrite <- replace_all_occurrencesb_ok; auto.
    Qed.

    Lemma inlining_passb_ok:
      forall sf,
        inlining_pass sigma sf = inlining_passb sf.
    Proof.
      unfold inlining_passb, inlining_pass. intros.
      erewrite <- fold_left_ext. reflexivity. simpl; intros.
      destr. rewrite <- simplify_varb_ok. auto.
    Qed.

    Lemma interp_cycleb_ok:
      forall sf,
        interp_cycle r sigma sf = interp_cycleb sf.
    Proof.
      unfold interp_cycle, interp_cycleb. intros.
      apply create_funext.
      intros.
      rews. destr; auto. rews. rewrite <- inlining_passb_ok. auto.
    Qed.

  End Eq.

End SimpleFormInterpretationb.
