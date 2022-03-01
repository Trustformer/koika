Require Import Coq.Lists.List.
Require Import Koika.BitsToLists Koika.EqDec Koika.Environments Koika.Types.
Require Import Koika.SimpleForm Koika.SimpleFormInterpretation.

Section SimpleFormTactics.
  Context {pos_t reg_t ext_fn_t rule_name_t: Type}.
  Context {reg_t_eq_dec: EqDec reg_t}.
  Context {ext_fn_t_eq_dec: EqDec ext_fn_t}.
  Context {REnv: Env reg_t}.
  Context {TR: reg_t -> type}.

  Context (sf: @simple_form pos_t reg_t ext_fn_t).

  Context (R: reg_t -> type).
  Context (Sigma: ext_fn_t -> ExternalSignature).
  Definition ext_funs_defs :=
    forall f: ext_fn_t, BitsToLists.val -> BitsToLists.val.
  Context (sigma: ext_funs_defs).

  Definition UREnv := REnv.(env_t) (fun _ => BitsToLists.val).

  Definition f rbf :=
    (fun (acc : env_t REnv (fun _ : reg_t => val)) '(reg, n) =>
      REnv.(putenv)
        acc reg
        (match
          list_assoc
            (simplify
             rbf sigma sf
             (Datatypes.length (vars sf)
              + Datatypes.length (external_calls sf)))
            n
         with
         | Some v => v
         | None => getenv REnv rbf reg
         end)).

  Definition f' fenv l acc :=
    fold_left (f fenv) l acc.

  Definition preserved_reg (bf: UREnv) (reg: reg_t) (af: UREnv) : Prop :=
    REnv.(getenv) bf reg = REnv.(getenv) af reg.

  Lemma rev_sym:
    forall {A: Type} (l1 l2: list A),
    l1 = rev l2 <-> rev l1 = l2.
  Proof.
    split; intro.
    - rewrite H. rewrite rev_involutive. easy.
    - rewrite <- H. rewrite rev_involutive. easy.
  Qed.

  Lemma fold_left_prop:
    forall {A B: Type} (P: B -> Prop) (f: B -> A -> B) (l: list A) (s: B),
    P s
    -> (forall x y, P x -> In y l -> P (f x y))
    -> P (fold_left f l s).
  Proof.
    induction l.
    - easy.
    - intros.
      rewrite <- fold_left_rev_right. simpl.
      rewrite fold_right_app. simpl.
      rewrite fold_left_rev_right.
      apply IHl.
      + apply H0.
        * easy.
        * unfold In. left. easy.
      + intros. apply H0.
        * easy.
        * unfold In. right. easy.
  Qed.

  Lemma interp_one_does_not_modify_others:
    forall fenv (e1 e2: UREnv) (reg reg': reg_t) (s: string),
    reg' <> reg
    -> preserved_reg e1 reg e2
    -> preserved_reg e1 reg (f fenv e2 (reg', s)).
  Proof.
    intros.
    simpl in *.
    unfold preserved_reg.
    rewrite get_put_neq; easy.
  Qed.

  Lemma interp_not_in_list_preserved:
    forall fenv (e: UREnv) (reg: reg_t),
    (forall x, In x (final_values sf) -> fst x <> reg)
    -> preserved_reg e reg (f' fenv (final_values sf) e).
  Proof.
    intros.
    unfold f'.
    apply fold_left_prop; try easy.
    intros.
    assert (fst y <> reg). { apply H. easy. }
    assert (y = (fst y, snd y)). { apply surjective_pairing. }
    rewrite H3.
    apply interp_one_does_not_modify_others; easy.
  Qed.

  Lemma list_assoc_in_some:
    forall {A B: Type} {EA: EqDec A} l (kv: A * B),
    In kv l -> exists v, list_assoc l (fst kv) = Some v.
  Proof.
    intros.
    destruct (list_assoc l (fst kv)) eqn:eq1.
    - exists b. reflexivity.
    - induction l.
      + inv H.
      + destruct H.
        * rewrite surjective_pairing in H.
          rewrite H in eq1. simpl in eq1.
          rewrite eq_dec_refl in eq1.
          inv eq1.
        * apply IHl; try easy.
          specialize (surjective_pairing a) as Hsa.
          rewrite Hsa in eq1.
          simpl in eq1.
          destruct (eq_dec (fst kv) (fst a)); easy.
  Qed.

  Lemma no_writes_implies_value_unchanged:
    forall (reg: reg_t) (e: UREnv),
    list_assoc (final_values sf) reg = None
    -> REnv.(getenv) e reg = REnv.(getenv) (interp_cycle e sigma sf) reg.
  Proof.
    intros.
    unfold interp_cycle.
    fold (f e). fold (f' e (final_values sf) e).
    apply interp_not_in_list_preserved.
    intros.
    apply list_assoc_in_some in H0.
    destruct H0. congruence.
  Qed.

  Lemma app_inv_last:
    forall {A: Type} (l1 l2: list A) (x y: A),
    l1 ++ [x] = l2 ++ [y]
    -> x = y.
  Proof.
    intros.
    apply (f_equal (@rev A)) in H.
    rewrite rev_app_distr in H. rewrite rev_app_distr in H at 1.
    simpl in H. inv H.
    easy.
  Qed.

  Lemma fold_left_prop_eventually_no_tail:
    forall {A B: Type} (P: B -> Prop) (f: B -> A -> B) (lb: list A) (s: B) x,
    (forall e, P (f e x))
    -> P (fold_left f (lb ++ [x]) s).
  Proof.
    intros.
    assert (exists l', l' = rev (lb ++ [x])).
      { exists (rev (lb ++ [x])). easy. }
    destruct H0.
    apply rev_sym in H0.
    rewrite <- H0.
    induction x0.
    - destruct lb; easy.
    - rewrite <- fold_left_rev_right. rewrite rev_involutive.
      assert (x = a). { simpl in H0. apply app_inv_last in H0. easy. }
      simpl. inv H1. eapply H.
  Qed.

  Lemma fold_left_prop_eventually:
    forall {A B: Type} (P: B -> Prop) (f: B -> A -> B) (lb la: list A) (s: B) x,
    (forall e, P (f e x))
    -> (forall y e, In y la -> P e -> P (f e y))
    -> P (fold_left f (lb ++ [x] ++ la) s).
  Proof.
    intros A B P f0 lb la s x H0.
    remember (rev la) as la'. apply rev_sym in Heqla'. rewrite <- Heqla'.
    generalize dependent la.
    induction la'; intros; simpl.
    - apply fold_left_prop_eventually_no_tail. easy.
    - rewrite <- fold_left_rev_right.
      repeat (rewrite rev_app_distr; simpl). rewrite rev_involutive.
      apply H.
      + apply in_rev. rewrite rev_involutive. left. easy.
      + assert ((la' ++ [x]) ++ rev lb = rev (lb ++ [x] ++ rev la')).
        { repeat (rewrite rev_app_distr). rewrite rev_involutive. easy. }
        rewrite H1.
        rewrite fold_left_rev_right.
        eapply IHla'.
        * eauto.
        * intros. apply H.
          ** apply in_rev. rewrite rev_involutive.
             apply in_rev in H2. right. easy.
          ** easy.
  Qed.

  Lemma one_in_fv_implies_written_value:
    forall fenv (e: UREnv) (reg: reg_t) (n: string) v,
    In (reg, n) (final_values sf)
    -> list_assoc (
         simplify
           fenv sigma sf
           (Datatypes.length (vars sf) + Datatypes.length (external_calls sf))
       ) n = Some v
    -> (forall m, In (reg, m) (final_values sf) -> m = n)
    -> getenv REnv (f' fenv (final_values sf) e) reg = v.
  Proof.
    intros.
    unfold f'.
    remember (fun x => getenv REnv x reg = v) as P.
    assert (
      (getenv REnv (fold_left (f fenv) (final_values sf) e) reg = v)
      = P (fold_left (f fenv) (final_values sf) e)
    ). { rewrite HeqP. reflexivity. }
    rewrite H2.
    apply in_split in H as H'.
    destruct H'. destruct H3.
    rewrite H3.
    assert (x ++ (reg, n) :: x0 = x ++ [(reg, n)] ++ x0) by easy.
    rewrite H4.
    apply fold_left_prop_eventually; intros; simpl.
    - rewrite HeqP. simpl. rewrite get_put_eq.
      rewrite H0. reflexivity.
    - specialize (surjective_pairing y) as Hsy. inv Hsy.
      assert (In y (final_values sf)).
      {
        rewrite H3. rewrite H4.
        apply in_app_iff. right. apply in_app_iff. right.
        easy.
      }
      destruct (beq_dec (fst y) reg) eqn:eqreg.
      + apply beq_dec_iff in eqreg. rewrite eqreg. unfold f.
        rewrite get_put_eq.
        assert (snd y = n).
        { rewrite eqreg in H7. apply H1. rewrite H7 in H6. easy. }
        rewrite H8. rewrite H0. easy.
      + apply beq_dec_false_iff in eqreg.
        unfold f. rewrite get_put_neq; easy.
  Qed.

  Axiom single_write:
    forall (reg: reg_t) (n: string),
    In (reg, n) (final_values sf)
    -> (forall m, In (reg, m) (final_values sf) -> n = m).

  Axiom fuel_ok:
    forall {e} {fenv} {reg} {n},
    list_assoc (final_values sf) reg = Some n
    -> exists v,
      list_assoc (
        simplify (REnv := e)
          fenv sigma sf
          (Datatypes.length (vars sf) + Datatypes.length (external_calls sf))
      ) n = Some v.

  Lemma reg_neq_neq_dec:
    forall (r s: reg_t), r <> s -> exists t, eq_dec r s = right t.
  Proof.
    intros.
    destruct (eq_dec r s).
    - contradiction.
    - exists n. reflexivity.
  Qed.

  Lemma write_implies_written_value:
    forall fenv (e: UREnv) (reg: reg_t) (n: string),
    In (reg, n) (final_values sf)
    -> (
      exists v,
      list_assoc (
        simplify
          fenv sigma sf
          (Datatypes.length (vars sf) + Datatypes.length (external_calls sf))
      ) n = Some v
      /\ getenv REnv (f' fenv (final_values sf) e) reg = v
    ).
  Proof.
    intros.
    specialize (single_write reg n) as H'.
    assert (list_assoc (final_values sf) reg = Some n).
    {
      induction (final_values sf).
      - inversion H.
      - rewrite (surjective_pairing a) in *. simpl.
        destruct (beq_dec reg (fst a)) eqn:eqr.
        + apply beq_dec_iff in eqr. rewrite <- eqr. rewrite eq_dec_refl.
          f_equal. symmetry. apply H'.
          * easy.
          * simpl. left. rewrite eqr. easy.
        + apply beq_dec_false_iff in eqr.
          destruct (reg_neq_neq_dec reg (fst a) eqr).
          rewrite H0.
          apply IHl; intros.
          * destruct H.
            ** inv H. contradiction.
            ** easy.
          * apply H'.
            ** simpl. right. easy.
            ** simpl. right. easy.
    }
    apply (fuel_ok (fenv := fenv)) in H0.
    destruct H0.
    exists x.
    split.
    - easy.
    - eapply one_in_fv_implies_written_value.
      + apply H.
      + easy.
      + intros. symmetry. apply H'; easy.
  Qed.
End SimpleFormTactics.
