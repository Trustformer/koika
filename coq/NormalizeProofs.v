(*! Proving | Proofs about the normal form !*)
Require Import List.
Import ListNotations.
Require Import Koika.EqDec Koika.Normalize Koika.Syntax Koika.Zipper.

Section NormalizeProofs.
  Context {pos_t var_t fn_name_t reg_t ext_fn_t: Type}.
  Context {reg_t_eq_dec: EqDec reg_t}.
  Context {var_t_eq_dec: EqDec var_t}.
  Context {ext_fn_t_eq_dec: EqDec ext_fn_t}.

  Lemma map_nil_nil: forall {A B} f sm, sm = [] -> @map A B f sm = [].
  Proof. intros. induction sm; easy. Qed.
  Lemma map_nil_nil': forall {A B} f sm, @map A B f sm = [] -> sm = [].
  Proof. intros. induction sm; easy. Qed.
  Lemma app_eq_nil:
    forall {A: Type} (l l': list A), l = [] /\ l' = [] -> l ++ l' = [].
  Proof. intros. destruct H. subst. reflexivity. Qed.
  Lemma app_eq_nil':
    forall {A: Type} (l l': list A),  l ++ l' = [] -> l = [] /\ l' = [].
  Proof. intros. induction l; simpl in *; split; easy. Qed.

  Lemma to_unit_t_does_not_add_UInternalCalls:
    forall (ua: uaction pos_t var_t fn_name_t reg_t ext_fn_t),
      find_all_in_uaction
        (inline_internal_calls ua)
        (fun a =>
          match a with UInternalCall _ _ => true | _ => false end
        ) = nil
    -> find_all_in_uaction
      (inline_internal_calls (to_unit_t ua))
      (fun a =>
        match a with UInternalCall _ _ => true | _ => false end
      ) = nil.
  Proof.
    intros.
    induction ua; auto; simpl in *.
    - apply app_eq_nil' in H. destruct H. apply map_nil_nil' in H, H0.
      apply app_eq_nil. split; apply map_nil_nil;auto.
    - apply app_eq_nil' in H. destruct H.
      apply app_eq_nil' in H. destruct H.
      apply map_nil_nil' in H, H0, H1.
      apply app_eq_nil. split.
      + apply app_eq_nil. split; apply map_nil_nil; auto.
      + apply map_nil_nil. apply IHua3; auto.
    - apply map_nil_nil. apply IHua; try assumption. apply map_nil_nil' in H.
      apply H.
  Qed.
End NormalizeProofs.
