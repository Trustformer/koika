(*! Language | Semantics of untyped Kôika programs !*)
Require Import Coq.Program.Equality.
Require Export Koika.Common Koika.Environments Koika.Syntax Koika.UntypedLogs.
Require Import Desugaring SyntaxMacros UntypedSemantics.
Require Import BitsToLists.

Section Interp.
  Context {pos_t var_t fn_name_t: Type}.
  Context `{var_t_eq_dec: EqDec var_t}.

  Inductive interp_list
    {reg_t ext_fn_t: Type} {REnv: Env reg_t} (r: REnv.(env_t) (fun _ => val))
    (sigma: forall f: ext_fn_t, val -> val)
    (i: forall
      (Gamma: list (var_t * val)) (sched_log: Log REnv) (action_log: Log REnv)
      (a: Syntax.uaction pos_t var_t fn_name_t reg_t ext_fn_t)
      (action_log': Log REnv) (res: val) (Gamma': list (var_t * val)), Prop
    )
  : forall
      (Gamma: list (var_t * val)) (sched_log: Log REnv) (action_log: Log REnv)
      (a: list (Syntax.uaction pos_t var_t fn_name_t reg_t ext_fn_t))
      (action_log': Log REnv) (res: list val) (Gamma': list (var_t * val)), Prop
  :=
  | interp_list_nil:
    forall
      (Gamma: list (var_t * val)) (sched_log: Log REnv) (action_log: Log REnv),
    interp_list r sigma i Gamma sched_log action_log [] action_log [] Gamma
  | interp_list_cons:
    forall
      (Gamma: list (var_t * val)) (sched_log: Log REnv) (action_log: Log REnv)
      Gamma' action_log' Gamma'' action_log'' a ar v vr,
    i Gamma sched_log action_log a action_log' v Gamma' ->
    interp_list
      r sigma i Gamma' sched_log action_log' ar action_log'' vr Gamma''
    -> interp_list
      r sigma i Gamma sched_log action_log (a::ar) action_log'' (vr++[v])
      Gamma''.

  Lemma fold_left_rec:
    forall
      {reg_t ext_fn_t: Type} {REnv: Env reg_t}
      (f: forall (Gamma: list (var_t * val)) (sched_log: Log REnv)
      (action_log: Log REnv)
      (a: Syntax.uaction pos_t var_t fn_name_t reg_t ext_fn_t),
    option
      (Log REnv * val * list (var_t * val)))
      (sched_log: Log REnv) l X action_log Gamma,
    fold_left
      (fun acc a =>
        let/opt3 action_log, l, Gamma := acc in
        let/opt3 action_log, v, Gamma := f Gamma sched_log action_log a in
        Some (action_log, v::l, Gamma)
      )
      l (Some (action_log, X, Gamma))
    = match fold_left
      (fun acc a =>
        let/opt3 action_log, l, Gamma := acc in
        let/opt3 action_log, v, Gamma := f Gamma sched_log action_log a in
        Some (action_log, v::l, Gamma)
      )
      l (Some (action_log, [], Gamma))
    with
    | None => None
    | Some (al, l, Gamma) => Some (al, l ++ X, Gamma)
    end.
  Proof.
    induction l; simpl; intros; eauto.
    destruct (f Gamma sched_log action_log a) eqn:?; simpl; auto.
    destruct p. destruct p.
    rewrite (IHl (v::X)).
    rewrite (IHl [v]).
    destr. repeat destr. rewrite <- app_assoc. simpl. auto.
    rewrite fold_left_none. auto. simpl; auto.
  Qed.

  Lemma interp_list_ok:
    forall
      {reg_t ext_fn_t: Type} {REnv: Env reg_t} (r: REnv.(env_t) (fun _ => val))
      (sigma: forall f: ext_fn_t, val -> val)
      (i: forall
          (Gamma: list (var_t * val)) (sched_log: Log REnv)
          (action_log: Log REnv)
          (a: Syntax.uaction pos_t var_t fn_name_t reg_t ext_fn_t)
          (action_log': Log REnv) (res: val) (Gamma': list (var_t * val)),
        Prop
      )
      (f: forall
          (Gamma: list (var_t * val)) (sched_log: Log REnv)
          (action_log: Log REnv)
          (a: Syntax.uaction pos_t var_t fn_name_t reg_t ext_fn_t),
        option (Log REnv * val * list (var_t * val))
      )
      l
      (iok:
        forall Gamma sched_log action_log Gamma' action_log' a v,
        In a l
        -> f Gamma sched_log action_log a = Some (action_log', v, Gamma')
        <-> i Gamma sched_log action_log a action_log' v Gamma'
      ),
    forall Gamma action_log sched_log action_log' Gamma' lv,
      fold_left
        (fun acc a =>
          let/opt3 action_log, l, Gamma := acc in
          let/opt3 action_log, v, Gamma := f Gamma sched_log action_log a in
          Some (action_log, v::l, Gamma)
        )
        l (Some (action_log, [], Gamma))
      = Some (action_log', lv, Gamma')
      <-> interp_list
        r sigma i Gamma sched_log action_log l action_log' lv Gamma'.
  Proof.
    induction l; simpl; intros; eauto.
    - split; intro A; inv A. constructor. auto.
    - destruct (f Gamma sched_log action_log a) eqn:?; simpl; auto.
      + destruct p. destruct p.
        rewrite fold_left_rec.
        destr. destruct p, p. rewrite IHl in Heqo0.
        split; intro A; inv A.
        * econstructor. apply iok. auto. eauto. auto.
        * apply iok in H4. rewrite H4 in Heqo. inv Heqo.
          rewrite <- IHl in Heqo0.
          rewrite <- IHl in H8.
          rewrite Heqo0 in H8. inv H8. auto.
          intros; apply iok; eauto.
          intros; apply iok; eauto. auto.
        * intros; apply iok; eauto.
        * split; intros A; inv A.
          rewrite <- iok in H4.
          rewrite Heqo in H4. inv H4.
          rewrite <- IHl in H8.
          rewrite Heqo0 in H8. inv H8.
          intros; apply iok; eauto. auto.
      + rewrite fold_left_none; auto.
        split; intros A; inv A.
        rewrite <- iok in H4. congruence. auto.
  Qed.

  Inductive interp_list_ctx
    {reg_t ext_fn_t: Type} {REnv: Env reg_t} (r: REnv.(env_t) (fun _ => val))
    (sigma: forall f: ext_fn_t, val -> val)
    (i: forall
      (Gamma: list (var_t * val)) (sched_log: Log REnv) (action_log: Log REnv)
      (a: Syntax.uaction pos_t var_t fn_name_t reg_t ext_fn_t)
      (action_log': Log REnv) (res: val) (Gamma': list (var_t * val)), Prop
    )
  : forall
      (Gamma: list (var_t * val)) (sched_log: Log REnv) (action_log: Log REnv)
      (a: list (var_t * Syntax.uaction pos_t var_t fn_name_t reg_t ext_fn_t))
      (action_log': Log REnv) (Gamma': list (var_t * val)),
    Prop
  :=
  | interp_list_ctx_nil:
    forall
      (Gamma: list (var_t * val)) (sched_log: Log REnv) (action_log: Log REnv),
    interp_list_ctx r sigma i Gamma sched_log action_log [] action_log Gamma
  | interp_list_ctx_cons:
    forall
      (Gamma: list (var_t * val)) (sched_log: Log REnv) (action_log: Log REnv)
      Gamma' action_log' Gamma'' action_log'' var a ar v,
    i Gamma sched_log action_log a action_log' v Gamma'
    -> interp_list_ctx
      r sigma i ((var,v)::Gamma') sched_log action_log' ar action_log'' Gamma''
    -> interp_list_ctx
      r sigma i Gamma sched_log action_log ((var,a)::ar) action_log'' Gamma''.

  Lemma interp_list_ctx_ok:
    forall
      {reg_t ext_fn_t: Type} {REnv: Env reg_t} (r: REnv.(env_t) (fun _ => val))
      (sigma: forall f: ext_fn_t, val -> val)
      (i: forall
          (Gamma: list (var_t * val)) (sched_log: Log REnv)
          (action_log: Log REnv)
          (a: Syntax.uaction pos_t var_t fn_name_t reg_t ext_fn_t)
          (action_log': Log REnv) (res: val) (Gamma': list (var_t * val)),
        Prop
      )
      (f: forall
          (Gamma: list (var_t * val)) (sched_log: Log REnv)
          (action_log: Log REnv)
          (a: Syntax.uaction pos_t var_t fn_name_t reg_t ext_fn_t),
        option (Log REnv * val * list (var_t * val))
      )
      l
      (iok:
        forall Gamma sched_log action_log Gamma' action_log' a v,
        In a (map snd l)
        -> f Gamma sched_log action_log a = Some (action_log', v, Gamma')
        <-> i Gamma sched_log action_log a action_log' v Gamma'
      ),
    forall Gamma action_log sched_log action_log' Gamma',
    List.fold_left
      (fun acc '(var, a) =>
        let/opt2 action_log, Gamma' := acc in
        let/opt3 action_log, v, Gamma' := f Gamma' sched_log action_log a in
        (Some (action_log, (var,v)::Gamma'))
      )
      l (Some (action_log, Gamma))
    = Some (action_log', Gamma')
    <-> interp_list_ctx
      r sigma i Gamma sched_log action_log l action_log' Gamma'.
  Proof.
    induction l; simpl; intros; eauto.
    - split; intros A; inv A. constructor. auto.
    - destr.
      destruct (f Gamma sched_log action_log u) eqn:?; simpl in *; auto.
      + destruct p, p.
        split; intros A.
        * rewrite IHl in A.
          econstructor. apply iok. auto. eauto.
          auto.
          intros; eapply iok; eauto.
        * inv A. rewrite <- IHl in H8.
          rewrite <- H8. f_equal.
          apply iok in H7. rewrite H7 in Heqo. inv Heqo. auto.
          auto.
          intros; eapply iok; eauto.
      + rewrite fold_left_none; simpl; auto. 2: intros; destr; auto.
        split; intros A; inv A.
        apply iok in H7. rewrite H7 in Heqo. inv Heqo.
        auto.
  Qed.

  Lemma structinit_ind_ok:
    forall
      {reg_t ext_fn_t: Type} {REnv: Env reg_t} (r: REnv.(env_t) (fun _ => val))
      (sigma: forall f: ext_fn_t, val -> val)
      (i: forall
          (Gamma: list (var_t * val)) (sched_log: Log REnv)
          (action_log: Log REnv)
          (a: Syntax.uaction pos_t var_t fn_name_t reg_t ext_fn_t)
          (action_log': Log REnv) (res: val) (Gamma': list (var_t * val)),
        Prop
      )
      (f: forall
          (Gamma: list (var_t * val)) (sched_log: Log REnv)
          (action_log: Log REnv)
          (a: Syntax.uaction pos_t var_t fn_name_t reg_t ext_fn_t),
        option (Log REnv * val * list (var_t * val))
      )
      fields
      (iok: forall Gamma sched_log action_log Gamma' action_log' a v,
         In a (map snd fields)
         -> f Gamma sched_log action_log a = Some (action_log', v, Gamma')
         <-> i Gamma sched_log action_log a action_log' v Gamma'
      )
      sched_log Gamma Gamma' action_log action_log' vs v sig,
    (exists vfields,
      interp_list
        r sigma i Gamma sched_log action_log (map snd fields) action_log'
        vfields Gamma'
      /\ List.fold_left
        (fun vs '(name, v) =>
          let/opt vs := vs in subst_field_name (struct_fields sig) name v vs
        )
        (combine (map fst fields) (rev vfields))
        (Some vs) = Some v
    )
    <-> List.fold_left
      (fun acc '(name, a) =>
        let/opt3 action_log, vs, Gamma := acc in
        let/opt3 action_log, v, Gamma := f Gamma sched_log action_log a in
        let/opt vs := subst_field_name (struct_fields sig) name v vs in
        (Some (action_log, vs, Gamma))
      )
      fields (Some (action_log, vs, Gamma)) = Some (action_log', v, Gamma').
  Proof.
    induction fields; simpl; intros; eauto.
    - split; intros A. destruct A; intuition subst. inv H1. inv H0. auto.
      inv A. eexists; split. constructor. auto.
    - destr.
      destruct (f Gamma sched_log action_log u) eqn:?; simpl in *; auto.
      + destruct p, p.
        destruct (subst_field_name (struct_fields sig) s v0 vs) eqn:?;
        simpl in *; auto.
        * rewrite <- IHfields.
          split; intros (vfields & A & B).
          inv A.
          rewrite rev_app_distr in B. simpl in B.
          apply iok in H4. rewrite H4 in Heqo; inv Heqo.
          eexists.
          rewrite <- Heqo0. rewrite B. split; eauto. auto.
          eexists; split. econstructor. apply iok; eauto. eauto.
          rewrite rev_app_distr. simpl. rewrite Heqo0.
          rewrite B. auto.
          intros; eapply iok; auto.
        * rewrite fold_left_none; auto. 2: intros; destr; auto.
          split; intros A. 2: inv A.
          destruct A; intuition. inv H0.
          apply iok in H6. rewrite H6 in Heqo; inv Heqo.
          rewrite rev_app_distr in H1. simpl in H1. rewrite Heqo0 in H1.
          rewrite fold_left_none in H1; simpl in *; intros; try destr. easy.
          auto.
      + rewrite fold_left_none; auto. 2: intros; destr; auto.
        split; intros A. 2: inv A.
        destruct A; intuition. inv H0.
        apply iok in H6. rewrite H6 in Heqo; inv Heqo. auto.
  Qed.

  Notation "'let/opt4' v1 ',' v2 ',' v3 ',' v4 ':=' expr 'in' body" :=
    (opt_bind expr (fun '(v1, v2, v3, v4) => body)) (at level 200).

  Lemma arrayinit_ind_ok:
    forall
      {reg_t ext_fn_t: Type} {REnv: Env reg_t} (r: REnv.(env_t) (fun _ => val))
      (sigma: forall f: ext_fn_t, val -> val)
      (i: forall
          (Gamma: list (var_t * val)) (sched_log: Log REnv)
          (action_log: Log REnv)
          (a: Syntax.uaction pos_t var_t fn_name_t reg_t ext_fn_t)
          (action_log': Log REnv) (res: val) (Gamma': list (var_t * val)),
        Prop
      )
      (f: forall
          (Gamma: list (var_t * val)) (sched_log: Log REnv)
          (action_log: Log REnv)
          (a: Syntax.uaction pos_t var_t fn_name_t reg_t ext_fn_t),
        option (Log REnv * val * list (var_t * val))
      )
      elts
      (iok:
        forall Gamma sched_log action_log Gamma' action_log' a v,
        In a elts
        -> f Gamma sched_log action_log a = Some (action_log', v, Gamma')
        <-> i Gamma sched_log action_log a action_log' v Gamma'
      )
      sched_log Gamma Gamma' action_log action_log' vs v x pos,
    (exists velts,
      interp_list
        r sigma i Gamma sched_log action_log elts action_log' velts Gamma'
        /\ List.fold_left
          (fun acc v =>
            let/opt2 pos, vs := acc in
            let/opt2 l1, l2 := take_drop pos vs in
            match l2 with
            | []    => None
            | a::l2 => Some (S pos, l1 ++ v :: l2)
            end
          )
          (rev velts) (Some (pos, vs))
        = Some (x, v)
    ) <-> List.fold_left
      (fun acc a =>
        let/opt4 pos, action_log, vs, Gamma := acc in
        let/opt3 action_log, v, Gamma := f Gamma sched_log action_log a in
        let/opt2 l1, l2 := take_drop pos vs in
        match l2 with
        | []    => None
        | a::l2 => Some (S pos, action_log, l1 ++ v :: l2, Gamma)
        end
      )
      elts (Some (pos, action_log, vs, Gamma))
    = Some (x, action_log', v, Gamma').
  Proof.
    induction elts; simpl; intros; eauto.
    - split; intros A. destruct A; intuition subst. inv H0.
      simpl in H1. inv H1. auto.
      inv A. eexists; split. constructor. auto.
    - destruct (f Gamma sched_log action_log a) eqn:?; simpl in *; auto.
      + destruct p, p.
        destruct (take_drop pos vs) eqn:?; simpl. destruct p.
        destruct l2.
        * rewrite fold_left_none; simpl; auto. subst.
          split; intros A. 2: inv A.
          decompose [ex and] A. clear A.
          inv H0. rewrite rev_app_distr in H1. simpl in H1.
          rewrite Heqo0 in H1.  simpl in H1.
          rewrite fold_left_none in H1; simpl; auto. congruence.
        * rewrite <- IHelts.
          2: intros; eapply iok; eauto.
          split; intros (velts & IL & FL).
          -- inv IL.
             rewrite rev_app_distr in FL. simpl in FL.
             rewrite Heqo0 in FL. simpl in FL.
             eapply iok in H4; eauto. rewrite H4 in Heqo; inv Heqo.
             eexists; split; eauto.
          -- eexists; split.
             econstructor. eapply iok; eauto. eauto.
             rewrite rev_app_distr. simpl.
             rewrite Heqo0; simpl. eauto.
        * rewrite fold_left_none; auto.
          split; intros A. 2: inv A.
          destruct A; intuition. inv H0.
          apply iok in H6. rewrite H6 in Heqo; inv Heqo.
          rewrite rev_app_distr in H1. simpl in H1. rewrite Heqo0 in H1.
          simpl in H1. rewrite fold_left_none in H1; simpl in *;
          intros; try destr. easy.
          auto. auto.
      + rewrite fold_left_none; auto.
        split; intros A. 2: inv A.
        destruct A; intuition. inv H0.
        apply iok in H6. rewrite H6 in Heqo; inv Heqo. auto.
  Qed.

  Inductive interp_action:
    forall
      {reg_t ext_fn_t: Type} `{REnv: Env reg_t} (r: REnv.(env_t) (fun _ => val))
      (sigma: forall f: ext_fn_t, val -> val) (Gamma: list (var_t * val))
      (sched_log: Log REnv) (action_log: Log REnv)
      (a: Syntax.uaction pos_t var_t fn_name_t reg_t ext_fn_t)
      (action_log': Log REnv) (res: val) (Gamma': list (var_t * val)),
    Prop
  :=
  | interp_action_var:
    forall
      {reg_t ext_fn_t: Type} `{REnv: Env reg_t} (r: REnv.(env_t) (fun _ => val))
      (sigma: forall f: ext_fn_t, val -> val) (Gamma: list (var_t * val))
      (sched_log: Log REnv) (action_log: Log REnv) var v,
    list_assoc Gamma var = Some v
    -> interp_action
      r sigma Gamma sched_log action_log (UVar var) action_log v Gamma
  | interp_action_const:
    forall
      {reg_t ext_fn_t: Type} {REnv: Env reg_t} (r: REnv.(env_t) (fun _ => val))
      (sigma: forall f: ext_fn_t, val -> val) (Gamma: list (var_t * val))
      (sched_log: Log REnv) (action_log: Log REnv) tau (cst: type_denote tau),
    interp_action
      r sigma Gamma sched_log action_log (UConst cst) action_log
      (val_of_value cst) Gamma
  | interp_action_assign:
    forall
      {reg_t ext_fn_t: Type} {REnv: Env reg_t} (r: REnv.(env_t) (fun _ => val))
      (sigma: forall f: ext_fn_t, val -> val) (Gamma: list (var_t * val))
      (sched_log: Log REnv) (action_log: Log REnv) k a action_log' Gamma' v,
    interp_action r sigma Gamma sched_log action_log a action_log' v Gamma'
    -> interp_action
      r sigma Gamma sched_log action_log (UAssign k a) action_log' (Bits [])
      (list_assoc_set Gamma' k v)
  | interp_action_seq:
    forall
      {reg_t ext_fn_t: Type} {REnv: Env reg_t} (r: REnv.(env_t) (fun _ => val))
      (sigma: forall f: ext_fn_t, val -> val) (Gamma: list (var_t * val))
      (sched_log: Log REnv) (action_log: Log REnv) a1 a2 v1 v2 action_log'
      Gamma' action_log'' Gamma'',
    interp_action r sigma Gamma sched_log action_log a1 action_log' v1 Gamma'
    -> interp_action
      r sigma Gamma' sched_log action_log' a2 action_log'' v2 Gamma''
    -> interp_action
      r sigma Gamma sched_log action_log (USeq a1 a2) action_log'' v2 Gamma''
  | interp_action_bind:
    forall
      {reg_t ext_fn_t: Type} {REnv: Env reg_t} (r: REnv.(env_t) (fun _ => val))
      (sigma: forall f: ext_fn_t, val -> val) (Gamma: list (var_t * val))
      (sched_log: Log REnv) (action_log: Log REnv) k a1 a2 v1 v2 action_log'
      Gamma' action_log'' Gamma'',
    interp_action r sigma Gamma sched_log action_log a1 action_log' v1 Gamma'
    -> interp_action
      r sigma ((k,v1)::Gamma') sched_log action_log' a2 action_log'' v2 Gamma''
    -> interp_action r sigma Gamma sched_log action_log (UBind k a1 a2)
      action_log'' v2 (tl Gamma'')
  | interp_action_if:
    forall
      {reg_t ext_fn_t: Type} {REnv: Env reg_t} (r: REnv.(env_t) (fun _ => val))
      (sigma: forall f: ext_fn_t, val -> val) (Gamma: list (var_t * val))
      (sched_log: Log REnv) (action_log: Log REnv) cond b athen aelse v2
      action_log' Gamma' action_log'' Gamma'',
    interp_action
      r sigma Gamma sched_log action_log cond action_log' (Bits [b]) Gamma'
    -> interp_action
      r sigma Gamma' sched_log action_log' (if b then athen else aelse)
      action_log'' v2 Gamma''
    -> interp_action
      r sigma Gamma sched_log action_log (UIf cond athen aelse) action_log'' v2
      Gamma''
  | interp_action_read:
    forall
      {reg_t ext_fn_t: Type} {REnv: Env reg_t} (r: REnv.(env_t) (fun _ => val))
      (sigma: forall f: ext_fn_t, val -> val) (Gamma: list (var_t * val))
      (sched_log: Log REnv) (action_log: Log REnv) prt idx,
    may_read sched_log prt idx = true
    -> interp_action
      r sigma Gamma sched_log action_log (URead prt idx)
      (log_cons idx (LE Logs.LogRead prt (Bits [])) action_log)
      (match prt with
        | P0 => REnv.(getenv) r idx
        | P1 =>
          match latest_write0 (V:=val) (log_app action_log sched_log) idx with
          | Some v => v
          | None => REnv.(getenv) r idx
          end
        end
      )
      Gamma
  | interp_action_write:
    forall
      {reg_t ext_fn_t: Type} {REnv: Env reg_t} (r: REnv.(env_t) (fun _ => val))
      (sigma: forall f: ext_fn_t, val -> val) (Gamma: list (var_t * val))
      (sched_log: Log REnv) (action_log: Log REnv) prt idx a v action_log'
      Gamma',
    interp_action r sigma Gamma sched_log action_log a action_log' v Gamma'
    -> may_write sched_log action_log' prt idx = true
    -> interp_action
      r sigma Gamma sched_log action_log (UWrite prt idx a)
      (log_cons idx (LE Logs.LogWrite prt v) action_log') (Bits []) Gamma'
  | interp_action_unop:
    forall
      {reg_t ext_fn_t: Type} {REnv: Env reg_t} (r: REnv.(env_t) (fun _ => val))
      (sigma: forall f: ext_fn_t, val -> val) (Gamma: list (var_t * val))
      (sched_log: Log REnv) (action_log: Log REnv) fn a v v' action_log' Gamma',
    interp_action r sigma Gamma sched_log action_log a action_log' v Gamma'
    -> sigma1 fn v = Some v'
    -> interp_action
      r sigma Gamma sched_log action_log (UUnop fn a) action_log' v' Gamma'
  | interp_action_binop:
    forall
      {reg_t ext_fn_t: Type} {REnv: Env reg_t} (r: REnv.(env_t) (fun _ => val))
      (sigma: forall f: ext_fn_t, val -> val) (Gamma: list (var_t * val))
      (sched_log: Log REnv) (action_log: Log REnv) fn a1 a2 v1 v2 v' action_log'
      Gamma' action_log'' Gamma'',
    interp_action r sigma Gamma sched_log action_log a1 action_log' v1 Gamma'
    -> interp_action
      r sigma Gamma' sched_log action_log' a2 action_log'' v2 Gamma''
    -> sigma2 fn v1 v2 = Some v'
    -> interp_action
      r sigma Gamma sched_log action_log (UBinop fn a1 a2) action_log'' v'
      Gamma''
  | interp_action_extcall:
    forall
      {reg_t ext_fn_t: Type} {REnv: Env reg_t} (r: REnv.(env_t) (fun _ => val))
      (sigma: forall f: ext_fn_t, val -> val) (Gamma: list (var_t * val))
      (sched_log: Log REnv) (action_log: Log REnv) fn a v action_log' Gamma',
    interp_action r sigma Gamma sched_log action_log a action_log' v Gamma'
    -> interp_action
      r sigma Gamma sched_log action_log (UExternalCall fn a) action_log'
      (sigma fn v) Gamma'
  | interp_action_intcall:
    forall
      {reg_t ext_fn_t: Type} {REnv: Env reg_t} (r: REnv.(env_t) (fun _ => val))
      (sigma: forall f: ext_fn_t, val -> val) (Gamma: list (var_t * val))
      (sched_log: Log REnv) (action_log: Log REnv) f args lv v action_log'
      Gamma' action_log'' Gamma'',
    interp_list
      r sigma (interp_action r sigma) Gamma sched_log action_log args
      action_log' lv Gamma'
    -> interp_action
      r sigma (map (fun '(name, _, v) => (name, v))
      (combine (rev (int_argspec f)) lv)) sched_log action_log' (int_body f)
      action_log'' v Gamma''
    -> interp_action
      r sigma Gamma sched_log action_log (UInternalCall f args) action_log'' v
      Gamma'
  | interp_action_pos:
    forall
      {reg_t ext_fn_t: Type} {REnv: Env reg_t} (r: REnv.(env_t) (fun _ => val))
      (sigma: forall f: ext_fn_t, val -> val) (Gamma: list (var_t * val))
      (sched_log: Log REnv) (action_log: Log REnv) p a v Gamma' action_log',
    interp_action r sigma Gamma sched_log action_log a action_log' v Gamma'
    -> interp_action
      r sigma Gamma sched_log action_log (UAPos p a) action_log' v Gamma'
  | interp_action_skip:
    forall
      {reg_t ext_fn_t: Type} {REnv: Env reg_t} (r: REnv.(env_t) (fun _ => val))
      (sigma: forall f: ext_fn_t, val -> val) (Gamma: list (var_t * val))
      (sched_log: Log REnv) (action_log: Log REnv),
      interp_action
        r sigma Gamma sched_log action_log (USugar USkip) action_log
        (Bits []) Gamma
  | interp_action_constbits:
    forall
      {reg_t ext_fn_t: Type} {REnv: Env reg_t} (r: REnv.(env_t) (fun _ => val))
      (sigma: forall f: ext_fn_t, val -> val) (Gamma: list (var_t * val))
      (sched_log: Log REnv) (action_log: Log REnv) n (v: bits n),
    let l := vect_to_list v in
    interp_action
      r sigma Gamma sched_log action_log (USugar (UConstBits v)) action_log
      (Bits l) Gamma
  | interp_action_conststring:
    forall
      {reg_t ext_fn_t: Type} {REnv: Env reg_t} (r: REnv.(env_t) (fun _ => val))
      (sigma: forall f: ext_fn_t, val -> val) (Gamma: list (var_t * val))
      (sched_log: Log REnv) (action_log: Log REnv) s,
    interp_action
      r sigma Gamma sched_log action_log (USugar (UConstString s)) action_log
      (Array
        {| array_type := bits_t 8; array_len := String.length s |}
        (List.map
          (fun x => Bits (vect_to_list x))
          (vect_to_list (SyntaxMacros.array_of_bytes s))
        )
      )
      Gamma
  | interp_action_constenum:
    forall
      {reg_t ext_fn_t: Type} {REnv: Env reg_t} (r: REnv.(env_t) (fun _ => val))
      (sigma: forall f: ext_fn_t, val -> val) (Gamma: list (var_t * val))
      (sched_log: Log REnv) (action_log: Log REnv) sig name idx,
    vect_index name sig.(enum_members) = Some idx
    -> interp_action
      r sigma Gamma sched_log action_log (USugar (UConstEnum sig name))
      action_log
      (val_of_value (tau:= enum_t sig) (vect_nth sig.(enum_bitpatterns) idx))
      Gamma
  | interp_action_progn:
    forall
      {reg_t ext_fn_t: Type} {REnv: Env reg_t} (r: REnv.(env_t) (fun _ => val))
      (sigma: forall f: ext_fn_t, val -> val) (Gamma: list (var_t * val))
      (sched_log: Log REnv) (action_log: Log REnv) aa Gamma' action_log' lv,
    interp_list
      r sigma (interp_action r sigma) Gamma sched_log action_log aa action_log'
      lv Gamma'
    -> interp_action
      r sigma Gamma sched_log action_log (USugar (UProgn aa)) action_log'
      (List.hd (Bits []) lv) Gamma'
  | interp_action_let:
    forall
      {reg_t ext_fn_t: Type} {REnv: Env reg_t} (r: REnv.(env_t) (fun _ => val))
      (sigma: forall f: ext_fn_t, val -> val) (Gamma: list (var_t * val))
      (sched_log: Log REnv) (action_log: Log REnv) bindings body action_log'
      action_log'' Gamma' Gamma'' v,
    interp_list_ctx
      r sigma (interp_action r sigma) Gamma sched_log action_log bindings
      action_log' Gamma'
    -> interp_action
      r sigma Gamma' sched_log action_log' body action_log'' v Gamma''
    -> interp_action
      r sigma Gamma sched_log action_log (USugar (ULet bindings body))
      action_log'' v (Nat.iter (List.length bindings) (@tl _) Gamma'')
  | interp_action_when:
    forall
      {reg_t ext_fn_t: Type} {REnv: Env reg_t} (r: REnv.(env_t) (fun _ => val))
      (sigma: forall f: ext_fn_t, val -> val) (Gamma: list (var_t * val))
      (sched_log: Log REnv) (action_log: Log REnv) cond athen v2 action_log'
      Gamma' action_log'' Gamma'',
    interp_action
      r sigma Gamma sched_log action_log cond action_log' (Bits [true]) Gamma'
    -> interp_action
      r sigma Gamma' sched_log action_log' athen action_log'' v2 Gamma''
    -> interp_action
      r sigma Gamma sched_log action_log (USugar (UWhen cond athen))
      action_log'' v2 Gamma''
  | interp_action_switch_nil:
    forall
      {reg_t ext_fn_t: Type} {REnv: Env reg_t} (r: REnv.(env_t) (fun _ => val))
      (sigma: forall f: ext_fn_t, val -> val) (Gamma: list (var_t * val))
      (sched_log: Log REnv) (action_log: Log REnv) var default v action_log'
      Gamma',
    interp_action
      r sigma Gamma sched_log action_log default action_log' v Gamma'
    -> interp_action
      r sigma Gamma sched_log action_log (USugar (USwitch var default []))
      action_log' v Gamma'
  | interp_action_switch_ok:
    forall
      {reg_t ext_fn_t: Type} {REnv: Env reg_t} (r: REnv.(env_t) (fun _ => val))
      (sigma: forall f: ext_fn_t, val -> val) (Gamma: list (var_t * val))
      (sched_log: Log REnv) (action_log: Log REnv) var default cond body
      branches action_log' Gamma' action_log'' Gamma'' action_log''' Gamma''' v0
      v v2,
    interp_action r sigma Gamma sched_log action_log var action_log' v0 Gamma'
    -> interp_action
      r sigma Gamma' sched_log action_log' cond action_log'' v Gamma''
    -> v = v0
    -> interp_action
      r sigma Gamma'' sched_log action_log'' body action_log''' v2 Gamma'''
    -> interp_action
      r sigma Gamma sched_log action_log
      (USugar (USwitch var default ((cond,body)::branches))) action_log''' v2
      Gamma'''
  | interp_action_switch_ko:
    forall
      {reg_t ext_fn_t: Type} {REnv: Env reg_t} (r: REnv.(env_t) (fun _ => val))
      (sigma: forall f: ext_fn_t, val -> val) (Gamma: list (var_t * val))
      (sched_log: Log REnv) (action_log: Log REnv) var default cond body
      branches action_log' Gamma' action_log'' Gamma'' action_log''' Gamma''' v0
      v v2,
    interp_action r sigma Gamma sched_log action_log var action_log' v0 Gamma'
    -> interp_action
      r sigma Gamma' sched_log action_log' cond action_log'' v Gamma''
    -> v <> v0 ->
      interp_action
        r sigma Gamma'' sched_log action_log''
        (USugar (USwitch var default branches)) action_log''' v2 Gamma'''
    -> interp_action
      r sigma Gamma sched_log action_log
      (USugar (USwitch var default ((cond,body)::branches))) action_log''' v2
      Gamma'''
  | interp_action_structinit:
    forall
      {reg_t ext_fn_t: Type} {REnv: Env reg_t} (r: REnv.(env_t) (fun _ => val))
      (sigma: forall f: ext_fn_t, val -> val) (Gamma: list (var_t * val))
      (sched_log: Log REnv) (action_log: Log REnv) sig fields vfields
      action_log' Gamma' vs v,
    interp_list
      r sigma (interp_action r sigma) Gamma sched_log action_log
      (map snd fields) action_log' vfields Gamma'
    -> let zeroes := repeat false (struct_fields_sz (struct_fields sig)) in
    uvalue_of_struct_bits (struct_fields sig) zeroes = Some vs
    -> List.fold_left
      (fun vs '(name, v) =>
        let/opt vs := vs in
        subst_field_name (struct_fields sig) name v vs
      )
      (combine (map fst fields) (rev vfields)) (Some vs)
    = Some v
    -> interp_action
      r sigma Gamma sched_log action_log (USugar (UStructInit sig fields))
      action_log' (Struct sig v) Gamma'
  | interp_action_arrayinit:
    forall
      {reg_t ext_fn_t: Type} {REnv: Env reg_t} (r: REnv.(env_t) (fun _ => val))
      (sigma: forall f: ext_fn_t, val -> val) (Gamma: list (var_t * val))
      (sched_log: Log REnv) (action_log: Log REnv) tau elements velts
      action_log' Gamma' vs v,
    interp_list
      r sigma (interp_action r sigma) Gamma sched_log action_log elements
      action_log' velts Gamma'
    ->
    let zeroes := repeat (repeat false (type_sz tau)) (List.length elements)
    in uvalue_of_list_bits (tau:=tau) zeroes = Some vs
    -> let sig := {| array_type := tau; array_len := List.length elements |}
    in List.fold_left
      (fun acc v =>
        let/opt2 pos, vs := acc in
        let/opt2 l1, l2 := take_drop pos vs in
        match l2 with
        | [] => None
        | a::l2 => Some (S pos, l1 ++ v :: l2)
        end
      )
      (rev velts) (Some (0, vs))
    = Some v
    -> interp_action
      r sigma Gamma sched_log action_log (USugar (UArrayInit tau elements))
      action_log' (Array sig (snd v)) Gamma'
  | interp_action_callmodule:
    forall
      {reg_t ext_fn_t: Type} {REnv: Env reg_t} (r: REnv.(env_t) (fun _ => val))
      (sigma: forall f: ext_fn_t, val -> val) (Gamma: list (var_t * val))
      (sched_log: Log REnv) (action_log: Log REnv) module_reg_t module_ext_fn_t
      `{finite: FiniteType module_reg_t} (fR: module_reg_t -> reg_t)
      (fSigma : module_ext_fn_t -> ext_fn_t) fn args lv v action_log' Gamma'
      action_log'' Gamma'',
    interp_list
      r sigma (interp_action r sigma) Gamma sched_log action_log args
      action_log' lv Gamma'
    -> let REnv' := @ContextEnv _ _
    in interp_action
      (create REnv' (fun idx => getenv REnv r (fR idx)))
      (fun f => sigma (fSigma f))
      (map (fun '(name, _, v) => (name, v)) (combine (rev (int_argspec fn)) lv))
      (fLog fR REnv REnv' sched_log) (fLog fR REnv REnv' action_log')
      (int_body fn) action_log'' v Gamma''
    -> interp_action
      r sigma Gamma sched_log action_log
      (USugar (UCallModule fR fSigma fn args))
      (fLog' fR REnv REnv' action_log'' action_log') v Gamma'.

  Lemma invert_var:
    forall
      {reg_t ext_fn_t: Type} {REnv: Env reg_t}
      (r: env_t REnv (fun _: reg_t => BitsToLists.val))
      (sigma: ext_fn_t -> BitsToLists.val -> BitsToLists.val)
      (Gamma Gamma': list (var_t * BitsToLists.val))
      (sched_log action_log action_log': Log REnv) var v,
    interp_action r sigma Gamma sched_log action_log (UVar var) action_log' v
      Gamma'
    -> action_log = action_log' /\ Gamma = Gamma'
    /\ list_assoc Gamma var = Some v.
  Proof.
    intros.
    dependent destruction H.
    repeat split.
    assumption.
  Qed.

  Lemma invert_const:
    forall
      {reg_t ext_fn_t: Type} {REnv: Env reg_t}
      (r: env_t REnv (fun _: reg_t => BitsToLists.val))
      (sigma: ext_fn_t -> BitsToLists.val -> BitsToLists.val)
      (Gamma Gamma': list (var_t * BitsToLists.val))
      (sched_log action_log action_log': Log REnv) tau (cst: type_denote tau) v,
    interp_action r sigma Gamma sched_log action_log (UConst cst) action_log' v
      Gamma'
    -> v = val_of_value cst /\ action_log = action_log' /\ Gamma = Gamma'.
  Proof.
    intros.
    dependent destruction H.
    repeat split.
  Qed.

  Lemma invert_assign:
    forall
      {reg_t ext_fn_t: Type} {REnv: Env reg_t}
      (r: env_t REnv (fun _: reg_t => BitsToLists.val))
      (sigma: ext_fn_t -> BitsToLists.val -> BitsToLists.val)
      (Gamma Gamma': list (var_t * BitsToLists.val))
      (sched_log action_log action_log': Log REnv) k a v,
    interp_action r sigma Gamma sched_log action_log (UAssign k a) action_log'
      v Gamma'
    -> exists v_init Gamma_init,
    v = Bits [] /\ Gamma' = list_assoc_set Gamma_init k v_init
    /\ interp_action r sigma Gamma sched_log action_log a action_log' v_init
      Gamma_init.
  Proof.
    intros.
    dependent destruction H.
    exists v. exists Gamma'.
    repeat split.
    assumption.
  Qed.

  Lemma invert_seq:
    forall
      {reg_t ext_fn_t: Type} {REnv: Env reg_t}
      (r: env_t REnv (fun _: reg_t => BitsToLists.val))
      (sigma: ext_fn_t -> BitsToLists.val -> BitsToLists.val)
      (Gamma Gamma': list (var_t * BitsToLists.val))
      (sched_log action_log action_log': Log REnv) a1 a2 v,
    interp_action r sigma Gamma sched_log action_log (USeq a1 a2) action_log' v
      Gamma'
    -> exists v1 v2 Gamma1 Gamma2 action_log1 action_log2,
    v = v2 /\ action_log' = action_log2 /\ Gamma' = Gamma2
    /\ interp_action r sigma Gamma sched_log action_log a1 action_log1 v1 Gamma1
    /\ interp_action r sigma Gamma1 sched_log action_log1 a2 action_log2 v2
      Gamma2.
  Proof.
    intros.
    dependent destruction H.
    exists v1. exists v2. exists Gamma'. exists Gamma''.
    exists action_log'. exists action_log''.
    repeat split; assumption.
  Qed.

  Lemma invert_bind:
    forall
      {reg_t ext_fn_t: Type} {REnv: Env reg_t}
      (r: env_t REnv (fun _: reg_t => BitsToLists.val))
      (sigma: ext_fn_t -> BitsToLists.val -> BitsToLists.val)
      (Gamma Gamma': list (var_t * BitsToLists.val))
      (sched_log action_log action_log': Log REnv) k a1 a2 v,
    interp_action r sigma Gamma sched_log action_log (UBind k a1 a2) action_log'
      v Gamma'
    -> exists v1 v2 Gamma1 Gamma2 action_log1 action_log2,
    v = v2 /\ action_log' = action_log2 /\ Gamma' = tl Gamma2
    /\ interp_action r sigma Gamma sched_log action_log a1 action_log1 v1 Gamma1
    /\ interp_action r sigma ((k, v1)::Gamma1) sched_log action_log1 a2
      action_log2 v2 Gamma2.
  Proof.
    intros.
    dependent destruction H.
    exists v1. exists v2. exists Gamma'. exists Gamma''.
    exists action_log'. exists action_log''.
    repeat split; assumption.
  Qed.

  Lemma invert_if:
    forall
      {reg_t ext_fn_t: Type} {REnv: Env reg_t}
      (r: env_t REnv (fun _: reg_t => BitsToLists.val))
      (sigma: ext_fn_t -> BitsToLists.val -> BitsToLists.val)
      (Gamma Gamma': list (var_t * BitsToLists.val))
      (sched_log action_log action_log': Log REnv) cond athen aelse v,
    interp_action r sigma Gamma sched_log action_log (UIf cond athen aelse)
      action_log' v Gamma'
    -> exists v2 b Gamma1 Gamma2 action_log1 action_log2,
    v = v2 /\ action_log' = action_log2 /\ Gamma' = Gamma2
    /\ interp_action r sigma Gamma sched_log action_log cond action_log1
      (Bits [b]) Gamma1
    /\ interp_action r sigma Gamma1 sched_log action_log1
      (if b then athen else aelse) action_log2 v2 Gamma2.
  Proof.
    intros.
    dependent destruction H.
    exists v2. exists b. exists Gamma'. exists Gamma''.
    exists action_log'. exists action_log''.
    repeat split; assumption.
  Qed.

  Lemma invert_read:
    forall
      {reg_t ext_fn_t: Type} {REnv: Env reg_t}
      (r: env_t REnv (fun _: reg_t => BitsToLists.val))
      (sigma: ext_fn_t -> BitsToLists.val -> BitsToLists.val)
      (Gamma: list (var_t * BitsToLists.val)) (sched_log action_log: Log REnv)
      (prt: Port) (idx: reg_t) (v: BitsToLists.val) (action_log': Log REnv)
      (Gamma': list (var_t * BitsToLists.val)),
    interp_action r sigma Gamma sched_log action_log (URead prt idx) action_log'
      v Gamma'
    -> may_read sched_log prt idx = true /\ Gamma' = Gamma
    /\ action_log' = log_cons idx (LE Logs.LogRead prt (Bits [])) action_log
    /\ v = (match prt with
      | P0 => REnv.(getenv) r idx
      | P1 =>
        match
          latest_write0 (V := BitsToLists.val) (log_app action_log sched_log)
            idx
        with
        | Some v => v
        | None => REnv.(getenv) r idx
        end
      end
    ).
  Proof.
    intros.
    dependent destruction H.
    repeat split; assumption.
  Qed.

  Lemma invert_write:
    forall
      {reg_t ext_fn_t: Type} {REnv: Env reg_t}
      (r: env_t REnv (fun _: reg_t => BitsToLists.val))
      (sigma: ext_fn_t -> BitsToLists.val -> BitsToLists.val)
      (Gamma: list (var_t * BitsToLists.val))
      (sched_log action_log: Log REnv) (prt: Port)
      (idx: reg_t) (a: uaction pos_t var_t fn_name_t reg_t ext_fn_t)
      (v_after: BitsToLists.val) (action_log': Log REnv)
      (Gamma': list (var_t * BitsToLists.val)),
    interp_action r sigma Gamma sched_log action_log (UWrite prt idx a)
      action_log' v_after Gamma'
    -> exists v_init action_log_init,
    v_after = Bits []
    /\ action_log' = log_cons idx (LE Logs.LogWrite prt v_init) action_log_init
    /\ may_write sched_log action_log_init prt idx = true
    /\ interp_action r sigma Gamma sched_log action_log a action_log_init
      v_init Gamma'.
  Proof.
    intros.
    dependent destruction H.
    exists v. exists action_log'.
    repeat split; assumption.
  Qed.

  Lemma invert_unop:
    forall
      {reg_t ext_fn_t: Type} {REnv: Env reg_t}
      (r: env_t REnv (fun _: reg_t => BitsToLists.val))
      (sigma: ext_fn_t -> BitsToLists.val -> BitsToLists.val)
      (Gamma Gamma': list (var_t * BitsToLists.val))
      (sched_log action_log action_log': Log REnv) fn a v,
    interp_action r sigma Gamma sched_log action_log (UUnop fn a) action_log' v
      Gamma'
    -> exists v_init,
    sigma1 fn v_init = Some v
    /\ interp_action r sigma Gamma sched_log action_log a action_log' v_init
      Gamma'.
  Proof.
    intros.
    dependent destruction H.
    exists v.
    repeat split; assumption.
  Qed.

  Lemma invert_binop:
    forall
      {reg_t ext_fn_t: Type} {REnv: Env reg_t}
      (r: env_t REnv (fun _: reg_t => BitsToLists.val))
      (sigma: ext_fn_t -> BitsToLists.val -> BitsToLists.val)
      (Gamma Gamma': list (var_t * BitsToLists.val))
      (sched_log action_log action_log': Log REnv) fn a1 a2 v,
    interp_action r sigma Gamma sched_log action_log (UBinop fn a1 a2)
      action_log' v Gamma'
    -> exists Gamma1 Gamma2 action_log1 action_log2 v1 v2,
    sigma2 fn v1 v2 = Some v /\ Gamma' = Gamma2 /\ action_log' = action_log2
    /\ interp_action r sigma Gamma sched_log action_log a1 action_log1 v1 Gamma1
    /\ interp_action r sigma Gamma1 sched_log action_log1 a2 action_log2 v2
      Gamma2.
  Proof.
    intros.
    dependent destruction H.
    exists Gamma'. exists Gamma''. exists action_log'. exists action_log''.
    exists v1. exists v2.
    repeat split; assumption.
  Qed.

  Lemma invert_extcall:
    forall
      {reg_t ext_fn_t: Type} {REnv: Env reg_t}
      (r: env_t REnv (fun _: reg_t => BitsToLists.val))
      (sigma: ext_fn_t -> BitsToLists.val -> BitsToLists.val)
      (Gamma Gamma': list (var_t * BitsToLists.val))
      (sched_log action_log action_log': Log REnv) fn a v,
    interp_action r sigma Gamma sched_log action_log (UExternalCall fn a)
      action_log' v Gamma'
    -> exists v_init,
    v = sigma fn v_init
    /\ interp_action r sigma Gamma sched_log action_log a action_log' v_init
      Gamma'.
  Proof.
    intros.
    dependent destruction H.
    exists v.
    repeat split; assumption.
  Qed.

  Lemma invert_intcall:
    forall
      {reg_t ext_fn_t: Type} {REnv: Env reg_t}
      (r: env_t REnv (fun _: reg_t => BitsToLists.val))
      (sigma: ext_fn_t -> BitsToLists.val -> BitsToLists.val)
      (Gamma Gamma': list (var_t * BitsToLists.val))
      (sched_log action_log action_log': Log REnv) f args v,
    interp_action r sigma Gamma sched_log action_log (UInternalCall f args)
      action_log' v Gamma'
    -> exists action_log1 lv Gamma2,
    interp_list r sigma (interp_action r sigma) Gamma sched_log action_log args
      action_log1 lv Gamma'
    /\ interp_action r sigma
      (map (fun '(name, _, v) => (name, v)) (combine (rev (int_argspec f)) lv))
      sched_log action_log1 (int_body f) action_log' v Gamma2.
  Proof.
    intros.
    dependent destruction H.
    exists action_log'. exists lv. exists Gamma''.
    repeat split; assumption.
  Qed.

  Lemma invert_pos:
    forall
      {reg_t ext_fn_t: Type} {REnv: Env reg_t}
      (r: env_t REnv (fun _: reg_t => BitsToLists.val))
      (sigma: ext_fn_t -> BitsToLists.val -> BitsToLists.val)
      (Gamma Gamma': list (var_t * BitsToLists.val))
      (sched_log action_log action_log': Log REnv) p a v,
    interp_action r sigma Gamma sched_log action_log (UAPos p a) action_log' v
      Gamma'
    -> interp_action r sigma Gamma sched_log action_log a action_log' v Gamma'.
  Proof.
    intros.
    dependent destruction H.
    assumption.
  Qed.

  Lemma invert_skip:
    forall
      {reg_t ext_fn_t: Type} {REnv: Env reg_t}
      (r: env_t REnv (fun _: reg_t => BitsToLists.val))
      (sigma: ext_fn_t -> BitsToLists.val -> BitsToLists.val)
      (Gamma Gamma': list (var_t * BitsToLists.val))
      (sched_log action_log action_log': Log REnv) v,
    interp_action r sigma Gamma sched_log action_log (USugar USkip) action_log'
      v Gamma'
    -> Gamma = Gamma' /\ action_log = action_log' /\ v = Bits [].
  Proof.
    intros.
    dependent destruction H.
    repeat split.
  Qed.

  Lemma invert_constbits:
    forall
      {reg_t ext_fn_t: Type} {REnv: Env reg_t}
      (r: env_t REnv (fun _: reg_t => BitsToLists.val))
      (sigma: ext_fn_t -> BitsToLists.val -> BitsToLists.val)
      (Gamma Gamma': list (var_t * BitsToLists.val))
      (sched_log action_log action_log': Log REnv) {n} (b: bits n) v,
    interp_action r sigma Gamma sched_log action_log (USugar (UConstBits b))
      action_log' v Gamma'
    -> let l := vect_to_list b in
    Gamma = Gamma' /\ action_log = action_log' /\ v = Bits l.
  Proof.
    intros.
    dependent destruction H.
    repeat split.
  Qed.

  Lemma invert_conststring:
    forall
      {reg_t ext_fn_t: Type} {REnv: Env reg_t}
      (r: env_t REnv (fun _: reg_t => BitsToLists.val))
      (sigma: ext_fn_t -> BitsToLists.val -> BitsToLists.val)
      (Gamma Gamma': list (var_t * BitsToLists.val))
      (sched_log action_log action_log': Log REnv) s v,
      interp_action r sigma Gamma sched_log action_log (USugar (UConstString s))
        action_log' v Gamma'
    -> action_log' = action_log /\ Gamma' = Gamma
    /\ v = (Array
        {| array_type := bits_t 8; array_len := String.length s |}
        (List.map
          (fun x => Bits (vect_to_list x))
          (vect_to_list (SyntaxMacros.array_of_bytes s))
        )
      ).
  Proof.
    intros.
    dependent destruction H.
    repeat split.
  Qed.

  Lemma invert_constenum:
    forall
      {reg_t ext_fn_t: Type} {REnv: Env reg_t}
      (r: env_t REnv (fun _: reg_t => BitsToLists.val))
      (sigma: ext_fn_t -> BitsToLists.val -> BitsToLists.val)
      (Gamma Gamma': list (var_t * BitsToLists.val))
      (sched_log action_log action_log': Log REnv) sig name v,
      interp_action r sigma Gamma sched_log action_log
        (USugar (UConstEnum sig name)) action_log' v Gamma'
    -> exists idx,
    Gamma' = Gamma /\ action_log' = action_log
    /\ v = val_of_value (tau:= enum_t sig) (
      vect_nth sig.(enum_bitpatterns) idx
    ).
  Proof.
    intros.
    dependent destruction H.
    exists idx.
    repeat split.
  Qed.

  Lemma invert_progn:
    forall
      {reg_t ext_fn_t: Type} {REnv: Env reg_t}
      (r: env_t REnv (fun _: reg_t => BitsToLists.val))
      (sigma: ext_fn_t -> BitsToLists.val -> BitsToLists.val)
      (Gamma Gamma': list (var_t * BitsToLists.val))
      (sched_log action_log action_log': Log REnv) aa v,
    interp_action r sigma Gamma sched_log action_log (USugar (UProgn aa))
      action_log' v Gamma'
    -> exists lv,
    v = List.hd (Bits []) lv
    /\ interp_list r sigma (interp_action r sigma) Gamma sched_log action_log aa
      action_log' lv Gamma'.
  Proof.
    intros.
    dependent destruction H.
    exists lv.
    repeat split.
    assumption.
  Qed.

  Lemma invert_let:
    forall
      {reg_t ext_fn_t: Type} {REnv: Env reg_t}
      (r: env_t REnv (fun _: reg_t => BitsToLists.val))
      (sigma: ext_fn_t -> BitsToLists.val -> BitsToLists.val)
      (Gamma Gamma': list (var_t * BitsToLists.val))
      (sched_log action_log action_log': Log REnv) bindings body v,
    interp_action r sigma Gamma sched_log action_log
      (USugar (ULet bindings body)) action_log' v Gamma'
    -> exists Gamma1 Gamma2 action_log1,
    Gamma' = Nat.iter (List.length bindings) (@tl _) Gamma2
    /\ interp_list_ctx r sigma (interp_action r sigma) Gamma sched_log
      action_log bindings action_log1 Gamma1
    /\ interp_action r sigma Gamma1 sched_log action_log1 body action_log' v
      Gamma2.
  Proof.
    intros.
    dependent destruction H.
    exists Gamma'. exists Gamma''. exists action_log'.
    repeat split; assumption.
  Qed.

  Lemma invert_when:
    forall
      {reg_t ext_fn_t: Type} {REnv: Env reg_t}
      (r: env_t REnv (fun _: reg_t => BitsToLists.val))
      (sigma: ext_fn_t -> BitsToLists.val -> BitsToLists.val)
      (Gamma Gamma': list (var_t * BitsToLists.val))
      (sched_log action_log action_log': Log REnv) cond athen v,
    interp_action r sigma Gamma sched_log action_log (USugar (UWhen cond athen))
      action_log' v Gamma'
    -> exists action_log1 Gamma1,
    interp_action r sigma Gamma sched_log action_log cond action_log1
      (Bits [true]) Gamma1
    /\ interp_action r sigma Gamma1 sched_log action_log1 athen action_log' v
      Gamma'.
  Proof.
    intros.
    dependent destruction H.
    exists action_log'. exists Gamma'.
    repeat split; assumption.
  Qed.

  Lemma invert_switch_nil:
    forall
      {reg_t ext_fn_t: Type} {REnv: Env reg_t}
      (r: env_t REnv (fun _: reg_t => BitsToLists.val))
      (sigma: ext_fn_t -> BitsToLists.val -> BitsToLists.val)
      (Gamma Gamma': list (var_t * BitsToLists.val))
      (sched_log action_log action_log': Log REnv) var default v,
    interp_action r sigma Gamma sched_log action_log
      (USugar (USwitch var default [])) action_log' v Gamma'
    -> interp_action r sigma Gamma sched_log action_log default action_log' v
      Gamma'.
  Proof.
    intros.
    dependent destruction H.
    repeat split; assumption.
  Qed.

  (* TODO Maybe separate OK and KO to avoid generating useless hypotheses *)
  Lemma invert_switch:
    forall
      {reg_t ext_fn_t: Type} {REnv: Env reg_t}
      (r: env_t REnv (fun _: reg_t => BitsToLists.val))
      (sigma: ext_fn_t -> BitsToLists.val -> BitsToLists.val)
      (Gamma Gamma': list (var_t * BitsToLists.val))
      (sched_log action_log action_log': Log REnv) var default cond body
      branches v,
    interp_action r sigma Gamma sched_log action_log
      (USugar (USwitch var default ((cond, body)::branches))) action_log' v
      Gamma'
    -> exists action_log1 action_log2 Gamma1 Gamma2 v1 v2,
    interp_action r sigma Gamma sched_log action_log var action_log1 v1 Gamma1
    /\ interp_action r sigma Gamma1 sched_log action_log1 cond action_log2 v2
      Gamma2
    /\ (v1 = v2 -> interp_action r sigma Gamma2 sched_log action_log2 body
      action_log' v Gamma')
    /\ (v1 <> v2 -> interp_action r sigma Gamma2 sched_log action_log2 (
      USugar (USwitch var default branches)
    ) action_log' v Gamma').
  Proof.
    intros.
    dependent destruction H.
    - exists action_log'. exists action_log''. exists Gamma'. exists Gamma''.
      exists v0. exists v0.
      repeat split; try assumption.
      + intro. assumption.
      + intro. destruct H1. reflexivity.
    - exists action_log'. exists action_log''. exists Gamma'. exists Gamma''.
      exists v0. exists v.
      repeat split; try assumption.
      + intro. destruct H1. symmetry. assumption.
      + intro. assumption.
  Qed.

  Lemma invert_structinit:
  forall
    {reg_t ext_fn_t: Type} {REnv: Env reg_t}
    (r: env_t REnv (fun _: reg_t => BitsToLists.val))
    (sigma: ext_fn_t -> BitsToLists.val -> BitsToLists.val)
    (Gamma Gamma': list (var_t * BitsToLists.val))
    (sched_log action_log action_log': Log REnv) sig fields v,
  interp_action r sigma Gamma sched_log action_log
    (USugar (UStructInit sig fields)) action_log' v Gamma'
  -> exists vs vfields v_init,
  interp_list r sigma (interp_action r sigma) Gamma sched_log action_log
    (map snd fields) action_log' vfields Gamma'
  /\ uvalue_of_struct_bits (struct_fields sig)
      (repeat false (struct_fields_sz (struct_fields sig)))
    = Some vs
  /\ List.fold_left
    (fun vs '(name, v) =>
      let/opt vs := vs in
      subst_field_name (struct_fields sig) name v vs
    )
    (combine (map fst fields) (rev vfields)) (Some vs)
    = Some v_init
  /\ v = Struct sig v_init.
  Proof.
    intros.
    dependent destruction H.
    exists vs. exists vfields. exists v.
    repeat split; assumption.
  Qed.

  Lemma invert_arrayinit:
    forall
      {reg_t ext_fn_t: Type} {REnv: Env reg_t}
      (r: env_t REnv (fun _: reg_t => BitsToLists.val))
      (sigma: ext_fn_t -> BitsToLists.val -> BitsToLists.val)
      (Gamma Gamma': list (var_t * BitsToLists.val))
      (sched_log action_log action_log': Log REnv) tau elements v,
    interp_action r sigma Gamma sched_log action_log
      (USugar (UArrayInit tau elements)) action_log' v Gamma'
    -> exists vs velts v_init,
    interp_list r sigma (interp_action r sigma) Gamma sched_log action_log
      elements action_log' velts Gamma'
    /\ uvalue_of_list_bits (tau:=tau)
        (repeat (repeat false (type_sz tau)) (List.length elements))
      = Some vs
    /\ List.fold_left (fun acc v =>
         let/opt2 pos, vs := acc in
         let/opt2 l1, l2 := take_drop pos vs in
         match l2 with
         | [] => None
         | a::l2 => Some (S pos, l1 ++ v :: l2)
         end
       ) (rev velts) (Some (0, vs))
       = Some v_init
    /\ v = Array {| array_type := tau; array_len := List.length elements |}
      (snd v_init).
  Proof.
    intros.
    dependent destruction H.
    exists vs. exists velts. exists v.
    repeat split; assumption.
  Qed.

  Lemma invert_callmodule:
    forall
      {reg_t ext_fn_t: Type} {REnv: Env reg_t}
      (r: env_t REnv (fun _: reg_t => BitsToLists.val))
      (sigma: ext_fn_t -> BitsToLists.val -> BitsToLists.val)
      (Gamma Gamma': list (var_t * BitsToLists.val))
      (sched_log action_log action_log': Log REnv) v
      module_reg_t module_ext_fn_t `{finite: FiniteType module_reg_t}
      (fR: module_reg_t -> reg_t) (fSigma: module_ext_fn_t -> ext_fn_t) fn
      args,
    interp_action r sigma Gamma sched_log action_log
      (USugar (UCallModule fR fSigma fn args)) action_log' v Gamma'
    -> exists lv action_log_init action_log1 Gamma1,
    interp_list r sigma (interp_action r sigma) Gamma sched_log action_log args
      action_log_init lv Gamma'
    /\ let REnv' := @ContextEnv _ _ in
      interp_action
        (create REnv' (fun idx => getenv REnv r (fR idx)))
        (fun f => sigma (fSigma f))
        (map (fun '(name, _, v) => (name, v))
          (combine (rev (int_argspec fn)) lv)
        )
        (fLog fR REnv REnv' sched_log) (fLog fR REnv REnv' action_log_init)
        (int_body fn) action_log1 v Gamma1
    /\ action_log' = (fLog' fR REnv REnv' action_log1 action_log_init).
  Proof.
    intros.
    dependent destruction H.
    exists lv. exists action_log'. exists action_log''. exists Gamma''.
    repeat split; assumption.
  Qed.

  Lemma list_assoc_eq_dec_ext:
    forall {K V: Type} {eq1 eq2: EqDec K} (l: list (K * V)) (k: K),
    @list_assoc _ _ eq1 l k = @list_assoc _ _ eq2 l k.
  Proof. induction l; simpl; intros; eauto. destr. repeat destr. Qed.

  Lemma list_assoc_set_eq_dec_ext:
    forall {K V: Type} {eq1 eq2: EqDec K} (l: list (K * V)) (k: K) v,
    @list_assoc_set _ _ eq1 l k v = @list_assoc_set _ _ eq2 l k v.
  Proof. induction l; simpl; intros; eauto. destr. repeat destr. Qed.

  Lemma ind_ok:
    forall
      {reg_t ext_fn_t: Type} a (REnv: Env reg_t)
      (r: REnv.(env_t) (fun _ => val)) (sigma: forall f: ext_fn_t, val -> val)
      Gamma sched_log action_log Gamma' action_log' v,
    UntypedSemantics.interp_action
      r sigma Gamma sched_log action_log a = Some (action_log', v, Gamma')
    <-> interp_action r sigma Gamma sched_log action_log a action_log' v Gamma'.
  Proof.
    intros reg_t ext_fn_t ua. pattern reg_t, ext_fn_t , ua.
    match goal with
    | |- ?P _ _ ua => set (PP:=P)
    end.
    remember (size_uaction ua).
    revert reg_t ext_fn_t ua Heqn.
    pattern n.
    eapply Nat.strong_right_induction with (z:=0).
    { red. red. intros. subst. tauto. } 2: lia.
    intros n0 _ Plt reg_t' ext_fn_t' ua Heqn. subst.
    assert (Plt':
      forall
        reg_t ext_fn_t (a: Syntax.uaction pos_t var_t fn_name_t reg_t ext_fn_t),
      size_uaction a < size_uaction ua -> PP reg_t ext_fn_t a
    ).
    { intros. eapply Plt. 3: reflexivity. lia. auto. }
    clear Plt. rename Plt' into IHua. clear n. unfold PP.
    destruct ua; simpl in *; intros.
    - split; intros A; inv A.
    - split; intros A; inv A.
    - split; intros A.
      unfold opt_bind in A; repeat destr_in A; inv A.
      econstructor; eauto.
      dependent induction A. subst.
      erewrite list_assoc_eq_dec_ext.
      rewrite H. simpl; auto.
    - split; intros A.
      inv A.
      econstructor; eauto.
      dependent induction A. subst.
      apply Eqdep_dec.inj_pair2_eq_dec in H. 2: apply eq_dec.
      congruence.
    - split; intros A.
      unfold opt_bind in A; repeat destr_in A; inv A.
      eapply interp_action_assign. apply IHua.  lia. auto.
      dependent induction A. subst.
      apply IHua in A. rewrite A. simpl.
      erewrite list_assoc_set_eq_dec_ext. eauto. lia.
    - split; intros A.
      unfold opt_bind in A; repeat destr_in A; inv A.
      apply IHua in Heqo. 2: lia.
      apply IHua in H0. 2: lia.
      econstructor; eauto.
      dependent induction A. subst.
      apply IHua in A1. 2: lia.
      apply IHua in A2. 2: lia.
      rewrite A1. simpl. rewrite A2. auto.
    - split; intros A.
      unfold opt_bind in A; repeat destr_in A; inv A.
      apply IHua in Heqo. 2: lia.
      apply IHua in Heqo0. 2: lia.
      econstructor; eauto.
      dependent induction A. subst.
      apply IHua in A1. 2: lia.
      apply IHua in A2. 2: lia.
      rewrite A1. simpl. rewrite A2. auto.
    - split; intros A.
      unfold opt_bind in A; repeat destr_in A; inv A.
      apply IHua in Heqo. 2: lia.
      apply IHua in H0. 2: lia.
      econstructor; eauto.
      apply IHua in Heqo. 2: lia.
      apply IHua in H0. 2: lia.
      econstructor; eauto.
      dependent induction A. subst.
      apply IHua in A1. 2: lia.
      apply IHua in A2. 2: destr; lia.
      rewrite A1. simpl. destr.
    - split; intros A.
      + unfold opt_bind in A.
        destr_in A. inv A.
        econstructor. auto. inv A.
      + dependent induction A. subst.
        rewrite H. auto.
    - split; intros A.
      + unfold opt_bind in A; repeat destr_in A; inv A.
        apply IHua in Heqo. 2: lia.
        econstructor; eauto.
      + dependent induction A. subst.
        apply IHua in A. 2: lia.
        rewrite A. simpl. rewrite H. auto.
    - split; intros A.
      + unfold opt_bind in A; repeat destr_in A; inv A.
        apply IHua in Heqo. 2: lia.
        econstructor; eauto.
      + dependent induction A. subst.
        apply IHua in A. 2: lia.
        rewrite A. simpl. rewrite H. auto.
    - split; intros A.
      + unfold opt_bind in A; repeat destr_in A; inv A.
        apply IHua in Heqo. 2: lia.
        apply IHua in Heqo0. 2: lia.
        econstructor; eauto.
      + dependent induction A. subst.
        apply IHua in A1. 2: lia.
        apply IHua in A2. 2: lia.
        rewrite A1. simpl. rewrite A2. simpl. rewrite H; auto.
    - split; intros A.
      + unfold opt_bind in A; repeat destr_in A; inv A.
        apply IHua in Heqo. 2: lia.
        econstructor; eauto.
      + dependent induction A. subst.
        apply IHua in A. 2: lia.
        rewrite A. simpl. auto.
    - split; intros A.
      + unfold opt_bind in A; repeat destr_in A; inv A.
        setoid_rewrite interp_list_ok in Heqo.
        2: intros; apply IHua.
        apply IHua in Heqo0. 2: lia.
        econstructor; eauto.
        cut (size_uaction a <= list_sum (map size_uaction args)).
        lia.
        { clear - H. revert H; induction args; simpl; intros; eauto. easy.
          destruct H. subst. lia.
          apply IHargs in H. lia.
        }
      + dependent induction A. subst.
        rewrite <- interp_list_ok in H.
        rewrite H. simpl.
        apply IHua in A. 2: lia.
        rewrite A. simpl. auto.
        intros; eapply IHua.
        cut (size_uaction a <= list_sum (map size_uaction args)).
        lia.
        { clear - H0. revert H0; induction args; simpl; intros; eauto. easy.
          destruct H0. subst. lia.
          apply IHargs in H. lia.
        }
    - split; intros A.
      + apply IHua in A. 2: lia.
        econstructor; eauto.
      + dependent induction A. subst.
        apply IHua in A. 2: lia.
        rewrite A. simpl. auto.
    - destruct s.
      + split; intros A.
        * inv A.
        * dependent induction A.
      + split; intros A.
        * inv A. econstructor; eauto.
        * dependent induction A. auto.
      + split; intros A.
        * inv A. econstructor; eauto.
        * dependent induction A. subst.
          apply Eqdep_dec.inj_pair2_eq_dec in H. 2: apply eq_dec.
          subst. unfold l. auto.
      + split; intros A.
        * inv A. econstructor; eauto.
        * dependent induction A. subst. eauto.
      + split; intros A.
        * destr_in A; inv A. econstructor; eauto.
        * dependent induction A. subst. rewrite H. eauto.
      + assert (
          forall aa v0 action_log Gamma,
          fold_left
            (fun
              (acc : option (Log REnv * val * list (var_t * val)))
              (a : uaction pos_t var_t fn_name_t reg_t' ext_fn_t')
             =>
               let/opt3 action_log, _, Gamma := acc in
               UntypedSemantics.interp_action
                r sigma Gamma sched_log action_log a
            ) aa (Some (action_log, v0, Gamma))
          = let/opt3 action_log, l, Gamma :=
            fold_left
              (fun
                (acc : option (Log REnv * list val * list (var_t * val)))
                (a : uaction pos_t var_t fn_name_t reg_t' ext_fn_t')
              =>
                let/opt3 action_log, l, Gamma := acc in
                let/opt3 action_log, v, Gamma :=
                  UntypedSemantics.interp_action
                    r sigma Gamma sched_log action_log a
                in Some(action_log, v::l, Gamma)
              )
              aa (Some (action_log, [], Gamma))
          in Some(action_log, hd v0 l, Gamma)
        ).
        { clear.
          induction aa; simpl; intros; eauto.
          destruct (
            UntypedSemantics.interp_action
              r sigma Gamma sched_log action_log a
          ) eqn:?.
          - destruct p, p; simpl.
            rewrite IHaa.
            rewrite fold_left_rec with (X:=[v]). destr; simpl; auto.
            destruct p, p. simpl.
            destruct l3; simpl; auto.
          - simpl.
            rewrite fold_left_none; simpl; auto.
            rewrite fold_left_none; simpl; auto.
        }
        rewrite H. clear H.
        split; intros A.
        * unfold opt_bind in A; destr_in A; simpl in *; try congruence.
          repeat destr_in A; inv A.
          econstructor. eapply interp_list_ok; eauto.
          2: setoid_rewrite Heqo; auto.
          intros; eapply IHua; eauto.
          { clear - H. revert H; induction aa; simpl; intros; eauto. easy.
            destruct H. subst. lia.
            apply IHaa in H. lia.
          }
        * dependent induction A. subst.
          eapply interp_list_ok in H.
          rewrite H. simpl. auto.
          intros; eapply IHua; eauto.
          { clear - H1. revert H1; induction aa; simpl; intros; eauto. easy.
            destruct H1. subst. lia.
            apply IHaa in H. simpl in H. lia.
          }
      + split; intros A.
        * unfold opt_bind in A; repeat destr_in A; inv A.
          setoid_rewrite interp_list_ctx_ok in Heqo.
          2: intros; eapply IHua.
          eapply IHua in Heqo0. 2: simpl; lia.
          econstructor; eauto.
          { clear - H. revert H; induction bindings; simpl; intros; eauto. easy.
            destruct H. subst. destr. simpl in *. lia.
            apply IHbindings in H. simpl in H. destr. lia.
          }
        * dependent induction A. subst.
          eapply interp_list_ctx_ok in H.
          rewrite H. simpl.
          eapply IHua in A. 2: simpl; lia.
          rewrite A. simpl; auto.
          intros; eapply IHua.
          { clear - H1. rename H1 into H.
            revert H; induction bindings; simpl; intros; eauto. easy.
            destruct H. subst. destr. simpl in *. lia.
            apply IHbindings in H. simpl in H. destr. lia.
          }
      + split; intros A.
        * unfold opt_bind in A; repeat destr_in A; inv A.
          eapply IHua in Heqo. 2: simpl; lia.
          eapply IHua in H0. 2: simpl; lia.
          econstructor; eauto.
        * dependent induction A. subst.
          eapply IHua in A1. 2: simpl; lia.
          eapply IHua in A2. 2: simpl; lia.
          rewrite A1; simpl. rewrite A2; simpl; auto.
      + split; intros A.
        * unfold opt_bind in A; repeat destr_in A; inv A.
          induction branches; simpl in *.
          -- inv Heqo.
          -- destruct a.
             destruct (
               match
                 UntypedSemantics.interp_action
                   r sigma Gamma sched_log action_log var
               with
               | Some (action_log, v0, Gamma) =>
                 match
                   UntypedSemantics.interp_action
                     r sigma Gamma sched_log action_log u
                 with
                 | Some (action_log0, v, Gamma0) =>
                   if val_eq_dec v v0 then
                     match
                       UntypedSemantics.interp_action
                         r sigma Gamma0 sched_log action_log0 u0
                     with
                     | Some (action_log1, v1, Gamma1) =>
                       Some (action_log1, Some v1, Gamma1)
                     | None => None
                     end
                   else Some (action_log0, None, Gamma0)
                 | None => None
                 end
               | None => None
               end
             ) eqn:?.
             2: rewrite fold_left_none in Heqo. 2: inv Heqo.
             2: intros; destr; auto.
             repeat destr_in Heqo0; inv Heqo0.
             replace (fold_left _ _ _) with (Some (l4, Some v2, l3)) in Heqo.
             2: { clear.
               induction branches; simpl; intros; eauto.
               destruct a; auto.
             }
             inv Heqo.
             eapply IHua in Heqo1. 2: simpl; lia.
             eapply IHua in Heqo2. 2: simpl; lia.
             eapply IHua in Heqo3. 2: simpl; lia.
             eapply interp_action_switch_ok; eauto.
             eapply IHua in Heqo1. 2: simpl; lia.
             eapply IHua in Heqo2. 2: simpl; lia.
             eapply interp_action_switch_ko; eauto.
             eapply IHua. simpl. lia.
             simpl. setoid_rewrite Heqo. simpl. auto.
          -- revert l l0 action_log Gamma Heqo H0.
             induction branches; simpl; intros; eauto.
             ++ eapply IHua in H0. 2: simpl; lia.
                inv Heqo.
                econstructor. eauto.
             ++ destruct a.
                destruct (
                  match
                    UntypedSemantics.interp_action
                      r sigma Gamma sched_log action_log var
                  with
                  | Some (action_log, v0, Gamma) =>
                    match
                      UntypedSemantics.interp_action
                        r sigma Gamma sched_log action_log u
                    with
                    | Some (action_log0, v, Gamma0) =>
                      if val_eq_dec v v0 then
                        match
                          UntypedSemantics.interp_action
                            r sigma Gamma0 sched_log action_log0 u0
                        with
                        | Some (action_log1, v1, Gamma1) =>
                          Some (action_log1, Some v1, Gamma1)
                        | None => None
                      end
                      else Some (action_log0, None, Gamma0)
                    | None => None
                    end
                  | None => None
                  end
                ) eqn:?.
                2: rewrite fold_left_none in Heqo. 2: inv Heqo.
                2: intros; destr; auto.
                repeat destr_in Heqo0; inv Heqo0.
                replace (fold_left _ _ _) with (Some (l6, Some v2, l5)) in Heqo.
                2: { clear.
                  induction branches; simpl; intros; eauto.
                  destruct a; auto.
                }
                inv Heqo.
                eapply IHua in Heqo1. 2: simpl; lia.
                eapply IHua in Heqo2. 2: simpl; lia.
                eapply IHua in H0. 2: simpl; lia.
                eapply interp_action_switch_ko; eauto.
                eapply IHbranches; eauto. simpl; intros; eapply IHua. simpl.
                lia. eapply IHua. simpl. lia. eauto.
        * dependent induction A; subst.
          -- eapply IHua in A. 2: simpl; lia.
             simpl. eauto.
          -- eapply IHua in A1. 2: simpl; lia. eapply IHua in A2. 2: simpl; lia.
             eapply IHua in A3. 2: simpl; lia. simpl.
             rewrite A1. simpl. rewrite A2. simpl. rewrite A3. simpl.
             destruct (val_eq_dec v0 v0); try congruence.
             replace (fold_left _ _ _)
               with (Some (action_log''', Some v2, Gamma''')).
             2: { clear.
               induction branches0; simpl; intros; eauto.
               destruct a; auto.
             }
             simpl. auto.
          -- eapply IHua in A1. 2: simpl; lia. eapply IHua in A2. 2: simpl; lia.
             eapply IHua in A3. 2: simpl; lia. simpl.
             rewrite A1. simpl. rewrite A2. simpl.
             destruct (val_eq_dec v v0); try congruence.
             eapply IHA3; eauto.
             intros; eapply IHua. simpl in *. lia.
      + split; intros A.
        * unfold opt_bind in A; repeat destr_in A; inv A.
          setoid_rewrite <- structinit_ind_ok in Heqo0.
          destruct Heqo0 as (vf & IL & FL).
          econstructor; eauto.
          intros; eapply IHua. simpl.
          { clear - H. revert H.
            induction fields; simpl; intros; eauto. easy.
            destruct a0; simpl in *.
            destruct H. subst. lia.
            apply IHfields in H. lia.
          }
        * dependent induction A. subst.
          unfold zeroes in *. rewrite H0. simpl.
          edestruct (structinit_ind_ok r sigma (interp_action r sigma))
            as [SIO _].
          intros; eapply IHua. 2: rewrite SIO.
          { clear - H2. revert H2.
            induction fields; simpl; intros; eauto. easy.
            destruct a0; simpl in *.
            destruct H2. subst. lia.
            apply IHfields in H. lia.
          } simpl. eauto.
          eexists; split. apply H.
          apply H1.
      + split; intros A.
        * unfold opt_bind in A; repeat destr_in A; inv A.
          setoid_rewrite <- arrayinit_ind_ok in Heqo0.
          destruct Heqo0 as (vf & IL & FL).
          replace (l1) with (snd (n, l1)).
          econstructor; eauto. reflexivity.
          intros; eapply IHua. simpl.
          { clear - H. revert H.
            induction elements; simpl; intros; eauto. easy.
            destruct H. subst. lia.
            apply IHelements in H. lia.
          }
        * dependent induction A. subst.
          unfold zeroes in *. rewrite H0. simpl.
          edestruct (arrayinit_ind_ok r sigma (interp_action r sigma))
            as [SIO _].
          intros; eapply IHua. 2: rewrite SIO.
          { clear - H2. revert H2.
            induction elements; simpl; intros; eauto. easy.
            destruct H2. subst. lia.
            apply IHelements in H. simpl in H. lia.
          } simpl. eauto.
          eexists; split. apply H.
          rewrite H1. f_equal.
          apply surjective_pairing.
      + split; intros A.
        * unfold opt_bind in A; repeat destr_in A; inv A.
          setoid_rewrite interp_list_ok with (i:=interp_action r sigma) in Heqo.
          2: intros; apply IHua.
          econstructor. eauto. apply IHua. simpl; lia. eauto.
          cut (size_uaction a <= list_sum (map size_uaction args)).
          simpl; lia.
          { clear - H. revert H; induction args; simpl; intros; eauto. easy.
            destruct H. subst. lia.
            apply IHargs in H. lia.
          }
        * dependent destruction A. subst.
          rewrite <- interp_list_ok in H. rewrite H. simpl.
          apply IHua in A.
          unfold REnv' in *.
          setoid_rewrite A. simpl. auto.
          simpl. lia.
          intros; eapply IHua.
          cut (size_uaction a <= list_sum (map size_uaction args)).
          simpl; lia.
          { clear - H0. revert H0; induction args; simpl; intros; eauto. easy.
            destruct H0. subst. lia.
            apply IHargs in H. lia.
          }
  Qed.

  Inductive interp_rule:
    forall
      {reg_t ext_fn_t: Type} `{REnv: Env reg_t} (r: REnv.(env_t) (fun _ => val))
      (sigma: forall f: ext_fn_t, val -> val) (sched_log: Log REnv)
      (a: Syntax.uaction pos_t var_t fn_name_t reg_t ext_fn_t)
      (action_log': Log REnv),
    Prop :=
  | interp_rule_intro:
    forall
      {reg_t ext_fn_t: Type} `{REnv: Env reg_t} (r: REnv.(env_t) (fun _ => val))
      (sigma: forall f: ext_fn_t, val -> val) (Gamma': list (var_t * val))
      (sched_log: Log REnv) (action_log': Log REnv) a v,
    interp_action r sigma nil sched_log log_empty a action_log' v Gamma'
    -> interp_rule r sigma sched_log a action_log'.

  Lemma interp_rule_ind_ok:
    forall
      {reg_t ext_fn_t: Type} a (REnv: Env reg_t)
      (r: REnv.(env_t) (fun _ => val)) (sigma: forall f: ext_fn_t, val -> val)
      sched_log action_log',
    UntypedSemantics.interp_rule r sigma sched_log a = Some (action_log')
    <-> interp_rule r sigma sched_log a action_log'.
  Proof.
    intros. unfold UntypedSemantics.interp_rule.
    split; intros A.
    - repeat destr_in A; inv A.
      apply ind_ok in Heqo. econstructor; eauto.
    - dependent destruction A. apply ind_ok in H. rewrite H. auto.
  Qed.

  Context {rule_name_t: Type}.

  Section Scheduler.
    Context {reg_t ext_fn_t: Type}.
    Context
      (rules: rule_name_t -> uaction pos_t var_t fn_name_t reg_t ext_fn_t).

    Inductive interp_try
      {REnv: Env reg_t} (r: REnv.(env_t) (fun _ => val))
      (sigma: forall f: ext_fn_t, val -> val)
      (IS: Log REnv -> scheduler pos_t rule_name_t -> Log REnv -> Prop)
    : Log REnv -> rule_name_t -> scheduler pos_t rule_name_t
      -> scheduler pos_t rule_name_t -> Log REnv -> Prop
    :=
    | interp_try_ok:
      forall sched_log rl l s1 s2 l',
      interp_rule r sigma sched_log (rules rl) l ->
      IS (log_app l sched_log) s1 l' ->
      interp_try r sigma IS sched_log rl s1 s2 l'
    | interp_try_ko:
      forall sched_log rl s1 s2 l',
      (forall l, ~ interp_rule r sigma sched_log (rules rl) l) ->
      IS sched_log s2 l' ->
      interp_try r sigma IS sched_log rl s1 s2 l'.

    Inductive interp_scheduler'
      {REnv: Env reg_t} (r: REnv.(env_t) (fun _ => val))
      (sigma: forall f: ext_fn_t, val -> val)
    : Log REnv -> scheduler pos_t rule_name_t -> Log REnv -> Prop :=
    | interp_scheduler'_done: forall l, interp_scheduler' r sigma l Done l
    | interp_scheduler'_cons:
      forall l rl s l',
      interp_try r sigma (interp_scheduler' r sigma) l rl s s l'
      -> interp_scheduler' r sigma l (Cons rl s) l'
    | interp_scheduler'_try:
      forall l rl s1 s2 l',
      interp_try r sigma (interp_scheduler' r sigma) l rl s1 s2 l'
      -> interp_scheduler' r sigma l (Try rl s1 s2) l'
    | interp_scheduler'_spos:
      forall l p s l',
      interp_scheduler' r sigma l s l'
      -> interp_scheduler' r sigma l (SPos p s) l'.

    Lemma interp_scheduler'_ind_ok:
      forall
        {REnv: Env reg_t} (r: REnv.(env_t) (fun _ => val))
        (sigma: forall f: ext_fn_t, val -> val) s l l',
      UntypedSemantics.interp_scheduler' rules r sigma l s = l'
      <-> interp_scheduler' r sigma l s l'.
    Proof.
      induction s; simpl; intros; eauto.
      - split. intros A. inv A. constructor.
        intros A; inv A; eauto.
      - split.
        + intros A. destr_in A.
          * apply IHs in A.
            apply interp_rule_ind_ok in Heqo. econstructor; eauto.
            eapply interp_try_ok; eauto.
          * apply IHs in A.
            econstructor.
            eapply interp_try_ko; eauto.
            intros l0 IR. apply interp_rule_ind_ok in IR. congruence.
        + intros A. inv A. inv H3.
          * apply IHs in H0.
            apply interp_rule_ind_ok in H. rewrite H. eauto.
          * apply IHs in H0.
            destr. apply interp_rule_ind_ok in Heqo. apply H in Heqo. easy.
      - split.
        + intros A. destr_in A.
          * apply IHs1 in A.
            apply interp_rule_ind_ok in Heqo. econstructor; eauto.
            eapply interp_try_ok; eauto.
          * apply IHs2 in A.
            econstructor.
            eapply interp_try_ko; eauto.
            intros l0 IR. apply interp_rule_ind_ok in IR. congruence.
        + intros A. inv A. inv H4.
          * apply IHs1 in H0.
            apply interp_rule_ind_ok in H. rewrite H. eauto.
          * apply IHs2 in H0.
            destr. apply interp_rule_ind_ok in Heqo. apply H in Heqo. easy.
      - rewrite IHs. split; intros A. econstructor; eauto. inv A; auto.
    Qed.

    Inductive interp_scheduler
      {REnv: Env reg_t} (r: REnv.(env_t) (fun _ => val))
      (sigma: forall f: ext_fn_t, val -> val)
    : scheduler pos_t rule_name_t -> Log REnv -> Prop :=
    | interp_scheduler_intro:
      forall s l,
      interp_scheduler' r sigma log_empty s l -> interp_scheduler r sigma s l.

    Lemma interp_scheduler_ind_ok:
      forall
        {REnv: Env reg_t} (r: REnv.(env_t) (fun _ => val))
        (sigma: forall f: ext_fn_t, val -> val) s l',
      UntypedSemantics.interp_scheduler rules r sigma s = l'
      <-> interp_scheduler r sigma s l'.
    Proof.
      intros. unfold UntypedSemantics.interp_scheduler.
      rewrite interp_scheduler'_ind_ok. split; intros A.
      econstructor; eauto.
      inv A; auto.
    Qed.

    Inductive interp_cycle
      {REnv: Env reg_t} (r: REnv.(env_t) (fun _ => val))
      (sigma: forall f: ext_fn_t, val -> val)
    : scheduler pos_t rule_name_t -> REnv.(env_t) (fun _ => val) -> Prop :=
    | interp_cycle_intro:
      forall s l, interp_scheduler r sigma s l
      -> interp_cycle r sigma s (commit_update r l).

    Lemma interp_cycle_ind_ok:
      forall
        {REnv: Env reg_t} (r: REnv.(env_t) (fun _ => val))
        (sigma: forall f: ext_fn_t, val -> val) s r',
      UntypedSemantics.interp_cycle rules r sigma s = r'
      <-> interp_cycle r sigma s r'.
    Proof.
      intros. unfold UntypedSemantics.interp_cycle.
      split; intros A.
      subst. econstructor.
      apply interp_scheduler_ind_ok. auto.
      inv A.
      apply interp_scheduler_ind_ok in H. congruence.
    Qed.
  End Scheduler.
End Interp.
