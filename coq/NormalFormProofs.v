Require Import Coq.Strings.Ascii.
Require Import Koika.BitsToLists Koika.Environments Koika.Normalize
  Koika.TypeInference Koika.UntypedSemantics.

Section NormalForm.
  Context {pos_t reg_t ext_fn_t rule_name_t: Type}.
  Context {reg_t_eq_dec: EqDec reg_t}.
  Context {ext_fn_t_eq_dec: EqDec ext_fn_t}.
  Context {REnv: Env reg_t}.
  Context {TR: reg_t -> type}.

  Context (R: reg_t -> type).
  Context (Sigma: ext_fn_t -> ExternalSignature).

  Definition uact := @uaction pos_t string string reg_t ext_fn_t.
  Definition schedule := scheduler pos_t rule_name_t.
  Definition ext_funs_defs :=
    forall f: ext_fn_t, BitsToLists.val -> BitsToLists.val.
  Definition UREnv := REnv.(env_t) (fun _ => BitsToLists.val).

  Fixpoint get_vars_in_simpl_uact (e: uact) : list string :=
    match e with
    | UBinop ufn a1 a2 =>
      (get_vars_in_simpl_uact a1)++(get_vars_in_simpl_uact a2)
    | UUnop ufn a1 => get_vars_in_simpl_uact a1
    | UVar v => [v]
    | UIf cond tb fb =>
      (get_vars_in_simpl_uact cond)
      ++(get_vars_in_simpl_uact tb)
      ++(get_vars_in_simpl_uact fb)
    | _ => [] (* Should never happen *)
    end.

  Definition get_var_depth (v: string) (vvm: var_value_map) : option nat :=
    match list_assoc vvm v with
    | None => None
    | Some e => Some (get_exp_depth e)
    end.

  Definition interp_cycle
    (r: UREnv) (sigma: ext_funs_defs) (n: @normal_form pos_t reg_t ext_fn_t)
  : UREnv :=
    let interp_read1s :=
      List.map (fun '(reg, name) => (name, getenv REnv r reg)) (reads n)
    in
    (* We use the fact that the variables are recursively defined *)
    let interp_vars :=
      List.map (fun '(name, e) => (name, )) (reads n)
    in
    (* let interp_extcalls := *)
    (* in *)
    r.

  Lemma normal_form_ok:
    forall
      (r: UREnv) (sigma: ext_funs_defs) (rules: rule_name_t -> uact)
      (s: schedule) (p: pos_t)
      (TA:
        forall rule, exists tcr,
        TypeInference.tc_rule TR Sigma p (rules rule) = Success tcr
      ),
    UntypedSemantics.interp_cycle rules r sigma s =
    NormalForm.interp_cycle r sigma (Normalize.schedule_to_normal_form rules s).
  Proof.
  Admitted.
End NormalForm.
