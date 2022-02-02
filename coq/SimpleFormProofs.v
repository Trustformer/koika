Require Import Coq.Strings.Ascii.
Require Import Koika.Environments Koika.SimpleForm Koika.TypeInference
  Koika.UntypedSemantics.
Require Import Koika.BitsToLists.

Section SimpleForm.
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

  Context (r: UREnv).
  Context (sigma: ext_funs_defs).

  Fixpoint contains_vars (e: uact) : bool :=
    match e with
    | UBinop ufn a1 a2 => orb (contains_vars a1) (contains_vars a2)
    | UUnop ufn a1 => contains_vars a1
    | UVar v => true
    | UIf cond tb fb =>
      orb (contains_vars cond) (orb (contains_vars tb) (contains_vars fb))
    | _ => false (* URead *)
    end.

  Fixpoint replace_all_occurrences_in_uact (ua: uact) (from: string) (to: val)
  : uact :=
    match ua with
    | UBinop ufn a1 a2 =>
      UBinop
        ufn (replace_all_occurrences_in_uact a1 from to)
        (replace_all_occurrences_in_uact a2 from to)
    | UUnop ufn a1 => UUnop ufn (replace_all_occurrences_in_uact a1 from to)
    | UVar v =>
      if (String.eqb v from) then
        let bl := ubits_of_value to in
        UConst (tau := bits_t (List.length bl)) (vect_of_list bl)
      else UVar v
    | UIf cond tb fb =>
      UIf
        (replace_all_occurrences_in_uact cond from to)
        (replace_all_occurrences_in_uact tb from to)
        (replace_all_occurrences_in_uact fb from to)
    | _ => ua
    end.

  Definition replace_all_occurrences_in_map
    (map: var_value_map) (from: string) (to: val)
  : var_value_map :=
    List.map
      (fun '(reg, ua) => (reg, replace_all_occurrences_in_uact ua from to))
      map.

  Definition simplification_pass (vars: var_value_map)
  : var_value_map * list (string * val) :=
    List.fold_left
      (fun '(vvm, l) '(reg, ua) =>
        if negb (contains_vars ua) then
          match interp_action r sigma [] log_empty log_empty ua with
          | None => ([], []) (* Should never happen *)
          | Some (_, v, _) =>
            (replace_all_occurrences_in_map vvm reg v, (reg, v)::l)
          end
        else (vvm, l))
      vars
      (vars, []).

  (* TODO Evaluate writes at the same time *)
  Fixpoint simplify
    (vars: @var_value_map pos_t reg_t ext_fn_t) (vals: list (string * val))
    (fuel: nat)
  : list (string * val) :=
    match fuel with
    | O => [] (* Should never happen *)
    | S f' =>
      let (vars', vals') := simplification_pass vars in
      simplify vars' (vals'++vals) f'
    end.

  (* Simply replace variables by their definition and delegate to inter_action *)

  Fixpoint interp_var_aux (variables: var_value_map) (v: uact) (fuel: nat)
  : option val :=
  match fuel with
  | 0 => None
  | S f' =>
    match v with
    | UBinop ufn a1 a2 => sigma2 ufn
    | UUnop ufn a1 => 
    | UVar v => 
    | UIf cond tb fb =>
    | URead p r =>
      match p with
      | P1 => None (* Illegal *)
      | P0 => Some 
      end
    | _ => None (* Illegal *)
    end.

  (* Assuming called in the right order, should not result in a None *)
  Definition interp_var (variables: var_value_map) (s: string) (fuel: nat)
  : option val :=
    match list_assoc variables s with
    | None => None
    | Some v => interp_var_aux variables v
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
        TypeInference.tc_rule TR Sigma p (rules rule) = Success tcr),
    UntypedSemantics.interp_cycle rules r sigma s =
    SimpleForm.interp_cycle r sigma
      (SimpleForm.schedule_to_normal_form rules s).
  Proof.
  Admitted.
End SimpleForm.
