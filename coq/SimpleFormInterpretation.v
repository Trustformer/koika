Require Import Coq.Strings.Ascii.
Require Import Koika.Environments Koika.SimpleForm Koika.TypeInference
  Koika.UntypedSemantics.
Require Import Koika.BitsToLists.
From RecordUpdate Require Import RecordSet.
Import RecordSetNotations.

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

  Definition replace_all_occurrences_in_vars
    (vars: var_value_map) (from: string) (to: val)
  : var_value_map :=
    map
      (fun '(reg, ua) => (reg, replace_all_occurrences_in_uact ua from to))
      vars.

  Definition replace_all_occurrences_in_extcalls
    (extc: extcall_log) (from: string) (to: val)
  : extcall_log :=
    map
      (fun '(en, ei) => (en, {|
        econd := replace_all_occurrences_in_uact (econd ei) from to;
        earg := replace_all_occurrences_in_uact (earg ei) from to;
        ebind := ebind ei |}))
      extc.

  (* TODO simplify as well: initial simpl pass then whenever change *)
  Definition replace_all_occurrences (sf: simple_form) (from: string) (to: val)
  : simple_form := {|
    final_values := final_values sf;
    vars := replace_all_occurrences_in_vars (vars sf) from to;
    external_calls :=
      replace_all_occurrences_in_extcalls (external_calls sf) from to |}.

  (* TODO use coq record update here as well *)
  (* TODO variable in environment instead of inlining *)

  Definition remove_by_name_extc
    (sf: @simple_form pos_t reg_t ext_fn_t) (name: string)
  : simple_form := {|
    final_values := final_values sf;
    vars := vars sf;
    external_calls :=
      filter (fun '(_, ei) => eqb (ebind ei) name) (external_calls sf) |}.

  Definition remove_by_name_var
    (sf: @simple_form pos_t reg_t ext_fn_t) (name: string)
  : simple_form := {|
    final_values := final_values sf;
    vars := filter (fun '(n, _) => eqb n name) (vars sf);
    external_calls := external_calls sf |}.

  Definition set_cond_true_by_name
    (sf: @simple_form pos_t reg_t ext_fn_t) (name: string)
  : simple_form := {|
    final_values := final_values sf;
    vars := vars sf;
    external_calls :=
      map
        (fun '(efn, ei) =>
          if eqb name (ebind ei)
          then (
            efn,
            {| econd := UConst (tau := bits_t 1) (Bits.of_nat 1 1);
               earg := earg ei; ebind := ebind ei |})
          else (efn, ei))
        (external_calls sf) |}.

  Definition simplification_pass (sf: @simple_form pos_t reg_t ext_fn_t)
  : simple_form * list (string * val) :=
    let (sf', lv) :=
      fold_left
        (fun '(sf', l) '(var, ua) =>
          if negb (contains_vars ua) then
            match interp_action r sigma [] log_empty log_empty ua with
            | None => (sf', []) (* Should never happen *)
            | Some (_, v, _) => (
               replace_all_occurrences (remove_by_name_var sf' var) var v,
               (var, v)::l)
            end
          else (sf', l))
        (vars sf) (sf, [])
    in
    fold_left
      (fun '(sf'', l) '(efn, ei) =>
        if (negb (contains_vars (econd ei))) then
          match interp_action r sigma [] log_empty log_empty (econd ei) with
          | None => (sf'', []) (* Should never happen *)
          | Some (_, cv, _) =>
            match cv with
            | Bits 1 [true] => 
              if (negb (contains_vars (earg ei))) then
                match
                  interp_action r sigma [] log_empty log_empty
                    (UExternalCall efn (earg ei))
                with
                | None => (sf'', l) (* Should nevet_r happen *)
                | Some (_, r, _) =>
                  (remove_by_name_extc sf'' (ebind ei), (ebind ei, r)::l)
                end
              else (set_cond_true_by_name sf'' (ebind ei), l)
            | _ => (remove_by_name_extc sf'' (ebind ei), l)
            end
          end
        else (sf'', l))
      (external_calls sf') (sf', lv).

  (* TODO *)
  Fixpoint simplify_uact (ua: uact) : uact :=
    match ua with
    | UIf =>
    | UBinop =>
    end

  Definition initial_simplification_pass (sf: @simple_form pos_t reg_t ext_fn_t)
  : simple_form :=
    let 
  .

  Fixpoint simplify
    (sf: @simple_form pos_t reg_t ext_fn_t) (fuel: nat)
  : list (string * val) :=
    let sf_simpl := initial_simplification sf in
    match fuel with
    | O => [] (* Should never happen *)
    | S f' =>
      let (vars', vals') := simplification_pass vars in
      simplify vars' (vals'++vals) f'
    end.

  (* Simply replace variables by their definition and delegate to
     interp_action *)
  Fixpoint interp_var_aux (registers: list (reg_t * uact)) (v: uact) (fuel: nat)
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
      | P0 => Some (* TODO *)
      end
    | _ => None (* Illegal *)
    end.

  (* Assuming called in the right order, should not result in a None *)
  Definition interp_var (registers: list (reg_t * uact)) (s: string) (fuel: nat)
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
