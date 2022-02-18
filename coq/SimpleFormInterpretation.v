Require Import Coq.Strings.Ascii.
Require Import Koika.Environments Koika.SimpleForm Koika.TypeInference
  Koika.UntypedSemantics.
Require Import Koika.BitsToLists.
From RecordUpdate Require Import RecordSet.
Import RecordSetNotations.

Section SimpleFormInterpretation.
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

  Definition const_nil :=
    @UConst pos_t string string reg_t ext_fn_t (bits_t 0) (Bits.of_nat 0 0).
  Definition const_false :=
    @UConst pos_t string string reg_t ext_fn_t (bits_t 1) (Bits.of_nat 1 0).
  Definition const_true :=
    @UConst pos_t string string reg_t ext_fn_t (bits_t 1) (Bits.of_nat 1 1).

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

  Definition inlining_pass (sf: @simple_form pos_t reg_t ext_fn_t)
  : simple_form * list (string * val) :=
    (* Try to determine the value of variables *)
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
    (* Try to determine the result of extcalls *)
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

  (* Cycles between variables are possible (a variable v can depend on another
     variable which itself depends on v). However, these can only occur in
     situations in which the cycle can be removed by applying some
     simplifications to the expression. We know this because of the way simple
     forms passed to this function are expected to have been built.

     Note that we don't need our simplifications to be exhaustive: for instance
     we choose to ignore that an and can be short-circuited based on its right
     operand. *)
  Fixpoint simplify_uact (ua: uact) : uact :=
    match ua with
    | UIf cond tb fb =>
      let cond' := simplify_uact cond in
      let tb' := simplify_uact tb in
      let fb' := simplify_uact fb in
      if (negb (contains_vars cond')) then
        match interp_action r sigma [] log_empty log_empty cond' with
        | Some (_, Bits 1 [true], _) => tb'
        | Some (_, Bits 1 [false], _) => fb'
        | _ => UVar "ERROR cond" (* Should never happen *)
        end
      else UIf cond' tb' fb'
    | UBinop ufn a1 a2 =>
      let a1' := simplify_uact a1 in
      let a2' := simplify_uact a2 in
      if andb (negb (contains_vars a1')) (contains_vars a2') then
        match ufn with
        | PrimUntyped.UBits2 PrimUntyped.UAnd =>
          match interp_action r sigma [] log_empty log_empty a1' with
          | Some (_, Bits 1 [false], _) => const_false
          | Some (_, Bits 1 [true], _) => a2'
          | _ => UVar "ERROR binop and" (* Should never happen *)
          end
        | PrimUntyped.UBits2 PrimUntyped.UOr =>
          match interp_action r sigma [] log_empty log_empty a2' with
          | Some (_, Bits 1 [true], _) => const_true
          | Some (_, Bits 1 [false], _) => a2'
          | _ => UVar "ERROR binop or" (* Should never happen *)
          end
        | _ => UBinop ufn a1' a2'
        end
      else UBinop ufn a1' a2'
    | UUnop ufn a => (* Perhaps not strictly required *)
        UUnop ufn (simplify_uact a)
    | _ => ua
    end.

  Definition expr_simplification_pass (sf: @simple_form pos_t reg_t ext_fn_t)
  : simple_form := {|
    final_values := final_values sf;
    vars := map (fun '(vn, vu) => (vn, simplify_uact vu)) (vars sf);
    external_calls :=
      map
        (fun '(efn, ei) => (efn, {|
          econd := simplify_uact (econd ei); earg := simplify_uact (earg ei);
          ebind := ebind ei; |}))
        (external_calls sf) |}.

  Definition simplification_pass (sf: @simple_form pos_t reg_t ext_fn_t)
  : simple_form * list (string * val)  :=
    inlining_pass (expr_simplification_pass sf).

  Fixpoint simplify (sf: @simple_form pos_t reg_t ext_fn_t) (fuel: nat)
  : list (string * val) :=
    match fuel with
    | O => [] (* Should never happen *)
    | S f' =>
      let (sf', vals) := simplification_pass sf in
      vals++(simplify sf' f')
    end.

  Definition interp_cycle (sf: @simple_form pos_t reg_t ext_fn_t) : UREnv :=
    let fenv :=
      simplify sf (List.length (vars sf) + List.length (external_calls sf))
    in
    (* No need to explicitly inline read0s: delegated to interp_action *)
    fold_left
      (fun acc '(reg, n) =>
        REnv.(putenv)
          acc reg
          (match list_assoc fenv n with
           | None => REnv.(getenv) r reg (* Should be unreachable *)
           | Some v => v
           end)
      )
      (final_values sf) r.

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
End SimpleFormInterpretation.
