(*! Proving | Transformation of a schedule to a single rule with a limited
    syntax !*)
Require Import Coq.Numbers.DecimalString Coq.Program.Equality Coq.Strings.Ascii.
Require Import Koika.BitsToLists Koika.Primitives Koika.Utils Koika.Zipper.
Open Scope nat.

(* In this file, whenever side-effects or equivalence are mentionned, bear in
   mind that we do not care about the contents of the logs, but rather about
   the state of the model at the end of the cycle. For example, reading an
   otherwise unaccessed variable is not considered a side-effect. *)

(* The normal form in question is a single rule (instead of a schedule)
   containing a sequence of writes guarded by a single if each. *)

Section Normalize.
  Context {pos_t var_t reg_t ext_fn_t: Type}.
  Context {reg_t_eq_dec: EqDec reg_t}.
  Context {ext_fn_t_eq_dec: EqDec ext_fn_t}.
  Definition uact := uaction pos_t string string reg_t ext_fn_t.

  (* A. Rule simplification *)
  (* A.1. Early simplification pass - we start by simplifying some elements that
     do not pose any issues with regard to purity *)
  (* Assumption: desugared *)
  Fixpoint remove_uapos (ua: uact) : uact :=
    match ua with
    | UAssign v ex => UAssign v (remove_uapos ex)
    | USeq a1 a2 => USeq (remove_uapos a1) (remove_uapos a2)
    | UBind v ex body => UBind v (remove_uapos ex) (remove_uapos body)
    | UIf cond tbranch fbranch =>
      UIf (remove_uapos cond) (remove_uapos tbranch) (remove_uapos fbranch)
    | UWrite port idx value => UWrite port idx (remove_uapos value)
    | UUnop ufn1 arg1 => UUnop ufn1 (remove_uapos arg1)
    | UBinop ufn2 arg1 arg2 =>
      UBinop ufn2 (remove_uapos arg1) (remove_uapos arg2)
    | UInternalCall ufn args =>
      UInternalCall {|
        int_name := int_name ufn;
        int_argspec := int_argspec ufn;
        int_retSig := int_retSig ufn;
        int_body := remove_uapos (int_body ufn);
      |} (map (remove_uapos) args)
    | UExternalCall ufn arg => UExternalCall ufn (remove_uapos arg)
    | UAPos p e => remove_uapos e
    | _ => ua
    end.

  (* Assumptions: desugared, no uapos *)
  Fixpoint inline_internal_calls (ua: uact) : uact :=
    match ua with
    | UAssign v ex => UAssign v (inline_internal_calls ex)
    | USeq a1 a2 => USeq (inline_internal_calls a1) (inline_internal_calls a2)
    | UBind v ex body =>
      UBind v (inline_internal_calls ex) (inline_internal_calls body)
    | UIf cond tbranch fbranch =>
      UIf (inline_internal_calls cond) (inline_internal_calls tbranch)
      (inline_internal_calls fbranch)
    | UWrite port idx value => UWrite port idx (inline_internal_calls value)
    | UUnop ufn1 arg1 => UUnop ufn1 (inline_internal_calls arg1)
    | UBinop ufn2 arg1 arg2 =>
      UBinop ufn2 (inline_internal_calls arg1) (inline_internal_calls arg2)
    | UExternalCall ufn arg => UExternalCall ufn (inline_internal_calls arg)
    | UInternalCall ufn args =>
      let args_name_val_pairs :=
        combine (fst (split (int_argspec ufn))) (map inline_internal_calls args)
      in
      fold_right
        (fun arg acc => UBind (fst arg) (snd arg) acc)
        (inline_internal_calls (int_body ufn))
        args_name_val_pairs
    | _ => ua
    end.

  Definition get_impures (ua: uact) : list zipper :=
    find_all_in_uaction ua
      (fun (ua: uact) =>
        match ua with
        | UExternalCall _ _ => true
        | URead _ _ => true
        | UWrite _ _ _ => true
        | _ => false
        end).

  (* Note that we consider reads to be pure *)
  Definition is_pure (ua: uact) : bool :=
    (* get_impures is a bit overkill, but this is unlikely to be a liability in
       practice *)
    List.length (get_impures ua) =? 0.

  Inductive binding :=
  | pure_binding: uact -> binding
  | impure_binding.

  (* Assumptions: desugared, no uapos, no internal calls *)
  (* We have to be careful about the fact that bindings may be pure at some
     point and then become impure and the other way around. *)
  Fixpoint remove_pure_bindings_aux (ua: uact) (Gamma: list (string * binding))
  : uact * list (string * binding) :=
    match ua with
    | UVar var =>
      match list_assoc Gamma var with
      | Some (pure_binding pval) => (pval, Gamma)
      | _ => (* impure or None (the "None" case is used for bindings to already
                managed impure elements) *)
          (UVar var, Gamma)
        end
      | UAssign v ex =>
        let (rex, Gamma') := remove_pure_bindings_aux ex Gamma in
      if (is_pure rex) then (
        match list_assoc Gamma v with
        (* We leave the assignment untouched here! See UIf for explanation. *)
        | Some _ => (UAssign v rex, list_assoc_set Gamma' v (pure_binding rex))
        | None => (* Should never happen in well-formed rules *)
          (UConst (tau := bits_t 0) (Bits.of_nat 0 0), Gamma')
        end
      )
      else (
        match list_assoc Gamma v with
        | Some _ => (UAssign v rex, list_assoc_set Gamma' v impure_binding)
        | None => (* Should never happen in well-formed rules *)
          (UConst (tau := bits_t 0) (Bits.of_nat 0 0), Gamma')
        end
      )
    | UBind v ex body =>
      let (rex, Gamma') := remove_pure_bindings_aux ex Gamma in
      if (is_pure rex) then
        let (rbody, Gamma'') :=
          remove_pure_bindings_aux ex ((v, (pure_binding rex))::Gamma')
        in (
          UBind v (UConst (tau := bits_t 0) (Bits.of_nat 0 0)) rbody,
          tl Gamma''
        )
      else
        let (rbody, Gamma'') :=
          remove_pure_bindings_aux ex ((v, impure_binding)::Gamma')
        in
        (UBind v rex rbody, tl Gamma'')
    | USeq a1 a2 =>
      let (ra1, Gamma') := remove_pure_bindings_aux a1 Gamma in
      let (ra2, Gamma'') := remove_pure_bindings_aux a2 Gamma' in
      (USeq ra1 ra2, Gamma'')
    | UIf cond tbranch fbranch =>
      let (ra1, Gamma_cond) := remove_pure_bindings_aux cond Gamma in
      let (rat, Gamma_t) := remove_pure_bindings_aux tbranch Gamma_cond in
      let (raf, Gamma_f) := remove_pure_bindings_aux fbranch Gamma_cond in
      let Gamma' :=
        fold_right
          (fun v acc => list_assoc_set acc v (
            match list_assoc Gamma_t v, list_assoc Gamma_f v with
            | Some impure_binding, Some impure_binding => impure_binding
            | Some (pure_binding lar), Some (pure_binding lar') =>
              if uaction_func_equiv lar lar' then pure_binding lar
              else pure_binding (UIf ra1 lar lar')
            | Some x, Some y =>
              (* Here, one binding is pure and the other is impure. We end up
                 turning the whole binding resulting from this function into
                 something impure. This is an important special case! The way we
                 currently deal with this situation is by never removing
                 assigns, which might sound like it defeats the purpose of this
                 whole function. However, we know that there is no such
                 situation before the first impure element of our model, which
                 is the only property we need. Assigns before this first impure
                 item can therefore be safely removed. *)
              impure_binding
            | _, _ => (* Should never happen in well-formed rules *)
              impure_binding
            end
          )) Gamma_cond (fst (split Gamma_cond))
      in
      (UIf ra1 rat raf, Gamma')
    | UWrite port idx value =>
      let (ra1, Gamma') := remove_pure_bindings_aux value Gamma in
      (UWrite port idx ra1, Gamma')
    | UUnop ufn1 arg1 =>
      let (ra1, Gamma') := remove_pure_bindings_aux arg1 Gamma in
      (UUnop ufn1 ra1, Gamma')
    | UBinop ufn2 arg1 arg2 =>
      let (ra1, Gamma') := remove_pure_bindings_aux arg1 Gamma in
      let (ra2, Gamma'') := remove_pure_bindings_aux arg2 Gamma' in
      (UBinop ufn2 ra1 ra2, Gamma'')
    | UExternalCall ufn arg =>
      let (ra1, Gamma') := remove_pure_bindings_aux arg Gamma in
      (UExternalCall ufn ra1, Gamma')
    | _ => (ua, Gamma)
    end.

  Definition remove_pure_bindings (ua: uact) : uact * list (string * binding) :=
    remove_pure_bindings_aux ua nil.

  (* Assumption: no impurities nor vars in conditions.
     Maybe some reads though. *)
  Definition extract_conditions (ua: uact) (z: zipper) : list (option uact) :=
    let extract_condition_one_step :=
      fun ua => (
        match ua with
        | UIf cond _ _ => Some cond
        | _ => None
        end
    ) in
    match (access_zipper_tracking ua z extract_condition_one_step) with
    | Some (_, l) => l
    | None => nil
    end.

  Fixpoint merge_conditions (cs: list (option uact)) : uact :=
    match cs with
    | (Some c)::t =>
      UBinop (PrimUntyped.UBits2 PrimUntyped.UAnd) c (merge_conditions t)
    | None::t => merge_conditions t
    | nil => UConst (tau := bits_t 1) (Bits.of_nat 1 1)
    end.

  Definition is_digit (c: ascii) : bool :=
    let n := nat_of_ascii c in
    ((Nat.leb 48 n) && (Nat.leb n 57)).

  Fixpoint digits_to_nat_aux (d: list ascii) (acc: nat) : nat :=
    match d with
    | h::t => digits_to_nat_aux t (10 * acc + (nat_of_ascii h - 48))
    | nil => acc
    end.

  (* Assumption: d contains digits only *)
  Definition digits_to_nat (d: list ascii) : nat :=
    digits_to_nat_aux d 0.

  Definition extract_custom_binding_digits (s: string) : list ascii :=
    String.list_ascii_of_string (String.substring 8 (String.length s - 8) s).

  Scheme Equality for option.
  Definition matches_control_binding_form (s: string) : bool :=
    let maybe_digits := extract_custom_binding_digits s in
    (String.prefix "binding_" s)
    && (negb (Nat.eqb (List.length maybe_digits) 0))
    && (List.forallb is_digit maybe_digits)
    && (negb
      (option_beq
        ascii (Ascii.eqb) (List.hd_error maybe_digits) (Some "0"%char)
      )
    ).

  Definition get_highest_binding_number (ua: uact): nat :=
    let bindings := find_all_in_uaction ua (fun a =>
      match a with
      | UBind _ _ _ => true
      | _ => false
      end
    ) in
    let binding_names := List.map (fun z =>
      match access_zipper ua z with
      | Some (UBind v _ _) => v
      | _ => "" (* Should never happen *)
      end
    ) bindings in
    let matching_bindings :=
      List.filter matches_control_binding_form binding_names
    in
    let binding_numbers :=
      List.map
        (fun s => digits_to_nat (extract_custom_binding_digits s))
        matching_bindings
    in
    List.list_max binding_numbers.

  Definition generate_binding_name (n: nat) : string :=
    String.append "binding_" (NilEmpty.string_of_uint (Init.Nat.to_uint n)).

  Definition is_controlled_binding (s: string) (first_controlled: nat) : bool :=
    (matches_control_binding_form s)
    && (Nat.leb first_controlled (
      digits_to_nat (extract_custom_binding_digits s)
    )).

  Fixpoint simplify_till_impure_aux
    (ua: uact) (first_controlled: nat) (Gamma: list (string * uact))
  (* return type: resulting tree * bindings * impure met *)
  : uact * list (string * uact) * bool :=
    let fc := first_controlled in
    match ua with
    | UVar var =>
      if is_controlled_binding var fc then
        match list_assoc Gamma var with
        | Some pval => (pval, Gamma, false)
        | _ => (UVar var, Gamma, true) (* Should never happen *)
        end
      else (UVar var, Gamma, false)
    | UAssign v ex =>
      let '(rex, Gamma', impure) := simplify_till_impure_aux ex fc Gamma in
      if impure then (UAssign v rex, Gamma', true)
      else (
        match list_assoc Gamma v with
        | Some _ =>
          (UAssign v rex, list_assoc_set Gamma' v rex, false)
        | None => (* Should never happen *)
          (UConst (tau := bits_t 0) (Bits.of_nat 0 0), Gamma', true)
        end
      )
    | UBind v ex body =>
      let '(rex, Gamma', impure) := simplify_till_impure_aux ex fc Gamma in
      if impure then (UBind v rex body, Gamma', true)
      else
        let '(rbody, Gamma'', impure') :=
          simplify_till_impure_aux body fc ((v, rex)::Gamma')
        in
        (UBind v rex rbody, tl Gamma'', impure')
    | USeq a1 a2 =>
      let '(ra1, Gamma', impure) := simplify_till_impure_aux a1 fc Gamma in
      if impure then (USeq ra1 a2, Gamma', true)
      else
        let '(ra2, Gamma'', impure') := simplify_till_impure_aux a2 fc Gamma' in
        (USeq ra1 ra2, Gamma'', impure')
    | UIf cond tbranch fbranch =>
      let '(rac, Gamma_cond, impure) :=
        simplify_till_impure_aux cond fc Gamma
      in
      if impure then (UIf rac tbranch fbranch, Gamma_cond, true)
      else
        let '(rat, Gamma_t, impure') :=
          simplify_till_impure_aux tbranch fc Gamma_cond
        in
        if impure' then (UIf rac rat fbranch, Gamma_t, true)
        else
          let '(raf, Gamma_f, impure'') :=
            simplify_till_impure_aux fbranch fc Gamma_cond
          in
          let Gamma' :=
            fold_right
              (fun v acc => list_assoc_set acc v (
                match list_assoc Gamma_t v, list_assoc Gamma_f v with
                | Some lar, Some lar' =>
                  if uaction_func_equiv lar lar' then lar else UIf rac lar lar'
                | _, _ => (* Should never happen in well-formed rules *)
                  (UConst (tau := bits_t 0) (Bits.of_nat 0 0))
                end
              )) Gamma_cond (fst (split Gamma_cond))
          in
          (UIf rac rat raf, Gamma', impure'')
    | UWrite port idx value =>
      let '(ra1, Gamma', _) := simplify_till_impure_aux value fc Gamma in
      (UWrite port idx ra1, Gamma', true)
    | URead port idx => (URead port idx, Gamma, true)
    | UUnop ufn1 arg1 =>
      let '(ra1, Gamma', impure) := simplify_till_impure_aux arg1 fc Gamma in
      (UUnop ufn1 ra1, Gamma', impure)
    | UBinop ufn2 arg1 arg2 =>
      let '(ra1, Gamma', impure) := simplify_till_impure_aux arg1 fc Gamma in
      if impure then (UBinop ufn2 ra1 arg2, Gamma', true)
      else
        let '(ra2, Gamma'', impure') :=
          simplify_till_impure_aux arg2 fc Gamma'
        in
        (UBinop ufn2 ra1 ra2, Gamma'', impure')
    | UExternalCall ufn arg =>
      let '(ra1, Gamma', _) := simplify_till_impure_aux arg fc Gamma in
      (UExternalCall ufn ra1, Gamma', true)
    | _ => (ua, Gamma, false)
    end.

  Definition simplify_till_impure (ua: uact) (first_controlled: nat) : uact :=
    let '(res, _, _) := simplify_till_impure_aux ua first_controlled nil in res.

  Inductive assigns :=
  | assign_nil
  | assign (var: string) (val: uact) (queue: assigns)
  | conditional_assign
    (cond: uact) (lt: assigns) (lf: assigns) (queue: assigns).

  Inductive failures :=
  | not_a_failure
  | failure
  | conditional_failure
    (cond: uact) (lt: failures) (lf: failures) (queue: failures).

  Fixpoint append_assigns (a1 a2: assigns) : assigns :=
    match a1 with
    | assign_nil => a2
    | assign var val q => append_assigns q (assign var val a2)
    | conditional_assign cond lt lf q =>
      append_assigns q (conditional_assign cond lt lf a2)
    end.

  Fixpoint append_failures (f1 f2: failures) : failures :=
    match f1 with
    | not_a_failure => f2
    | failure => failure
    | conditional_failure cond lt lf q =>
      conditional_failure cond lt lf (append_failures q f2)
    end.

  (* Limited filter function (variable name only) for assigns, required for
     dealing with shadowing *)
  Fixpoint assigns_filter (f: string -> bool) (a: assigns) : assigns :=
    match a with
    | assign_nil => assign_nil
    | assign var val q =>
      if (f var) then assign var val (assigns_filter f q)
      else assigns_filter f q
    | conditional_assign cond lt lf q =>
      conditional_assign
        cond (assigns_filter f lt) (assigns_filter f lf) (assigns_filter f q)
    end.

  (* TODO shared precondition: no USugar, no UInternalCall, no UApos *)

  (* Pure bindings need to have been forwarded as much as possible *)
  (* Precondition: no impure elements *)
  (* Precondition: no uncontrolled UVars *)
  Fixpoint remove_assigns_aux (ua: uact) : uact :=
    match ua with
    | UAssign _ _ => UConst (tau := bits_t 0) (Bits.of_nat 0 0)
    | UBind _ _ body => body
    | USeq a1 a2 => USeq (remove_assigns_aux a1) (remove_assigns_aux a2)
    | UIf cond tbranch fbranch =>
      UIf
        (remove_assigns_aux cond) (remove_assigns_aux tbranch)
        (remove_assigns_aux fbranch)
    | UBinop ufn2 arg1 arg2 =>
      UBinop ufn2 (remove_assigns_aux arg1) (remove_assigns_aux arg2)
    | UUnop ufn1 arg1 => UUnop ufn1 (remove_assigns_aux arg1)
    | _ => ua
    end.

  (* Precondition: no uncontrolled UVars *)
  Definition remove_assigns (ua: uact) : uact :=
    match ua with
    | UWrite port reg ex => UWrite port reg (remove_assigns_aux ex)
    | UExternalCall ufn arg => UExternalCall ufn (remove_assigns_aux arg)
    | _ => UConst (tau := bits_t 0) (Bits.of_nat 0 0) (* Includes URead *)
    end.

  (* Precondition: no impure elements *)
  (* Precondition: no uncontrolled UVars *)
  (* Precondition: no assigns/binds *)
  Fixpoint remove_failures_aux (ua: uact) : uact :=
    match ua with
    | USeq a1 a2 => USeq (remove_failures_aux a1) (remove_failures_aux a2)
    | UIf cond tbranch fbranch =>
      UIf
        (remove_failures_aux cond) (remove_failures_aux tbranch)
        (remove_failures_aux fbranch)
    | UBinop ufn a1 a2 =>
      UBinop ufn (remove_failures_aux a1) (remove_failures_aux a2)
    | UUnop ufn a => UUnop ufn (remove_failures_aux a)
    | UError _ => UConst (tau := bits_t 0) (Bits.of_nat 0 0)
    | UFail _ => UConst (tau := bits_t 0) (Bits.of_nat 0 0)
    | _ => ua
    end.

  (* Precondition: impure root and no other impure elements *)
  (* Precondition: no uncontrolled UVars *)
  (* Precondition: no assigns/binds *)
  Definition remove_failures (ua: uact) : uact :=
    match ua with
    | UWrite port reg ex => UWrite port reg (remove_failures_aux ex)
    | UExternalCall ufn arg => UExternalCall ufn (remove_failures_aux arg)
    | URead reg port => URead reg port
    | _ => UConst (tau := bits_t 0) (Bits.of_nat 0 0)
    end.

  (* Precondition: no impure elements *)
  (* Precondition: All UVar replaced except if controlled *)
  Fixpoint extract_assigns_aux (ua: uact) : assigns :=
    match ua with
    | UAssign v ex => assign v ex assign_nil
    | UBind v ex body =>
      let tr := extract_assigns_aux body in
      (* Remove all assigns to v at the end: shadowing *)
      assigns_filter (fun name => negb (String.eqb name v)) tr
    | USeq a1 a2 =>
      append_assigns (extract_assigns_aux a1) (extract_assigns_aux a2)
    | UIf cond tb fb =>
      let rt := extract_assigns_aux tb in
      let rf := extract_assigns_aux fb in
      match rt, rf with
      | assign_nil, assign_nil => assign_nil
      | _, _ =>
        conditional_assign (remove_failures (remove_assigns cond)) rt rf
        assign_nil
      end
    | UUnop _ a1 => extract_assigns_aux a1
    | UBinop _ a1 a2 =>
      append_assigns (extract_assigns_aux a1) (extract_assigns_aux a2)
    | _ => assign_nil
    end.

  (* Precondition: impure root *)
  Definition extract_assigns (ua: uact) : assigns :=
    match ua with
    | UWrite _ _ ex => extract_assigns_aux ex
    | UExternalCall _ arg => extract_assigns_aux arg
    | _ => assign_nil (* Includes URead *)
    end.

  (* Precondition: no impure elements *)
  (* Precondition: no uncontrolled UVars *)
  Fixpoint extract_failures_aux (ua: uact) : failures :=
    match ua with
    | UBind _ val body =>
      append_failures (extract_failures_aux val) (extract_failures_aux body)
    | UAssign _ val => extract_failures_aux val
    | USeq a1 a2 =>
      append_failures (extract_failures_aux a1) (extract_failures_aux a2)
    | UIf cond tb fb =>
      (* TODO cond may contain assigns, check if managed correctly (also remove
         failures) *)
      let cf := extract_failures_aux cond in
      let tf := extract_failures_aux tb in
      let ff := extract_failures_aux fb in
      match tf, ff with
      | not_a_failure, not_a_failure => cf
      | _, _ =>
        append_failures
          cf (conditional_failure (remove_failures cond) tf ff not_a_failure)
      end
    | UBinop ufn a1 a2 =>
      append_failures (extract_failures_aux a1) (extract_failures_aux a2)
    | UUnop ufn a => extract_failures_aux a
    | UError _ => failure
    | UFail _ => failure
    | _ => not_a_failure
    end.

  (* Precondition: impure root and no other impure elements *)
  (* Precondition: no uncontrolled UVars *)
  (* Precondition: no assigns/binds *)
  Definition extract_failures (ua: uact) : failures :=
    match ua with
    | UWrite port reg ex => extract_failures_aux ex
    | UExternalCall ufn arg => extract_failures_aux arg
    | _ => not_a_failure (* Includes URead *)
    end.

  Fixpoint assigns_to_action (a: assigns) : uact :=
    match a with
    | assign_nil => UConst (tau := bits_t 0) (Bits.of_nat 0 0)
    | assign var val q => USeq (UAssign var val) (assigns_to_action q)
    | conditional_assign cond lt lf q =>
      USeq
        (UIf cond (assigns_to_action lt) (assigns_to_action lf))
        (assigns_to_action q)
    end.

  Fixpoint prepend_condition (f: failures) (cond: uact) : failures :=
    conditional_failure cond f not_a_failure not_a_failure.

  Fixpoint failures_to_action (f: failures) : uact :=
    match f with
    | not_a_failure => UConst (tau := bits_t 1) (Bits.of_nat 1 0)
    | failure => UConst (tau := bits_t 1) (Bits.of_nat 1 1)
    | conditional_failure cond tf ff q =>
      UBinop
        (PrimUntyped.UBits2 PrimUntyped.UOr)
        (UBinop
          (PrimUntyped.UBits2 PrimUntyped.UOr)
          (
            UBinop
              (PrimUntyped.UBits2 PrimUntyped.UAnd) cond (failures_to_action tf)
          )
          (
            UBinop
              (PrimUntyped.UBits2 PrimUntyped.UAnd)
              (UUnop (PrimUntyped.UBits1 PrimUntyped.UNot) cond)
              (failures_to_action ff)
          )
        )
        (failures_to_action q)
    end.

  (* Precondition: ua's root is impure *)
  Definition remove_impure (ua: uact) (last_controlled: nat) : uact * nat :=
    match ua with
    | UExternalCall _ _ =>
      (UVar (generate_binding_name (S last_controlled)), last_controlled + 1)
    | URead _ _ =>
      (UVar (generate_binding_name (S last_controlled)), last_controlled + 1)
    | _ => (* Includes UWrite *)
      (UConst (tau := bits_t 0) (Bits.of_nat 0 0), last_controlled)
    end.

  (* Precondition: no impurity. *)
  (* Precondition: only controlled variables. *)
  (* Removes UAssigns, UBinds and USeq *)
  Fixpoint cleanup (ua: uact) : uact :=
    match ua with
    | UAssign _ _ => UConst (tau := bits_t 0) (Bits.of_nat 0 0)
    | UBind _ _ _ => UConst (tau := bits_t 0) (Bits.of_nat 0 0)
    | USeq _ a2 =>
      (* We only care about the return value which a1 can't possibly impact
         anymore *)
      cleanup a2
    | UIf cond tb fb => UIf (cleanup cond) (cleanup tb) (cleanup fb)
    | UBinop ufn a1 a2 => UBinop ufn (cleanup a1) (cleanup a2)
    | UUnop ufn a => UUnop ufn (cleanup a)
    | _ => ua
    end.

  (* Precondition: ua's root is impure *)
  Definition get_action (ua: uact) (next_free_binding: nat) : uact :=
    match ua with
    | UExternalCall fn arg =>
      UAssign
        (generate_binding_name next_free_binding)
        (UExternalCall fn (cleanup arg))
    | URead port var =>
      UAssign
        (generate_binding_name next_free_binding)
        (URead port var)
    | UWrite port var val => UWrite port var (cleanup val)
    | _ => UConst (tau := bits_t 0) (Bits.of_nat 0 0) (* Should never happen *)
    end.

  (* list (reg * (cond * bind_name)) *)
  Definition read_log := list (reg_t * (uact * string)).
  (* list (reg * (cond * val)) *)
  Definition write_log := list (reg_t * (uact * uact)).
  (* list (ufn * (cond * bind_name * arg)) *)
  Definition extcall_log := list (ext_fn_t * (uact * string * uact)).

  Record action_logs := mkActions {
    read0s: read_log;
    read1s: read_log;
    write0s: write_log;
    write1s: write_log;
    extcalls: extcall_log;
  }.

  Definition extract_write0_cond (al: action_logs) (reg: reg_t) :=
    match list_assoc (write0s al) reg with
    | None => None
    | Some (cond, _) => Some cond
    end.
  Definition extract_write1_cond (al: action_logs) (reg: reg_t) :=
    match list_assoc (write1s al) reg with
    | None => None
    | Some (cond, _) => Some cond
    end.
  Definition extract_read1_cond (al: action_logs) (reg: reg_t) :=
    match list_assoc (read1s al) reg with
    | None => None
    | Some (cond, _) => Some cond
    end.

  Fixpoint or_conds (conds: list uact) :=
    List.fold_left
      (fun acc c =>
        match acc with
        | None => Some c
        | Some x => Some (UBinop (PrimUntyped.UBits2 PrimUntyped.UOr) c x)
        end
      )
      conds None.

  Definition merge_failures_list (action_cond: uact) (conds: list uact) :=
    match or_conds conds with
    | None => None
    | Some x =>
      Some (UBinop (PrimUntyped.UBits2 PrimUntyped.UOr) action_cond x)
    end.

  Definition list_options_to_list (l: list (option uact)) : list uact :=
    List.map
      (fun i =>
        match i with
        | Some x => x
        | None => (* Should never happen *)
          (UConst (tau := bits_t 0) (Bits.of_nat 0 0))
        end
      )
      (List.filter
        (fun i => match i with None => false | Some _ => true end) l
      ).

  Definition upd_read0 (al: action_logs) (nl: read_log) := {|
    read0s := nl; read1s := read1s al; write0s := write0s al;
    write1s := write1s al; extcalls := extcalls al
  |}.
  Definition upd_read1 (al: action_logs) (nl: read_log) := {|
    read0s := read0s al; read1s := nl; write0s := write0s al;
    write1s := write1s al; extcalls := extcalls al
  |}.
  Definition upd_write0 (al: action_logs) (nl: write_log) := {|
    read0s := read0s al; read1s := read1s al; write0s := nl;
    write1s := write1s al; extcalls := extcalls al
  |}.
  Definition upd_write1 (al: action_logs) (nl: write_log) := {|
    read0s := read0s al; read1s := read1s al; write0s := write0s al;
    write1s := nl; extcalls := extcalls al
  |}.
  Definition upd_extcalls (al: action_logs) (nl: extcall_log) := {|
    read0s := read0s al; read1s := read1s al; write0s := write0s al;
    write1s := write1s al; extcalls := nl
  |}.

  Definition add_read0
    (al: action_logs) (cond: uact) (reg: reg_t) (fresh_name: string)
  (* Returns modified action_logs, failure conditions, used name *)
  : action_logs * option uact * string :=
    let previous_wr0 := extract_write0_cond al reg in
    let previous_wr1 := extract_write1_cond al reg in
    let failure_cond :=
      merge_failures_list
        cond (list_options_to_list [previous_wr0; previous_wr1])
    in
    match list_assoc (read0s al) reg with
    | None => (
      upd_read0 al (list_assoc_set (read0s al) reg (cond, fresh_name)),
      failure_cond, fresh_name
    )
    | Some (cond', name) => (
      upd_read0 al
        (list_assoc_set (read0s al) reg
          (UBinop (PrimUntyped.UBits2 PrimUntyped.UOr) cond cond', name)
        ),
      failure_cond, name
    )
    end.

  Definition add_read1
    (al: action_logs) (cond: uact) (reg: reg_t) (fresh_name: string)
  (* Returns modified action_logs, failure conditions, used name *)
  : action_logs * option uact * string :=
    let previous_wr1 := extract_write1_cond al reg in
    let failure_cond :=
      merge_failures_list cond (list_options_to_list [previous_wr1])
    in
    match list_assoc (read1s al) reg with
    | None => (
      upd_read1 al (list_assoc_set (read1s al) reg (cond, fresh_name)),
      failure_cond, fresh_name
    )
    | Some (cond', name) => (
      upd_read1 al
        (list_assoc_set (read1s al) reg
          (UBinop (PrimUntyped.UBits2 PrimUntyped.UOr) cond cond', name)
        ),
      failure_cond, name
    )
    end.

  Definition add_write0 (al: action_logs) (cond: uact) (val: uact) (reg: reg_t)
  (* Returns modified action_logs, failure conditions *)
  : action_logs * option uact :=
    let previous_wr0 := extract_write0_cond al reg in
    let previous_wr1 := extract_write1_cond al reg in
    let previous_rd1 := extract_read1_cond al reg in
    let failure_cond :=
      merge_failures_list
        cond (list_options_to_list [previous_wr0; previous_wr1; previous_rd1])
    in
    (* Somewhat redundant with extract_write0_cond *)
    match list_assoc (write0s al) reg with
    | None => (
      upd_write0 al (list_assoc_set (write0s al) reg (cond, val)),
      failure_cond
    )
    | Some (cond', val') => (
      upd_write0 al
        (list_assoc_set (write0s al) reg
          (UBinop (PrimUntyped.UBits2 PrimUntyped.UOr) cond cond',
           UIf cond val val'
          )
        ),
      failure_cond
    )
    end.

  Definition add_write1 (al: action_logs) (cond: uact) (val: uact) (reg: reg_t)
  (* Returns modified action_logs, failure conditions *)
  : action_logs * option uact :=
    let previous_wr1 := extract_write1_cond al reg in
    let failure_cond :=
      merge_failures_list cond (list_options_to_list [previous_wr1])
    in
    (* Somewhat redundant with extract_write0_cond *)
    match list_assoc (write1s al) reg with
    | None => (
      upd_write1 al (list_assoc_set (write1s al) reg (cond, val)),
      failure_cond
    )
    | Some (cond', val') => (
      upd_write1 al
        (list_assoc_set (write1s al) reg
          (UBinop (PrimUntyped.UBits2 PrimUntyped.UOr) cond cond',
           UIf cond val val'
          )
        ),
      failure_cond
    )
    end.

  Definition add_extcall
    (al: action_logs) (ufn: ext_fn_t) (cond: uact) (arg: uact)
    (fresh_name: string)
  : action_logs :=
    upd_extcalls al ((ufn, (cond, fresh_name, arg))::(extcalls al)).

  Definition merge_uacts (cond: uact) (ua1 ua2: option uact) : option uact :=
    match ua1, ua2 with
    | Some x, Some y => Some (UIf cond x y)
    | _, _ => None
    end.

  Definition merge_Gammas (cond: uact) (g1 g2: list (string * uact))
  : list (string * uact) :=
    (* We can safely assume that both gammas contain the same variables in the
       same order. *)
    List.map
      (fun '((str, ua1), (_, ua2)) =>
        if uaction_func_equiv ua1 ua2 then (str, ua1)
        else (str, UIf cond ua1 ua2)
      )
      (List.combine g1 g2).

  (* TODO merge with merge_failures_list? *)
  Definition merge_failures (f1 f2: option uact) : option uact :=
    match f1, f2 with
    | None, None => None
    | Some x, None => Some x
    | None, Some x => Some x
    | Some x, Some y => Some (UBinop (PrimUntyped.UBits2 PrimUntyped.UOr) x y)
    end.

  Definition reduce (ua: option uact) : uact :=
    match ua with
    | None => UConst (tau := bits_t 0) (Bits.of_nat 0 0)
    | Some x => x
    end.

  Fixpoint distill
    (* No need to pass failures *)
    (ua: uact) (Gamma: list (string * uact)) (guard: uact) (al: action_logs)
    (last_controlled: nat)
    (* Returns value, context, failure condition, action_logs,
       last_controlled *)
  : option uact * (list (string * uact)) * (option uact) * action_logs * nat :=
    let lc := last_controlled in
    match ua with
    | UBind var val body =>
      let '(ret_val, Gamma_val, failures_val, al_val, lc_val) :=
        distill val Gamma guard al lc
      in
      let '(ret_body, Gamma_body, failures_body, al_body, lc_body) :=
        distill
          body (list_assoc_set Gamma_val var (reduce ret_val)) guard al lc_val
      in
      (None, List.skipn 1 Gamma_body, (* Remove the binding to var *)
       merge_failures failures_val failures_body, al_body, lc_body)
    | UAssign var val =>
      let '(ret_val, Gamma_val, failures_val, al_val, lc_val) :=
        distill val Gamma guard al lc
      in
      (None, list_assoc_set Gamma_val var (reduce ret_val), failures_val,
       al_val, lc_val)
    | UVar var =>
      (* TODO deal correctly with controlled bindings *)
      (list_assoc Gamma var, Gamma, None, al, lc)
    | USeq a1 a2 =>
      let '(_, Gamma_a1, failures_a1, al_a1, lc_a1) :=
        distill a1 Gamma guard al lc
      in
      let '(ret_a2, Gamma_a2, failures_a2, al_a2, lc_a2) :=
        distill a2 Gamma_a1 guard al_a1 lc_a1
      in
      (ret_a2, Gamma_a2, merge_failures failures_a1 failures_a2, al_a2, lc_a2)
    | UIf cond tb fb =>
      let '(ret_cond, Gamma_cond, failures_cond, al_cond, lc_cond) :=
        distill cond Gamma guard al lc
      in
      let guard_tb :=
        UBinop (PrimUntyped.UBits2 PrimUntyped.UAnd) guard (reduce ret_cond)
      in
      let guard_fb :=
        UBinop (PrimUntyped.UBits2 PrimUntyped.UAnd)
          guard (UUnop (PrimUntyped.UBits1 PrimUntyped.UNot) (reduce ret_cond))
      in
      let '(ret_tb, Gamma_tb, failures_tb, al_tb, lc_tb) :=
        distill tb Gamma_cond guard_tb al_cond lc_cond
      in
      let '(ret_fb, Gamma_fb, failures_fb, al_fb, lc_fb) :=
        (* We use al_tb here even though we know that none of the actions added
           by the other branch can impact those from this branch as they are
           mutually exclusive. However, this way, we don't have to deal with
           action_logs merging. *)
        distill fb Gamma_cond guard_fb al_tb lc_tb
      in
      (merge_uacts cond ret_tb ret_fb,
       merge_Gammas cond Gamma_fb Gamma_tb,
       merge_failures failures_tb failures_fb, al_fb, lc_fb)
    | UUnop ufn a =>
      let '(ret_a, Gamma_a, failures_a, al_a, lc_a) :=
        distill a Gamma guard al lc
      in
      (Some (UUnop ufn (reduce ret_a)), Gamma_a, failures_a, al_a, lc_a)
    | UBinop ufn a1 a2 =>
      let '(ret_a1, Gamma_a1, failures_a1, al_a1, lc_a1) :=
        distill a1 Gamma guard al lc
      in
      let '(ret_a2, Gamma_a2, failures_a2, al_a2, lc_a2) :=
        distill a2 Gamma_a1 guard al_a1 lc_a1
      in
      (Some (UBinop ufn (reduce ret_a1) (reduce ret_a2)), Gamma_a2,
       merge_failures failures_a1 failures_a2, al_a2, lc_a2)
    | UInternalCall ufn args =>
      let '(arg_values, Gamma_args, failure_args, al_args, lc_args) := (
        List.fold_left
          (fun '(values, Gamma_p, failures_p, al_p, lc_p) a =>
            let '(val_n, Gamma_n, failure_n, al_n, lc_n) :=
              distill a Gamma_p guard al_p lc_p
            in (
              val_n::values, Gamma_n, merge_failures failure_n failures_p,
              al_n, lc_n
            )
          )
          args
          ([], Gamma, None, al, lc)
      ) in
      let args_name_val_pairs :=
        combine
          (fst (split (int_argspec ufn)))
          (* We filter Nones out to please Coq. It isn't strictly required as we
             know that a value is assigned to each argument in well formed
             code. *)
          (List.map
            (fun i =>
              match i with
              | None => (* Should never happen *)
                UConst (tau := bits_t 0) (Bits.of_nat 0 0)
              | Some x => x
              end
            )
            (List.filter
              (fun x => match x with None => false | _ => true end)
              arg_values
            )
          )
      in
      let Gamma_in :=
        (* Initial state of the local context of the function *)
        List.fold_left
          (fun Gamma_acc name_value_couple => name_value_couple::Gamma_acc)
          args_name_val_pairs []
      in
      let '(ret_ic, _, failure_ic, al_ic, lc_ic) :=
        distill (int_body ufn) Gamma_in guard al_args lc_args
      in
      (ret_ic, Gamma_args, merge_failures failure_ic failure_args, al_ic,
       lc_ic)
    | UAPos _ e => distill e Gamma guard al lc
    | URead port reg =>
      let fresh_name := generate_binding_name (S lc) in
      let '(modified_al, failure_read, used_name) :=
        match port with
        | P0 => add_read0 al guard reg fresh_name
        | P1 => add_read1 al guard reg fresh_name
        end
      in
      let new_lc := if String.eqb fresh_name used_name then S lc else lc in
      (Some (UVar (used_name)), Gamma, failure_read, modified_al, new_lc)
    | UWrite port reg val =>
      let '(ret_val, Gamma_val, failures_val, actions_val, lc_val) :=
        distill val Gamma guard al lc
      in
      let '(al_wr, failure_wr) :=
        match port with
        | P0 => add_write0 actions_val guard (reduce ret_val) reg
        | P1 => add_write1 actions_val guard (reduce ret_val) reg
        end
      in
      (None, Gamma_val, merge_failures failures_val failure_wr, actions_val,
       lc_val)
    | UExternalCall ufn arg =>
      let '(ret_arg, Gamma_arg, failures_arg, actions_arg, lc_arg) :=
        distill arg Gamma guard al lc
      in
      let fresh_name := generate_binding_name (S lc) in
      let new_al := add_extcall al ufn guard arg fresh_name in
      (Some (UVar fresh_name), Gamma_arg, failures_arg, new_al, S lc)
    | UError _ =>
      (None, Gamma, Some (UConst (tau := bits_t 1) (Bits.of_nat 1 1)), al, lc)
    | UFail _ =>
      (None, Gamma, Some (UConst (tau := bits_t 1) (Bits.of_nat 1 1)), al, lc)
    | _ => (Some ua, Gamma, None, al, lc)
    end.

  (* Precondition: impures sorted by order of occurrence. It is meant to use the
     output of find_all_in_xxx. *)
  (* TODO pick better variable names *)
  Fixpoint to_list_of_impures_aux
    (ua: uact) (first_controlled: nat) (last_controlled: nat)
    (impures: list zipper)
  (* Return type: condition + impures, failures (includes condition, see
     inductive definition), last registered controlled binding, modified
     subtree. *)
  : list (uact * uact) * failures * nat * uact :=
    match impures with
    | nil => (nil, not_a_failure, last_controlled, ua)
    | h::t =>
      let ua' := simplify_till_impure ua first_controlled in
      let cond := merge_conditions (extract_conditions ua' h) in
      (* An impure may contain other impures (e.g. write0(x, read0(y))). Deal
         with these first. Note how we pass a subtree instead of using ua
         directly. *)
      let subtree := access_zipper ua' h in
      match subtree with
      | None => (* Should never happen *)
        (nil, not_a_failure, last_controlled, ua)
      | Some s =>
        (* TODO transform initial list to match decreasing heuristics. Not
             sufficient. *)
        let h_depth := get_depth h in
        let impures_in_subtree_count := List.length (get_impures s) in
        let impures_in_subtree :=
          List.map
            (remove_top h_depth)
            (List.firstn impures_in_subtree_count t)
        in
        let '(actions, deep_failures, last_controlled', subtree') :=
          to_list_of_impures_aux
            s first_controlled last_controlled impures_in_subtree
        in
        (* Prepend sublist of actions with the local condition. *)
        let actions' :=
          List.map (fun '(c, a) =>
            (merge_conditions [Some c; Some cond], a)
          ) actions
        in
        (* Prepend list of failures with the local condition. *)
        let deep_failures' := prepend_condition deep_failures cond in
        (* We may now remove the impures removed by the the recursive call. *)
        let t' := List.skipn (List.length actions') t in
        (* We need to ensure that the contents of the impure have been fully
           simplified. Some simplifications have already been performed as part
           of the recursive call, but some work is still required for what comes
           after the last impure child. Since there is no impure,
           simplify_till_impure simplifies everything. *)
        let subtree'' := simplify_till_impure subtree' first_controlled in
        (* The impure elements that we remove may contain assignments. We don't
           want assignments to remain in the action and we can't leave anything
           impure in the tree, yet the effects of these assignments have an
           impact on the rest of the rule. We therefore have to extract them. *)
        let assignments_in_subtree := extract_assigns subtree'' in
        (* We already extracted the failures of impure children of h as part of
           the recursive call. This takes care of the rest. *)
        let failures_in_subtree :=
          prepend_condition (extract_failures subtree'') cond
        in
        (* Merge failures from all sources. *)
        let fails := append_failures deep_failures' failures_in_subtree in
        (* Simplify subtree. *)
        let h_cleaned := remove_failures (remove_assigns subtree'') in
        let h_action := get_action h_cleaned last_controlled' in
        let (h_replacement, last_controlled'') :=
          remove_impure h_cleaned last_controlled'
        in
        (* We remove anything impure from the tree, leaving instead a sequence
           of assignments eventually followed by a controlled variable
           containing the value corresponding to the initial impure if it was a
           read or an external call. *)
        match
          replace_at_zipper
            ua' h
            (USeq (assigns_to_action assignments_in_subtree) h_replacement)
        with
        | None => (* Should never happen *)
          (nil, not_a_failure, last_controlled, ua')
        | Some updated_tree =>
          (* Deal with the other impures located at the same level as h. *)
          let '(al, f, lc, rt) :=
            to_list_of_impures_aux
              updated_tree first_controlled last_controlled'' t'
          in
          (* We don't need to pass the name of the action corresponding to h as
             the list is ordered. *)
          (al ++ ((cond, h_action)::actions'), append_failures fails f, lc, rt)
        end
      end
    end.

  Definition to_list_of_impures (ua: uact) : list (uact * uact) * uact * nat :=
    let bn := get_highest_binding_number ua in
    let (res, f, last_controlled, updated_ua) :=
      to_list_of_impures_aux ua bn bn nil (get_impures (prepare_uaction ua)) nil
    (* Failures with no impure ancestors were ignored prior to this point. *)
    let remaining_failures := extract_failures updated_ua in
    in (res, append_failures f remaining_failures, last_controlled).

  (* Implicit failures *)
  Record reg_actions_ledger_atom := mk_reg_actions_ledger_atom {
    read0: list uact;
    read1: list uact;
    write0: list uact;
    write1: list uact;
  }.
  Definition reg_actions_ledger := list (string * reg_actions_ledger_atom).

  Fixpoint write_conditions_list_to_failures (l: list uact) :=
    match l with
    | h::h'::t =>
      let fail_cond :=
        List.fold_left
        (fun i acc => (UBinop (PrimUntyped.UBits2 PrimUntyped.UAnd) acc i))
        t
        (UBinop (PrimUntyped.UBits2 PrimUntyped.UAnd) h h')
      in
      conditional_failure fail_cond failure not_a_failure not_a_failure
    | _ => not_a_failure
    end.

  Fixpoint detect_double_writes (al: reg_actions_ledger) : failures :=
    append_failures
      (write_conditions_list_to_failures (write0 al))
      (write_conditions_list_to_failures (write1 al)).

  Definition merge_atoms (a1 a2: reg_actions_ledger) : reg_actions_ledger := {|
    read0 := read0 a1 ++ read0 a2;
    read1 := read1 a1 ++ read1 a2;
    write0 := write0 a1 ++ write0 a2;
    write1 := write1 a1 ++ write1 a2;
  |}.

  Definition merge_atoms_option
    (a: reg_actions_ledger) (am: option reg_actions_ledger)
  : reg_actions_ledger :=
    match am with
    | None => a
    | Some x => merge_atoms a x
    end.

  Fixpoint to_reg_actions_ledger (act: list (uact * uact)) : actions_ledger :=
    List.fold_left
      (fun '(c, a) acc =>
        let prev_atom := list_assoc acc reg in
        let temp_atom :=
          match a with
          | URead port reg =>
            match port with
            | P0 => {| read0 := [c]; read1 := []; write0 := []; write1 := []; |}
            | P1 => {| read0 := []; read1 := [c]; write0 := []; write1 := []; |}
            end
          | UWrite port reg val =>
            match port with
            | P0 => {| read0 := []; read1 := []; write0 := [c]; write1 := []; |}
            | P1 => {| read0 := []; read1 := []; write0 := []; write1 := [c]; |}
            end
          | _ =>  (* Should only occur for external calls *)
            {| read0 := []; read1 := []; write0 := []; write1 := []; |}
          end
        in
        merge_atoms_option temp_atom prev_atom
      )
      act
      nil.

  Fixpoint rename_in_uact (from to: string) (ua: uact) :=
    match ua with
    | UVar v =>
      if String.eqb from v then UVar to else UVar v
    | UIf cond tb fb =>
      UIf
        (rename_in_uact from to cond) (rename_in_uact from to tb)
        (rename_in_uact from to fb)
    | UBinop ufn a1 a2 =>
      UBinop ufn (rename_in_uact from to a1) (rename_in_uact from to a2)
    | UUnop ufn a => UUnop ufn (rename_in_uact a)
    | _ => ua
    end.

  Fixpoint rename_binding (from to: string) (al: list (uact * uact))
  : list (uact * uact) :=
    match al with
    | [] => []
    | (c, a)::t =>
      (rename_in_uact from to c, rename_in_uact from to a)::(
        rename_binding from to t
      )
    end.

  (* Actions list simplification stage: e.g. merge multiple writes occuring in
     the same rule. *)
  Fixpoint detect_wrong_orderings_aux
    (actions: uact * uact) (ledger: actions_ledger)
  :

  Definition detect_wrong_orderings (actions: uact * uact) :=.

  Definition integrate_failures (actions: list (uact * uact)) (f: failures) :=
    let failure_cond := failures_to_action f in
    List.map (fun '(c, a) =>
      (f, a)
    ) nil actions.

  Definition merge_rules (rules: list (uact * uact)) :=.

  (* We don't return the next binding: we deal with the identifiers merging
     tedium during the rules merging phase only. *)
  Definition extract_impures_from_rule (r: rule) : list (uact * uact) :=
    normalize_aux (prepare_uaction ua) (get_highest_binding_number ua + 1).

  Definition extract_impures_from_rules (lr: list rules)
  : list (list (uact * uact)) :=
    List.map extract_impures_from_rules lr.

  Definition is_in_normal_form (ua: uact) : bool :=
    find_all_in_uaction ().
  Close Scope nat.
End Normalize.
