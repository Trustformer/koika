(*! Proving | Transformation of a schedule to a single rule with a limited
    syntax !*)
Require Import Coq.Program.Equality.
Require Import Koika.BitsToLists Koika.Primitives Koika.Utils Koika.Zipper.
Open Scope nat.

(* In this file, whenever side-effects or equivalence are mentionned, bear in
   mind that we do not care about the contents of the logs, but rather about
   the state of the model at the end of the cycle. For example, reading an
   otherwise unaccessed variable is not considered a side-effect. *)

(* The normal form in question is a single rule (instead of a schedule)
   containing a sequence of writes guarded by a single if each. *)

Section Normalize.
  Context {pos_t var_t fn_name_t reg_t ext_fn_t: Type}.
  Context {reg_t_eq_dec: EqDec reg_t}.
  Context {var_t_eq_dec: EqDec var_t}.
  Context {ext_fn_t_eq_dec: EqDec ext_fn_t}.

  (* A. Rule simplification *)
  (* A.1. Early simplification pass - we start by simplifying some elements that
     do not pose any issues with regard to purity *)
  (* Assumption: desugared *)
  Fixpoint remove_uapos
    (ua: uaction pos_t var_t fn_name_t reg_t ext_fn_t)
  : uaction pos_t var_t fn_name_t reg_t ext_fn_t :=
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
  Fixpoint inline_internal_calls
    (ua: uaction pos_t var_t fn_name_t reg_t ext_fn_t)
  : uaction pos_t var_t fn_name_t reg_t ext_fn_t :=
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

  (* XXX Note that we consider reads to be pure *)
  Definition is_pure (ua: uaction pos_t var_t fn_name_t reg_t ext_fn_t)
  : bool :=
    (* find_all_in_uaction is a bit overkill, but this is unlikely to be a
       liability in practice *)
    List.length
      (find_all_in_uaction ua
        (fun (ua: uaction pos_t var_t fn_name_t reg_t ext_fn_t) =>
          match ua with
          | UExternalCall _ _ => true
          | UWrite _ _ _ => true
          | _ => false
          end))
    =? 0.

  Inductive binding :=
  | pure_binding: uaction pos_t var_t fn_name_t reg_t ext_fn_t -> binding
  | impure_binding.

  (* Assumptions: desugared, no uapos, no internal calls *)
  (* We have to be careful about the fact that bindings may be pure at some
     point and then become impure and the other way around. *)
  Fixpoint remove_pure_bindings_aux
    (ua: uaction pos_t var_t fn_name_t reg_t ext_fn_t)
    (Gamma: list (var_t * binding))
  : uaction pos_t var_t fn_name_t reg_t ext_fn_t * list (var_t * binding) :=
    match ua with
    | UVar var =>
      match list_assoc Gamma var with
      | Some (pure_binding pval) => (pval, Gamma)
      | Some impure_binding => (UVar var, Gamma)
      | None => (* Should never happen in well-formed rules *)
        (UConst (tau := bits_t 0) (Bits.of_nat 0 0), Gamma)
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
              (* Here, a pure binding is turned into an impure one. This is a
                 very special case! The way we currently deal with this
                 situation is by never removing assigns, which might sound
                 like it defeats the purpose of this whole function. However,
                 we know that there is no such situation before the first
                 impure element of our model, which is the only property we
                 need. Assigns before this first impure item can therefore be
                 safely removed. *)
              (impure_binding)
            | _, _ => (* Should never happen in well-formed rules *)
              (impure_binding)
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

  Definition remove_pure_bindings
    (ua: uaction pos_t var_t fn_name_t reg_t ext_fn_t)
  : uaction pos_t var_t fn_name_t reg_t ext_fn_t * list (var_t * binding) :=
    remove_pure_bindings_aux ua nil.

  (* A.2. Extcalls management *)
  Definition prepare_extcalls_dumping_ground
    (ua: uaction pos_t var_t fn_name_t reg_t ext_fn_t)
  : uaction pos_t var_t fn_name_t reg_t ext_fn_t :=
    USeq (UConst (tau := bits_t 0) (Bits.of_nat 0 0)) ua.

  Definition extract_condition_one_step
    (ua: uaction pos_t var_t fn_name_t reg_t ext_fn_t)
  : option (uaction pos_t var_t fn_name_t reg_t ext_fn_t) :=
    match ua with
    | UIf cond _ _ => Some cond
    | _ => None
    end.

  (* Assumption: no impurities nor vars in conditions.
     Maybe some reads though. *)
  Definition extract_conditions
    (ua: uaction pos_t var_t fn_name_t reg_t ext_fn_t) (z: zipper)
  : list (option (uaction pos_t var_t fn_name_t reg_t ext_fn_t)) :=
    match (access_zipper_tracking ua z extract_condition_one_step) with
    | Some (_, l) => l
    | None => nil
    end.

  Definition merge_conditions
    (cs: list (option (uaction pos_t var_t fn_name_t reg_t ext_fn_t)))
  : uaction pos_t var_t fn_name_t reg_t ext_fn_t :=
    match cs with
    | (Some c)::t => UBinop merge_conditions
    | None::t => merge_conditions t
    | nil => UConst
    end.

  (* Should delegate to remove_pure_bindings_aux *)
  Definition bindings_simplification_pass :=.

  (* Although UVars are replaced whenever the current value of th*)
  Definition remove_unused_bindings :=.

  Definition deal_with_first_impure :=.
  Definition normalize :=.

  (* B. Schedule merging *)

  (* 1. Internal calls inlining - supposes desugared *)
  (* 1.1. Side-effects management functions *)
  (* Some internal calls expect arguments and those behave like let-in bindings.
     Importantly, the side-effects related to the evaluation of the expressions
     passed as arguments should occur exactly once right before the function is
     called. Merely inlining those expressions would lead to trouble. *)
  (* Assumes no internal calls. *)
  (* What if external call? The value needs to be stored somehow. Some
     restricted notion of binding needs to  remain. *)
  Fixpoint remove_side_effects
    (ua: uaction pos_t var_t fn_name_t reg_t ext_fn_t)
  : uaction pos_t var_t fn_name_t reg_t ext_fn_t := (*
    This function is used to avoid duplicating side-effects when arguments are
    inlined. We do not have to care about reads at all as whenever at least
    a read occurs in a rule, subsequent reads are not a problem. *)
    match ua with
    (* TODO remove assigns as well. Mind the effects there as well! *)
    | UAssign v ex => UAssign v (remove_writes ex)
    | USeq a1 a2 => USeq (remove_writes a1) (remove_writes a2)
    | UBind v ex body => UBind v (remove_writes ex) (remove_writes body)
    | UIf cond tbranch fbranch =>
      UIf (remove_writes cond) (remove_writes tbranch) (remove_writes fbranch)
    | UWrite port idx value => (remove_writes value)
    | UUnop ufn1 arg1 => UUnop ufn1 (remove_writes arg1)
    | UBinop ufn2 arg1 arg2 =>
      UBinop ufn2 (remove_writes arg1) (remove_writes arg2)
    | UExternalCall ufn arg => UExternalCall ufn (remove_writes arg)
    | UInternalCall ufn args =>
      UInternalCall {|
        int_name := int_name ufn;
        int_argspec := int_argspec ufn;
        int_retSig := int_retSig ufn;
        int_body := remove_writes (int_body ufn);
      |} (map (remove_writes) args)
    | UAPos p e => UAPos p (remove_writes e)
    | _ => ua
    end.

  Fixpoint to_unit_t
    (ua: uaction pos_t var_t fn_name_t reg_t ext_fn_t)
  : uaction pos_t var_t fn_name_t reg_t ext_fn_t := (*
    This function transforms any uaction to an uaction of type unit_t but with
    the same side-effects. It is used to ensure that the arguments passed to
    any function are indeed evaluated at the point where the function is
    called. *)
    match ua with
    | UAssign v ex => UAssign v ex
    | USeq a1 a2 => USeq a1 (to_unit_t a2)
    | UBind v ex body => UBind v ex body
    | UIf cond tbranch fbranch =>
      UIf cond (to_unit_t tbranch) (to_unit_t fbranch)
    | URead port idx => UConst (tau := bits_t 0) (Bits.of_nat 0 0)
    | UWrite port idx value => UWrite port idx value
    | UUnop ufn1 arg1 => UConst (tau := bits_t 0) (Bits.of_nat 0 0)
    | UBinop ufn2 arg1 arg2 => UConst (tau := bits_t 0) (Bits.of_nat 0 0)
    | UExternalCall ufn arg => UExternalCall ufn arg
    | UInternalCall ufn args => UConst (tau := bits_t 0) (Bits.of_nat 0 0)
    | UAPos p e => UAPos p (to_unit_t e)
    | _ => UConst (tau := bits_t 0) (Bits.of_nat 0 0)
    end.

  (* 1.2. Arguments inlining *)
  Fixpoint replace_variable_with_expr
    (ua: uaction pos_t var_t fn_name_t reg_t ext_fn_t) (vr: var_t)
    (rex: uaction pos_t var_t fn_name_t reg_t ext_fn_t)
  : uaction pos_t var_t fn_name_t reg_t ext_fn_t
    * uaction pos_t var_t fn_name_t reg_t ext_fn_t
  :=
    match ua with
    | UAssign v ex =>
      let (ra1, post_val_1) := replace_variable_with_expr ex vr rex in
      if (eq_dec v vr) then (UConst (tau := bits_t 0) (Bits.of_nat 0 0), ra1)
      else (UAssign v ra1, post_val_1)
    | USeq a1 a2 =>
      let (ra1, post_val_1) := replace_variable_with_expr a1 vr rex in
      let (ra2, post_val_2) := replace_variable_with_expr a2 vr post_val_1 in
      (USeq ra1 ra2, post_val_2)
    | UBind v ex body =>
      let (ra1, post_val_1) := replace_variable_with_expr ex vr rex in
      if (eq_dec v vr) then
        (* vr is shadowed, don't replace in body *)
        (UBind v ra1 body, post_val_1)
      else
        let (ra2, post_val_2) :=
          replace_variable_with_expr body vr post_val_1
        in
        (UBind v ra1 ra2, post_val_2)
    | UIf cond tbranch fbranch =>
      let (ra1, post_val_1) := replace_variable_with_expr cond vr rex in
      let (rat, post_val_t) :=
        replace_variable_with_expr tbranch vr post_val_1
      in
      let (raf, post_val_f) :=
        replace_variable_with_expr fbranch vr post_val_1
      in
      if (uaction_func_equiv post_val_t post_val_f)
      then (UIf ra1 rat raf, post_val_t)
      else (UIf ra1 rat raf, UIf ra1 post_val_t post_val_f)
    | UWrite port idx value =>
      let (ra1, post_val_1) := replace_variable_with_expr value vr rex in
      (UWrite port idx ra1, post_val_1)
    | UUnop ufn1 arg1 =>
      let (ra1, post_val_1) := replace_variable_with_expr arg1 vr rex in
      (UUnop ufn1 ra1, post_val_1)
    | UBinop ufn2 arg1 arg2 =>
      let (ra1, post_val_1) := replace_variable_with_expr arg1 vr rex in
      let (ra2, post_val_2) := replace_variable_with_expr arg2 vr post_val_1 in
      (UBinop ufn2 ra1 ra2, post_val_2)
    | UExternalCall ufn arg =>
      let (ra1, post_val_1) := replace_variable_with_expr arg vr rex in
      (UExternalCall ufn ra1, post_val_1)
    | UInternalCall ufn args =>
      let (rargs, post_val_args) := (
        fold_right
          (fun arg '(l, rex') =>
            let (ran, post_val) := replace_variable_with_expr arg vr rex' in
            (ran::l, post_val)
          )
          (nil, rex)
          args
      ) in
      (UInternalCall ufn rargs, post_val_args)
    | UAPos p e =>
      let (ra1, post_val_1) := replace_variable_with_expr e vr rex in
      (UAPos p ra1, post_val_1)
    | UVar var => if (eq_dec var vr) then (rex, rex) else (ua, rex)
    | _ => (ua, rex)
    end.

  (* 1.3. Internal calls inlining *)
  Fixpoint inline_internal_calls
    (ua: uaction pos_t var_t fn_name_t reg_t ext_fn_t)
  : uaction pos_t var_t fn_name_t reg_t ext_fn_t :=
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
      let args_eval :=
        fold_right (fun arg acc => USeq acc (inline_internal_calls arg))
        (UConst (tau := bits_t 0) (Bits.of_nat 0 0)) args
      in
      let inlined_call :=
        fold_right
          (fun '(arg_n, arg_v) bd =>
            fst (replace_variable_with_expr bd arg_n arg_v)
          )
          (inline_internal_calls (int_body ufn))
          (combine
            (fst (split (int_argspec ufn)))
            (map (fun arg => remove_writes (inline_internal_calls arg)) args)
          )
      in
      USeq (to_unit_t args_eval) inlined_call
    | UAPos p e => UAPos p (inline_internal_calls e)
    | _ => ua
    end.

  (* 2. Bindings removal - supposes desugared, no internal calls *)
  (* TODO What if a binding contains an external call? What if a binding
    contains contains a write? Use replace_variable_with_expr I guess. *)

  Definition remove_bindings
    (ua: uaction pos_t var_t fn_name_t reg_t ext_fn_t)
  : uaction pos_t var_t fn_name_t reg_t ext_fn_t :=
    fst (remove_bindings_aux ua nil).

  (* 3. UAPos removal - supposes desugared, no internal calls, no bindings *)
  Fixpoint remove_uapos
    (ua: uaction pos_t var_t fn_name_t reg_t ext_fn_t)
  : uaction pos_t var_t fn_name_t reg_t ext_fn_t :=
    match ua with
    | USeq a1 a2 => USeq (remove_uapos a1) (remove_uapos a2)
    | UIf cond tbranch fbranch =>
      UIf (remove_uapos cond) (remove_uapos tbranch) (remove_uapos fbranch)
    | UWrite port idx value => UWrite port idx (remove_uapos value)
    | UUnop ufn1 arg1 => UUnop ufn1 (remove_uapos arg1)
    | UBinop ufn2 arg1 arg2 =>
      UBinop ufn2 (remove_uapos arg1) (remove_uapos arg2)
    | UExternalCall ufn arg => UExternalCall ufn (remove_uapos arg)
    | UAPos p e => remove_uapos e
    | _ => ua
    end.

  (* External calls:
  *)

  (* TODO careful about extcalls duplication *)
  (* TODO should we define restrictions about extcalls? e.g. no more than one
    of a given type per cycle *)
  (* 4. Schedule to single rule - supposes desugared, no internal calls, no
    bindings, no uapos *)
  Fixpoint extract_preconditions_aux
    (ua: uaction pos_t var_t fn_name_t reg_t ext_fn_t)
    (guard: list (uaction pos_t var_t fn_name_t reg_t ext_fn_t))
  : list (
    list (uaction pos_t var_t fn_name_t reg_t ext_fn_t)
    * uaction pos_t var_t fn_name_t reg_t ext_fn_t
  ) :=
    match ua with
    | USeq a1 a2 =>
      extract_preconditions_aux a1 guard++extract_preconditions_aux a2 guard
    | UIf cond tbranch fbranch =>
      (* TODO ??? *)
      let t_res := extract_preconditions_aux tbranch (cond::guard) in
      let f_res :=
        extract_preconditions_aux fbranch (
          (UUnop (PrimUntyped.UBits1 PrimUntyped.UNot) cond)::guard
        )
      in
      t_res ++ f_res
    | URead port idx => [(guard, ua)]
    | UWrite port idx value => [(guard, ua)]
    | UUnop ufn1 arg1 => extract_preconditions_aux arg1 guard
    | UBinop ufn2 arg1 arg2 =>
      extract_preconditions_aux arg1 guard++extract_preconditions_aux arg2 guard
    | UExternalCall ufn arg =>
    | _ => []
    end.

  Definition extract_preconditions
    (ua: uaction pos_t var_t fn_name_t reg_t ext_fn_t)
  : list (uaction reg_t ext_fn_t * uaction reg_t ext_fn_t) :=
    match ua with
    | UWrite
    end.

  Definition extract_postconditions
    (ua: uaction pos_t var_t fn_name_t reg_t ext_fn_t)
  : list (uaction reg_t ext_fn_t * uaction reg_t ext_fn_t) :=
    match
  .

  Close Scope nat.
End Normalize.
