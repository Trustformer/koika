(*! Proving | Transformation of a schedule to a single rule in normal form !*)
Require Import Coq.Program.Equality.
Require Import Koika.BitsToLists Koika.Utils Koika.Zipper.
Open Scope nat.

(* In this file, whenever side-effects or equivalence are mentionned, bear in
   mind that we do not care about the contents of the logs, but rather about
   the state of the model at the end of the cycle. For example, reading an
   otherwise unaccessed variable is not considered a side-effect. *)

(* The normal form in question is a single rule (instead of a schedule)
   containing a sequence of writes guarded by a single if each. *)

(* 1. Internal calls inlining - supposes desugared *)
(* 1.1. Side-effects management functions *)
(* Some internal calls expect arguments and those behave like let-in bindings.
   Importantly, the side-effects related to the evaluation of the expressions
   passed as arguments should occur exactly once right before the function is
   called. Merely inlining those expressions would lead to trouble. *)
Fixpoint remove_writes
  {pos_t var_t fn_name_t reg_t ext_fn_t: Type}
  (ua: uaction pos_t var_t fn_name_t reg_t ext_fn_t)
: uaction pos_t var_t fn_name_t reg_t ext_fn_t := (*
  This function is used to avoid duplicating side-effects when arguments are
  inlined. We do not have to care about reads at all as whenever at least a read
  occurs in a rule, subsequent reads are not a problem.
  However, writes are removed - this is not a problem as far as the final value
  of the argument is concerned as writes are of type unit_t anyways. *)
  match ua with
  (* TODO remove assigns as well *)
  | UAssign v ex => UAssign v (remove_writes ex)
  | USeq a1 a2 => USeq (remove_writes a1) (remove_writes a2)
  | UBind v ex body =>
    UBind v (remove_writes ex) (remove_writes body)
  | UIf cond tbranch fbranch =>
    UIf
      (remove_writes cond) (remove_writes tbranch)
      (remove_writes fbranch)
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
  {pos_t var_t fn_name_t reg_t ext_fn_t: Type}
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
  | UIf cond tbranch fbranch => UIf cond (to_unit_t tbranch) (to_unit_t fbranch)
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
  {pos_t var_t fn_name_t reg_t ext_fn_t: Type}
  {beq_var_t: EqDec var_t}
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
      let (ra2, post_val_2) := replace_variable_with_expr body vr post_val_1 in
      (UBind v ra1 ra2, post_val_2)
  | UIf cond tbranch fbranch =>
    let (ra1, post_val_1) := replace_variable_with_expr cond vr rex in
    let (rat, post_val_t) := replace_variable_with_expr tbranch vr post_val_1 in
    let (raf, post_val_f) := replace_variable_with_expr fbranch vr post_val_1 in
    if (post_val_t post_val_f)
    (UIf ra1 rat raf, UIf ra1 post_val_t post_val_f)
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
  {pos_t var_t fn_name_t reg_t ext_fn_t: Type} {beq_var_t: EqDec var_t}
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

(* 1.X. Testing *)
Definition remove_this_internal_call
  {pos_t var_t fn_name_t reg_t ext_fn_t: Type} {beq_var_t: EqDec var_t}
  (ua: uaction pos_t var_t fn_name_t reg_t ext_fn_t) (z: zipper)
: option (uaction pos_t var_t fn_name_t reg_t ext_fn_t) :=
  match (access_zipper ua z) with
  | Some x =>
    match x with
    | UInternalCall _ _ =>
      replace_at_zipper_with
        ua z
        (fun e =>
          match e with
          | UInternalCall ufn args =>
            let args_eval :=
              fold_right (USeq)
              (UConst (tau := bits_t 0) (Bits.of_nat 0 0)) args
            in
            let inlined_call :=
              fold_right
                (fun '(arg_n, arg_v) bd =>
                  fst (replace_variable_with_expr bd arg_n arg_v)
                )
                (int_body ufn)
                (combine
                  (fst (split (int_argspec ufn))) (map remove_writes args)
                )
            in
            USeq (to_unit_t args_eval) inlined_call
          | _ => (UConst (tau := bits_t 0) (Bits.of_nat 0 0))
          end
        )
    | _ => None
    end
  | None => None
  end.

Definition is_internal_call
  {pos_t var_t fn_name_t reg_t ext_fn_t: Type}
  (ua: uaction pos_t var_t fn_name_t reg_t ext_fn_t)
: bool :=
  match ua with
  | UInternalCall _ _ => true
  | _ => false
  end.

Fixpoint remove_first_n_internal_calls_aux
  {pos_t var_t fn_name_t reg_t ext_fn_t: Type} {beq_var_t: EqDec var_t}
  (ua: uaction pos_t var_t fn_name_t reg_t ext_fn_t) (lz: list zipper) (n: nat)
: option (uaction pos_t var_t fn_name_t reg_t ext_fn_t) :=
  match n with
  | O => Some ua
  | S n' =>
    match lz with
    | h::t =>
      match remove_this_internal_call ua h with
      | Some x => remove_first_n_internal_calls_aux x t n'
      | None => None
      end
    | nil => None
    end
  end.

Definition remove_first_n_internal_calls
  {pos_t var_t fn_name_t reg_t ext_fn_t: Type} {beq_var_t: EqDec var_t}
  (ua: uaction pos_t var_t fn_name_t reg_t ext_fn_t) (n: nat)
: option (uaction pos_t var_t fn_name_t reg_t ext_fn_t) :=
  let matches := rev (find_all_in_uaction ua (is_internal_call)) in
  match matches with
  | nil => None
  | _ => remove_first_n_internal_calls_aux ua matches n
  end.

Definition remove_first_internal_call
  {pos_t var_t fn_name_t reg_t ext_fn_t: Type} {beq_var_t: EqDec var_t}
  (ua: uaction pos_t var_t fn_name_t reg_t ext_fn_t)
: option (uaction pos_t var_t fn_name_t reg_t ext_fn_t) :=
  remove_first_n_internal_calls ua 1.

Definition get_init_value
  {pos_t var_t fn_name_t reg_t ext_fn_t: Type} {beq_var_t: EqDec var_t}
  (ua: uaction pos_t var_t fn_name_t reg_t ext_fn_t)
:=
  let lz := rev (find_all_in_uaction ua (is_internal_call)) in
  match lz with
  | h::t => access_zipper ua h
  | nil => None
  end.

Definition get_final_value
  {pos_t var_t fn_name_t reg_t ext_fn_t: Type} {beq_var_t: EqDec var_t}
  (ua: uaction pos_t var_t fn_name_t reg_t ext_fn_t)
: option (uaction pos_t var_t fn_name_t reg_t ext_fn_t) :=
  let lz := rev (find_all_in_uaction ua (is_internal_call)) in
  match lz with
  | h::t =>
    match (access_zipper ua h) with
    | Some zv =>
      ((fun e =>
        match e with
        | UInternalCall ufn args =>
          Some (fold_right
            (fun '(arg_n, arg_v) bd =>
              fst (replace_variable_with_expr bd arg_n arg_v)
            )
            (int_body ufn)
            (firstn 1 (rev (combine (fst (split (int_argspec ufn))) (args))))
          )
        | _ => None
        end
      ) zv)
    | None => None
    end
  | nil => None
  end.

Definition get_zip
  {pos_t var_t fn_name_t reg_t ext_fn_t: Type} {beq_var_t: EqDec var_t}
  (ua: uaction pos_t var_t fn_name_t reg_t ext_fn_t)
: option zipper :=
  hd_error (rev (find_all_in_uaction ua (is_internal_call))).

Definition get_count
  {pos_t var_t fn_name_t reg_t ext_fn_t: Type} {beq_var_t: EqDec var_t}
  (ua: uaction pos_t var_t fn_name_t reg_t ext_fn_t)
: nat :=
  List.length (find_all_in_uaction ua (is_internal_call)).

Fixpoint get_size
  {pos_t var_t fn_name_t reg_t ext_fn_t: Type} {beq_var_t: EqDec var_t}
  (ua: uaction pos_t var_t fn_name_t reg_t ext_fn_t)
: nat :=
  1 +
  match ua with
  | UError _ => 0
  | UFail _ => 0
  | UVar _ => 0
  | UConst _ => 0
  | UAssign _ ex => get_size ex
  | USeq a1 a2 => get_size a1 + get_size a2
  | UBind _ ex body => get_size ex + get_size body
  | UIf cond tbranch fbranch =>
    get_size cond + get_size tbranch + get_size fbranch
  | URead _ _ => 0
  | UWrite _ _ value => get_size value
  | UUnop _ arg1 => get_size arg1
  | UBinop _ arg1 arg2 => get_size arg1 + get_size arg2
  | UExternalCall _ arg => get_size arg
  | UInternalCall ufn args =>
    get_size (int_body ufn)
    + List.fold_left (fun acc ua => acc + (get_size ua)) args 0
  | UAPos _ e => get_size e
  | USugar _ => 0
  end.

Definition get_nth_call
  {pos_t var_t fn_name_t reg_t ext_fn_t: Type} {beq_var_t: EqDec var_t}
  (ua: uaction pos_t var_t fn_name_t reg_t ext_fn_t) (n: nat)
: option zipper :=
  nth_error (rev (find_all_in_uaction ua (is_internal_call))) n.

Definition get_replacement
  {pos_t var_t fn_name_t reg_t ext_fn_t: Type} {beq_var_t: EqDec var_t}
  (ua: uaction pos_t var_t fn_name_t reg_t ext_fn_t) (z: zipper)
: option (uaction pos_t var_t fn_name_t reg_t ext_fn_t) :=
  match access_zipper ua z with
  | Some (UInternalCall ufn args) => Some (
    let args_eval :=
      fold_right (USeq) (UConst (tau := bits_t 0) (Bits.of_nat 0 0)) args
    in
    let inlined_call :=
      fold_right
        (fun '(arg_n, arg_v) bd =>
          fst (replace_variable_with_expr bd arg_n arg_v)
        )
        (int_body ufn)
        (combine (fst (split (int_argspec ufn))) (map remove_writes args))
    in
    USeq (to_unit_t args_eval) inlined_call
  )
  | _ => None
  end.

Definition get_nth_replacement
  {pos_t var_t fn_name_t reg_t ext_fn_t: Type} {beq_var_t: EqDec var_t}
  (ua: uaction pos_t var_t fn_name_t reg_t ext_fn_t) (n: nat)
: option (uaction pos_t var_t fn_name_t reg_t ext_fn_t) :=
    (nth_error (rev (find_all_in_uaction ua (is_internal_call))) n)
    >>=
    (get_replacement ua)
.

Definition get_nth_arg
  {pos_t var_t fn_name_t reg_t ext_fn_t: Type} {beq_var_t: EqDec var_t}
  (ua: uaction pos_t var_t fn_name_t reg_t ext_fn_t) (z: zipper) (n: nat)
: option (uaction pos_t var_t fn_name_t reg_t ext_fn_t) :=
  match access_zipper ua z with
  | Some (UInternalCall ufn args) => nth_error args n
  | _ => None
  end.

(* Definition get_nth_replacement *)
(*   {pos_t var_t fn_name_t reg_t ext_fn_t: Type} {beq_var_t: EqDec var_t} *)
(*   (ua: uaction pos_t var_t fn_name_t reg_t ext_fn_t) (n: nat) *)
(* : option (uaction pos_t var_t fn_name_t reg_t ext_fn_t) := *)
(*   let lz := rev (find_all_in_uaction ua (is_internal_call)) in *)
(*   match lz with *)
(*   | h::t => *)
(*     match (access_zipper ua h) with *)
(*     | Some x => *)
(*       match x with *)
(*       | UInternalCall ufn args => *)
(*         match nth_error (fst (split (int_argspec ufn))) n with *)
(*         | Some y => *)
(*           let inlined_call := *)
(*             fst (replace_variable_with_expr (int_body ufn) y ) *)
(*           in *)
(*           Some inlined_call *)
(*         | None => None *)
(*         end *)
(*       | _ => None *)
(*       end *)
(*     | None => None *)
(*     end *)
(*   | nil => None *)
(*   end. *)

(* 2. Bindings removal - supposes desugared, no internal calls *)
Fixpoint remove_bindings_aux
  {pos_t var_t fn_name_t reg_t ext_fn_t: Type} {beq_var_t: EqDec var_t}
  (ua: uaction pos_t var_t fn_name_t reg_t ext_fn_t)
  (Gamma: list (var_t * uaction pos_t var_t fn_name_t reg_t ext_fn_t))
: uaction pos_t var_t fn_name_t reg_t ext_fn_t
  * list (var_t * uaction pos_t var_t fn_name_t reg_t ext_fn_t)
:=
  match ua with
  | UVar var =>
    match list_assoc Gamma var with
    | Some lar => (lar, Gamma)
    (* Should never happen in well-formed rules *)
    | None => (UConst (tau := bits_t 0) (Bits.of_nat 0 0), Gamma)
    end
  | UAssign v ex =>
    let (ra1, Gamma') := remove_bindings_aux ex Gamma in
    (to_unit_t ra1, list_assoc_set Gamma' v (remove_writes ra1))
  | USeq a1 a2 =>
    let (ra1, Gamma') := remove_bindings_aux a1 Gamma in
    let (ra2, Gamma'') := remove_bindings_aux a2 Gamma' in
    (USeq ra1 ra2, Gamma'')
  | UBind v ex body =>
    let (ra1, Gamma') := remove_bindings_aux ex Gamma in
    let (ra2, Gamma'') := remove_bindings_aux body ((v, ex)::Gamma') in
    (USeq (to_unit_t ra1) ra2, tl Gamma'')
  | UIf cond tbranch fbranch =>
    let (ra1, Gamma_cond) := remove_bindings_aux cond Gamma in
    let (rat, Gamma_t) := remove_bindings_aux tbranch Gamma_cond in
    let (raf, Gamma_f) := remove_bindings_aux fbranch Gamma_cond in
    (* TODO most cases could be simplified *)
    let Gamma' :=
      fold_right
        (fun v acc =>
          list_assoc_set acc v (
            UIf ra1 (
              match list_assoc Gamma_t v with
              | Some lar => lar
              | None => UConst (tau := bits_t 0) (Bits.of_nat 0 0)
              end
            ) (
              match list_assoc Gamma_f v with
              | Some lar => lar
              | None => UConst (tau := bits_t 0) (Bits.of_nat 0 0)
              end
            )
          )
        )
        Gamma_cond (fst (split Gamma_cond))
    in
    (UIf ra1 rat raf, Gamma')
  | UWrite port idx value =>
    let (ra1, Gamma') := remove_bindings_aux value Gamma in
    (UWrite port idx ra1, Gamma')
  | UUnop ufn1 arg1 =>
    let (ra1, Gamma') := remove_bindings_aux arg1 Gamma in
    (UUnop ufn1 ra1, Gamma')
  | UBinop ufn2 arg1 arg2 =>
    let (ra1, Gamma') := remove_bindings_aux arg1 Gamma in
    let (ra2, Gamma'') := remove_bindings_aux arg2 Gamma' in
    (UBinop ufn2 ra1 ra2, Gamma'')
  | UExternalCall ufn arg =>
    let (ra1, Gamma') := remove_bindings_aux arg Gamma in
    (UExternalCall ufn ra1, Gamma')
  | UInternalCall ufn args =>
    let (rargs, Gamma_args) := (
      fold_right
        (fun arg '(l, Gamma') =>
          let (ran, post_val) := remove_bindings_aux arg Gamma' in
          (ran::l, post_val)
        )
        (nil, Gamma)
        args
    ) in
    (UInternalCall ufn rargs, Gamma_args)
  | UAPos p e =>
    let (ra1, Gamma') := remove_bindings_aux e Gamma in
    (UAPos p ra1, Gamma')
  | _ => (ua, Gamma)
  end.

Definition remove_bindings
  {pos_t var_t fn_name_t reg_t ext_fn_t: Type} {beq_var_t: EqDec var_t}
  (ua: uaction pos_t var_t fn_name_t reg_t ext_fn_t)
: uaction pos_t var_t fn_name_t reg_t ext_fn_t :=
  fst (remove_bindings_aux ua nil).

(* 2.X. Testing *)
Fixpoint remove_bindings_depth_1
  {pos_t var_t fn_name_t reg_t ext_fn_t: Type} {beq_var_t: EqDec var_t}
  (ua: uaction pos_t var_t fn_name_t reg_t ext_fn_t)
: uaction pos_t var_t fn_name_t reg_t ext_fn_t :=
  match ua with
  | USeq a1 a2 => USeq (remove_bindings_depth_1 a1) (remove_bindings_depth_1 a2)
  | UBind v ex body =>
    USeq
      (to_unit_t ex)
      (fst (replace_variable_with_expr body v (remove_writes ex)))
  | UIf cond tbranch fbranch =>
    UIf (remove_bindings_depth_1 cond) (remove_bindings_depth_1 tbranch)
      (remove_bindings_depth_1 fbranch)
  | UWrite port idx value => UWrite port idx (remove_bindings_depth_1 value)
  | UUnop ufn1 arg1 => UUnop ufn1 (remove_bindings_depth_1 arg1)
  | UBinop ufn2 arg1 arg2 =>
    UBinop ufn2 (remove_bindings_depth_1 arg1) (remove_bindings_depth_1 arg2)
  | UExternalCall ufn arg => UExternalCall ufn (remove_bindings_depth_1 arg)
  | UAPos p e => UAPos p (remove_bindings_depth_1 e)
  | _ => ua
  end.

Fixpoint remove_bindings_depth_n
  {pos_t var_t fn_name_t reg_t ext_fn_t: Type} {beq_var_t: EqDec var_t}
  (ua: uaction pos_t var_t fn_name_t reg_t ext_fn_t) (n: nat)
: uaction pos_t var_t fn_name_t reg_t ext_fn_t :=
  match n with
  | O => ua
  | S n' => remove_bindings_depth_n (remove_bindings_depth_1 ua) n'
  end.

Definition is_binding
  {pos_t var_t fn_name_t reg_t ext_fn_t: Type}
  (ua: uaction pos_t var_t fn_name_t reg_t ext_fn_t)
: bool :=
  match ua with
  | UBind _ _ _ => true
  | _ => false
  end.

Definition remove_this_binding
  {pos_t var_t fn_name_t reg_t ext_fn_t: Type} {beq_var_t: EqDec var_t}
  (ua: uaction pos_t var_t fn_name_t reg_t ext_fn_t) (z: zipper)
: option (uaction pos_t var_t fn_name_t reg_t ext_fn_t) :=
  match (access_zipper ua z) with
  | Some x =>
    match x with
    | UBind _ _ _ =>
      replace_at_zipper_with
        ua z
        (fun e =>
          match e with
          | UBind v ex body =>
            USeq
              (to_unit_t ex)
              (fst (replace_variable_with_expr body v (remove_writes ex)))
          | _ => e
          end
        )
    | _ => None
    end
  | None => None
  end.

Fixpoint remove_first_n_bindings_aux
  {pos_t var_t fn_name_t reg_t ext_fn_t: Type} {beq_var_t: EqDec var_t}
  (ua: uaction pos_t var_t fn_name_t reg_t ext_fn_t) (lz: list zipper) (n: nat)
: option (uaction pos_t var_t fn_name_t reg_t ext_fn_t) :=
  match n with
  | O => Some ua
  | S n' =>
    match lz with
    | h::t =>
      match remove_this_binding ua h with
      | Some x => remove_first_n_bindings_aux x t n'
      | None => None
      end
    | nil => None
    end
  end.

Definition remove_first_n_bindings
  {pos_t var_t fn_name_t reg_t ext_fn_t: Type} {beq_var_t: EqDec var_t}
  (ua: uaction pos_t var_t fn_name_t reg_t ext_fn_t) (n: nat)
: option (uaction pos_t var_t fn_name_t reg_t ext_fn_t) :=
  let matches := find_all_in_uaction ua (is_binding) in
  remove_first_n_bindings_aux ua matches n.

Definition remove_first_binding
  {pos_t var_t fn_name_t reg_t ext_fn_t: Type} {beq_var_t: EqDec var_t}
  (ua: uaction pos_t var_t fn_name_t reg_t ext_fn_t)
: option (uaction pos_t var_t fn_name_t reg_t ext_fn_t) :=
  remove_first_n_bindings ua 1.

(* 3. UAPos removal - supposes desugared, no internal calls, no bindings *)
Fixpoint remove_uapos
  {pos_t var_t fn_name_t reg_t ext_fn_t: Type}
  (ua: uaction pos_t var_t fn_name_t reg_t ext_fn_t)
: uaction pos_t var_t fn_name_t reg_t ext_fn_t :=
  match ua with
  | USeq a1 a2 => USeq (remove_uapos a1) (remove_uapos a2)
  | UIf cond tbranch fbranch =>
    UIf (remove_uapos cond) (remove_uapos tbranch) (remove_uapos fbranch)
  | UWrite port idx value => UWrite port idx (remove_uapos value)
  | UUnop ufn1 arg1 => UUnop ufn1 (remove_uapos arg1)
  | UBinop ufn2 arg1 arg2 => UBinop ufn2 (remove_uapos arg1) (remove_uapos arg2)
  | UExternalCall ufn arg => UExternalCall ufn (remove_uapos arg)
  | UAPos p e => remove_uapos e
  | _ => ua
  end.
Close Scope nat.
