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
      (* TODO deal correctly with controlled bindings. Add them to Gamma with
           UVar self? *)
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
