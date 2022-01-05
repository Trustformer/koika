(*! Proving | Transformation of a schedule into a proof-friendly form !*)
Require Import Coq.Numbers.DecimalString Coq.Program.Equality Coq.Strings.Ascii.
Require Import Koika.BitsToLists Koika.Primitives Koika.Syntax Koika.Utils
  Koika.Zipper.

(* The normal form we want to turn schedules into is a single rule containing a
   sequence of writes guarded by a single if each. It goes without saying that a
   normalized schedule should be equivalent to its initial form (in terms of
   the effects of a cycle on the final state of the registers and the emitted
   extcalls). TODO explain extcalls. The reason why we go through the trouble of
   defining this normal form is because reasoning about Kôika models is because
   quite some stuff happens implicitly (rules merging and cancellation, etc).
   In the normal form, everything is explicit. In particular, problems such as
   finding under which conditions the value of a register is updated or proving
   that the value of register x never reaches 5 become easier. *)

Open Scope nat.
Section Normalize.
  Context {pos_t var_t reg_t ext_fn_t rule_name_t: Type}.
  Context {reg_t_eq_dec: EqDec reg_t}.
  Context {ext_fn_t_eq_dec: EqDec ext_fn_t}.
  Definition uact := uaction pos_t string string reg_t ext_fn_t.
  Definition schedule := scheduler pos_t rule_name_t.
  Context (rules: rule_name_t -> uact).

  (* A. Basics *)
  (* A.1. Data structures *)
  (* A.1.a. Structures *)
  (* reg * (cond * bind_name) *)
  Definition read_info : Type := reg_t * (uact * string).
  Definition read_log := list read_info.
  (* reg * (cond * val) *)
  Definition write_info : Type := reg_t * (uact * uact).
  Definition write_log := list write_info.
  (* ufn * (cond * bind_name * arg) *)
  Definition extcall_info : Type := ext_fn_t * (uact * string * uact).
  Definition extcall_log := list extcall_info.
  Record action_logs := mkActions {
    read0s: read_log;
    read1s: read_log;
    write0s: write_log;
    write1s: write_log;
    extcalls: extcall_log;
  }.
  Record rule_information := mkRuleInformation {
    actions: action_logs;
    (* We do not worry about potential conflicts in action logs. What if we
       stumble on two write1s on register x? We simply register the write1s as
       they stand, but update the following condition for the whole rule: *)
    failure_cond: option uact;
  }.
  (* Note that we did not reuse uact for that purpose as that could have made
     things confusing (we consider a set of actions and not a sequence). *)
  Definition schedule_information := action_logs.
  Record normal_form := mkNormalForm {
    reads: read_log;
    writes: write_log;
    external_calls: extcall_log;
  }.

  (* A.1.b. Helper functions for structures *)
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

  (* A.2. Helper functions *)
  (* Remove Nones from list, turn rest from (Some x) to x. *)
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

  (* B. Variable names collisions management *)
  (* We will need to generate some new variables when transforming individual
     rules. For instance, an extcall can return a value which can be needed
     elsewhere. Take the following example (pseudocode and approximation of the
     real normal form, don't take it too literally):
     let a := extcall("e1", 5) + 3 in
     write0(r, a)
     This will be transformed as:
     [extcall ("e1", (true, "bind0", (5))), write0 (r, (true, "bind0" + 3))]
     Therefore, we need a way to generate new variable names. Of course, we have
     to be careful about name collisions. Our new variables will follow the form
     of "bind0". To avoid collisions, we look for all the variables matching
     this form that were initially present in the function. Then, adding 1 to
     the maximum value that was found following a "bind" is enough. *)
  (* B.1. Variables detection *)
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
    String.list_ascii_of_string (String.substring 4 (String.length s - 4) s).

  Scheme Equality for option.
  Definition matches_control_binding_form (s: string) : bool :=
    let maybe_digits := extract_custom_binding_digits s in
    (String.prefix "bind" s)
    && (negb (Nat.eqb (List.length maybe_digits) 0))
    && (List.forallb is_digit maybe_digits)
    && (negb
      (option_beq
        ascii (Ascii.eqb) (List.hd_error maybe_digits) (Some "0"%char)
      )
    ).

  (* B.2. Variables generation *)
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
    String.append "bind" (NilEmpty.string_of_uint (Init.Nat.to_uint n)).

  (* C. rule_information extraction *)
  (* The rule_information structure is defined in A.1. *)
  (* C.1. Addition of a new action into an existing rule_information *)
  (* C.1.a. Merger of failure conditions *)
  Definition or_conds (conds: list uact) :=
    List.fold_left
      (fun acc c =>
        match acc with
        | None => Some c
        | Some x => Some (UBinop (PrimUntyped.UBits2 PrimUntyped.UOr) c x)
        end
      )
      conds None.

  (* TODO weird function, why not single list? *)
  Definition merge_failures_list (action_cond: uact) (conds: list uact) :=
    match or_conds conds with
    | None => None
    | Some x =>
      Some (UBinop (PrimUntyped.UBits2 PrimUntyped.UOr) action_cond x)
    end.

  (* C.1.b. Merger of actions *)
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

  (* C.2. Extraction of actions from rule *)
  (* TODO poor name *)
  Definition merge_uacts (cond: uact) (ua1 ua2: option uact) : option uact :=
    match ua1, ua2 with
    | Some x, Some y => Some (UIf cond x y)
    | _, _ => None
    end.

  (* Precondition: both Gammas contain the same variables in the same order. *)
  Definition merge_Gammas (cond: uact) (g1 g2: list (string * uact))
  : list (string * uact) :=
    List.map
      (fun '((str, ua1), (_, ua2)) =>
        if uaction_func_equiv ua1 ua2 then (str, ua1)
        else (str, UIf cond ua1 ua2)
      )
      (List.combine g1 g2).

  (* TODO unite with merge_failures_list? *)
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

  Fixpoint distill_aux
    (* No need to pass failures as failures impact the whole rule - taking note
       of all of them and factoring the conditions in is enough. Conflicts
       between different actions are also dealt with here - see C.1. *)
    (ua: uact) (Gamma: list (string * uact)) (guard: uact) (al: action_logs)
    (last_controlled: nat)
    (* Returns value, context, failure condition, action_logs,
       last_controlled *)
  : option uact * (list (string * uact)) * (option uact) * action_logs * nat :=
    let lc := last_controlled in
    match ua with
    | UBind var val body =>
      let '(ret_val, Gamma_val, failures_val, al_val, lc_val) :=
        distill_aux val Gamma guard al lc
      in
      let '(ret_body, Gamma_body, failures_body, al_body, lc_body) :=
        distill_aux
          body (list_assoc_set Gamma_val var (reduce ret_val)) guard al lc_val
      in
      (None, List.skipn 1 Gamma_body, (* Remove the binding to var *)
       merge_failures failures_val failures_body, al_body, lc_body)
    | UAssign var val =>
      let '(ret_val, Gamma_val, failures_val, al_val, lc_val) :=
        distill_aux val Gamma guard al lc
      in
      (None, list_assoc_set Gamma_val var (reduce ret_val), failures_val,
       al_val, lc_val)
    | UVar var =>
      match list_assoc Gamma var with
      (* If there is no binding and the rule is well formed, then the variable
         has to be a controlled binding. TODO maybe rewrite to make proofs
         easier, for instance check if the form matches that of a controlled
         binding with a number less than or equal to last_controlled. *)
      | None => (Some (UVar var), Gamma, None, al, lc)
      | Some x => (list_assoc Gamma var, Gamma, None, al, lc)
      end
    | USeq a1 a2 =>
      let '(_, Gamma_a1, failures_a1, al_a1, lc_a1) :=
        distill_aux a1 Gamma guard al lc
      in
      let '(ret_a2, Gamma_a2, failures_a2, al_a2, lc_a2) :=
        distill_aux a2 Gamma_a1 guard al_a1 lc_a1
      in
      (ret_a2, Gamma_a2, merge_failures failures_a1 failures_a2, al_a2, lc_a2)
    | UIf cond tb fb =>
      let '(ret_cond, Gamma_cond, failures_cond, al_cond, lc_cond) :=
        distill_aux cond Gamma guard al lc
      in
      let guard_tb :=
        UBinop (PrimUntyped.UBits2 PrimUntyped.UAnd) guard (reduce ret_cond)
      in
      let guard_fb :=
        UBinop (PrimUntyped.UBits2 PrimUntyped.UAnd)
          guard (UUnop (PrimUntyped.UBits1 PrimUntyped.UNot) (reduce ret_cond))
      in
      let '(ret_tb, Gamma_tb, failures_tb, al_tb, lc_tb) :=
        distill_aux tb Gamma_cond guard_tb al_cond lc_cond
      in
      let '(ret_fb, Gamma_fb, failures_fb, al_fb, lc_fb) :=
        (* We use al_tb here even though we know that none of the actions added
           by the other branch can impact those from this branch as they are
           mutually exclusive. However, this way, we don't have to deal with
           action_logs merging. *)
        distill_aux fb Gamma_cond guard_fb al_tb lc_tb
      in
      (merge_uacts cond ret_tb ret_fb,
       merge_Gammas cond Gamma_fb Gamma_tb,
       merge_failures failures_tb failures_fb, al_fb, lc_fb)
    | UUnop ufn a =>
      let '(ret_a, Gamma_a, failures_a, al_a, lc_a) :=
        distill_aux a Gamma guard al lc
      in
      (Some (UUnop ufn (reduce ret_a)), Gamma_a, failures_a, al_a, lc_a)
    | UBinop ufn a1 a2 =>
      let '(ret_a1, Gamma_a1, failures_a1, al_a1, lc_a1) :=
        distill_aux a1 Gamma guard al lc
      in
      let '(ret_a2, Gamma_a2, failures_a2, al_a2, lc_a2) :=
        distill_aux a2 Gamma_a1 guard al_a1 lc_a1
      in
      (Some (UBinop ufn (reduce ret_a1) (reduce ret_a2)), Gamma_a2,
       merge_failures failures_a1 failures_a2, al_a2, lc_a2)
    | UInternalCall ufn args =>
      let '(arg_values, Gamma_args, failure_args, al_args, lc_args) := (
        List.fold_left
          (fun '(values, Gamma_p, failures_p, al_p, lc_p) a =>
            let '(val_n, Gamma_n, failure_n, al_n, lc_n) :=
              distill_aux a Gamma_p guard al_p lc_p
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
          (* We filter Nones out to please Coq, although we know that a value is
             assigned to each argument in well formed code *)
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
        distill_aux (int_body ufn) Gamma_in guard al_args lc_args
      in
      (ret_ic, Gamma_args, merge_failures failure_ic failure_args, al_ic,
       lc_ic)
    | UAPos _ e => distill_aux e Gamma guard al lc
    | URead port reg =>
      let fresh_name := generate_binding_name (S lc) in
      let '(modified_al, failure_read, used_name) :=
        match port with
        | P0 => add_read0 al guard reg fresh_name
        | P1 => add_read1 al guard reg fresh_name end
      in
      let new_lc := if String.eqb fresh_name used_name then S lc else lc in
      (Some (UVar (used_name)), Gamma, failure_read, modified_al, new_lc)
    | UWrite port reg val =>
      let '(ret_val, Gamma_val, failures_val, actions_val, lc_val) :=
        distill_aux val Gamma guard al lc
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
        distill_aux arg Gamma guard al lc
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

  (* This function extracts the actions for a given rule. It also returns the
     highest value used for a custom binding (if rule A and rule B are in a
     schedule, the initial value of last_controlled for rule B should be the
     last value of last_controlled for rule A). *)
  Definition distill (ua: uact) (last_controlled: nat) :
    rule_information * nat
  :=
    let '(_, _, failure, action_logs, last_controlled') :=
      distill_aux
        ua [] (UConst (tau := bits_t 1) (Bits.of_nat 1 1))
        {|
          read0s := []; read1s := []; write0s := []; write1s := [];
          extcalls := [];
        |}
        last_controlled
    in (
      {| actions := action_logs; failure_cond := failure; |}, last_controlled'
    ).

  (* D. Scheduling conflicts detection *)
  (* It is here that we take into account how a rule might cancel any later
     rule. *)
  (* D.1. Conflicts between two rules *)
  Definition detect_conflicts_step
    (acc: option uact) (al: action_logs) (cond: uact) (reg: reg_t)
    (reg_failure_detection: action_logs -> uact -> reg_t -> option uact)
  : option uact :=
    match reg_failure_detection al cond reg with
    | None => acc
    | Some x =>
      match acc with
      | None => Some x
      | Some y => Some (UBinop (PrimUntyped.UBits2 PrimUntyped.UOr) x y)
      end
    end.

  (* The following functions are meant to be passed as argument to
     detect_conflicts_step. *)
  Definition detect_conflicts_read0s_reg
    (al: action_logs) (cond: uact) (reg: reg_t)
  : option uact :=
    (* TODO Refactor since shared with add_read0? *)
    let previous_wr0 := extract_write0_cond al reg in
    let previous_wr1 := extract_write1_cond al reg in
    merge_failures_list
      cond (list_options_to_list [previous_wr0; previous_wr1]).
  Definition detect_conflicts_read1s_reg
    (al: action_logs) (cond: uact) (reg: reg_t)
  : option uact :=
    let previous_wr1 := extract_write1_cond al reg in
    merge_failures_list cond (list_options_to_list [previous_wr1]).
  Definition detect_conflicts_write0s_reg
    (al: action_logs) (cond: uact) (reg: reg_t)
  : option uact :=
    let previous_wr0 := extract_write0_cond al reg in
    let previous_wr1 := extract_write1_cond al reg in
    let previous_rd1 := extract_read1_cond al reg in
    merge_failures_list
      cond (list_options_to_list [previous_wr0; previous_wr1; previous_rd1]).
  Definition detect_conflicts_write1s_reg
    (* TODO make cond option instead? *)
    (al: action_logs) (cond: uact) (reg: reg_t)
  : option uact :=
    let previous_wr1 := extract_write1_cond al reg in
    merge_failures_list cond (list_options_to_list [previous_wr1]).

  (* These functions take the action_logs of a rule as well as some logs of a
     subsequent rule, and returns a condition that is true in all the situations
     in which the second rule has to fail for e.g. read0s conflicts reasons (and
     no other cases). *)
  Definition detect_conflicts_read0s (al: action_logs) (rl: read_log)
  : option uact :=
    List.fold_left
      (fun acc '(reg, (cond, _)) =>
        detect_conflicts_step acc al cond reg detect_conflicts_read0s_reg
      )
      rl None.
  Definition detect_conflicts_read1s (al: action_logs) (rl: read_log)
  : option uact :=
    List.fold_left
      (fun acc '(reg, (cond, _)) =>
        detect_conflicts_step acc al cond reg detect_conflicts_read1s_reg
      )
      rl None.
  Definition detect_conflicts_write0s (al: action_logs) (rl: write_log)
  : option uact :=
    List.fold_left
      (fun acc '(reg, (cond, _)) =>
        detect_conflicts_step acc al cond reg detect_conflicts_write0s_reg
      )
      rl None.
  Definition detect_conflicts_write1s (al: action_logs) (rl: write_log)
  : option uact :=
    List.fold_left
      (fun acc '(reg, (cond, _)) =>
        detect_conflicts_step acc al cond reg detect_conflicts_write1s_reg
      )
      rl None.

  (* The order of the arguments matters! If there is a conflict between a1 and
     a2, a1 takes precedence. Does not take the fact that rule 1 might fail and
     therefore not impact rule 2 into account, see detect_conflicts for this. *)
  Definition detect_conflicts_actions (a1 a2: action_logs) : option uact :=
    merge_failures
      (merge_failures
        (merge_failures
          (detect_conflicts_read0s a1 (read0s a2))
          (detect_conflicts_read1s a1 (read1s a2))
        )
        (detect_conflicts_write0s a1 (write0s a2))
      )
      (detect_conflicts_write1s a1 (write1s a2)).

  (* Returns a failure condition for ri2's conflicts with ri1. Includes ri1's
     initial failure condition. *)
  Definition detect_conflicts (ri1 ri2: rule_information) : option uact :=
    merge_failures
      (failure_cond ri2)
      (match detect_conflicts_actions (actions ri1) (actions ri2) with
       | None => None
       | Some x =>
         match failure_cond ri1 with
         | None => Some x
         | Some y =>
           let not_failure_1 := UUnop (PrimUntyped.UBits1 PrimUntyped.UNot) y in
           (* If rule 1 fails, then it can't cause rule 2 to fail. *)
           Some (UBinop (PrimUntyped.UBits2 PrimUntyped.UAnd) not_failure_1 x)
         end
       end
      ).

  (* D.2. Conflicts with any prior rule *)
  Definition detect_conflicts_any_prior
    (r: rule_information) (prior_rules: list rule_information)
  : rule_information :=
    List.fold_left
      (fun r' p =>
        {| actions := actions r'; failure_cond := detect_conflicts p r' |}
      )
      prior_rules
      r.

  (* D.3. All scheduling conflicts *)
  (* This function detects all the scheduling conflicts. It returns a list of
     rule_information where the failure conditions have been edited
     appropriately. *)
  Definition detect_all_conflicts (rl: list rule_information)
  : list action_logs :=
    List.map
      (fun x => actions x)
      (List.fold_left
        (fun acc c =>
          match acc with
          | [] => [c]
          | h::t => List.app acc [detect_conflicts_any_prior c acc]
          end
        )
        rl
        []).

  (* E. Schedule merger *)
  (* Starting from a schedule with all the right failures conditions under the
     form of a list of rule_information structures (see D.), we want to get to a
     schedule_information structure (which is a collection of actions with no
     failure condition, as a schedule can't fail). *)
  (* E.1. Integrate failure conditions into actions *)
  (* We start by extracting the action logs of all the rules in the schedule. In
     fact, the failure condition was just a building block: we can remove it
     without losing information as long as we integrate it into the conditions
     of all the actions of the rule it guarded. *)
  Definition prepend_condition_reads (cond: uact) (rl: read_log) : read_log :=
    List.map
      (fun '(reg, (cond', name)) =>
        (reg, (UBinop (PrimUntyped.UBits2 PrimUntyped.UAnd) cond cond', name))
      )
      rl.
  Definition prepend_condition_writes (cond: uact) (wl: write_log)
  : write_log :=
    List.map
      (fun '(reg, (cond', val)) =>
        (reg, (UBinop (PrimUntyped.UBits2 PrimUntyped.UAnd) cond cond', val))
      )
      wl.
  Definition prepend_condition_extcalls (cond: uact) (el: extcall_log)
  : extcall_log :=
    List.map
      (fun '(ufn, (cond', name, arg)) =>
        (ufn,
          (UBinop (PrimUntyped.UBits2 PrimUntyped.UAnd) cond cond', name, arg)
        )
      )
      el.

  Definition prepend_failure_actions (ri: rule_information) : action_logs :=
    let not_failure :=
      UUnop (PrimUntyped.UBits1 PrimUntyped.UNot) (reduce (failure_cond ri))
    in
    let al := actions ri in {|
      read0s := prepend_condition_reads not_failure (read0s al);
      read1s := prepend_condition_reads not_failure (read1s al);
      write0s := prepend_condition_writes not_failure (write0s al);
      write1s := prepend_condition_writes not_failure (write1s al);
      extcalls := prepend_condition_extcalls not_failure (extcalls al);
    |}.

  Definition integrate_failures (ri: list rule_information)
  : list action_logs :=
    List.map prepend_failure_actions ri.

  (* E.2. Merge duplicated actions across rules *)
  (* At this point, we know that there is at most only one rd0/rd1/wr0/wr1
     targeting a register in each action - see C.1.b. for details. This is not
     true for external calls however and does not need to be (the same external
     call can occur multiple times in a single cycle).

     Note that names need to be updated. For instance in the situation where
     rule 1 reads register r on port 0 and names the result "bind0" whereas rule
     2 performs the same action but uses the name "bind3" instead, it might well
     be that one of rule 2's external calls refers "bind3". If the actions are
     merged and the name "bind0" is kept, all the references to "bind3" have to
     be updated accordingly. *)
  (* E.2.a. Names update *)
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
    | UUnop ufn a => UUnop ufn (rename_in_uact from to a)
    | _ => ua
    end.

  Definition map_names_w (name_map: list (string * string)) (wl: write_log)
  : write_log :=
    List.fold_left
      (fun wl' '(from, to) =>
        List.map
          (fun '(reg, (cond, val)) =>
            (reg, (rename_in_uact from to cond, rename_in_uact from to val))
          )
          wl'
      )
      name_map
      wl.

  Definition map_names_e (name_map: list (string * string)) (el: extcall_log)
  : extcall_log :=
    List.fold_left
      (fun el' '(from, to) =>
        List.map
          (fun '(reg, (cond, name, val)) =>
            (reg,
             (rename_in_uact from to cond, name, rename_in_uact from to val)
            )
          )
          el'
      )
      name_map
      el.

  (* E.2.b. Merge one rule *)
  (* TODO maybe make conds optional in xxx_info *)
  (* Returns updated name if appropriate. Used for both read0 and read1. *)
  Definition merge_next_read (rl: read_log) (r: read_info)
  : read_log * option string :=
    let (reg, rst) := r in
    let (cond, name) := rst in
    let prev := list_assoc rl reg in
    match prev with
    | None => (list_assoc_set rl reg (cond, name), None)
    | Some (prev_cond, prev_name) => (
      list_assoc_set
        rl reg
        (UBinop (PrimUntyped.UBits2 PrimUntyped.UOr) prev_cond cond, prev_name),
      Some prev_name
    )
    end.

  (* Used for both write0 and write1. *)
  Definition merge_next_write (wl: write_log) (w: write_info) : write_log :=
    let (reg, rst) := w in
    let (cond, val) := rst in
    let prev := list_assoc wl reg in
    match prev with
    | None => list_assoc_set wl reg (cond, val)
    | Some (prev_cond, prev_val) =>
      list_assoc_set
        wl reg
        (UBinop (PrimUntyped.UBits2 PrimUntyped.UOr) prev_cond cond,
        (* We know that the conditions are mutually exclusive *)
         UIf cond val prev_val
        )
    end.

  Definition merge_reads_single_rule (rl_acc rl_curr: read_log)
  : read_log * list (string * string) :=
    List.fold_left
      (fun '(rl_acc', name_map) n =>
        let (rl_acc'', new_name) := merge_next_read rl_acc' n in
        match new_name with
        | None => (rl_acc'', name_map)
        | Some x => (rl_acc'', (snd (snd n), x)::name_map)
        end
      )
      rl_curr
      (rl_acc, []).

  Definition merge_writes_single_rule (wl_acc wl_curr: write_log) : write_log :=
    List.fold_left merge_next_write wl_curr wl_acc.

  Definition merge_single_rule (acc_log rule_logs: action_logs) : action_logs :=
    let (read0s', name_map_0) :=
      merge_reads_single_rule (read0s acc_log) (read0s rule_logs)
    in
    let (read1s', name_map_1) :=
      merge_reads_single_rule (read0s acc_log) (read1s rule_logs)
    in
    let write0s' :=
      merge_writes_single_rule
        (write0s acc_log)
        (map_names_w name_map_1 (map_names_w name_map_0 (write0s rule_logs)))
    in
    let write1s' :=
      merge_writes_single_rule
        (write1s acc_log)
        (map_names_w name_map_1 (map_names_w name_map_0 (write1s rule_logs)))
    in
    let extcalls' :=
      app
        (extcalls acc_log)
        (map_names_e name_map_1 (map_names_e name_map_0 (extcalls rule_logs)))
    in
    {| read0s := read0s'; read1s := read1s'; write0s := write0s';
       write1s := write1s'; extcalls := extcalls'
    |}.

  (* E.2.b. Merge full schedule *)
  Definition merge_schedule (rules_logs: list action_logs)
  : schedule_information :=
    match hd_error rules_logs with
    | None => {|
      read0s := []; read1s := []; write0s := []; write1s := []; extcalls := []
    |}
    | Some x => List.fold_left merge_single_rule (tl rules_logs) x
    end.

  (* F. Final simplifications *)
  (* At this stage, we know that there is at most one rd0/rd1/wr0/wr1 in the
     schedule_information. *)
  (* F.1. Remove read1s *)
  (* F.1.a. Replacement of variables by expression *)
  Fixpoint replace_var_by_uact_in_uact (from: string) (to ua: uact) :=
    match ua with
    | UVar v =>
      if String.eqb from v then to else UVar v
    | UIf cond tb fb =>
      UIf
        (replace_var_by_uact_in_uact from to cond)
        (replace_var_by_uact_in_uact from to tb)
        (replace_var_by_uact_in_uact from to fb)
    | UBinop ufn a1 a2 =>
      UBinop
        ufn
        (replace_var_by_uact_in_uact from to a1)
        (replace_var_by_uact_in_uact from to a2)
    | UUnop ufn a => UUnop ufn (replace_var_by_uact_in_uact from to a)
    | _ => ua
    end.

  Definition replace_var_by_uact_w (w: write_log) (from: string) (to: uact)
  : write_log :=
    List.map
      (fun '(reg, (cond, val)) =>
        (reg,
          (replace_var_by_uact_in_uact from to cond,
           replace_var_by_uact_in_uact from to val
          )
        )
      )
      w.

  Definition replace_var_by_uact_e (e: extcall_log) (from: string) (to: uact)
  : extcall_log :=
    List.map
      (fun '(reg, (cond, name, val)) =>
        (reg,
          (replace_var_by_uact_in_uact from to cond, name,
           replace_var_by_uact_in_uact from to val
          )
        )
      )
      e.

  Definition replace_var_by_uact
    (s: schedule_information) (from: string) (to: uact)
  : schedule_information :=
    {| read0s := read0s s; read1s := read1s s;
       write0s := replace_var_by_uact_w (write0s s) from to;
       write1s := replace_var_by_uact_w (write1s s) from to;
       extcalls := replace_var_by_uact_e (extcalls s) from to
    |}.

  (* F.1.b. Removal *)
  (* This function can actually modify the schedule information! This is because
     in situations where no read0 occurs, we need to add one for use in read1's
     replacement. We therefore also need to pass it the last controlled id. *)
  Definition get_value_at_read1
    (s: schedule_information) (rd1_cond: uact) (r: reg_t) (last_controlled: nat)
  : uact * schedule_information * nat :=
    let '(read0s', rd0_name, lc') :=
      match list_assoc (read0s s) r with
      | None => (* create new binding *)
        let new_name := generate_binding_name (last_controlled + 1) in
        (list_assoc_set (read0s s) r (rd1_cond, new_name), new_name,
         last_controlled + 1)
      | Some (rd0_cond, rd0_name) => (* ensure read0 triggers when needed *)
        (list_assoc_set
           (read0s s) r
           (UBinop (PrimUntyped.UBits2 PrimUntyped.UOr) rd1_cond rd0_cond,
            rd0_name
           ),
         rd0_name, last_controlled
        )
      end
    in (
      match list_assoc (write0s s) r with
      | None => UVar rd0_name
      | Some (wr0_cond, wr0_val) => UIf wr0_cond wr0_val (UVar rd0_name)
      end,
      upd_read0 s read0s', lc'
    ).

  Definition remove_single_read1
    (s: schedule_information) (last_controlled: nat) (rd: read_info)
  : schedule_information * nat :=
    let '(reg, rst) := rd in
    let '(cond, name) := rst in
    (* Wr0, wr1 and extcalls impacted *)
    let '(val, s', lc') := get_value_at_read1 s cond reg last_controlled in
    (replace_var_by_uact s name val, lc').

  (* We don't care about last controlled after this pass, hence no nat in
     return type. *)
  Definition remove_read1s (s: schedule_information) (last_controlled: nat)
  : schedule_information :=
    let (s'', lc'') :=
      List.fold_left
        (fun '(s', lc') rd =>
          remove_single_read1 s' lc' rd
        )
        (read1s s)
        (s, last_controlled)
    in upd_read1 s'' [].

  (* F.2. Remove write0s *)
  (* If there is both a write0 and a write1, the write1 takes priority.
     Otherwise, promote to write1. *)
  Definition remove_single_write0 (s: schedule_information) (wr: write_info)
  : schedule_information :=
    let '(reg, rst) := wr in
    let '(cond, val) := rst in
    match list_assoc (write1s s) reg with
    | None => upd_write1 s (list_assoc_set (write1s s) reg (cond, val))
    | Some (wr1_cond, wr1_val) =>
      upd_write1
        s
        (list_assoc_set
          (write1s s) reg
          (UBinop (PrimUntyped.UBits2 PrimUntyped.UOr) wr1_cond cond,
           UIf wr1_cond wr1_val val
          )
        )
    end.

  Definition remove_write0s (s: schedule_information) : schedule_information :=
    let s' := List.fold_left remove_single_write0 (write0s s) s in
    upd_write0 s' [].

  (* G. Normalization *)
  (* Schedule can contain try or spos, but they are not used in the case we care
     about. *)
  Fixpoint schedule_to_list_of_rules (s: schedule) : list uact :=
    match s with
    | Done => []
    | Cons r s' => (rules r)::(schedule_to_list_of_rules s')
    | _ => []
    end.

  (* Precondition: only Cons and Done in schedule. *)
  Definition schedule_to_normal_form (s: schedule) : normal_form :=
    (* Get list of uact from scheduler *)
    let rules_l := schedule_to_list_of_rules s in
    (* Prepare binding names generation *)
    let last_controlled_init :=
      list_max (List.map (get_highest_binding_number) rules_l)
    in
    (* Get rule_information from each rule*)
    let (rule_info_l, lc') :=
      List.fold_right
        (fun r '(ri_acc, lc') =>
          let (ri, lc'') := distill r lc' in
          (ri::ri_acc, lc'')
        )
        ([], last_controlled_init)
        rules_l
    in
    (* Factor inter-rules conflicts in *)
    let rule_info_with_conflicts_l := detect_all_conflicts rule_info_l in
    (* To schedule info *)
    let schedule_info := merge_schedule rule_info_with_conflicts_l in
    (* Remove read1s and write0s *)
    let schedule_info_simpl :=
      remove_write0s (remove_read1s schedule_info lc')
    in
    (* To normal form *)
    {| reads := read0s schedule_info_simpl;
       writes := write1s schedule_info_simpl;
       external_calls := extcalls schedule_info_simpl
    |}.
End Normalize.
Close Scope nat.
