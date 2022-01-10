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
  (* bind_name * value *)
  Definition var_value_pair : Type := string * uact.
  Definition var_value_map := list var_value_pair.
  Record action_logs := mkActions {
    read0s: read_log;
    read1s: read_log;
    write0s: write_log;
    write1s: write_log;
    extcalls: extcall_log;
  }.
  Record rule_information := mkRuleInformation {
    actions: action_logs;
    var_val_map: var_value_map;
    (* We do not worry about potential conflicts in action logs. What if we
       stumble on two write1s on register x? We simply register the write1s as
       they stand, but update the following condition for the whole rule: *)
    failure_cond: option uact;
  }.
  (* Note that we did not reuse uact for that purpose as that could have made
     things confusing (we consider a set of actions and not a sequence). *)
  Record schedule_information := mkSceduleInformation {
    sc_actions : action_logs;
    sc_vars : var_value_map;
  }.
  Record normal_form := mkNormalForm {
    reads: read_log;
    writes: write_log;
    variables: var_value_map;
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

  Scheme Equality for option.
  Definition action_binding_prefix := "action_bind_".
  Definition expr_binding_prefix := "expr_bind_".
  Inductive binding_type := action | expr.

  Definition get_prefix (b: binding_type) :=
    match b with
    | action => action_binding_prefix
    | expr => expr_binding_prefix
    end.

  Definition extract_custom_binding_digits (b: binding_type) (s: string)
  : list ascii :=
    let pl := String.length (get_prefix b) in
    String.list_ascii_of_string (String.substring pl (String.length s - pl) s).

  Definition matches_binding_form (b: binding_type) (s: string) : bool :=
    let prefix := get_prefix b in
    let maybe_digits := extract_custom_binding_digits b s in
    (String.prefix prefix s)
    && (negb (Nat.eqb (List.length maybe_digits) 0))
    && (List.forallb is_digit maybe_digits)
    (* First digit not zero - <binding_prefix>0 does not exist, start at 1*)
    && (negb
      (option_beq
        ascii (Ascii.eqb) (List.hd_error maybe_digits) (Some "0"%char)
      )
    ).

  (* B.2. Variables generation *)
  Definition get_highest_binding_id (b: binding_type) (ua: uact) : nat :=
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
      List.filter (matches_binding_form b) binding_names
    in
    let binding_numbers :=
      List.map
        (fun s => digits_to_nat (extract_custom_binding_digits b s))
        matching_bindings
    in
    List.list_max binding_numbers.

  Definition generate_binding_name (b: binding_type) (n: nat) : string :=
    String.append (get_prefix b) (NilEmpty.string_of_uint (Init.Nat.to_uint n)).

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
    (* No need to pass failures as these impact the whole rule - taking note of
       all of them and factoring the conditions in is enough. Conflicts between
       different actions are also dealt with here - see C.1. *)
    (ua: uact) (var_map: list (string * string)) (guard: uact) (al: action_logs)
    (last_action_id last_expr_id: nat)
    (* Returns value, var_map, var_values, failure condition, action_logs,
       last_action_id, last_expr_id *)
  : option uact * list (string * string) * (list (string * uact))
    * (option uact) * action_logs * nat * nat
  :=
    let la := last_action_id in
    let le := last_expr_id in
    match ua with
    | UBind var val body =>
      let '(ret_val, vm_val, vv_val, failures_val, al_val, la_val, le_val) :=
        distill_aux val var_map guard al la le
      in
      let name := generate_binding_name expr (S last_expr_id) in
      let '(
        ret_body, vm_body, vv_body, failures_body, al_body, la_body, le_body
      ) :=
        distill_aux
          body (list_assoc_set vm_val var name) guard al_val la_val le_val
      in
      (
        None, List.skipn 1 vm_body, (* Remove the binding to var *)
        ((var, reduce ret_val)::vv_val)++vv_body,
        merge_failures failures_val failures_body, al_body, la_body, le_body
      )
    | UAssign var val =>
      let name := generate_binding_name expr (S last_expr_id) in
      let '(ret_val, vm_val, vv_val, failures_val, al_val, la_val, le_val) :=
        distill_aux val var_map guard al la le
      in
      (None, list_assoc_set vm_val var name, (var, reduce ret_val)::vv_val,
       failures_val, al_val, la_val, le_val)
    | UVar var =>
      match list_assoc var_map var with
      (* If there is no binding and the rule is well formed, then the variable
         has to correspond to an action and can be left unchanged. *)
      | None => (Some (UVar var), var_map, [], None, al, la, le)
      | Some x => (Some (UVar x), var_map, [], None, al, la, le)
      end
    | USeq a1 a2 =>
      let '(_, vm_a1, vv_a1, failures_a1, al_a1, la_a1, le_a1) :=
        distill_aux a1 var_map guard al la le
      in
      let '(ret_a2, vm_a2, vv_a2, failures_a2, al_a2, la_a2, le_a2) :=
        distill_aux a2 vm_a1 guard al_a1 la_a1 le_a1
      in
      (ret_a2, vm_a2, vv_a1++vv_a2, merge_failures failures_a1 failures_a2,
       al_a2, la_a2, le_a2)
    | UIf cond tb fb =>
      let '(
        ret_cond, vm_cond, vv_cond, failures_cond, al_cond, la_cond, le_cond
      ) :=
        distill_aux cond var_map guard al la le
      in
      let cond_name := generate_binding_name expr (S le_cond) in
      let guard_tb :=
        UBinop (PrimUntyped.UBits2 PrimUntyped.UAnd) guard (UVar cond_name)
      in
      let guard_fb :=
        UBinop (PrimUntyped.UBits2 PrimUntyped.UAnd)
          guard (UUnop (PrimUntyped.UBits1 PrimUntyped.UNot) (UVar cond_name))
      in
      let '(ret_tb, vm_tb, vv_tb, failures_tb, al_tb, la_tb, le_tb) :=
        distill_aux tb vm_cond guard_tb al_cond la_cond (S le_cond)
      in
      let '(ret_fb, vm_fb, vv_fb, failures_fb, al_fb, la_fb, le_fb) :=
        (* We use al_tb here even though we know that none of the actions added
           by the other branch can impact those from this branch as they are
           mutually exclusive. Plus, this way, we don't have to deal with
           action_logs merging. *)
        distill_aux fb vm_cond guard_fb al_tb la_tb le_tb
      in
      let '(vm_merge, vv_merge, le_merge) :=
        List.fold_left
          (fun '(acc, vv', le') '((str, n1), (_, n2)) =>
            if String.eqb n1 n2 then ((str, n1)::acc, vv', le')
            else
              let name := generate_binding_name expr (S le') in
              (
                (str, name)::acc,
                (name, UIf (UVar cond_name) (UVar n1) (UVar n2))::vv',
                S le'
              )
          )
          (List.combine vm_tb vm_fb)
          ([], [], le_tb)
      in
      (merge_uacts cond ret_tb ret_fb,
       vm_merge,
       (cond_name, reduce ret_cond)::vv_merge++vv_cond++vv_tb++vv_fb,
       match ret_cond with
       | None => (* Should never happen in a well-formed rule *)
         None
       | Some x =>
         merge_failures
          failures_cond
          (merge_failures
            (option_map
              (fun y => UBinop (PrimUntyped.UBits2 PrimUntyped.UAnd) x y)
              failures_tb
            )
            (option_map
              (fun y =>
                (UBinop (PrimUntyped.UBits2 PrimUntyped.UAnd)
                  (UUnop (PrimUntyped.UBits1 PrimUntyped.UNot) x) y
                )
              )
              failures_fb
            )
          )
        end,
        al_fb, la_fb, le_merge)
    | UUnop ufn a =>
      let '(ret_a, vm_a, vv_a, failures_a, al_a, la_a, le_a) :=
        distill_aux a var_map guard al la le
      in
      (Some (UUnop ufn (reduce ret_a)), vm_a, vv_a, failures_a, al_a, la_a,
       le_a)
    | UBinop ufn a1 a2 =>
      let '(ret_a1, vm_a1, vv_a1, failures_a1, al_a1, la_a1, le_a1) :=
        distill_aux a1 var_map guard al la le
      in
      let '(ret_a2, vm_a2, vv_a2, failures_a2, al_a2, la_a2, le_a2) :=
        distill_aux a2 vm_a1 guard al_a1 la_a1 le_a1
      in
      (Some (UBinop ufn (reduce ret_a1) (reduce ret_a2)), vm_a2, vv_a1++vv_a2,
       merge_failures failures_a1 failures_a2, al_a2, la_a2, le_a2)
    | UInternalCall ufn args =>
      let '(
        arg_names, vm_args, vv_args, failure_args, al_args, la_args, le_args
      ) :=
        (
          List.fold_left
            (fun '(names, vm_p, vv_p, failures_p, al_p, la_p, le_p) a =>
              let '(val_c, vm_c, vv_c, failure_c, al_c, la_c, le_c) :=
                distill_aux a vm_p guard al_p la_p le_p
              in
              let arg_bind_name := generate_binding_name expr (S le_c) in
              (
                arg_bind_name::names, vm_c,
                (arg_bind_name, reduce val_c)::vv_c++vv_p,
                merge_failures failure_c failures_p, al_c, la_c, S le_c
              )
            )
            args
            ([], var_map, [], None, al, la, le)
        ) in
      let vm_tmp :=
        combine
          (fst (split (int_argspec ufn))) (* Names from argspec *)
          (* We know that a value is assigned to each argument in well formed
             models *)
          arg_names
      in
      let '(ret_ic, _, vv_ic, failure_ic, al_ic, la_ic, le_ic) :=
        distill_aux (int_body ufn) vm_tmp guard al_args la_args le_args
      in
      (* We drop vm_tmp which contained the temporary map for use in the called
         function. *)
      (ret_ic, vm_args, vv_ic++vv_args, merge_failures failure_ic failure_args,
       al_ic, la_ic, le_ic)
    | UAPos _ e => distill_aux e var_map guard al la le
    | URead port reg =>
      let fresh_name := generate_binding_name action (S la) in
      let '(modified_al, failure_read, used_name) :=
        match port with
        | P0 => add_read0 al guard reg fresh_name
        | P1 => add_read1 al guard reg fresh_name
        end
      in
      let new_la := if String.eqb fresh_name used_name then S la else la in
      (
        Some (UVar (used_name)), var_map, [], failure_read, modified_al, new_la,
        le
      )
    | UWrite port reg val =>
      let '(
        ret_val, vm_val, vv_val, failures_val, actions_val, la_val, le_val
      ) :=
        distill_aux val var_map guard al la le
      in
      let '(al_wr, failure_wr) :=
        match port with
        | P0 => add_write0 actions_val guard (reduce ret_val) reg
        | P1 => add_write1 actions_val guard (reduce ret_val) reg
        end
      in
      (None, vm_val, vv_val, merge_failures failures_val failure_wr, al_wr,
       la_val, le_val)
    | UExternalCall ufn arg =>
      let '(
        ret_arg, vm_arg, vv_arg, failures_arg, actions_arg, la_arg, le_arg
      ) :=
        distill_aux arg var_map guard al la le
      in
      let fresh_name := generate_binding_name action (S la_arg) in
      let new_al := add_extcall al ufn guard arg fresh_name in
      (Some (UVar fresh_name), vm_arg, vv_arg, failures_arg, new_al, S la_arg,
       le_arg)
    | UError _ =>
      (None, var_map, [], Some (UConst (tau := bits_t 1) (Bits.of_nat 1 1)), al,
       la, le)
    | UFail _ =>
      (None, var_map, [], Some (UConst (tau := bits_t 1) (Bits.of_nat 1 1)), al,
       la, le)
    | _ => (* UConst *)
      (Some ua, var_map, [], None, al, la, le)
    end.

  (* This function extracts the actions for a given rule. It also returns the
     highest value used for a custom binding (if rule A and rule B are in a
     schedule, the initial value of last_controlled for rule B should be the
     last value of last_controlled for rule A). *)
  Definition distill (ua: uact) (last_action_id last_expr_id: nat) :
    rule_information * nat * nat
  :=
    let '(_, _, failure, action_logs, last_action_id', last_expr_id') :=
      distill_aux
        ua [] (UConst (tau := bits_t 1) (Bits.of_nat 1 1))
        {|
          read0s := []; read1s := []; write0s := []; write1s := [];
          extcalls := [];
        |}
        last_action_id last_expr_id
    in (
      (* TODO var_val_map *)
      {| actions := action_logs; var_val_map := []; failure_cond := failure; |},
      last_action_id', last_expr_id'
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
        {| actions := actions r'; var_val_map := var_val_map r';
           failure_cond := detect_conflicts p r'
        |}
      )
      prior_rules r.

  (* D.3. All scheduling conflicts *)
  (* This function detects all the scheduling conflicts. It returns a list of
     rule_information where the failure conditions have been edited
     appropriately. *)
  Definition detect_all_conflicts (rl: list rule_information)
  : list rule_information :=
    List.fold_left
      (fun acc c =>
        match acc with
        | [] => [c]
        | h::t => List.app acc [detect_conflicts_any_prior c acc]
        end
      )
      rl [].

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
  : list rule_information :=
    List.map
      (fun r => {|
         actions := prepend_failure_actions r;
         failure_cond := None;
         var_val_map := var_val_map r
       |}
      )
      ri.

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

  Definition map_names_extc (name_map: list (string * string)) (el: extcall_log)
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

  Definition map_names_expr
    (name_map: list (string * string)) (expr: var_value_map)
  : var_value_map :=
    List.fold_left
      (fun vvm' '(from, to) =>
        List.map (fun '(name, val) => (name, rename_in_uact from to val)) vvm'
      )
      name_map
      expr.

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

  Definition merge_single_rule (s: schedule_information) (r: rule_information)
  : schedule_information :=
    let rule_logs := actions r in
    let rule_exprs := var_val_map r in
    (* failure_cond can be ignored as it already was integrated *)
    let acc_log := sc_actions s in
    let acc_exprs := sc_vars s in
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
        (map_names_extc name_map_1 (map_names_extc name_map_0 (
          extcalls rule_logs
        )))
    in {|
      sc_actions := {|
        read0s := read0s'; read1s := read1s'; write0s := write0s';
        write1s := write1s'; extcalls := extcalls'
      |};
      sc_vars :=
        List.concat [
          map_names_expr name_map_1 (acc_exprs);
          rule_exprs
        ]
    |}.

  (* E.2.b. Merge full schedule *)
  Definition merge_schedule (rules_info: list rule_information)
  : schedule_information :=
    let rules_info' := integrate_failures rules_info in
    (* TODO really necessary? Wouldn't a direct fold left suffice? *)
    match hd_error rules_info' with
    | None => {|
        sc_actions := {|
          read0s := []; read1s := []; write0s := []; write1s := [];
          extcalls := []
        |};
        sc_vars := []
      |}
    | Some x =>
      List.fold_left
        merge_single_rule
        (tl rules_info')
        {| sc_actions := actions x; sc_vars := var_val_map x; |}
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

  Definition replace_var_by_uact_extc (e: extcall_log) (from: string) (to: uact)
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

  Definition replace_var_by_uact_expr
    (v: var_value_map) (from: string) (to: uact)
  : var_value_map :=
    List.map
      (fun '(reg, val) => (reg, replace_var_by_uact_in_uact from to val))
      v.

  (* Variables bound to the return values of read1s need to be replaced with the
     appropriate value. TODO store res as expr instead and change name only *)
  Definition replace_var_by_uact
    (s: schedule_information) (from: string) (to: uact)
  : schedule_information :=
    let a := sc_actions s in
    {|
      sc_actions := {|
        read0s := read0s a; read1s := read1s a;
        write0s := replace_var_by_uact_w (write0s a) from to;
        write1s := replace_var_by_uact_w (write1s a) from to;
        extcalls := replace_var_by_uact_extc (extcalls a) from to
      |};
      sc_vars := replace_var_by_uact_expr (sc_vars s) from to
    |}.

  (* F.1.b. Removal *)
  (* This function can actually modify the schedule information! This is because
     in situations where no read0 occurs, we need to add one for use in read1's
     replacement. We therefore also need to pass it the last action id. *)
  Definition get_value_at_read1
    (s: schedule_information) (rd1_cond: uact) (r: reg_t) (last_action_id: nat)
  : uact * schedule_information * nat :=
    let a := sc_actions s in
    let '(read0s', rd0_name, lc') :=
      match list_assoc (read0s a) r with
      | None => (* create new binding *)
        let new_name := generate_binding_name action (last_action_id + 1) in
        (list_assoc_set (read0s a) r (rd1_cond, new_name), new_name,
         last_action_id + 1)
      | Some (rd0_cond, rd0_name) => (* ensure read0 triggers when needed *)
        (list_assoc_set
           (read0s a) r
           (UBinop (PrimUntyped.UBits2 PrimUntyped.UOr) rd1_cond rd0_cond,
            rd0_name
           ),
         rd0_name, last_action_id
        )
      end
    in (
      match list_assoc (write0s a) r with
      | None => UVar rd0_name
      | Some (wr0_cond, wr0_val) => UIf wr0_cond wr0_val (UVar rd0_name)
      end,
      {| sc_actions := upd_read0 a read0s'; sc_vars := sc_vars s |}, lc'
    ).

  Definition remove_single_read1
    (s: schedule_information) (last_action_id: nat) (rd: read_info)
  : schedule_information * nat :=
    let '(reg, rst) := rd in
    let '(cond, name) := rst in
    (* Wr0, wr1 and extcalls impacted *)
    let '(val, s', lc') := get_value_at_read1 s cond reg last_action_id in
    (replace_var_by_uact s name val, lc').

  (* We don't care about last controlled after this pass, hence no nat in return
     type. *)
  Definition remove_read1s (s: schedule_information) (last_action_id: nat)
  : schedule_information :=
    let (s'', la'') :=
      List.fold_left
        (fun '(s', la') rd =>
          remove_single_read1 s' la' rd
        )
        (read1s (sc_actions s))
        (s, last_action_id)
    in {|
      sc_actions := upd_read1 (sc_actions s'') []; sc_vars := sc_vars s''
    |}.

  (* F.2. Remove write0s *)
  (* If there is both a write0 and a write1, the write1 takes priority.
     Otherwise, promote to write1. *)
  (* TODO upd_wr/rd directly for schedule_information? *)
  Definition remove_single_write0 (s: schedule_information) (wr: write_info)
  : schedule_information :=
    let a := sc_actions s in
    let '(reg, rst) := wr in
    let '(cond, val) := rst in
    match list_assoc (write1s a) reg with
    | None => {|
        sc_actions := upd_write1 a (list_assoc_set (write1s a) reg (cond, val));
        sc_vars := sc_vars s
      |}
    | Some (wr1_cond, wr1_val) => {|
        sc_actions :=
          upd_write1
            a
            (list_assoc_set
              (write1s a) reg
              (UBinop (PrimUntyped.UBits2 PrimUntyped.UOr) wr1_cond cond,
               UIf wr1_cond wr1_val val
              )
            );
        sc_vars := sc_vars s
      |}
    end.

  Definition remove_write0s (s: schedule_information) : schedule_information :=
    let s' := List.fold_left remove_single_write0 (write0s (sc_actions s)) s in
    {| sc_actions := upd_write0 (sc_actions s') []; sc_vars := sc_vars s' |}.

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
  (* Precondition: rules desugared. *)
  Definition schedule_to_normal_form (s: schedule) : normal_form :=
    (* Get list of uact from scheduler *)
    let rules_l := schedule_to_list_of_rules s in
    (* Prepare binding names generation *)
    let last_action_init :=
      list_max (List.map (get_highest_binding_id action) rules_l)
    in
    let last_expr_init :=
      list_max (List.map (get_highest_binding_id expr) rules_l)
    in
    (* Get rule_information from each rule*)
    let '(rule_info_l, la', _) :=
      List.fold_right
        (fun r '(ri_acc, la', le') =>
          let '(ri, la'', le'') := distill r la' le' in
          (ri::ri_acc, la'', le'')
        )
        ([], last_action_init, last_expr_init)
        rules_l
    in
    (* Detect inter-rules conflicts *)
    let rule_info_with_conflicts_l := detect_all_conflicts rule_info_l in
    (* To schedule info, merge cancel conditions with actions conditions *)
    let schedule_info := merge_schedule rule_info_with_conflicts_l in
    (* Remove read1s and write0s *)
    let schedule_info_simpl :=
      remove_write0s (remove_read1s schedule_info la')
    in
    (* To normal form *)
    {| reads := read0s (sc_actions schedule_info_simpl);
       writes := write1s (sc_actions schedule_info_simpl);
       variables := sc_vars schedule_info_simpl;
       external_calls := extcalls (sc_actions schedule_info_simpl)
    |}.
End Normalize.

(* TODO switching back to register names instead of "bind<n>" at the end would
   be helpful *)
(* TODO what makes passing writeback to distill so slow? Removing
     Scoreboard.remove and Rf.write_0 fixes this, why? *)
Close Scope nat.
