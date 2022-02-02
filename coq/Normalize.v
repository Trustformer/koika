(*! Proving | Transformation of a schedule into a proof-friendly form !*)
(* TODO Not a normal form anymore but a new model entirely, change name to
        reflect *)
Require Import Coq.Numbers.DecimalString Coq.Program.Equality Coq.Strings.Ascii.
Require Import Koika.BitsToLists Koika.Primitives Koika.Syntax Koika.Utils
  Koika.Zipper.
From RecordUpdate Require Import RecordSet.
Import RecordSetNotations.

(* When reasoning about a Koîka schedule, a lot of tedious implicit mechanisms
   have to be considered explicitly (rules merging, cancellation, ...).
   Furthermore, performance issues related to abstract interpretation make
   reasoning about the behavior of some even moderately complex models (e.g.,
   the RISC-V processor example) an impossibility.

   This is what this simpler form aims to fix. In particular, it makes finding
   under which conditions the value of a register is updated or proving that the
   value of register x never reaches 5 much easier (even trivial in certain
   cases).

   It goes without saying that the result of the interpretation of a model
   before or after its conversion to the form defined hereafter should be equal
   (in terms of the effects of a cycle on the final state of the registers and
   of the emitted extcalls, although the latter are not really considered in
   Koîka's pure semantics). *)

Open Scope nat.
Section Normalize.
  Context {pos_t reg_t ext_fn_t rule_name_t: Type}.
  Context {reg_t_eq_dec: EqDec reg_t}.
  Context {ext_fn_t_eq_dec: EqDec ext_fn_t}.
  Definition uact := uaction pos_t string string reg_t ext_fn_t.
  Definition schedule := scheduler pos_t rule_name_t.

  (* A. Normal form and related structures *)
  Definition read_info := uact.
  Definition read_log := list (reg_t * read_info).
  (* TODO switch back to strings for conds and edit their bindings to include
       failures conditions instead *)
  Record write_info := mkWriteInfo { wcond: uact; wval: uact }.
  Definition write_log := list (reg_t * list (write_info)).
  Record extcall_info := mkExtcallInfo
    { econd: uact; earg: uact; ebind: string }.
  Definition extcall_log := list (ext_fn_t * extcall_info).
  Definition var_value_map := list (string * uact).
  Record action_logs := mkActionLogs {
    read0s: read_log; write0s: write_log; read1s: read_log; write1s: write_log;
    extcalls: extcall_log }.
  Instance etaActionLogs : Settable _ :=
    settable! mkActionLogs < read0s; write0s; read1s; write1s; extcalls >.

  Record rule_information := mkRuleInformation {
    rl_actions: action_logs;
    rl_vars: var_value_map;
    (* We do not worry about potential conflicts in action logs. What if there
       are two write1s targetting register x? We simply register the write1s as
       they stand, but update the following condition for the whole rule: *)
    rl_failure_cond: option uact }.
  (* Note that we did not reuse uact for that purpose as that could have made
     things confusing (we consider a set of actions and not a sequence). *)
  Record schedule_information := mkScheduleInformation {
    sc_actions: action_logs;
    sc_vars: var_value_map; }.
  Record normal_form := mkNormalForm {
    (* Equivalent to disjunction, why not stick to an uact? *)
    intermediate_values: write_log;
    final_values: write_log;
    vars: var_value_map;
    external_calls: extcall_log; }.

  (* B. Bindings names *)
  (* TODO name collisions with previously standing variables can't possibly
       happen anymore (we treat everything in order). This makes it easier to
       give informative names to our variables. *)
  Inductive binding_type :=
  | ctxb | letb | extcb | rcondb | wcondb | fcond_cb | fcond_ncb | ivalb.
  Record next_ids := mkNextIds {
    ctx_id: nat; let_id: nat; extc_id: nat; rcond_id: nat; wcond_id: nat;
    fcond_c_id: nat; fcond_nc_id: nat; ival_id: nat }.
  Instance etaNextIds : Settable _ := settable! mkNextIds <
    ctx_id; let_id; extc_id; rcond_id; wcond_id; fcond_c_id; fcond_nc_id;
    ival_id >.
  Definition initial_ids : next_ids := {|
    ctx_id := 0; let_id := 0; extc_id := 0; rcond_id := 0; wcond_id := 0;
    fcond_c_id := 0; fcond_nc_id := 0; ival_id := 0 |}.

  Definition get_prefix (b: binding_type) : string :=
    match b with
    | ctxb => "ctx_" | letb => "let_" | extcb => "extc_" | rcondb => "rcond_"
    | wcondb => "wcond_" | fcond_cb => "fcond_c_" | fcond_ncb => "fcond_nc_"
    | ivalb => "ival_"
    end.

  Definition generate_binding_name (b: binding_type) (n: nat) : string :=
    String.append (get_prefix b) (NilEmpty.string_of_uint (Init.Nat.to_uint n)).

  (* C. rule_information extraction *)
  (* C.1. Addition of a new action into an existing rule_information *)
  (* C.1.a. Merger of failure conditions *)
  Definition or_conds (conds: list uact) :=
    fold_left
      (fun acc c =>
        match acc with
        | None => Some c
        | Some x => Some (UBinop (PrimUntyped.UBits2 PrimUntyped.UOr) c x)
        end)
      conds None.

  Definition merge_failures (f1 f2: option uact) : option uact :=
    match f1, f2 with
    | None, None => None
    | Some x, None => Some x
    | None, Some x => Some x
    | Some x, Some y => Some (UBinop (PrimUntyped.UBits2 PrimUntyped.UOr) x y)
    end.

  Definition build_uif (cond ua1 ua2: option uact) : option uact :=
    (* We know that the original if being valid implies that cond != None and
       ua1 = Some x iff. ua2 = Some y *)
    match cond, ua1, ua2 with
    | Some c, Some x, Some y => Some (UIf c x y)
    | _, _, _ => None
    end.

  (* C.1.b. Merger of actions *)
  (* Remove Nones from list, turn rest from (Some x) to x. *)
  Definition list_options_to_list (l: list (option uact)) : list uact :=
    map
      (fun i =>
        match i with
        | Some x => x
        | None => (UConst (tau := bits_t 0) (Bits.of_nat 0 0)) (* Unreachable *)
        end)
      (filter
        (fun i => match i with None => false | Some _ => true end) l).

  Definition merge_conds (wl: option (list write_info)) : option uact :=
    match wl with
    | None => None
    | Some l =>
      fold_left
        (fun acc entry =>
          match acc with
          | None => Some (wcond entry)
          | Some x => Some (
            UBinop (PrimUntyped.UBits2 PrimUntyped.UOr) x (wcond entry))
          end)
        l
        None
    end.

  Definition extract_wr_cond (wl: write_log) (reg: reg_t) :=
    merge_conds (list_assoc wl reg).

  Definition merge_failures_list (action_cond: uact) (conds: list uact) :=
    match or_conds conds with
    | None => None
    | Some x =>
      Some (UBinop (PrimUntyped.UBits2 PrimUntyped.UAnd) action_cond x)
    end.

  Definition add_read0 (al: action_logs) (guard: string) (reg: reg_t)
  (* Returns modified action_logs, failure conditions *)
  : action_logs * option uact :=
    let prev_wr0 := extract_wr_cond (write0s al) reg in
    let prev_wr1 := extract_wr_cond (write1s al) reg in
    let grd := UVar (guard) in
    let failure_cond :=
      merge_failures_list grd (list_options_to_list [prev_wr0; prev_wr1])
    in
    match list_assoc (read0s al) reg with
    | None =>
      (al <| read0s := list_assoc_set (read0s al) reg grd |>, failure_cond)
    | Some cond' => (
      al <|
        read0s :=
          list_assoc_set (read0s al) reg
            (UBinop (PrimUntyped.UBits2 PrimUntyped.UOr) grd cond')
      |>, failure_cond)
    end.

  Definition add_read1 (al: action_logs) (guard: string) (reg: reg_t)
  (* Returns modified action_logs, failure conditions *)
  : action_logs * option uact :=
    let prev_wr1 := extract_wr_cond (write1s al) reg in
    let grd := UVar (guard) in
    let failure_cond :=
      merge_failures_list grd (list_options_to_list [prev_wr1])
    in
    match list_assoc (read1s al) reg with
    | None => (
      al <| read1s := list_assoc_set (read1s al) reg grd |>, failure_cond)
    | Some cond' => (
      al <|
        read1s :=
          list_assoc_set (read1s al) reg
            (UBinop (PrimUntyped.UBits2 PrimUntyped.UOr) grd cond')
      |>, failure_cond)
    end.

  Definition add_write0
    (al: action_logs) (guard: string) (reg: reg_t) (val: uact)
  (* Returns modified action_logs, failure conditions *)
  : action_logs * option uact :=
    let prev_wr0 := extract_wr_cond (write0s al) reg in
    let prev_rd1 := list_assoc (read1s al) reg in
    let prev_wr1 := extract_wr_cond (write1s al) reg in
    let grd := UVar (guard) in
    let failure_cond :=
      merge_failures_list
        grd (list_options_to_list [prev_wr0; prev_wr1; prev_rd1])
    in
    (* Somewhat redundant with extract_write0_cond *)
    match list_assoc (write0s al) reg with
    | None => (
      al <|
        write0s :=
          list_assoc_set
            (write0s al) reg [{| wcond := UVar guard; wval := val |}]
      |>, failure_cond)
    | Some l => (
      al <|
        write0s :=
          list_assoc_set (write0s al) reg
          (l++[{| wcond := UVar guard; wval := val |}])
      |>, failure_cond)
    end.

  Definition add_write1
    (al: action_logs) (guard: string) (reg: reg_t) (val: uact)
  (* Returns modified action_logs, failure conditions *)
  : action_logs * option uact :=
    let prev_wr1 := extract_wr_cond (write1s al) reg in
    let grd := UVar (guard) in
    let failure_cond :=
      merge_failures_list grd (list_options_to_list [prev_wr1])
    in
    (* Somewhat redundant with extract_write0_cond *)
    match list_assoc (write1s al) reg with
    | None => (
      al <|
        write1s :=
          list_assoc_set
            (write1s al) reg [{| wcond := UVar guard; wval := val |}]
      |>, failure_cond)
    | Some l => (
      al <|
        write1s :=
          list_assoc_set (write1s al) reg
          (l++[{| wcond := UVar guard; wval := val |}])
      |>, failure_cond)
    end.

  Definition add_extcall
    (al: action_logs) (guard: string) (ufn: ext_fn_t) (arg: uact) (name: string)
  : action_logs :=
    al <|
      extcalls :=
        (ufn,
          {| econd := UVar guard; earg := arg; ebind := name |}
        )::(extcalls al)
    |>.

  (* C.2. Extraction of actions from rule *)
  Definition reduce (ua: option uact) : uact :=
    match ua with
    | None => UConst (tau := bits_t 0) (Bits.of_nat 0 0)
    | Some x => x
    end.

  (* This function extracts the actions for a given rule. It also returns the
     updated next_ids structure. *)
  Fixpoint get_rule_information_aux
    (* No need to pass failures as these impact the whole rule - taking note of
       all of them and factoring the conditions in is enough. Conflicts between
       different actions are also dealt with here - see C.1. *)
    (* TODO improve guards management *)
    (ua: uact) (var_map: list (string * string)) (guard: uact) (al: action_logs)
    (nid: next_ids)
    (* Returns value, var_map, var_values, failure condition, action_logs,
       next_ids *)
  : option uact * list (string * string) * (list (string * uact))
    * (option uact) * action_logs * next_ids
  :=
    match ua with
    | UBind var val body =>
      let '(ret_val, vm_val, vv_val, failures_val, al_val, nid_val) :=
        get_rule_information_aux val var_map guard al nid
      in
      let name := generate_binding_name letb (S (let_id nid_val)) in
      let '(ret_body, vm_body, vv_body, failures_body, al_body, nid_body) :=
        get_rule_information_aux
          body ((name, var)::var_map) guard al_val
          (nid_val <| let_id := S (let_id nid_val) |>)
      in (
        None, skipn 1 vm_body, (* var's binding goes out of scope *)
        vv_val++[(name, reduce ret_val)]++vv_body,
        merge_failures failures_val failures_body, al_body, nid_body)
    | UAssign var val =>
      let '(ret_val, vm_val, vv_val, failures_val, al_val, nid_val) :=
        get_rule_information_aux val var_map guard al nid
      in
      let name := generate_binding_name letb (S (let_id nid_val)) in
      (None, list_assoc_set vm_val var name, vv_val++[(name, reduce ret_val)],
       failures_val, al_val, nid_val <| let_id := S (let_id nid_val) |>
      )
    | UVar var =>
      match list_assoc var_map var with
      | Some x => (Some (UVar x), var_map, [], None, al, nid)
      | None => (* Unreachable assuming rule valid *)
        (Some (UVar "ERROR"), var_map, [], None, al, nid)
      end
    | USeq a1 a2 =>
      let '(_, vm_a1, vv_a1, failures_a1, al_a1, nid_a1) :=
        get_rule_information_aux a1 var_map guard al nid
      in
      let '(ret_a2, vm_a2, vv_a2, failures_a2, al_a2, nid_a2) :=
        get_rule_information_aux a2 vm_a1 guard al_a1 nid_a1
      in
      (ret_a2, vm_a2, vv_a1++vv_a2, merge_failures failures_a1 failures_a2,
       al_a2, nid_a2)
    | UIf cond tb fb =>
      let '(ret_cond, vm_cond, vv_cond, failures_cond, al_cond, nid_cond) :=
        get_rule_information_aux cond var_map guard al nid
      in
      let cond_name := generate_binding_name ctxb (S (ctx_id nid_cond)) in
      let guard_tb :=
        UBinop (PrimUntyped.UBits2 PrimUntyped.UAnd) guard (UVar cond_name)
      in
      let guard_fb :=
        UBinop (PrimUntyped.UBits2 PrimUntyped.UAnd)
          guard (UUnop (PrimUntyped.UBits1 PrimUntyped.UNot) (UVar cond_name))
      in
      let '(ret_tb, vm_tb, vv_tb, failures_tb, al_tb, nid_tb) :=
        get_rule_information_aux tb vm_cond guard_tb al_cond
        (nid_cond <| ctx_id := (S (ctx_id nid_cond)) |>)
      in
      let '(ret_fb, vm_fb, vv_fb, failures_fb, al_fb, nid_fb) :=
        (* We use al_tb here even though we know that none of the actions added
           by the other branch can impact those from this branch (they are
           mutually exclusive). This way, we don't have to deal with action_logs
           merging. However, this also means that the failure condition will
           contain some redundancy. *)
        get_rule_information_aux fb vm_cond guard_fb al_tb nid_tb
      in
      (* Merge var maps: if vm_tb and vm_fb disagree for some value, generate a
         new variable reflecting the condition and update the variables map. *)
      let '(vm_merge, vv_merge, let_id_merge) :=
        fold_left
          (fun '(acc, vv', let_id) '((str, n1), (_, n2)) =>
            if String.eqb n1 n2 then ((str, n1)::acc, vv', let_id)
            else
              let name := generate_binding_name letb (S let_id) in (
                (str, name)::acc,
                vv'++[(name, UIf (UVar cond_name) (UVar n1) (UVar n2))],
                S let_id))
          (combine vm_tb vm_fb) ([], [], let_id nid_fb)
      in
      (build_uif ret_cond ret_tb ret_fb, vm_merge,
       vv_cond++[(cond_name, reduce ret_cond)]++vv_tb++vv_fb++vv_merge,
       (* Merging the failure conditions: looks complex because of the option
          types but really not that tricky. *)
       match ret_cond with
       | None => None (* Unreachable assuming a well-formed rule *)
       | Some x =>
         merge_failures
           failures_cond
           (merge_failures
             (option_map
               (fun y => UBinop (PrimUntyped.UBits2 PrimUntyped.UAnd) x y)
               failures_tb)
             (option_map
               (fun y =>
                 (UBinop (PrimUntyped.UBits2 PrimUntyped.UAnd)
                   (UUnop (PrimUntyped.UBits1 PrimUntyped.UNot) x) y))
               failures_fb))
        end,
        al_fb, nid_fb <| let_id := let_id_merge |>)
    | UUnop ufn a =>
      let '(ret_a, vm_a, vv_a, failures_a, al_a, nid_a) :=
        get_rule_information_aux a var_map guard al nid
      in
      (Some (UUnop ufn (reduce ret_a)), vm_a, vv_a, failures_a, al_a, nid_a)
    | UBinop ufn a1 a2 =>
      let '(ret_a1, vm_a1, vv_a1, failures_a1, al_a1, nid_a1) :=
        get_rule_information_aux a1 var_map guard al nid
      in
      let '(ret_a2, vm_a2, vv_a2, failures_a2, al_a2, nid_a2) :=
        get_rule_information_aux a2 vm_a1 guard al_a1 nid_a1
      in
      (Some (UBinop ufn (reduce ret_a1) (reduce ret_a2)), vm_a2, vv_a1++vv_a2,
       merge_failures failures_a1 failures_a2, al_a2, nid_a2)
    | UInternalCall ufn args =>
      let '(arg_names, vm_args, vv_args, failure_args, al_args, nid_args) := (
          fold_left
            (fun '(names, vm_p, vv_p, failures_p, al_p, nid_p) a =>
              let '(val_c, vm_c, vv_c, failure_c, al_c, nid_c) :=
                get_rule_information_aux a vm_p guard al_p nid_p
              in
              let arg_bind_name :=
                generate_binding_name letb (S (let_id nid_c))
              in (
                arg_bind_name::names, vm_c,
                vv_p++vv_c++[(arg_bind_name, reduce val_c)],
                merge_failures failure_c failures_p, al_c,
                nid_c <| let_id := S (let_id nid_c) |>))
            args
            ([], var_map, [], None, al, nid)
        ) in
      let vm_tmp :=
        combine
          (fst (split (int_argspec ufn))) (* Names from argspec *)
          (* We know that a value is assigned to each argument in well formed
             rules *)
          arg_names
      in
      let '(ret_ic, _, vv_ic, failure_ic, al_ic, nid_ic) :=
        get_rule_information_aux
          (int_body ufn) vm_tmp guard al_args nid_args
      in
      (* We can forget vm_tmp which contained the temporary map for use in the
         called function. *)
      (ret_ic, vm_args, vv_args++vv_ic, merge_failures failure_ic failure_args,
       al_ic, nid_ic)
    | UAPos _ e => get_rule_information_aux e var_map guard al nid
    | URead port reg =>
      let action_guard := generate_binding_name ctxb (S (ctx_id nid)) in
      let '(modified_al, failure_read) :=
        match port with
        | P0 => add_read0 al action_guard reg
        | P1 => add_read1 al action_guard reg
        end
      in (
        Some ua, var_map, [(action_guard, guard)], failure_read, modified_al,
        nid <| ctx_id := S (ctx_id nid) |>)
    | UWrite port reg val =>
      let '(ret_val, vm_val, vv_val, failures_val, actions_val, nid_val) :=
        get_rule_information_aux val var_map guard al nid
      in
      let action_guard := generate_binding_name ctxb (S (ctx_id nid_val)) in
      let '(al_wr, failure_wr) :=
        match port with
        | P0 => add_write0 actions_val action_guard reg (reduce ret_val)
        | P1 => add_write1 actions_val action_guard reg (reduce ret_val)
        end
      in
      (None, vm_val, vv_val++[(action_guard, guard)],
       merge_failures failures_val failure_wr, al_wr,
       nid_val <| ctx_id := S (ctx_id nid_val) |>)
    | UExternalCall ufn arg =>
      let '(ret_arg, vm_arg, vv_arg, failures_arg, actions_arg, nid_arg) :=
        get_rule_information_aux arg var_map guard al nid
      in
      let fresh_name := generate_binding_name extcb (S (extc_id nid_arg)) in
      let action_guard := generate_binding_name ctxb (S (ctx_id nid)) in
      let new_al := add_extcall al action_guard ufn arg fresh_name in
      (Some (UVar fresh_name), vm_arg, vv_arg, failures_arg, new_al,
       nid_arg <| ctx_id := S (ctx_id nid_arg) |>
         <| extc_id := S (extc_id nid_arg) |>)
    | UError _ =>
      (None, var_map, [], Some (UConst (tau := bits_t 1) (Bits.of_nat 1 1)), al,
       nid)
    | UFail _ =>
      (None, var_map, [], Some (UConst (tau := bits_t 1) (Bits.of_nat 1 1)), al,
       nid)
    | _ => (Some ua, var_map, [], None, al, nid) (* UConst *)
    end.

  Definition get_rule_information (ua: uact) (nid: next_ids)
  : rule_information * next_ids :=
    let '(_, _, vvm, failure, action_logs, nid') :=
      get_rule_information_aux
        ua [] (UConst (tau := bits_t 1) (Bits.of_nat 1 1))
        {| read0s := []; read1s := []; write0s := []; write1s := [];
           extcalls := []; |}
        nid
    in ({|
      rl_actions := action_logs; rl_vars := vvm; rl_failure_cond := failure
    |}, nid').

  (* D. Scheduling conflicts detection *)
  (* It is here that we take into account how a rule might cancel any later
     rule. *)
  (* D.1. Conflicts between two rules *)
  (* rl_failure_cond al is used in detect_conflicts only so as to keep things
     nicely factored. *)
  Definition detect_conflicts_step
    (acc: option uact) (al: action_logs) (cond: uact) (reg: reg_t)
    (reg_failure_detection: action_logs -> uact -> reg_t -> option uact)
  : option uact :=
    match reg_failure_detection al cond reg with
    | None => acc
    | Some x =>
      match acc with
      | None => Some x
      | Some y => Some (UBinop (PrimUntyped.UBits2 PrimUntyped.UAnd) x y)
      end
    end.

  (* The following functions are meant to be passed as arguments to
     detect_conflicts_step. *)
  Definition detect_conflicts_read0s_reg
    (al: action_logs) (cond: uact) (reg: reg_t)
  : option uact :=
    let prev_wr0 := extract_wr_cond (write0s al) reg in
    let prev_wr1 := extract_wr_cond (write1s al) reg in
    merge_failures_list cond (list_options_to_list [prev_wr0; prev_wr1]).
  Definition detect_conflicts_write0s_reg
    (al: action_logs) (cond: uact) (reg: reg_t)
  : option uact :=
    let prev_wr0 := extract_wr_cond (write0s al) reg in
    let prev_rd1 := list_assoc (read1s al) reg in
    let prev_wr1 := extract_wr_cond (write1s al) reg in
    merge_failures_list
      cond (list_options_to_list [prev_wr0; prev_wr1; prev_rd1]).
  Definition detect_conflicts_read1s_reg
    (al: action_logs) (cond: uact) (reg: reg_t)
  : option uact :=
    let prev_wr1 := extract_wr_cond (write1s al) reg in
    merge_failures_list cond (list_options_to_list [prev_wr1]).
  Definition detect_conflicts_write1s_reg
    (al: action_logs) (cond: uact) (reg: reg_t)
  : option uact :=
    let prev_wr1 := extract_wr_cond (write1s al) reg in
    merge_failures_list cond (list_options_to_list [prev_wr1]).

  (* These functions take the action_logs of a rule as well as a subset of the
     logs of a subsequent rule and return a condition that is true in all the
     situations in which the second rule has to fail for e.g. read0s conflicts
     reasons. *)
  Definition detect_conflicts_read0s (al: action_logs) (rl: read_log)
  : option uact :=
    fold_left
      (fun acc '(reg, cond) =>
        detect_conflicts_step acc al cond reg detect_conflicts_read0s_reg)
      rl None.
  Definition detect_conflicts_write0s (al: action_logs) (wl: write_log)
  : option uact :=
    fold_left
      (fun acc '(reg, l) =>
        match extract_wr_cond wl reg with
        | None => None (* Illegal *)
        | Some c =>
          detect_conflicts_step acc al c reg detect_conflicts_write0s_reg
        end)
      wl None.
  Definition detect_conflicts_read1s (al: action_logs) (rl: read_log)
  : option uact :=
    fold_left
      (fun acc '(reg, cond) =>
        detect_conflicts_step acc al cond reg detect_conflicts_read1s_reg)
      rl None.
  Definition detect_conflicts_write1s (al: action_logs) (wl: write_log)
  : option uact :=
    fold_left
      (fun acc '(reg, l) =>
        match extract_wr_cond wl reg with
        | None => None (* Illegal *)
        | Some c =>
          detect_conflicts_step acc al c reg detect_conflicts_write1s_reg
        end)
      wl None.

  (* The order of the arguments matters! If there is a conflict between a1 and
     a2, a1 takes precedence. This function does not take the fact that rule 1
     might fail and therefore not impact rule 2 into account, as this is done
     from detect_conflicts. *)
  Definition detect_conflicts_actions (a1 a2: action_logs) : option uact :=
    merge_failures
      (merge_failures
        (merge_failures
          (detect_conflicts_read0s a1 (read0s a2))
          (detect_conflicts_write0s a1 (write0s a2)))
        (detect_conflicts_read1s a1 (read1s a2)))
      (detect_conflicts_write1s a1 (write1s a2)).

  (* Returns a failure condition for ri2's conflicts with ri1. Includes ri1's
     initial failure condition. *)
  Definition detect_conflicts (ri1 ri2: rule_information) : option uact :=
    merge_failures
      (rl_failure_cond ri2)
      (match detect_conflicts_actions (rl_actions ri1) (rl_actions ri2) with
       | None => None
       | Some x =>
         match rl_failure_cond ri1 with
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
    fold_left
      (fun r' p =>
        {| rl_actions := rl_actions r'; rl_vars := rl_vars r';
           rl_failure_cond := detect_conflicts p r' |})
      prior_rules r.

  (* D.3. All scheduling conflicts *)
  (* This function detects all the scheduling conflicts. It returns a list of
     rule_information where the failure conditions have been edited
     appropriately. *)
  Definition detect_all_conflicts (rl: list rule_information) (nid: next_ids)
  : list rule_information :=
    fold_left
      (fun acc c =>
        match acc with
        | [] => [c]
        | h::t => app acc [detect_conflicts_any_prior c acc]
        end)
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
    map
      (fun '(reg, cond') =>
        (reg, UBinop (PrimUntyped.UBits2 PrimUntyped.UAnd) cond cond'))
      rl.
  Definition prepend_condition_writes (cond: uact) (wl: write_log)
  : write_log :=
    map
      (fun '(reg, wl') =>
        (reg, map (fun wi => {| wcond := wcond wi; wval := wval wi |}) wl'))
      wl.
  Definition prepend_condition_extcalls (cond: uact) (el: extcall_log)
  : extcall_log :=
    map
      (fun '(ufn, ei) =>
        (ufn, {|
          econd := UBinop (PrimUntyped.UBits2 PrimUntyped.UAnd) cond (econd ei);
          ebind := ebind ei; earg := earg ei |}))
      el.

  Definition prepend_failure_actions (al: action_logs) (fail_var_name: string)
  : action_logs :=
    let cond := (UVar fail_var_name) in {|
      read0s := prepend_condition_reads cond (read0s al);
      write0s := prepend_condition_writes cond (write0s al);
      read1s := prepend_condition_reads cond (read1s al);
      write1s := prepend_condition_writes cond (write1s al);
      extcalls := prepend_condition_extcalls cond (extcalls al);
    |}.

  Definition to_negated_cond (cond: option uact) : uact :=
    match cond with
    | Some x => UUnop (PrimUntyped.UBits1 PrimUntyped.UNot) x
    | None => UConst (tau := bits_t 1) (Bits.of_nat 1 1)
    end.

  Definition integrate_failures (ri: list rule_information) (nid: next_ids)
  : list rule_information * next_ids :=
    fold_left
      (fun '(acc, nid') r =>
        let fail_var_name :=
          generate_binding_name fcond_ncb (S (fcond_nc_id nid))
        in
        let not_failure_cond := to_negated_cond (rl_failure_cond r) in
        ({| rl_actions := prepend_failure_actions (rl_actions r) fail_var_name;
            rl_vars := (rl_vars r)++[(fail_var_name, not_failure_cond)];
            (* TODO perhaps return not_failure_cond separately and regroup all
               such variables at the end of the list so as to preserve order *)
            rl_failure_cond := None
         |}::acc, nid <| fcond_nc_id := S (fcond_nc_id nid') |>))
      ri
      ([], nid).

  (* E.2. Merge duplicated actions across rules *)
  (* E.2.a. Merge one rule *)
  (* Used for both write0 and write1. *)
  Definition merge_next_write (reg: reg_t) (wl: write_log) (w: list write_info)
  : write_log :=
    let prev := list_assoc wl reg in
    match prev with
    | None => list_assoc_set wl reg w
    | Some wil => list_assoc_set wl reg (wil ++ w)
    end.

  Definition merge_writes_single_rule (wl_acc wl_curr: write_log)
  : write_log :=
    fold_left (fun acc '(reg, x) => merge_next_write reg acc x) wl_curr wl_acc.

  Definition merge_single_rule (s: schedule_information) (r: rule_information)
  : schedule_information :=
    let rule_logs := rl_actions r in
    let rule_exprs := rl_vars r in
    (* failure_cond can be ignored as it already was integrated *)
    let acc_log := sc_actions s in
    let acc_exprs := sc_vars s in
    let write0s' :=
      merge_writes_single_rule (write0s acc_log) (write0s rule_logs)
    in
    let write1s' :=
      merge_writes_single_rule (write1s acc_log) (write1s rule_logs)
    in
    let extcalls' := app (extcalls acc_log) (extcalls rule_logs) in
    {|
      sc_actions := {|
        read0s := []; write0s := write0s'; read1s := [];
        write1s := write1s'; extcalls := extcalls'
      |};
      sc_vars := List.concat [rule_exprs; acc_exprs]
    |}.

  (* E.2.b. Merge full schedule *)
  Definition merge_schedule
    (rules_info: list rule_information) (nid: next_ids)
  (* next_ids isn't used past this point and therefore isn't returned *)
  : schedule_information :=
    let '(rules_info', le') := integrate_failures rules_info nid in
    (* TODO really necessary? Wouldn't a direct fold left suffice? *)
    match hd_error rules_info' with
    | None => {|
        sc_actions := {|
          read0s := []; write0s := []; read1s := []; write1s := [];
          extcalls := []
        |};
        sc_vars := []
      |}
    | Some x =>
      fold_left
        merge_single_rule (tl rules_info')
        {| sc_actions := rl_actions x; sc_vars := rl_vars x |}
    end.

  (* F. Final simplifications *)
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
    map
      (fun '(reg, wil) =>
        (reg,
         map (fun wi =>
           {| wcond := replace_var_by_uact_in_uact from to (wcond wi);
              wval := replace_var_by_uact_in_uact from to (wval wi) |})
         wil))
      w.

  Definition replace_var_by_uact_extc (e: extcall_log) (from: string) (to: uact)
  : extcall_log :=
    map
      (fun '(reg, ei) =>
        (reg,
          {| econd := replace_var_by_uact_in_uact from to (econd ei);
             earg := replace_var_by_uact_in_uact from to (earg ei);
             ebind := ebind ei |}))
      e.

  Definition replace_var_by_uact_expr
    (v: var_value_map) (from: string) (to: uact)
  : var_value_map :=
    map (fun '(reg, val) => (reg, replace_var_by_uact_in_uact from to val)) v.

  (* Variables bound to the return values of read1s need to be replaced with the
     appropriate value. TODO store res as expr instead and change name only *)
  Definition replace_var_by_uact
    (s: schedule_information) (from: string) (to: uact)
  : schedule_information :=
    let a := sc_actions s in {|
      sc_actions := {|
        read0s := [];
        write0s := replace_var_by_uact_w (write0s a) from to;
        read1s := [];
        write1s := replace_var_by_uact_w (write1s a) from to;
        extcalls := replace_var_by_uact_extc (extcalls a) from to
      |};
      sc_vars := replace_var_by_uact_expr (sc_vars s) from to
    |}.

  (* F.1.b. Removal *)
  Definition get_value_at_read1
    (s: schedule_information) (rd1_cond: uact) (r: reg_t)
  : uact :=
    let a := sc_actions s in
    let '(read0s', rd0_name) :=
        (list_assoc_set
           (read0s a) r
           (UBinop (PrimUntyped.UBits2 PrimUntyped.UOr) rd1_cond rd0_cond,
            rd0_name),
         rd0_name, last_action_id)
    in (
      match list_assoc (write0s a) r with
      | None => UVar rd0_name
      | Some (wr0_cond, wr0_val) => UIf wr0_cond wr0_val (UVar rd0_name)
      end,
      {| sc_actions := upd_read0 a read0s'; sc_vars := sc_vars s |}
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
      fold_left
        (fun '(s', la') rd =>
          remove_single_read1 s' la' rd)
        (read1s (sc_actions s)) (s, last_action_id)
    in
    {| sc_actions := upd_read1 (sc_actions s'') []; sc_vars := sc_vars s'' |}.

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
               UIf wr1_cond wr1_val val));
        sc_vars := sc_vars s
      |}
    end.

  Definition remove_write0s (s: schedule_information) : schedule_information :=
    let s' := fold_left remove_single_write0 (write0s (sc_actions s)) s in
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
  (* Precondition: rules desugared. TODO desugar from here. *)
  Definition schedule_to_normal_form (s: schedule) : normal_form :=
    (* Get list of uact from scheduler *)
    let rules_l := schedule_to_list_of_rules s in
    (* Get rule_information from each rule *)
    let '(rule_info_l, nid') :=
      fold_left
        (fun '(ri_acc, nid') r =>
          let '(ri, nid'') := get_rule_information r nid' in
          (* Not a fold right since we want the first rule to have the lowest
             indices. *)
          (ri_acc++[ri], nid'')
        )
        rules_l
        ([], initial_ids)
    in
    (* Detect inter-rules conflicts *)
    let rule_info_with_conflicts_l := detect_all_conflicts rule_info_l in
    (* To schedule info, merge cancel conditions with actions conditions *)
    let schedule_info := merge_schedule rule_info_with_conflicts_l nid' in
    (* Remove read1s and write0s *)
    let schedule_info_simpl :=
      remove_write0s (remove_read1s schedule_info nid')
    in
    (* To normal form *)
    {| reads :=
        map
          (fun '(reg, (_, name)) => (reg, name))
          (read0s (sc_actions schedule_info_simpl));
       writes := write1s (sc_actions schedule_info_simpl);
       variables := sc_vars schedule_info_simpl;
       external_calls := extcalls (sc_actions schedule_info_simpl)
    |}.
End Normalize.

(* TODO try to pick more helpful names for expressions and actions *)
Close Scope nat.
