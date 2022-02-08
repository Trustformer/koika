(*! Proving | Transformation of a schedule into a proof-friendly form !*)
Require Import Coq.Numbers.DecimalString Coq.Program.Equality Coq.Strings.Ascii.
Require Import Koika.BitsToLists Koika.Primitives Koika.Syntax.
From RecordUpdate Require Import RecordSet.
Import RecordSetNotations.

(* When reasoning about a Koîka schedule, a lot of tedious implicit mechanisms
   have to be considered explicitly (rules merging, cancellation, ...).
   Furthermore, performance issues related to abstract interpretation make
   reasoning about the behavior of some even moderately complex models (e.g.,
   the RISC-V processor example) impossible.

   This is what this simpler form aims to fix. For instance, it makes finding
   under which conditions the value of a register is updated or proving that the
   value of register x never reaches 5 much easier (even trivial in certain
   cases).

   It goes without saying that the result of the interpretation of a model
   before or after its conversion to the form defined hereafter should be equal
   (in terms of the effects of a cycle on the final state of the registers and
   of the emitted extcalls, although the latter are not really considered in
   Koîka's pure semantics). *)

Open Scope nat.
Section SimpleForm.
  Context {pos_t reg_t ext_fn_t rule_name_t: Type}.
  Context {reg_t_eq_dec: EqDec reg_t}.
  Context {ext_fn_t_eq_dec: EqDec ext_fn_t}.
  Definition uact := uaction pos_t string string reg_t ext_fn_t.
  Definition schedule := scheduler pos_t rule_name_t.

  Definition const_nil :=
    @UConst pos_t string string reg_t ext_fn_t (bits_t 0) (Bits.of_nat 0 0).
  Definition const_true :=
    @UConst pos_t string string reg_t ext_fn_t (bits_t 1) (Bits.of_nat 1 1).

  (* A. Simple form and related structures *)
  Definition cond_log := list (reg_t * uact).
  Record write_info := mkWriteInfo { wcond: uact; wval: uact }.
  Definition write_log := list (reg_t * list (write_info)).
  Definition write_log_raw := list (reg_t * (uact * list (write_info))).
  Record extcall_info := mkExtcallInfo
    { econd: uact; earg: uact; ebind: string }.
  Instance etaExtcallInfo : Settable _ :=
    settable! mkExtcallInfo < econd; earg; ebind >.
  Definition extcall_log := list (ext_fn_t * extcall_info).
  Definition var_value_map := list (string * uact).

  Record rule_information_raw := mkRuleInformationRaw {
    rir_read0s: cond_log;
    rir_read1s: cond_log;
    rir_write0s: write_log_raw;
    rir_write1s: write_log_raw;
    rir_extcalls: extcall_log;
    rir_vars: var_value_map;
    rir_failure_cond: option uact }.
  Instance etaRuleInformationRaw : Settable _ :=
    settable! mkRuleInformationRaw <
      rir_read0s; rir_read1s; rir_write0s; rir_write1s; rir_extcalls; rir_vars;
      rir_failure_cond >.
  Record rule_information_clean := mkRuleInformationClean {
    ric_write0s: write_log;
    ric_write1s: write_log;
    ric_extcalls: extcall_log;
    ric_vars: var_value_map;
    ric_failure_cond: option uact }.
  Instance etaRuleInformationClean : Settable _ :=
    settable! mkRuleInformationClean
      < ric_write0s; ric_write1s; ric_extcalls; ric_vars; ric_failure_cond >.
  Record schedule_information := mkScheduleInformation {
    sc_write0s: cond_log;
    sc_write1s: cond_log;
    sc_extcalls: extcall_log;
    sc_vars: var_value_map }.
  Instance etaScheduleInformation : Settable _ :=
    settable! mkScheduleInformation
      < sc_write0s; sc_write1s; sc_extcalls; sc_vars >.
  Record simple_form := mkSimpleForm {
    final_values: list (reg_t * string);
    vars: var_value_map;
    external_calls: extcall_log }.
  Instance etaSimpleForm : Settable _ :=
    settable! mkSimpleForm < final_values; vars; external_calls >.

  (* B. Bindings names *)
  (* TODO name collisions with previously standing variables can't possibly
       happen anymore (we treat everything in order). This makes it easier to
       give informative names to our variables. *)
  Inductive binding_type :=
  | ctxb | letb | extcb | wcondb | fcond_ncb | fcond_cb | ivalb | fvalb.
  Record next_ids := mkNextIds { ctx_id: nat; let_id: nat; extc_id: nat }.
  Instance etaNextIds : Settable _ :=
    settable! mkNextIds < ctx_id; let_id; extc_id >.

  Definition initial_ids : next_ids :=
    {| ctx_id := 0; let_id := 0; extc_id := 0 |}.

  Definition get_prefix (b: binding_type) : string :=
    match b with
    | ctxb => "ctx_" | letb => "let_" | extcb => "extc_" | wcondb => "wcond_"
    | fcond_ncb => "fcond_nc_" | fcond_cb => "fcond_c_" | ivalb => "ival_"
    | fvalb => "fval_"
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
        | None => const_nil (* Unreachable *)
        end)
      (filter (fun i => match i with None => false | Some _ => true end) l).

  Definition merge_conds (wl: option (list write_info)) : option uact :=
    match wl with
    | None => None
    | Some l => or_conds (map wcond l)
    end.

  Definition merge_failures_list (action_cond: uact) (conds: list uact) :=
    match or_conds conds with
    | None => None
    | Some x =>
      Some (UBinop (PrimUntyped.UBits2 PrimUntyped.UAnd) action_cond x)
    end.

  Definition add_read0 (rir: rule_information_raw) (grd: uact) (reg: reg_t)
  (* Returns modified rir, failure conditions *)
  : rule_information_raw * option uact := (
      match list_assoc (rir_read0s rir) reg with
      | None =>
        rir <| rir_read0s := list_assoc_set (rir_read0s rir) reg grd |>
      | Some cond' =>
        rir <| rir_read0s :=
          list_assoc_set (rir_read0s rir) reg
            (UBinop (PrimUntyped.UBits2 PrimUntyped.UOr) cond' grd) |>
      end,
      merge_failures_list grd (
        list_options_to_list
          [option_map fst (list_assoc (rir_write0s rir) reg);
           option_map fst (list_assoc (rir_write1s rir) reg)])).

  Definition add_read1 (rir: rule_information_raw) (grd: uact) (reg: reg_t)
  (* Returns modified rule_information_raw, failure conditions *)
  : rule_information_raw * option uact := (
    match list_assoc (rir_read1s rir) reg with
    | None =>
      rir <| rir_read1s := list_assoc_set (rir_read1s rir) reg grd |>
    | Some cond' =>
      rir <| rir_read1s :=
        list_assoc_set (rir_read1s rir) reg
          (UBinop (PrimUntyped.UBits2 PrimUntyped.UOr) cond' grd) |>
    end,
    merge_failures_list grd
      (list_options_to_list [option_map fst (list_assoc (rir_write1s rir) reg)])
  ).

   Definition add_write0
    (rir: rule_information_raw) (grd: uact) (reg: reg_t) (val: uact)
  (* Returns modified rule_information_raw, failure conditions *)
  : rule_information_raw * option uact := (
    match list_assoc (rir_write0s rir) reg with
    | None =>
      rir <| rir_write0s :=
        list_assoc_set (rir_write0s rir) reg
          (grd, [{| wcond := grd; wval := val |}]) |>
    | Some c =>
      rir <| rir_write0s :=
        list_assoc_set (rir_write0s rir) reg
          (UBinop (PrimUntyped.UBits2 PrimUntyped.UOr) (fst c) grd,
           (snd c)++[{| wcond := grd; wval := val |}]) |>
    end,
    merge_failures_list
      grd
      (list_options_to_list ([
        option_map fst (list_assoc (rir_write0s rir) reg);
        list_assoc (rir_read1s rir) reg;
        option_map fst (list_assoc (rir_write1s rir) reg)]))).

  Definition add_write1
    (rir: rule_information_raw) (grd: uact) (reg: reg_t) (val: uact)
  (* Returns modified rule_information_raw, failure conditions *)
  : rule_information_raw * option uact := (
    match list_assoc (rir_write1s rir) reg with
    | None =>
      rir <| rir_write1s :=
        list_assoc_set (rir_write1s rir) reg
          (grd, [{| wcond := grd; wval := val |}]) |>
    | Some c =>
      rir <| rir_write1s :=
        list_assoc_set (rir_write1s rir) reg
          (UBinop (PrimUntyped.UBits2 PrimUntyped.UOr) (fst c) grd,
           ((snd c)++[{| wcond := grd; wval := val |}])) |>
    end,
    merge_failures_list grd (list_options_to_list [
      option_map fst (list_assoc (rir_write1s rir) reg)])).

  Definition add_extcall
    (rir: rule_information_raw) (grd: uact) (ufn: ext_fn_t) (arg: uact)
    (name: string)
  : rule_information_raw :=
    rir <| rir_extcalls :=
      (ufn, {| econd := grd; earg := arg; ebind := name |})::(rir_extcalls rir)
    |>.

  (* C.2. Extraction of actions from rule *)
  Definition reduce (ua: option uact) : uact :=
    match ua with
    | None => const_nil
    | Some x => x
    end.

  (* This function extracts the actions for a given rule. It also returns the
     updated next_ids structure. *)
  Fixpoint get_rule_information_aux
    (* No need to pass failures as these impact the whole rule - taking note of
       all of them and factoring the conditions in is enough. Conflicts between
       different actions are also dealt with here - see C.1. *)
    (* TODO improve guards management *)
    (* TODO guard could be option string instead *)
    (ua: uact) (env: list (string * string)) (guard: uact)
    (rir: rule_information_raw) (nid: next_ids)
    (* Returns value, env, var_values, failure condition, rule_information_raw,
       next_ids *)
  : option uact * list (string * string) * (list (string * uact))
    * (option uact) * rule_information_raw * next_ids
    (* TODO remove redundancies with rule_information_raw (failure_cond,
         var_values) *)
  :=
    match ua with
    | UBind var val body =>
      let '(ret_val, vm_val, vv_val, failures_val, rir_val, nid_val) :=
        get_rule_information_aux val env guard rir nid
      in
      let name := generate_binding_name letb (S (let_id nid_val)) in
      let '(ret_body, vm_body, vv_body, failures_body, rir_body, nid_body) :=
        get_rule_information_aux
          body ((var, name)::env) guard rir_val
          (nid_val <| let_id := S (let_id nid_val) |>)
      in (
        ret_body, skipn 1 vm_body (* var's binding goes out of scope *),
        vv_val++[(name, reduce ret_val)]++vv_body,
        merge_failures failures_val failures_body, rir_body, nid_body)
    | UAssign var val =>
      let '(ret_val, vm_val, vv_val, failures_val, rir_val, nid_val) :=
        get_rule_information_aux val env guard rir nid
      in
      let name := generate_binding_name letb (S (let_id nid_val)) in
      (None, list_assoc_set vm_val var name, vv_val++[(name, reduce ret_val)],
       failures_val, rir_val, nid_val <| let_id := S (let_id nid_val) |>
      )
    | UVar var =>
      match list_assoc env var with
      | Some x => (Some (UVar x), env, [], None, rir, nid)
      | None => (* Unreachable assuming rule valid *)
        (Some (UVar "ERROR"), env, [], None, rir, nid)
      end
    | USeq a1 a2 =>
      let '(_, vm_a1, vv_a1, failures_a1, rir_a1, nid_a1) :=
        get_rule_information_aux a1 env guard rir nid
      in
      let '(ret_a2, vm_a2, vv_a2, failures_a2, rir_a2, nid_a2) :=
        get_rule_information_aux a2 vm_a1 guard rir_a1 nid_a1
      in
      (ret_a2, vm_a2, vv_a1++vv_a2, merge_failures failures_a1 failures_a2,
       rir_a2, nid_a2)
    | UIf cond tb fb =>
      let '(ret_cond, vm_cond, vv_cond, failures_cond, rir_cond, nid_cond) :=
        get_rule_information_aux cond env guard rir nid
      in
      let cond_name := generate_binding_name ctxb (ctx_id nid_cond + 1) in
      let guard_tb_name := generate_binding_name ctxb (ctx_id nid_cond + 2) in
      let guard_fb_name := generate_binding_name ctxb (ctx_id nid_cond + 3) in
      let guard_tb :=
        UBinop (PrimUntyped.UBits2 PrimUntyped.UAnd) guard (UVar cond_name)
      in
      let guard_fb :=
        UBinop (PrimUntyped.UBits2 PrimUntyped.UAnd)
          guard (UUnop (PrimUntyped.UBits1 PrimUntyped.UNot) (UVar cond_name))
      in
      let '(ret_tb, vm_tb, vv_tb, failures_tb, rir_tb, nid_tb) :=
        get_rule_information_aux tb vm_cond (UVar guard_tb_name) rir_cond
        (nid_cond <| ctx_id := (ctx_id nid_cond + 3) |>)
      in
      let '(ret_fb, vm_fb, vv_fb, failures_fb, rir_fb, nid_fb) :=
        (* We use rir_tb here even though we know that none of the actions added
           by the other branch can impact those from this branch (they are
           mutually exclusive). This way, we don't have to deal with
           rule_information_raw merging. However, this also means that the
           failure condition will contain some redundancy. *)
        get_rule_information_aux fb vm_cond (UVar guard_fb_name) rir_tb nid_tb
      in
      (* Merge var maps: if vm_tb and vm_fb disagree for some variable, generate
         a new variable reflecting the condition and update the variables map.
       *)
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
       vv_cond++[
         (cond_name, reduce ret_cond); (guard_tb_name, guard_tb);
         (guard_fb_name, guard_fb)
       ]++vv_tb++vv_fb++vv_merge,
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
        rir_fb, nid_fb <| let_id := let_id_merge |>)
    | UUnop ufn a =>
      let '(ret_a, vm_a, vv_a, failures_a, rir_a, nid_a) :=
        get_rule_information_aux a env guard rir nid
      in
      (Some (UUnop ufn (reduce ret_a)), vm_a, vv_a, failures_a, rir_a, nid_a)
    | UBinop ufn a1 a2 =>
      let '(ret_a1, vm_a1, vv_a1, failures_a1, rir_a1, nid_a1) :=
        get_rule_information_aux a1 env guard rir nid
      in
      let '(ret_a2, vm_a2, vv_a2, failures_a2, rir_a2, nid_a2) :=
        get_rule_information_aux a2 vm_a1 guard rir_a1 nid_a1
      in
      (Some (UBinop ufn (reduce ret_a1) (reduce ret_a2)), vm_a2, vv_a1++vv_a2,
       merge_failures failures_a1 failures_a2, rir_a2, nid_a2)
    | UInternalCall ufn args =>
      let '(arg_names, vm_args, vv_args, failure_args, rir_args, nid_args) := (
        fold_left
          (fun '(names, vm_p, vv_p, failures_p, rir_p, nid_p) a =>
            let '(val_c, vm_c, vv_c, failure_c, rir_c, nid_c) :=
              get_rule_information_aux a vm_p guard rir_p nid_p
            in
            let arg_bind_name :=
              generate_binding_name letb (S (let_id nid_c))
            in (
              arg_bind_name::names, vm_c,
              vv_p++vv_c++[(arg_bind_name, reduce val_c)],
              merge_failures failure_c failures_p, rir_c,
              nid_c <| let_id := S (let_id nid_c) |>))
          args
          ([], env, [], None, rir, nid)
      ) in
      let vm_tmp :=
        combine
          (fst (split (int_argspec ufn))) (* Names from argspec *)
          (* We know that a value is assigned to each argument in well formed
             rules *)
          arg_names
      in
      let '(ret_ic, _, vv_ic, failure_ic, rir_ic, nid_ic) :=
        get_rule_information_aux (int_body ufn) vm_tmp guard rir_args nid_args
      in
      (* We can forget vm_tmp which contained the temporary map for use in the
         called function. *)
      (ret_ic, vm_args, vv_args++vv_ic, merge_failures failure_ic failure_args,
       rir_ic, nid_ic)
    | UAPos _ e => get_rule_information_aux e env guard rir nid
    | URead port reg =>
      let '(modified_rir, failure_read) :=
        match port with
        | P0 => add_read0 rir guard reg
        | P1 => add_read1 rir guard reg
        end
      in (Some ua, env, [], failure_read, modified_rir, nid)
    | UWrite port reg val =>
      let '(ret_val, vm_val, vv_val, failures_val, actions_val, nid_val) :=
        get_rule_information_aux val env guard rir nid
      in
      let '(rir_wr, failure_wr) :=
        match port with
        | P0 => add_write0 actions_val guard reg (reduce ret_val)
        | P1 => add_write1 actions_val guard reg (reduce ret_val)
        end
      in
      (None, vm_val, vv_val, merge_failures failures_val failure_wr, rir_wr,
       nid_val)
    | UExternalCall ufn arg =>
      let '(ret_arg, vm_arg, vv_arg, failures_arg, actions_arg, nid_arg) :=
        get_rule_information_aux arg env guard rir nid
      in
      let name := generate_binding_name extcb (S (extc_id nid_arg)) in
      let new_rir := add_extcall rir guard ufn arg name in
      (Some (UVar name), vm_arg, vv_arg, failures_arg, new_rir,
       nid_arg <| extc_id := S (extc_id nid_arg) |>)
    | UError _ => (None, env, [], Some (const_true), rir, nid)
    | UFail _ => (None, env, [], Some (const_true), rir, nid)
    | _ => (Some ua, env, [], None, rir, nid) (* UConst *)
    end.

  Definition get_rule_information (ua: uact) (nid: next_ids)
  : rule_information_raw * next_ids :=
    let '(_, _, vvm, failure, rule_information_raw, nid') :=
      get_rule_information_aux
        ua [] const_true
        {| rir_read0s := []; rir_read1s := []; rir_write0s := [];
           rir_write1s := []; rir_extcalls := []; rir_vars := [];
           rir_failure_cond := None |}
        nid
    in (
      rule_information_raw <| rir_failure_cond := failure |>
        <| rir_vars := vvm|>,
      nid').

  (* D. Scheduling conflicts detection *)
  (* It is here that we take into account how a rule might cancel any later
     rule. *)
  (* D.1. Conflicts between two rules *)
  (* rl_failure_cond rir is used in detect_conflicts only so as to keep things
     nicely factored. *)
  Definition detect_conflicts_step
    (acc: option uact) (rir: rule_information_raw) (cond: uact) (reg: reg_t)
    (reg_failure_detection:
      rule_information_raw -> uact -> reg_t -> option uact)
  : option uact :=
    match reg_failure_detection rir cond reg with
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
    (rir: rule_information_raw) (cond: uact) (reg: reg_t)
  : option uact :=
    let prev_wr0 := option_map fst (list_assoc (rir_write0s rir) reg) in
    let prev_wr1 := option_map fst (list_assoc (rir_write1s rir) reg) in
    merge_failures_list cond (list_options_to_list [prev_wr0; prev_wr1]).
  Definition detect_conflicts_write0s_reg
    (rir: rule_information_raw) (cond: uact) (reg: reg_t)
  : option uact :=
    let prev_wr0 := option_map fst (list_assoc (rir_write0s rir) reg) in
    let prev_rd1 := list_assoc (rir_read1s rir) reg in
    let prev_wr1 := option_map fst (list_assoc (rir_write1s rir) reg) in
    merge_failures_list
      cond (list_options_to_list [prev_wr0; prev_wr1; prev_rd1]).
  Definition detect_conflicts_read1s_reg
    (rir: rule_information_raw) (cond: uact) (reg: reg_t)
  : option uact :=
    let prev_wr1 := option_map fst (list_assoc (rir_write1s rir) reg) in
    merge_failures_list cond (list_options_to_list [prev_wr1]).
  Definition detect_conflicts_write1s_reg
    (rir: rule_information_raw) (cond: uact) (reg: reg_t)
  : option uact :=
    let prev_wr1 := option_map fst (list_assoc (rir_write1s rir) reg) in
    merge_failures_list cond (list_options_to_list [prev_wr1]).

  (* These functions take a rule's rule_information_raw as well as a subset of
     the logs of a subsequent rule and return a condition that is true in all
     the situations in which the second rule has to fail for e.g. read0s
     conflicts reasons. *)
  Definition detect_conflicts_read0s (rir: rule_information_raw) (rl: cond_log)
  : option uact :=
    fold_left
      (fun acc '(reg, cond) =>
        detect_conflicts_step acc rir cond reg detect_conflicts_read0s_reg)
      rl None.
  Definition detect_conflicts_write0s
    (rir: rule_information_raw) (wl: write_log_raw)
  : option uact :=
    fold_left
      (fun acc '(reg, w) =>
        detect_conflicts_step acc rir (fst w) reg detect_conflicts_write0s_reg)
      wl None.
  Definition detect_conflicts_read1s (rir: rule_information_raw) (rl: cond_log)
  : option uact :=
    fold_left
      (fun acc '(reg, cond) =>
        detect_conflicts_step acc rir cond reg detect_conflicts_read1s_reg)
      rl None.
  Definition detect_conflicts_write1s
    (rir: rule_information_raw) (wl: write_log_raw)
  : option uact :=
    fold_left
      (fun acc '(reg, w) =>
        detect_conflicts_step acc rir (fst w) reg detect_conflicts_write1s_reg)
      wl None.

  (* The order of the arguments matters! If there is a conflict between a1 and
     a2, a1 takes precedence. This function does not take the fact that rule 1
     might fail and therefore not impact rule 2 into account, as this is done
     from detect_conflicts. *)
  Definition detect_conflicts_actions (a1 a2: rule_information_raw)
  : option uact :=
    merge_failures
      (merge_failures
        (merge_failures
          (detect_conflicts_read0s a1 (rir_read0s a2))
          (detect_conflicts_write0s a1 (rir_write0s a2)))
        (detect_conflicts_read1s a1 (rir_read1s a2)))
      (detect_conflicts_write1s a1 (rir_write1s a2)).

  (* Returns a failure condition for ri2's conflicts with ri1. Includes ri1's
     initial failure condition. *)
  Definition detect_conflicts (ri1 ri2: rule_information_raw) : option uact :=
    merge_failures
      (rir_failure_cond ri2)
      (match detect_conflicts_actions ri1 ri2 with
       | None => None
       | Some x =>
         match rir_failure_cond ri1 with
         | None => Some x
         | Some y =>
           let not_failure_1 := UUnop (PrimUntyped.UBits1 PrimUntyped.UNot) y in
           (* If rule 1 fails, then it can't cause rule 2 to fail. *)
           Some (UBinop (PrimUntyped.UBits2 PrimUntyped.UAnd) not_failure_1 x)
         end
       end).

  (* D.2. Conflicts with any prior rule *)
  Definition detect_conflicts_any_prior
    (r: rule_information_raw) (prior_rules: list rule_information_raw)
  : rule_information_raw :=
    fold_left
      (fun r' p => r' <| rir_failure_cond := detect_conflicts p r' |>)
      prior_rules r.

  (* D.3. All scheduling conflicts *)
  (* This function detects all the scheduling conflicts. It returns a list of
     rule_information where the failure conditions have been edited
     appropriately. *)
  Definition detect_all_conflicts (rl: list rule_information_raw)
  : list rule_information_clean :=
    let raw := fold_left
      (fun acc c =>
        match acc with
        | [] => [c]
        | h::t => app acc [detect_conflicts_any_prior c acc]
        end)
      rl []
    in
    map (fun r => {|
      ric_write0s := map (fun '(a, (_, b)) => (a, b)) (rir_write0s r);
      ric_write1s := map (fun '(a, (_, b)) => (a, b)) (rir_write1s r);
      ric_extcalls := rir_extcalls r;
      ric_vars := rir_vars r;
      ric_failure_cond := rir_failure_cond r
   |}) raw.

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

  Definition prepend_failure_actions
    (ric: rule_information_clean) (fail_var_name: string)
  : rule_information_clean :=
    let cond := (UVar fail_var_name) in
    ric
      <|ric_write0s := prepend_condition_writes cond (ric_write0s ric)|>
      <|ric_write1s := prepend_condition_writes cond (ric_write1s ric)|>
      <|ric_extcalls := prepend_condition_extcalls cond (ric_extcalls ric)|>.

  Definition to_negated_cond (cond: option uact) : uact :=
    match cond with
    | Some x => UUnop (PrimUntyped.UBits1 PrimUntyped.UNot) x
    | None => const_true
    end.

  Definition integrate_failures (ri: list rule_information_clean)
  : list rule_information_clean :=
    let (res, _) :=
      fold_left
        (fun '(acc, id') r =>
          let fail_var_name := generate_binding_name fcond_ncb id' in
          let not_failure_cond := to_negated_cond (ric_failure_cond r) in (
            ((prepend_failure_actions r fail_var_name)
              (* TODO perhaps return not_failure_cond separately and regroup all
                 such variables at the end of the list so as to preserve order
                *)
              <|ric_vars := (ric_vars r)++[(fail_var_name, not_failure_cond)]|>
              <|ric_failure_cond := None|>
            )::acc, S id'))
        ri
        ([], 0)
    in res.

  (* E.2. Merge duplicated actions across rules *)
  (* E.2.a. Merge one rule *)
  (* Used for both write0 and write1 *)
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

  (* We do not use the schedule record since we still want to use write logs at
     this point *)
  Definition merge_single_rule (racc r: rule_information_clean)
  : rule_information_clean :=
    let write0s' :=
      merge_writes_single_rule (ric_write0s racc) (ric_write0s r)
    in
    let write1s' :=
      merge_writes_single_rule (ric_write1s racc) (ric_write1s r)
    in
    let extcalls' := app (ric_extcalls racc) (ric_extcalls r) in
    {| ric_write0s := write0s'; ric_write1s := write1s';
       ric_extcalls := extcalls';
       ric_vars := List.concat [ric_vars r; ric_vars racc];
       ric_failure_cond := None |}.

  (* E.2.b. Merge full schedule *)
  Fixpoint write_log_to_uact (r: reg_t) (wl: list write_info) (p: Port): uact :=
    match wl with
    | [] => URead p r
    | h::t => UIf (wcond h) (wval h) (write_log_to_uact r t p)
    end.

  Definition merge_schedule (rules_info: list rule_information_clean)
  (* next_ids isn't used past this point and therefore isn't returned *)
  : schedule_information :=
    let rules_info' := integrate_failures rules_info in
    let res := fold_left
      merge_single_rule (tl rules_info')
      {| ric_write0s := []; ric_write1s := []; ric_extcalls := [];
         ric_vars := []; ric_failure_cond := None |}
    in {|
      sc_write0s :=
        map (fun '(r, l) => (r, write_log_to_uact r l P0)) (ric_write0s res);
      sc_write1s :=
        map (fun '(r, l) => (r, write_log_to_uact r l P1)) (ric_write1s res);
      sc_extcalls := ric_extcalls res; sc_vars := ric_vars res |}.

  (* F. Final simplifications *)
  Definition is_member {A: Type} {eq_dec_A: EqDec A} (l: list A) (i: A) :=
    existsb (beq_dec i) l.

  Fixpoint app_uniq (l1 l2: list reg_t) : list reg_t :=
    match l1 with
    | [] => l2
    | h::t => if (is_member l2 h) then app_uniq t l2 else app_uniq t (h::l2)
    end.

  Fixpoint find_all_ua_regs (ua: uact) : list reg_t :=
    match ua with
    | URead _ r => [r]
    | UIf cond tb fb =>
      app_uniq
        (find_all_ua_regs cond)
        (app_uniq (find_all_ua_regs tb) (find_all_ua_regs fb))
    | UBinop ufn a1 a2 => app_uniq (find_all_ua_regs a1) (find_all_ua_regs a2)
    | UUnop ufn a => find_all_ua_regs a
    | _ => []
    end.

  Definition find_all_wr_regs (cl: cond_log) : list reg_t :=
    fold_left
      (fun acc '(r, ua) => app_uniq [r] (app_uniq (find_all_ua_regs ua) acc))
      cl [].

  Definition find_all_extc_regs (el: extcall_log) : list reg_t :=
    fold_left
      (fun acc '(_, ei) =>
        app_uniq
          (find_all_ua_regs (econd ei))
          (app_uniq (find_all_ua_regs (earg ei)) acc))
      el [].

  Definition find_all_bind_regs (vvm: var_value_map) : list reg_t :=
    fold_left (fun acc '(_, ua) => app_uniq (find_all_ua_regs ua) acc) vvm [].

  Definition find_all_used_regs (s: schedule_information) : list reg_t :=
    app_uniq
      (app_uniq
        (find_all_wr_regs (sc_write0s s))
        (find_all_wr_regs (sc_write1s s)))
      (app_uniq
        (find_all_extc_regs (sc_extcalls s))
        (find_all_bind_regs (sc_vars s))).

  (* F.1. Remove read1s *)
  (* F.1.a. Replacement of variables by expression *)
  Fixpoint replace_rd1_with_var_in_uact (from: reg_t) (to ua: uact) :=
    match ua with
    | URead p r =>
      match p with
      | P1 => if beq_dec from r then to else ua
      | _ => ua
      end
    | UIf cond tb fb =>
      UIf
        (replace_rd1_with_var_in_uact from to cond)
        (replace_rd1_with_var_in_uact from to tb)
        (replace_rd1_with_var_in_uact from to fb)
    | UBinop ufn a1 a2 =>
      UBinop
        ufn
        (replace_rd1_with_var_in_uact from to a1)
        (replace_rd1_with_var_in_uact from to a2)
    | UUnop ufn a => UUnop ufn (replace_rd1_with_var_in_uact from to a)
    | _ => ua
    end.

  Definition replace_rd1_with_var_w (w: cond_log) (from: reg_t) (to: uact)
  : cond_log :=
    map (fun '(reg, ua) => (reg, replace_rd1_with_var_in_uact from to ua)) w.

  Definition replace_rd1_with_var_extc (e: extcall_log) (from: reg_t) (to: uact)
  : extcall_log :=
    map
      (fun '(reg, ei) =>
        (reg,
          {| econd := replace_rd1_with_var_in_uact from to (econd ei);
             earg := replace_rd1_with_var_in_uact from to (earg ei);
             ebind := ebind ei |}))
      e.

  Definition replace_rd1_with_var_expr
    (v: var_value_map) (from: reg_t) (to: uact)
  : var_value_map :=
    map (fun '(reg, val) => (reg, replace_rd1_with_var_in_uact from to val)) v.

  (* Variables bound to the return values of read1s need to be replaced with the
     appropriate value. TODO store res as expr instead and change name only *)
  Definition replace_rd1_with_var
    (s: schedule_information) (from: reg_t) (to: uact)
  : schedule_information := {|
      sc_write0s := replace_rd1_with_var_w (sc_write0s s) from to;
      sc_write1s := replace_rd1_with_var_w (sc_write1s s) from to;
      sc_extcalls := replace_rd1_with_var_extc (sc_extcalls s) from to;
      sc_vars := replace_rd1_with_var_expr (sc_vars s) from to |}.

  (* F.1.b. Removal *)
  Definition get_intermediate_value (s: schedule_information) (r: reg_t)
  : uact :=
    match list_assoc (sc_write0s s) r with
    | None => URead P0 r
    | Some v => v (* See write_log_to_uact *)
    end.

  Definition generate_intermediate_values_table
    (s: schedule_information) (regs: list reg_t)
  : ((list (reg_t * string)) * (list (string * uact))) :=
    let (r, _) :=
      fold_left
        (fun '(table, vars, id) r =>
          let name := generate_binding_name ivalb (S id) in
          ((r, name)::table, (name, get_intermediate_value s r)::vars, S id))
        regs ([], [], 0)
    in r.

  Definition remove_read1s
    (s: schedule_information) (active_regs: list reg_t)
    (ivt: list (reg_t * string))
  : schedule_information :=
    fold_left
      (fun s' r =>
        match list_assoc ivt r with
        | None => s' (* Unreachable *)
        | Some v => replace_rd1_with_var s' r (UVar v)
        end)
      active_regs s.

  (* F.2. Remove write0s *)
  Definition get_final_value
    (s: schedule_information) (ivt: list (reg_t * string)) (r: reg_t)
  : uact :=
    match list_assoc (sc_write1s s) r with
    | None => (* Not every active reg is in write1s *)
      match list_assoc ivt r with
      | None => URead P0 r (* Unreachable *)
      | Some v => UVar v
      end
    | Some v => v
    end.

  Definition generate_final_values_table
    (s: schedule_information) (regs: list reg_t) (ivt: list (reg_t * string))
  : ((list (reg_t * string)) * (list (string * uact))) :=
    let (r, _) :=
      fold_left
        (fun '(fvt, fvvm, id) r =>
          let name := generate_binding_name fvalb (S id) in
          ((r, name)::fvt, (name, get_final_value s ivt r)::fvvm, S id)
        )
        regs ([], [], 0)
    in r.

  Definition remove_interm (s: schedule_information) : simple_form :=
    let active_regs := find_all_used_regs s in
    let (ivt, ivvm) := generate_intermediate_values_table s active_regs in
    let s' := remove_read1s s active_regs ivt in
    let (fvt, fvvm) := generate_final_values_table s' active_regs ivt in {|
      final_values := fvt; vars := fvvm++ivvm++(sc_vars s');
      external_calls := sc_extcalls s' |}.

  (* G. Conversion *)
  (* Schedule can contain try or spos, but they are not used in the case we care
     about. *)
  Fixpoint schedule_to_list_of_rules (s: schedule) (rules: rule_name_t -> uact)
  : list uact :=
    match s with
    | Done => []
    | Cons r s' => (rules r)::(schedule_to_list_of_rules s' rules)
    | _ => []
    end.

  (* Precondition: only Cons and Done in schedule. *)
  (* Precondition: rules desugared. TODO desugar from here instead? *)
  Definition schedule_to_simple_form (s: schedule) (rules: rule_name_t -> uact)
  : simple_form :=
    (* Get list of uact from scheduler *)
    let rules_l := schedule_to_list_of_rules s rules in
    (* Get rule_information from each rule *)
    let '(rule_info_l, nid') :=
      fold_left
        (fun '(ri_acc, nid') r =>
          let '(ri, nid'') := get_rule_information r nid' in
          (* Not a fold right since we want the first rule to have the lowest
             indices. *)
          (ri_acc++[ri], nid''))
        rules_l ([], initial_ids)
    in
    (* Detect inter-rules conflicts *)
    let rule_info_with_conflicts_l := detect_all_conflicts rule_info_l in
    (* To schedule info, merge cancel conditions with actions conditions *)
    let schedule_info := merge_schedule rule_info_with_conflicts_l in
    (* To simple form *)
    remove_interm schedule_info.
End SimpleForm.
Close Scope nat.
