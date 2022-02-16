(*! Proving | Transformation of a schedule into a proof-friendly form !*)
Require Import Coq.Numbers.DecimalString Coq.Program.Equality Coq.Strings.Ascii.
Require Import Koika.Primitives Koika.Syntax.
From RecordUpdate Require Import RecordSet.
Import RecordSetNotations.
Require Import UntypedSemantics Koika.BitsToLists.

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
  Definition uact := @daction pos_t string string reg_t ext_fn_t.
  Definition schedule := scheduler pos_t rule_name_t.

  Definition const_nil {reg_t ext_fn_t} :=
    @DConst pos_t string string reg_t ext_fn_t (bits_t 0) (Bits.of_nat 0 0).
  Definition const_true {reg_t ext_fn_t} :=
    @DConst pos_t string string reg_t ext_fn_t (bits_t 1) (Bits.of_nat 1 1).
  Definition const_false {reg_t ext_fn_t} :=
    @DConst pos_t string string reg_t ext_fn_t (bits_t 1) (Bits.of_nat 1 0).

  (* Simple form and related structures *)
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

  (* * Bindings names *)
  (* TODO name collisions with previously standing variables can't possibly
       happen anymore (we treat everything in order). This makes it easier to
       give informative names to our variables. *)

  Definition generate_binding_name (n: nat) : string :=
    String.append "internal_var_" (NilEmpty.string_of_uint (Init.Nat.to_uint n)).

  Definition uor (x y: uact) := DBinop (PrimUntyped.UBits2 PrimUntyped.UOr) x y.
  Definition uand (x y: uact) := DBinop (PrimUntyped.UBits2 PrimUntyped.UAnd) x y.
  Definition unot (x: uact) := DUnop (PrimUntyped.UBits1 PrimUntyped.UNot) x.

  (* * rule_information extraction *)
  (* ** Addition of a new action into an existing rule_information *)
  (* *** Merger of failure conditions *)
  Definition or_conds (conds: list uact) :=
    fold_left uor conds const_false.

  Definition merge_failures (f1 f2: uact) : uact := uor f1 f2.

  Definition build_uif (cond ua1 ua2: option uact) : option uact :=
    (* We know that the original if being valid implies that cond != None and
       ua1 = Some x iff. ua2 = Some y *)
    match cond, ua1, ua2 with
    | Some c, Some x, Some y => Some (DIf c x y)
    | _, _, _ => None
    end.

  Fixpoint filter_map {A B: Type} (f: A -> option B) (l: list A) : list B :=
    match l with
      [] => []
    | x::r =>
        match f x with
        | None => filter_map f r
        | Some b => b::filter_map f r
        end
    end.

  (* *** Merger of actions *)
  (* Remove Nones from list, turn rest from (Some x) to x. *)
  Definition list_options_to_list (l: list (option uact)) : list uact :=
    filter_map id l.

  Definition merge_conds (wl: (* option *) (list write_info)) : (* option  *)uact :=
    (* match wl with *)
    (* | None => None *)
    (* | Some l =>  *)or_conds (map wcond wl)
    (* end *).

  Definition merge_failures_list (action_cond: uact) (conds: list uact)
    : (* option *) uact :=
    uand action_cond (or_conds conds).

  Definition add_read0 (rir: rule_information_raw) (grd: uact) (reg: reg_t)
  (* Returns modified rir *)
    : rule_information_raw :=
    let new_grd :=
      match list_assoc (rir_read0s rir) reg with
      | None => grd
      | Some cond' => uor cond' grd
      end in
    rir <| rir_read0s := list_assoc_set (rir_read0s rir) reg new_grd |>.

  Definition add_read1 (rir: rule_information_raw) (grd: uact) (reg: reg_t)
  (* Returns modified rule_information_raw *)
    : rule_information_raw :=
    let new_grd :=
      match list_assoc (rir_read1s rir) reg with
      | None => grd
      | Some cond' => uor cond' grd
      end in
    rir <| rir_read1s := list_assoc_set (rir_read1s rir) reg new_grd |>.

   Definition add_write0
    (rir: rule_information_raw) (grd: uact) (reg: reg_t) (val: uact)
  (* Returns modified rule_information_raw, failure conditions *)
     : rule_information_raw * uact :=
     let (new_grd, new_wi) :=
       match list_assoc (rir_write0s rir) reg with
       | None => (grd, [{| wcond := grd; wval := val |}])
       | Some c =>
           (uor (fst c) grd,
             (snd c)++[{| wcond := grd; wval := val |}])
       end in
     (rir <| rir_write0s :=
        list_assoc_set (rir_write0s rir) reg (new_grd, new_wi) |>,
    merge_failures_list
      grd
      (list_options_to_list ([
        option_map fst (list_assoc (rir_write0s rir) reg);
        list_assoc (rir_read1s rir) reg;
        option_map fst (list_assoc (rir_write1s rir) reg)]))).

  Definition add_write1
    (rir: rule_information_raw) (grd: uact) (reg: reg_t) (val: uact)
  (* Returns modified rule_information_raw, failure conditions *)
    : rule_information_raw * uact :=
    let (new_grd, new_wi) :=
       match list_assoc (rir_write1s rir) reg with
       | None => (grd, [{| wcond := grd; wval := val |}])
       | Some c =>
           (uor (fst c) grd,
             (snd c)++[{| wcond := grd; wval := val |}])
       end in
     (rir <| rir_write1s :=
        list_assoc_set (rir_write1s rir) reg (new_grd, new_wi) |>,
    merge_failures_list grd (list_options_to_list [
      option_map fst (list_assoc (rir_write1s rir) reg)])).

  Definition add_extcall
    (rir: rule_information_raw) (grd: uact) (ufn: ext_fn_t) (arg: uact)
    (name: string)
  : rule_information_raw :=
    rir <| rir_extcalls :=
      (ufn, {| econd := grd; earg := arg; ebind := name |})::(rir_extcalls rir)
    |>.

  (* ** Extraction of actions from rule *)
    Definition reduce (ua: option (uact)) : uact :=
    match ua with
    | None => const_nil
    | Some x => x
    end.
  
  Definition merge_branches
             (vm_tb vm_fb: list (string*string))
             (vvs: list (string * uact))
             (nid: nat)
             (cond_name: string) :=
    fold_left
      (fun '(acc, vv', let_id) '((str, n1), (_, n2)) =>
         if String.eqb n1 n2
         then ((str, n1)::acc, vv', let_id)
         else
           let name := generate_binding_name let_id in
           (
             (str, name)::acc,
             vv'++[(name, DIf (DVar cond_name) (DVar n1) (DVar n2))],
             S let_id)
      )
      (combine vm_tb vm_fb) ([], vvs, nid).

  Fixpoint merge_branches'
           (vm_tb vm_fb: list (string*string))
           (vvs: list (string * uact))
           (nid: nat)
           (cond_name: string) :=
    match vm_tb, vm_fb with
    | (str, n1)::vm_tb, (_, n2)::vm_fb =>
        let '(acc, vv', let_id) := merge_branches' vm_tb vm_fb vvs nid cond_name in
        if String.eqb n1 n2
        then ((str, n1)::acc, vv', let_id)
        else let name := generate_binding_name let_id in
             (
               (str, name)::acc,
               vv'++[(name, DIf (DVar cond_name) (DVar n1) (DVar n2))],
               S let_id)
    | _, _ => ([], vvs, nid)
    end.

  Lemma merge_branches_ok:
    forall vm_tb vm_fb vvs nid cond_name,
      List.length vm_tb = List.length vm_fb ->
      merge_branches (rev vm_tb) (rev vm_fb) vvs nid cond_name =
        merge_branches' vm_tb vm_fb vvs nid cond_name.
  Proof.
    induction vm_tb; simpl; intros; eauto.
    repeat destr. simpl. unfold merge_branches. rewrite combine_nil. simpl. auto.
    simpl.
    unfold merge_branches in *. rewrite combine_app. rewrite fold_left_app.
    simpl. destr. rewrite IHvm_tb in Heqp3.
    rewrite Heqp1 in Heqp3. inv Heqp3. rewrite Heqb. reflexivity.
    simpl in H; congruence.
    simpl in H.
    rewrite ! List.rev_length. congruence. reflexivity.
    simpl in H. inv H.
    simpl. unfold merge_branches. simpl.
    unfold merge_branches in *. rewrite combine_app. rewrite fold_left_app.
    simpl. destr. rewrite IHvm_tb in Heqp.
    rewrite Heqp1 in Heqp. inv Heqp. rewrite Heqb. reflexivity.
    auto.
    rewrite ! List.rev_length. auto. reflexivity.
  Qed.

  Definition gria_list
             (args: list uact)
             (env: list (string * string))
             vvs
             (rir: rule_information_raw)
             (nid: nat)
             (guard: uact)
             (rec: uact -> list (string * string) -> list(string * uact) -> uact -> rule_information_raw -> nat -> (option uact * list (string * string) * list (string * uact) * uact * rule_information_raw * nat ))
             names0 fail0
    :=
    fold_left
      (fun '(names, vm_p, vv_p, failures_p, rir_p, nid) a =>
         let '(val_c, vm_c, vv_c, failure_c, rir_c, nid) :=
           rec a vm_p vv_p guard rir_p nid
         in
         let arg_bind_name :=
           generate_binding_name nid
         in (
           arg_bind_name::names, vm_c,
           list_assoc_set vv_c (arg_bind_name) (reduce val_c),
           merge_failures failure_c failures_p, rir_c,
           S nid))
      args
      (names0, env, vvs, fail0, rir, nid).


  Definition gria_list'
             (guard: uact)
             (rec: uact -> list (string * string) -> list(string * uact) -> uact -> rule_information_raw -> nat -> (option uact * list (string * string) * list (string * uact) * uact * rule_information_raw * nat ))
    :=
    fix gria_list'
        (args: list uact)
        (env: list (string * string))
        (vvs: list (string * uact))
        (rir: rule_information_raw)
        (nid: nat)
        names0
        fail0
      : list string * list (string * string) * list (string * uact) * uact * rule_information_raw * nat
      :=
      match args with
        [] => (names0, env, vvs, fail0, rir, nid)
      | a::args =>
          let '(vc, vms, vvs, failure, rir, nid) :=
            rec a env vvs guard rir nid in
          let arg_bind_name := generate_binding_name nid in
          gria_list' args vms
                   (list_assoc_set vvs arg_bind_name (reduce vc))
                   rir (S nid) (arg_bind_name :: names0) (merge_failures failure fail0)
      end.

  Lemma gria_list_ok:
    forall args env vvs rir nid guard rec names0 fail0,
      gria_list args env vvs rir nid guard rec names0 fail0 =
        gria_list' guard rec args env vvs rir nid names0 fail0.
  Proof.
    induction args; simpl; intros; eauto.
    unfold gria_list in *. simpl.
    repeat destr. subst.
    rewrite IHargs. auto.
  Qed.

  (* This function extracts the actions for a given rule. It also returns the
     updated next_ids structure. *)
  Fixpoint get_rule_information_aux
           (* No need to pass failures as these impact the whole rule - taking note of
       all of them and factoring the conditions in is enough. Conflicts between
       different actions are also dealt with here. *)
           (* TODO improve guards management *)
           (* TODO guard could be option string instead *)
           (ua: uact) (env: list (string * string))
           (vvs: list (string * uact))
           (guard: uact)
           (rir: rule_information_raw) (nid: nat)
    (* Returns value, env, var_values, failure condition, rule_information_raw,
       next_ids *)
    : option (uact)
      * list (string * string)
      * (list (string * uact))
      * (uact) * rule_information_raw * nat
    (* TODO remove redundancies with rule_information_raw (failure_cond,
         var_values) *)
    :=
    match ua with
    | DBind var val body =>
        let '(ret_val, vm_val, vv_val, failures_val, rir_val, nid) :=
          get_rule_information_aux val env vvs guard rir nid
        in
        let name := generate_binding_name nid in
        let '(ret_body, vm_body, vv_body, failures_body, rir_body, nid) :=
          get_rule_information_aux
            body
            ((var, name)::env)
            (list_assoc_set vv_val name (reduce ret_val))
            guard
            rir_val
            (S nid)
        in (
          ret_body, skipn 1 vm_body (* var's binding goes out of scope *),
          vv_body,
          merge_failures failures_val failures_body, rir_body, nid)
    | DAssign var val =>
        let '(ret_val, vm_val, vv_val, failures_val, rir_val, nid) :=
          get_rule_information_aux val env vvs guard rir nid
        in
        let name := generate_binding_name nid in
        (None,
          list_assoc_set vm_val var name,
          list_assoc_set vv_val name (reduce ret_val),
          failures_val, rir_val, S nid
        )
    | DVar var =>
        match list_assoc env var with
        | Some x => (Some (DVar x), env, vvs, const_false, rir, nid)
        | None => (* Unreachable assuming rule valid *)
            (None, env, vvs, const_true, rir, nid)
        end
    | DSeq a1 a2 =>
        let '(_, vm_a1, vv_a1, failures_a1, rir_a1, nid_a1) :=
          get_rule_information_aux a1 env vvs guard rir nid
        in
        let '(ret_a2, vm_a2, vv_a2, failures_a2, rir_a2, nid_a2) :=
          get_rule_information_aux a2 vm_a1 vv_a1 guard rir_a1 nid_a1
        in
        (ret_a2, vm_a2, vv_a2, merge_failures failures_a1 failures_a2,
          rir_a2, nid_a2)
    | DIf cond tb fb =>
        let '(ret_cond, vm_cond, vv_cond, failures_cond, rir_cond, nid) :=
          get_rule_information_aux cond env vvs guard rir nid
        in
        let cond_name := generate_binding_name nid in
        let guard_tb_name := generate_binding_name (nid + 1) in
        let guard_fb_name := generate_binding_name (nid + 2) in
        let guard_tb := uand guard (DVar cond_name) in
        let guard_fb := uand guard (unot (DVar cond_name)) in
        let vv_cond := list_assoc_set vv_cond cond_name (reduce ret_cond) in
        let vv_cond := list_assoc_set vv_cond guard_tb_name guard_tb in
        let vv_cond := list_assoc_set vv_cond guard_fb_name guard_fb in
        let '(ret_tb, vm_tb, vv_tb, failures_tb, rir_tb, nid) :=
          get_rule_information_aux tb vm_cond vv_cond (DVar guard_tb_name) rir_cond
                                   (nid + 3)
        in
        let '(ret_fb, vm_fb, vv_fb, failures_fb, rir_fb, nid) :=
          (* We use rir_tb here even though we know that none of the actions added
           by the other branch can impact those from this branch (they are
           mutually exclusive). This way, we don't have to deal with
           rule_information_raw merging. However, this also means that the
           failure condition will contain some redundancy. *)
          get_rule_information_aux fb vm_cond vv_tb (DVar guard_fb_name) rir_tb nid
        in
        (* Merge var maps: if vm_tb and vm_fb disagree for some variable, generate
         a new variable reflecting the condition and update the variables map.
         *)
        let '(vm_merge, vv_merge, nid) := merge_branches' vm_tb vm_fb vv_fb nid cond_name in
        (build_uif ret_cond ret_tb ret_fb,
          vm_merge,
          vv_merge,
          (* Merging the failure conditions: looks complex because of the option
          types but really not that tricky. *)
          match ret_cond with
          | None => const_true (* Unreachable assuming a well-formed rule *)
          | Some x =>
              uor failures_cond
                  (uor
                     (uand x failures_tb)
                     (uand (unot x) failures_fb)
                  )
          end,
          rir_fb, nid)
    | DUnop ufn a =>
        let '(ret_a, vm_a, vv_a, failures_a, rir_a, nid) :=
          get_rule_information_aux a env vvs guard rir nid
        in
        (Some (DUnop ufn (reduce ret_a)), vm_a, vv_a, failures_a, rir_a, nid)
    | DBinop ufn a1 a2 =>
        let '(ret_a1, vm_a1, vvs, failures_a1, rir_a1, nid) :=
          get_rule_information_aux a1 env vvs guard rir nid
        in
        let '(ret_a2, vm_a2, vvs, failures_a2, rir_a2, nid) :=
          get_rule_information_aux a2 vm_a1 vvs guard rir_a1 nid
        in
        (Some (DBinop ufn (reduce ret_a1) (reduce ret_a2)), vm_a2, vvs,
          merge_failures failures_a1 failures_a2, rir_a2, nid)
    | DInternalCall ufn args =>
        let '(arg_names, vm_args, vv_args, failure_args, rir_args, nid) :=
          gria_list' guard get_rule_information_aux args env vvs rir nid [] const_false in
        let vm_tmp :=
          combine
            (fst (split (int_argspec ufn))) (* Names from argspec *)
            (* We know that a value is assigned to each argument in well formed
             rules *)
            arg_names
        in
        let '(ret_ic, _, vv_ic, failure_ic, rir_ic, nid) :=
          get_rule_information_aux (int_body ufn) vm_tmp vv_args guard rir_args nid
        in
        (* We can forget vm_tmp which contained the temporary map for use in the
         called function. *)
        (ret_ic, vm_args, vv_ic, merge_failures failure_ic failure_args,
          rir_ic, nid)
    | DAPos _ e => get_rule_information_aux e env vvs guard rir nid
    | DRead port reg =>
        let modified_rir :=
          match port with
          | P0 => add_read0 rir guard reg
          | P1 => add_read1 rir guard reg
          end
        in (Some ua, env, vvs, const_false, modified_rir, nid)
    | DWrite port reg val =>
        let '(ret_val, vm_val, vv_val, failures_val, actions_val, nid) :=
          get_rule_information_aux val env vvs guard rir nid
        in
        let '(rir_wr, failure_wr) :=
          match port with
          | P0 => add_write0 actions_val guard reg (reduce ret_val)
          | P1 => add_write1 actions_val guard reg (reduce ret_val)
          end
        in
        (None, vm_val, vv_val, merge_failures failures_val failure_wr, rir_wr,
          nid)
    | DExternalCall ufn arg =>
        let '(ret_arg, vm_arg, vv_arg, failures_arg, actions_arg, nid) :=
          get_rule_information_aux arg env vvs guard rir nid
        in
        let name := generate_binding_name nid in
        let new_rir := add_extcall rir guard ufn (reduce ret_arg) name in
        (Some (DVar name), vm_arg, vv_arg, failures_arg, new_rir,
          S nid)
    | DError _ => (None, env, vvs, const_true, rir, nid)
    | DFail _ => (None, env, vvs, const_true, rir, nid)
    | DConst _ => (Some ua, env, vvs, const_false, rir, nid)
    end.

  Inductive simple_shape : uact -> Prop :=
  | simple_shape_var v: simple_shape (DVar v)
  | simple_shape_const tau (v: type_denote tau): simple_shape (DConst v)
  | simple_shape_if c t f:
    simple_shape c -> simple_shape t -> simple_shape f ->
    simple_shape (DIf c t f)
  | simple_shape_unop ufn a: simple_shape a -> simple_shape (DUnop ufn a)
  | simple_shape_binop ufn a1 a2: simple_shape a1 -> simple_shape a2 -> simple_shape (DBinop ufn a1 a2)
  | simple_shape_read prt idx: simple_shape (DRead prt idx)
  .

  Lemma get_rule_information_aux_act_shape:
    forall (ua: uact)
           (env: list (string * string)) (guard: uact)
           (rir: rule_information_raw) (nid: nat)
           v env' vvs vvs0 fail_cond rir' nid'
           (GRIA: get_rule_information_aux ua env vvs0 guard rir nid = (Some v, env', vvs, fail_cond, rir', nid')),
      simple_shape v.
  Proof.
    intros ua; pattern ua.
    eapply daction_ind'; simpl; intros; eauto.
    - inv GRIA.
    - inv GRIA.
    - repeat destr_in GRIA; inv GRIA; constructor.
    - repeat destr_in GRIA; inv GRIA; constructor.
    - repeat destr_in GRIA; inv GRIA; constructor.
    - repeat destr_in GRIA; inv GRIA. eauto.
    - repeat destr_in GRIA; inv GRIA; eauto.
    - repeat destr_in GRIA; inv GRIA.
      repeat destr_in H3; inv H3. constructor; eauto.
    - repeat destr_in GRIA; inv GRIA; constructor.
    - repeat destr_in GRIA; inv GRIA.
    - repeat destr_in GRIA; inv GRIA. constructor. unfold reduce; destr. eauto. constructor.
    - repeat destr_in GRIA; inv GRIA. constructor.
      unfold reduce; destr. eauto. constructor.
      unfold reduce; destr. eauto. constructor.
    - repeat destr_in GRIA; inv GRIA. constructor.
    - repeat destr_in GRIA; inv GRIA. eauto.
  Qed.

  
  Inductive var_in_uact : uact -> string -> Prop :=
  | var_in_uact_var v: var_in_uact (DVar v) v
  | var_in_if_cond c t f v:
    var_in_uact c v ->
    var_in_uact (DIf c t f) v
  | var_in_if_true c t f v:
    var_in_uact f v ->
    var_in_uact (DIf c t f) v
  | var_in_if_false c t f v:
    var_in_uact t v ->
    var_in_uact (DIf c t f) v
  | var_in_uact_unop ufn a v:
    var_in_uact a v -> var_in_uact (DUnop ufn a) v
  | var_in_uact_binop_1 ufn a1 a2 v:
    var_in_uact a1 v -> var_in_uact (DBinop ufn a1 a2) v
  | var_in_uact_binop_2 ufn a1 a2 v:
    var_in_uact a2 v -> var_in_uact (DBinop ufn a1 a2) v.


  Lemma list_assoc_set_key_in:
    forall {K V: Type} {eq_dec_k: EqDec K} (l: list (K*V)) k v,
      In k (map fst (list_assoc_set l k v)).
  Proof.
    induction l; simpl; intros; eauto.
    repeat destr. subst; simpl; auto. simpl; eauto.
  Qed.


  Lemma list_assoc_set_key_stays_in:
    forall {K V: Type} {eq_dec_k: EqDec K} (l: list (K*V)) k k' v,
      In k (map fst l) ->
      In k (map fst (list_assoc_set l k' v)).
  Proof.
    induction l; simpl; intros; eauto.
    repeat destr. subst; simpl; auto. simpl in *; eauto.
    destruct H; auto.
  Qed.

  Lemma list_assoc_cons:
    forall {K V: Type} {eq_dec_k: EqDec K} (l: list (K*V)) k k' v,
      list_assoc ((k,v)::l) k' =
        if eq_dec k' k then Some v else list_assoc l k'.
  Proof.
    reflexivity.
  Qed.

  Inductive wf_uact_known_vars: list string -> uact -> Prop :=
  | wf_uact_known_vars_error l e: wf_uact_known_vars l (DError e)
  | wf_uact_known_vars_fail l e: wf_uact_known_vars l (DFail e)
  | wf_uact_known_vars_var l v: In v l -> wf_uact_known_vars l (DVar v)
  | wf_uact_known_vars_const l tau (c: type_denote tau): wf_uact_known_vars l (DConst c)
  | wf_uact_known_vars_assign l v a:
    wf_uact_known_vars l a ->
    In v l ->
    wf_uact_known_vars l (DAssign v a)
  | wf_uact_known_vars_seq l a1 a2:
    wf_uact_known_vars l a1 ->
    wf_uact_known_vars l a2 ->
    wf_uact_known_vars l (DSeq a1 a2)
  | wf_uact_known_vars_bind l v a body :
    wf_uact_known_vars l a ->
    wf_uact_known_vars (v::l) body ->
    wf_uact_known_vars l (DBind v a body)
  | wf_uact_known_vars_if l c t f :
    wf_uact_known_vars l c ->
    wf_uact_known_vars l t ->
    wf_uact_known_vars l f ->
    wf_uact_known_vars l (DIf c t f)
  | wf_uact_known_vars_read l p i:
    wf_uact_known_vars l (DRead p i)
  | wf_uact_known_vars_write l p i a:
    wf_uact_known_vars l a ->
    wf_uact_known_vars l (DWrite p i a)
  | wf_uact_known_vars_unop l ufn a:
    wf_uact_known_vars l a ->
    wf_uact_known_vars l (DUnop ufn a)
  | wf_uact_known_vars_binop l ufn a1 a2:
    wf_uact_known_vars l a1 ->
    wf_uact_known_vars l a2 ->
    wf_uact_known_vars l (DBinop ufn a1 a2)
  | wf_uact_known_vars_ext l ufn a:
    wf_uact_known_vars l a ->
    wf_uact_known_vars l (DExternalCall ufn a)
  | wf_uact_known_vars_int l ufn a:
    Forall (wf_uact_known_vars l) a ->
    List.length (map fst (int_argspec ufn)) = List.length a ->
    wf_uact_known_vars (map fst (int_argspec ufn)) (int_body ufn) ->
    wf_uact_known_vars l (DInternalCall ufn a).

  Lemma same_env_set_in:
    forall env' env
           (SAMEENV: Forall2 (fun x y : string * string => fst x = fst y) env env')
           v n
           (VARIN: In v (map fst env)) ,
      Forall2 (fun x y : string * string => fst x = fst y) env (list_assoc_set env' v n).
  Proof.
    Opaque eq_dec.
    induction env'; simpl; intros; eauto.
    - inv SAMEENV. simpl in *; easy.
    - inv SAMEENV. simpl in *. destr. simpl in *. subst.
      destr.
      + subst. simpl. constructor. reflexivity. auto.
      + constructor. reflexivity. eapply IHenv'. eauto. destruct VARIN; congruence.
  Qed.

  Lemma same_env_trans:
    forall {P: Type} (R: P -> P -> Prop) (Rtrans: forall x y z, R x y -> R y z -> R x z)
           l1 l2,
      Forall2 R l1 l2 -> forall l3, Forall2 R l2 l3 -> Forall2 R l1 l3.
  Proof.
    induction 2; simpl; intros; eauto. inv H1; constructor; eauto.
  Qed.

  Lemma same_env_refl:
    forall (l: list (string * string)),
      Forall2 (fun x y => fst x = fst y) l l.
  Proof.
    induction l; simpl; intros; eauto.
  Qed.

  Lemma same_env_sym:
    forall (l1 l2: list (string * string)),
      Forall2 (fun x y => fst x = fst y) l1 l2 ->
      Forall2 (fun x y => fst x = fst y) l2 l1.
  Proof.
    induction 1; simpl; intros; eauto.
  Qed.

  Lemma same_env_same_fst:
    forall (l1 l2: list (string * string)),
      Forall2 (fun x y => fst x = fst y) l1 l2 ->
      map fst l1 = map fst l2.
  Proof.
    induction 1; simpl; intros; eauto. congruence.
  Qed.

  Lemma merge_vms_preserve_same_env:
    forall (l2 l4: list (string*string))
           (F: Forall2 (fun x y => fst x = fst y) l2 l4)
           (l3: list (string*uact)) cname n1 env' vvs n2,
      merge_branches' l2 l4 l3 n1 cname = (env', vvs, n2) ->
      Forall2 (fun x y => fst x = fst y) l2 env'.
  Proof.
    induction 1; simpl; intros; eauto.
    - inv H. constructor.
    - do 4 destr_in H0. apply IHF in Heqp1.
      destr_in H0. inv H0. constructor; auto.
      inv H0. constructor; auto.
  Qed.



  Lemma gria_list_same_env:
    forall
      args env
      (F: Forall (wf_uact_known_vars (map fst env)) args)
      (IH: Forall
             (fun u : uact =>
                forall (env : list (string * string)) (guard : uact)
                       (rir : rule_information_raw) (nid : nat) 
                       (v : option uact) (env' : list (string * string))
                       (vvs : list (string * uact)) (fail_cond : uact)
                       (rir' : rule_information_raw) (nid' : nat)
                       (vvs0 : list (string * uact)),
                  wf_uact_known_vars (map fst env) u ->
                  get_rule_information_aux u env vvs0 guard rir nid =
                    (v, env', vvs, fail_cond, rir', nid') ->
                  Forall2 (fun x y : string * string => fst x = fst y) env env') args
      )
      names0 vvs0 fail0 rir nid l0 env' l u r n guard,
      gria_list' guard get_rule_information_aux args env vvs0 rir nid names0 fail0 =
        (l0, env', l, u, r, n) ->
      Forall2 (fun x y => fst x = fst y) env env' /\ List.length l0 = List.length names0 + List.length args.
  Proof.
    induction args; simpl; intros; eauto.
    - inv H. split. apply same_env_refl. lia.
    - repeat destr_in H. subst. inv IH. inv F.
      eapply H2 in Heqp; eauto. clear H2.
      eapply IHargs in H; eauto.
      destruct H.
      split.
      eapply same_env_trans; eauto. congruence.
      simpl in H0. lia.
      erewrite <- same_env_same_fst; eauto.
  Qed.

  Lemma map_fst_combine:
    forall {A B: Type} (l1: list A) (l2: list B),
      List.length l1 = List.length l2 ->
      map fst (combine l1 l2) = l1.
  Proof.
    induction l1; simpl; intros; eauto. destr. simpl in *; lia. simpl in *.
    f_equal. eauto.
  Qed.

  Lemma fst_split_map:
    forall {A B: Type} (l: list (A*B)),
      fst (split l) = map fst l.
  Proof.
    induction l; simpl; intros; eauto. repeat destr. subst. simpl. f_equal.
    simpl in IHl. auto.
  Qed.
  
  Lemma get_rule_information_aux_same_vm:
    forall (ua: uact)
           (env: list (string * string)) (guard: uact)
           (rir: rule_information_raw) (nid: nat)
           v env' vvs fail_cond rir' nid' vvs0
           (WUKV: wf_uact_known_vars (map fst env) ua)
           (GRIA: get_rule_information_aux ua env vvs0 guard rir nid = (v, env', vvs, fail_cond, rir', nid'))
    ,
      Forall2 (fun x y => fst x = fst y) env env'.
  Proof.
    assert (forall e : list (string*string), Forall2 (fun x y => fst x = fst y) e e).
    {
      induction e; simpl; intros; eauto.
    }
    Opaque skipn.
    intros ua; pattern ua; eapply daction_ind'; simpl; intros; eauto.
    all: try now (repeat destr_in GRIA; inv GRIA; inv WUKV; eauto).
    - repeat destr_in GRIA; inv GRIA; inv WUKV; eauto.
      apply H0 in Heqp; auto.
      eapply same_env_set_in; eauto.
    - repeat destr_in GRIA; inv GRIA; inv WUKV; eauto.
      apply H0 in Heqp; auto.
      apply H1 in Heqp4; auto.
      eapply same_env_trans; eauto. congruence.
      erewrite <- same_env_same_fst; eauto.
    - repeat destr_in GRIA. inv GRIA.
      apply H0 in Heqp; auto.
      apply H1 in Heqp4; auto.
      inv Heqp4. eauto.
      inv WUKV. simpl; auto.
      inv WUKV. auto.
    - do 17 destr_in GRIA. inv GRIA; inv WUKV; eauto.
      apply H0 in Heqp; auto.
      apply H1 in Heqp4; auto.
      apply H2 in Heqp9; auto.
      eapply same_env_trans; eauto. congruence.
      eapply merge_vms_preserve_same_env in Heqp14.
      eapply same_env_trans. congruence. apply Heqp4. auto.
      eapply same_env_trans. congruence. apply same_env_sym. eauto. auto.
      erewrite <- same_env_same_fst; eauto.
      erewrite <- same_env_same_fst; eauto.
    - repeat destr_in GRIA. inv GRIA. inv WUKV.
      apply H0 in Heqp; auto.
      apply H1 in Heqp4; auto.
      eapply same_env_trans; eauto. congruence.
      erewrite <- same_env_same_fst; eauto.
    - repeat destr_in GRIA. inv GRIA. inv WUKV.
      eapply gria_list_same_env in Heqp; eauto.
      destruct Heqp; eauto.
  Qed.

  Lemma in_list_assoc_set_inv:
    forall {K V: Type} {eq_dec: EqDec K} (l: list (K * V)) k' v' k v,
      In (k', v') (list_assoc_set l k v) ->
      (k, v) = (k', v') \/ In (k', v') l.
  Proof.
    induction l; simpl; intros; eauto.
    repeat destr_in H; simpl in *; subst.
    destruct H; auto.
    destruct H; auto. apply IHl in H. destruct H; auto.
  Qed.

  Definition valid_name name nid :=
    exists n, name = generate_binding_name n /\ n < nid.
  Definition vvs_range (vvs: list (string * uact)) (nid: nat) :=
    forall x y,
      In (x,y) vvs -> valid_name x nid.

  Lemma string_append_inj:
    forall (s1 s2 s3: string),
      String.append s1 s2 = String.append s1 s3 -> s2 = s3.
  Proof.
    induction s1; simpl; intros; eauto. inv H. eauto.
  Qed.
  Lemma generate_binding_name_inj:
    forall n1 n2,
      generate_binding_name n1 = generate_binding_name n2 -> n1 = n2.
  Proof.
    unfold generate_binding_name.

    intros.
    apply string_append_inj in H.
    apply (f_equal NilEmpty.uint_of_string) in H.
    rewrite ! NilEmpty.usu in H.
    inv H.
  Admitted.

  Lemma list_assoc_set_not_before:
    forall {K V: Type} {eqdec: EqDec K} (l: list (K * V)) k v k' v' ,
      ~ In k (map fst l) ->
      In (k', v') (list_assoc_set l k v) <-> In (k', v') l \/ (k, v) = (k', v').
  Proof.
    induction l; simpl; intros; eauto. tauto.
    repeat destr; simpl in *; subst.
    contradict H. auto.
    rewrite IHl. tauto. tauto.
  Qed.

  Lemma vvs_range_in_fst:
    forall vvs n,
    vvs_range vvs n ->
    forall k,
      In (generate_binding_name k) (map fst vvs) ->
      k < n.
  Proof.
    unfold vvs_range. intros.
    rewrite in_map_iff in H0. destruct H0 as (x & EQ & IN).
    destruct x. simpl in *. subst.
    apply H in IN.
    destruct IN as (n0 & EQ & LT).
    apply generate_binding_name_inj in EQ. subst. auto.
  Qed.

  Lemma vvs_range_list_assoc_set:
    forall vvs n name v,
      vvs_range vvs n ->
      valid_name name n ->
      vvs_range (list_assoc_set vvs name v) n.
  Proof.
    unfold vvs_range; simpl; intros.
    apply in_list_assoc_set_inv in H1; destruct H1. inv H1. auto. eauto.
  Qed.

  Lemma valid_name_incr:
    forall name n1 n2 (INCR: n1 <= n2),
      valid_name name n1 -> valid_name name n2.
  Proof.
    unfold valid_name. intros name n1 n2 INCR (n & EQ & LT).
    eexists; split; eauto. lia.
  Qed.

  Lemma vvs_range_incr:
    forall vvs n1 n2 (INCR: n1 <= n2),
      vvs_range vvs n1 -> vvs_range vvs n2.
  Proof.
    unfold vvs_range; simpl; intros; eauto using valid_name_incr.
  Qed.
  Ltac trim H :=
    match type of H with
    | ?a -> ?b =>
      let x := fresh "H" in
      assert(x: a);[|specialize(H x); clear x]
    end.

  Lemma in_map_list_assoc_set_inv:
    forall {K V: Type} {eqdec: EqDec K} (l : list (K * V)) (k : K)
           (v : V) k' ,
      In k' (map fst (list_assoc_set l k v)) ->
      k = k' \/ In k' (map fst l).
  Proof.
    induction l; simpl; intros; eauto. repeat destr_in H. subst. simpl. auto.
    simpl in *. destruct H; auto. apply IHl in H. tauto.
  Qed.


  Definition var_lt (v1 v2: string) :=
    exists n1 n2,
      v1 = generate_binding_name n1
      /\ v2 = generate_binding_name n2
      /\ n1 < n2.

  Lemma var_lt_gen_r:
    forall s n n' ,
      n <= n' ->
      var_lt s (generate_binding_name n) ->
      var_lt s (generate_binding_name n').
  Proof.
    unfold var_lt; simpl; intros. destruct H0 as (n1 & n2 & EQ & EQ2 & LT). subst.
    apply generate_binding_name_inj in EQ2.
    do 2 eexists; repeat split; eauto. lia.
  Qed.

  Lemma merge_banches_grows:
    forall vm_tb vm_fb vvs nid cond_name vm' vvs' nid'
           (MB: merge_branches' vm_tb vm_fb vvs nid cond_name = (vm', vvs', nid'))
           (ENVVVS1: forall x y, In (x,y) vm_tb -> In y (map fst vvs))
           (ENVVVS2: forall x y, In (x,y) vm_fb -> In y (map fst vvs))
           (RNGVVS: vvs_range vvs nid)
           (VVSVALID: forall (v : string) (a : uact),
               In (v, a) vvs -> forall v' : string, var_in_uact a v' -> var_lt v' v
           )
           (VALIDCOND: valid_name cond_name nid)
    ,
      (forall x y, In (x,y) vvs -> In (x,y) vvs') /\
        vvs_range vvs' nid' /\
        (forall x y, In (x,y) vm' -> In y (map fst vvs')) /\ nid <= nid' /\
        (forall (v : string) (a : uact),
            In (v, a) vvs' -> forall v' : string, var_in_uact a v' -> var_lt v' v).
  Proof.
    induction vm_tb; simpl; intros; eauto.
    - inv MB. split; auto.
    - repeat destr_in MB; inv MB. auto.
      + edestruct IHvm_tb as (VVSGROWS3 & VVSRANGE3 & ENVVVS3 & NIDGROWS3 & VVSVALID3). eauto.
        intros; eapply ENVVVS1; eauto.
        intros; eapply ENVVVS2; simpl; eauto. auto. auto. auto.
        repeat split; auto.
        simpl; intros. destruct H; eauto. inv H.
        specialize (ENVVVS2 _ _ (or_introl eq_refl)). apply in_map_iff in ENVVVS2.
        destruct ENVVVS2 as ((s3&aa)&EQ&IN). simpl in *; subst.
        apply VVSGROWS3 in IN.
        apply (in_map fst) in IN. simpl in IN.
        apply eqb_eq in Heqb. subst; auto.
      + edestruct IHvm_tb as (VVSGROWS3 & VVSRANGE3 & ENVVVS3 & NIDGROWS3 & VVSVALID3). eauto.
        intros; eapply ENVVVS1; eauto.
        intros; eapply ENVVVS2; simpl; eauto. auto. auto. auto.
        repeat split; auto.
        * simpl; intros. rewrite in_app_iff. eauto.
        * red. intros x y. rewrite in_app_iff.  intros [A|A].
          eapply VVSRANGE3 in A. eapply valid_name_incr. 2: eauto. lia.
          simpl in A. destruct A as [A|[]]. inv A. red; eexists; split; eauto.
        * simpl. intros x y [A|A].
          inv A. rewrite map_app.  apply in_or_app. right. simpl.  auto.
          rewrite map_app.  apply in_or_app. left. eauto.
        * intros.
          rewrite in_app_iff in H. destruct H; eauto.
          simpl in H. destruct H as [H|[]]. inv H.
          inv H0. inv H4.
          destruct VALIDCOND as (condno & EQ & LT). subst.
          do 2 eexists; repeat split; eauto. lia.
          inv H4; eauto.
          specialize (ENVVVS2 _ _ (or_introl eq_refl)). apply in_map_iff in ENVVVS2.
          destruct ENVVVS2 as ((ss&a) & EQ & IN). simpl in *. subst.
          apply RNGVVS in IN.
          destruct IN as (condno & EQ & LT). subst.
          do 2 eexists; repeat split; eauto. lia.
          inv H4; eauto.
          specialize (ENVVVS1 _ _ (or_introl eq_refl)). apply in_map_iff in ENVVVS1.
          destruct ENVVVS1 as ((ss&a) & EQ & IN). simpl in *. subst.
          apply RNGVVS in IN.
          destruct IN as (condno & EQ & LT). subst.
          do 2 eexists; repeat split; eauto. lia.
  Qed.

  Definition valid_vars_uact v n :=
    forall var, var_in_uact v var -> var_lt var (generate_binding_name n).
  Lemma valid_vars_merge_failures:
    forall u u0 n,
      valid_vars_uact u n ->
      valid_vars_uact u0 n ->
      valid_vars_uact (merge_failures u u0) n.
  Proof.
    red; intros. inv H1; eauto.
  Qed.

  Lemma valid_vars_and:
    forall u u0 n,
      valid_vars_uact u n ->
      valid_vars_uact u0 n ->
      valid_vars_uact (uand u u0) n.
  Proof.
    red; intros. inv H1; eauto.
  Qed.

  Lemma valid_vars_not:
    forall u n,
      valid_vars_uact u n ->
      valid_vars_uact (unot u) n.
  Proof.
    red; intros. inv H0; eauto.
  Qed.

  Lemma valid_vars_fold_uor:
    forall conds n,
      Forall (fun a => valid_vars_uact a n) conds ->
      forall ci,
        valid_vars_uact ci n ->
        valid_vars_uact (fold_left uor conds ci) n.
  Proof.
    induction 1; simpl; intros; eauto.
    apply IHForall. apply valid_vars_merge_failures; auto.
  Qed.

  Lemma valid_vars_or_conds:
    forall conds n,
      Forall (fun a => valid_vars_uact a n) conds ->
      valid_vars_uact (or_conds conds) n.
  Proof.
    intros; eapply valid_vars_fold_uor; eauto.
    red; intros. inv H0.
  Qed.

  Lemma valid_var_uact_incr:
    forall v n1 n2,
      valid_vars_uact v n1 ->
      n1 <= n2 ->
      valid_vars_uact v n2.
  Proof.
    red; intros.
    eapply H in H1. eapply var_lt_gen_r; eauto.
  Qed.

  Lemma gria_list_grows:
    forall
      (I: list (string*string) -> list (string * uact) -> nat -> rule_information_raw -> uact -> Prop)
      (P: list (string*string) -> list (string * uact) -> nat -> rule_information_raw ->
          list (string*string) -> list (string * uact) -> nat -> rule_information_raw -> Prop)
      (Prefl: forall env vvs nid rir, P env vvs nid rir env vvs nid rir)
      (Ptrans: forall env1 vvs1 nid1 rir1 env2 vvs2 nid2 rir2 env3 vvs3 nid3 rir3 grd1 grd2,
          I env1 vvs1 nid1 rir1 grd1 ->
          P env1 vvs1 nid1 rir1 env2 vvs2 nid2 rir2 ->
          I env2 vvs2 nid2 rir2 grd2 ->
          P env2 vvs2 nid2 rir2 env3 vvs3 nid3 rir3 ->
          P env1 vvs1 nid1 rir1 env3 vvs3 nid3 rir3
      )
      (Pwukv:
        forall env1 vvs1 nid1 rir1 env2 vvs2 nid2 rir2,
          P env1 vvs1 nid1 rir1 env2 vvs2 nid2 rir2 ->
          forall u,
            wf_uact_known_vars (map fst env1) u ->
            wf_uact_known_vars (map fst env2) u
      )
      (Psetvvs:
        forall env vvs n rir grd v,
          I env vvs n rir grd ->
          valid_vars_uact v n ->
          P env vvs n rir env (list_assoc_set vvs (generate_binding_name n) v) (S n) rir /\
            I env (list_assoc_set vvs (generate_binding_name n) v) (S n) rir grd
      )
      (Pvvsgrows:
        forall env1 vvs1 nid1 rir1 grd1 env2 vvs2 nid2 rir2,
          P env1 vvs1 nid1 rir1 env2 vvs2 nid2 rir2 ->
          I env1 vvs1 nid1 rir1 grd1 ->
          forall x,
            In x (map fst vvs1) -> In x (map fst vvs2)
      )
      rec args
      (F: Forall (fun u =>
                    forall env guard rir nid v env' vvs fail_cond rir' nid' vvs0,
                      rec u env vvs0 guard rir nid = (v, env', vvs, fail_cond, rir', nid') ->
                      wf_uact_known_vars (map fst env) u ->
                      valid_vars_uact guard nid ->
                      I env vvs0 nid rir guard ->
                      P env vvs0 nid rir env' vvs nid' rir' /\ I env' vvs nid' rir' guard
                      /\ (forall ov, v = Some ov -> valid_vars_uact ov nid')
                      /\ valid_vars_uact guard nid'
                      /\ valid_vars_uact fail_cond nid'
                      /\ nid <= nid'
                 ) args)
      guard env vvs0 rir nid names0 fail0 names env' vvs fail1 rir' nid'
      (WUKV: Forall (wf_uact_known_vars (map fst env)) args)
      (VG: valid_vars_uact guard nid)
      (VF: valid_vars_uact fail0 nid)
      (INV: I env vvs0 nid rir guard)
      (GRIA: gria_list' guard rec args env vvs0 rir nid names0 fail0 = (names, env', vvs, fail1, rir', nid'))
      (NAMES: Forall (fun name => In name (map fst vvs0)) names0)
    ,
      P env vvs0 nid rir env' vvs nid' rir'
      /\ I env' vvs nid' rir' guard
      /\ Forall (fun name => In name (map fst vvs)) names
      /\ List.length names = List.length names0 + List.length args
      /\ valid_vars_uact fail1 nid'
      /\ nid <= nid'.
  Proof.
    induction 6; simpl; intros; eauto.
    - inv GRIA. repeat split; eauto.
    - inv WUKV.
      repeat destr_in GRIA. subst.
      apply H in Heqp; auto. destruct Heqp as (P2 & I2 & RV2 & VG2 & VF2 & NIDGROWS2). clear H.
      eapply Forall_impl in H3.
      2: intros a WUKV; eapply Pwukv in WUKV. 3: exact P2. 2: apply WUKV.
      eapply IHF in GRIA;  eauto.
      destruct GRIA as (Pgria & Igria & NAMES1 & LENNAMES & VF3 & NIDGROWS).

      repeat split; eauto.
      + eapply Ptrans; eauto.
        eapply Ptrans. eauto. 3: eauto.
        all: eapply Psetvvs; eauto.
        intros. destruct o. simpl. eauto. red; simpl; intros. inv H.
        intros. destruct o. simpl. eauto. red; simpl; intros. inv H.
      + simpl in LENNAMES; lia.
      + lia.
      + red; intros. eapply var_lt_gen_r. 2: eauto. lia.
      + eapply valid_vars_merge_failures; eauto using valid_var_uact_incr.
      + eapply Psetvvs; eauto.
        intros. destruct o. simpl. eauto. red; simpl; intros. inv H.
      + constructor.
        apply list_assoc_set_key_in.
        eapply Forall_impl. 2: apply NAMES. simpl.
        intros a IN.
        eapply Pvvsgrows in IN. 2: eauto.
        eapply list_assoc_set_key_stays_in; eauto. eauto.
  Qed.

  Lemma list_assoc_in:
    forall {K V: Type} {eq_dec_k: EqDec K} (l: list (K*V)) k v,
      list_assoc l k = Some v -> In (k,v) l.
  Proof.
    induction l; simpl; intros; eauto. easy. repeat destr_in H. inv H. auto. eauto.
  Qed.

  Lemma incl_incl_map:
    forall {A B: Type} (l1 l2: list (A * B))
           (P: forall x y, In (x, y) l1 -> In (x, y) l2),
    forall x, In x (map fst l1) -> In x (map fst l2).
  Proof.
    intros.
    rewrite in_map_iff in H.
    destruct H as ((a,b) & EQ & IN). subst.
    apply in_map; auto.
  Qed.


  Record wf_write_log_raw (wl: write_log_raw) (n: nat) :=
    {
      wf_wlr_glob_cond: forall i a, In (i, a) wl -> valid_vars_uact (fst a) n ;
      wf_wlr_each_cond: forall i a, In (i, a) wl ->
                                    Forall (fun wi => valid_vars_uact (wcond wi) n) (snd a);
      wf_wlr_each_act: forall i a, In (i, a) wl ->
                                   Forall (fun wi => valid_vars_uact (wval wi) n) (snd a);
    }.

  Record wf_extcall_info (ext: extcall_info) (n: nat) :=
    {
      wf_ei_cond: valid_vars_uact (econd ext) n;
      wf_ei_arg: valid_vars_uact (earg ext) n;
      wf_ei_bind: var_lt (ebind ext) (generate_binding_name n);
    }.

  Record wf_rir (r: rule_information_raw) (n: nat) :=
    {
      wf_rir_read0s: forall i a, In (i, a) (rir_read0s r) -> valid_vars_uact a n;
      wf_rir_read1s: forall i a, In (i, a) (rir_read1s r) -> valid_vars_uact a n;
      wf_rir_write0s: wf_write_log_raw (rir_write0s r) n;
      wf_rir_write1s: wf_write_log_raw (rir_write1s r) n;
      wf_rir_extcalls: forall i ext, In (i, ext) (rir_extcalls r) -> wf_extcall_info ext n
    }.


  Lemma wf_extcall_info_incr:
    forall r n1 n2,
      wf_extcall_info r n1 ->
      n1 <= n2 ->
      wf_extcall_info r n2.
  Proof.
    intros. inv H. split; eauto using valid_var_uact_incr.
    eauto using var_lt_gen_r.
  Qed.

  Lemma wf_write_log_raw_incr:
    forall r n1 n2,
      wf_write_log_raw r n1 ->
      n1 <= n2 ->
      wf_write_log_raw r n2.
  Proof.
    intros. inv H. split; eauto using valid_var_uact_incr.
    intros. apply wf_wlr_each_cond0 in H. eapply Forall_impl; eauto. simpl; eauto using valid_var_uact_incr.
    intros. apply wf_wlr_each_act0 in H. eapply Forall_impl; eauto. simpl; eauto using valid_var_uact_incr.
  Qed.

  Lemma wf_rir_incr:
    forall r n1 n2,
      wf_rir r n1 ->
      n1 <= n2 ->
      wf_rir r n2.
  Proof.
    intros. inv H. split; eauto using valid_var_uact_incr, wf_extcall_info_incr, wf_write_log_raw_incr.
  Qed.

  Lemma vss_or_extcall_var_lt:
    forall l n rir
           (VVSRANGE : vvs_range l n)
           (RIRRNG : wf_rir rir n)
           v'
           (H0 : In v' (map fst l) \/
                   (exists ext : ext_fn_t * extcall_info,
                       In ext (rir_extcalls rir) /\ ebind (snd ext) = v')),
      var_lt v' (generate_binding_name n).
  Proof.
    intros.
    destruct H0.
    rewrite in_map_iff in H. destruct H as ((s&a) & EQ & IN). apply VVSRANGE in IN.
    red in IN. destruct IN as (n0 & EQ2 & LT). do 2 eexists; repeat split; eauto. subst.  reflexivity.
    destruct H as (ext & IN & EQ).
    subst. inv RIRRNG. destruct ext. apply wf_rir_extcalls0 in IN.
    destruct IN. eauto.
  Qed.


  Lemma filter_map_In:
    forall {A B: Type} (f: A -> option B) l x,
      In x (filter_map f l) <-> (exists y, Some x = f y /\ In y l).
  Proof.
    induction l; simpl; intros; eauto. split. tauto. intros (y & _ & []).
    destr; simpl; rewrite IHl.
    - split. intros [C | (y & EQ & IN)]. subst. eexists; split; eauto.
      eexists; split; eauto.
      intros (y & EQ & [IN|IN]); subst. left; congruence. right; eexists; split; eauto.
    - split; intros (y & EQ & IN); eauto.
      destruct IN as [IN|IN]; eauto. congruence.
  Qed.

  Lemma Forall_list_options:
    forall {A:Type} (P: A -> Prop) l,
      (forall x y,
          In x l ->
          x = Some y ->
          P y
      ) ->
      Forall P (filter_map id l).
  Proof.
    intros.
    rewrite Forall_forall. intros.
    rewrite filter_map_In in H0. destruct H0 as (y & EQ & IN). unfold id in EQ. subst.
    eauto.
  Qed.

  Lemma wf_rir_add_write0:
    forall rir n guard v idx rir' fail,
      wf_rir rir n ->
      valid_vars_uact guard n ->
      valid_vars_uact v n ->
      add_write0 rir guard idx v = (rir', fail) ->
      wf_rir rir' n /\ valid_vars_uact fail n.
  Proof.
    intros. inv H. unfold add_write0 in H2.
    repeat destr_in H2. inv H2.
    split. repeat (split; simpl; eauto).
    - intros i a IN.
      apply in_list_assoc_set_inv in IN. destruct IN; eauto.
      inv H. simpl. destr_in Heqp; inv Heqp; eauto.
      apply list_assoc_in in Heqo.
      destruct p; simpl in *. apply valid_vars_merge_failures; eauto.
      inv wf_rir_write0s0. eapply wf_wlr_glob_cond0 in Heqo; eauto.
      eapply wf_wlr_glob_cond in H; eauto.
    - intros i a IN.
      apply in_list_assoc_set_inv in IN. destruct IN; eauto.
      inv H. simpl. destr_in Heqp; inv Heqp; eauto.
      apply Forall_app; split; eauto.
      apply list_assoc_in in Heqo.
      destruct p; simpl in *. eapply wf_wlr_each_cond in Heqo; eauto.
      eapply wf_wlr_each_cond in H; eauto.
    - intros i a IN.
      apply in_list_assoc_set_inv in IN. destruct IN; eauto.
      inv H. simpl. destr_in Heqp; inv Heqp; eauto.
      apply Forall_app; split; eauto.
      apply list_assoc_in in Heqo.
      destruct p; simpl in *. eapply wf_wlr_each_act in Heqo; eauto.
      eapply wf_wlr_each_act in H; eauto.
    - apply valid_vars_and. auto.
      apply valid_vars_or_conds.
      apply Forall_list_options. simpl. intros. subst. unfold option_map in H.
      destruct H as [H|[H|[H|[]]]]; repeat destr_in H; inv H.
      + destruct p. apply list_assoc_in in Heqo.
        eapply wf_wlr_glob_cond in Heqo; eauto.
      + apply list_assoc_in in H3.
        eapply wf_rir_read1s0 in H3. auto.
      + destruct p. apply list_assoc_in in Heqo.
        eapply wf_wlr_glob_cond in Heqo; eauto.
  Qed.

  Lemma wf_rir_add_write1:
    forall rir n guard v idx rir' fail,
      wf_rir rir n ->
      valid_vars_uact guard n ->
      valid_vars_uact v n ->
      add_write1 rir guard idx v = (rir', fail) ->
      wf_rir rir' n /\ valid_vars_uact fail n.
  Proof.
    intros. inv H. unfold add_write1 in H2.
    repeat destr_in H2. inv H2.
    split. repeat (split; simpl; eauto).
    - intros i a IN.
      apply in_list_assoc_set_inv in IN. destruct IN; eauto.
      inv H. simpl. destr_in Heqp; inv Heqp; eauto.
      apply list_assoc_in in Heqo.
      destruct p; simpl in *. apply valid_vars_merge_failures; eauto.
      inv wf_rir_write1s0. eapply wf_wlr_glob_cond0 in Heqo; eauto.
      eapply wf_wlr_glob_cond in H; eauto.
    - intros i a IN.
      apply in_list_assoc_set_inv in IN. destruct IN; eauto.
      inv H. simpl. destr_in Heqp; inv Heqp; eauto.
      apply Forall_app; split; eauto.
      apply list_assoc_in in Heqo.
      destruct p; simpl in *. eapply wf_wlr_each_cond in Heqo; eauto.
      eapply wf_wlr_each_cond in H; eauto.
    - intros i a IN.
      apply in_list_assoc_set_inv in IN. destruct IN; eauto.
      inv H. simpl. destr_in Heqp; inv Heqp; eauto.
      apply Forall_app; split; eauto.
      apply list_assoc_in in Heqo.
      destruct p; simpl in *. eapply wf_wlr_each_act in Heqo; eauto.
      eapply wf_wlr_each_act in H; eauto.
    - apply valid_vars_and. auto.
      apply valid_vars_or_conds.
      apply Forall_list_options. simpl. intros. subst. unfold option_map in H.
      destruct H as [H|[]]; repeat destr_in H; inv H.
      destruct p. apply list_assoc_in in Heqo.
      eapply wf_wlr_glob_cond in Heqo; eauto.
  Qed.

  Lemma wf_rir_add_read0:
    forall rir n guard idx,
      wf_rir rir n ->
      valid_vars_uact guard n ->
      wf_rir (add_read0 rir guard idx) n.
  Proof.
    intros. inv H. unfold add_read0. split; simpl; eauto.
    intros.
    apply in_list_assoc_set_inv in H. destruct H.
    - inv H. destr; eauto.
      apply valid_vars_merge_failures; auto.
      apply list_assoc_in in Heqo. eauto.
    - eauto.
  Qed.
  Lemma wf_rir_add_read1:
    forall rir n guard idx,
      wf_rir rir n ->
      valid_vars_uact guard n ->
      wf_rir (add_read1 rir guard idx) n.
  Proof.
    intros. inv H. unfold add_read1. split; simpl; eauto.
    intros.
    apply in_list_assoc_set_inv in H. destruct H.
    - inv H. destr; eauto.
      apply valid_vars_merge_failures; auto.
      apply list_assoc_in in Heqo. eauto.
    - eauto.
  Qed.

  Lemma get_rule_information_aux_env_grows:
    forall (ua: uact)
           (env: list (string * string)) (guard: uact)
           (rir: rule_information_raw) (nid: nat)
           v env' vvs fail_cond rir' nid' vvs0
           (GRIA: get_rule_information_aux ua env vvs0 guard rir nid = (v, env', vvs, fail_cond, rir', nid'))
           (WUKV: wf_uact_known_vars (map fst env) ua)
           (ENVVVS: forall x y, In (x,y) env -> In y (map fst vvs0))
           (RNGVVS: vvs_range vvs0 nid)
           (VVSVALID: forall v a, In (v, a) vvs0 -> forall v' , var_in_uact a v' -> var_lt v' v)
           (RIRRNG: wf_rir rir nid)
           (GUARDVALID: valid_vars_uact guard nid),
      (forall x y, In (x,y) vvs0 -> In (x,y) vvs)
      /\ vvs_range vvs nid'
      /\ (forall x y, In (x,y) env' -> In y (map fst vvs))
      /\ (forall ext, In ext (rir_extcalls rir) -> In ext (rir_extcalls rir'))
      /\ (forall ov x, v = Some ov -> var_in_uact ov x ->
                       In x (map fst vvs) \/
                         exists ext, In ext (rir_extcalls rir') /\ ebind (snd ext) = x)
      /\ wf_rir rir' nid'
      /\ (forall v a, In (v, a) vvs -> forall v' , var_in_uact a v' -> var_lt v' v)
      /\ valid_vars_uact fail_cond nid'
      /\ nid <= nid'
  .
  Proof.
    intros ua; pattern ua; eapply daction_ind'; simpl; intros; eauto.
    all: repeat destr_in GRIA; inv GRIA; inv WUKV; eauto; try now (intuition congruence).
    - intuition try congruence. red; intros. inv H. lia.
    - intuition try congruence. red; intros. inv H. lia.
    - intuition try congruence.
      inv H. inv H0. apply list_assoc_in in Heqo. eauto.
      red; intros. inv H.
      lia.
    - intuition try congruence. red; intros. inv H. lia.
    - intuition try congruence. inv H. inv H0. red; intros. inv H. lia.
    - specialize (H _ _ _ _ _ _ _ _ _ _ _ Heqp H3 ENVVVS RNGVVS VVSVALID RIRRNG GUARDVALID).
      destruct H as (VVSGROWS & VVSRANGE & ENVVVS2 & EXTCALL2 & VAR2 & RIRLT2 & LT2 & VF2 & GUARDVALID2).
      repeat (refine (conj _ _)); eauto.
      + intros.
        rewrite list_assoc_set_not_before. eauto. intro IN.
        eapply vvs_range_in_fst in IN. 2: eauto. lia.
      + eapply vvs_range_list_assoc_set. eapply vvs_range_incr. 2: eauto. lia.
        red. eexists; split; eauto.
      + intros.
        apply in_list_assoc_set_inv in H.
        destruct H. inv H.
        eapply list_assoc_set_key_in; eauto.
        apply ENVVVS2 in H.
        eapply list_assoc_set_key_stays_in; eauto.
      + easy.
      + eapply wf_rir_incr; eauto.
      + intros.
        apply in_list_assoc_set_inv in H. destruct H; eauto.
        inv H.
        destruct o; simpl in H0; [| inv H0].
        eapply VAR2 in H0; eauto.
        eapply vss_or_extcall_var_lt in H0. eauto. auto. eauto.
      + eapply valid_var_uact_incr; eauto.
    - specialize (H0 _ _ _ _ _ _ _ _ _ _ _ Heqp4).
      specialize (H _ _ _ _ _ _ _ _ _ _ _ Heqp H4).
      generalize (get_rule_information_aux_same_vm _ _ _ _ _ _ _ _ _ _ _ _ H4 Heqp).
      generalize (fun wukv => get_rule_information_aux_same_vm _ _ _ _ _ _ _ _ _ _ _ _ wukv Heqp4).
      intros SVM2 SVM1.
      erewrite same_env_same_fst in H5. 2: eauto.
      specialize (SVM2 H5).
      specialize (H0 H5).
      specialize (H ENVVVS RNGVVS VVSVALID RIRRNG GUARDVALID).
      destruct H as (VVSGROWS1 & VVSRANGE1 & ENVVVS1 & EXTCALL1 & VAR1 & RIRRNG1 & VVSVALID1 & VF1 & GV1).
      specialize (H0 ENVVVS1 VVSRANGE1).
      destruct H0 as (VVSGROWS2 & VVSRANGE2 & ENVVVS2 & EXTCALL2 &  VAR2 & RIRRNG2 & VVSVALID2 & VF2 & GV2); eauto.
      2: repeat refine (conj _ _); eauto.
      eapply valid_var_uact_incr; eauto.

      red; intros. inv H. eapply VF1 in H6. eapply var_lt_gen_r; eauto.
      eauto.
      lia.

    - specialize (H0 _ _ _ _ _ _ _ _ _ _ _ Heqp4).
      specialize (H _ _ _ _ _ _ _ _ _ _ _ Heqp).
      generalize (get_rule_information_aux_same_vm _ _ _ _ _ _ _ _ _ _ _ _ H4 Heqp).
      generalize (fun wukv => get_rule_information_aux_same_vm _ _ _ _ _ _ _ _ _ _ _ _ wukv Heqp4). simpl.
      intros SVM2 SVM1.
      specialize (SVM2 H6). inv SVM2. simpl in H3. subst.
      simpl in *.
      change (skipn 1 (y::l')) with l'.
      specialize (H H4 ENVVVS RNGVVS VVSVALID RIRRNG).
      destruct H as (VVSGROWS1 & VVSRANGE1 & ENVVVS1 & EXTCALL1 & VAR1 & RIRRNG1 & VVSVALID1 & VF1 & GV1); eauto.
      specialize (H0 H6). destruct y; simpl in *.
      trim H0.
      {
        intros x y [A|A].
        - inv A.
          apply list_assoc_set_key_in.
        - eapply list_assoc_set_key_stays_in.
          apply ENVVVS in A. rewrite in_map_iff in A. destruct A as ((x0&x1) & EQ & A). simpl in EQ; subst.
          apply VVSGROWS1 in A.
          apply (in_map fst) in A. simpl in A; auto.
      }
      trim H0.
      apply vvs_range_list_assoc_set. eapply vvs_range_incr. 2: eauto. lia.
      red. eauto.
      destruct H0 as (VVSGROWS2 & VVSRANGE2 & ENVVVS2 & EXTCALL2 & VAR2 & RIRRNG2 & VVSVALID2 & VF2 & GV2).
      {
        intros v a IN.
        apply in_list_assoc_set_inv in IN. destruct IN as [IN|IN]; eauto.
        inv IN.
        intros v' VIU.
        destruct o; simpl in VIU; [| inv VIU].
        eapply VAR1 in VIU; eauto.
        eapply vss_or_extcall_var_lt in VIU. eauto. auto. eauto.
      }
      eapply wf_rir_incr; eauto.
      eapply valid_var_uact_incr; eauto.
      repeat (refine (conj _ _)); eauto.
      intros; eapply VVSGROWS2.
      apply VVSGROWS1 in H.
      rewrite list_assoc_set_not_before. auto.
      intro IN.
      eapply vvs_range_in_fst in IN. 2: eauto. lia.
      eapply valid_vars_merge_failures; eauto. eapply valid_var_uact_incr; eauto. lia. lia.
    -
      specialize (H _ _ _ _ _ _ _ _ _ _ _ Heqp H6 ENVVVS RNGVVS VVSVALID RIRRNG).
      destruct H as (VVSGROWS1 & VVSRANGE1 & ENVVVS1 & EXTCALL1 & VAR1 & RIRRNG1 & VVSVALID1 & VF1 & NIDGROWS1). eauto.
      generalize (get_rule_information_aux_same_vm _ _ _ _ _ _ _ _ _ _ _ _ H6 Heqp). intro SVM1.

      erewrite same_env_same_fst in H7; eauto.
      erewrite same_env_same_fst in H8; eauto.

      specialize (H0 _ _ _ _ _ _ _ _ _ _ _ Heqp4).
      destruct H0 as (VVSGROWS2 & VVSRANGE2 & ENVVVS2 & EXTCALL2 & VAR2 & RIRRNG2 & VVSVALID2 & VF2 & NIDGROWS2); eauto.
      {
        intros.
        apply list_assoc_set_key_stays_in.
        apply list_assoc_set_key_stays_in.
        apply list_assoc_set_key_stays_in. eauto.
      }
      {
        eapply vvs_range_list_assoc_set.
        eapply vvs_range_list_assoc_set.
        eapply vvs_range_list_assoc_set.
        eapply vvs_range_incr. 2: eauto. lia.
        red; eexists; split; eauto. lia.
        red; eexists; split; eauto. lia.
        red; eexists; split; eauto. lia.
      }
      {
        intros.
        apply in_list_assoc_set_inv in H. destruct H; eauto. inv H.
        inv H0. eapply GUARDVALID in H5. eapply var_lt_gen_r. 2: eauto. lia.
        inv H5. inv H3.
        do 2 eexists; repeat split; eauto. lia.
        apply in_list_assoc_set_inv in H. destruct H; eauto. inv H.
        inv H0. eapply GUARDVALID in H5. eapply var_lt_gen_r. 2: eauto. lia.
        inv H5.
        do 2 eexists; repeat split; eauto. lia.
        apply in_list_assoc_set_inv in H. destruct H; eauto. inv H.
        eapply VAR1 in H0; eauto.
        eapply vss_or_extcall_var_lt in H0. eauto. auto. eauto.
      }
      eapply wf_rir_incr; eauto. lia.
      {
        red; intros. inv H.
        do 2 eexists; repeat split; eauto. lia.
      }
      specialize (H1 _ _ _ _ _ _ _ _ _ _ _ Heqp9).
      destruct H1 as (VVSGROWS3 & VVSRANGE3 & ENVVVS3 & EXTCALL3 & VAR3 & RIRRNG3 & VVSVALID3 & VF3 & NIDGROWS3). auto.
      {
        intros.
        apply ENVVVS1 in H.
        rewrite in_map_iff in H. destruct H as ((s&a)&EQ & IN). simpl in EQ. subst.
        replace y with (fst (y, a)). eapply in_map. apply VVSGROWS2.
        rewrite list_assoc_set_not_before.
        rewrite list_assoc_set_not_before.
        rewrite list_assoc_set_not_before. auto.
        intro IN2; eapply vvs_range_in_fst in IN2; eauto. lia.
        intro IN2. apply in_map_list_assoc_set_inv in IN2.
        destruct IN2. apply generate_binding_name_inj in H. lia.
        eapply vvs_range_in_fst in H; eauto. lia.
        intro IN2. apply in_map_list_assoc_set_inv in IN2.
        destruct IN2. apply generate_binding_name_inj in H. lia.
        apply in_map_list_assoc_set_inv in H.
        destruct H. apply generate_binding_name_inj in H. lia.
        eapply vvs_range_in_fst in H; eauto. lia.
        reflexivity.
      }
      auto. auto. auto.
      {
        red; intros. inv H.
        do 2 eexists; repeat split; eauto. lia.
      }
      edestruct merge_banches_grows as (VVSGROWS4 & VVSRANGE4 & ENVVVS4 & NIDGROWS4 & VVSVALID4). eauto.
      {
        intros x y INl2.
        apply ENVVVS2 in INl2.
        rewrite in_map_iff in INl2. destruct INl2 as (xx & EQ & IN). subst. destruct xx.
        apply VVSGROWS3 in IN. apply in_map. auto.
      }
      auto. auto. auto.
      eexists; split; eauto. lia.
      repeat (refine (conj _ _)); auto.
      {
        intros. eapply VVSGROWS1 in H.
        eapply VVSGROWS4.
        eapply VVSGROWS3.
        eapply VVSGROWS2.
        rewrite ! list_assoc_set_not_before. auto.
        intro IN2; eapply vvs_range_in_fst in IN2; eauto. lia.
        intro IN2. apply in_map_list_assoc_set_inv in IN2.
        destruct IN2. apply generate_binding_name_inj in H0. lia.
        eapply vvs_range_in_fst in H0; eauto. lia.
        intro IN2. apply in_map_list_assoc_set_inv in IN2.
        destruct IN2. apply generate_binding_name_inj in H0. lia.
        apply in_map_list_assoc_set_inv in H0.
        destruct H0. apply generate_binding_name_inj in H0. lia.
        eapply vvs_range_in_fst in H0; eauto. lia.
      }
      {
        intros ov x EX.
        repeat destr_in EX; inv EX. intro VIU; inv VIU.
        + eapply VAR1 in H3; eauto. destruct H3; eauto. left.
          eapply incl_incl_map; eauto.
          eapply incl_incl_map; eauto.
          eapply incl_incl_map; eauto.
          repeat apply list_assoc_set_key_stays_in; auto.
          right; eauto.
          destruct H as (ext & IN & EQ).
          eexists; split; eauto.
        + eapply VAR3 in H3; eauto. destruct H3; eauto. left.
          eapply incl_incl_map; eauto.
        + eapply VAR2 in H3; eauto. destruct H3; eauto. left.
          eapply incl_incl_map; eauto.
          eapply incl_incl_map; eauto.
          destruct H as (ext & IN & EQ).
          right; eexists; split; eauto.
      }
      + eapply wf_rir_incr; eauto.
      + apply valid_vars_merge_failures.
        eapply valid_var_uact_incr. eauto. lia.
        apply valid_vars_merge_failures.
        apply valid_vars_and.
        red; intros.
        eapply VAR1 in H. eapply vss_or_extcall_var_lt in H; eauto.
        eapply vvs_range_incr. 2: eauto. lia.
        eapply wf_rir_incr; eauto. lia. auto.
        eapply valid_var_uact_incr. eauto. lia.
        apply valid_vars_and.
        apply valid_vars_not. 
        red; intros.
        eapply VAR1 in H. eapply vss_or_extcall_var_lt in H; eauto.
        eapply vvs_range_incr. 2: eauto. lia.
        eapply wf_rir_incr; eauto. lia. auto.
        eapply valid_var_uact_incr. eauto. lia.
      + lia.
    - specialize (H _ _ _ _ _ _ _ _ _ _ _ Heqp H6 ENVVVS RNGVVS).
      destruct H as (VVSGROWS1 & VVSRANGE1 & ENVVVS1 & EXTCALL1 & VAR1 & RIRRNG1 & VVSVALID1 & VF1 & NIDGROWS1). eauto. auto. auto.
      generalize (get_rule_information_aux_same_vm _ _ _ _ _ _ _ _ _ _ _ _ H6 Heqp). intro SVM1.

      erewrite same_env_same_fst in H7; eauto.
      erewrite same_env_same_fst in H8; eauto.

      specialize (H0 _ _ _ _ _ _ _ _ _ _ _ Heqp4).
      destruct H0 as (VVSGROWS2 & VVSRANGE2 & ENVVVS2 & EXTCALL2 & VAR2 & RIRRNG2 & VVSVALID2 & VF2 & NIDGROWS2); auto.
      {
        intros.
        apply list_assoc_set_key_stays_in.
        apply list_assoc_set_key_stays_in.
        apply list_assoc_set_key_stays_in. eauto.
      }
      {
        eapply vvs_range_list_assoc_set.
        eapply vvs_range_list_assoc_set.
        eapply vvs_range_list_assoc_set.
        eapply vvs_range_incr. 2: eauto. lia.
        red; eexists; split; eauto. lia.
        red; eexists; split; eauto. lia.
        red; eexists; split; eauto. lia.
      }
      {
        intros.
        apply in_list_assoc_set_inv in H. destruct H; eauto. inv H.
        inv H0. eapply GUARDVALID in H5. eapply var_lt_gen_r. 2: eauto. lia.
        inv H5. inv H3.
        do 2 eexists; repeat split; eauto. lia.
        apply in_list_assoc_set_inv in H. destruct H; eauto. inv H.
        inv H0. eapply GUARDVALID in H5. eapply var_lt_gen_r. 2: eauto. lia.
        inv H5.
        do 2 eexists; repeat split; eauto. lia.
        apply in_list_assoc_set_inv in H. destruct H; eauto. inv H.
        inv H0.
      }
      eapply wf_rir_incr; eauto. lia.
      {
        red; intros. inv H.
        do 2 eexists; repeat split; eauto. lia.
      }
      specialize (H1 _ _ _ _ _ _ _ _ _ _ _ Heqp9).
      destruct H1 as (VVSGROWS3 & VVSRANGE3 & ENVVVS3 & EXTCALL3 & VAR3 & RIRRNG3 & VVSVALID3 & VF3 & NIDGROWS3); auto.
      {
        intros.
        apply ENVVVS1 in H.
        rewrite in_map_iff in H. destruct H as ((s&a)&EQ & IN). simpl in EQ. subst.
        replace y with (fst (y, a)). eapply in_map. apply VVSGROWS2.
        rewrite list_assoc_set_not_before.
        rewrite list_assoc_set_not_before.
        rewrite list_assoc_set_not_before. auto.
        intro IN2; eapply vvs_range_in_fst in IN2; eauto. lia.
        intro IN2. apply in_map_list_assoc_set_inv in IN2.
        destruct IN2. apply generate_binding_name_inj in H. lia.
        eapply vvs_range_in_fst in H; eauto. lia.
        intro IN2. apply in_map_list_assoc_set_inv in IN2.
        destruct IN2. apply generate_binding_name_inj in H. lia.
        apply in_map_list_assoc_set_inv in H.
        destruct H. apply generate_binding_name_inj in H. lia.
        eapply vvs_range_in_fst in H; eauto. lia.
        reflexivity.
      }
      {
        red; intros.
        inv H.
        do 2 eexists; repeat split; eauto. lia.
      }
      edestruct merge_banches_grows as (VVSGROWS4 & VVSRANGE4 & ENVVVS4 & NIDGROWS4 & VVSVALID4); eauto.
      {
        intros x y INl2.
        apply ENVVVS2 in INl2.
        rewrite in_map_iff in INl2. destruct INl2 as (xx & EQ & IN). subst. destruct xx.
        apply VVSGROWS3 in IN. apply in_map. auto.
      }
      {
        eexists; split; eauto. lia.
      }
      repeat (refine (conj _ _)); eauto.
      {
        intros. eapply VVSGROWS1 in H.
        eapply VVSGROWS4.
        eapply VVSGROWS3.
        eapply VVSGROWS2.
        rewrite ! list_assoc_set_not_before. auto.
        intro IN2; eapply vvs_range_in_fst in IN2; eauto. lia.
        intro IN2. apply in_map_list_assoc_set_inv in IN2.
        destruct IN2. apply generate_binding_name_inj in H0. lia.
        eapply vvs_range_in_fst in H0; eauto. lia.
        intro IN2. apply in_map_list_assoc_set_inv in IN2.
        destruct IN2. apply generate_binding_name_inj in H0. lia.
        apply in_map_list_assoc_set_inv in H0.
        destruct H0. apply generate_binding_name_inj in H0. lia.
        eapply vvs_range_in_fst in H0; eauto. lia.
      }
      easy.
      eapply wf_rir_incr; eauto.
      red; intros. inv H.
      lia.
    - repeat (refine (conj _ _)); eauto. intros. inv H. inv H0.
      eapply wf_rir_add_read0; eauto.
      red; intros; inv H.
    - repeat (refine (conj _ _)); eauto. intros. inv H. inv H0.
      eapply wf_rir_add_read1; eauto. red; intros; inv H.
    - specialize (H _ _ _ _ _ _ _ _ _ _ _ Heqp H2 ENVVVS RNGVVS).
      destruct H as (VVSGROWS1 & VVSRANGE1 & ENVVVS1 & EXTCALL1 & VAR1 & RIRRNG1 & VVSVALID1 & VF1 & NIDGROWS1 ); eauto.
      assert (valid_vars_uact guard nid'). eapply valid_var_uact_incr; eauto.
      assert (valid_vars_uact (reduce o) nid').
      destruct o; simpl.
      red; intros. eapply VAR1 in H0. eapply vss_or_extcall_var_lt in H0; eauto. auto.
      red; intros; inv H0.
      assert (wf_rir rir' nid' /\ valid_vars_uact u0 nid').
      {
        destr_in Heqp4; [eapply wf_rir_add_write0 in Heqp4 | eapply wf_rir_add_write1 in Heqp4]; eauto.
      }
      destruct H1.
      repeat (refine (conj _ _)); eauto. 2: easy.
      unfold add_write0, add_write1 in Heqp4;
        repeat destr_in Heqp4; inv Heqp4; simpl; eauto.
      apply valid_vars_merge_failures; auto.

    - specialize (H _ _ _ _ _ _ _ _ _ _ _ Heqp H2 ENVVVS RNGVVS).
      destruct H as (VVSGROWS1 & VVSRANGE1 & ENVVVS1 & EXTCALL1 & VAR1 & RIRRNG1 & VVSVALID1 & VF1 & NIDGROWS1); eauto.
      repeat (refine (conj _ _)); eauto. intros. inv H. inv H0.
      destruct o. 2: inv H4. simpl in H4.
      eapply VAR1 in H4; eauto.
    - specialize (H _ _ _ _ _ _ _ _ _ _ _ Heqp H4 ENVVVS RNGVVS).
      destruct H as (VVSGROWS1 & VVSRANGE1 & ENVVVS1 & EXTCALL1 & VAR1 & RIRRNG1 & VVSVALID1 & VF1 & NIDGROWS1); eauto.
      generalize (get_rule_information_aux_same_vm _ _ _ _ _ _ _ _ _ _ _ _ H4 Heqp). intro SVM1.
      erewrite same_env_same_fst in H6; eauto.
      specialize (H0 _ _ _ _ _ _ _ _ _ _ _ Heqp4 H6).
      destruct H0 as (VVSGROWS2 & VVSRANGE2 & ENVVVS2 & EXTCALL2 & VAR2 & RIRRNG2 & VVSVALID2 & VF2 & NIDGROWS2); eauto.
      {
        intros v VARINGUARD. apply GUARDVALID in VARINGUARD.
        eapply var_lt_gen_r. 2: eauto. lia.
      }
      repeat (refine (conj _ _)); eauto.
      intros. inv H. inv H0.
      destruct o. 2: inv H5. simpl in H5.
      eapply VAR1 in H5; eauto. destruct H5. left.
      eapply incl_incl_map; eauto. decompose [ex and] H; right; eexists; split; eauto.
      destruct o0. 2: inv H5. simpl in H5.
      eapply VAR2 in H5; eauto.
      apply valid_vars_merge_failures; auto. eapply valid_var_uact_incr; eauto. lia.
    - specialize (H _ _ _ _ _ _ _ _ _ _ _ Heqp H2 ENVVVS RNGVVS).
      destruct H as (VVSGROWS1 & VVSRANGE1 & ENVVVS1 & EXTCALL1 & VAR1 & RIRRNG1 & VVSVALID1 & VF1 & NIDGROWS1); eauto.
      repeat refine (conj _ _); eauto.
      eapply vvs_range_incr. 2: eauto. lia.
      unfold add_extcall. simpl. eauto.
      intros. inv H. inv H0. right.
      unfold add_extcall; eexists; split; eauto.
      simpl. left; reflexivity. reflexivity.

      Lemma wf_rir_add_extcall:
        forall rir guard ufn arg n,
          wf_rir rir n ->
          valid_vars_uact guard n ->
          valid_vars_uact arg n ->
          wf_rir (add_extcall rir guard ufn arg (generate_binding_name n)) (S n).
      Proof.
        intros rir guard ufn arg n WR VG VA.
        unfold add_extcall; simpl.
        inv WR; split; simpl; eauto using valid_var_uact_incr, wf_write_log_raw_incr.
        intros i ext [EQ|IN]; eauto using wf_extcall_info_incr.
        inv EQ. constructor; simpl; eauto using valid_var_uact_incr.
        do 2 eexists; repeat split; eauto.
      Qed.
      eapply wf_rir_add_extcall; eauto using wf_rir_incr.
      eapply valid_var_uact_incr; eauto.
      destruct o; simpl.
      red; intros. eapply VAR1 in H. eapply vss_or_extcall_var_lt in H; eauto. auto.
      red; intros; inv H.
      eapply valid_var_uact_incr; eauto.
    -  
      eapply gria_list_grows with
        (I:= fun env vvs nid rir guard =>
               (forall x y : string, In (x, y) env -> In y (map fst vvs))
               /\ vvs_range vvs nid
               /\ (forall x y, In (x, y) vvs -> forall v, var_in_uact y v -> var_lt v x)
               /\ wf_rir rir nid
               /\ valid_vars_uact guard nid
        )
        (P:= fun env vvs nid rir env' vvs' nid' rir' =>
               Forall2 (fun x y => fst x = fst y) env env'
               /\ (forall (x : string) (y : uact), In (x, y) vvs -> In (x, y) vvs')
               /\ (forall ext, In ext (rir_extcalls rir) -> In ext (rir_extcalls rir'))
               (* /\ nid <= nid' *)
         ) in Heqp.
      7: {
        eapply Forall_impl.
        2: apply H0. simpl; intros. decompose [and] H8. clear H8.
        generalize (get_rule_information_aux_same_vm _ _ _ _ _ _ _ _ _ _ _ _ H4 H2). intro SVM1.
        eapply H1 in H2; eauto. intuition eauto.
        - eapply valid_var_uact_incr; eauto.
        - red; intros.
          eapply H16 in H22; eauto.
          eapply var_lt_gen_r. 2: eapply vss_or_extcall_var_lt in H22; eauto. lia.
        - eapply valid_var_uact_incr; eauto.
      }
      destruct Heqp as ((SAMEENV1 & (VVSGROWS1 & EXTGROWS1)) & ((ENVVVS1 & VVSRANGE1 & VVSVALID1 & RIRRNG1 & GUARDVALID1) & (NAMES & LENNAMES & VF1 & NID1))).
      2: {
        simpl. split. apply same_env_refl. auto.
      }
      2: {
        simpl; intros; eauto.
        decompose [and] H1; clear H1.
        decompose [and] H2; clear H2.
        decompose [and] H4; clear H4.
        decompose [and] H7; clear H7.
        repeat split; eauto.
        eapply same_env_trans; eauto. congruence.
      }
      2: {
        intros. destruct H1.
        erewrite <- same_env_same_fst; eauto.
      }
      2: {
        intuition.
        - apply same_env_refl.
        - rewrite list_assoc_set_not_before. auto.
          intro IN2; eapply vvs_range_in_fst in IN2; eauto. lia.
        - apply list_assoc_set_key_stays_in. eauto.
        - eapply vvs_range_list_assoc_set. eapply vvs_range_incr. 2: eauto. lia.
          eexists; split; eauto.
        - apply in_list_assoc_set_inv in H9; destruct H9 as [EQ|IN].
          inv EQ. eapply var_lt_gen_r. 2: eauto. lia. eauto.
        - eapply wf_rir_incr; eauto.
        - eapply valid_var_uact_incr; eauto.
      }
      2:{
        simpl; intros. intuition; eauto.
        rewrite in_map_iff in H4. decompose [ex and] H4. clear H4; subst. destruct x0.
        apply in_map. eauto.
      }
      2: now auto.
      2: now (eapply valid_var_uact_incr; eauto).
      2: red; now inversion 1.
      2: now split; auto.
      2: constructor.

      clear H0.
      simpl in LENNAMES.
      specialize (H _ _ _ _ _ _ _ _ _ _ _ Heqp4).
      rewrite map_fst_combine in H.
      rewrite fst_split_map in H. 
      destruct H as (VVSGROWS2 & VVSRANGE2 & ENVVVS2 & EXTGROWS2 & VAR2 & RIR2 & VVSVALID2 & FV2 & NID2); auto.
      intros x y IN; apply in_combine_r in IN.
      rewrite Forall_forall in NAMES; apply NAMES in IN. auto.
      repeat refine(conj _ _); eauto.
      + intros x y IN; apply ENVVVS1 in IN.
        rewrite in_map_iff in IN. decompose [ex and] IN. clear IN; subst. destruct x0.
        apply in_map. eauto.
      + eapply valid_vars_merge_failures; eauto using valid_var_uact_incr.
      + lia.
      + rewrite fst_split_map. setoid_rewrite H5. congruence.
  Qed.

  (* Fixpoint read_from_rirs *)
  (*          (REnv: Env reg_t) *)
  (*          (r: env_t REnv (fun _ => val)) *)
  (*          (rir: rule_information_raw) *)
  (*          (prt: Port) (idx: reg_t) : val := *)
  (*   match prt with *)
  (*   | P0 => getenv REnv r idx *)
  (*   | P1 => *)
  (*       match list_assoc (rir_writes0s rir) idx with *)
  (*         None => getenv REnv r idx *)
  (*       | Some (_, wil) => *)

  (*       end *)
  (*   end *)
  (* . *)

  (* Fixpoint interp_uact_with_fake_vars *)
  (*          (u: uact) *)
  (*          (vvs: list (string * uact)) *)
  (*          (REnv: Env reg_t) *)
  (*          (r: env_t REnv (fun _ => val)) *)
  (*          (rirs: list rule_information_raw) *)
  (*   : option val := *)
  (*   match u with *)
  (*   | DVar var => None          (* TODO *) *)
  (*   | DRead port idx => *)
  (*       None *)
  (*   | DConst cst => Some (BitsToLists.val_of_value cst) *)
  (*   | DIf cond tbranch fbranch => *)
  (*       let/opt c := interp_uact_with_fake_vars cond vvs in *)
  (*       match c with *)
  (*       | Bits _ [true] => interp_uact_with_fake_vars tbranch vvs *)
  (*       | Bits _ [false] => interp_uact_with_fake_vars tbranch vvs *)
  (*       | _ => None *)
  (*       end *)
  (*   | DUnop ufn1 arg1 => *)
  (*       let/opt v := interp_uact_with_fake_vars arg1 vvs in *)
  (*       UntypedSemantics.sigma1 ufn1 v *)
  (*   | DBinop ufn2 arg1 arg2 => *)
  (*       let/opt v1 := interp_uact_with_fake_vars arg1 vvs in *)
  (*       let/opt v2 := interp_uact_with_fake_vars arg2 vvs in *)
  (*       UntypedSemantics.sigma2 ufn2 v1 v2 *)
  (*   | DError _ *)
  (*   | DFail _ *)
  (*   | DAssign _ _ *)
  (*   | DSeq _ _ *)
  (*   | DBind _ _ _ *)
  (*   | DWrite _ _ _ *)
  (*   | DExternalCall _ _ *)
  (*   | DInternalCall _ _ *)
  (*   | DAPos _ _ => None *)
  (*   end. *)


  (* Lemma get_rule_information_aux_act: *)
  (*   forall *)
  (*     (R: reg_t -> type) *)
  (*     (Sigma: ext_fn_t -> ExternalSignature) *)
  (*     (ua: uact) (env: list (string * string)) (guard: uact) *)
  (*     (rir: rule_information_raw) (nid: next_ids) *)
  (*     v env' vvs fail_cond rir' nid' *)
  (*     sig t *)
  (*     (GRIA: get_rule_information_aux ua env guard rir nid = (v, env', vvs, fail_cond, rir', nid')) *)
  (*     (TA: forall p, exists tcr, *)
  (*         TypeInference.tc_action R Sigma p sig t ua = Success tcr) *)
  (*     Gamma sched_log action_log action_log' v' Gamma' *)
  (*     (REnv: Env reg_t) *)
  (*     (r: env_t REnv (fun _ => val)) *)
  (*     (sigma: ext_fn_t -> val -> val) *)
  (*     (IA: UntypedSemantics.interp_action *)
  (*            r sigma Gamma *)
  (*            sched_log action_log ua = Some (action_log', v', Gamma')), *)
  (*     interp_uact_with_fake_vars v vvs = Some v'. *)



      

  Record rule_information_raw_ok (r: rule_information_raw) (ua: uact) :=
    {
      rir_read0s_ok:
      forall reg ua', In (reg, ua') (rir_read0s r) ->
                     False;
     
      (* ... *)
    }.


  Lemma get_rule_information_raw_aux:
    forall
      (ua: uact) (env: list (string * string)) (guard: uact)
      (rir: rule_information_raw) (nid: nat)
      v env' vvs0 vvs fail_cond rir' nid',
      get_rule_information_aux ua env vvs0 guard rir nid = (Some v, env', vvs, fail_cond, rir', nid') ->
      rule_information_raw_ok rir ua ->
      rule_information_raw_ok rir' ua.

  Definition get_rule_information (ua: uact) (nid: nat)
  : rule_information_raw * nat :=
    let '(_, _, vvm, failure, rule_information_raw, nid') :=
      get_rule_information_aux
        ua [] [] const_true
        {| rir_read0s := []; rir_read1s := []; rir_write0s := [];
           rir_write1s := []; rir_extcalls := []; rir_vars := [];
           rir_failure_cond := None |}
        nid
    in (
      rule_information_raw <| rir_failure_cond := Some failure |>
        <| rir_vars := vvm|>,
      nid').

  Lemma get_rule_information_ok:
    forall ua ni r ni',
      get_rule_information ua ni = (r, ni') ->
      rule_information_raw_ok r ua.
  Proof.
  Admitted.

  (* * Scheduling conflicts detection *)
  (* It is here that we take into account how a rule might cancel any later
     rule. *)
  (* ** Conflicts between two rules *)
  (* rir_failure_cond rir is used in detect_conflicts only so as to keep things
     nicely factored. *)
  Definition detect_conflicts_step
    (acc: option uact) (rir: rule_information_raw) (cond: uact) (reg: reg_t)
    (reg_failure_detection:
      rule_information_raw -> uact -> reg_t -> option uact)
    : option uact :=
    (* reg_failure_detection rir cond reg && acc *)
    match reg_failure_detection rir cond reg with
    | None => acc
    | Some x =>
      match acc with
      | None => Some x
      | Some y => Some (uand x y)
      end
    end.

  (* The following functions are meant to be passed as arguments to
     detect_conflicts_step. *)
  Definition detect_conflicts_read0s_reg
    (rir: rule_information_raw) (cond: uact) (reg: reg_t)
  : uact :=
    let prev_wr0 := option_map fst (list_assoc (rir_write0s rir) reg) in
    let prev_wr1 := option_map fst (list_assoc (rir_write1s rir) reg) in
    merge_failures_list cond (list_options_to_list [prev_wr0; prev_wr1]).
  Definition detect_conflicts_write0s_reg
    (rir: rule_information_raw) (cond: uact) (reg: reg_t)
  : uact :=
    let prev_wr0 := option_map fst (list_assoc (rir_write0s rir) reg) in
    let prev_rd1 := list_assoc (rir_read1s rir) reg in
    let prev_wr1 := option_map fst (list_assoc (rir_write1s rir) reg) in
    merge_failures_list
      cond (list_options_to_list [prev_wr0; prev_wr1; prev_rd1]).
  Definition detect_conflicts_read1s_reg
    (rir: rule_information_raw) (cond: uact) (reg: reg_t)
  : uact :=
    let prev_wr1 := option_map fst (list_assoc (rir_write1s rir) reg) in
    merge_failures_list cond (list_options_to_list [prev_wr1]).
  Definition detect_conflicts_write1s_reg
    (rir: rule_information_raw) (cond: uact) (reg: reg_t)
  : uact :=
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
      (fun acc '(reg, (ua,lwi)) =>
        detect_conflicts_step acc rir ua reg detect_conflicts_write0s_reg)
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
      (fun acc '(reg, (ua, lwi)) =>
        detect_conflicts_step acc rir ua reg detect_conflicts_write1s_reg)
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
           Some (DBinop (PrimUntyped.UBits2 PrimUntyped.UAnd) not_failure_1 x)
         end
       end).

  (* ** Conflicts with any prior rule *)
  Definition detect_conflicts_any_prior
    (r: rule_information_raw) (prior_rules: list rule_information_raw)
  : rule_information_raw :=
    fold_left
      (fun r' p => r' <| rir_failure_cond := detect_conflicts p r' |>)
      prior_rules r.


  Definition clean_rule_information (r: rule_information_raw) :
      rule_information_clean :=
    {|
      ric_write0s := map (fun '(a, (_, b)) => (a, b)) (rir_write0s r);
      ric_write1s := map (fun '(a, (_, b)) => (a, b)) (rir_write1s r);
      ric_extcalls := rir_extcalls r;
      ric_vars := rir_vars r;
      ric_failure_cond := rir_failure_cond r
    |}.


  Record rule_information_clean_ok (r: rule_information_clean) (ua: uact) :=
    {
      (* ... *)
    }.

  Lemma clean_rule_information_ok:
    forall ua r,
      rule_information_raw_ok r ua ->
      rule_information_clean_ok (clean_rule_information r) ua.
  Proof.
  Admitted.


  (* ** All scheduling conflicts *)
  (* This function detects all the scheduling conflicts. It returns a list of
     rule_information where the failure conditions have been edited
     appropriately. *)
  Definition detect_all_conflicts (rl: list rule_information_raw)
  : list rule_information_clean :=
    let raw := fold_left
      (fun acc c => acc ++ [detect_conflicts_any_prior c acc])
      rl []
    in
    (* TODO: PROVE STUFF HERE *)
    map clean_rule_information raw.

  (* * Schedule merger *)
  (* Starting from a schedule with all the right failures conditions under the
     form of a list of rule_information structures, we want to get to a
     schedule_information structure (which is a collection of actions with no
     failure condition, as a schedule can't fail). *)
  (* ** Integrate failure conditions into actions *)
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
          econd := DBinop (PrimUntyped.UBits2 PrimUntyped.UAnd) cond (econd ei);
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

  (* ** Merge duplicated actions across rules *)
  (* *** Merge one rule *)
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

  (* *** Merge full schedule *)
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

  (* * Final simplifications *)
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
    | DBinop ufn a1 a2 => app_uniq (find_all_ua_regs a1) (find_all_ua_regs a2)
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

  (* ** Remove read1s *)
  (* *** Replacement of variables by expression *)
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
    | DBinop ufn a1 a2 =>
      DBinop
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

  (* *** Removal *)
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

  (* ** Remove write0s *)
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

  (* * Conversion *)
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
        (fun '(rir_acc, nid') r =>
          let '(ri, nid'') := get_rule_information r nid' in
          (rir_acc++[ri], nid''))
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
