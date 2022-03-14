(*! Proving | Transformation of a schedule into a proof-friendly form !*)
Require Import Coq.Numbers.DecimalString Coq.Program.Equality Coq.Strings.Ascii.
Require Import Koika.Primitives Koika.Syntax.
From RecordUpdate Require Import RecordSet.
Import RecordSetNotations.
Require Import Sact.
Require Import BitsToLists.
Require Export SimpleForm.

Fixpoint list_assocb {K V: Type} (beq_dec: K -> K -> bool) (l: list (K * V)) (k: K)
  : option V :=
  match l with
  | [] => None
  | (k1,v1)::l => if beq_dec k k1 then Some v1 else list_assocb beq_dec l k
  end.

Fixpoint list_assoc_setb
         {K V: Type} (beq_dec: K -> K -> bool) (l: list (K * V)) (k: K) (v: V)
  : list (K * V) :=
  match l with
  | [] => [(k,v)]
  | (k1,v1)::l =>
      if beq_dec k k1 then (k1,v)::l else (k1,v1) :: list_assoc_setb beq_dec l k v
  end.

Lemma list_assocb_eq:
  forall {K V: Type} {eq: EqDec K} beq_dec
         (BEQ: forall k1 k2, reflect (k1 = k2) (beq_dec k1 k2))
         (l: list (K * V)) (k: K),
    list_assoc l k = list_assocb beq_dec l k.
Proof.
  induction l; simpl; intros; eauto.
  destr.
  specialize (BEQ k k0). destr. inv BEQ. auto. congruence.
  inv BEQ. congruence. eauto.
Qed.

Lemma list_assoc_setb_eq:
  forall {K V: Type} {eq: EqDec K} beq_dec
         (BEQ: forall k1 k2, reflect (k1 = k2) (beq_dec k1 k2))
         (l: list (K * V)) (k: K) v,
    list_assoc_set l k v = list_assoc_setb beq_dec l k v.
Proof.
  induction l; simpl; intros; eauto.
  destr.
  specialize (BEQ k k0). destr; inv BEQ; try congruence.
Qed.

Definition list_assoc_modifyb {K V: Type} eqb
           (l: (list (K*V)))
           k vdef (f: V -> V) :=
  let newv :=
    match list_assocb eqb l k with
    | None => vdef
    | Some v => f v
    end in
  list_assoc_setb eqb l k newv.

Lemma list_assoc_modifyb_eq:
  forall {K V: Type} {eq: EqDec K} beq_dec
         (BEQ: forall k1 k2, reflect (k1 = k2) (beq_dec k1 k2))
         (l: list (K * V)) (k: K) v f,
    list_assoc_modify l k v f = list_assoc_modifyb beq_dec l k v f.
Proof.
  unfold list_assoc_modify, list_assoc_modifyb. intros.
  rewrite <- list_assocb_eq; auto.
  rewrite <- list_assoc_setb_eq; auto.
Qed.

Existing Instance etaRuleInformationRaw.

Open Scope nat.
Section SimpleFormb.
  Context {pos_t reg_t ext_fn_t rule_name_t: Type}.

  Variable reg_eqb: reg_t -> reg_t -> bool.
  Hypothesis reg_eqb_correct: forall r1 r2, reflect (r1 = r2) (reg_eqb r1 r2).
  Variable ext_fn_eqb: ext_fn_t -> ext_fn_t -> bool.
  Hypothesis ext_fn_eqb_correct: forall r1 r2, reflect (r1 = r2) (ext_fn_eqb r1 r2).

  Definition port_eqb (p1 p2: Port) : bool :=
    match p1, p2 with
    | P0, P0
    | P1, P1 => true
    | _, _ => false
    end.

  Lemma reflect_port_eqb: forall p1 p2, reflect (p1=p2) (port_eqb p1 p2).
  Proof.
    intros p1 p2.
    destruct p1, p2; simpl; constructor; congruence.
  Qed.

  Definition port_unit_eqb (p1 p2: Port + unit) : bool :=
    match p1, p2 with
    | inl p1, inl p2 => port_eqb p1 p2
    | inr _, inr _ => true
    | _, _ => false
    end.

  Lemma reflect_port_unit_eqb: forall p1 p2, reflect (p1=p2) (port_unit_eqb p1 p2).
  Proof.
    intros p1 p2.
    destruct p1, p2; simpl; try (constructor; congruence).
    destruct (reflect_port_eqb p p0); constructor; congruence.
    constructor. destruct u, u0; auto.
  Qed.

  Definition reg_port_unit_eqb (rp1 rp2: reg_t * (Port + unit)) : bool :=
    reg_eqb (fst rp1) (fst rp2) && port_unit_eqb (snd rp1) (snd rp2).

  Lemma reflect_reg_port_unit_eqb: forall p1 p2, reflect (p1=p2) (reg_port_unit_eqb p1 p2).
  Proof.
    intros (r1&p1) (r2&p2). unfold reg_port_unit_eqb.
    simpl.
    generalize (reg_eqb_correct r1 r2) (reflect_port_unit_eqb p1 p2).
    intros A B. inv A; inv B; simpl; constructor; congruence.
  Qed.

  Variable REnv : Env reg_t.
  Variable r : env_t REnv (fun _ => val).
  Context {sigma : ext_fn_t -> val -> val}.
  Variable R: reg_t -> type.
  Context {Sigma: ext_fn_t -> ExternalSignature}.

  Context {wt_sigma: forall ufn vc,
      wt_val (arg1Sig (Sigma ufn)) vc ->
      wt_val (retSig (Sigma ufn)) (sigma ufn vc)}.

  Definition sact := sact (ext_fn_t:=ext_fn_t).

  Definition rir_has_write0b rir reg : sact :=
    match list_assocb reg_eqb (rir_write0s rir) reg with
      None => const_false
    | Some gcond => gcond
    end.
  Definition rir_has_write1b rir reg : sact :=
    match list_assocb reg_eqb(rir_write1s rir) reg with
      None => const_false
    | Some gcond => gcond
    end.
  Definition rir_has_read0b rir reg : sact :=
    match list_assocb reg_eqb(rir_read0s rir) reg with
      None => const_false
    | Some (gcond) => gcond
    end.
  Definition rir_has_read1b rir reg : sact :=
    match list_assocb reg_eqb(rir_read1s rir) reg with
      None => const_false
    | Some (gcond) => gcond
    end.

  Definition add_read0b (rir: rule_information_raw) (grd: sact) (reg: reg_t)
    : rule_information_raw :=
    let new_grd :=
      match list_assocb reg_eqb (rir_read0s rir) reg with
      | None => grd
      | Some cond' => uor cond' grd
      end in
    rir <| rir_read0s := list_assoc_setb reg_eqb (rir_read0s rir) reg new_grd |>.

  Definition add_read1b (rir: rule_information_raw) (grd: sact) (reg: reg_t)
    : rule_information_raw :=
    let new_grd :=
      match list_assocb reg_eqb (rir_read1s rir) reg with
      | None => grd
      | Some cond' => uor cond' grd
      end in
    rir <| rir_read1s := list_assoc_setb reg_eqb (rir_read1s rir) reg new_grd |>.

  Definition add_write0b
             (sched_rir: rule_information_raw)
             (rir: rule_information_raw) (grd: sact) (reg: reg_t) (v:sact)
    (* Returns modified rule_information_raw, failure conditions *)
    : rule_information_raw * sact :=
    let new_grd :=
      match list_assocb reg_eqb (rir_write0s rir) reg with
      | None => grd
      | Some c => uor c grd
      end in
    ((rir <| rir_write0s := list_assoc_setb reg_eqb (rir_write0s rir) reg new_grd |>),
      merge_failures_list grd
                          ([rir_has_write0b rir reg;
                            rir_has_read1b rir reg;
                            rir_has_write1b rir reg;
                            rir_has_write0b sched_rir reg;
                            rir_has_read1b sched_rir reg;
                            rir_has_write1b sched_rir reg]
           )
    ).

  Definition add_write1b
             sched_rir
             (rir: rule_information_raw) (grd: sact) (reg: reg_t) (v:sact)
    : rule_information_raw * sact :=
    let new_grd :=
      match list_assocb reg_eqb(rir_write1s rir) reg with
      | None => grd
      | Some c => uor c grd
      end in
    ((rir <| rir_write1s := list_assoc_setb reg_eqb (rir_write1s rir) reg new_grd |>),
      merge_failures_list grd [rir_has_write1b rir reg; rir_has_write1b sched_rir reg]).

  Fixpoint merge_branchesb
           (vm_tb vm_fb: list (string*nat))
           (vvs: list (nat * (type * sact)))
           (nid: nat)
           (cond_name: nat) :=
    match vm_tb, vm_fb with
    | (str, n1)::vm_tb, (_, n2)::vm_fb =>
        let '(acc, vv', nid) := merge_branchesb vm_tb vm_fb vvs nid cond_name in
        if eq_nat_dec n1 n2
        then ((str, n1)::acc, vv', nid)
        else
          let t :=
            match list_assocb Nat.eqb vvs n1 with
            | Some (t, _) => t
            | None => bits_t 0
            end in
          ((str, nid)::acc,
            list_assoc_setb Nat.eqb vv' nid (t, SIf (SVar cond_name) (SVar n1) (SVar n2)),
            S nid)
    | _, _ => ([], vvs, nid)
    end.


  Definition merge_reg2vars_regb (r1 r2: r2vtype) reg prt cond_name r
             (vvs:list (nat * (type * sact))) nid :=
    match list_assocb reg_port_unit_eqb r1 (reg,prt), list_assocb reg_port_unit_eqb r2 (reg,prt) with
    | Some v1, Some v2 =>
        if eq_nat_dec v1 v2 then (list_assoc_setb reg_port_unit_eqb r (reg,prt) v1, vvs, nid)
        else
          let t :=
            match list_assocb Nat.eqb vvs v1 with
            | Some (t, _) => t
            | None => bits_t 0
            end in
          (list_assoc_setb reg_port_unit_eqb r (reg,prt) nid,
            list_assoc_setb Nat.eqb vvs nid (t, SIf (SVar cond_name) (SVar v1) (SVar v2)),
            S nid)
    | _, _ => (r, vvs, nid)
    end.

  Fixpoint merge_reg2vars_auxb ks (r1 r2: r2vtype) r cond_name vvs nid :=
    match ks with
    | [] => (r, vvs, nid)
    | (reg,prt)::ks =>
        let '(r, vvs, nid) := merge_reg2vars_regb r1 r2 reg prt cond_name r vvs nid in
        merge_reg2vars_auxb ks r1 r2 r cond_name vvs nid
    end.

  Definition merge_reg2varsb (r1 r2: r2vtype) cond_name vvs nid :=
    let keys := List.map fst r1 in
    merge_reg2vars_auxb keys r1 r2 [] cond_name vvs nid.

  Definition gria_listb
             (guard: sact)
             (rec: uact (pos_t:=pos_t) (reg_t:=reg_t) (ext_fn_t:=ext_fn_t) -> (list (string * type)) -> list (string * nat) ->
                   r2vtype -> list(nat * (type*sact)) ->
                   sact -> rule_information_raw -> rule_information_raw -> nat ->
                   (option sact * list (string * nat) * r2vtype * list (nat * (type * sact)) * sact * rule_information_raw * nat * type))
    :=
    fix gria_listb
        (args: list _)
        (tsig: list (string * type))
        (env: list (string * nat))
        (reg2var : r2vtype)
        (vvs: list (nat * (type * sact)))
        (sched_rir: rule_information_raw (reg_t:=reg_t) (ext_fn_t:=ext_fn_t))
        (rir: rule_information_raw (reg_t:=reg_t) (ext_fn_t:=ext_fn_t))
        (nid: nat)
        names0
        fail0
      : list (nat * type) * list (string * nat) * (r2vtype (reg_t:=reg_t)) * list (nat * (type * sact)) * sact * rule_information_raw * nat
      :=
      match args with
        [] => (names0, env, reg2var, vvs, fail0, rir, nid)
      | a::args =>
          let '(vc, vms, reg2var, vvs, failure, rir, nid, t) :=
            rec a tsig env reg2var vvs guard sched_rir rir nid in
          let arg_bind_name := nid in
          gria_listb args tsig vms reg2var
                    (list_assoc_setb Nat.eqb vvs arg_bind_name (t, reduce t vc))
                    sched_rir rir (S nid) ((arg_bind_name, t) :: names0) (merge_failures failure fail0)
      end.

  Fixpoint get_rule_information_auxb
           (ua: uact (pos_t:=pos_t) (reg_t:=reg_t) (ext_fn_t:=ext_fn_t))
           (tsig: list (string * type))
           (env: list (string * nat))
           (reg2var: r2vtype)
           (vvs: list (nat * (type * sact)))
           (guard: sact)
           (sched_rir: rule_information_raw (reg_t:=reg_t) (ext_fn_t:=ext_fn_t))
           (rir: rule_information_raw (reg_t:=reg_t) (ext_fn_t:=ext_fn_t)) (nid: nat)
    : option (sact)
      * list (string * nat)
      * r2vtype
      * (list (nat * (type * sact)))
      * sact * rule_information_raw * nat * type
    :=
    match ua with
    | DBind var val body =>
        let '(ret_val, vm_val, reg2var, vv_val, failures_val, rir_val, nid, tval) :=
          get_rule_information_auxb val tsig env reg2var vvs guard sched_rir rir nid in
        let name := nid in
        let '(ret_body, vm_body, reg2var, vv_body, failures_body, rir_body, nid, tbody) :=
          get_rule_information_auxb
            body ((var, tval)::tsig) ((var, name)::vm_val) reg2var
            (list_assoc_setb Nat.eqb vv_val name (tval, (reduce tval ret_val)))
            guard sched_rir rir_val (S nid) in
        (ret_body, skipn 1 vm_body (* var's binding goes out of scope *),
          reg2var,
          vv_body,
          merge_failures failures_val failures_body, rir_body, nid, tbody)
    | DAssign var val =>
        let '(ret_val, vm_val, reg2var, vv_val, failures_val, rir_val, nid, t) :=
          get_rule_information_auxb val tsig env reg2var vvs guard sched_rir rir nid in
        let name := nid in
        (None,
          list_assoc_setb eqb vm_val var name,
          reg2var,
          list_assoc_setb Nat.eqb vv_val name (t, (reduce t ret_val)),
          failures_val, rir_val, S nid, bits_t 0
        )
    | DVar var =>
        match list_assocb eqb env var, list_assocb eqb tsig var with
        | Some x, Some t => (Some (SVar x), env, reg2var, vvs, const_false, rir, nid, t)
        | _, _ => (* Unreachable assuming rule valid *)
            (None, env, reg2var, vvs, const_true, rir, nid, bits_t 0)
        end
    | DSeq a1 a2 =>
        let '(_, vm_a1, reg2var, vv_a1, failures_a1, rir_a1, nid_a1, _) :=
          get_rule_information_auxb a1 tsig env reg2var vvs guard sched_rir rir nid in
        let '(ret_a2, vm_a2, reg2var, vv_a2, failures_a2, rir_a2, nid_a2, t) :=
          get_rule_information_auxb a2 tsig vm_a1 reg2var vv_a1 guard sched_rir rir_a1 nid_a1 in
        (ret_a2, vm_a2, reg2var, vv_a2, merge_failures failures_a1 failures_a2,
          rir_a2, nid_a2, t)
    | DIf cond tb fb =>
        let '(ret_cond, vm_cond, reg2var, vv_cond, failures_cond, rir_cond, nid, t) :=
          get_rule_information_auxb cond tsig env reg2var vvs guard sched_rir rir nid in
        let cond_name := nid in
        let guard_tb_name := (nid + 1) in
        let guard_fb_name := (nid + 2) in
        let guard_tb := uand guard (SVar cond_name) in
        let guard_fb := uand guard (unot (SVar cond_name)) in
        let vv_cond := list_assoc_setb Nat.eqb vv_cond cond_name (bits_t 1, reduce (bits_t 1) ret_cond) in
        let vv_cond := list_assoc_setb Nat.eqb vv_cond guard_tb_name (bits_t 1, guard_tb) in
        let vv_cond := list_assoc_setb Nat.eqb vv_cond guard_fb_name (bits_t 1, guard_fb) in
        let '(ret_tb, vm_tb, reg2var_tb, vv_tb, failures_tb, rir_tb, nid, t1) :=
          get_rule_information_auxb tb tsig vm_cond reg2var vv_cond (SVar guard_tb_name) sched_rir rir_cond
                                   (nid + 3)
        in
        let '(ret_fb, vm_fb, reg2var_fb, vv_fb, failures_fb, rir_fb, nid, t2) :=
          (* We use rir_tb here even though we know that none of the actions added
           by the other branch can impact those from this branch (they are
           mutually exclusive). This way, we don't have to deal with
           rule_information_raw merging. However, this also means that the
           failure condition will contain some redundancy. *)
          get_rule_information_auxb fb tsig vm_cond reg2var vv_tb (SVar guard_fb_name) sched_rir rir_tb nid
        in
        (* Merge var maps: if vm_tb and vm_fb disagree for some variable, generate
         a new variable reflecting the condition and update the variables map.
         *)
        let '(vm_merge, vvs, nid) := merge_branchesb vm_tb vm_fb vv_fb nid cond_name in
        let '(reg2var, vvs, nid) := merge_reg2varsb reg2var_tb reg2var_fb cond_name vvs nid in
        (Some (SIf (reduce (bits_t 1) ret_cond) (reduce t1 ret_tb) (reduce t2 ret_fb)),
          vm_merge,
          reg2var,
          vvs,
          uor failures_cond
              (uor (uand (reduce (bits_t 1) ret_cond) failures_tb)
                   (uand (unot (reduce (bits_t 1) ret_cond)) failures_fb)),
          rir_fb, nid, t1)
    | DUnop ufn a =>
        let '(ret_a, vm_a, reg2var, vv_a, failures_a, rir_a, nid, t) :=
          get_rule_information_auxb a tsig env reg2var vvs guard sched_rir rir nid in
        (Some (SUnop ufn (reduce t ret_a)), vm_a, reg2var,
          vv_a, failures_a, rir_a, nid, ret_type_unop ufn t)
    | DBinop ufn a1 a2 =>
        let '(ret_a1, vm_a1, reg2var, vvs, failures_a1, rir_a1, nid, t1) :=
          get_rule_information_auxb a1 tsig env reg2var vvs guard sched_rir rir nid in
        let '(ret_a2, vm_a2, reg2var, vvs, failures_a2, rir_a2, nid, t2) :=
          get_rule_information_auxb a2 tsig vm_a1 reg2var vvs guard sched_rir rir_a1 nid in
        (Some (SBinop ufn (reduce t1 ret_a1) (reduce t2 ret_a2)), vm_a2, reg2var, vvs,
          merge_failures failures_a1 failures_a2, rir_a2, nid, ret_type_binop ufn t1 t2)
    | DInternalCall ufn args =>
        let '(arg_names, vm_args, reg2var, vv_args, failure_args, rir_args, nid) :=
          gria_listb guard get_rule_information_auxb
                    args tsig env reg2var vvs sched_rir rir nid [] const_false in
        let vm_tmp :=
          combine
            (fst (split (rev (int_argspec ufn)))) (* Names from argspec *)
            (map fst arg_names) in
        let '(ret_ic, _, reg2var, vv_ic, failure_ic, rir_ic, nid, t) :=
          get_rule_information_auxb (int_body ufn) (rev (int_argspec ufn)) vm_tmp reg2var vv_args guard sched_rir rir_args nid in
        (* We can forget vm_tmp which contained the temporary map for use in the
         called function. *)
        (ret_ic, vm_args, reg2var, vv_ic, merge_failures failure_ic failure_args,
          rir_ic, nid, t)
    | DAPos _ e => get_rule_information_auxb e tsig env reg2var vvs guard sched_rir rir nid
    | DRead port reg =>
        let failure :=
          match port with
            P0 =>
              uor (rir_has_write0b sched_rir reg)
                  (rir_has_write1b sched_rir reg)
          | P1 =>
              rir_has_write1b sched_rir reg
          end in
        let modified_rir :=
          match port with
          | P0 => add_read0b rir guard reg
          | P1 => add_read1b rir guard reg
          end in
        match list_assocb reg_port_unit_eqb reg2var (reg, inl port) with
        | Some v => (Some (SVar v), env, reg2var, vvs, failure, modified_rir, nid, R reg)
        | None => (None, env, reg2var, vvs, const_true, modified_rir, nid, R reg)
        end
    | DWrite port reg val =>
        let '(ret_val, vm_val, reg2var, vvs, failures_val, rir, nid, t) :=
          get_rule_information_auxb val tsig env reg2var vvs guard sched_rir rir nid in
        let '(rir_wr, failure_wr) :=
          match port with
          | P0 => add_write0b sched_rir rir guard reg (reduce t ret_val)
          | P1 => add_write1b sched_rir rir guard reg (reduce t ret_val)
          end
        in
        let '(reg2var, vvs, nid, t) :=
          match port with
          | P0 =>
              let v_read1 := nid in
              let nid := nid + 1 in
              let vvs := list_assoc_setb Nat.eqb vvs v_read1 (t, reduce t ret_val) in
              let reg2var := list_assoc_setb reg_port_unit_eqb reg2var (reg, inl P1) v_read1 in
              let reg2var := list_assoc_setb reg_port_unit_eqb reg2var (reg, inr tt) v_read1 in
              (reg2var, vvs, nid, t)
          | P1 =>
              let v_read1 := nid in
              let nid := nid + 1 in
              let vvs := list_assoc_setb Nat.eqb vvs v_read1 (t, reduce t ret_val) in
              let reg2var := list_assoc_setb reg_port_unit_eqb reg2var (reg, inr tt) v_read1 in
              (reg2var, vvs, nid, t)
          end in
        (None, vm_val, reg2var, vvs, merge_failures failures_val failure_wr, rir_wr,
          nid, bits_t 0)
    | DExternalCall ufn arg =>
        let '(ret_arg, vm_arg, reg2var, vv_arg, failures_arg, rir, nid, t) :=
          get_rule_information_auxb arg tsig env reg2var vvs guard sched_rir rir nid in
        let name := nid in
        (Some (SVar name), vm_arg, reg2var,
          list_assoc_setb Nat.eqb vv_arg name (retSig (Sigma ufn), SExternalCall ufn (reduce t ret_arg)),
          failures_arg, rir,
          S nid, retSig (Sigma ufn))
    | DError _ => (None, env, reg2var, vvs, const_true, rir, nid, bits_t 0)
    | DFail tau => (None, env, reg2var, vvs, const_true, rir, nid, tau)
    | @DConst _ _ _ _ _ tau c =>
        (Some (SConst (BitsToLists.val_of_value c)), env, reg2var, vvs, const_false, rir, nid, tau)
    end.

  Definition get_rule_informationb (ua: uact) (nid: nat) r2v vvs sched_rir
    : rule_information_raw * r2vtype * nat :=
    let '(vret, env, r2v, vvs, failure, rir, nid', t) :=
      get_rule_information_auxb
        ua [] [] r2v vvs const_true
        sched_rir
        init_rir
        nid
    in (
      (rir <| rir_failure_cond := failure |> <| rir_vars := vvs|>),
      r2v,
      nid').

  Fixpoint merge_cond_logsb (cl1 cl2: cond_log) (cond2: sact) :=
    match cl2 with
    | [] => cl1
    | (idx, c)::cl2 =>
        let c := uand (unot cond2) c in
        merge_cond_logsb (list_assoc_modifyb reg_eqb cl1 idx c (fun c1 => uor c1 c)) cl2 cond2
    end.

  Definition merge_rirsb rir rir' conflict_name vvs :=
    {|
      rir_read0s := merge_cond_logsb (rir_read0s rir) (rir_read0s rir') (SVar conflict_name);
      rir_read1s := merge_cond_logsb (rir_read1s rir) (rir_read1s rir') (SVar conflict_name);
      rir_write0s := merge_cond_logsb (rir_write0s rir) (rir_write0s rir') (SVar conflict_name);
      rir_write1s := merge_cond_logsb (rir_write1s rir) (rir_write1s rir') (SVar conflict_name);
      rir_vars := vvs;
      rir_failure_cond := uor (rir_failure_cond rir) (rir_failure_cond rir')
    |}.

  Fixpoint get_rir_scheduler'b (sched_rir: rule_information_raw) r2v
          (rules: rule_name_t -> uact) nid
          (s: scheduler pos_t rule_name_t) {struct s}
    :=
      let interp_cons rl s :=
        let '(rir', r2v', nid) := get_rule_informationb (rules rl) nid r2v (rir_vars sched_rir) sched_rir in
        let conflict : sact := rir_failure_cond rir' in
        let conflict_name := nid in
        let vvs := list_assoc_setb Nat.eqb (rir_vars rir') nid (bits_t 1, conflict) in
        let nid := nid + 1 in
        let '(r2v2, vvs, nid) := merge_reg2varsb r2v r2v' conflict_name vvs nid in
        let rir2 := merge_rirsb sched_rir rir' conflict_name vvs in
        get_rir_scheduler'b rir2 r2v2 rules nid s
      in
      match s with
      | Done => (sched_rir, r2v, nid)
      | Cons r s => interp_cons r s
      | Try r s1 s2 =>   (sched_rir,r2v,nid)       (* Ignored for now *)
      | SPos _ s => get_rir_scheduler'b sched_rir r2v rules nid s
      end.

  Definition init_regb r2v vvs (nid: nat) (idx: reg_t)
    : r2vtype * list (nat * (type * sact)) * nat :=
    let r2v := list_assoc_setb reg_port_unit_eqb r2v (idx,inl P0) nid in
    let r2v := list_assoc_setb reg_port_unit_eqb r2v (idx,inl P1) nid in
    let r2v := list_assoc_setb reg_port_unit_eqb r2v (idx,inr tt) nid in
    let vvs := list_assoc_setb Nat.eqb vvs nid (R idx, SConst (getenv REnv r idx)) in
    (r2v, vvs, nid + 1).

  Definition init_regsb r2v vvs (nid: nat) (l: list reg_t)
    : r2vtype * list (nat * (type * sact)) * nat :=
    fold_left (fun '(r2v,vvs,nid) idx => init_regb r2v vvs nid idx)
              l (r2v,vvs,nid).

  Context {finreg_t: FiniteType reg_t}.

  Definition init_r2vb nid :=
    init_regsb [] [] nid (finite_elements).

  Definition get_rir_schedulerb rules s :=
    let '(r2v, vvs, n) := init_r2vb O in
    get_rir_scheduler'b (init_rir <| rir_vars := vvs|>) r2v rules n s.

  Definition schedule_to_simple_formb rules s :=
    let '(rir, r2v, nid) := get_rir_schedulerb rules s in
    {|
      final_values := Sact.filter_map (fun '(r,p,n) => match p with
                                                  | inr tt => Some (r,n)
                                                  | inl _ => None
                                                  end) r2v ;
      vars := rir_vars rir;
    |}.

  Section Eq.
    Context {eqreg: EqDec reg_t}.
    Context {eqextfn: EqDec ext_fn_t}.

    Lemma rir_has_write0b_ok:
      forall rir reg,
        rir_has_write0 rir reg = rir_has_write0b rir reg.
    Proof.
      unfold rir_has_write0, rir_has_write0b. intros.
      rewrite <- list_assocb_eq; auto.
    Qed.

    Lemma rir_has_write1b_ok:
      forall rir reg,
        rir_has_write1 rir reg = rir_has_write1b rir reg.
    Proof.
      unfold rir_has_write1, rir_has_write1b. intros.
      rewrite <- list_assocb_eq; auto.
    Qed.

    Lemma rir_has_read0b_ok:
      forall rir reg,
        rir_has_read0 rir reg = rir_has_read0b rir reg.
    Proof.
      unfold rir_has_read0, rir_has_read0b. intros.
      rewrite <- list_assocb_eq; auto.
    Qed.

    Lemma rir_has_read1b_ok:
      forall rir reg,
        rir_has_read1 rir reg = rir_has_read1b rir reg.
    Proof.
      unfold rir_has_read1, rir_has_read1b. intros.
      rewrite <- list_assocb_eq; auto.
    Qed.

    Lemma add_read0b_ok: forall rir grd reg,
        add_read0 rir grd reg = add_read0b rir grd reg.
    Proof.
      unfold add_read0, add_read0b; intros.
      rewrite <- list_assocb_eq, <- list_assoc_setb_eq; auto.
    Qed.

    Lemma add_read1b_ok: forall rir grd reg,
        add_read1 rir grd reg = add_read1b rir grd reg.
    Proof.
      unfold add_read1, add_read1b; intros.
      rewrite <- list_assocb_eq, <- list_assoc_setb_eq; auto.
    Qed.

    Lemma add_write0b_ok: forall srir rir grd reg v,
        add_write0 srir rir grd reg v = add_write0b srir rir grd reg v.
    Proof.
      unfold add_write0, add_write0b; intros.
      rewrite
        <- ! list_assocb_eq,
        <- ! list_assoc_setb_eq,
        <- ! rir_has_write0b_ok,
        <- ! rir_has_write1b_ok,
        <- ! rir_has_read1b_ok
      ; auto.
    Qed.


    Lemma add_write1b_ok: forall srir rir grd reg v,
        add_write1 srir rir grd reg v = add_write1b srir rir grd reg v.
    Proof.
      unfold add_write1, add_write1b; intros.
      rewrite
        <- ! list_assocb_eq,
        <- ! list_assoc_setb_eq,
        <- ! rir_has_write1b_ok
      ; auto.
    Qed.

    Lemma merge_branchesb_ok:
      forall (vm_tb vm_fb: list (string*nat))
             (vvs: list (nat * (type * sact)))
             (nid: nat)
             (cond_name: nat),
        merge_branches vm_tb vm_fb vvs nid cond_name =
          merge_branchesb vm_tb vm_fb vvs nid cond_name.
    Proof.
      induction vm_tb; simpl; intros; eauto.
      destr; auto.
      do 2 (destr; auto). setoid_rewrite <- IHvm_tb.
      repeat (destr; auto; [idtac]).
      rewrite <- list_assoc_setb_eq, <- list_assocb_eq; eauto.
      apply Nat.eqb_spec.
      apply Nat.eqb_spec.
    Qed.

    Lemma merge_reg2vars_regb_ok:
      forall (r1 r2: r2vtype) reg prt cond_name r
             (vvs:list (nat * (type * sact))) nid,
        merge_reg2vars_reg r1 r2 reg prt cond_name r vvs nid =
          merge_reg2vars_regb r1 r2 reg prt cond_name r vvs nid.
    Proof.
      unfold merge_reg2vars_regb, merge_reg2vars_reg. intros.
      repeat rewrite <- ? list_assocb_eq, <- ? list_assoc_setb_eq; eauto.
      repeat (destr; auto; [idtac]).
      repeat rewrite <- ? list_assocb_eq, <- ? list_assoc_setb_eq; eauto.
      apply Nat.eqb_spec.
      apply reflect_reg_port_unit_eqb.
      apply Nat.eqb_spec.
      apply reflect_reg_port_unit_eqb.
      apply reflect_reg_port_unit_eqb.
      apply reflect_reg_port_unit_eqb.
    Qed.

    Lemma merge_reg2vars_auxb_ok:
      forall ks (r1 r2: r2vtype) r cond_name vvs nid,
        merge_reg2vars_aux ks r1 r2 r cond_name vvs nid =
          merge_reg2vars_auxb ks r1 r2 r cond_name vvs nid.
    Proof.
      induction ks; simpl; intros; eauto.
      destr.
      rewrite <- merge_reg2vars_regb_ok; eauto.
      repeat destr.
    Qed.

    Lemma merge_reg2varsb_ok:
      forall (r1 r2: r2vtype) cond_name vvs nid,
        merge_reg2vars r1 r2 cond_name vvs nid =
          merge_reg2varsb r1 r2 cond_name vvs nid.
    Proof.
      unfold merge_reg2varsb, merge_reg2vars.
      intros. eapply merge_reg2vars_auxb_ok.
    Qed.


    Lemma gria_listb_ok:
      forall guard rec1 rec2
             args (OK:
               forall u tsig env r2v vvs guard sched_rir rir nid,
                 In u args ->
                 rec1 u tsig env r2v vvs guard sched_rir rir nid =
                   rec2 u tsig env r2v vvs guard sched_rir rir nid
             )
             tsig env reg2var vvs sched_rir rir nid names0 fail0,
        gria_list guard rec1 args tsig env reg2var vvs sched_rir rir nid names0 fail0 =
          gria_listb guard rec2 args tsig env reg2var vvs sched_rir rir nid names0 fail0.
    Proof.
      induction args; simpl; intros; eauto.
      rewrite <- OK.
      repeat destr.
      rewrite <- list_assoc_setb_eq; eauto. apply Nat.eqb_spec. auto.
    Qed.

    Lemma get_rule_information_auxb_ok:
      forall (u: uact) tsig env reg2var vvs sched_rir rir nid guard,
        get_rule_information_aux R (Sigma:=Sigma) u tsig env reg2var vvs guard sched_rir rir nid =
        get_rule_information_auxb u tsig env reg2var vvs guard sched_rir rir nid.
    Proof.
      Ltac rews :=
        repeat rewrite <- ? list_assocb_eq,
          <- ? list_assoc_setb_eq; eauto using Nat.eqb_spec, reflect_reg_port_unit_eqb, eqb_spec.

      induction u using daction_ind'; simpl; intros; eauto; rews.
      - rewrite <- IHu.
        repeat (destr; rews; subst; auto; [idtac]).
        destr. rews.
      - rewrite <- ? IHu.
        do 7 destr.
        rewrite <- ? IHu0. auto.
      - rewrite <- ? IHu.
        do 7 destr.
        rews.
        rewrite <- ? IHu0. auto.
      - rewrite <- ? IHu.
        do 7 destr.
        rews.
        rewrite <- ? IHu0.
        destr. setoid_rewrite Heqp6.
        do 6 destr.
        rewrite <- ? IHu1.
        do 7 destr.
        rewrite <- merge_branchesb_ok.
        do 2 destr.
        rewrite <- merge_reg2varsb_ok. auto.
      - rews.
        rewrite
          <- ? rir_has_write0b_ok,
          <- ? rir_has_write1b_ok,
          <- ? rir_has_read1b_ok,
          <- ? add_read0b_ok,
          <- ? add_read1b_ok. auto.
      - rewrite <- IHu. do 7 destr.
        rewrite
          <- ? rir_has_write0b_ok,
          <- ? rir_has_write1b_ok,
          <- ? rir_has_read1b_ok,
          <- ? add_write0b_ok,
          <- ? add_write1b_ok.
        rews.
      - rewrite <- IHu. auto.
      - rewrite <- IHu. do 7 destr.
        rewrite <- IHu0. auto.
      - rewrite <- IHu. do 7 destr. rews.
      - rewrite <- gria_listb_ok with (rec1:=get_rule_information_aux R (Sigma:=Sigma)).
        do 6 destr.
        rewrite <- IHu; eauto.
        rewrite Forall_forall in H; intros; eapply H. auto.
    Qed.

    Lemma get_rule_informationb_ok:
      forall (u: uact) reg2var vvs sched_rir nid,
        get_rule_information R (Sigma:=Sigma) u nid reg2var vvs sched_rir =
          get_rule_informationb u nid reg2var vvs sched_rir.
    Proof.
      unfold get_rule_informationb, get_rule_information. intros.
      rewrite <- get_rule_information_auxb_ok. auto.
    Qed.

    Lemma merge_cond_logsb_ok: forall (cl2 cl1: cond_log) (cond2: sact),
        merge_cond_logs cl1 cl2 cond2 = merge_cond_logsb cl1 cl2 cond2.
    Proof.
      induction cl2; simpl; intros; eauto. destr.
      rewrite <- list_assoc_modifyb_eq. auto. auto.
    Qed.

    Lemma merge_rirsb_ok: forall rir rir' conflict_name vvs,
        merge_rirs rir rir' conflict_name vvs =
          merge_rirsb rir rir' conflict_name vvs.
    Proof.
      unfold merge_rirs, merge_rirsb. intros.
      f_equal.
      apply merge_cond_logsb_ok.
      apply merge_cond_logsb_ok.
      apply merge_cond_logsb_ok.
      apply merge_cond_logsb_ok.
    Qed.
    
    Lemma get_rir_scheduler'b_ok:
      forall (rules: rule_name_t -> uact)
             (s: scheduler pos_t rule_name_t)
             (sched_rir: rule_information_raw) r2v nid,
        get_rir_scheduler' R (Sigma:=Sigma) sched_rir r2v rules nid s =
          get_rir_scheduler'b sched_rir r2v rules nid s.
    Proof.
      induction s; simpl; intros; eauto.
      rewrite <- get_rule_informationb_ok. do 2 destr.
      rews.
      rewrite <- merge_reg2varsb_ok. do 2 destr.
      setoid_rewrite Heqp1. rewrite <- merge_rirsb_ok. eapply IHs.
    Qed.

    Lemma init_regb_ok: forall r2v vvs nid idx,
        init_reg REnv r R r2v vvs nid idx = init_regb r2v vvs nid idx.
    Proof.
      unfold init_reg, init_regb. intros. rews.
    Qed.

    Lemma fold_left_ext:
      forall {A B: Type} (f1 f2: A -> B -> A) (Fext: forall x y, f1 x y = f2 x y)
             (l: list B) (a: A),
        fold_left f1 l a = fold_left f2 l a.
    Proof.
      induction l; simpl; intros; eauto.
      rewrite Fext; apply IHl.
    Qed.

    Lemma init_regsb_ok:
      forall l r2v vvs nid,
        init_regs REnv r R r2v vvs nid l = init_regsb r2v vvs nid l.
    Proof.
      intros. unfold init_regs, init_regsb.
      apply fold_left_ext. intros. do 2 destr. apply init_regb_ok.
    Qed.

    Lemma init_r2vb_ok: forall nid,
        init_r2v REnv r R nid = init_r2vb nid.
    Proof.
      unfold init_r2v, init_r2vb. intros.
      apply init_regsb_ok.
    Qed.

    Lemma get_rir_schedulerb_ok:
      forall rules s,
        get_rir_scheduler (Sigma:=Sigma) REnv r R rules s = get_rir_schedulerb rules s.
    Proof.
      unfold get_rir_schedulerb, get_rir_scheduler. intros.
      rewrite <- init_r2vb_ok. do 2 destr. apply get_rir_scheduler'b_ok.
    Qed.

    Lemma schedule_to_simple_formb_ok:
      forall rules s,
        schedule_to_simple_form (Sigma:=Sigma) REnv r R rules s =
          schedule_to_simple_formb rules s.
    Proof.
      unfold schedule_to_simple_formb, schedule_to_simple_form.
      intros. rewrite <- get_rir_schedulerb_ok. auto.
    Qed.

  End Eq.

End SimpleFormb.

Close Scope nat.
