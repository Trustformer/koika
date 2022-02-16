(*! Frontend | Untyped syntax !*)
Require Export Koika.Common Koika.Primitives Koika.Types Koika.ErrorReporting.

Section Syntax.
  Context {pos_t var_t rule_name_t fn_name_t: Type}.
  Context {var_t_eq_dec: EqDec var_t}.

  Class Lift {from to: Type} := lift: from -> to.
  Class Inj {from to: Type} (f: from -> to) :=
    inj: forall i j, i <> j -> f i <> f j.
  Hint Mode Lift - ! : typeclass_instances.

  Inductive uaction {reg_t ext_fn_t} :=
  | UError (err: error pos_t var_t fn_name_t)
  | UFail (tau: type)
  | UVar (var: var_t)
  | UConst {tau: type} (cst: type_denote tau)
  | UAssign (v: var_t) (ex: uaction)
  | USeq (a1 a2: uaction)
  | UBind (v: var_t) (ex: uaction) (body: uaction)
  | UIf (cond: uaction) (tbranch: uaction) (fbranch: uaction)
  | URead (port: Port) (idx: reg_t)
  | UWrite (port: Port) (idx: reg_t) (value: uaction)
  | UUnop (ufn1: PrimUntyped.ufn1) (arg1: uaction)
  | UBinop (ufn2: PrimUntyped.ufn2) (arg1: uaction) (arg2: uaction)
  | UExternalCall (ufn: ext_fn_t) (arg: uaction)
  | UInternalCall (ufn: InternalFunction var_t fn_name_t uaction)
    (args: list uaction)
  | UAPos (p: pos_t) (e: uaction)
  | USugar (s: usugar)
  with usugar {reg_t ext_fn_t} :=
  | UErrorInAst
  | USkip
  | UConstBits {sz} (bs: bits sz)
  | UConstString (s: string)
  | UConstEnum (sig: enum_sig) (cst: string)
  | UProgn (aa: list uaction)
  | ULet (bindings: list (var_t * uaction)) (body: uaction)
  | UWhen (cond: uaction) (body: uaction)
  | USwitch (var: uaction) (default: uaction)
    (branches: list (uaction * uaction))
  | UStructInit (sig: struct_sig) (fields: list (string * uaction))
  | UArrayInit (tau: type) (elements: list uaction)
  | UCallModule {module_reg_t module_ext_fn_t: Type}
    `{finite_reg: FiniteType module_reg_t} (fR: module_reg_t -> reg_t)
    (fSigma: @Lift module_ext_fn_t ext_fn_t)
    (fn: InternalFunction var_t fn_name_t (
      @uaction module_reg_t module_ext_fn_t
    )) (args: list uaction).

  Section uaction_ind'.
    Context {reg_t ext_fn_t: Type}.
    Variable P: uaction (reg_t := reg_t) (ext_fn_t := ext_fn_t) -> Prop.

    Hypothesis UError_case: forall err, P (UError err).
    Hypothesis UFail_case: forall tau, P (UFail tau).
    Hypothesis UVar_case: forall var, P (UVar var).
    Hypothesis UConst_case: forall tau cst, P (UConst (tau := tau) cst).
    Hypothesis UAssign_case: forall v ex, P ex -> P (UAssign v ex).
    Hypothesis USeq_case: forall a1 a2, P a1 -> P a2 -> P (USeq a1 a2).
    Hypothesis UBind_case:
      forall v ex body, P ex -> P body -> P (UBind v ex body).
    Hypothesis UIf_case:
      forall cond tbranch fbranch,
      P cond -> P tbranch -> P fbranch -> P (UIf cond tbranch fbranch).
    Hypothesis URead_case: forall port idx, P (URead port idx).
    Hypothesis UWrite_case:
      forall port idx value, P value -> P (UWrite port idx value).
    Hypothesis UUnop_case: forall ufn1 arg1, P arg1 -> P (UUnop ufn1 arg1).
    Hypothesis UBinop_case:
      forall ufn2 arg1 arg2, P arg1 -> P arg2 -> P (UBinop ufn2 arg1 arg2).
    Hypothesis UExternalCall_case:
      forall ufn arg, P arg -> P (UExternalCall ufn arg).
    Hypothesis UInternalCall_case:
      forall ufn args,
      P (int_body ufn) -> Forall P args -> P (UInternalCall ufn args).
    Hypothesis UAPos_case: forall p e, P e -> P (UAPos p e).
    (* We don't care about the mutually inductive part. *)
    Hypothesis USugar_case: forall s, P (USugar s).

    Fixpoint uaction_ind' ua: P ua :=
      match ua with
      | UError err => UError_case err
      | UFail tau => UFail_case tau
      | UVar var => UVar_case var
      | @UConst _ _ tau cst => UConst_case tau cst
      | UAssign v ex => UAssign_case v ex (uaction_ind' ex)
      | USeq a1 a2 => USeq_case a1 a2 (uaction_ind' a1) (uaction_ind' a2)
      | UBind v ex body =>
        UBind_case v ex body (uaction_ind' ex) (uaction_ind' body)
      | UIf cond tbranch fbranch =>
        UIf_case cond tbranch fbranch (uaction_ind' cond) (uaction_ind' tbranch)
          (uaction_ind' fbranch)
      | URead port idx => URead_case port idx
      | UWrite port idx value => UWrite_case port idx value (uaction_ind' value)
      | UUnop ufn1 arg1 => UUnop_case ufn1 arg1 (uaction_ind' arg1)
      | UBinop ufn2 arg1 arg2 =>
        UBinop_case ufn2 arg1 arg2 (uaction_ind' arg1) (uaction_ind' arg2)
      | UExternalCall ufn arg => UExternalCall_case ufn arg (uaction_ind' arg)
      | UInternalCall ufn args =>
        UInternalCall_case ufn args (uaction_ind' (int_body ufn)) ((
          fix uaction_list_ind' args: Forall P args :=
            match args with
            | [] => Forall_nil P
            | h::t => Forall_cons (h) (uaction_ind' h) (uaction_list_ind' t)
            end
        ) args)
      | UAPos p e => UAPos_case p e (uaction_ind' e)
      | USugar s => USugar_case s
      end.
  End uaction_ind'.

  Inductive scheduler :=
  | Done
  | Cons (r: rule_name_t) (s: scheduler)
  | Try (r: rule_name_t) (s1 s2: scheduler)
  | SPos (p: pos_t) (s: scheduler).



  Inductive daction {reg_t ext_fn_t} :=
  | DError (err: error pos_t var_t fn_name_t)
  | DFail (tau: type)
  | DVar (var: var_t)
  | DConst {tau: type} (cst: type_denote tau)
  | DAssign (v: var_t) (ex: daction)
  | DSeq (a1 a2: daction)
  | DBind (v: var_t) (ex: daction) (body: daction)
  | DIf (cond: daction) (tbranch: daction) (fbranch: daction)
  | DRead (port: Port) (idx: reg_t)
  | DWrite (port: Port) (idx: reg_t) (value: daction)
  | DUnop (ufn1: PrimUntyped.ufn1) (arg1: daction)
  | DBinop (ufn2: PrimUntyped.ufn2) (arg1: daction) (arg2: daction)
  | DExternalCall (ufn: ext_fn_t) (arg: daction)
  | DInternalCall (ufn: InternalFunction var_t fn_name_t daction)
    (args: list daction)
  | DAPos (p: pos_t) (e: daction).

  Definition map_error {A B: Type} (f: A -> option B) :=
    fix map_error (l: list A) {struct l}: option (list B) :=
    match l with
      [] => Some []
    | a::r =>
        let/opt fr := map_error r in
        let/opt fa := f a in
        Some (fa::fr)
    end.

  Fixpoint uaction_to_daction {reg_t ext_fn_t} (ua: uaction (reg_t:=reg_t) (ext_fn_t:=ext_fn_t))
    {struct ua}:
    option (@daction reg_t ext_fn_t) :=
    match ua with
    | UError err => Some (DError err)
    | UFail t => Some (DFail t)
    | UVar v => Some (DVar v)
    | UConst cst => Some (DConst cst)
    | UAssign v e =>
        let/opt de := uaction_to_daction e in
        Some (DAssign v de)
    | USeq s1 s2 =>
        let/opt ds1 := uaction_to_daction s1 in
        let/opt ds2 := uaction_to_daction s2 in
        Some (DSeq ds1 ds2)
    | UBind v e body =>
        let/opt de := uaction_to_daction e in
        let/opt dbody := uaction_to_daction body in
        Some (DBind v de dbody)
    | UIf c t f =>
        let/opt dc := uaction_to_daction c in
        let/opt dt := uaction_to_daction t in
        let/opt df := uaction_to_daction f in
        Some (DIf dc dt df)
    | URead prt idx => Some (DRead prt idx)
    | UWrite prt idx v =>
        let/opt dv := uaction_to_daction v in
        Some (DWrite prt idx dv)
    | UUnop fn a =>
        let/opt da := uaction_to_daction a in
        Some (DUnop fn da)
    | UBinop fn a1 a2 =>
        let/opt da1 := uaction_to_daction a1 in
        let/opt da2 := uaction_to_daction a2 in
        Some (DBinop fn da1 da2)
    | UExternalCall ufn a =>
        let/opt da := uaction_to_daction a in
        Some (DExternalCall ufn da)
    | UInternalCall ufn args =>
      let/opt dargs := map_error uaction_to_daction args in
      let/opt dbody := uaction_to_daction (int_body ufn) in
      Some (DInternalCall {| int_name := int_name ufn;
                            int_argspec := int_argspec ufn;
                            int_retSig := int_retSig ufn;
                            int_body := dbody
                          |} dargs)
    | UAPos p e =>
        let/opt de := uaction_to_daction e in
        Some (DAPos p de)
    | USugar _ => None
    end.

  Section daction_ind'.
    Context {reg_t ext_fn_t: Type}.
    Variable P: daction (reg_t := reg_t) (ext_fn_t := ext_fn_t) -> Prop.

    Hypothesis DError_case: forall err, P (DError err).
    Hypothesis DFail_case: forall tau, P (DFail tau).
    Hypothesis DVar_case: forall var, P (DVar var).
    Hypothesis DConst_case: forall tau cst, P (DConst (tau := tau) cst).
    Hypothesis DAssign_case: forall v ex, P ex -> P (DAssign v ex).
    Hypothesis DSeq_case: forall a1 a2, P a1 -> P a2 -> P (DSeq a1 a2).
    Hypothesis DBind_case:
      forall v ex body, P ex -> P body -> P (DBind v ex body).
    Hypothesis DIf_case:
      forall cond tbranch fbranch,
      P cond -> P tbranch -> P fbranch -> P (DIf cond tbranch fbranch).
    Hypothesis DRead_case: forall port idx, P (DRead port idx).
    Hypothesis DWrite_case:
      forall port idx value, P value -> P (DWrite port idx value).
    Hypothesis DUnop_case: forall ufn1 arg1, P arg1 -> P (DUnop ufn1 arg1).
    Hypothesis DBinop_case:
      forall ufn2 arg1 arg2, P arg1 -> P arg2 -> P (DBinop ufn2 arg1 arg2).
    Hypothesis DExternalCall_case:
      forall ufn arg, P arg -> P (DExternalCall ufn arg).
    Hypothesis DInternalCall_case:
      forall ufn args,
      P (int_body ufn) -> Forall P args -> P (DInternalCall ufn args).
    Hypothesis DAPos_case: forall p e, P e -> P (DAPos p e).

    Fixpoint daction_ind' ua: P ua :=
      match ua with
      | DError err => DError_case err
      | DFail tau => DFail_case tau
      | DVar var => DVar_case var
      | @DConst _ _ tau cst => DConst_case tau cst
      | DAssign v ex => DAssign_case v ex (daction_ind' ex)
      | DSeq a1 a2 => DSeq_case a1 a2 (daction_ind' a1) (daction_ind' a2)
      | DBind v ex body =>
        DBind_case v ex body (daction_ind' ex) (daction_ind' body)
      | DIf cond tbranch fbranch =>
        DIf_case cond tbranch fbranch (daction_ind' cond) (daction_ind' tbranch)
          (daction_ind' fbranch)
      | DRead port idx => DRead_case port idx
      | DWrite port idx value => DWrite_case port idx value (daction_ind' value)
      | DUnop ufn1 arg1 => DUnop_case ufn1 arg1 (daction_ind' arg1)
      | DBinop ufn2 arg1 arg2 =>
        DBinop_case ufn2 arg1 arg2 (daction_ind' arg1) (daction_ind' arg2)
      | DExternalCall ufn arg => DExternalCall_case ufn arg (daction_ind' arg)
      | DInternalCall ufn args =>
        DInternalCall_case ufn args (daction_ind' (int_body ufn)) ((
          fix daction_list_ind' args: Forall P args :=
            match args with
            | [] => Forall_nil P
            | h::t => Forall_cons (h) (daction_ind' h) (daction_list_ind' t)
            end
        ) args)
      | DAPos p e => DAPos_case p e (daction_ind' e)
      end.
  End daction_ind'.


End Syntax.

Arguments Lift: clear implicits.
Arguments usugar : clear implicits.
Arguments uaction : clear implicits.
Arguments scheduler : clear implicits.
