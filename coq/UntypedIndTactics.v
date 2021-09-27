(*! Language | Tactics and theorems for reasoning about the untyped inductive
    semantics of Kôika programs !*)
Require Import Coq.Program.Equality.
Require Import List.
Require Import Koika.BitsToLists Koika.Frontend Koika.UntypedSemantics
  Koika.UntypedIndSemantics.

Ltac invert_next H :=
  lazymatch type of H with
  | interp_action ?ctx ?sigma ?Gamma ?sched_log ?action_log
      (UVar ?var) ?action_log' ?v ?Gamma'
    => apply invert_var in H; do 2 (let a := fresh in destruct H as (a & H))
  | interp_action ?ctx ?sigma ?Gamma ?sched_log ?action_log
      (UConst ?cst) ?action_log' ?v ?Gamma'
    => apply invert_const in H; do 2 (let a := fresh in destruct H as (a & H))
  | interp_action ?ctx ?sigma ?Gamma ?sched_log ?action_log
      (UAssign ?k ?a) ?action_log' ?v ?Gamma'
    => apply invert_assign in H; do 2 (destruct H);
      do 2 (let a := fresh in destruct H as (a & H))
  | interp_action ?ctx ?sigma ?Gamma ?sched_log ?action_log
      (USeq ?a1 ?a2) ?action_log' ?v ?Gamma'
    => apply invert_seq in H; do 10 (let a := fresh in destruct H as (a & H))
  | interp_action ?ctx ?sigma ?Gamma ?sched_log ?action_log
      (UBind ?k ?a1 ?a2) ?action_log' ?v ?Gamma'
    => apply invert_bind in H; do 10 (let a := fresh in destruct H as (a & H))
  | interp_action ?ctx ?sigma ?Gamma ?sched_log ?action_log
      (UIf ?cond ?athen ?aelse) ?action_log' ?v ?Gamma'
    => apply invert_if in H; do 10 (let a := fresh in destruct H as (a & H))
  | interp_action ?ctx ?sigma ?Gamma ?sched_log ?action_log
      (URead ?prt ?idx) ?action_log' ?v ?Gamma'
    => apply invert_read in H; do 3 (let a := fresh in destruct H as (a & H))
  | interp_action ?ctx ?sigma ?Gamma ?sched_log ?action_log
      (UWrite ?prt ?idx ?a) ?action_log' ?v ?Gamma'
    => apply invert_write in H;
    do 2 (let a := fresh in destruct H as (a & H));
    let a := fresh in destruct H as (a & H); destruct a;
    do 2 (let a := fresh in destruct H as (a & H))
  | interp_action ?ctx ?sigma ?Gamma ?sched_log ?action_log
      (UUnop ?fn ?a) ?action_log' ?v ?Gamma'
    => apply invert_unop in H; do 2 (let a := fresh in destruct H as (a & H))
  | interp_action ?ctx ?sigma ?Gamma ?sched_log ?action_log
      (UBinop ?fn ?a1 ?a2) ?action_log' ?v ?Gamma'
    => apply invert_binop in H;
    do 10 (let a := fresh in destruct H as (a & H))
  | interp_action ?ctx ?sigma ?Gamma ?sched_log ?action_log
      (UExternalCall ?fn ?a) ?action_log' ?v ?Gamma'
    => apply invert_extcall in H;
    do 2 (let a := fresh in destruct H as (a & H))
  | interp_action ?ctx ?sigma ?Gamma ?sched_log ?action_log
      (UInternalCall ?fn ?a) ?action_log' ?v ?Gamma'
    => apply invert_intcall in H;
    do 4 (let a := fresh in destruct H as (a & H))
  | interp_action ?ctx ?sigma ?Gamma ?sched_log ?action_log
      (USugar (UAPos ?p ?a)) ?action_log' ?v ?Gamma'
    => apply invert_pos in H
  | interp_action ?ctx ?sigma ?Gamma ?sched_log ?action_log
      (USugar USkip) ?action_log' ?v ?Gamma'
    => apply invert_skip in H; do 2 (let a := fresh in destruct H as (a & H))
  | interp_action ?ctx ?sigma ?Gamma ?sched_log ?action_log
      (USugar (UConstBits ?b)) ?action_log' ?v ?Gamma'
    => apply invert_constbits in H; simpl in H;
    do 2 (let a := fresh in destruct H as (a & H))
  | interp_action ?ctx ?sigma ?Gamma ?sched_log ?action_log
      (USugar (UConstString ?s)) ?action_log' ?v ?Gamma'
    => apply invert_conststring in H;
    do 2 (let a := fresh in destruct H as (a & H))
  | interp_action ?ctx ?sigma ?Gamma ?sched_log ?action_log
      (USugar (UConstEnum ?sig ?name)) ?action_log' ?v ?Gamma'
    => apply invert_constenum in H; do 3 (let a := fresh in destruct H as (a & H))
  | interp_action ?ctx ?sigma ?Gamma ?sched_log ?action_log
      (USugar (UProgn ?aa)) ?action_log' ?v ?Gamma'
    => apply invert_progn in H; do 2 (let a := fresh in destruct H as (a & H))
  | interp_action ?ctx ?sigma ?Gamma ?sched_log ?action_log
      (USugar (ULet ?bindings ?body)) ?action_log' ?v ?Gamma'
    => apply invert_let in H; do 6 (let a := fresh in destruct H as (a & H))
  | interp_action ?ctx ?sigma ?Gamma ?sched_log ?action_log
      (USugar (UWhen ?cond ?athen)) ?action_log' ?v ?Gamma'
    => apply invert_when in H; do 3 (let a := fresh in destruct H as (a & H))
  | interp_action ?ctx ?sigma ?Gamma ?sched_log ?action_log
      (USugar (USwitch ?var ?default [])) ?action_log' ?v ?Gamma'
    => apply invert_switch_nil in H
  | interp_action ?ctx ?sigma ?Gamma ?sched_log ?action_log
      (USugar (USwitch ?var ?default ?b)) ?action_log' ?v ?Gamma'
    => apply invert_switch in H;
    do 9 (let a := fresh in destruct H as (a & H))
  | interp_action ?ctx ?sigma ?Gamma ?sched_log ?action_log
      (USugar (UStructInit ?sig ?fields)) ?action_log' ?v ?Gamma'
    => apply invert_structinit in H;
    do 6 (let a := fresh in destruct H as (a & H))
  | interp_action ?ctx ?sigma ?Gamma ?sched_log ?action_log
      (USugar (UArrayInit ?sig ?fields)) ?action_log' ?v ?Gamma'
    => apply invert_arrayinit in H;
    do 6 (let a := fresh in destruct H as (a & H))
  | interp_action ?ctx ?sigma ?Gamma ?sched_log ?action_log
      (USugar (UCallModule ?fR ?fSigma ?fn ?args)) ?action_log' ?v ?Gamma'
    => apply invert_callmodule in H;
    do 6 (let a := fresh in destruct H as (a & H))
  end; subst.

(* TODO WIP *)
Ltac invert_full H :=
  lazymatch type of H with
  | interp_action ?ctx ?sigma ?Gamma ?sched_log ?action_log
      (UAssign ?k ?a) ?action_log' ?v ?Gamma'
    => apply invert_assign in H; do 2 (destruct H);
    do 2 (let a := fresh in destruct H as (a & H)); invert_full H
  | interp_action ?ctx ?sigma ?Gamma ?sched_log ?action_log
      (USeq ?a1 ?a2) ?action_log' ?v ?Gamma'
    => apply invert_seq in H; do 9 (let a := fresh in destruct H as (a & H));
    let a := fresh in destruct H as (a & H); invert_full a; invert_full H
  | interp_action ?ctx ?sigma ?Gamma ?sched_log ?action_log
      (UBind ?k ?a1 ?a2) ?action_log' ?v ?Gamma'
    => apply invert_bind in H;
    do 9 (let a := fresh in destruct H as (a & H));
    let a := fresh in destruct H as (a & H); invert_full a; invert_full H
  | interp_action ?ctx ?sigma ?Gamma ?sched_log ?action_log
      (UIf ?cond ?athen ?aelse) ?action_log' ?v ?Gamma'
    => apply invert_if in H; do 9 (let a := fresh in destruct H as (a & H));
    let a := fresh in destruct H as (a & H); invert_full a; invert_full H
  | interp_action ?ctx ?sigma ?Gamma ?sched_log ?action_log
      (UWrite ?prt ?idx ?a) ?action_log' ?v ?Gamma'
    => apply invert_write in H;
    do 2 (let a := fresh in destruct H as (a & H));
    let a := fresh in destruct H as (a & H); destruct a;
    do 2 (let a := fresh in destruct H as (a & H));
    invert_full H
  | interp_action ?ctx ?sigma ?Gamma ?sched_log ?action_log
      (UUnop ?fn ?a) ?action_log' ?v ?Gamma'
    => apply invert_unop in H; do 2 (let a := fresh in destruct H as (a & H));
    invert_full H
  | interp_action ?ctx ?sigma ?Gamma ?sched_log ?action_log
      (UBinop ?fn ?a1 ?a2) ?action_log' ?v ?Gamma'
    => apply invert_binop in H;
    do 9 (let a := fresh in destruct H as (a & H));
    let a := fresh in destruct H as (a & H); invert_full a; invert_full H
  | interp_action ?ctx ?sigma ?Gamma ?sched_log ?action_log
      (UExternalCall ?fn ?a) ?action_log' ?v ?Gamma'
    => apply invert_extcall in H;
    do 2 (let a := fresh in destruct H as (a & H)); invert_full H
  | interp_action ?ctx ?sigma ?Gamma ?sched_log ?action_log
      (UInternalCall ?fn ?a) ?action_log' ?v ?Gamma'
    => apply invert_intcall in H;
    do 4 (let a := fresh in destruct H as (a & H))
  (* TODO Not done from here *)
  | interp_action ?ctx ?sigma ?Gamma ?sched_log ?action_log
      (USugar (UAPos ?p ?a)) ?action_log' ?v ?Gamma'
    => apply invert_pos in H
  | interp_action ?ctx ?sigma ?Gamma ?sched_log ?action_log
      (USugar (UProgn ?aa)) ?action_log' ?v ?Gamma'
    => apply invert_progn in H; do 2 (let a := fresh in destruct H as (a & H))
  | interp_action ?ctx ?sigma ?Gamma ?sched_log ?action_log
      (USugar (ULet ?bindings ?body)) ?action_log' ?v ?Gamma'
    => apply invert_let in H; do 6 (let a := fresh in destruct H as (a & H))
  | interp_action ?ctx ?sigma ?Gamma ?sched_log ?action_log
      (USugar (UWhen ?cond ?athen)) ?action_log' ?v ?Gamma'
    => apply invert_when in H; do 3 (let a := fresh in destruct H as (a & H))
  | interp_action ?ctx ?sigma ?Gamma ?sched_log ?action_log
      (USugar (USwitch ?var ?default [])) ?action_log' ?v ?Gamma'
    => apply invert_switch_nil in H
  | interp_action ?ctx ?sigma ?Gamma ?sched_log ?action_log
      (USugar (USwitch ?var ?default ?b)) ?action_log' ?v ?Gamma'
    => apply invert_switch in H;
    do 9 (let a := fresh in destruct H as (a & H))
  | interp_action ?ctx ?sigma ?Gamma ?sched_log ?action_log
      (USugar (UStructInit ?sig ?fields)) ?action_log' ?v ?Gamma'
    => apply invert_structinit in H;
    do 6 (let a := fresh in destruct H as (a & H))
  | interp_action ?ctx ?sigma ?Gamma ?sched_log ?action_log
      (USugar (UArrayInit ?sig ?fields)) ?action_log' ?v ?Gamma'
    => apply invert_arrayinit in H;
    do 6 (let a := fresh in destruct H as (a & H))
  | interp_action ?ctx ?sigma ?Gamma ?sched_log ?action_log
      (USugar (UCallModule ?fR ?fSigma ?fn ?args)) ?action_log' ?v ?Gamma'
    => apply invert_callmodule in H;
    do 6 (let a := fresh in destruct H as (a & H))
  | interp_action ?ctx ?sigma ?Gamma ?sched_log ?action_log ?term ?action_log'
      ?v ?Gamma' => try invert_next H
  end; subst.

Fixpoint existsb_uaction
  {reg_t' ext_fn_t' pos_t var_t fn_name_t reg_t ext_fn_t: Type}
  (ua: uaction pos_t var_t fn_name_t reg_t' ext_fn_t')
  (pred:
    forall (reg_t'' ext_fn_t'': Type),
    uaction pos_t var_t fn_name_t reg_t'' ext_fn_t''
    -> (reg_t'' -> reg_t) -> (ext_fn_t'' -> ext_fn_t)
    -> bool
  )
  (fR: reg_t' -> reg_t) (fSigma: ext_fn_t' -> ext_fn_t)
: bool :=
  pred reg_t' ext_fn_t' ua fR fSigma ||
  match ua with
  | UAssign _ ex => existsb_uaction ex pred fR fSigma
  | USeq a1 a2 => existsb_uaction a1 pred fR fSigma || existsb_uaction a2 pred fR fSigma
  | UBind _ ex b => existsb_uaction ex pred fR fSigma || existsb_uaction b pred fR fSigma
  | UIf c t f => existsb_uaction c pred fR fSigma || existsb_uaction t pred fR fSigma
    || existsb_uaction f pred fR fSigma
  | UWrite _ _ a => existsb_uaction a pred fR fSigma
  | UUnop _ a => existsb_uaction a pred fR fSigma
  | UBinop _ a1 a2 => existsb_uaction a1 pred fR fSigma || existsb_uaction a2 pred fR fSigma
  | UExternalCall _ a => existsb_uaction a pred fR fSigma
  | UInternalCall ufn al =>
    existsb_uaction (int_body ufn) pred fR fSigma
    || existsb (fun a => existsb_uaction a pred fR fSigma) al
  | UAPos _ e => existsb_uaction e pred fR fSigma
  | USugar s => existsb_usugar s pred fR fSigma
  | _ => false
  end
with existsb_usugar
  {reg_t' ext_fn_t' pos_t var_t fn_name_t reg_t ext_fn_t: Type}
  (us: usugar pos_t var_t fn_name_t reg_t' ext_fn_t')
  (pred:
    forall (reg_t'' ext_fn_t'': Type),
    uaction pos_t var_t fn_name_t reg_t'' ext_fn_t''
    -> (reg_t'' -> reg_t) -> (ext_fn_t'' -> ext_fn_t)
    -> bool
  )
  (fR: reg_t' -> reg_t) (fSigma: ext_fn_t' -> ext_fn_t)
: bool :=
  match us with
  | UProgn aa => existsb (fun a => existsb_uaction a pred fR fSigma) aa
  | ULet bindings body =>
    existsb (fun '(_, u) => existsb_uaction u pred fR fSigma) bindings
    || existsb_uaction body pred fR fSigma
  | UWhen c b => existsb_uaction c pred fR fSigma || existsb_uaction b pred fR fSigma
  | USwitch v d b => existsb_uaction v pred fR fSigma || existsb_uaction d pred fR fSigma
    || existsb (
      fun '(u1, u2) => existsb_uaction u1 pred fR fSigma || existsb_uaction u2 pred fR fSigma
    ) b
  | UStructInit _ f => existsb (fun '(_, u) => existsb_uaction u pred fR fSigma) f
  | UArrayInit _ elts => existsb (fun u => existsb_uaction u pred fR fSigma) elts
  | UCallModule fR' fSigma' fn args =>
    existsb_uaction (int_body fn) pred
      (fun x => fR (fR' x)) (fun x => fSigma (fSigma' x))
    || existsb (fun u => existsb_uaction u pred fR fSigma) args
  | _ => false
  end.

Definition is_write
  {reg_t' ext_fn_t' pos_t var_t fn_name_t reg_t ext_fn_t: Type}
  (ua: uaction pos_t var_t fn_name_t reg_t ext_fn_t)
  (fR: reg_t -> reg_t') (fSigma: ext_fn_t -> ext_fn_t')
: bool :=
  match ua with
  | UWrite _ _ _ => true
  | _ => false
  end.

Inductive breadcrumb := here | through_nth_branch (n: nat) (b: breadcrumb).

Open Scope nat.
Definition zoom_result_type
  {pos_t var_t fn_name_t reg_t ext_fn_t: Type}
  (bc: breadcrumb) (ua: uaction pos_t var_t fn_name_t reg_t ext_fn_t)
: Type :=
  match bc with
  | here => uaction pos_t var_t fn_name_t reg_t ext_fn_t
  | through_nth_branch n _ =>
    match ua with
    | USugar s =>
      match s with
      | @UCallModule _ _ _ _ _ reg_t' ext_fn_t' _ _ _ _ _ =>
          if (Nat.ltb 1 n) then uaction pos_t var_t fn_name_t reg_t' ext_fn_t'
          else uaction pos_t var_t fn_name_t reg_t ext_fn_t
      | _ => uaction pos_t var_t fn_name_t reg_t ext_fn_t
      end
    | _ => uaction pos_t var_t fn_name_t reg_t ext_fn_t
    end
  end.

Compute zoom_result_type (through_nth_branch _ _) (UAssign _ _).

Definition zoom_breadcrumb
  {pos_t var_t fn_name_t reg_t ext_fn_t: Type}
  (bc: breadcrumb) (ua: uaction pos_t var_t fn_name_t reg_t ext_fn_t)
: option ((zoom_result_type bc ua) * breadcrumb) :=
  match bc with
  | here => None
  | through_nth_branch n sbc =>
    match ua as ua0 return option (zoom_result_type (through_nth_branch n sbc) ua * breadcrumb) with
    | UAssign v a => if n =? 1 return (option (zoom_result_type (through_nth_branch n sbc) (UAssign v a)) * breadcrumb) then Some (a, sbc) else None
    | USeq a1 a2 =>
      if n =? 1 then Some (a1, sbc) else if n =? 2 then Some (a2, sbc) else None
    | UBind _ expr body =>
      if n =? 1 then Some (expr, sbc)
      else if n =? 2 then Some (body, sbc)
      else None
    | UIf cond tbranch fbranch =>
      if n =? 1 then Some (cond, sbc)
      else if n =? 2 then Some (tbranch, sbc)
      else if n =? 3 then Some (fbranch, sbc)
      else None
    | UWrite _ _ v => if n =? 1 then Some (v, sbc) else None
    | UUnop _ a1 => if n =? 1 then Some (a1, sbc) else None
    | UBinop _ a1 a2 =>
      if n =? 1 then Some (a1, sbc) else if n =? 2 then Some (a2, sbc) else None
    | UExternalCall _ a => if n =? 1 then Some (a, sbc) else None
    | UInternalCall ufn la =>
      if n =? 1 then Some (int_body ufn, sbc)
      else
        match nth_error la (n - 1) with
        | Some a => Some (a, sbc)
        | None => None
        end
    | UAPos _ e => if n =? 1 then Some (e, sbc) else None
    | USugar s =>
      match s with
      | UProgn la =>
        match nth_error la n with
        | Some a => Some (a, sbc)
        | None => None
        end
      | ULet bnd body =>
        if n =? (List.length bnd) + 1 then Some (body, sbc)
        else
          match nth_error bnd n with
          | Some (_, a) => Some (a, sbc)
          | None => None
          end
      | UWhen cond body =>
        if n =? 1 then Some (cond, sbc)
        else if n =? 2 then Some (body, sbc)
        else None
      | USwitch v def branches =>
        if n =? 1 then Some (v, sbc)
        else if n =? 2 then Some (def, sbc)
        else
          match nth_error branches ((n - 2)/2) with
          | Some (a, b) =>
            if (n mod 2 =? 0) then Some (a, sbc) else Some (b, sbc)
          | None => None
          end
      | UStructInit _ fields =>
        match nth_error fields n with
        | Some (_, a) => Some (a, sbc)
        | None => None
        end
      | UArrayInit _ elts =>
        match nth_error elts n with
        | Some a => Some (a, sbc)
        | None => None
        end
      | UCallModule _ _ fn args =>
          if n =? 1 then Some (int_body fn, sbc)
          else
            match nth_error args with
            | Some a => Some (a, sbc)
            | None => None
            end
      | _ => None
      end
    | _ => None
    end
  end.
Close Scope nat.

Fixpoint zoom_n_breadcrumb :=
  {pos_t var_t fn_name_t reg_t ext_fn_t: Type}
  (bc: breadcrumb) (ua: uaction pos_t var_t fn_name_t reg_t ext_fn_t)
  (n : nat)
  : Some (uaction pos_t var_t fn_name_t reg_t ext_fn_t * breadcrumb) :=
  match n with
  | O => Some (ua, bc)
  | S n' =>
    match zoom_breadcrumb with
    | None => None
    | Some (ua', bc') => zoom_n_breadcrumb bc' ua' n'
    end
  end.

Fixpoint access_breadcrumb
  {pos_t var_t fn_name_t reg_t ext_fn_t: Type}
  (bc: breadcrumb) (ua: uaction pos_t var_t fn_name_t reg_t ext_fn_t)
: Some uaction pos_t var_t fn_name_t reg_t ext_fn_t :=
  match bc with
  | here => Some ua
  | through_nth_branch _ _ =>
      match zoom_breadcrumb with
      | None => None
      | Some (ua', bc') => access_breadcrumb bc' ua'
      end
  end.

Fixpoint findsb_uaction
  {pos_t var_t fn_name_t reg_t ext_fn_t: Type}
  (ua: uaction pos_t var_t fn_name_t reg_t ext_fn_t)
  (pred:
    forall (reg_t'' ext_fn_t'': Type),
    uaction pos_t var_t fn_name_t reg_t'' ext_fn_t''
    -> (reg_t'' -> reg_t) -> (ext_fn_t'' -> ext_fn_t)
    -> bool
  )
  (fR: reg_t -> reg_t') (fSigma: ext_fn_t -> ext_fn_t')
: option breadcrumb :=
  if pred reg_t' ext_fn_t' ua fR fSigma then
    Some here
  else match ua with
  | UAssign _ ex =>
    match findsb_uaction ex pred with
    | Some x => Some (through_nth_branch 0 x)
    | None => None
    end
  | USeq a1 a2 =>
    match findsb_uaction a1 pred with
    | Some x => Some (through_nth_branch 0 x)
    | None =>
      match findsb_uaction a2 pred with
      | Some x => Some (through_nth_branch 1 x)
      | None => None
      end
    end
  | UBind _ ex b =>
      match findsb_uaction ex pred with
      | Some x => Some (through_nth_branch 0 x)
      | None =>
        match findsb_uaction b pred with
        | Some x => Some (through_nth_branch 1 x)
        | None => None
        end
      end
  | UIf c t f =>
    match findsb_uaction c pred with
    | Some x => Some (through_nth_branch 0 x)
    | None =>
      match findsb_uaction t pred with
      | Some x => Some (through_nth_branch 1 x)
      | None =>
        match findsb_uaction f pred with
        | Some x => (through_nth_branch 2 x)
        | None => None
        end
      end
    end
  | UWrite _ _ a =>
    match findsb_uaction a pred with
    | Some x => Some (through_nth_branch 0 x)
    | None => None
    end
  | UUnop _ a =>
    match findsb_uaction a pred with
    | Some x => Some (through_nth_branch 0 x)
    | None => None
    end
  | UBinop _ a1 a2 =>
    match findsb_uaction a1 pred with
    | Some x => Some (through_nth_branch 0 x)
    | None =>
      match findsb_uaction a2 pred with
      | Some x => (through_nth_branch 1 x)
      | None => None
      end
    end
  | UExternalCall _ a =>
    match findsb_uaction a pred with
    | Some x => Some (through_nth_branch 0 x)
    | None => None
    end
  | UInternalCall ufn al =>
    match findsb_uaction (int_body ufn) pred with
    | Some x => Some (through_nth_branch 0 x)
    | None =>
      match TODO
        findsb (fun a => findsb_uaction a pred (through_nth_branch TODO)) al
      end
    end
  | UAPos _ e =>
    match findsb_uaction e pred with
    | Some x => Some (through_nth_branch 0 x)
    | None => None
    end
  | USugar s =>
    match findsb_usugar s pred with
    | Some x => Some (through_nth_branch 0 x)
    | None => None
  | _ => None
  end
with findsb_usugar
  {pos_t var_t fn_name_t reg_t ext_fn_t: Type}
  (us: usugar pos_t var_t fn_name_t reg_t ext_fn_t)
  (pred: uaction pos_t var_t fn_name_t reg_t ext_fn_t -> bool)
: breadcrumb :=
  match us with
  | UProgn aa =>
    match TODO
      findsb (fun a => findsb_uaction a pred) aa (through_nth_branch 0)
    end
  | ULet bindings body =>
    findsb (
      fun '(_, u) => findsb_uaction u pred (through_nth_branch TODO)
    ) bindings
    || findsb_uaction body pred (through_nth_branch TODO)
  | UWhen c b =>
    findsb_uaction c pred (through_nth_branch 0)
    || findsb_uaction b pred (through_nth_branch 1)
  | USwitch v d b =>
    findsb_uaction v pred (through_nth_branch 0)
    || findsb_uaction d pred (through_nth_branch 1)
    || findsb (
      fun '(u1, u2) =>
        findsb_uaction u1 pred (through_nth_branch TODO)
        || findsb_uaction u2 pred (through_nth_branch TODO)
    ) b
  | UStructInit _ f =>
    findsb (fun '(_, u) => findsb_uaction u pred (through_nth_branch TODO)) f
  | UArrayInit _ elts =>
    findsb (fun u => findsb_uaction u pred (through_nth_branch TODO)) elts
  | UCallModule fR fSigma fn args =>
    findsb_uaction (int_body fn) pred (through_nth_branch 0)
    || findsb (fun u => findsb_uaction u pred (through_nth_branch TODO)) args
  | _ => false
  end.

(* findsb_all_uaction *)

Theorem findsb_all_uaction_complete :
  forall 
(* Lemma no_write_to_reg_r_in_tree_implies_no_write_to_reg_r_in_trace: *)
(*   forall ctx sigma Gamma sched_log action_log rule action_log' v Gamma', *)
(*   interp_action ctx sigma Gamma sched_log action_log rule action_log' v Gamma' *)
(*   -> *)
(*   . *)
