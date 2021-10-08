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

Inductive zipper := here | through_nth_branch (n: nat) (b: zipper).

Open Scope nat.

Definition zoom_zipper
  {pos_t var_t fn_name_t reg_t ext_fn_t: Type}
  (ua: uaction pos_t var_t fn_name_t reg_t ext_fn_t) (bc: zipper)
: option (uaction pos_t var_t fn_name_t reg_t ext_fn_t * zipper) :=
  match bc with
  | here => None
  | through_nth_branch n sbc =>
    match ua with
    | UAssign v a =>
      if n =? 0 then Some (a, sbc) else None
    | USeq a1 a2 =>
      if n =? 0 then Some (a1, sbc) else if n =? 1 then Some (a2, sbc) else None
    | UBind _ expr body =>
      if n =? 0 then Some (expr, sbc)
      else if n =? 1 then Some (body, sbc)
      else None
    | UIf cond tbranch fbranch =>
      if n =? 0 then Some (cond, sbc)
      else if n =? 1 then Some (tbranch, sbc)
      else if n =? 2 then Some (fbranch, sbc)
      else None
    | UWrite _ _ v => if n =? 0 then Some (v, sbc) else None
    | UUnop _ a1 => if n =? 0 then Some (a1, sbc) else None
    | UBinop _ a1 a2 =>
      if n =? 0 then Some (a1, sbc) else if n =? 1 then Some (a2, sbc) else None
    | UExternalCall _ a => if n =? 0 then Some (a, sbc) else None
    | UInternalCall ufn la =>
      if n =? 0 then Some (int_body ufn, sbc)
      else
        match nth_error la (n - 1) with
        | Some a => Some (a, sbc)
        | None => None
        end
    | UAPos _ e => if n =? 0 then Some (e, sbc) else None
    | _ => None
    end
  end.

Fixpoint zoom_n_zipper
  {pos_t var_t fn_name_t reg_t ext_fn_t: Type}
  (ua: uaction pos_t var_t fn_name_t reg_t ext_fn_t) (n: nat) (bc: zipper)
: option (uaction pos_t var_t fn_name_t reg_t ext_fn_t * zipper) :=
  match n with
  | O => Some (ua, bc)
  | S n' =>
    match zoom_zipper ua bc with
    | None => None
    | Some (ua', bc') => zoom_n_zipper ua' n' bc'
    end
  end.

Fixpoint access_zipper
  {pos_t var_t fn_name_t reg_t ext_fn_t: Type}
  (ua: uaction pos_t var_t fn_name_t reg_t ext_fn_t) (bc: zipper)
  {struct bc}
: option (uaction pos_t var_t fn_name_t reg_t ext_fn_t) :=
  match bc with
  | here => Some ua
  | through_nth_branch n sbc =>
    match ua with
    | UAssign v a => if n =? 0 then access_zipper a sbc else None
    | USeq a1 a2 =>
      if n =? 0 then access_zipper a1 sbc
      else if n =? 1 then access_zipper a2 sbc
     else None
    | UBind _ expr body =>
      if n =? 0 then access_zipper expr sbc
      else if n =? 1 then access_zipper body sbc
      else None
    | UIf cond tbranch fbranch =>
      if n =? 0 then access_zipper cond sbc
      else if n =? 1 then access_zipper tbranch sbc
      else if n =? 2 then access_zipper fbranch sbc
      else None
    | UWrite _ _ v => if n =? 0 then access_zipper v sbc else None
    | UUnop _ a1 => if n =? 0 then access_zipper a1 sbc else None
    | UBinop _ a1 a2 =>
      if n =? 0 then access_zipper a1 sbc
      else if n =? 1 then access_zipper a2 sbc
      else None
    | UExternalCall _ a => if n =? 0 then access_zipper a sbc else None
    | UInternalCall ufn la =>
      if n =? 0 then access_zipper (int_body ufn) sbc
      else
        match nth_error la (n - 1) with
        | Some a => access_zipper a sbc
        | None => None
        end
    | UAPos _ e => if n =? 0 then access_zipper e sbc else None
    | _ => None
    end
  end.

Fixpoint find_all_uaction
  {pos_t var_t fn_name_t reg_t ext_fn_t: Type}
  (ua: uaction pos_t var_t fn_name_t reg_t ext_fn_t)
  (pred: uaction pos_t var_t fn_name_t reg_t ext_fn_t -> bool)
: list zipper :=
  if pred ua then [here]
  else match ua with
  | UAssign _ ex =>
    map (fun bc => through_nth_branch 0 bc) (find_all_uaction ex pred)
  | USeq a1 a2 =>
    app
      (map (fun bc => through_nth_branch 0 bc) (find_all_uaction a1 pred))
      (map (fun bc => through_nth_branch 1 bc) (find_all_uaction a2 pred))
  | UBind _ ex b =>
    app
      (map (fun bc => through_nth_branch 0 bc) (find_all_uaction ex pred))
      (map (fun bc => through_nth_branch 1 bc) (find_all_uaction b pred))
  | UIf c t f =>
    app
      (app
        (map (fun bc => through_nth_branch 0 bc) (find_all_uaction c pred))
        (map (fun bc => through_nth_branch 1 bc) (find_all_uaction t pred))
      )
      (map (fun bc => through_nth_branch 2 bc) (find_all_uaction f pred))
  | UWrite _ _ a =>
    map (fun bc => through_nth_branch 0 bc) (find_all_uaction a pred)
  | UUnop _ a =>
    map (fun bc => through_nth_branch 0 bc) (find_all_uaction a pred)
  | UBinop _ a1 a2 =>
    app
      (map (fun bc => through_nth_branch 0 bc) (find_all_uaction a1 pred))
      (map (fun bc => through_nth_branch 1 bc) (find_all_uaction a2 pred))
  | UExternalCall _ a =>
    map (fun bc => through_nth_branch 0 bc) (find_all_uaction a pred)
  | UInternalCall ufn al =>
    app
      (map (fun bc => through_nth_branch 0 bc) (find_all_uaction (int_body ufn) pred))
      (List.concat (snd (fold_left
        (fun acc ua => (S (fst acc), (find_all_uaction ua pred) :: (snd acc)))
        al (1, [])
      )))
  | UAPos _ e =>
    map (fun bc => through_nth_branch 0 bc) (find_all_uaction e pred)
  | _ => nil
  end.
Close Scope nat.

Definition is_write
  {pos_t var_t fn_name_t reg_t ext_fn_t: Type}
  (ua: uaction pos_t var_t fn_name_t reg_t ext_fn_t)
: bool :=
  match ua with
  | UWrite _ _ _ => true
  | _ => false
  end.

Definition find_all_rule
  {rule_name_t pos_t var_t fn_name_t reg_t ext_fn_t: Type}
  (urule: rule_name_t -> uaction pos_t var_t fn_name_t reg_t ext_fn_t)
  (r: rule_name_t) (pred: uaction pos_t var_t fn_name_t reg_t ext_fn_t -> bool)
: list zipper :=
  find_all_uaction (urule r) pred.

Fixpoint find_all_schedule
  {rule_name_t pos_t var_t fn_name_t reg_t ext_fn_t: Type}
  (urule: rule_name_t -> uaction pos_t var_t fn_name_t reg_t ext_fn_t)
  (s: scheduler pos_t rule_name_t)
  (pred: uaction pos_t var_t fn_name_t reg_t ext_fn_t -> bool)
: list (rule_name_t * list zipper) :=
  match s with
  | Done => []
  | Cons r s' =>
    (r, find_all_rule urule r pred)::(find_all_schedule urule s' pred)
  | Try r s1 s2 =>
    (r, find_all_rule urule r pred)::(
      app (find_all_schedule urule s1 pred) (find_all_schedule urule s2 pred)
    )
  | SPos _ s' => find_all_schedule urule s' pred
  end.
