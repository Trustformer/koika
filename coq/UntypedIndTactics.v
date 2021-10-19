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

Definition map_uaction
  {rule_name_t pos_t var_t fn_name_t reg_t ext_fn_t: Type}
  (ua: uaction pos_t var_t fn_name_t reg_t ext_fn_t)
  (f: uaction pos_t var_t fn_name_t reg_t ext_fn_t
    -> uaction pos_t var_t fn_name_t reg_t ext_fn_t)
: uaction pos_t var_t fn_name_t reg_t ext_fn_t :=
  match ua with
  | USeq a1 a2 => USeq (f a1) (f a2)
  | UBind v ex body => UBind v (f ex) (f body)
  | UIf cond tbranch fbranch => UIf (f cond) (f tbranch) (f fbranch)
  | UWrite port idx value => UWrite port idx (f value)
  | UUnop ufn1 arg1 => UUnop ufn1 (f arg1)
  | UBinop ufn2 arg1 arg2 => UBinop ufn2 (f arg1) (f arg2)
  | UExternalCall ufn arg => UExternalCall ufn (f arg)
  | UInternalCall ufn args =>
    UInternalCall {|
      int_name := int_name ufn;
      int_argspec := int_argspec ufn;
      int_retSig := int_retSig ufn;
      int_body := f (int_body ufn);
    |} (map (f) args)
  | UAPos p e => UAPos p (f e)
  | _ => ua
  end.

Fixpoint fold_uaction
  {pos_t var_t fn_name_t reg_t ext_fn_t A: Type}
  (ua: uaction pos_t var_t fn_name_t reg_t ext_fn_t)
  (f: uaction pos_t var_t fn_name_t reg_t ext_fn_t -> A -> A) (acc: A)
: A :=
  let acc' := f ua acc in
  match ua with
  | USeq a1 a2 => fold_uaction a2 f (fold_uaction a1 f acc')
  | UBind _ ex body => fold_uaction body f (fold_uaction ex f acc')
  | UIf cond tbranch fbranch =>
    fold_uaction fbranch f (fold_uaction tbranch f (fold_uaction cond f acc'))
  | UWrite _ _ value => fold_uaction value f acc'
  | UUnop _ arg1 => fold_uaction arg1 f acc'
  | UBinop _ arg1 arg2 => fold_uaction arg2 f (fold_uaction arg1 f acc')
  | UExternalCall _ arg => fold_uaction arg f acc'
  | UInternalCall ufn args =>
    fold_right
      (fun a ac => fold_uaction a (f) ac) (fold_uaction (int_body ufn) f acc')
      args
  | UAPos _ e => fold_uaction e f acc'
  | _ => acc'
  end.

Definition apply_over_one_step
  {pos_t var_t fn_name_t reg_t ext_fn_t A: Type}
  (ua: uaction pos_t var_t fn_name_t reg_t ext_fn_t)
  (f: uaction pos_t var_t fn_name_t reg_t ext_fn_t -> A -> A) (acc: A)
: A :=
  match ua with
  | USeq a1 a2 => f a2 (f a1 acc)
  | UBind _ ex body => f body (f ex acc)
  | UIf cond tbranch fbranch => f fbranch (f tbranch (f cond acc))
  | UWrite _ _ value => f value acc
  | UUnop _ arg1 => f arg1 acc
  | UBinop _ arg1 arg2 => f arg2 (f arg1 acc)
  | UExternalCall _ arg => f arg acc
  | UInternalCall ufn args => fold_right (f) (f (int_body ufn) acc) args
  | UAPos _ e => f e acc
  | _ => acc
  end.

Fixpoint obtain_used_names_aux
  {pos_t var_t fn_name_t reg_t ext_fn_t: Type}
  (ua: uaction pos_t var_t fn_name_t reg_t ext_fn_t) (l: list var_t)
: list var_t :=
  match ua with
  | UBind v ex body =>
    obtain_used_names_aux body (obtain_used_names_aux ex (v::l))
  | UInternalCall ufn args => obtain_used_names_aux (int_body ufn) l
  | _ => apply_over_one_step ua (obtain_used_names_aux) l
  end.

Definition obtain_used_names
  {pos_t var_t fn_name_t reg_t ext_fn_t: Type}
  (ua: uaction pos_t var_t fn_name_t reg_t ext_fn_t)
: list var_t :=
  obtain_used_names_aux ua nil.

(* TODO remove assigns as well *)
Fixpoint remove_writes
  {pos_t var_t fn_name_t reg_t ext_fn_t: Type}
  (ua: uaction pos_t var_t fn_name_t reg_t ext_fn_t)
: uaction pos_t var_t fn_name_t reg_t ext_fn_t :=
  match ua with
  | UAssign v ex => UAssign v (remove_writes ex)
  | USeq a1 a2 => USeq (remove_writes a1) (remove_writes a2)
  | UBind v ex body =>
    UBind v (remove_writes ex) (remove_writes body)
  | UIf cond tbranch fbranch =>
    UIf
      (remove_writes cond) (remove_writes tbranch)
      (remove_writes fbranch)
  | UWrite port idx value => (remove_writes value)
  | UUnop ufn1 arg1 => UUnop ufn1 (remove_writes arg1)
  | UBinop ufn2 arg1 arg2 =>
    UBinop ufn2 (remove_writes arg1) (remove_writes arg2)
  | UExternalCall ufn arg => UExternalCall ufn (remove_writes arg)
  | UInternalCall ufn args =>
    UInternalCall {|
      int_name := int_name ufn;
      int_argspec := int_argspec ufn;
      int_retSig := int_retSig ufn;
      int_body := remove_writes (int_body ufn);
    |} (map (remove_writes) args)
  | UAPos p e => UAPos p (remove_writes e)
  | _ => ua
  end.

Fixpoint to_unit_t
  {pos_t var_t fn_name_t reg_t ext_fn_t: Type}
  (ua: uaction pos_t var_t fn_name_t reg_t ext_fn_t)
: uaction pos_t var_t fn_name_t reg_t ext_fn_t :=
  match ua with
  | UAssign v ex => UAssign v ex
  | USeq a1 a2 => USeq a1 (to_unit_t a2)
  | UBind v ex body => UBind v ex body
  | UIf cond tbranch fbranch => UIf cond (to_unit_t tbranch) (to_unit_t fbranch)
  | URead port idx => UConst (tau := bits_t 0) (Bits.of_nat 0 0)
  | UWrite port idx value => UWrite port idx value
  | UUnop ufn1 arg1 => UConst (tau := bits_t 0) (Bits.of_nat 0 0)
  | UBinop ufn2 arg1 arg2 => UConst (tau := bits_t 0) (Bits.of_nat 0 0)
  | UExternalCall ufn arg => UExternalCall ufn arg
  | UInternalCall ufn args => UConst (tau := bits_t 0) (Bits.of_nat 0 0)
  | UAPos p e => UAPos p (to_unit_t e)
  | _ => UConst (tau := bits_t 0) (Bits.of_nat 0 0)
  end.

Fixpoint replace_variable_with_expr
  {pos_t var_t fn_name_t reg_t ext_fn_t: Type}
  {beq_var_t: EqDec var_t}
  (ua: uaction pos_t var_t fn_name_t reg_t ext_fn_t) (vr: var_t)
  (rex: uaction pos_t var_t fn_name_t reg_t ext_fn_t)
: uaction pos_t var_t fn_name_t reg_t ext_fn_t
  * uaction pos_t var_t fn_name_t reg_t ext_fn_t
:=
  match ua with
  | UAssign v ex =>
    let (ra1, post_val_1) := replace_variable_with_expr ex vr rex in
    if (eq_dec v vr) then (UConst (tau := bits_t 0) (Bits.of_nat 0 0), ra1)
    else (UAssign v ra1, post_val_1)
  | USeq a1 a2 =>
    let (ra1, post_val_1) := replace_variable_with_expr a1 vr rex in
    let (ra2, post_val_2) := replace_variable_with_expr a2 vr post_val_1 in
    (USeq ra1 ra2, post_val_2)
  | UBind v ex body =>
    let (ra1, post_val_1) := replace_variable_with_expr ex vr rex in
    if (eq_dec v vr) then
      (* vr is shadowed, don't replace in body *)
      (UBind v ra1 body, post_val_1)
    else
      let (ra2, post_val_2) := replace_variable_with_expr body vr post_val_1 in
      (UBind v ra1 ra2, post_val_2)
  | UIf cond tbranch fbranch =>
    let (ra1, post_val_1) := replace_variable_with_expr cond vr rex in
    let (rat, post_val_t) := replace_variable_with_expr tbranch vr post_val_1 in
    let (raf, post_val_f) := replace_variable_with_expr fbranch vr post_val_1 in
    (UIf ra1 rat raf, UIf ra1 post_val_t post_val_f)
  | UWrite port idx value =>
    let (ra1, post_val_1) := replace_variable_with_expr value vr rex in
    (UWrite port idx ra1, post_val_1)
  | UUnop ufn1 arg1 =>
    let (ra1, post_val_1) := replace_variable_with_expr arg1 vr rex in
    (UUnop ufn1 ra1, post_val_1)
  | UBinop ufn2 arg1 arg2 =>
    let (ra1, post_val_1) := replace_variable_with_expr arg1 vr rex in
    let (ra2, post_val_2) := replace_variable_with_expr arg2 vr post_val_1 in
    (UBinop ufn2 ra1 ra2, post_val_2)
  | UExternalCall ufn arg =>
    let (ra1, post_val_1) := replace_variable_with_expr arg vr rex in
    (UExternalCall ufn ra1, post_val_1)
  | UInternalCall ufn args =>
    let (rargs, post_val_args) := (
      fold_right
        (fun arg '(l, rex') =>
          let (ran, post_val) := replace_variable_with_expr arg vr rex' in
          (ran::l, post_val)
        )
        (nil, rex)
        args
    ) in
    (UInternalCall ufn rargs, post_val_args)
  | UAPos p e =>
    let (ra1, post_val_1) := replace_variable_with_expr e vr rex in
    (UAPos p ra1, post_val_1)
  | UVar var => if (eq_dec var vr) then (rex, rex) else (ua, rex)
  | _ => (ua, rex)
  end.

(* XXX Supposes desugared *)
Fixpoint inline_internal_calls
  {pos_t var_t fn_name_t reg_t ext_fn_t: Type} {beq_var_t: EqDec var_t}
  (ua: uaction pos_t var_t fn_name_t reg_t ext_fn_t)
: uaction pos_t var_t fn_name_t reg_t ext_fn_t :=
  match ua with
  | UAssign v ex => UAssign v (inline_internal_calls ex)
  | USeq a1 a2 => USeq (inline_internal_calls a1) (inline_internal_calls a2)
  | UBind v ex body =>
    UBind v (inline_internal_calls ex) (inline_internal_calls body)
  | UIf cond tbranch fbranch =>
    UIf (inline_internal_calls cond) (inline_internal_calls tbranch)
    (inline_internal_calls fbranch)
  | UWrite port idx value => UWrite port idx (inline_internal_calls value)
  | UUnop ufn1 arg1 => UUnop ufn1 (inline_internal_calls arg1)
  | UBinop ufn2 arg1 arg2 =>
    UBinop ufn2 (inline_internal_calls arg1) (inline_internal_calls arg2)
  | UExternalCall ufn arg => UExternalCall ufn (inline_internal_calls arg)
  | UInternalCall ufn args =>
    let args_eval :=
      fold_right (fun arg acc => USeq acc (inline_internal_calls arg))
      (UConst (tau := bits_t 0) (Bits.of_nat 0 0)) args
    in
    let inlined_call :=
      fold_right
        (fun '(arg_n, arg_v) bd =>
          fst (replace_variable_with_expr bd arg_n arg_v)
        )
        (inline_internal_calls (int_body ufn))
        (combine
          (fst (split (int_argspec ufn)))
          (map (fun arg => remove_writes (inline_internal_calls arg)) args)
        )
    in
    USeq (to_unit_t args_eval) inlined_call
  | UAPos p e => UAPos p (inline_internal_calls e)
  | _ => ua
  end.

Lemma map_nil_nil: forall {A B} f sm, sm = [] -> @map A B f sm = [].
Proof. intros. induction sm; easy. Qed.

Lemma map_nil_nil': forall {A B} f sm, @map A B f sm = [] -> sm = [].
Proof. intros. induction sm; easy. Qed.

Lemma app_eq_nil:
  forall {A: Type} (l l': list A), l = [] /\ l' = [] -> l ++ l' = [].
Proof. intros. destruct H. subst. reflexivity. Qed.

Lemma app_eq_nil':
  forall {A: Type} (l l': list A),  l ++ l' = [] -> l = [] /\ l' = [].
Proof. intros. induction l; simpl in *; split; easy. Qed.

Lemma to_unit_t_does_not_add_UInternalCalls:
  forall {pos_t var_t fn_name_t reg_t ext_fn_t: Type} {beq_var_t: EqDec var_t}
  (ua: uaction pos_t var_t fn_name_t reg_t ext_fn_t),
  find_all_uaction (inline_internal_calls ua) (fun a =>
    match a with UInternalCall _ _ => true | _ => false end
  ) = nil
  -> find_all_uaction (inline_internal_calls (to_unit_t ua)) (fun a =>
    match a with UInternalCall _ _ => true | _ => false end
  ) = nil.
Proof.
  intros.
  induction ua; auto; simpl in *.
  - apply app_eq_nil' in H. destruct H. apply map_nil_nil' in H, H0.
    apply app_eq_nil. split; apply map_nil_nil;auto.
  - apply app_eq_nil' in H. destruct H.
    apply app_eq_nil' in H. destruct H.
    apply map_nil_nil' in H, H0, H1.
    apply app_eq_nil. split.
    + apply app_eq_nil. split; apply map_nil_nil; auto.
    + apply map_nil_nil. apply IHua3; auto.
  - apply map_nil_nil. apply IHua. apply map_nil_nil' in H. apply H.
Qed.

(* Lemma inline_internal_calls_removes_UInternalCalls: *)
(*   forall {pos_t var_t fn_name_t reg_t ext_fn_t: Type} {beq_var_t: EqDec var_t} *)
(*   (ua: uaction pos_t var_t fn_name_t reg_t ext_fn_t), *)
(*   find_all_uaction (inline_internal_calls ua) (fun ua => *)
(*     match ua with UInternalCall _ _ => true | _ => false end *)
(*   ) = nil. *)
(* Proof. *)
  (* intros. *)
  (* induction ua using uaction_ind'; simpl; try reflexivity; *)
  (*   try auto 15 using map_nil_nil, app_eq_nil, combine_nil, app_eq_nil. *)
  (* - induction H. *)
  (*   + simpl. apply map_nil_nil. rewrite combine_nil. simpl. apply IHua. *)
  (*   + apply app_eq_nil' in IHForall. destruct IHForall. *)
  (*     apply map_nil_nil' in H1. apply map_nil_nil' in H2. *)
  (*     simpl. apply app_eq_nil. *)
  (*     split; try apply map_nil_nil; try apply app_eq_nil; try split; *)
  (*     try apply map_nil_nil; simpl in *. *)
  (*     * apply H1. Search fold_right. *)



  (*     induction l. *)
  (*     * simpl in *. split; repeat apply map_nil_nil. *)
  (*       ** rewrite to_unit_t_does_not_add_UInternalCalls. *)



  (*     split. *)
  (*     * apply map_nil_nil. apply app_eq_nil. split; apply map_nil_nil. *)
  (*       ** induction l. *)
  (*          *** simpl in *. reflexivity. *)
  (*          *** simpl in *. apply app_eq_nil. split; apply map_nil_nil. *)
  (*            ++ apply app_eq_nil' in H1. destruct H1. apply IHl. *)
  (*              +++ apply Forall_inv_tail in H0. assumption. *)
  (*              +++ apply map_nil_nil' in H1. *)
  (*                  apply to_unit_t_does_not_add_UInternalCalls with *)
  (*                  (ua := (fold_right *)
  (*                    (fun arg acc : uaction pos_t var_t fn_name_t reg_t ext_fn_t *)
  (*                      => USeq acc (inline_internal_calls arg) *)
  (*                    ) *)
  (*                   (UConst ()) l) *)
  (*                 ). *)
  (*     ; try rewrite app_eq_nil; try split; apply map_nil_nil. *)
  (*     * *)
(* Qed. *)

(* Lemma inline_internal_calls_ok: *)
(*   forall {pos_t var_t fn_name_t reg_t ext_fn_t: Type} {beq_var_t: EqDec var_t} *)
(*   Sigma *)
(*   (ua: uaction pos_t var_t fn_name_t reg_t ext_fn_t), *)
(*   interp_action Sigma ua inline_internal_calls ua *)
(* Proof. *)
  (* TODO *)
(* Qed. *)

(* XXX Supposes desugared, no internal calls *)
(* TODO rename post_gamma_x to Gamma''...' *)
Fixpoint remove_bindings_aux
  {pos_t var_t fn_name_t reg_t ext_fn_t: Type} {beq_var_t: EqDec var_t}
  (ua: uaction pos_t var_t fn_name_t reg_t ext_fn_t)
  (Gamma: list (var_t * uaction pos_t var_t fn_name_t reg_t ext_fn_t))
: uaction pos_t var_t fn_name_t reg_t ext_fn_t
  * list (var_t * uaction pos_t var_t fn_name_t reg_t ext_fn_t)
:=
  match ua with
  | UVar var =>
    match list_assoc Gamma var with
    | Some lar => (lar, Gamma)
    (* Should never happen in well-formed rules *)
    | None => (UConst (tau := bits_t 0) (Bits.of_nat 0 0), Gamma)
    end
  | UAssign v ex =>
    let (ra1, post_gamma_1) := remove_bindings_aux ex Gamma in
    (to_unit_t ra1, list_assoc_set post_gamma_1 v (remove_writes ra1))
  | USeq a1 a2 =>
    let (ra1, post_gamma_1) := remove_bindings_aux a1 Gamma in
    let (ra2, post_gamma_2) := remove_bindings_aux a2 post_gamma_1 in
    (USeq ra1 ra2, post_gamma_2)
  | UBind v ex body =>
    let (ra1, post_gamma_1) := remove_bindings_aux ex Gamma in
    let (ra2, post_gamma_2) :=
      remove_bindings_aux body ((v, ex)::post_gamma_1)
    in
    (USeq (to_unit_t ra1) ra2, tl post_gamma_2)
  | UIf cond tbranch fbranch =>
    let (ra1, post_gamma_1) := remove_bindings_aux cond Gamma in
    let (rat, post_gamma_t) := remove_bindings_aux tbranch post_gamma_1 in
    let (raf, post_gamma_f) := remove_bindings_aux fbranch post_gamma_1 in
    (* TODO most cases could be simplified *)
    let final_gamma :=
      fold_right
        (fun v acc =>
          list_assoc_set acc v (
            UIf ra1 (
              match list_assoc post_gamma_t v with
              | Some lar => lar
              | None => UConst (tau := bits_t 0) (Bits.of_nat 0 0)
              end
            ) (
              match list_assoc post_gamma_f v with
              | Some lar => lar
              | None => UConst (tau := bits_t 0) (Bits.of_nat 0 0)
              end
            )
          )
        )
        post_gamma_1 (fst (split post_gamma_1))
    in
    (UIf ra1 rat raf, final_gamma)
  | UWrite port idx value =>
    let (ra1, post_gamma_1) := remove_bindings_aux value Gamma in
    (UWrite port idx ra1, post_gamma_1)
  | UUnop ufn1 arg1 =>
    let (ra1, post_gamma_1) := remove_bindings_aux arg1 Gamma in
    (UUnop ufn1 ra1, post_gamma_1)
  | UBinop ufn2 arg1 arg2 =>
    let (ra1, post_gamma_1) := remove_bindings_aux arg1 Gamma in
    let (ra2, post_gamma_2) := remove_bindings_aux arg2 post_gamma_1 in
    (UBinop ufn2 ra1 ra2, post_gamma_2)
  | UExternalCall ufn arg =>
    let (ra1, post_gamma_1) := remove_bindings_aux arg Gamma in
    (UExternalCall ufn ra1, post_gamma_1)
  | UInternalCall ufn args =>
    let (rargs, post_gamma_args) := (
      fold_right
        (fun arg '(l, Gamma') =>
          let (ran, post_val) := remove_bindings_aux arg Gamma' in
          (ran::l, post_val)
        )
        (nil, Gamma)
        args
    ) in
    (UInternalCall ufn rargs, post_gamma_args)
  | UAPos p e =>
    let (ra1, post_gamma_1) := remove_bindings_aux e Gamma in
    (UAPos p ra1, post_gamma_1)
  | _ => (ua, Gamma)
  end.

Definition remove_bindings
  {pos_t var_t fn_name_t reg_t ext_fn_t: Type} {beq_var_t: EqDec var_t}
  (ua: uaction pos_t var_t fn_name_t reg_t ext_fn_t)
: uaction pos_t var_t fn_name_t reg_t ext_fn_t :=
  fst (remove_bindings_aux ua nil).

(* XXX Supposes desugared, no internal calls, no bindings *)
Fixpoint remove_uapos
  {pos_t var_t fn_name_t reg_t ext_fn_t: Type}
  (ua: uaction pos_t var_t fn_name_t reg_t ext_fn_t)
: uaction pos_t var_t fn_name_t reg_t ext_fn_t :=
  match ua with
  | USeq a1 a2 => USeq (remove_uapos a1) (remove_uapos a2)
  | UIf cond tbranch fbranch =>
    UIf (remove_uapos cond) (remove_uapos tbranch) (remove_uapos fbranch)
  | UWrite port idx value => UWrite port idx (remove_uapos value)
  | UUnop ufn1 arg1 => UUnop ufn1 (remove_uapos arg1)
  | UBinop ufn2 arg1 arg2 => UBinop ufn2 (remove_uapos arg1) (remove_uapos arg2)
  | UExternalCall ufn arg => UExternalCall ufn (remove_uapos arg)
  | UAPos p e => remove_uapos e
  | _ => ua
  end.

(* XXX Supposes no internal calls, desugared *)
Fixpoint remove_first_binding
  {pos_t var_t fn_name_t reg_t ext_fn_t: Type} {beq_var_t: EqDec var_t}
  (ua: uaction pos_t var_t fn_name_t reg_t ext_fn_t)
: uaction pos_t var_t fn_name_t reg_t ext_fn_t :=
  match ua with
  | USeq a1 a2 => USeq (remove_first_binding a1) (remove_first_binding a2)
  | UBind v ex body =>
    USeq
      (to_unit_t ex)
      (fst (replace_variable_with_expr body v (remove_writes ex)))
  | UIf cond tbranch fbranch =>
    UIf (remove_first_binding cond) (remove_first_binding tbranch)
      (remove_first_binding fbranch)
  | UWrite port idx value => UWrite port idx (remove_first_binding value)
  | UUnop ufn1 arg1 => UUnop ufn1 (remove_first_binding arg1)
  | UBinop ufn2 arg1 arg2 => UBinop ufn2 (remove_first_binding arg1) (remove_first_binding arg2)
  | UExternalCall ufn arg => UExternalCall ufn (remove_first_binding arg)
  | UAPos p e => UAPos p (remove_first_binding e)
  | _ => ua
  end.

Fixpoint remove_first_n_bindings
  {pos_t var_t fn_name_t reg_t ext_fn_t: Type} {beq_var_t: EqDec var_t}
  (ua: uaction pos_t var_t fn_name_t reg_t ext_fn_t) (n: nat)
: uaction pos_t var_t fn_name_t reg_t ext_fn_t :=
  match n with
  | O => ua
  | S n' => remove_first_n_bindings (remove_first_binding ua) n'
  end.

Fixpoint replace_at_zipper
  {pos_t var_t fn_name_t reg_t ext_fn_t: Type}
  (ua: uaction pos_t var_t fn_name_t reg_t ext_fn_t) (z: zipper)
  (zr: uaction pos_t var_t fn_name_t reg_t ext_fn_t) {struct z}
: option (uaction pos_t var_t fn_name_t reg_t ext_fn_t) :=
  match z with
  | here => Some ua
  | through_nth_branch n sz =>
    match ua with
    | UAssign v a =>
      if n =? 0 then
        option_map (fun e => UAssign v e) (replace_at_zipper a sz zr)
      else None
    | USeq a1 a2 =>
      if n =? 0 then
        option_map (fun e => USeq e a2) (replace_at_zipper a1 sz zr)
      else if n =? 1 then
        option_map (fun e => USeq a1 e) (replace_at_zipper a2 sz zr)
      else None
    | UBind var expr body =>
      if n =? 0 then
        option_map (fun e => UBind var e body) (replace_at_zipper expr sz zr)
      else if n =? 1 then
        option_map (fun e => UBind var expr e) (replace_at_zipper body sz zr)
      else None
    | UIf cond tbranch fbranch =>
      if n =? 0 then
        option_map (fun e => UIf e tbranch fbranch)
          (replace_at_zipper cond sz zr)
      else if n =? 1 then
        option_map (fun e => UIf cond e fbranch)
          (replace_at_zipper tbranch sz zr)
      else if n =? 2 then
        option_map (fun e => UIf cond tbranch e)
          (replace_at_zipper fbranch sz zr)
      else None
    | UWrite r p v =>
      if n =? 0 then
        option_map (fun e => UWrite r p e) (replace_at_zipper v sz zr)
      else None
    | UUnop f a1 =>
      if n =? 0 then
        option_map (fun e => UUnop f e) (replace_at_zipper a1 sz zr)
      else None
    | UBinop f a1 a2 =>
      if n =? 0 then
        option_map (fun e => UBinop f e a2) (replace_at_zipper a1 sz zr)
      else if n =? 1 then
        option_map (fun e => UBinop f a1 e) (replace_at_zipper a2 sz zr)
      else None
    | UExternalCall f a =>
      if n =? 0 then
        option_map (fun e => UExternalCall f a) (replace_at_zipper a sz zr)
      else None
    | UInternalCall ufn la =>
      if n =? 0 then
        option_map (fun e =>
          UInternalCall {|
            int_name := int_name ufn;
            int_argspec := int_argspec ufn;
            int_retSig := int_retSig ufn;
            int_body := e;
          |} la) (replace_at_zipper (int_body ufn) sz zr)
      else
        match (nth_error la (n - 1)) with
        | Some x =>
          option_map (fun e =>
            UInternalCall ufn ((firstn (n - 2) la) ++ [e] ++ (skipn (n - 1) la))
          ) (replace_at_zipper x sz zr)
        | None => None
        end
    | UAPos p a =>
      if n =? 0 then option_map (fun e => UAPos p e) (replace_at_zipper a sz zr)
      else None
    | _ => Some ua
    end
  end.
Close Scope nat.

Definition replace_at_zipper_with
  {pos_t var_t fn_name_t reg_t ext_fn_t: Type}
  (ua: uaction pos_t var_t fn_name_t reg_t ext_fn_t) (z: zipper)
  (f: uaction pos_t var_t fn_name_t reg_t ext_fn_t ->
      uaction pos_t var_t fn_name_t reg_t ext_fn_t)
: option (uaction pos_t var_t fn_name_t reg_t ext_fn_t) :=
  match access_zipper ua z with
  | Some x => replace_at_zipper ua z (f x)
  | None => None
  end.

Fixpoint remove_this_binding
  {pos_t var_t fn_name_t reg_t ext_fn_t: Type} {beq_var_t: EqDec var_t}
  (ua: uaction pos_t var_t fn_name_t reg_t ext_fn_t) (z: zipper)
: option (uaction pos_t var_t fn_name_t reg_t ext_fn_t) :=
  (* TODO return none when zipper does not point to a binding *)
  replace_at_zipper_with ua z remove_first_binding.
(* TODO How to deal with external calls? This depends on what we mean by
     functional equivalence.

   In Kôika, logs generation is done through interp_action, which takes a pure
   model of the available external calls as an argument.

   Should we perhaps prove that no matter which model is given for these
   functions, the logs that end up being generated are the same? Is this even
   possible with Kôika's semantics?

   We know that we are not reasoning on raw logs since we ultimately want to get
   rid of the write1s. Maybe something that associates a new expression that
   including .

   What about impure external calls?
*)

(* XXX Supposes desugared, no internal calls, no bindings, no uapos *)
(* This is acceptable as sigma *)
(* Fixpoint remove_unused_external_calls *)
(*   {pos_t var_t fn_name_t reg_t ext_fn_t: Type} *)
(*   (Sigma: ext_fn_t -> Sig 1) (ext_mocks: forall f, Sig_denote (Sigma f)) *)
(*   (ua: uaction pos_t var_t fn_name_t reg_t ext_fn_t) *)
(* : uaction pos_t var_t fn_name_t reg_t ext_fn_t := *)
(*   match ua with *)
(*   | USeq a1 a2 => *)
(*     USeq *)
(*       (remove_unused_external_calls Sigma ext_mocks a1) *)
(*       (remove_unused_external_calls Sigma ext_mocks a2) *)
(*   | UIf cond tbranch fbranch => *)
(*     UIf *)
(*       (remove_unused_external_calls Sigma ext_mocks cond) *)
(*       (remove_unused_external_calls Sigma ext_mocks tbranch) *)
(*       (remove_unused_external_calls Sigma ext_mocks fbranch) *)
(*   | UWrite port idx value => *)
(*     UWrite port idx (remove_unused_external_calls Sigma ext_mocks value) *)
(*   | UUnop ufn1 arg1 => *)
(*     UUnop ufn1 (remove_unused_external_calls Sigma ext_mocks arg1) *)
(*   | UBinop ufn2 arg1 arg2 => *)
(*     UBinop *)
(*       ufn2 (remove_unused_external_calls Sigma ext_mocks arg1) *)
(*       (remove_unused_external_calls Sigma ext_mocks arg2) *)
(*   | UExternalCall ufn arg => *)
(*     USeq (to_unit_t (remove_unused_external_calls Sigma ext_mocks arg)) ufn *)
(*   | _ => ua *)
(*   end. *)
