(*! Language | Tactics and theorems for reasoning about the untyped inductive
    semantics of Kôika programs !*)
Require Import Coq.Program.Equality.
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
  {pos_t var_t fn_name_t reg_t ext_fn_t: Type}
  (ua: uaction pos_t var_t fn_name_t reg_t ext_fn_t)
  (pred: uaction pos_t var_t fn_name_t reg_t ext_fn_t -> bool)
: bool :=
  pred ua ||
  match ua with
  | UAssign _ ex => existsb_uaction ex pred
  | USeq a1 a2 => existsb_uaction a1 pred || existsb_uaction a2 pred
  | UBind _ ex b => existsb_uaction ex pred || existsb_uaction b pred
  | UIf c t f => existsb_uaction c pred || existsb_uaction t pred
    || existsb_uaction f pred
  | UWrite _ _ a => existsb_uaction a pred
  | UUnop _ a => existsb_uaction a pred
  | UBinop _ a1 a2 => existsb_uaction a1 pred || existsb_uaction a2 pred
  | UExternalCall _ a => existsb_uaction a pred
  | UInternalCall ufn al =>
    existsb_uaction (int_body ufn) pred
    || existsb (fun a => existsb_uaction a pred) al
  | UAPos _ e => existsb_uaction e pred
  | USugar s => existsb_usugar s pred
  | _ => false
  end
with existsb_usugar
  {pos_t var_t fn_name_t reg_t ext_fn_t: Type}
  (us: usugar pos_t var_t fn_name_t reg_t ext_fn_t)
  (pred: uaction pos_t var_t fn_name_t reg_t ext_fn_t -> bool)
: bool :=
  match us with
  | UProgn aa => existsb (fun a => existsb_uaction a pred) aa
  | ULet bindings body =>
    existsb (fun '(_, u) => existsb_uaction u pred) bindings
    || existsb_uaction body pred
  | UWhen c b => existsb_uaction c pred || existsb_uaction b pred
  | USwitch v d b => existsb_uaction v pred || existsb_uaction d pred
    || existsb (
      fun '(u1, u2) => existsb_uaction u1 pred || existsb_uaction u2 pred
    ) b
  | UStructInit _ f => existsb (fun '(_, u) => existsb_uaction u pred) f
  | UArrayInit _ elts => existsb (fun u => existsb_uaction u pred) elts
  | UCallModule fR fSigma fn args =>
    existsb_uaction (int_body fn) pred
    || existsb (fun u => existsb_uaction u pred) args
  | _ => false
  end.

Inductive Breadcrumb: here | through_nth_branch (n: nat).

Lemma no_write_to_reg_r_in_tree_implies_no_write_to_reg_r_in_trace:
  forall ctx sigma Gamma sched_log action_log rule action_log' v Gamma',
  interp_action ctx sigma Gamma sched_log action_log rule action_log' v Gamma'
  ->
  .
