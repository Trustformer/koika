(*! Proving | Zippers for uactions as well as functions for searching the
   syntactic tree !*)
Require Import List.
Require Import Koika.Syntax.
Open Scope nat.

Inductive zipper := here | through_nth_branch (n: nat) (b: zipper).

Definition zoom_zipper
  {pos_t var_t fn_name_t reg_t ext_fn_t: Type}
  (ua: uaction pos_t var_t fn_name_t reg_t ext_fn_t) (z: zipper)
: option (uaction pos_t var_t fn_name_t reg_t ext_fn_t) :=
  match z with
  | here => None
  | through_nth_branch n sz =>
    match ua with
    | UAssign v a => if n =? 0 then Some a else None
    | USeq a1 a2 => if n =? 0 then Some a1 else if n =? 1 then Some a2 else None
    | UBind _ expr body =>
      if n =? 0 then Some expr else if n =? 1 then Some body else None
    | UIf cond tbranch fbranch =>
      if n =? 0 then Some cond
      else if n =? 1 then Some tbranch
      else if n =? 2 then Some fbranch
      else None
    | UWrite _ _ v => if n =? 0 then Some v else None
    | UUnop _ a1 => if n =? 0 then Some a1 else None
    | UBinop _ a1 a2 =>
      if n =? 0 then Some a1 else if n =? 1 then Some a2 else None
    | UExternalCall _ a => if n =? 0 then Some a else None
    | UInternalCall ufn la =>
      if n =? 0 then Some (int_body ufn)
      else
        match nth_error la (n - 1) with
        | Some a => Some a
        | None => None
        end
    | UAPos _ e => if n =? 0 then Some e else None
    | _ => None
    end
  end.

Fixpoint access_zipper
  {pos_t var_t fn_name_t reg_t ext_fn_t: Type}
  (ua: uaction pos_t var_t fn_name_t reg_t ext_fn_t) (z: zipper)
: option (uaction pos_t var_t fn_name_t reg_t ext_fn_t) :=
  match z with
  | here => Some ua
  | through_nth_branch n sz =>
    match zoom_zipper ua z with
    | Some ua' => access_zipper ua' sz
    | None => None
    end
  end.

Definition zoom_zipper_tracking
  {pos_t var_t fn_name_t reg_t ext_fn_t A: Type}
  (ua: uaction pos_t var_t fn_name_t reg_t ext_fn_t) (z: zipper)
  (f: uaction pos_t var_t fn_name_t reg_t ext_fn_t -> A)
: option (uaction pos_t var_t fn_name_t reg_t ext_fn_t * A) :=
  match z with
  | here => None
  | through_nth_branch n sz =>
    match ua with
    | UAssign v a => if n =? 0 then Some (a, f ua) else None
    | USeq a1 a2 =>
      if n =? 0 then Some (a1, f ua)
      else if n =? 1 then Some (a2, f ua)
      else None
    | UBind _ expr body =>
      if n =? 0 then Some (expr, f ua)
      else if n =? 1 then Some (body, f ua)
      else None
    | UIf cond tbranch fbranch =>
      if n =? 0 then Some (cond, f ua)
      else if n =? 1 then Some (tbranch, f ua)
      else if n =? 2 then Some (fbranch, f ua)
      else None
    | UWrite _ _ v => if n =? 0 then Some (v, f ua) else None
    | UUnop _ a1 => if n =? 0 then Some (a1, f ua) else None
    | UBinop _ a1 a2 =>
      if n =? 0 then Some (a1, f ua)
      else if n =? 1 then Some (a2, f ua)
      else None
    | UExternalCall _ a => if n =? 0 then Some (a, f ua) else None
    | UInternalCall ufn la =>
      if n =? 0 then Some (int_body ufn, f ua)
      else
        match nth_error la (n - 1) with
        | Some a => Some (a, f ua)
        | None => None
        end
    | UAPos _ e => if n =? 0 then Some (e, f ua) else None
    | _ => None
    end
  end.

Fixpoint access_zipper_tracking_aux
  {pos_t var_t fn_name_t reg_t ext_fn_t A: Type}
  (ua: uaction pos_t var_t fn_name_t reg_t ext_fn_t) (z: zipper)
  (f: uaction pos_t var_t fn_name_t reg_t ext_fn_t -> A) (l: list A)
: option (uaction pos_t var_t fn_name_t reg_t ext_fn_t * list A) :=
  match z with
  | here => Some (ua, l)
  | through_nth_branch n sz =>
    match zoom_zipper_tracking ua z f with
    | Some (ua', r) => access_zipper_tracking_aux ua' sz f (r::l)
    | None => None
    end
  end.

Definition access_zipper_tracking
  {pos_t var_t fn_name_t reg_t ext_fn_t A: Type}
  (ua: uaction pos_t var_t fn_name_t reg_t ext_fn_t) (z: zipper)
  (f: uaction pos_t var_t fn_name_t reg_t ext_fn_t -> A)
: option (uaction pos_t var_t fn_name_t reg_t ext_fn_t * list A) :=
  access_zipper_tracking_aux ua z f nil.

Fixpoint find_all_in_uaction
  {pos_t var_t fn_name_t reg_t ext_fn_t: Type}
  (ua: uaction pos_t var_t fn_name_t reg_t ext_fn_t)
  (pred: uaction pos_t var_t fn_name_t reg_t ext_fn_t -> bool)
: list zipper :=
  app
    (if pred ua then [here] else [])
    (match ua with
    | UAssign _ ex =>
      map (fun z => through_nth_branch 0 z) (find_all_in_uaction ex pred)
    | USeq a1 a2 =>
      app
        (map (fun z => through_nth_branch 0 z) (find_all_in_uaction a1 pred))
        (map (fun z => through_nth_branch 1 z) (find_all_in_uaction a2 pred))
    | UBind _ ex b =>
      app
        (map (fun z => through_nth_branch 0 z) (find_all_in_uaction ex pred))
        (map (fun z => through_nth_branch 1 z) (find_all_in_uaction b pred))
    | UIf c t f =>
      app
        (app
          (map (fun z => through_nth_branch 0 z) (find_all_in_uaction c pred))
          (map (fun z => through_nth_branch 1 z) (find_all_in_uaction t pred))
        )
        (map (fun z => through_nth_branch 2 z) (find_all_in_uaction f pred))
    | UWrite _ _ a =>
      map (fun z => through_nth_branch 0 z) (find_all_in_uaction a pred)
    | UUnop _ a =>
      map (fun z => through_nth_branch 0 z) (find_all_in_uaction a pred)
    | UBinop _ a1 a2 =>
      app
        (map (fun z => through_nth_branch 0 z) (find_all_in_uaction a1 pred))
        (map (fun z => through_nth_branch 1 z) (find_all_in_uaction a2 pred))
    | UExternalCall _ a =>
      map (fun z => through_nth_branch 0 z) (find_all_in_uaction a pred)
    | UInternalCall ufn al =>
      app
        (map
          (fun z => through_nth_branch 0 z)
          (find_all_in_uaction (int_body ufn) pred)
        )
        (List.concat (snd (fold_left
          (fun acc ua => (
            S (fst acc), (find_all_in_uaction ua pred) :: (snd acc))
          )
          al (1, [])
        )))
    | UAPos _ e =>
      map (fun z => through_nth_branch 0 z) (find_all_in_uaction e pred)
    | _ => nil
    end).

Definition find_all_in_rule
  {rule_name_t pos_t var_t fn_name_t reg_t ext_fn_t: Type}
  (urule: rule_name_t -> uaction pos_t var_t fn_name_t reg_t ext_fn_t)
  (r: rule_name_t) (pred: uaction pos_t var_t fn_name_t reg_t ext_fn_t -> bool)
: list zipper :=
  find_all_in_uaction (urule r) pred.

Fixpoint find_all_in_schedule
  {rule_name_t pos_t var_t fn_name_t reg_t ext_fn_t: Type}
  (urule: rule_name_t -> uaction pos_t var_t fn_name_t reg_t ext_fn_t)
  (s: scheduler pos_t rule_name_t)
  (pred: uaction pos_t var_t fn_name_t reg_t ext_fn_t -> bool)
: list (rule_name_t * list zipper) :=
  match s with
  | Done => []
  | Cons r s' =>
    (r, find_all_in_rule urule r pred)::(find_all_in_schedule urule s' pred)
  | Try r s1 s2 =>
    (r, find_all_in_rule urule r pred)::(
      app
        (find_all_in_schedule urule s1 pred)
        (find_all_in_schedule urule s2 pred)
    )
  | SPos _ s' => find_all_in_schedule urule s' pred
  end.

Fixpoint replace_at_zipper
  {pos_t var_t fn_name_t reg_t ext_fn_t: Type}
  (ua: uaction pos_t var_t fn_name_t reg_t ext_fn_t) (z: zipper)
  (zr: uaction pos_t var_t fn_name_t reg_t ext_fn_t) {struct z}
: option (uaction pos_t var_t fn_name_t reg_t ext_fn_t) :=
  match z with
  | here => Some zr
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

Fixpoint get_depth (z: zipper) :=
  match z with
  | here => 0
  | through_nth_branch _ z' => S (get_depth z')
  end.

Fixpoint remove_top (n: nat) (z: zipper) :=
  match n with
  | 0 => z
  | S n' =>
    match z with
    | here => here
    | through_nth_branch _ z' => remove_top n' z'
    end
  end.
Close Scope nat.
